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

  (* DLAB off, read off the bundle without spending it: what the RHR pop
     needs to know that offset 0 really is the receive register and not the
     divisor latch. *)
  Lemma uart_ghosts_dlab_off (γ : uart_names) (u : uart_state) :
    uart_dlab_off γ -∗ uart_ghosts γ u -∗ ⌜ uart_dlab u = false ⌝.
  Proof.
    iIntros "Hoff (_ & _ & _ & Hdl)".
    by iDestruct (uart_dlab_agree with "Hdl Hoff") as %Hd.
  Qed.

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
  Proof. rewrite /uart_rx_pushed_lb. apply _. Qed.
  Global Instance uart_rx_tok_timeless γ k hl : Timeless (uart_rx_tok γ k hl).
  Proof. rewrite /uart_rx_tok. apply _. Qed.
  Global Instance uart_rx_hi_timeless γ q hh : Timeless (uart_rx_hi γ q hh).
  Proof. rewrite /uart_rx_hi. apply _. Qed.

  Lemma uart_rx_tok_agree γ k k' hl hl' :
    uart_rx_popped γ k hl -∗ uart_rx_tok γ k' hl' -∗ ⌜k = k' /\ hl = hl'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq.
    iPureIntro. by injection Heq.
  Qed.
  Lemma uart_rx_tok_update γ k k' hl hl' :
    uart_rx_popped γ k hl -∗ uart_rx_tok γ k hl ==∗
      uart_rx_popped γ k' hl' ∗ uart_rx_tok γ k' hl'.
  Proof.
    iIntros "H1 H2". iApply (ghost_var_update_halves with "H1 H2").
  Qed.

  Lemma uart_rx_hi_agree γ hh hh' :
    uart_rx_hi γ (1/2) hh -∗ uart_rx_hi γ (1/2) hh' -∗ ⌜hh = hh'⌝.
  Proof.
    iIntros "H1 H2". by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.
  Lemma uart_rx_hi_update γ hh hh' :
    uart_rx_hi γ (1/2) hh -∗ uart_rx_hi γ (1/2) hh ==∗
      uart_rx_hi γ (1/2) hh' ∗ uart_rx_hi γ (1/2) hh'.
  Proof.
    iIntros "H1 H2". iApply (ghost_var_update_halves with "H1 H2").
  Qed.
  Lemma uart_rx_hi_alloc (hh : option (list mobs)) :
    ⊢ |==> ∃ γn : gname, ghost_var γn (1/2) hh ∗ ghost_var γn (1/2) hh.
  Proof.
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
  Proof. rewrite /uart_inited. apply _. Qed.
  Global Instance uart_preinit_timeless γ : Timeless (uart_preinit γ).
  Proof. rewrite /uart_preinit. apply _. Qed.

  Lemma uart_preinit_inited_False γ : uart_preinit γ -∗ uart_inited γ -∗ False.
  Proof.
    iIntros "Ha Hlb".
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle].
    iPureIntro. lia.
  Qed.
  Lemma uart_preinit_fire γ : uart_preinit γ ==∗ uart_inited γ.
  Proof.
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
  Definition uart_col_ok (u : uart_state) (hs : list (list mobs))
      (np nk : nat) (hl ht : option (list mobs)) : Prop :=
    np = (nk + length (u_rx u))%nat
    /\ length hs = length (u_rx u)
    /\ uart_loopback u = false
    /\ u_wire u = u_out u
    /\ (forall (j : nat) (b : bv 8) (h : list mobs),
          u_rx u !! j = Some b -> hs !! j = Some h -> obs_ends_in h b)
    /\ (forall (i j : nat) (hi hj : list mobs),
          hs !! i = Some hi -> hs !! j = Some hj -> (i < j)%nat ->
          hist_ext hi hj)
    /\ (forall (j : nat) (h : list mobs), hs !! j = Some h -> ohist_ext hl h)
    /\ ohist_le hl ht
    /\ (forall (j : nat) (h : list mobs),
          hs !! j = Some h -> ohist_le (Some h) ht).

  (* the lower bound at an optional history: nothing at all when there is
     none, which is the boot state and the state after a flush that found an
     empty queue. *)
  Definition obs_hist_lb_o (o : option (list mobs)) : iProp Σ :=
    match o with Some g => obs_hist_lb g | None => emp end.

  Global Instance obs_hist_lb_o_persistent o : Persistent (obs_hist_lb_o o).
  Proof. destruct o; apply _. Qed.
  Global Instance obs_hist_lb_o_timeless o : Timeless (obs_hist_lb_o o).
  Proof. destruct o; apply _. Qed.

  Definition uart_col (γ : uart_names) (u : uart_state)
      (hs : list (list mobs)) (np nk : nat)
      (hl ht : option (list mobs)) : iProp Σ :=
    (mono_nat_auth_own γ.(un_rxpush) 1 np ∗ uart_rx_popped γ nk hl ∗
     ([∗ list] h ∈ hs, riscv_rx_tag h ∗ obs_hist_lb h) ∗
     obs_hist_lb_o ht ∗
     ⌜uart_col_ok u hs np nk hl ht⌝)%I.

  Definition uart_colE (γ : uart_names) (u : uart_state) : iProp Σ :=
    (∃ hs np nk hl ht, uart_col γ u hs np nk hl ht)%I.

  Global Instance uart_col_timeless γ u hs np nk hl ht :
    Timeless (uart_col γ u hs np nk hl ht).
  Proof. rewrite /uart_col /uart_rx_popped. apply _. Qed.
  Global Instance uart_colE_timeless γ u : Timeless (uart_colE γ u).
  Proof. rewrite /uart_colE. apply _. Qed.

  (* the clause the tx arm reads: the column exists only with LOOP off *)
  Lemma uart_colE_loopback (γ : uart_names) (u : uart_state) :
    uart_colE γ u -∗ ⌜uart_loopback u = false⌝.
  Proof.
    iIntros "H". iDestruct "H" as (hs np nk hl ht) "(_ & _ & _ & _ & %Hok)".
    iPureIntro. exact (proj1 (proj2 (proj2 Hok))).
  Qed.

  (* ...AND THE ONE THE LEDGER READS: the wire IS the drained sequence, so a
     client that knows [obs_wire (open_seg h) = u_wire u] knows the wire's
     length is [length (u_out u)] -- the accepted position the byte the
     drain popped sits at. *)
  Lemma uart_colE_wire_out (γ : uart_names) (u : uart_state) :
    uart_colE γ u -∗ ⌜u_wire u = u_out u⌝.
  Proof.
    iIntros "H". iDestruct "H" as (hs np nk hl ht) "(_ & _ & _ & _ & %Hok)".
    iPureIntro. exact (proj1 (proj2 (proj2 (proj2 Hok)))).
  Qed.

  (* a transition that touches neither the FIFO nor LOOP nor the transmit
     pair carries it over.  The two transmit facts are new with the
     wire/out clause and are a one-liner at every caller: no MMIO access
     moves either ([ObsTrace.uart_read_wire]/[uart_write_wire],
     [DevModel.uart_read_stable]/[uart_write_out]) and neither does an
     arrival ([uart_rx_push_wire]/[uart_rx_push_out]). *)
  Lemma uart_colE_stable (γ : uart_names) (u u' : uart_state) :
    u_rx u' = u_rx u ->
    uart_loopback u' = uart_loopback u ->
    u_wire u' = u_wire u ->
    u_out u' = u_out u ->
    uart_colE γ u -∗ uart_colE γ u'.
  Proof.
    iIntros (Hrx Hlb Hw Ho) "H".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iExists hs, np, nk, hl, ht. iFrame "Ha Hk Hts Hht". iPureIntro.
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8).
    rewrite /uart_col_ok Hrx Hlb Hw Ho. split_and!; assumption.
  Qed.

  (* THE DRAIN, the one transition that moves the transmit pair: with LOOP
     off -- which is the column's own clause, so nothing has to be supplied
     -- the popped byte goes on the END of BOTH lists
     ([ObsTrace.uart_tx_pop_wire], [DevModel.uart_tx_pop_out]), and the
     receive side is untouched. *)
  Lemma uart_colE_tx_pop (γ : uart_names) (u u' : uart_state) (b : bv 8) :
    uart_tx_pop u = Some (b, u') ->
    uart_colE γ u -∗ uart_colE γ u'.
  Proof.
    iIntros (Hpop) "H".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & Hht & %Hok)".
    pose proof Hok as Hok'.
    destruct Hok' as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8).
    destruct (uart_tx_pop_rx u b u' H3 Hpop) as [Hrxe Hlbe].
    iExists hs, np, nk, hl, ht. iFrame "Ha Hk Hts Hht". iPureIntro.
    rewrite /uart_col_ok Hrxe Hlbe. split_and!; try assumption.
    rewrite (uart_tx_pop_wire u b u' Hpop) (uart_tx_pop_out u b u' Hpop) H3.
    by rewrite Hwo.
  Qed.

  (* THE PUSH (the device thread's rx arm), AS AN ACCESSOR.  The order the
     new history has to satisfy is decided against the MACHINE'S OWN
     history, which is why this takes [obs_auth h] -- the history BEFORE the
     event -- reads the column's top out against it, and hands the auth
     straight back so the trace permit can move it.  The wand that comes out
     is the push itself, at the history the permit then produced. *)
  Lemma uart_colE_push_acc (γ : uart_names) (u : uart_state) (h : list mobs) :
    uart_colE γ u -∗ obs_auth h -∗
      obs_auth h ∗
      (∀ (u' : uart_state) (b : bv 8),
         ⌜u_rx u' = (u_rx u ++ [b])%list⌝ -∗
         ⌜uart_loopback u' = uart_loopback u⌝ -∗
         (* an arrival touches neither end of the transmit pair *)
         ⌜u_wire u' = u_wire u⌝ -∗ ⌜u_out u' = u_out u⌝ -∗
         riscv_rx_tag (h ++ [ObsUartIn b])%list -∗
         obs_hist_lb (h ++ [ObsUartIn b])%list ==∗
         uart_colE γ u').
  Proof.
    iIntros "H Hauth".
    iDestruct "H" as (hs np nk hl ht) "(Ha & Hk & Hts & #Hht & %Hok)".
    (* the top is at or before the machine's current history *)
    iAssert (⌜ohist_le ht (Some h)⌝)%I as "%Htop".
    { destruct ht as [g|]; [| done]. cbn [obs_hist_lb_o].
      iDestruct (obs_hist_lb_prefix with "Hauth Hht") as %Hp.
      iPureIntro. exact Hp. }
    iFrame "Hauth".
    iIntros (u' b) "%Hrx %Hlbk %Hw %Ho #Htg #Hlbn".
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8).
    iMod (mono_nat_own_update (S np) with "Ha") as "[Ha _]"; [lia|].
    iModIntro.
    set (hn := (h ++ [ObsUartIn b])%list).
    (* every history the column holds is a prefix of [h], hence strictly
       before the new one *)
    assert (Hxall : forall (j : nat) (g : list mobs),
              hs !! j = Some g -> hist_ext g hn).
    { intros j g Hj.
      pose proof (H8 j g Hj) as Hg.
      assert (Hp : g `prefix_of` h).
      { destruct ht as [t|]; [| done]. cbn in Hg, Htop. by etrans. }
      exact (hist_ext_of_prefix g h hn Hp (hist_ext_snoc h (ObsUartIn b))). }
    iExists (hs ++ [hn])%list, (S np), nk, hl, (Some hn).
    iFrame "Ha Hk".
    iSplitL "Hts".
    { rewrite big_sepL_app. iFrame "Hts". cbn [big_opL].
      iSplitL; [| done]. iSplitR; [iExact "Htg" | iExact "Hlbn"]. }
    iSplitR; [iExact "Hlbn" |].
    iPureIntro. rewrite /uart_col_ok Hrx Hlbk Hw Ho !length_app H2 H3.
    cbn [length]. split_and!; [lia | lia | reflexivity | exact Hwo | | | | | ].
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
        exact (obs_ends_in_snoc h b).
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
                 (hist_ext_snoc h (ObsUartIn b))).
    - (* the anchor is at or before the NEW top *)
      exact (ohist_le_trans hl ht (Some hn) H7
               (ohist_le_trans ht (Some h) (Some hn) Htop
                  (proj1 (hist_ext_snoc h (ObsUartIn b))))).
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
  Qed.

  (* THE POLL: a non-empty FIFO means at least one more byte has been pushed
     than the token's holder has removed. *)
  Lemma uart_col_poll (γ : uart_names) (u : uart_state) (k : nat)
      (hl : option (list mobs)) :
    u_rx u <> [] ->
    uart_colE γ u -∗ uart_rx_tok γ k hl -∗
      uart_colE γ u ∗ uart_rx_tok γ k hl ∗ uart_rx_pushed_lb γ (S k).
  Proof.
    iIntros (Hne) "H Htok".
    iDestruct "H" as (hs np nk hl0 ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iDestruct (uart_rx_tok_agree with "Hk Htok") as %[<- <-].
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8).
    assert (Hle : (S nk <= np)%nat)
      by (destruct (u_rx u); [done | cbn [length] in H1; lia]).
    iDestruct (mono_nat_lb_own_get with "Ha") as "#Hlb".
    (* [uart_rx_tok] and [uart_rx_popped] are the same proposition, so the
       two halves must be placed by hand: [iFrame] would put the caller's
       token into the column's own slot. *)
    iSplitR "Htok".
    - iExists hs, np, nk, hl0, ht. iFrame "Ha Hk Hts Hht". iPureIntro.
      rewrite /uart_col_ok. split_and!; assumption.
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
  Lemma uart_col_pop (γ : uart_names) (u u' : uart_state) (k : nat)
      (hl : option (list mobs)) (bt : bv 8) :
    (forall b rx', u_rx u = b :: rx' ->
       bt = b /\ u_rx u' = rx' /\ uart_loopback u' = uart_loopback u) ->
    (* an RHR read is a [uart_read]: it moves neither end of the transmit
       pair ([ObsTrace.uart_read_wire], [DevModel.uart_read_stable]) *)
    u_wire u' = u_wire u ->
    u_out u' = u_out u ->
    uart_colE γ u -∗ uart_rx_tok γ k hl -∗ uart_rx_pushed_lb γ (S k) ==∗
      uart_colE γ u' ∗
      (∃ h, ⌜obs_ends_in h bt⌝ ∗ ⌜ohist_ext hl h⌝ ∗
            riscv_rx_tag h ∗ obs_hist_lb h ∗ uart_rx_tok γ (S k) (Some h)).
  Proof.
    iIntros (Hpop Hw Ho) "H Htok #Hlb".
    iDestruct "H" as (hs np nk hl0 ht) "(Ha & Hk & Hts & Hht & %Hok)".
    iDestruct (uart_rx_tok_agree with "Hk Htok") as %[<- <-].
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8).
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hge].
    destruct (u_rx u) as [| b rx'] eqn:Hrx.
    { cbn [length] in H1. lia. }
    destruct (Hpop b rx' eq_refl) as (-> & Hrx' & Hlb').
    destruct hs as [| hh hs']; [cbn [length] in H2; discriminate|].
    iDestruct "Hts" as "[[#Hth #Hlbh] Hts]".
    assert (Hhead : obs_ends_in hh b) by exact (H4 0%nat b hh eq_refl eq_refl).
    assert (Hanch : ohist_ext hl0 hh) by exact (H6 0%nat hh eq_refl).
    iMod (uart_rx_tok_update γ nk (S nk) hl0 (Some hh) with "Hk Htok")
      as "[Hk Htok]".
    iModIntro. iSplitR "Htok".
    - iExists hs', np, (S nk), (Some hh), ht. iFrame "Ha Hk Hts Hht".
      iPureIntro.
      rewrite /uart_col_ok Hrx' Hlb' Hw Ho. cbn [length] in H1, H2.
      split_and!; [lia | lia | exact H3 | exact Hwo | | | | |].
      + intros j c g Hj Hg. exact (H4 (S j) c g Hj Hg).
      + intros i j gi gj Hi Hj Hij.
        exact (H5 (S i) (S j) gi gj Hi Hj ltac:(lia)).
      + intros j g Hj. cbn.
        exact (H5 0%nat (S j) hh g eq_refl Hj ltac:(lia)).
      + exact (H8 0%nat hh eq_refl).
      + intros j g Hj. exact (H8 (S j) g Hj).
    - iExists hh. iFrame "Htok".
      iSplitR; [iPureIntro; exact Hhead |].
      iSplitR; [iPureIntro; exact Hanch |].
      iSplitR; [iExact "Hth" | iExact "Hlbh"].
  Qed.

  (* THE FLUSH: an FCR write that clears the receive FIFO is a pop of
     EVERYTHING, and needs the token for exactly that reason.  THE ANCHOR
     BECOMES THE TOP: the flushed bytes are gone, but the next byte to
     arrive must still be known to be newer than them, and the top is the
     one bound that dominates every history the column held. *)
  Lemma uart_colE_flush (γ : uart_names) (u u' : uart_state) (k : nat)
      (hl : option (list mobs)) :
    u_rx u' = [] ->
    uart_loopback u' = uart_loopback u ->
    (* an FCR write is a [uart_write]: it moves neither end of the transmit
       pair ([ObsTrace.uart_write_wire], [DevModel.uart_write_out]) *)
    u_wire u' = u_wire u ->
    u_out u' = u_out u ->
    uart_colE γ u -∗ uart_rx_tok γ k hl ==∗
      uart_colE γ u' ∗ ∃ k' hl', uart_rx_tok γ k' hl'.
  Proof.
    iIntros (Hrx Hlb Hw Ho) "H Htok".
    iDestruct "H" as (hs np nk hl0 ht) "(Ha & Hk & Hts & #Hht & %Hok)".
    iDestruct (uart_rx_tok_agree with "Hk Htok") as %[<- <-].
    destruct Hok as (H1 & H2 & H3 & Hwo & H4 & H5 & H6 & H7 & H8).
    iMod (uart_rx_tok_update γ nk np hl0 ht with "Hk Htok") as "[Hk Htok]".
    iModIntro. iSplitR "Htok"; [| iExists np, ht; iExact "Htok"].
    iExists [], np, np, ht, ht. iFrame "Ha Hk Hht".
    iSplitR; [done|].
    iPureIntro. rewrite /uart_col_ok Hrx Hlb Hw Ho H3.
    cbn [length]. split_and!; [lia | reflexivity | reflexivity | exact Hwo | | | | |].
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
  Definition dev_inv_body (γ : uart_names) (γd : disk_names) : iProp Σ :=
    (∃ (u : uart_state) (p : plic_state) (v : virtio_state),
       uart_frag u ∗ plic_frag p ∗ virtio_frag v ∗
       uart_ghosts γ u ∗ uart_colE γ u ∗ uart_preinit γ ∗
       virtio_proto γd v ∗
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
    (∃ u : uart_state, uart_frag u ∗ uart_ghosts γ u ∗ uart_colE γ u)%I.

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
  (*  The three tables are CONCRETE.  Only the UART has a payload -- the  *)
  (*  receive token, THE EXCLUSIVE RIGHT TO POP the receive FIFO -- so    *)
  (*  only the UART has a one-shot to run, and it is the [un_init] field  *)
  (*  [uart_names] already carries.  Every other source's slot is [emp]   *)
  (*  at every [p]: it is founded in its post-state at boot and survives  *)
  (*  every transition with nothing to prove.  Giving a second source a   *)
  (*  payload is three table rows, one ghost name, and an extra case in   *)
  (*  the two movers below; no statement outside this block moves.        *)
  (* ------------------------------------------------------------------ *)
  (* THE RIGHT TO POP, AND THE RIGHT TO STORE WHAT WAS POPPED.  The receive
     token alone is not a whole payload any more: the byte a hart pops has
     to be filed in the console ring, and the ring's own picture of "the
     newest byte I hold" must be known to be OLDER than the byte being
     filed.  So the payload carries the consumer's high-water half beside
     the token, with the pure clause that ties the two -- and that clause is
     re-established at every pop (the anchor moves forward) and at every
     store (the mark moves to the byte just filed). *)
  Definition uart_rx_writer (γ : uart_names) (k : nat)
      (hl : option (list mobs)) : iProp Σ :=
    (uart_rx_tok γ k hl ∗
     ∃ hh : option (list mobs), uart_rx_hi γ (1/2) hh ∗ ⌜ohist_le hh hl⌝)%I.

  Definition plic_payload_uart (γ : uart_names) : iProp Σ :=
    (∃ (k : nat) (hl : option (list mobs)), uart_rx_writer γ k hl)%I.

  Definition plic_payload (γ : uart_names) (i : N) : iProp Σ :=
    (if (i =? uart_irq_id)%N then plic_payload_uart γ else emp)%I.
  Definition plic_preinit (γ : uart_names) (i : N) : iProp Σ :=
    (if (i =? uart_irq_id)%N then uart_preinit γ else False)%I.
  Definition plic_inited (γ : uart_names) (i : N) : iProp Σ :=
    (if (i =? uart_irq_id)%N then uart_inited γ else emp)%I.

  Definition plic_slot (γ : uart_names) (p : plic_state) (i : N) : iProp Σ :=
    (plic_preinit γ i
     ∨ (plic_inited γ i ∗
        if p_claimed p i then emp else plic_payload γ i))%I.

  (* THE SOURCES THE INVARIANT TRACKS.  Not [plic_srcs] (DevModel.v: all
     ninety-five real ids): under [plic_ok] a claim can only ever return one
     of the machine's own two ([PlicPlan.plic_enabled_srcs], and
     [plic_claim_ret] on top of it), so this list already covers every source
     a claim can hand a payload for -- and the big-op is a two-element cons
     instead of a ninety-five-element fold. *)
  Definition plic_tracked : list N := [uart_irq_id; virtio_irq_id].

  Definition plic_slots (γ : uart_names) (p : plic_state) : iProp Σ :=
    ([∗ list] i ∈ plic_tracked, plic_slot γ p i)%I.

  (* A PAYLOAD-LESS SLOT IS FREE, at any state: both of its arms are [emp].
     This is what makes the big-op collapse to the UART's slot. *)
  Lemma plic_slot_other (γ : uart_names) (p : plic_state) (i : N) :
    (i =? uart_irq_id)%N = false -> ⊢ plic_slot γ p i.
  Proof.
    intros Hi.
    rewrite /plic_slot /plic_preinit /plic_inited /plic_payload Hi.
    iRight. iSplitR; [done|]. destruct (p_claimed p i); done.
  Qed.

  (* ...so the big-op IS the UART's slot, in both directions. *)
  Lemma plic_slots_uart (γ : uart_names) (p : plic_state) :
    plic_slots γ p -∗ plic_slot γ p uart_irq_id.
  Proof. rewrite /plic_slots /plic_tracked. iIntros "(Hu & _)". iExact "Hu". Qed.

  Lemma plic_slots_of_uart (γ : uart_names) (p : plic_state) :
    plic_slot γ p uart_irq_id -∗ plic_slots γ p.
  Proof.
    rewrite /plic_slots /plic_tracked. iIntros "Hu".
    iSplitL "Hu"; [iExact "Hu"|]. iSplitR; [| done].
    iApply (plic_slot_other γ p virtio_irq_id). vm_compute. reflexivity.
  Qed.

  (* THE UART SLOT, read and written.  [plic_slot] is a definition, so the
     proofmode needs these three to see its disjunction; they are also where
     the PRE-STATE IS REFUTED, which is the whole content of "a caller
     holding [uart_inited] never meets the left arm". *)
  Lemma plic_slot_uart_cases (γ : uart_names) (p : plic_state) :
    plic_slot γ p uart_irq_id -∗
      uart_preinit γ
      ∨ (uart_inited γ ∗
         if p_claimed p uart_irq_id then emp else plic_payload_uart γ).
  Proof. rewrite /plic_slot. iIntros "H". iExact "H". Qed.

  Lemma plic_slot_uart_intro (γ : uart_names) (p : plic_state) :
    uart_inited γ -∗
    (if p_claimed p uart_irq_id then emp else plic_payload_uart γ) -∗
    plic_slot γ p uart_irq_id.
  Proof.
    iIntros "#Hin Hpay". rewrite /plic_slot. iRight.
    iSplitR; [iExact "Hin"|]. iExact "Hpay".
  Qed.

  Lemma plic_slot_uart_elim (γ : uart_names) (p : plic_state) :
    uart_inited γ -∗ plic_slot γ p uart_irq_id -∗
    (if p_claimed p uart_irq_id then emp else plic_payload_uart γ).
  Proof.
    iIntros "#Hin Hu".
    iDestruct (plic_slot_uart_cases with "Hu") as "[Hpre | [_ Hpay]]".
    - iDestruct (uart_preinit_inited_False with "Hpre Hin") as %[].
    - iExact "Hpay".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  WHAT THE THREE PLIC TRANSITIONS DO TO THE SLOTS.                   *)
  (* ------------------------------------------------------------------ *)

  (* ANYTHING THAT LEAVES SERVICE ALONE leaves the slots alone: a latch, a
     priority write, an enable write, a threshold write. *)
  Lemma plic_slots_stable (γ : uart_names) (p p' : plic_state) :
    p_claimed p' uart_irq_id = p_claimed p uart_irq_id ->
    plic_slots γ p -∗ plic_slots γ p'.
  Proof.
    intros Hcl. iIntros "H". iDestruct (plic_slots_uart with "H") as "Hu".
    iApply plic_slots_of_uart. rewrite /plic_slot Hcl. iExact "Hu".
  Qed.

  (* A CLAIM TAKES THE PAYLOAD OUT of the slot it marks in service, and the
     handout is keyed by the id the claim RETURNS -- which is what lets a
     caller spend it without any fact about [plic_best]. *)
  Lemma plic_slots_claim (γ : uart_names) (p : plic_state) (c : nat) :
    plic_ok p ->
    uart_inited γ -∗ plic_slots γ p -∗
      plic_slots γ (snd (plic_claim p c)) ∗
      (⌜ fst (plic_claim p c) = Z_to_bv 32 (Z.of_N uart_irq_id) ⌝ -∗
         plic_payload_uart γ).
  Proof.
    intros Hok. iIntros "#Hin H".
    iDestruct (plic_slots_uart with "H") as "Hu".
    destruct (plic_best p c) as [i|] eqn:Hbest; last first.
    { (* nothing to serve: the state is unchanged and the id is 0 *)
      assert (Hsnd : snd (plic_claim p c) = p)
        by (unfold plic_claim; rewrite Hbest; reflexivity).
      assert (Hfst : fst (plic_claim p c) = Z_to_bv 32 0)
        by (unfold plic_claim; rewrite Hbest; reflexivity).
      rewrite Hsnd Hfst.
      iSplitL "Hu"; [by iApply plic_slots_of_uart|].
      iIntros (Hv). exfalso.
      apply (f_equal bv_unsigned) in Hv. vm_compute in Hv. discriminate. }
    destruct (plic_claim_serves p c i Hok Hbest) as [Hb Ha].
    destruct (decide (i = uart_irq_id)) as [->|Hne].
    - (* the UART: it was out of service, so the payload was in the slot, and
         it is in service now, so the slot is empty and the payload leaves *)
      iDestruct (plic_slot_uart_elim with "Hin Hu") as "Hpay".
      iEval (rewrite Hb) in "Hpay".
      iSplitR "Hpay".
      { iApply plic_slots_of_uart.
        iApply (plic_slot_uart_intro with "Hin"). rewrite Ha. done. }
      iIntros (_). iExact "Hpay".
    - (* some other source: the UART's service bit is untouched, and the id
         the claim returns is not the UART's *)
      assert (Hother : plic_best p c <> Some uart_irq_id).
      { rewrite Hbest. injection 1 as Hi. exact (Hne Hi). }
      assert (Hcl : p_claimed (snd (plic_claim p c)) uart_irq_id
                    = p_claimed p uart_irq_id)
        by exact (plic_claim_other_claimed p c uart_irq_id Hother).
      assert (Hfst : fst (plic_claim p c) = Z_to_bv 32 (Z.of_N i))
        by (unfold plic_claim; rewrite Hbest; reflexivity).
      iSplitL "Hu".
      { iApply plic_slots_of_uart. rewrite /plic_slot Hcl. iExact "Hu". }
      iIntros (Hv). exfalso. apply Hne.
      apply (plic_claim_uart_of_ret p c i Hok Hbest).
      rewrite -Hfst. exact Hv.
  Qed.

  (* ...and a completion puts it back. *)
  Lemma plic_slots_complete (γ : uart_names) (p : plic_state) (i : N) :
    uart_inited γ -∗ plic_slots γ p -∗
    (⌜ i = uart_irq_id ⌝ -∗ plic_payload_uart γ) -∗
    plic_slots γ (plic_complete p i).
  Proof.
    iIntros "#Hin H Htok".
    destruct (decide (i = uart_irq_id)) as [Heq|Hne].
    - iDestruct (plic_slots_uart with "H") as "Hu".
      iApply plic_slots_of_uart.
      assert (Hf : p_claimed (plic_complete p i) uart_irq_id = false).
      { rewrite Heq.
        exact (plic_complete_claimed_in p uart_irq_id
                 (proj1 uart_irq_id_range) (proj2 uart_irq_id_range)). }
      iApply (plic_slot_uart_intro with "Hin"). rewrite Hf.
      iApply "Htok". iPureIntro. exact Heq.
    - (* a completion of anything else leaves the UART's service bit alone *)
      iApply (plic_slots_stable γ p (plic_complete p i)
                (plic_complete_claimed_ne p i uart_irq_id ltac:(congruence))).
      iExact "H".
  Qed.

  (* THE PLIC INVARIANT: the fabric, the plan, and one slot per tracked
     source.  The boot chain founds the UART's slot in its pre-state and
     moves it to its post-state in ONE fupd ([uart_rx_tok_deposit]), which is
     also where the receive token is parked; every later PLIC access carries
     [uart_inited] and therefore never meets the pre-state again. *)
  Definition plic_inv_body (γ : uart_names) : iProp Σ :=
    (∃ p : plic_state, plic_frag p ∗ ⌜ plic_ok p ⌝ ∗ plic_slots γ p)%I.

  Definition disk_inv_body (γd : disk_names) : iProp Σ :=
    (∃ v : virtio_state,
       virtio_frag v ∗ virtio_proto γd v ∗ ⌜ virtio_isr_ok v ⌝)%I.

  Global Instance uart_inv_body_timeless γ : Timeless (uart_inv_body γ).
  Proof. rewrite /uart_inv_body. apply _. Qed.
  Global Instance plic_slot_timeless γ p i : Timeless (plic_slot γ p i).
  Proof.
    rewrite /plic_slot /plic_preinit /plic_inited /plic_payload
            /uart_preinit /uart_inited.
    destruct (i =? uart_irq_id)%N; destruct (p_claimed p i); apply _.
  Qed.
  Global Instance plic_slots_timeless γ p : Timeless (plic_slots γ p).
  Proof. rewrite /plic_slots. apply _. Qed.
  Global Instance plic_inv_body_timeless γ : Timeless (plic_inv_body γ).
  Proof. rewrite /plic_inv_body. apply _. Qed.
  Global Instance disk_inv_body_timeless γd : Timeless (disk_inv_body γd).
  Proof. rewrite /disk_inv_body. apply _. Qed.

  Definition uart_inv (γ : uart_names) : iProp Σ := inv uartN (uart_inv_body γ).
  Definition plic_inv (γ : uart_names) : iProp Σ := inv plicN (plic_inv_body γ).
  Definition disk_inv (γd : disk_names) : iProp Σ := inv diskN (disk_inv_body γd).

  Global Instance uart_inv_persistent γ : Persistent (uart_inv γ).
  Proof. rewrite /uart_inv. apply _. Qed.
  Global Instance plic_inv_persistent γ : Persistent (plic_inv γ).
  Proof. rewrite /plic_inv. apply _. Qed.
  Global Instance disk_inv_persistent γd : Persistent (disk_inv γd).
  Proof. rewrite /disk_inv. apply _. Qed.

  Lemma uart_inv_alloc E γ : uart_inv_body γ ={E}=∗ uart_inv γ.
  Proof. iIntros "Hbody". rewrite /uart_inv. by iApply inv_alloc. Qed.
  Lemma plic_inv_alloc E γ : plic_inv_body γ ={E}=∗ plic_inv γ.
  Proof. iIntros "Hbody". rewrite /plic_inv. by iApply inv_alloc. Qed.
  Lemma disk_inv_alloc E γd : disk_inv_body γd ={E}=∗ disk_inv γd.
  Proof. iIntros "Hbody". rewrite /disk_inv. by iApply inv_alloc. Qed.

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
  Definition dev_inv (γ : uart_names) (γd : disk_names) : iProp Σ :=
    (uart_inv γ ∗ plic_inv γ ∗ disk_inv γd ∗ perm_inv gen_id (dn_perm γd))%I.

  Global Instance dev_inv_persistent γ γd : Persistent (dev_inv γ γd).
  Proof. rewrite /dev_inv. apply _. Qed.

  (* the three projections out of the bundle.  A leaf that borrows the fabric
     takes [dev_inv] (unchanged statement) and projects the ONE half it
     touches; the projections are wands out of a persistent premise, so a
     leaf holding [dev_inv] in its intuitionistic context keeps it. *)
  Lemma dev_inv_uart γ γd : dev_inv γ γd -∗ uart_inv γ.
  Proof. iIntros "(#H & _ & _ & _)". iExact "H". Qed.
  Lemma dev_inv_plic γ γd : dev_inv γ γd -∗ plic_inv γ.
  Proof. iIntros "(_ & #H & _ & _)". iExact "H". Qed.
  Lemma dev_inv_disk γ γd : dev_inv γ γd -∗ disk_inv γd.
  Proof. iIntros "(_ & _ & #H & _)". iExact "H". Qed.
  (* THE CRASH-PERMIT CHANNEL rides the SAME bundle (PermInv.v), which is why
     no client spec statement changed when it landed: every driver proof that
     already threads [dev_inv] can open [permN] to deposit its permit at
     enqueue and to collect its receipt after the wake. *)
  Lemma dev_inv_perm γ γd : dev_inv γ γd -∗ perm_inv gen_id (dn_perm γd).
  Proof. iIntros "(_ & _ & _ & #H)". iExact "H". Qed.

  (* ... and the bundle allocation, at the EXISTING signature: the old
     ∃-triple body is split into the three per-device bodies. *)
  (* The permit body is a SEPARATE premise rather than a conjunct of
     [dev_inv_body]: that body carries a [Timeless] instance (it is what the
     three timeless per-device invariants are carved out of), and
     [perm_inv_body] is deliberately NOT timeless. *)
  (* THE ALLOCATION HANDS THE RECEIVE TOKEN OUT.  The UART's slot is founded
     in its PRE-STATE ([uart_preinit]) and every other tracked source's in
     its post-state with an [emp] payload, so the token itself goes to the
     boot chain, which threads it through consoleinit into uartinit's FCR
     flush and deposits it afterwards ([uart_rx_tok_deposit]). *)
  Lemma dev_inv_alloc E γ γd :
    dev_inv_body γ γd -∗ perm_inv_body gen_id (dn_perm γd) -∗
    uart_rx_tok γ 0 None ={E}=∗ dev_inv γ γd ∗ uart_rx_tok γ 0 None.
  Proof.
    iIntros "Hbody Hperm Htok". rewrite /dev_inv_body.
    iDestruct "Hbody" as (u p v)
      "(Hu & Hp & Hv & Hg & Hcol & Hpre & Hproto & %Hpok & %Hvok)".
    iMod (uart_inv_alloc E γ with "[Hu Hg Hcol]") as "#Huinv".
    { iExists u. iFrame "Hu Hg Hcol". }
    iMod (plic_inv_alloc E γ with "[Hp Hpre]") as "#Hpinv".
    { iExists p. iFrame "Hp". iSplitR; [iPureIntro; exact Hpok|].
      iApply plic_slots_of_uart. rewrite /plic_slot. iLeft. iExact "Hpre". }
    iMod (disk_inv_alloc E γd with "[Hv Hproto]") as "#Hdinv".
    { iExists v. iFrame "Hv Hproto". iPureIntro. exact Hvok. }
    iMod (perm_inv_alloc E gen_id (dn_perm γd) with "Hperm") as "#Hqinv".
    iModIntro. rewrite /dev_inv. iFrame "Huinv Hpinv Hdinv Hqinv Htok".
  Qed.

  (* THE DEPOSIT: the boot chain parks the token, in the ONE fupd that runs
     the UART slot's one-shot -- out of the pre-state, into the post-state
     with the payload.  main runs it between consoleinit and plicinit, and
     the [uart_inited] it mints is what every later PLIC access carries, so
     no one meets the pre-state again.

     THE SLOT'S [if] IS THE ONE PLACE the pre-state's silence about [p] is
     felt.  The pre-state says nothing at all about the PLIC state -- no
     "the UART is enabled nowhere" clause -- so [p_claimed p uart_irq_id =
     false] is not available here, and the (unreachable: nothing has enabled
     the UART's source yet, so no claim can have taken it) in-service branch
     parks [emp] and drops the token.  Nothing downstream is weakened by
     that: a claim hands out the payload only from an OUT-of-service slot,
     and this branch leaves the slot exactly as an in-service one must look. *)
  Lemma uart_rx_tok_deposit E γ (k : nat) (hl hh : option (list mobs)) :
    ↑plicN ⊆ E ->
    ohist_le hh hl ->
    plic_inv γ -∗ uart_rx_tok γ k hl -∗ uart_rx_hi γ (1/2) hh
      ={E}=∗ uart_inited γ.
  Proof.
    iIntros (Hmask Hle) "#Hpinv Htok Hhi".
    iInv "Hpinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (p) "(Hp & %Hpok & Hslots)".
    iDestruct (plic_slots_uart with "Hslots") as "Hu".
    iDestruct (plic_slot_uart_cases with "Hu") as "[Hpre | [#Hin Hrest]]".
    - iMod (uart_preinit_fire with "Hpre") as "#Hin".
      iMod ("Hclose" with "[Hp Htok Hhi]") as "_".
      { iNext. iExists p. iFrame "Hp". iSplitR; [iPureIntro; exact Hpok|].
        iApply plic_slots_of_uart.
        iApply (plic_slot_uart_intro with "Hin").
        destruct (p_claimed p uart_irq_id); [done |].
        rewrite /plic_payload_uart /uart_rx_writer.
        iExists k, hl. iFrame "Htok". iExists hh. iFrame "Hhi".
        iPureIntro. exact Hle. }
      by iModIntro.
    - (* the deposit has already run: the slot's own payload is the token's
         partner, so this one is spare and is simply dropped *)
      iMod ("Hclose" with "[Hp Hrest]") as "_".
      { iNext. iExists p. iFrame "Hp". iSplitR; [iPureIntro; exact Hpok|].
        iApply plic_slots_of_uart.
        iApply (plic_slot_uart_intro with "Hin"). iExact "Hrest". }
      iModIntro. iFrame "Hin".
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
    u_rx u = [] ->
    uart_loopback u = false ->
    (* ...AND NOTHING HAS BEEN DRIVEN ON THE WIRE THAT IS NOT DRAINED: at
       power-on both lists are empty ([DevModel.uart0_state]), which is the
       base case of the column's wire/out clause. *)
    u_wire u = u_out u ->
    ⊢ |==> ∃ γ, uart_sent_auth γ u ∗ uart_out_auth γ u ∗
                uart_tx_auth γ u ∗ uart_dlab_auth γ u ∗
                uart_tx_own γ (uart_acc u) ∗ uart_sent γ (uart_acc u) ∗
                uart_dlab_is γ (DfracOwn (1/2)) (uart_dlab u) ∗
                (* the receive side: the column at an empty FIFO, the token
                   the boot chain carries, and the one-shot the PLIC
                   invariant's pre-deposit arm holds *)
                uart_colE γ u ∗ uart_rx_tok γ 0 None ∗
                uart_rx_hi γ (1/2) None ∗ uart_rx_hi γ (1/2) None ∗
                uart_preinit γ.
  Proof.
    intros Hrx Hlb Hwo.
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
    iModIntro. iExists (UartNames γa γb γc γd γpu γpo γhi γin).
    rewrite /uart_sent_auth /uart_out_auth /uart_tx_auth /uart_tx_own
            /uart_dlab_auth /uart_dlab_is /uart_sent /uart_colE /uart_col
            /uart_rx_tok /uart_rx_popped /uart_rx_hi /uart_preinit /=.
    iFrame "Ha Hb Hc1 Hd1 Hc2 Hsent Hd2".
    (* the column's own half of the pop counter and the caller's token are
       the SAME proposition, so the rest are placed by hand *)
    iSplitR "Hpo2 Hhi1 Hhi2 Hin".
    { iExists [], 0%nat, 0%nat, None, None. iFrame "Hpu Hpo1".
      iSplitR; [done|]. iSplitR; [done|].
      iPureIntro. rewrite /uart_col_ok Hrx Hlb. cbn [length].
      split_and!; [done | done | done | exact Hwo | intros j b h Hj; done
                  | intros i j hi hj Hi; done | intros j h Hj; done
                  | exact I | intros j h Hj; done]. }
    iSplitL "Hpo2"; [iExact "Hpo2" |].
    iSplitL "Hhi1"; [iExact "Hhi1" |].
    iSplitL "Hhi2"; [iExact "Hhi2" | iExact "Hin"].
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
    | [ObsUartIn _] => riscv_rx_tag (h ++ κ)%list
    | _ => emp
    end%I.

  Global Instance uart_tag_of_persistent h κ : Persistent (uart_tag_of h κ).
  Proof.
    rewrite /uart_tag_of. destruct κ as [|k κ']; [apply _|].
    destruct k; destruct κ'; apply _.
  Qed.

  (* at the trivial family every arm's tag is free *)
  Lemma uart_tag_of_triv (h κ : list mobs) :
    riscv_rx_tag = rx_tag_triv -> ⊢ uart_tag_of h κ.
  Proof.
    intros Htag. rewrite /uart_tag_of.
    destruct κ as [|k κ']; [done|].
    destruct k; destruct κ'; try done.
    rewrite Htag /rx_tag_triv. done.
  Qed.

  Definition uart_obs_permit (γ : uart_names) : iProp Σ :=
    (□ ∀ (h κ : list mobs) (d : dev_state) (u' : uart_state),
       ⌜uart_step d κ (set_duart d u')⌝ -∗ ⌜trace_shape h true⌝ -∗
       ⌜obs_wire (open_seg h) = u_wire (duart d)⌝ -∗
       uart_ghosts γ u' -∗ obs_auth h ={⊤ ∖ ↑uartN}=∗
       uart_ghosts γ u' ∗ obs_auth (h ++ κ)%list ∗ uart_tag_of h κ)%I.

  Lemma uart_obs_permit_triv (γ : uart_names) :
    riscv_obs_pred = obs_pred_triv ->
    (* the trivial application claims nothing of its input, so the tag the rx
       arm owes is [True] and the permit can mint it out of nothing *)
    riscv_rx_tag = rx_tag_triv ->
    obs_inv -∗ uart_obs_permit γ.
  Proof.
    intros Heq Htag. iIntros "#Hoinv !>" (h κ d u') "%Hstep %Hsh %Hwire Hg Hauth".
    iInv "Hoinv" as "HP" "Hclose".
    iEval (rewrite Heq /obs_pred_triv) in "HP".
    iDestruct "HP" as (h') ">Hfrag".
    iDestruct (obs_agree with "Hauth Hfrag") as %<-.
    iMod (obs_update _ (h ++ κ)%list (ex_intro _ κ eq_refl)
            with "Hauth Hfrag") as "[Hauth Hfrag]".
    iMod ("Hclose" with "[Hfrag]") as "_".
    { iNext. rewrite Heq /obs_pred_triv. iExists (h ++ κ)%list. iExact "Hfrag". }
    iModIntro. iFrame "Hg Hauth". iApply uart_tag_of_triv. exact Htag.
  Qed.

  (* THE PERMIT FROM A LEDGER (uart-trace.md phase 4).  The client's trace
     predicate is [obs_ledger R], and its two wands are the whole
     obligation: at the tx arm, with the byte that reached the wire (NOT
     under LOOP, which emits nothing); at the rx arm, with the ENVIRONMENT's
     byte -- each with the device ghosts after the step and the two machine
     facts in hand, at a mask that lets the wand open the crash invariant
     too.  Coq-level hypotheses, so the system theorem can pass its own
     down; [R] timeless, so the ledger's later strips. *)
  Lemma uart_obs_permit_ledger (R : list mobs -> iProp Σ)
      (Tg : list mobs -> iProp Σ) (γ : uart_names)
      (HRt : forall h, Timeless (R h))
      (Heq : riscv_obs_pred = obs_ledger R)
      (* the tag family the record carries IS the client's, which is what
         lets the rx wand below discharge the permit's tag output *)
      (Htag : riscv_rx_tag = Tg)
      (Htx : ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
               ⌜uart_tx_pop u = Some (b, u')⌝ -∗ ⌜uart_loopback u = false⌝ -∗
               ⌜trace_shape h true⌝ -∗ ⌜obs_wire (open_seg h) = u_wire u⌝ -∗
               uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
               uart_ghosts γ u' ∗ R (h ++ [ObsUartOut b])%list))
      (Hrx : ⊢ □ (∀ (h : list mobs) (b : bv 8) (u u' : uart_state),
               ⌜uart_rx_push u b = Some u'⌝ -∗ ⌜trace_shape h true⌝ -∗
               uart_ghosts γ u' -∗ R h ={⊤ ∖ ↑uartN ∖ ↑obsN}=∗
               uart_ghosts γ u' ∗ R (h ++ [ObsUartIn b])%list ∗
               Tg (h ++ [ObsUartIn b])%list)) :
    obs_inv -∗ uart_obs_permit γ.
  Proof.
    iIntros "#Hoinv". iPoseProof Htx as "#Htx". iPoseProof Hrx as "#Hrx".
    iIntros "!>" (h κ d u') "%Hstep %Hsh %Hwire Hg Hauth".
    iInv "Hoinv" as "HP" "Hclose".
    iEval (rewrite Heq /obs_ledger) in "HP".
    iDestruct "HP" as (h') "[>Hfrag >HR]".
    iDestruct (obs_agree with "Hauth Hfrag") as %<-.
    remember (set_duart d u') as d' eqn:Hd'.
    destruct Hstep as [b u0 Htx0 | b u0 Hrx0 | p' _ _ |].
    - (* a byte left the transmitter *)
      unfold set_duart in Hd'. injection Hd' as ->.
      destruct (uart_loopback (duart d)) eqn:Hlb.
      + (* under LOOP nothing reached the wire: no event *)
        iMod ("Hclose" with "[Hfrag HR]") as "_".
        { iNext. rewrite Heq /obs_ledger. iExists h. iFrame. }
        iModIntro. rewrite app_nil_r. iFrame "Hg Hauth"; try done.
      + iMod ("Htx" $! h b (duart d) _ with "[//] [//] [//] [//] Hg HR")
          as "[Hg HR]".
        iMod (obs_update _ (h ++ [ObsUartOut b])%list
                (ex_intro _ [ObsUartOut b] eq_refl) with "Hauth Hfrag")
          as "[Hauth Hfrag]".
        iMod ("Hclose" with "[Hfrag HR]") as "_".
        { iNext. rewrite Heq /obs_ledger. iExists _. iFrame. }
        iModIntro. iFrame "Hg Hauth"; try done.
    - (* a byte arrived from the outside world: the ONE arm with a tag *)
      unfold set_duart in Hd'. injection Hd' as ->.
      iMod ("Hrx" $! h b (duart d) _ with "[//] [//] Hg HR")
        as "(Hg & HR & Htg)".
      iMod (obs_update _ (h ++ [ObsUartIn b])%list
              (ex_intro _ [ObsUartIn b] eq_refl) with "Hauth Hfrag")
        as "[Hauth Hfrag]".
      iMod ("Hclose" with "[Hfrag HR]") as "_".
      { iNext. rewrite Heq /obs_ledger. iExists _. iFrame. }
      iModIntro. iFrame "Hg Hauth". rewrite /uart_tag_of Htag. iExact "Htg".
    - (* the latch: silent *)
      iMod ("Hclose" with "[Hfrag HR]") as "_".
      { iNext. rewrite Heq /obs_ledger. iExists h. iFrame. }
      iModIntro. rewrite app_nil_r. iFrame "Hg Hauth"; try done.
    - (* the stutter: silent *)
      iMod ("Hclose" with "[Hfrag HR]") as "_".
      { iNext. rewrite Heq /obs_ledger. iExists h. iFrame. }
      iModIntro. rewrite app_nil_r. iFrame "Hg Hauth"; try done.
  Qed.

  Lemma wp_uart_loop γ :
    gen_cert -∗ uart_inv γ -∗ plic_inv γ -∗ uart_obs_permit γ -∗
    WP (UartLoop : expr riscv_lang).
  Proof.
    iIntros "#Hcert #Huinv #Hpinv #Hperm".
    iLöb as "IH".
    iApply (wp_uart_step with "Hcert").
    iIntros (gr m d h Hsh Hwire) "(Hgr & Hmem & Hdev & Hoauth)".
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
      iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
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
      (* THE TRACE STEP: the client moves the history by the output event
         (nothing under LOOP -- the arm's own [κ]) *)
      iAssert (uart_ghosts γ u') with "[Hacc Hout Htx Hdl]" as "Hg".
      { rewrite /uart_ghosts. iFrame. }
      (* the tx arm's tag output is [emp] ([uart_tag_of] mints one only for
         an rx event), so the column takes nothing here. *)
      iMod ("Hperm" $! h _ d u' with "[//] [//] [//] Hg Hoauth")
        as "(Hg & Hoauth & _)".
      (* THE COLUMN: with LOOP off ([uart_col]'s own clause, read off the
         state the invariant is at) the drain does not touch [u_rx] at all;
         under LOOP it would re-enter the receiver with no observation, which
         is why the clause is there. *)
      iDestruct (uart_colE_tx_pop γ u u' _ Htx0 with "Hcol") as "Hcol".
      iMod ("Hclose" with "[Hu' Hg Hcol]") as "_".
      { iNext. iExists u'. iFrame. }
      iModIntro. iFrame "Hgr Hmem Hdev' Hoauth". iApply "IH".
    - (* a byte arrives from the outside world: rx only, trace untouched *)
      iInv "Huinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
      iDestruct (dev_interp_agree_uart with "Hdev Hu") as %Hu.
      rewrite Hu in Hrx.
      iMod (dev_interp_update_uart _ u u' with "Hdev Hu") as "[Hdev' Hu']".
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
      iDestruct (uart_colE_push_acc γ u h with "Hcol Hoauth")
        as "[Hoauth Hpush]".
      iMod ("Hperm" $! h [ObsUartIn b] d u' with "[//] [//] [//] Hg Hoauth")
        as "(Hg & Hoauth & #Htg)".
      iDestruct (obs_auth_lb with "Hoauth") as "[Hoauth #Hlbn]".
      (* THE COLUMN: the byte goes on the tail of [u_rx] and its history --
         which ends with exactly this event -- on the tail of the column. *)
      destruct (uart_rx_push_rx u b u' Hrx) as [Hrxe Hlbe].
      pose proof (uart_rx_push_wire u b u' Hrx) as Hwe.
      pose proof (uart_rx_push_out u b u' Hrx) as Hoe.
      iMod ("Hpush" $! u' b with "[//] [//] [//] [//] Htg Hlbn") as "Hcol".
      iMod ("Hclose" with "[Hu' Hg Hcol]") as "_".
      { iNext. iExists u'. iFrame. }
      iModIntro. iFrame "Hgr Hmem Hdev' Hoauth". iApply "IH".
    - (* the gateway latches the UART's interrupt level.  This is the ONE
         UART transition that touches the PLIC, and it touches nothing else,
         so only [plicN] is opened. *)
      iInv "Hpinv" as ">Hbody" "Hclose".
      iDestruct "Hbody" as (p) "(Hp & %Hpok & Harm)".
      iDestruct (dev_interp_agree_plic with "Hdev Hp") as %Hp.
      iMod (dev_interp_update_plic _ p p' with "Hdev Hp") as "[Hdev' Hp']".
      assert (Hlat : plic_latch p uart_irq_id = Some p')
        by (rewrite <- Hp; exact Hlatch).
      (* the gateway sets a PENDING bit and touches no service bit, so every
         slot survives it *)
      pose proof (plic_latch_claimed p p' uart_irq_id Hlat) as Hcl'.
      iMod ("Hclose" with "[Hp' Harm]") as "_".
      { iNext. iExists p'. iFrame "Hp'".
        iSplitR; [iPureIntro; exact (plic_ok_latch p p' uart_irq_id Hlat Hpok)|].
        iApply (plic_slots_stable _ p p' (Hcl' uart_irq_id)). iExact "Harm". }
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
  Lemma wp_disk_loop (γu : uart_names) γd :
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
    plic_inv γu -∗
    WP (DiskLoop : expr riscv_lang).
  Proof.
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
        iApply (plic_slots_stable _ p p' (Hcl' uart_irq_id)). iExact "Harm". }
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
  Lemma wp_plic_loop (γu : uart_names) :
    gen_cert -∗ plic_inv γu -∗ wire_inv -∗
    WP (PlicLoop : expr riscv_lang).
  Proof.
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
