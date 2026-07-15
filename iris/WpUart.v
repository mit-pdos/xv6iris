(* WpUart.v -- reasoning about the UART + PLIC device fabric (DevModel.v).

   Contents:
   §1  per-hart register ownership [reg_pointsto_at] (the [↦ᵣ]-analogue for a
       NON-ambient hart) + its bridge lemmas + [gregs_interp_acc_at]: the
       device thread's wire step writes ANOTHER hart's [sig_seip], so it needs
       the per-hart bridge that the ambient-[CpuId] API hides.
   §2  device-fabric ghost bridges: agreement/update of the [uart_frag]/
       [plic_frag] halves against [dev_interp].
   §3  MMIO transaction leaves: [dev_read]/[dev_write] reductions for the
       UART registers xv6 touches, and the [exec]-level towers
       (read_ram/write_ram -> checked_mem_read/write -> mem_read/
       mem_write_value) for a 1-byte device access in Machine mode --
       the device twins of WpLoad.v / WpGprStore.v's RAM towers.
   §4  the DEVICE THREAD: [wp_dev_loop] -- the [DevLoop] execution context
       runs forever under an invariant owning the device halves and every
       hart's [sig_seip] wire.  This is the shape of every future
       driver-vs-device proof: CPU-side WPs and the device loop share
       [dev_inv]-style invariants.
   §5  the interrupt chain, as pure facts: UART rx-avail raises the level
       ([uart_irq]), the gateway latches it ([plic_latch]), the latched
       source drives the hart's EIP wire ([plic_eip_uart]), and a high
       [sig_seip] wire makes the S-mode dispatch fire
       ([s_dispatch_seip_fires], against WpIntrCore's [s_dispatch]). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
(* re-import the model AFTER Base so the model's names (read_kind/Read_plain/
   write_kind/...) win over SailStdpp's homonyms -- same order as WpLoad.v. *)
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import WpIntrCore.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1  per-hart register ownership.                                       *)
(* ===================================================================== *)

Section RegAt.
  Context `{!riscvGS Σ}.

  (* [r ↦ᵣ v] for an EXPLICIT hart [c] (the ambient-[CpuId] [reg_pointsto]
     is [reg_pointsto_at cpu_id]). *)
  Definition reg_pointsto_at (c : CPU) (r : register) (dq : dfrac)
      (v : type_of_register r) : iProp Σ :=
    ghost_map_elem (cpu_reg_name c) r dq (existT r v).

  Lemma reg_valid_at (c : CPU) rs r dq v :
    reg_interp_at (cpu_reg_name c) rs -∗ reg_pointsto_at c r dq v -∗
    ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto_at /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  Lemma reg_update_at (c : CPU) rs r v v' :
    reg_interp_at (cpu_reg_name c) rs -∗ reg_pointsto_at c r (DfracOwn 1) v ==∗
      reg_interp_at (cpu_reg_name c) (register_set r v' rs) ∗
      reg_pointsto_at c r (DfracOwn 1) v'.
  Proof.
    rewrite /reg_pointsto_at /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iMod (ghost_map_update (existT r v') with "Hm Hr") as "[Hm $]".
    iModIntro. iExists (<[r := existT r v']> m). iFrame "Hm".
    iPureIntro. intros k dv Hk.
    destruct (decide (k = r)) as [->|Hne].
    - rewrite lookup_insert in Hk. injection Hk as <-.
      by rewrite register_lookup_set.
    - rewrite lookup_insert_ne in Hk; [|done].
      rewrite (Hag k dv Hk).
      by rewrite (irrelevant_register_set k r rs v' (register_beq_false k r Hne)).
  Qed.

  (* focus an ARBITRARY hart [c]'s register bridge out of the global one
     (the ambient [gregs_interp_acc] fixed [c := cpu_id]). *)
  Lemma gregs_interp_acc_at (c : CPU) (gr : CPU -> regstate) :
    gregs_interp gr ⊢ reg_interp_at (cpu_reg_name c) (gr c) ∗
      (∀ rs', reg_interp_at (cpu_reg_name c) rs' -∗ gregs_interp (<[c := rs']> gr)).
  Proof.
    rewrite /gregs_interp.
    iIntros "H".
    iDestruct (big_sepS_delete _ _ c with "H") as "[Hcur Hrest]";
      [ apply elem_of_fin_to_set |].
    iFrame "Hcur".
    iIntros (rs') "Hrs'".
    iApply (big_sepS_delete _ _ c); [ apply elem_of_fin_to_set |].
    rewrite /insert /greg_insert decide_True //.
    iFrame "Hrs'".
    iApply (big_sepS_mono with "Hrest").
    intros cpu Hcpu. apply elem_of_difference in Hcpu as [_ Hne].
    rewrite decide_False; [ done | ].
    intros ->. apply Hne, elem_of_singleton. reflexivity.
  Qed.
End RegAt.

(* ===================================================================== *)
(* §2  device-fabric ghost bridges.                                       *)
(* ===================================================================== *)

Section DevGhost.
  Context `{!riscvGS Σ}.

  Lemma dev_interp_agree d u p :
    dev_interp d -∗ uart_frag u -∗ plic_frag p -∗ ⌜duart d = u /\ dplic d = p⌝.
  Proof.
    iIntros "[Hua Hpa] Hu Hp".
    iDestruct (uart_agree with "Hua Hu") as %->.
    iDestruct (plic_agree with "Hpa Hp") as %->.
    done.
  Qed.

  Lemma dev_interp_update d u p u' p' :
    dev_interp d -∗ uart_frag u -∗ plic_frag p ==∗
      dev_interp (DevState u' p') ∗ uart_frag u' ∗ plic_frag p'.
  Proof.
    iIntros "[Hua Hpa] Hu Hp".
    iMod (uart_update with "Hua Hu") as "[$ $]".
    iMod (plic_update with "Hpa Hp") as "[$ $]".
    done.
  Qed.

  (* uart-only update (the plic component rides along) *)
  Lemma dev_interp_update_uart d u u' :
    dev_interp d -∗ uart_frag u ==∗ dev_interp (set_duart d u') ∗ uart_frag u'.
  Proof.
    iIntros "[Hua Hpa] Hu".
    iMod (uart_update with "Hua Hu") as "[$ $]".
    rewrite /set_duart /dev_interp /=. by iFrame "Hpa".
  Qed.

  Lemma dev_interp_update_plic d p p' :
    dev_interp d -∗ plic_frag p ==∗ dev_interp (set_dplic d p') ∗ plic_frag p'.
  Proof.
    iIntros "[Hua Hpa] Hp".
    iMod (plic_update with "Hpa Hp") as "[$ $]".
    rewrite /set_dplic /dev_interp /=. by iFrame "Hua".
  Qed.
End DevGhost.

(* ===================================================================== *)
(* §3  MMIO transaction leaves.                                           *)
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

(* checked_mem_read of one byte from the device fabric *)
Lemma exec_checked_mem_read_dev_1 (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (b : bv 8) (d' : dev_state) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_readable) = true ->
  exec (within_clint (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_htif_readable (Physaddr pa) 1) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_read s.(mdev) pa 1 = Some (b, d') ->
  exec (checked_mem_read (Load Data) pbmt Machine (Physaddr pa) 1 false false false false)
       s = Some (Ok (b, default_meta), MState s.(sregs) s.(mem) d').
Proof.
  intros Hpmp Hmatch Hread Hc Hsig Hh Hdev Hrd.
  unfold checked_mem_read.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_dev_load_1 pa pbmt region s Hmatch Hread)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_readable (Physaddr pa) 1) s = Some (false, s))).
  2:{ unfold within_mmio_readable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (read_kind_of_flags _ _ _) s = Some (Read_plain, s))).
  2:{ unfold read_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_dev_1 pa b d' s Hdev Hrd)).
  apply exec_returnM.
Qed.

(* checked_mem_write of one byte to the device fabric *)
Lemma exec_checked_mem_write_dev_1 (pbmt : page_based_mem_type) (pa : Arch.pa)
    (region : PMA_Region) (data : bv 8) (d' : dev_state) s :
  (forall i, pmpAddrMatchType_encdec_backwards
               (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) i))
             = OFF) ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr pa) 1
    = Some region ->
  (override_PMA (PMA_Region_attributes region) pbmt).(PMA_writable) = true ->
  exec (within_clint (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_sig (Physaddr pa) 1) s = Some (false, s) ->
  exec (within_htif_writable (Physaddr pa) 1) s = Some (false, s) ->
  dev_addr pa = true ->
  dev_write s.(mdev) pa 1 data = Some d' ->
  exec (checked_mem_write (Physaddr pa) 1 data (Store Data) pbmt Machine tt false false false)
       s = Some (Ok true, MState s.(sregs) s.(mem) d').
Proof.
  intros Hpmp Hmatch Hwrite Hc Hsig Hh Hdev Hwr.
  unfold checked_mem_write.
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (phys_access_check _ _ _ _ _ _) s = Some (None, s))).
  2:{ unfold phys_access_check.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmpCheck_machine_none _ _ _ s Hpmp)).
      cbn match.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_pmaCheck_dev_store_1 pa pbmt region s Hmatch Hwrite)).
      cbn match. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _
            (_ : exec (within_mmio_writable (Physaddr pa) 1) s = Some (false, s))).
  2:{ unfold within_mmio_writable. cbn [get_config_rvfi].
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
      rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
      rewrite (exec_and_boolM_Some _ _ _ _ _ Hh). cbn match. reflexivity. }
  rewrite (exec_bind_Some _ _ _ _ _ (_ : exec (write_kind_of_flags _ _ _) s = Some (Write_plain, s))).
  2:{ unfold write_kind_of_flags. apply exec_returnM. }
  rewrite (exec_bind_Some _ _ _ _ _ (exec_write_dev_1 pa data d' s Hdev Hwr)).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* §4  the device thread: [DevLoop] runs forever under the device          *)
(*     invariant.                                                          *)
(* ===================================================================== *)

Section DevLoop.
  Context `{!riscvGS Σ}.

  Definition devN : namespace := nroot .@ "dev".

  (* the device invariant: the device halves + every hart's [sig_seip] wire.
     Owning the wires HERE is the design point: the PLIC may flip a hart's
     external-interrupt pin at any time, so no CPU-side proof may pin it. *)
  Definition dev_inv_body : iProp Σ :=
    (∃ (u : uart_state) (p : plic_state) (line : CPU -> mword 1),
       uart_frag u ∗ plic_frag p ∗
       [∗ set] c ∈ (fin_to_set CPU : gset CPU),
         reg_pointsto_at c sig_seip (DfracOwn 1) (line c))%I.

  Global Instance uart_frag_timeless u : Timeless (uart_frag u).
  Proof. rewrite /uart_frag. apply _. Qed.
  Global Instance plic_frag_timeless p : Timeless (plic_frag p).
  Proof. rewrite /plic_frag. apply _. Qed.
  Global Instance reg_pointsto_at_timeless c r dq v :
    Timeless (reg_pointsto_at c r dq v).
  Proof. rewrite /reg_pointsto_at. apply _. Qed.
  Global Instance dev_inv_body_timeless : Timeless dev_inv_body.
  Proof. rewrite /dev_inv_body. apply _. Qed.

  Lemma wp_dev_loop E Φ :
    ↑devN ⊆ E ->
    inv devN dev_inv_body ⊢ WP (DevLoop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN) "#Hinv".
    iLöb as "IH".
    iApply wp_dev_step.
    iIntros (gr d) "[Hgr Hdev]".
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u p line) "(Hu & Hp & Hwires)".
    iDestruct (dev_interp_agree with "Hdev Hu Hp") as %[Hu Hp].
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iNext. iIntros (d' gr' Hstep).
    iMod "Hmask" as "_".
    destruct Hstep as [b u' Htx | b u' Hrx | p' Hirq Hlatch | c].
    - (* a byte leaves the tx FIFO *)
      iMod (dev_interp_update_uart _ u u' with "Hdev Hu") as "[Hdev' Hu']".
      iMod ("Hclose" with "[Hu' Hp Hwires]") as "_".
      { iNext. iExists u', p, line. iFrame. }
      iModIntro. iFrame "Hgr Hdev'". iApply "IH".
    - (* a byte arrives from the outside world *)
      iMod (dev_interp_update_uart _ u u' with "Hdev Hu") as "[Hdev' Hu']".
      iMod ("Hclose" with "[Hu' Hp Hwires]") as "_".
      { iNext. iExists u', p, line. iFrame. }
      iModIntro. iFrame "Hgr Hdev'". iApply "IH".
    - (* the gateway latches the UART's interrupt level *)
      iMod (dev_interp_update_plic _ p p' with "Hdev Hp") as "[Hdev' Hp']".
      iMod ("Hclose" with "[Hu Hp' Hwires]") as "_".
      { iNext. iExists u, p', line. iFrame. }
      iModIntro. iFrame "Hgr Hdev'". iApply "IH".
    - (* the PLIC drives hart [c]'s sig_seip wire *)
      iDestruct (gregs_interp_acc_at c with "Hgr") as "[Hrc Hback]".
      iDestruct (big_sepS_delete _ _ c with "Hwires") as "[Hwc Hwrest]";
        [ apply elem_of_fin_to_set |].
      iMod (reg_update_at c (gr c) sig_seip (line c)
              (bool_to_bit (dev_seip d (fin_to_nat c))) with "Hrc Hwc")
        as "[Hrc' Hwc']".
      iDestruct ("Hback" with "Hrc'") as "Hgr'".
      set (line' := fun c' : CPU =>
             if decide (c' = c) then bool_to_bit (dev_seip d (fin_to_nat c))
             else line c').
      iMod ("Hclose" with "[Hu Hp Hwc' Hwrest]") as "_".
      { iNext. iExists u, p, line'. iFrame "Hu Hp".
        iApply (big_sepS_delete _ _ c); [ apply elem_of_fin_to_set |].
        iSplitL "Hwc'".
        { rewrite /line' decide_True //. }
        iApply (big_sepS_mono with "Hwrest").
        intros c' Hc'. apply elem_of_difference in Hc' as [_ Hne].
        rewrite /line' decide_False; [ done | ].
        intros ->. apply Hne, elem_of_singleton. reflexivity. }
      iModIntro. iFrame "Hgr' Hdev". iApply "IH".
  Qed.
End DevLoop.

(* ===================================================================== *)
(* §5  the interrupt chain, end to end (pure facts).                       *)
(* ===================================================================== *)

(* (1) receive data + rx interrupts enabled => the UART raises its level *)
Lemma uart_irq_rx (u : uart_state) :
  Z.testbit (bv_unsigned (u_ier u)) 0 = true ->
  u_rx u <> [] ->
  uart_irq u = true.
Proof.
  intros Hier Hrx. unfold uart_irq, uart_rx_int, uart_rx_ready.
  rewrite Hier. destruct (u_rx u); [congruence | reflexivity].
Qed.

(* (2) the gateway latches a raised level (unless already pending/claimed) *)
Lemma plic_latch_pending (p p' : plic_state) :
  plic_latch p = Some p' -> p_pending p' uart_irq_id = true.
Proof.
  unfold plic_latch. intros H.
  destruct (negb (p_pending p uart_irq_id) && negb (p_claimed p uart_irq_id));
    [ injection H as <- | discriminate ].
  reflexivity.
Qed.

(* (3) a pending, enabled, above-threshold source drives the hart's EIP wire *)
Lemma plic_eip_uart (p : plic_state) (h : nat) :
  p_pending p uart_irq_id = true ->
  plic_enabled p h uart_irq_id = true ->
  0 < bv_unsigned (p_prio p uart_irq_id) ->
  bv_unsigned (p_thresh p h) < bv_unsigned (p_prio p uart_irq_id) ->
  plic_eip p h = true.
Proof.
  intros Hpend Hen Hprio Hthr.
  unfold plic_eip. apply existsb_exists.
  exists uart_irq_id. split.
  - unfold plic_srcs, plic_nsrc, uart_irq_id.
    apply in_map_iff. exists 10%nat. split; [reflexivity|].
    apply in_seq. lia.
  - unfold plic_cand. rewrite Hpend Hen.
    rewrite (proj2 (Z.ltb_lt _ _) Hprio) (proj2 (Z.ltb_lt _ _) Hthr).
    reflexivity.
Qed.

(* (4) a high sig_seip wire fires the S-mode dispatch: with xv6's interrupt
   configuration (mie = SSIE|STIE|SEIE = 0x222, mideleg = 0xffff, nothing
   else pending) and sstatus.SIE = 1, WpIntrCore's [s_dispatch] -- the
   proven dispatch function of one try_step cycle -- returns the
   supervisor-external interrupt. *)
Lemma s_dispatch_seip_fires (ms : mword 64) :
  eq_vec (_get_Mstatus_SIE ms) ('b"1" : mword 1) = true ->
  s_dispatch (zeros' 64) ('b"0") ('b"1")
             (mword_of_int 0x222) (mword_of_int 0xffff) ms
    = Some (I_S_External, Supervisor).
Proof.
  intros Hsie.
  unfold s_dispatch.
  rewrite Hsie.
  vm_compute. reflexivity.
Qed.
