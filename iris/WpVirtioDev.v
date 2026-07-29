(* WpVirtioDev.v -- the width-4 virtio-mmio LOAD and STORE weakest-precondition
   leaves for code that runs while the DEVICE INVARIANT is live.

   These are the [dev_inv]-BORROWING cousins of WpVirtioMmio.v's raw-fragment
   leaves.  [virtio_disk_init] owns [virtio_frag v] outright (it resets the
   device, which no invariant could tolerate); every LATER driver access --
   [virtio_disk_intr]'s INTERRUPT_STATUS read and INTERRUPT_ACK write,
   [virtio_disk_rw]'s QUEUE_NOTIFY write -- runs concurrently with the device
   thread and with the other harts, so the [virtio_frag] half lives inside
   [WpUart.dev_inv] and these leaves borrow it by opening the invariant around
   the (atomic) access.  The shape is exactly WpPlic.v's
   [wp_lw_plic_dev_s_sconf] / [wp_sw_plic_dev_s_sconf]:

   - the caller cannot NAME the device state (the invariant's [v] is
     existentially quantified and the device thread moves it), so its
     obligation is UNIVERSAL over every state the invariant admits -- i.e.
     over every [v] with [virtio_isr_ok v] -- and in exchange it may name a
     property [P] of the value read that holds at all of them;
   - the invariant must be RE-CLOSABLE, so the store leaf's obligation also
     demands that the write preserve [virtio_isr_ok] and leave the four
     components [virtio_proto] depends on (cfg / seen / used_idx / disk)
     alone; [VirtioProto.virtio_proto_stable] then rides the protocol
     through the write untouched.

   The two offsets the live driver writes -- QUEUE_NOTIFY (0x50) and
   INTERRUPT_ACK (0x64), i.e. exactly [VirtioModel.vio_cfg_stable] -- meet
   that obligation, and §0 below proves it once and for all:
   [virtio_notify_write_ok] (the notify write leaves the state ENTIRELY
   unchanged) and [virtio_ack_write_ok] (the ack write changes only [v_isr],
   and only by clearing bits, so [virtio_isr_ok] survives for ANY mask -- not
   just xv6's 0x3).

   A virtio-mmio READ does not advance the device (WpVirtioExec's
   [dev_read_virtio] concludes at the SAME [d]), so the load leaf closes the
   invariant with the state it opened it at and touches [state_interp]'s
   device half not at all.                                                 *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import DevModel RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpLoad WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import KptPt KMap.
Require Import SmodeCore WpSmodeGpr.
Require Import SmodeCorePt SRegime.
Require Import IntrDefs WpSmodeIntr.
Require Import VirtioModel.
Require Import WpVirtio.
Require Import DiskPtsto VirtioProto WpUart.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpVirtioExec.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(* §0  The two LIVE-driver MMIO writes, as pure device facts.             *)
(* ===================================================================== *)

(* Clearing bits of a value that only has bits 0..1 leaves only bits 0..1 --
   for ANY mask, so the ack leaf does not have to know xv6 writes 0x3. *)
Lemma virtio_isr_land_lnot (x wz : Z) :
  Z.land x 3 = x ->
  Z.land (bv_unsigned (Z_to_bv 32 (Z.land x (Z.lnot wz)))) 3
  = bv_unsigned (Z_to_bv 32 (Z.land x (Z.lnot wz))).
Proof.
  intro Hx. apply land3_intro. intros i Hi.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 32) with 32.
  destruct (decide (i < 32)) as [Hlt|Hge].
  - rewrite (Z.mod_pow2_bits_low _ 32 i Hlt).
    rewrite Z.land_spec (land3_bit_high _ i Hx Hi). reflexivity.
  - rewrite (Z.mod_pow2_bits_high _ 32 i ltac:(lia)). reflexivity.
Qed.

(* INTERRUPT_ACK: always accepted, changes only [v_isr], and only downward. *)
Lemma virtio_ack_write_ok (v : virtio_state) (w : bv 32) :
  virtio_isr_ok v ->
  exists v' : virtio_state,
    virtio_write v vio_off_interrupt_ack w = Some v'
    /\ virtio_isr_ok v'
    /\ v_cfg v' = v_cfg v /\ v_seen v' = v_seen v
    /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v.
Proof.
  intro Hok. eexists. split; [ reflexivity |].
  split_and!; [| reflexivity .. ].
  unfold virtio_isr_ok. cbn [v_isr].
  apply virtio_isr_land_lnot. exact Hok.
Qed.

(* QUEUE_NOTIFY of queue 0: accepted, and a complete no-op on the state. *)
Lemma virtio_notify_write_ok (v : virtio_state) (w : bv 32) :
  bv_unsigned w = 0 ->
  virtio_isr_ok v ->
  exists v' : virtio_state,
    virtio_write v vio_off_queue_notify w = Some v'
    /\ virtio_isr_ok v'
    /\ v_cfg v' = v_cfg v /\ v_seen v' = v_seen v
    /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v.
Proof.
  intros Hw Hok. exists v.
  assert (Hz : (bv_unsigned w =? 0) = true) by (apply Z.eqb_eq; exact Hw).
  split.
  { unfold virtio_write. cbv zeta. rewrite Hz. reflexivity. }
  split_and!; [ exact Hok | reflexivity .. ].
Qed.

(* INTERRUPT_STATUS: always readable, and the value is the ISR itself, so a
   reader learns [virtio_isr_ok] of what it loaded. *)
Lemma virtio_isr_read_ok (v : virtio_state) :
  virtio_isr_ok v ->
  exists w : bv 32,
    virtio_read v vio_off_interrupt_status = Some w
    /\ Z.land (bv_unsigned w) 3 = bv_unsigned w.
Proof. intro Hok. exists (v_isr v). split; [ reflexivity | exact Hok ]. Qed.

(* the width-4 store tower's store word is a double [autocast]/subrange of the
   register value; collapsing the redundant outer layer bridges it to the
   caller-facing single-layer [storeword].  (WpVirtioMmio's twin; kept local so
   the two files stay independent.) *)
Lemma vd_subrange32_31_0_id (x : mword 32) : subrange_vec_dec x 31 0 = x.
Proof.
  apply bv_eq.
  unfold subrange_vec_dec. rewrite autocast_id.
  unfold to_word_idx. rewrite MachineWord.MachineWord.cast_idx_refl.
  unfold get_word, MachineWord.MachineWord.slice, Values.to_word.
  rewrite bv_extract_unsigned.
  change (Z.of_N (MachineWord.MachineWord.Z_idx 0)) with 0%Z.
  rewrite Z.shiftr_0_r.
  change (MachineWord.MachineWord.Z_idx (31 - 0 + 1)) with 32%N.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N in Hx.
  exact Hx.
Qed.

Lemma vd_wv32_collapse (x : mword 32) :
  autocast (T := mword) (subrange_vec_dec x 31 0) = x.
Proof. rewrite vd_subrange32_31_0_id. apply autocast_id. Qed.

Section WpVirtioDev.
Context `{!riscvGS Σ, !sieG Σ}.
Context `{!uartGhostG Σ, !diskGhostG Σ}.
Context `{CID : CpuId}.
Existing Instance riscv_memGS.

(* ===================================================================== *)
(* §1  the [dev_inv]-borrowing width-4 virtio-mmio LOAD                    *)
(* ===================================================================== *)

(* [virtio_disk_intr]'s [lw a5,96(a5)] of INTERRUPT_STATUS.  Nothing about the
   device survives into the continuation -- the invariant is closed again at
   the state it was opened at (a virtio read does not advance the device) --
   what the caller gets is the property [P] it proved of the loaded word at
   EVERY state the invariant admits. *)
Lemma wp_lw_virtio_dev_s_sconf (γ : gname) (γu : uart_names) (γd : disk_names)
    (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5)
    (imm : mword 12) (m : regfile) (n : nat) (P : bv 32 -> Prop) :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let ldval := fun (w : bv 32) =>
        (extend_value is_unsigned
           (update_subrange_vec_dec (zeros' (8*1*4)) (8*(0+1)*4-1) (8*0*4) w) : mword 64) in
  (virtio_base <= uint a8 < virtio_base + virtio_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  uint rd <> 0 ->
  rd <> csp_rs1 ->
  (forall v : virtio_state, virtio_isr_ok v ->
     exists w : bv 32, virtio_read v (uint a8 - virtio_base)%Z = Some w /\ P w) ->
  sie_cap_gpr γ m n -∗
  pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) -∗
  dev_inv γu γd -∗
  ( ∀ w : bv 32,
    ⌜ P w ⌝ -∗
    sie_cap_gpr γ (<[Regidx rd := regval_into_reg (ldval w)]> m) n -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 ldval Hrange Halign Hcanon Hdevvpn Hrdnz Hrdsp Hread.
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iApply (wp_instr_s_sconf γ m n Φ pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
            with "Hcg Hpc Hinstr").
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (Hpma_all a8 4) as (region_ld & Hmatch_ld & _ & Hread_ld & _ & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  (* only the DISK half of the fabric is touched, and [↑diskN ⊆ ↑devN] *)
  iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
  iInv "Hvinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
  iDestruct (dev_interp_agree_virtio with "Hdev Hvf") as %Hveq.
  destruct (Hread vst Hvok) as (w & Hrd_v & HPw).
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform strans_regime (Load Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_introl eq_refl)) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_load_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iMod (sr_absorb strans_regime (Load Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc
          (or_intror (or_introl eq_refl)) I Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_load s_pc)
          Lpma_pc' with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hdrd_virtio : dev_read s_tr.(mdev) a8 4 = Some (w, σ.(mdev))).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_read_virtio σ.(mdev) a8 w Hrange).
    rewrite Hveq. exact Hrd_v. }
  pose (s_x := set_reg (MState s_tr.(sregs) s_tr.(mem) σ.(mdev))
                 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (ldval w))).
  assert (Hload : exec (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))) s_pc
                  = Some (RETIRE_SUCCESS, s_x)).
  { subst s_x. unfold ldval.
    apply (exec_execute_LOAD_4_gpr_S_walk_dev rs1 rd imm is_unsigned w σ.(mdev) region_ld s_pc s_tr
             Hrdnz Htea
             ltac:(rewrite !Lva; exact Halign)
             ltac:(cbn [bits_of_virtaddr]; rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
             Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
             HA1 Hord1
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply virtio_pmp_match4; [exact Hrange | exact Hcov1])
             HR1
             ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_ld)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
             Hread_ld
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_virtio; [exact Hrange | lia])
             ltac:(apply within_sig_virtio)
             ltac:(apply within_htif_false; exact Lhtif_tr)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_virtio; exact Hrange)
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hdrd_virtio)). }
  iDestruct (gpr_file_insert_acc m (Regidx rd) (regval_into_reg (ldval w)) with "Hfmap") as "[Hrdc Hfins]".
  rewrite (gpr_pt_nz rd _ Hrdnz).
  iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg (ldval w)) with "Hreg Hrdc") as "[Hreg Hrdc]".
  iDestruct ("Hfins" with "[Hrdc]") as "Hfmap".
  { rewrite (gpr_pt_nz rd _ Hrdnz). iExact "Hrdc". }
  iMod ("Hdclose" with "[Hvf Hproto]") as "_".
  { iNext. iExists vst. iFrame. iPureIntro. exact Hvok. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hload. }
  iSplitL "Hreg Hmem Hdev".
  { unfold s_x, set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x, set_reg; cbn [sregs]. tmig.
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  assert (Hsp : m !!! Regidx csp_rs1
                = <[Regidx rd := regval_into_reg (ldval w)]> m !!! Regidx csp_rs1)
    by (symmetry; apply upd_ne; congruence).
  iAssert (sconf γ) with "[Hpriv Hmiex Hms Hhalf Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf".
    { iExists mstatus0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  iDestruct (sie_cap_retarget γ m
               (<[Regidx rd := regval_into_reg (ldval w)]> m) n Hsp with "Hcap") as "Hcap".
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iApply ("Hcont" $! w with "[%] Hcg [$Hpc' $Hnpc]").
  { exact HPw. }
Qed.

(* ===================================================================== *)
(* §2  the [dev_inv]-borrowing width-4 virtio-mmio STORE                  *)
(* ===================================================================== *)

(* [virtio_disk_intr]'s [sw a5,100(a4)] of INTERRUPT_ACK and
   [virtio_disk_rw]'s [sw zero,80(a5)] of QUEUE_NOTIFY.  The caller must show
   the write is DEFINED and PROTOCOL-NEUTRAL at every state the invariant
   admits: it keeps [virtio_isr_ok] and leaves cfg / seen / used_idx / disk
   alone, which is exactly what [VirtioProto.virtio_proto_stable] needs to
   carry the driver protocol across the store.  §0's
   [virtio_ack_write_ok] / [virtio_notify_write_ok] discharge it. *)
Lemma wp_sw_virtio_dev_s_sconf (γ : gname) (γu : uart_names) (γd : disk_names)
    (Φ : mval -> iProp Σ) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) (imm : mword 12)
    (m : regfile) (n : nat) :
  let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (m !!! Regidx rs2) (Z.sub (Z.mul 4 8) 1) 0) in
  (virtio_base <= uint a8 < virtio_base + virtio_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  (forall v : virtio_state, virtio_isr_ok v ->
     exists v' : virtio_state,
       virtio_write v (uint a8 - virtio_base)%Z storeword = Some v'
       /\ virtio_isr_ok v'
       /\ v_cfg v' = v_cfg v /\ v_seen v' = v_seen v
       /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v) ->
  sie_cap_gpr γ m n -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  dev_inv γu γd -∗
  ( sie_cap_gpr γ m n -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn Hwrite.
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iApply (wp_instr_s_sconf γ m n Φ pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            with "Hcg Hpc Hinstr").
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (Hpma_all a8 4) as (region_st & Hmatch_st & _ & _ & Hwrite_st & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  (* only the DISK half of the fabric is touched, and [↑diskN ⊆ ↑devN] *)
  iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
  iInv "Hvinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
  iDestruct (dev_interp_agree_virtio with "Hdev Hvf") as %Hveq.
  destruct (Hwrite vst Hvok) as (vst' & Hvw & Hvok' & Hcfg' & Hseen' & Hused' & Hdisk').
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc m (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (gpr_file_lookup_acc m (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value rs2 (m (Regidx rs2)) s_pc with "Hreg Hr2c") as %Lv2.
  iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
  assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor) by (unfold s_pc; tmig; exact Lpriv).
  assert (Lms_pc : register_lookup mstatus s_pc.(sregs) = mstatus0) by (unfold s_pc; tmig; exact Lms).
  assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0) by (unfold s_pc; tmig; exact Lmenv).
  assert (Lpma_pc : register_lookup pma_regions s_pc.(sregs) = pmar0) by (unfold s_pc; tmig; exact Lpma).
  assert (Lhtif_pc : register_lookup htif_tohost_base s_pc.(sregs) = None) by (unfold s_pc; tmig; exact Lhtif).
  assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0) by (unfold s_pc; tmig; exact Lmisa).
  assert (Lmisa_pc' : register_lookup misa s_pc.(sregs) = MISA_C) by (rewrite Lmisa_pc; exact Hmisa_val0).
  assert (Lmenv_pc' : register_lookup menvcfg s_pc.(sregs) = MENVCFG_S) by (rewrite Lmenv_pc; exact Hmenvval0).
  assert (LSXL_pc : _get_Mstatus_SXL (register_lookup mstatus s_pc.(sregs)) = 'b"10") by (rewrite Lms_pc; exact HSXL).
  assert (Lpma_pc' : pma_allows_all (register_lookup pma_regions s_pc.(sregs))) by (rewrite Lpma_pc; exact Hpma_all).
  iDestruct (sr_transform strans_regime (Store Data)
               (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                         else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                        (sign_extend' 64 imm))
               s_pc (or_intror (or_intror (or_introl eq_refl))) Lpriv_pc LSXL_pc
               (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
                  ltac:(rewrite Lms_pc; exact HMPRV))
               (exec_get_pmlen_store_S s_pc ltac:(rewrite Lms_pc; exact HMXR)
                  ltac:(rewrite Lmenv_pc; exact Hpmm))
               with "Hreg Htr") as %Htea.
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic with "Hkmapb") as "#Hclaim".
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  iMod (sr_absorb strans_regime (Store Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc
          (or_intror (or_intror (or_introl eq_refl))) eq_refl Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)".
  rewrite (pa_of_id a8 Ha8lt) in Htr0.
  destruct Hgr as (HA1 & Hord1 & HX1 & HW1 & HR1 & Hcov1).
  pose proof (pt_regs_preserved _ _ Hshtr) as Hprestr.
  assert (Lpriv_tr : register_lookup cur_privilege s_tr.(sregs) = Supervisor)
    by (rewrite (Hprestr cur_privilege ltac:(vm_compute; reflexivity)); exact Lpriv_pc).
  assert (Lms_tr : register_lookup mstatus s_tr.(sregs) = mstatus0)
    by (rewrite (Hprestr mstatus ltac:(vm_compute; reflexivity)); exact Lms_pc).
  assert (Lpma_tr : register_lookup pma_regions s_tr.(sregs) = pmar0)
    by (rewrite (Hprestr pma_regions ltac:(vm_compute; reflexivity)); exact Lpma_pc).
  assert (Lhtif_tr : register_lookup htif_tohost_base s_tr.(sregs) = None)
    by (rewrite (Hprestr htif_tohost_base ltac:(vm_compute; reflexivity)); exact Lhtif_pc).
  assert (Hwr_virtio : dev_write s_tr.(mdev) a8 4 storeword = Some (set_dvirtio σ.(mdev) vst')).
  { rewrite Hmdevtr. unfold s_pc, set_reg; cbn [mdev].
    apply (dev_write_virtio σ.(mdev) a8 storeword vst' Hrange).
    rewrite Hveq. exact Hvw. }
  pose (d' := set_dvirtio σ.(mdev) vst').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_4_gpr_S_walk_dev rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(rewrite !Lva; exact Halign)
               ltac:(cbn [bits_of_virtaddr]; rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
               Lpriv_tr ltac:(rewrite Lms_tr; exact HMPRV)
               HA1 Hord1
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply virtio_pmp_match4; [exact Hrange | exact Hcov1])
               HW1
               ltac:(rewrite Lpma_tr !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Hmatch_st)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Halign)
               Hwrite_st
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply within_clint_virtio; [exact Hrange | lia])
               ltac:(apply within_sig_virtio)
               ltac:(apply within_htif_writable_false; exact Lhtif_tr)
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; apply dev_addr_virtio; exact Hrange)
               ltac:(rewrite !Lva !Lv2; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id;
                     change (8 * (0 + 1) * 4 - 1)%Z with 31%Z; change (8 * 0 * 4)%Z with 0%Z;
                     rewrite vd_wv32_collapse; exact Hwr_virtio)).
    subst s_x d'. reflexivity. }
  iMod (dev_interp_update_virtio σ.(mdev) vst vst' with "Hdev Hvf") as "[Hdev' Hvf']".
  iDestruct (virtio_proto_stable γd vst vst' Hcfg' Hseen' Hused' Hdisk' with "Hproto") as "Hproto'".
  iMod ("Hdclose" with "[Hvf' Hproto']") as "_".
  { iNext. iExists vst'. iFrame. iPureIntro. exact Hvok'. }
  iModIntro. iExists s_x.
  iSplitR.
  { iPureIntro. rewrite Hpceq. change (if is_rvc then 2%Z else 4%Z) with (if is_rvc then 2 else 4). fold s_pc. exact Hstore. }
  iSplitL "Hreg Hmem Hdev'".
  { unfold s_x; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev'". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; cbn [sregs].
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  iAssert (sconf γ) with "[Hpriv Hmiex Hms Hhalf Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf".
    { iExists mstatus0. iFrame "Hms Hhalf". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap γ m n) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr". }
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  iApply ("Hcont" with "Hcg [$Hpc' $Hnpc]").
Qed.

End WpVirtioDev.
