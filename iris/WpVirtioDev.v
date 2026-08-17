(* WpVirtioDev.v -- the width-4 virtio-mmio LOAD and STORE weakest-precondition
   leaves.  EVERY virtio-mmio access in the kernel goes through them: the
   [virtio_frag] half can never sit raw in a CPU's precondition, because the
   disk thread runs from step 0 and has to REFUTE [DevStepDiskWild] at every
   step, which only [virtio_proto] can do.  So the fragment lives inside
   [WpUart.disk_inv] and these leaves borrow it by opening the invariant around
   the (atomic) access -- for [virtio_disk_init]'s reset and queue programming
   just as much as for [virtio_disk_intr]'s INTERRUPT_STATUS read and
   INTERRUPT_ACK write and [virtio_disk_rw]'s QUEUE_NOTIFY write.

   §1/§2 are the GENERAL leaves, over the bare [disk_inv] and an ACCESSOR-form
   ghost callback (the shape SpecUart's [wp_sb_uart_uinv_s_sconf] uses for the
   UART): the caller cannot NAME the device state -- the invariant's [v] is
   existentially quantified and the device thread moves it -- so it hands in a
   resource [R], a callback that moves the protocol from [v] to [v'] however it
   likes, and gets [S] back.  §3 restates the two for the LIVE driver, whose
   reads are state-independent and whose writes are protocol-neutral, at the
   [dev_inv]-bundle signatures their call sites were written against.

   - the invariant must be RE-CLOSABLE, so the store callback's obligation
     includes preserving [virtio_isr_ok]; for a protocol-neutral write, leaving
     the four components [virtio_proto] depends on (cfg / seen / used_idx /
     disk) alone is what lets [VirtioProto.virtio_proto_stable] ride the
     protocol through untouched (§3).

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
Require Import RegFile HartTp WpNext.
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
   caller-facing single-layer [storeword].  (WpPlic has the same fact for its
   own tower; kept local so the two files stay independent.) *)
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
Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
(* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
   bundle like the register map.  Implicit, so no call site changes. *)
Context {p : mword 64}.
Existing Instance riscv_memGS.

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

(* ===================================================================== *)
(* §1  the width-4 virtio-mmio LOAD, ACCESSOR form over the BARE           *)
(*     [disk_inv]                                                          *)
(* ===================================================================== *)

(* THE GENERAL LOAD LEAF.  The caller cannot NAME the device state (the
   invariant's [v] is existentially quantified and the device thread moves
   it), so its obligation is a GHOST CALLBACK, universal over every state the
   invariant admits: given the protocol at [v] and the caller's own resource
   [R], produce the word the read yields, hand the protocol back, and hand out
   whatever the caller wants to know about the word ([S w]).  A virtio read
   does not advance the device (WpVirtioExec's [dev_read_virtio] concludes at
   the SAME [d]), so the invariant is closed at the state it was opened at and
   the protocol travels through unchanged -- but it is the CALLBACK that says
   so, because that is also where a caller holding a ghost fragment of the
   protocol ([DiskPtsto.disk_cfg_is], the boot chain's config tracker) reads
   the register value out of the state.
   [wp_lw_virtio_dev_s_sconf] below is the bundle-taking, pure-premise
   restatement for the live driver, whose reads are state-independent. *)
Lemma wp_lw_virtio_dinv_s_sconf (γd : disk_names) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1}
    (imm : mword 12) (m : regfile) (n : nat) (R : iProp Σ) (S : bv 32 -> iProp Σ) :
  let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  (* the vmem level hands back the value itself now, not the split accumulator *)
  let ldval := fun (w : mword (8*4)) => (extend_value is_unsigned w : mword 64) in
  (virtio_base <= uint a8 < virtio_base + virtio_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  uint rd <> 0 ->
  rd_ok rd ->
  sie_cap_gpr kt m n false p -∗
  pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) -∗
  disk_inv γd -∗
  R -∗
  ( ∀ (v : virtio_state) (_ : virtio_isr_ok v),
    virtio_proto γd v -∗ R ==∗
    ∃ w : bv 32, ⌜ virtio_read v (uint a8 - virtio_base)%Z = Some w ⌝ ∗
                 virtio_proto γd v ∗ S w ) -∗
  wp_next false p (fun (CID : CpuId) =>
    ∀ w : bv 32,
    sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ldval w)]> m) n false p -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    S w -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros ea a8 ldval Hrange Halign Hcanon Hdevvpn Hrdnz Hrdok.
  (* the class, consumed at [rs1] -- the one line the funnel change needs,
     and this leaf's wiring check.  See the family note at the head of this
     section. *)
  assert (Hea_all : forall hh : CpuId,
            add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
    by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
  pose proof (rd_ok_sp rd Hrdok) as Hrdsp.
  pose proof (rd_ok_tp rd Hrdok) as Hrdtp.
  iIntros "Hcg Hpc Hinstr #Hvinv HR Hacc Hcont".
  iApply (wp_instr_s_sconf m n false pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
            with "Hcg Hpc Hinstr").
  (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic
     obligation is discharged by [wp_next]'s OWN introduction rule at the
     ambient hart -- the same [wp_next_off_intro] every b = false leaf
     already uses for its own conclusion.  Nothing is renamed and nothing
     is substituted: the body below is the pre-move proof VERBATIM. *)
  iApply wp_next_off_intro.
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & Hspp & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (pma_all_io Hpma_all a8 4
             (pma_access_io _ _ virtio_base (virtio_base + virtio_size) (proj1 Hrange) (proj2 Hrange)
                eq_refl eq_refl (pma_width_ok 4 eq_refl eq_refl))) as (region_ld & Hmatch_ld & Hread_ld & _).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iInv "Hvinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
  iDestruct (dev_interp_agree_virtio with "Hdev Hvf") as %Hveq.
  iMod ("Hacc" $! vst Hvok with "Hproto HR") as (w) "(%Hrd_v & Hproto & HS)".
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
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
  iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
  unshelve iMod (sr_absorb strans_regime (Load Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc _
          (or_intror (or_introl eq_refl)) I Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_load_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_load s_pc)
          Lpma_pc' (pa_of_id a8 Ha8lt) _ with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
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
  { rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
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
             md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
             ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
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
  iDestruct (gpr_file_insert_acc (tp_pin m) (Regidx rd) (regval_into_reg (ldval w)) with "Hfmap") as "[Hrdc Hfins]".
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
  { unfold s_x; rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg. iFrame "Hreg Hmem Hdev". }
  iIntros "Hhs' Hpc'".
  assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc (if is_rvc then 2 else 4)).
  { unfold s_x; rewrite ?sregs_set_reg. tmig.
    rewrite (Hprestr nextPC ltac:(vm_compute; reflexivity)).
    unfold s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
  iEval (rewrite Lnpc) in "Hpc'".
  assert (Hsp : m !!! Regidx csp_rs1
                = <[Regidx rd := regval_into_reg (ldval w)]> m !!! Regidx csp_rs1)
    by (symmetry; apply upd_ne; congruence).
  (* the leaf's own write commutes with the tp pin *)
  tp_refold Hrdtp "Hfmap".
  iAssert (sconf) with "[Hpriv Hmiex Hms Hhalf Hspp Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf Hspp".
    { iExists mstatus0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap kt m n false p) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr Hwit". }
  iDestruct (sie_cap_retarget m
               (<[Regidx rd := regval_into_reg (ldval w)]> m) n false Hsp with "Hcap") as "Hcap".
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
     obligation is discharged by instantiating it here. *)
  iSpecialize ("Hcont" $! cpu_id with "[]"); [ done | ].
  iApply ("Hcont" $! w with "Hcg [$Hpc' $Hnpc] HS").
Qed.

(* ===================================================================== *)
(* §2  the width-4 virtio-mmio STORE, ACCESSOR form over the BARE          *)
(*     [disk_inv]                                                          *)
(* ===================================================================== *)

(* THE GENERAL STORE LEAF, the dual of §1: the ghost callback must show the
   write is DEFINED at the state the invariant currently holds, keep
   [virtio_isr_ok] (which is what makes the acknowledgement in
   [virtio_disk_intr] provably effective) and re-establish the protocol at the
   new state.  That is general enough for all three kinds of driver write:
   a PROTOCOL-NEUTRAL one (notify / ack -- [VirtioProto.virtio_proto_stable]
   carries the protocol across), a PRE-FLIP CONFIGURATION one
   ([virtio_proto_cfg_write] steps the config tracker), and THE FLIP itself
   ([virtio_proto_intro] pays in the DMA lease and mints the publisher token).
   [wp_sw_virtio_dev_s_sconf] below is the bundle-taking, pure-premise
   restatement for the first kind. *)
Lemma wp_sw_virtio_dinv_s_sconf (γd : disk_names) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) (R S : iProp Σ) :
  let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 4 8) 1) 0) in
  (virtio_base <= uint a8 < virtio_base + virtio_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  sie_cap_gpr kt m n false p -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  disk_inv γd -∗
  R -∗
  ( ∀ (v : virtio_state) (_ : virtio_isr_ok v),
    virtio_proto γd v -∗ R ==∗
    ∃ v' : virtio_state,
      ⌜ virtio_write v (uint a8 - virtio_base)%Z storeword = Some v' ⌝ ∗
      ⌜ virtio_isr_ok v' ⌝ ∗ virtio_proto γd v' ∗ S ) -∗
  wp_next false p (fun (CID : CpuId) =>
    sie_cap_gpr kt m n false p -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    S -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn.
  (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
     and this leaf's wiring check.  See the family note at the head of this
     section. *)
  assert (Hea_all : forall hh : CpuId,
            add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
    by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
  assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
    by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
  iIntros "Hcg Hpc Hinstr #Hvinv HR Hacc Hcont".
  iApply (wp_instr_s_sconf m n false pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            with "Hcg Hpc Hinstr").
  (* INTERRUPTS ARE OFF AT THIS LEAF, so the funnel's hart-generic obligation
     is discharged by [wp_next]'s OWN introduction rule at the ambient hart --
     the same [wp_next_off_intro] a b = false leaf already uses for its own
     conclusion.  Nothing is renamed, so the body below is VERBATIM. *)
  iApply wp_next_off_intro.
  iIntros (σ Hpceq) "Hsc Hcap Hfmap Hnpc Hsi".
  iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
  iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
  iDestruct "Hmsx" as (mstatus0) "(Hms & Hhalf & Hspp & %Hmsf)".
  pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
  iDestruct "Hmenvx" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
  iPoseProof "Hhw" as "#Hhwc".
  iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
    "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
      %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
  destruct (pma_all_io Hpma_all a8 4
             (pma_access_io _ _ virtio_base (virtio_base + virtio_size) (proj1 Hrange) (proj2 Hrange)
                eq_refl eq_refl (pma_width_ok 4 eq_refl eq_refl))) as (region_st & Hmatch_st & _ & Hwrite_st).
  iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
  iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
  iDestruct (reg_valid_dq with "Hreg Hms")   as %Lms.
  iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
  iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma.
  iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
  iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
  iInv "Hvinv" as ">Hdbody" "Hdclose".
  iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
  iDestruct (dev_interp_agree_virtio with "Hdev Hvf") as %Hveq.
  iMod ("Hacc" $! vst Hvok with "Hproto HR") as (vst')
    "(%Hvw & %Hvok' & Hproto & HS)".
  iMod (reg_update _ nextPC _ (add_vec_int pc (if is_rvc then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
  set (s_pc := set_reg σ nextPC (add_vec_int pc (if is_rvc then 2 else 4))).
  iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs1) with "Hfmap") as "[Hspc Hfb1]".
  iDestruct (gpr_pt_value rs1 (tp_pin m (Regidx rs1)) s_pc with "Hreg Hspc") as %Lva.
  iDestruct ("Hfb1" with "Hspc") as "Hfmap".
  iDestruct (gpr_file_lookup_acc (tp_pin m) (Regidx rs2) with "Hfmap") as "[Hr2c Hfb2]".
  iDestruct (gpr_pt_value rs2 (tp_pin m (Regidx rs2)) s_pc with "Hreg Hr2c") as %Lv2.
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
  iDestruct (sr_tmode strans_regime s_pc LSXL_pc with "Hreg Htr") as %(md0 & Htm_pc).
  unshelve iMod (sr_absorb strans_regime (Store Data) a8 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
          (kpt_leaf_ppn (svpn_of a8)) KP_rw s_pc _
          (or_intror (or_intror (or_introl eq_refl))) eq_refl Hcanon ltac:(reflexivity)
          Lmisa_pc' Lmenv_pc' Lhtif_pc Lpriv_pc LSXL_pc
          (exec_effectivePrivilege_store_S (register_lookup mstatus s_pc.(sregs)) s_pc
             ltac:(rewrite Lms_pc; exact HMPRV))
          (exec_is_shadow_stack_store s_pc)
          Lpma_pc' (pa_of_id a8 Ha8lt) _ with "Hclaim Hreg Hmem Htr")
    as (s_tr) "(%Htr0 & %Hmdevtr & %Hshtr & %Hgr & Hreg & Hmem & Htr)"; [solve_ndisj |].
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
  { rewrite Hmdevtr. unfold s_pc; rewrite ?mdev_set_reg.
    apply (dev_write_virtio σ.(mdev) a8 storeword vst' Hrange).
    rewrite Hveq. exact Hvw. }
  pose (d' := set_dvirtio σ.(mdev) vst').
  pose (s_x := MState s_tr.(sregs) s_tr.(mem) d').
  assert (Hstore : exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 4))) s_pc = Some (RETIRE_SUCCESS, s_x)).
  { rewrite (exec_execute_STORE_4_gpr_S_walk_dev rs2 rs1 imm region_st s_pc s_tr d'
               Htea
               ltac:(rewrite !Lva; exact Halign)
               md0 Lpriv_pc ltac:(rewrite Lms_pc; exact HMPRV) Htm_pc
               ltac:(rewrite !Lva; change (0 * 4)%Z with 0%Z; rewrite !avi0 zero_extend'_id; exact Htr0)
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
  iMod ("Hdclose" with "[Hvf' Hproto]") as "_".
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
  iAssert (sconf) with "[Hpriv Hmiex Hms Hhalf Hspp Hmenv]" as "Hsc".
  { iFrame "Hhw Hminv Hpriv Hmiex".
    iSplitL "Hms Hhalf Hspp".
    { iExists mstatus0. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
    iExists menvcfg0. iFrame "Hmenv". iPureIntro. repeat split; assumption. }
  iAssert (sie_cap kt m n false p) with "[Hstk Htr Harm]" as "Hcap".
  { rewrite /sie_cap. iFrame "Hstk Harm Htr Hwit". }
  iDestruct (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfmap") as "Hcg".
  (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
     obligation is discharged by instantiating it here. *)
  iApply ("Hcont" $! cpu_id with "[] Hcg [$Hpc' $Hnpc] HS").
  iPureIntro. done.
Qed.

(* ===================================================================== *)
(* §3  the LIVE-DRIVER restatements, over the [dev_inv] bundle.            *)
(*                                                                        *)
(*     Verbatim the statements [virtio_disk_intr] and [virtio_disk_rw] were*)
(*     written against (WRAPPER RECIPE, claude-notes/durable-notes.md), so *)
(*     no call site changed when the leaves went accessor-form: a live     *)
(*     driver's reads are state-independent and its writes are            *)
(*     protocol-neutral, so [R = S = emp] and the ghost callback is just   *)
(*     the pure premise plus [virtio_proto_stable].                        *)
(* ===================================================================== *)

(* [virtio_disk_intr]'s [lw a5,96(a5)] of INTERRUPT_STATUS.  Nothing about the
   device survives into the continuation -- the invariant is closed again at
   the state it was opened at (a virtio read does not advance the device) --
   what the caller gets is the property [P] it proved of the loaded word at
   EVERY state the invariant admits. *)
Lemma wp_lw_virtio_dev_s_sconf (γu : uart_names) (γd : disk_names) (pc : mword 64) (is_rvc is_unsigned : bool) (rd rs1 : mword 5) `{!SrcOk rs1}
    (imm : mword 12) (m : regfile) (n : nat) (P : bv 32 -> Prop) :
  let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  (* the vmem level hands back the value itself now, not the split accumulator *)
  let ldval := fun (w : mword (8*4)) => (extend_value is_unsigned w : mword 64) in
  (virtio_base <= uint a8 < virtio_base + virtio_size)%Z ->
  is_aligned_vaddr (Virtaddr a8) 4 = true ->
  neq_vec (bits_of_virtaddr (Virtaddr a8)) (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr a8)) (Z.sub 39 1) 0)) = false ->
  kpt_dev_vpn (svpn_of a8) ->
  uint rd <> 0 ->
  rd_ok rd ->
  (forall v : virtio_state, virtio_isr_ok v ->
     exists w : bv 32, virtio_read v (uint a8 - virtio_base)%Z = Some w /\ P w) ->
  sie_cap_gpr kt m n false p -∗
  pc_is pc -∗ instr pc is_rvc (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)) -∗
  dev_inv γu γd -∗
  wp_next false p (fun (CID : CpuId) =>
    ∀ w : bv 32,
    ⌜ P w ⌝ -∗
    sie_cap_gpr kt (<[Regidx rd := regval_into_reg (ldval w)]> m) n false p -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros ea a8 ldval Hrange Halign Hcanon Hdevvpn Hrdnz Hrdok Hread.
  (* the class, consumed at [rs1] -- the one line the funnel change needs,
     and this leaf's wiring check.  See the family note at the head of this
     section. *)
  assert (Hea_all : forall hh : CpuId,
            add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
    by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  (* only the DISK half of the fabric is touched, and [↑diskN ⊆ ↑devN] *)
  iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
  iApply (wp_lw_virtio_dinv_s_sconf γd pc is_rvc is_unsigned rd rs1 imm m n
            emp%I (fun w => ⌜P w⌝%I)
            Hrange Halign Hcanon Hdevvpn Hrdnz Hrdok
            with "Hcg Hpc Hinstr Hvinv [] [] [-]").
  { done. }
  { iIntros (v Hvok) "Hproto _".
    destruct (Hread v Hvok) as (w & Hrd & HPw).
    iModIntro. iExists w. iFrame "Hproto". iSplitR; [| iPureIntro; exact HPw ].
    iPureIntro. exact Hrd. }
  (* the callee's continuation shape carries [S w] LAST; ours carries [⌜P w⌝]
     FIRST -- reassemble across the wp_next/forall-w binders explicitly. *)
  iIntros (CIDx) "%Hcid".
  iIntros (w) "Hcg Hpc %HPw".
  iSpecialize ("Hcont" $! CIDx with "[]"); [ done | ].
  iApply ("Hcont" $! w with "[%] Hcg Hpc"). { exact HPw. }
Qed.

(* [virtio_disk_intr]'s [sw a5,100(a4)] of INTERRUPT_ACK and
   [virtio_disk_rw]'s [sw zero,80(a5)] of QUEUE_NOTIFY.  The caller must show
   the write is DEFINED and PROTOCOL-NEUTRAL at every state the invariant
   admits: it keeps [virtio_isr_ok] and leaves cfg / seen / used_idx / disk
   alone, which is exactly what [VirtioProto.virtio_proto_stable] needs to
   carry the driver protocol across the store.  §0's
   [virtio_ack_write_ok] / [virtio_notify_write_ok] discharge it. *)
Lemma wp_sw_virtio_dev_s_sconf (γu : uart_names) (γd : disk_names) (pc : mword 64) (is_rvc : bool) (rs2 rs1 : mword 5) `{!SrcOk rs1} `{!SrcOk rs2} (imm : mword 12)
    (m : regfile) (n : nat) :
  let ea := add_vec (rget m rs1) (sign_extend' 64 imm) in
  let a8 := sign_extend' 64 (subrange_vec_dec ea (xlen - 0 - 1) 0) in
  let storeword : mword 32 := autocast (T := mword) (subrange_vec_dec (rget m rs2) (Z.sub (Z.mul 4 8) 1) 0) in
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
  sie_cap_gpr kt m n false p -∗
  pc_is pc -∗ instr pc is_rvc (STORE (imm, Regidx rs2, Regidx rs1, 4)) -∗
  dev_inv γu γd -∗
  wp_next false p (fun (CID : CpuId) =>
    sie_cap_gpr kt m n false p -∗
    pc_is (add_vec_int pc (if is_rvc then 2 else 4)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
Proof.
  intros ea a8 storeword Hrange Halign Hcanon Hdevvpn Hwrite.
  (* the class, consumed at [rs1 / rs2] -- the one line the funnel change needs,
     and this leaf's wiring check.  See the family note at the head of this
     section. *)
  assert (Hea_all : forall hh : CpuId,
            add_vec (rget (CID := hh) m rs1) (sign_extend' 64 imm) = ea)
    by (intros hh; unfold ea; by rewrite (src_ok_rget_indep m rs1 hh CID)).
  assert (Hsv2_all : forall hh : CpuId, rget (CID := hh) m rs2 = rget (CID := CID) m rs2)
    by (intros hh; exact (src_ok_rget_indep m rs2 hh CID)).
  iIntros "Hcg Hpc Hinstr #Hdinv Hcont".
  iDestruct (dev_inv_disk with "Hdinv") as "#Hvinv".
  iApply (wp_sw_virtio_dinv_s_sconf γd pc is_rvc rs2 rs1 imm m n
            emp%I emp%I Hrange Halign Hcanon Hdevvpn
            with "Hcg Hpc Hinstr Hvinv [] [] [-]").
  { done. }
  { iIntros (v Hvok) "Hproto _".
    destruct (Hwrite v Hvok) as (v' & Hvw & Hvok' & Hcfg' & Hseen' & Hused' & Hdisk').
    iDestruct (virtio_proto_stable γd v v' Hcfg' Hseen' Hused'
                 with "Hproto") as "Hproto".
    iModIntro. iExists v'.
    iSplitR; [iPureIntro; exact Hvw|].
    iSplitR; [iPureIntro; exact Hvok'|].
    iFrame "Hproto". }
  (* the callee's continuation carries a trailing [emp] wand (S := emp) that
     ours does not -- discard it. *)
  iIntros (CIDx) "%Hcid".
  iIntros "Hcg Hpc _".
  iSpecialize ("Hcont" $! CIDx with "[]"); [ done | ].
  iApply ("Hcont" with "Hcg Hpc").
Qed.

(* ------------------------------------------------------------------- *)
(* [SrcOk] SMOKE TEST -- see IntrDefs.v's checker block.  x15/x14 (a5/a4) *)
(* are the registers the virtio driver holds its MMIO base in.           *)
(* ------------------------------------------------------------------- *)
Definition vdev_srcok_pos_a5 : SrcOk (mword_of_int 15 : mword 5) := _.
Definition vdev_srcok_pos_a4 : SrcOk (mword_of_int 14 : mword 5) := _.
Fail Definition vdev_srcok_neg : SrcOk Rtp := _.

End WpVirtioDev.
