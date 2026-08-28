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
Require Import DevModel RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile HartTp WpNext.
Require Import KMap.
Require Import KptPt.
Require Import RiscvExtras.
Require Import SRegime.
Require Import HartLift HartSpan HartSwp HartSMem.
Require Import WpSmodePtEngine.
Require Import KptGoodb.
Require Import WpIntrInv.
Require Import IntrDefs WpSmodeIntr.
Require Import VirtioModel.
Require Import WpVirtio.
Require Import DiskPtsto VirtioProto WpUart.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import WpVirtioExec.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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
    /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v
    /\ v_cache v' = v_cache v /\ v_taken v' = v_taken v
    /\ v_inflight v' = v_inflight v.
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
    /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v
    /\ v_cache v' = v_cache v /\ v_taken v' = v_taken v
    /\ v_inflight v' = v_inflight v.
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
Context `{!riscvGS Σ, !xv6G Σ}.
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
  (* [a8] IS [ea]: the model's [subrange 63 0] / [sign_extend' 64] round trip.
     Collapsing the [let] chain FIRST is what keeps the engine's own [ea]
     unifiable with this leaf's premises. *)
  assert (Ha8ea : a8 = ea)
    by (unfold a8; rewrite subrange_id sign_extend'_id; reflexivity).
  (* THE DEVICE WINDOW'S OWN CLAIM, off [hw_config]'s STATIC bundle.  A
     device page is mapped by the kernel table at every tier, so -- unlike a
     RAM window, whose claim rides beside the atomic update -- nothing here
     has to open an invariant to learn its [ppn]. *)
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  pose proof (pa_of_id a8 Ha8lt) as Hpaid.
  assert (Hdcls : dev_cls 4 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)).
  { rewrite Hpaid. split; [ exact (dev_addr_virtio a8 Hrange) | ].
    split; [ exact (virtio_pa_not_in_clint a8 Hrange) | ].
    exact (pma_access_io a8 4 virtio_base (virtio_base + virtio_size)
             (proj1 Hrange) (proj2 Hrange) eq_refl eq_refl
             (pma_width_ok 4 eq_refl eq_refl)). }
  assert (Hdaddr : dev_addr (pa_of (kpt_leaf_ppn (svpn_of a8)) a8) = true)
    by (rewrite Hpaid; exact (dev_addr_virtio a8 Hrange)).
  assert (Hpalignp : is_aligned_paddr
            (Physaddr (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)) 4 = true)
    by (rewrite Hpaid; exact Halign).
  iIntros "Hcg Hpc #Hinstr #Hvinv HR Hacc Hcont".
  iApply (wp_instr_s_sconf m n false false pc is_rvc
            (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4))
            (fun (_CIDx : CpuId) npc _ms' m' n' =>
               ∃ w : bv 32,
                 ⌜npc = add_vec_int pc (if is_rvc then 2 else 4)⌝ ∗
                 ⌜m' = <[Regidx rd := regval_into_reg (ldval w)]> m⌝ ∗
                 ⌜n' = n⌝ ∗ S w)%I
            with "Hcg Hpc Hinstr [HR Hacc Hcont]").
  iApply bi.later_intro.
  rename CID into CID0.
  iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HR Hacc".
  - (* ---------------- THE INSTRUCTION ---------------- *)
    iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
    assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
      by exact (src_ok_rget_indep m rs1 CID CID0).
    iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
      "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
        Hmdl & Hmenv)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                        HMPP & HTVM).
    (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
       [WpIntrInv.sda_slot_acc] below, the one place the two translation
       arms are told apart. *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Htc & #Hwit)".
    iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
        %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
        %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
           [sda_Drw] under the kernel table, the EMPTY set under Bare. ---- *)
    iDestruct (sda_slot_acc (CID := CID) kt (DfracOwn 1) mst0 MENVCFG_S
                 pmar0 eq_refl HSXL HMPRV (pma_all_ram Hpma_all)
                 with "Htr Hms Hpriv Hmenv Hpma Hhtif Hmisa")
      as (SD satp0 tlbv pcfg paddr)
      "(%Hdisj & %Hsub & %Hsok & %Hpok & Htrobl & Hrw & Hro & HRes & Hclose)".
    destruct Hpok as (HpA & HpOrd & HpX & HpW & HpR & HpCov).
    iDestruct "Hkmapb" as "[#Hkmb #Hgc]".
    iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic
                 with "Hkmb") as "#Hclaim".
    iAssert (sr_swp_res (strans_regime (CID := CID))
               (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
      with "[HRes]" as "HRes".
    { rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)).
      rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
    iDestruct "Hresv" as (rr) "Hfrag".
    (* the tower's lookups, POSED: an [ltac:] in argument position runs
       before the application's implicits are solved (durable-notes). *)
    pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
    pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
    pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
    assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
            = true) by (rewrite Lmst; exact HMXR).
    assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
            = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
    assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
            by (rewrite Lmst; exact HSXL).
    assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
              (register_lookup satp
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
            = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
            by (rewrite Lsatp;
                exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
    assert (Lep : effectivePrivilege (Load Data) (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
            = returnM Supervisor)
            by (rewrite Lmst;
                exact (effectivePrivilege_mprv0 (Load Data) _ Supervisor HMPRV)).
    change (execute (LOAD (imm, Regidx rs1, Regidx rd, is_unsigned, 4)))
      with (execute_LOAD imm (Regidx rs1) (Regidx rd) is_unsigned 4).
    assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                    (sign_extend' 64 imm) = a8)
      by (rewrite Lpin_rs1 Ha8ea; reflexivity).
    assert (Lva : is_aligned_vaddr (Virtaddr
              (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                 (sign_extend' 64 imm))) 4 = true)
      by (rewrite Hea; exact Halign).
    iApply (swp_mono (CID := CID)
              with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
    2:{ iApply (swp_execute_LOAD_dev_S4_ex (CID := CID)
                  SD sda_Dro (sda_Df (DfracOwn 1))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                  imm rs1 rd is_unsigned (tp_pin (CID := CID) m)
                  (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)
                  pmar0 pcfg paddr
                  S (Mobl_dev4_ex (pa_of (kpt_leaf_ppn (svpn_of a8)) a8) S)
                  (sr_swp_res (strans_regime (CID := CID))) rr
                  (sr_swp_mode (strans_regime (CID := CID)) satp0)
                  Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                  (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                  (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_htif _ _ _ _ _ _ _)
                  (sda_rs_pma _ _ _ _ _ _ _) (sda_rs_pcfg _ _ _ _ _ _ _)
                  (sda_rs_paddr _ _ _ _ _ _ _)
                  Lmxr Lpmm Lsxl
                  (hval_transform_effective_address_S_mode
                     (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                        (sign_extend' 64 imm))
                     (Load Data)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                     (sda_rs_priv _ _ _ _ _ _ _)
                     Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                  (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                  Lep
                  HpA HpOrd HpR HpCov (pma_all_io Hpma_all) Hdcls
                  Lva Hpalignp Hrdnz
                  (swp_dev_read_node4_ex (CID := CID)
                     (pa_of (kpt_leaf_ppn (svpn_of a8)) a8) S Hdaddr)
                  with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HR Hacc]").
        - (* the data translation *)
          iIntros "Hfrag HRes Hrw Hro".
          rewrite Hea.
          iApply ("Htrobl" $! KT0 (Load Data) KP_rw
                    a8 (kpt_leaf_ppn (svpn_of a8)) rr
                    with "[%] [%] [%] [%] [%] Hwit Hclaim Hcert
                    Hfrag HRes Hrw Hro").
          + apply _.
          + exact (or_intror (or_introl eq_refl)).
          + exact I.
          + exact Ha8lt.
          + exact Hpaid.
        - (* THE MMIO READ NODE: the disk invariant is opened HERE, and it is
             the ghost callback -- not a points-to -- that names the word. *)
          iIntros (sigma) "Hsi".
          iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
          iInv "Hvinv" as ">Hdbody" "Hdclose".
          iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
          iDestruct (dev_interp_agree_virtio with "Hdev Hvf") as %Hveq.
          iMod ("Hacc" $! vst Hvok with "Hproto HR") as (w) "(%Hrd_v & Hproto & HS)".
          iMod ("Hdclose" with "[Hvf Hproto]") as "_".
          { iApply bi.later_intro. iExists vst. iFrame. iPureIntro. exact Hvok. }
          iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
          iModIntro. iExists w, sigma.(mdev).
          iSplitR.
          { iPureIntro. rewrite Hpaid.
            apply (dev_read_virtio sigma.(mdev) a8 w Hrange).
            rewrite Hveq. exact Hrd_v. }
          iApply bi.later_intro. iMod "Hb2" as "_". iModIntro.
          destruct sigma as [srx mmx ddx]; cbn [mdev sregs mem].
          iFrame "Hreg Hmem Hdev HS". }
    (* ---- the post ---- *)
    iIntros (e) "(-> & Hpost)".
    iDestruct "Hpost" as (w) "(Hfile & Hland)".
    iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & Hany & HS)".
    iSplitR; [done|].
    iAssert (∃ tv2 : type_of_register tlb,
               hreg_frame (CID := CID)
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) SD ∗
               hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
               strans_res_at (CID := CID) satp0 tv2)%I
      with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
    { destruct Hshape as [-> | (tvx & ->)].
      - iExists tlbv. iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
               sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
      - iExists tvx.
        iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hrw") as "Hrw".
        iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hro") as "Hro".
        iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (register_set tlb tvx
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
               register_lookup_set) in "HRes".
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite sda_rs_satp. iExact "HRes". }
    (* the slot re-seals itself, at the landing tlb value *)
    iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes") as
      "(Htr & Hms & Hpriv & Hmenv)".
    iExists (add_vec_int pc (if is_rvc then 2 else 4)), mst0,
            (<[Regidx rd := regval_into_reg (ldval w)]> m), n.
    iFrame "HPC HnPC Hany".
    iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
    { rewrite /sconf_at_priv. iExists mdv0.
      iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      iPureIntro. split; assumption. }
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg (ldval w)]> m
                      !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    iSplitL "Htr Hstk Harm".
    { rewrite /sie_cap -Hsp. iFrame "Hstk Htr Harm Htc Hwit". }
    iSplitL "Hfile".
    { iEval (rewrite (tp_pin_upd m rd (regval_into_reg (ldval w)) Hrdtp))
        in "Hfile". iExact "Hfile". }
    iExists w. iFrame "HS". iPureIntro. split_and!; reflexivity.
  - (* ---------------- THE CONTINUATION ---------------- *)
    iIntros (npc ms' m' n') "Hcg' Hpc' Hpay".
    iDestruct "Hpay" as (w) "(-> & -> & -> & HS)".
    iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
    iSpecialize ("Hcont" $! CID with "[%]"); [ exact Hs | ].
    iApply ("Hcont" $! w with "Hcg' Hpc' HS").
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
  (* [a8] IS [ea]; collapse the [let] chain before anything unifies. *)
  assert (Ha8ea : a8 = ea)
    by (unfold a8; rewrite subrange_id sign_extend'_id; reflexivity).
  (* the device window's own claim, off [hw_config]'s STATIC bundle *)
  assert (Hdevstatic : kmap_static (svpn_of a8) KP_rw)
    by (apply kmap_class_rw; right; exact Hdevvpn).
  pose proof (static_canon_lo a8 KP_rw Hdevstatic Hcanon) as Ha8lt.
  pose proof (pa_of_id a8 Ha8lt) as Hpaid.
  assert (Hdcls : dev_cls 4 (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)).
  { rewrite Hpaid. split; [ exact (dev_addr_virtio a8 Hrange) | ].
    split; [ exact (virtio_pa_not_in_clint a8 Hrange) | ].
    exact (pma_access_io a8 4 virtio_base (virtio_base + virtio_size)
             (proj1 Hrange) (proj2 Hrange) eq_refl eq_refl
             (pma_width_ok 4 eq_refl eq_refl)). }
  assert (Hpalignp : is_aligned_paddr
            (Physaddr (pa_of (kpt_leaf_ppn (svpn_of a8)) a8)) 4 = true)
    by (rewrite Hpaid; exact Halign).
  iIntros "Hcg Hpc #Hinstr #Hvinv HR Hacc Hcont".
  iApply (wp_instr_s_sconf m n false false pc is_rvc
            (STORE (imm, Regidx rs2, Regidx rs1, 4))
            (fun (_CIDx : CpuId) npc _ms' m' n' =>
               (⌜npc = add_vec_int pc (if is_rvc then 2 else 4)⌝ ∗
                ⌜m' = m⌝ ∗ ⌜n' = n⌝ ∗ S)%I)
            with "Hcg Hpc Hinstr [HR Hacc Hcont]").
  iApply bi.later_intro.
  rename CID into CID0.
  iIntros (CID Hs). rewrite /sconf_step_obl. iSplitL "HR Hacc".
  - (* ---------------- THE INSTRUCTION ---------------- *)
    iIntros "Hsc Hcap Hfile HPC HnPC Hresv".
    assert (Lpin_rs1 : tp_pin (CID := CID) m !!! Regidx rs1 = rget m rs1)
      by exact (src_ok_rget_indep m rs1 CID CID0).
    assert (Lpin_rs2 : tp_pin (CID := CID) m !!! Regidx rs2 = rget m rs2)
      by exact (src_ok_rget_indep m rs2 CID CID0).
    iDestruct (sconf_to_cells (CID := CID) with "Hsc") as (mst0 mdv0)
      "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
        Hmdl & Hmenv)".
    pose proof Hmsf as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD &
                        HMPP & HTVM).
    (* THE SLOT STAYS FOLDED -- the pre-port shape; the frame comes out of
       [WpIntrInv.sda_slot_acc] below, the one place the two translation
       arms are told apart. *)
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Htc & #Hwit)".
    iDestruct (hw_config_cert (CID := CID) with "Hhw") as "#Hcert".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS &
        %HmisaC & %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 &
        %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    subst misa0.
    (* ---- THE FRAME, OUT OF THE FOLDED SLOT.  [SD] is abstract here:
           [sda_Drw] under the kernel table, the EMPTY set under Bare. ---- *)
    iDestruct (sda_slot_acc (CID := CID) kt (DfracOwn 1) mst0 MENVCFG_S
                 pmar0 eq_refl HSXL HMPRV (pma_all_ram Hpma_all)
                 with "Htr Hms Hpriv Hmenv Hpma Hhtif Hmisa")
      as (SD satp0 tlbv pcfg paddr)
      "(%Hdisj & %Hsub & %Hsok & %Hpok & Htrobl & Hrw & Hro & HRes & Hclose)".
    destruct Hpok as (HpA & HpOrd & HpX & HpW & HpR & HpCov).
    iDestruct "Hkmapb" as "[#Hkmb #Hgc]".
    iDestruct (kmap_static_claims_at (svpn_of a8) KP_rw Hdevstatic
                 with "Hkmb") as "#Hclaim".
    iAssert (sr_swp_res (strans_regime (CID := CID))
               (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
      with "[HRes]" as "HRes".
    { rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)).
      rewrite sda_rs_satp sda_rs_tlb. iExact "HRes". }
    iDestruct "Hresv" as (rr) "Hfrag".
    (* the tower's lookups, POSED -- an [ltac:] in argument position runs
       before the application's implicits are solved (durable-notes). *)
    pose proof (sda_rs_mst mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmst.
    pose proof (sda_rs_menv mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lmenv.
    pose proof (sda_rs_satp mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv) as Lsatp.
    assert (Lmxr : eq_vec (_get_Mstatus_MXR (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))) ('b"0")
            = true) by (rewrite Lmst; exact HMXR).
    assert (Lpmm : pmm_mode_backwards (_get_MEnvcfg_PMM (register_lookup menvcfg
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
            = PMM_Disabled) by (rewrite Lmenv; vm_compute; reflexivity).
    assert (Lsxl : _get_Mstatus_SXL (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) = 'b"10")
            by (rewrite Lmst; exact HSXL).
    assert (Lmd : satpMode_of_bits RV64 (_get_Satp64_Mode (Mk_Satp64
              (register_lookup satp
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))))
            = Some (sr_swp_mode (strans_regime (CID := CID)) satp0))
            by (rewrite Lsatp;
                exact (sr_swp_mode_ok (strans_regime (CID := CID)) satp0 Hsok)).
    assert (Lep : effectivePrivilege (Store Data) (register_lookup mstatus
              (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)) Supervisor
            = returnM Supervisor)
            by (rewrite Lmst;
                exact (effectivePrivilege_mprv0 (Store Data) _ Supervisor HMPRV)).
    change (execute (STORE (imm, Regidx rs2, Regidx rs1, 4)))
      with (execute_STORE imm (Regidx rs2) (Regidx rs1) 4).
    assert (Hea : add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                    (sign_extend' 64 imm) = a8)
      by (rewrite Lpin_rs1 Ha8ea; reflexivity).
    assert (Lva : is_aligned_vaddr (Virtaddr
              (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                 (sign_extend' 64 imm))) 4 = true)
      by (rewrite Hea; exact Halign).
    assert (Lsv : autocast (T := mword)
              (subrange_vec_dec (tp_pin (CID := CID) m !!! Regidx rs2)
                 (Z.sub (Z.mul 4 8) 1) 0) = storeword)
      by (rewrite Lpin_rs2; reflexivity).
    iApply (swp_mono (CID := CID)
              with "[HPC HnPC Hmie Hmdl Hhalf Htie Hstk Harm Hclose] [-]").
    2:{ iApply (swp_execute_STORE_dev_S4 (CID := CID)
                  SD sda_Dro (sda_Df (DfracOwn 1))
                  (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                  imm rs2 rs1 (tp_pin (CID := CID) m)
                  (pa_of (kpt_leaf_ppn (svpn_of a8)) a8) storeword
                  pmar0 pcfg paddr
                  S (sr_swp_res (strans_regime (CID := CID))) rr
                  (sr_swp_mode (strans_regime (CID := CID)) satp0)
                  Lsv
                  Hdisj (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                  (sda_in_pma_D SD) (sda_in_pcfg_D SD) (sda_in_paddr_D SD) (sda_in_htif_D SD)
                  (sda_rs_priv _ _ _ _ _ _ _) (sda_rs_pma _ _ _ _ _ _ _)
                  (sda_rs_pcfg _ _ _ _ _ _ _) (sda_rs_paddr _ _ _ _ _ _ _)
                  (sda_rs_htif _ _ _ _ _ _ _)
                  Lmxr Lpmm Lsxl
                  (hval_transform_effective_address_S_mode
                     (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (add_vec (tp_pin (CID := CID) m !!! Regidx rs1)
                        (sign_extend' 64 imm))
                     (Store Data)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_priv_D SD) (sda_in_menv_D SD) (sda_in_satp_D SD)
                     (sda_rs_priv _ _ _ _ _ _ _)
                     Lep eq_refl eq_refl eq_refl Lmxr Lpmm Lsxl Lmd)
                  (hval_translationMode_S_mode (SD ∪ sda_Dro) SD
                     (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)
                     (sr_swp_mode (strans_regime (CID := CID)) satp0)
                     (sda_in_mst_D SD) (sda_in_satp_D SD) Lsxl Lmd)
                  Lep
                  HpA HpOrd HpW HpCov (pma_all_io Hpma_all) Hdcls
                  Lva Hpalignp
                  with "Hcert Hfrag HRes Hfile Hrw Hro [Htrobl] [HR Hacc]").
        - (* the data translation *)
          iIntros "Hfrag HRes Hrw Hro".
          rewrite Hea.
          iApply ("Htrobl" $! KT0 (Store Data) KP_rw
                    a8 (kpt_leaf_ppn (svpn_of a8)) rr
                    with "[%] [%] [%] [%] [%] Hwit Hclaim Hcert
                    Hfrag HRes Hrw Hro").
          + apply _.
          + exact (or_intror (or_intror (or_introl eq_refl))).
          + exact eq_refl.
          + exact Ha8lt.
          + exact Hpaid.
        - (* THE MMIO WRITE NODE: the disk invariant is opened HERE, and the
             ghost callback both licenses the write and re-closes it. *)
          iIntros (sigma) "Hsi".
          iDestruct "Hsi" as "[Hreg [Hmem Hdev]]".
          iInv "Hvinv" as ">Hdbody" "Hdclose".
          iDestruct "Hdbody" as (vst) "(Hvf & Hproto & %Hvok)".
          iDestruct (dev_interp_agree_virtio with "Hdev Hvf") as %Hveq.
          iMod ("Hacc" $! vst Hvok with "Hproto HR")
            as (vst') "(%Hvw & %Hvok' & Hproto & HS)".
          iMod (dev_interp_update_virtio sigma.(mdev) vst vst'
                  with "Hdev Hvf") as "[Hdev' Hvf']".
          iMod ("Hdclose" with "[Hvf' Hproto]") as "_".
          { iApply bi.later_intro. iExists vst'. iFrame. iPureIntro. exact Hvok'. }
          iMod (fupd_mask_subseteq ∅) as "Hb2"; [set_solver|].
          iModIntro. iExists (set_dvirtio sigma.(mdev) vst').
          iSplitR.
          { iPureIntro. rewrite Hpaid.
            apply (dev_write_virtio sigma.(mdev) a8 storeword vst' Hrange).
            rewrite Hveq. exact Hvw. }
          iApply bi.later_intro. iMod "Hb2" as "_". iModIntro.
          destruct sigma as [srx mmx ddx]; cbn [mdev sregs mem].
          iFrame "Hreg Hmem Hdev' HS". }
    (* ---- the post ---- *)
    iIntros (e) "(-> & Hfile & Hland)".
    iDestruct "Hland" as (rsf) "(%Hshape & Hrw & Hro & HRes & HS & Hfrag)".
    iSplitR; [done|].
    iAssert (∃ tv2 : type_of_register tlb,
               hreg_frame (CID := CID)
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) SD ∗
               hreg_frame_ro (CID := CID) (sda_Df (DfracOwn 1))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tv2) sda_Dro ∗
               strans_res_at (CID := CID) satp0 tv2)%I
      with "[Hrw Hro HRes]" as (tv2) "(Hrw & Hro & HRes)".
    { destruct Hshape as [-> | (tvx & ->)].
      - iExists tlbv. iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv))
               sda_rs_satp sda_rs_tlb) in "HRes". iExact "HRes".
      - iExists tvx.
        iDestruct (sda_rw_ext_D SD _ _ Hsub (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hrw") as "Hrw".
        iDestruct (sda_ro_ext _ _ _ (sda_set_tlb mst0 MENVCFG_S satp0 pmar0
                     pcfg paddr tlbv tvx) with "Hro") as "Hro".
        iFrame "Hrw Hro".
        iEval (rewrite -(sr_swp_res_agree (strans_regime (CID := CID))
                 (register_set tlb tvx
                    (sda_rs mst0 MENVCFG_S satp0 pmar0 pcfg paddr tlbv)))
               register_lookup_set) in "HRes".
        rewrite irrelevant_register_set; [| vm_compute; reflexivity].
        rewrite sda_rs_satp. iExact "HRes". }
    (* the slot re-seals itself, at the landing tlb value *)
    iDestruct ("Hclose" $! tv2 with "Hrw Hro HRes") as
      "(Htr & Hms & Hpriv & Hmenv)".
    iExists (add_vec_int pc (if is_rvc then 2 else 4)), mst0, m, n.
    iFrame "HPC HnPC".
    iSplitL "Hfrag"; [ iApply (resv_any_intro _ None with "Hfrag") | ].
    iSplitL "Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
    { rewrite /sconf_at_priv. iExists mdv0.
      iFrame "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv".
      iPureIntro. split; assumption. }
    iSplitL "Htr Hstk Harm".
    { rewrite /sie_cap. iFrame "Hstk Htr Harm Htc Hwit". }
    iFrame "Hfile HS". iPureIntro. split_and!; reflexivity.
  - (* ---------------- THE CONTINUATION ---------------- *)
    iIntros (npc ms' m' n') "Hcg' Hpc' (-> & -> & -> & HS)".
    iDestruct (sie_cap_gpr_at_close with "Hcg'") as "Hcg'".
    iApply ("Hcont" $! CID with "[%] Hcg' Hpc' HS"). exact Hs.
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
       /\ v_used_idx v' = v_used_idx v /\ v_disk v' = v_disk v
       (* AND THE VOLATILE WRITE CACHE (claude-notes/projects/async-disk.md):
          what the device is still holding decides which branch of an
          in-flight write's sequential permit is outstanding, so a
          protocol-neutral store has to leave both fields alone.  Both stores
          the live driver makes do. *)
       /\ v_cache v' = v_cache v /\ v_taken v' = v_taken v
       (* ...AND THE SERVED-AHEAD SET (finding 5): the window is a watermark
          plus the positions answered out of turn, so a protocol-neutral
          store has to leave that set alone too ([virtio_write_inflight]). *)
       /\ v_inflight v' = v_inflight v) ->
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
    destruct (Hwrite v Hvok)
      as (v' & Hvw & Hvok' & Hcfg' & Hseen' & Hused' & Hdisk' & Hca' & Htk' &
          Hah').
    iDestruct (virtio_proto_stable γd v v' Hcfg' Hseen' Hah' Hused' Hca' Htk'
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
