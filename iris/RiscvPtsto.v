(* RiscvPtsto.v -- riscvGS, register/memory points-to, the regstate/heap bridge. *)
From Stdlib Require Import Eqdep_dec ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var.
From iris.algebra Require Import csum excl agree.
From iris.program_logic Require Import weakestpre.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang.
Require Import PtreeType.   (* [ptree]: the carrier of the shared kernel table's ghost *)
Local Open Scope Z_scope.

(* Name [mword] locally (qualified target) rather than [Require Import
   SailStdpp.Values] -- the latter would leak Sail's key typeclass
   instances into every file that imports RiscvPtsto (durable-notes).  The
   VA-based points-to layer below ([svpn_of]/[pa_of]/[kmap_at]/↦ₘ/↦ₓ) is
   stated over mwords, so the name has to be in scope here. *)
Local Notation mword := SailStdpp.Values.mword.

(* ===== RiscvModelIris ===== *)
(* ====================================================================== *)
(* RiscvModelIris.v                                                        *)
(*                                                                         *)
(* LAYER 2: the Iris program-logic layer over RiscvModelLang.v.            *)
(*                                                                         *)
(*   - register & memory [gen_heap]s, with points-to [r |->r v] / [a|->m b]*)
(*   - state_interp that BRIDGES the model's [regstate] to per-register    *)
(*     points-to via an existential register map + an agreement invariant  *)
(*     (axiom-free: existT injectivity goes through Eqdep_dec, register     *)
(*      has decidable equality; no Finite/UIP needed).                     *)
(*   - the two bridge lemmas [reg_valid] / [reg_update] and a memory read  *)
(*     lemma [mem_valid].                                                   *)
(*                                                                         *)
(* The WP for ADD *through* [try_step] (symbolic unfolding of fetch/decode/*)
(* execute/currentlyEnabled) is the next milestone; this file provides the *)
(* ghost-state foundation it will rest on.                                 *)
(* ====================================================================== *)




(* ---------------------------------------------------------------------- *)
(* 0. Two small facts about the model's [register_beq] and [existT].       *)
(* ---------------------------------------------------------------------- *)

Lemma register_beq_true (k r : register) : register_beq k r = true -> k = r.
Proof.
  destruct k, r; simpl; intro E; try discriminate;
    f_equal; autorewrite with register_beq_iffs in E; exact E.
Qed.

Lemma register_beq_false (k r : register) : k <> r -> register_beq k r = false.
Proof.
  intros Hne. destruct (register_beq k r) eqn:E; [|reflexivity].
  exfalso. apply Hne. by apply register_beq_true.
Qed.

(* existT injectivity on the (decidable) index type [register]: axiom-free. *)
Lemma reg_existT_inj (r : register) (v v' : type_of_register r) :
  existT r v = existT r v' -> v = v'.
Proof.
  apply (inj_pair2_eq_dec register (fun x y => decide (x = y))).
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. Ghost state: a register map ([ghost_map]) and a memory heap           *)
(*    ([gen_heap]).  The registers use [ghost_map] -- an explicitly-named   *)
(*    authoritative gmap ([riscv_reg_name]) with per-key elements -- rather *)
(*    than [gen_heap]; the byte memory keeps its [gen_heap].                *)
(* ---------------------------------------------------------------------- *)

(* The two kernel permission CLASSES of the etext region split (rwx-kmap):
   text pages are mapped R|X, data/device pages R|W.  The enum lives here,
   above [riscvGS], so the class can carry the kernel-mapping claim ghost
   (KMap.v) over it; the PTE flag bytes and the vpn classifier are KptPt
   §15's. *)
Inductive kperm : Set := KP_rx | KP_rw.

Global Instance kperm_eq_dec : EqDecision kperm.
Proof. solve_decision. Defined.

(* the shared kernel page table's resource algebra: one-shot agreement on
   the A/D-canonical table. *)
Definition kptR : cmra := csumR (exclR unitO) (agreeR (leibnizO ptree)).

Class riscvGS (Σ : gFunctors) := RiscvGS {
  riscv_invGS :: invGS Σ;
  riscv_regGS :: ghost_mapG Σ register (sigT type_of_register);
  (* one register-map ghost name PER hart.  A [ghost_map] element on
     [cpu_reg_name c] owns a register of hart [c].  The function is total (every
     [CPU] is a real hart) and its per-hart authoritative maps are threaded by
     [gregs_interp] below. *)
  cpu_reg_name : CPU -> gname;
  riscv_memGS :: gen_heapGS Arch.pa (bv 8) Σ;
  (* the device fabric (DevModel.v): one [ghost_var] per device, in the
     standard halves pattern -- [state_interp] holds one half (the "auth"),
     the other half (the "frag") floats freely and is typically stored in an
     invariant shared between the driver's hart and the device thread. *)
  riscv_uartGS :: ghost_varG Σ uart_state;
  riscv_plicGS :: ghost_varG Σ plic_state;
  riscv_virtioGS :: ghost_varG Σ virtio_state;
  uart_name : gname;
  plic_name : gname;
  virtio_name : gname;
  (* the kernel-mapping claim ghost (KMap.v, rwx-kmap): one global
     vpn ↦ (ppn, class) map.  Lives here -- not as a separate class --
     because [tlb_inv_pt] rides inside [sie_cap_gpr], and a separate
     class would have to be threaded through every sconf-tier file;
     like [uart_name]/[plic_name] it is global (not per-hart). *)
  (* pinned to the SAIL key instances (Decidable_eq_mword/Countable_mword),
     because every use site (KMap/KptPt/adequacy) imports Sail and elaborates
     [gmap (mword 27)] with them; without pinning, this field would take
     stdpp's bv_eq_dec/bv_countable (RiscvPtsto does not import the Sail
     instance modules) and the ghost_mapG key-instance args would not unify. *)
  riscv_kmapGS :: @ghost_mapG Σ (SailStdpp.Values.mword 27) (SailStdpp.Values.mword 44 * kperm)
                    (@SailStdpp.Instances.Decidable_eq_mword 27) (@SailStdpp.Instances.Countable_mword 27);
  kmap_name : gname;
  (* THE SHARED KERNEL PAGE TABLE's ghost (claude-notes/projects/
     kpt-share.md): a ONE-SHOT agreement on the table's A/D-CANONICAL form
     ([PtTree.ptree_canon]).  Adequacy mints the unset token [Cinl (Excl ())];
     main's kvm assembly shoots it, at the tree kvminit built, to the
     PERSISTENT [Cinr (to_agree …)] every hart then carries in its
     translation residue.  Agreement is enough -- not an order -- because
     the Svadu A/D write-back leaves the canonical table INVARIANT
     ([PtTree.ptree_canon_set_leaf]), so a write-back needs no ghost update
     at all.  Lives HERE, not in a separate class, for exactly the reason
     [kmap_name] does: the residue rides inside [sie_cap]/[intr_frame], so a
     class would have to be threaded through every sconf-tier file. *)
  riscv_kptGS :: inG Σ kptR;
  kpt_name : gname;
  (* the S-mode translation-slot arm bit ('b"0" = Bare, 'b"1" = kernel PT
     installed): a global ghost name (like [kmap_name]) tracking which arm
     of [strans_inv] the capability's translation slot is in.  A client
     half held outside the slot is a "still-Bare receipt" pinning the arm;
     the kvminithart switch flips it with both halves.  The [ghost_varG Σ
     (mword 1)] functor instance comes from [sieG] at the use sites (NOT a
     field here -- a second [ghost_varG Σ (mword 1)] instance would make
     typeclass resolution ambiguous between two functor slots).
     PER-HART, like [cpu_reg_name]: satp and tlb are per-hart registers, so
     which arm a hart's translation slot is in is a per-hart fact, and the
     shared-kernel-table sweep (claude-notes/projects/kpt-share.md) needs
     every hart to flip its own bit at its own kvminithart. *)
  strans_name : CPU -> gname;
}.

(* [reg_name] is the register-map ghost name of the AMBIENT hart [cpu_id].  It is
   what every [r ↦ᵣ v] / [reg_interp] / [reg_valid] / [reg_update] silently talks
   about, so those keep their single-CPU spelling: which hart they concern is
   selected by the surrounding [CpuId] instance, never written out. *)
Definition reg_name `{!riscvGS Σ} `{CpuId} : gname := cpu_reg_name cpu_id.

(* register points-to: [r |->r v] owns register [r] (of the ambient hart)
   holding [v].  Backed by a [ghost_map] element on [reg_name]. *)
Definition reg_pointsto `{!riscvGS Σ} `{CpuId} (r : register) (dq : dfrac)
    (v : type_of_register r) : iProp Σ :=
  ghost_map_elem reg_name r dq (existT r v).

Notation "r ↦ᵣ{ dq } v" := (reg_pointsto r dq v)
  (at level 20, format "r  ↦ᵣ{ dq }  v") : bi_scope.
Notation "r ↦ᵣ v" := (reg_pointsto r (DfracOwn 1) v)
  (at level 20, format "r  ↦ᵣ  v") : bi_scope.
(* discarded (persistent, duplicable) read-only register ownership.  Used for the
   configuration registers (misa, mseccfg, the PMP/PMA config, the HTIF base, ...)
   that the boot sequence never writes: once persisted they need not be threaded
   through (or returned by) every WP -- see [hw_config] in RiscvFetchExec.v. *)
Notation "r ↦ᵣ□ v" := (reg_pointsto r DfracDiscarded v)
  (at level 20, format "r  ↦ᵣ□  v") : bi_scope.
(* The concrete physical RAM of the platform: a single DRAM bank of
   [ram_size] bytes based at [ram_base] (0x80000000), matching the Sail
   model's RAM-region PMA (model-xv6iris/sail-config-rv64d.json) and the
   xv6 memory map: 128 MiB, so that [ram_base + ram_size] = xv6's PHYSTOP
   = 0x88000000 (kernel/memlayout.h; QEMU runs with `-m 128M`). *)
Definition ram_base : Z := 0x80000000.       (* 2147483648 *)
Definition ram_size : Z := 0x8000000.        (* 134217728 = 128 MiB *)

(* A physical byte address is "real" RAM iff it lies inside that DRAM bank.
   This is STRICTLY stronger than merely being outside the platform MMIO
   ranges: the whole bank sits above every MMIO window (CLINT ends at
   0x20C0000, SIG at 0xC000020, both far below 0x80000000), so being RAM
   discharges the model's [within_clint]/[within_sig] MMIO checks (see
   [addr_is_ram_not_in_clint]/[addr_is_ram_not_in_sig] below, which feed
   [within_clint_false]/[within_sig_false]).  Being a concrete range it also
   pins the address's high bits (bits 63:31 are 0b1..., bits 63:39 = 0), which
   lets the higher-level WPs discharge their per-address geometry obligations
   (Sv39 canonicality, identity translation, PMP TOR match) purely from an
   owned points-to rather than carrying them as explicit preconditions.
   ([within_htif] depends on the [htif_tohost_base] register, not the address,
   so it is handled separately by owning that register.) *)
Definition addr_is_ram (a : Arch.pa) : Prop :=
  (ram_base <= uint a < ram_base + ram_size)%Z.

(* rwx-kmap: the RAM bank split at etext.  [text_end] is hardcoded here to
   keep the base memory layer off the kernel dump (KernelSyms.etext =
   0x80007000 is cross-checked by vm_compute higher up: KptExecMap's
   [etext_vpn], KvmSpec).  Kernel TEXT [ram_base, text_end) is mapped R|X
   by the kernel page table, kernel DATA [text_end, PHYSTOP) R|W; the
   points-to layer records the region so stores to text are unprovable
   and fetches carry their own R|X evidence. *)
Definition text_end : Z := 0x80007000.
Definition addr_is_text (a : Arch.pa) : Prop :=
  (ram_base <= uint a < text_end)%Z.
Definition addr_is_kdata (a : Arch.pa) : Prop :=
  (text_end <= uint a < ram_base + ram_size)%Z.

Lemma addr_is_text_ram a : addr_is_text a -> addr_is_ram a.
Proof.
  unfold addr_is_text, addr_is_ram, text_end, ram_base, ram_size. lia.
Qed.
Lemma addr_is_kdata_ram a : addr_is_kdata a -> addr_is_ram a.
Proof.
  unfold addr_is_kdata, addr_is_ram, text_end, ram_base, ram_size. lia.
Qed.
Lemma addr_is_ram_split a : addr_is_ram a <-> addr_is_text a \/ addr_is_kdata a.
Proof.
  unfold addr_is_ram, addr_is_text, addr_is_kdata, text_end, ram_base, ram_size.
  lia.
Qed.

(* The two legacy MMIO-disjointness predicates, kept as the interface the
   model discharges ([within_clint_false]/[within_sig_false] consume them). *)
Definition not_in_clint (a : Arch.pa) : Prop :=
  (uint a < uint plat_clint_base \/ uint plat_clint_base + uint plat_clint_size <= uint a)%Z.
Definition not_in_sig (a : Arch.pa) : Prop :=
  (uint a < uint plat_sig_base \/ uint plat_sig_base + uint plat_sig_size <= uint a)%Z.

(* Being RAM implies being outside each MMIO window: the bank is above both. *)
Lemma addr_is_ram_not_in_clint a : addr_is_ram a -> not_in_clint a.
Proof.
  intros [Hlo _]. right.
  assert (uint plat_clint_base + uint plat_clint_size = 34340864)%Z as -> by (vm_compute; reflexivity).
  unfold ram_base in Hlo. lia.
Qed.

Lemma addr_is_ram_not_in_sig a : addr_is_ram a -> not_in_sig a.
Proof.
  intros [Hlo _]. right.
  assert (uint plat_sig_base + uint plat_sig_size = 201326624)%Z as -> by (vm_compute; reflexivity).
  unfold ram_base in Hlo. lia.
Qed.

(* Being RAM also implies being off the device fabric: the bus routes only
   sub-DRAM addresses ([dev_bound] = [ram_base]) to the UART/PLIC. *)
Lemma addr_is_ram_not_dev a : addr_is_ram a -> dev_addr a = false.
Proof.
  intros [Hlo _]. apply dev_addr_false.
  unfold dev_bound; unfold ram_base in Hlo. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The kernel-mapping CLAIM (uniform-claims): a persisted fragment of the  *)
(* kernel-mapping ghost map -- "vpn maps to ppn at class pc, under the     *)
(* current and all future regimes" (monotone across Bare→Sv39).  It        *)
(* carries BOTH the permission and the va→pa mapping; the points-to facts  *)
(* below are built on it.  Uniqueness is ghost-map library agreement.      *)
(* The auth / static-map machinery lives in KMap.v.                        *)
(* ---------------------------------------------------------------------- *)

(* the vpn of an S-mode va (moved here from RiscvExtras; the arithmetic
   lemmas [svpn_of_unsigned]/[svpn_of_unsigned_lo] remain there) *)
Definition svpn_of (a : mword 64) : mword 27 :=
  SailStdpp.TypeCasts.autocast (T := mword) (subrange_vec_dec
     (subrange_vec_dec (bits_of_virtaddr (Virtaddr a)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits).

(* The mapping fragment.  The [ghost_map_elem] key instances are given
   EXPLICITLY (fully qualified) to match the [riscv_kmapGS] field's pinning
   -- RiscvPtsto must NOT [Import] the Sail instance modules (they would
   clobber stdpp's bv instances for [Arch.pa]=mword 64 gen_heap keys; the
   durable-notes leak), so we cannot rely on TC search resolving
   [EqDecision (mword 27)] here. *)
Definition kmap_at `{!riscvGS Σ} (vpn : mword 27) (ppn : mword 44) (pc : kperm) : iProp Σ :=
  @ghost_map_elem Σ (mword 27) (mword 44 * kperm)
    (@SailStdpp.Instances.Decidable_eq_mword 27)
    (@SailStdpp.Instances.Countable_mword 27)
    riscv_kmapGS kmap_name vpn DfracDiscarded (ppn, pc).

Global Instance kmap_at_persistent `{!riscvGS Σ} vpn ppn pc :
  Persistent (kmap_at vpn ppn pc).
Proof. apply _. Qed.
Global Instance kmap_at_timeless `{!riscvGS Σ} vpn ppn pc :
  Timeless (kmap_at vpn ppn pc).
Proof. apply _. Qed.

(* UNIQUENESS: two claims for one vpn agree -- what lets split fractions
   of a [↦ₘ] recombine (their existential ppn witnesses coincide). *)
Lemma kmap_at_agree `{!riscvGS Σ} vpn ppn1 pc1 ppn2 pc2 :
  kmap_at vpn ppn1 pc1 -∗ kmap_at vpn ppn2 pc2 -∗ ⌜ppn1 = ppn2 /\ pc1 = pc2⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (ghost_map_elem_agree with "H1 H2") as %He.
  iPureIntro. injection He as -> ->. split; reflexivity.
Qed.

(* the pa a claim maps [va] to: the claim's ppn ++ [va]'s page offset *)
Definition pa_of (ppn : mword 44) (va : mword 64) : mword 64 :=
  zero_extend' 64 (concat_vec ppn (subrange_vec_dec va 11 0)).

(* memory points-to, VA-BASED (uniform-claims): owns the byte at the
   PHYSICAL address the kernel mapping takes [va] to, bundled with the
   claim itself -- for identity mappings (the static fragments) pa = va;
   for kstack vas pa is the kalloc-chosen page.  The KP_rw class is what
   makes stores provable ONLY through writable mappings; the R|X kernel
   text lives at the CODE points-to [↦ₓ] below.  The canonicality
   conjunct (positive Sv39 half) pins va ↔ (vpn, offset).  [dq] is a
   [dfrac]: [DfracOwn 1] = full (writable) ownership, [DfracDiscarded] =
   persistent/duplicable read-only ownership (the immutable kernel
   globals image [kernel_data]). *)
Definition mem_pointsto `{!riscvGS Σ} (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
  (∃ ppn : mword 44,
     kmap_at (svpn_of va) ppn KP_rw ∗
     ⌜(uint va < 274877906944)%Z⌝ ∗          (* 2^38: canonical, positive half *)
     ⌜addr_is_ram (pa_of ppn va)⌝ ∗
     pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn va) dq v)%I.
Notation "a ↦ₘ{ dq } v" := (mem_pointsto a dq v)
  (at level 20, format "a  ↦ₘ{ dq }  v") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership. *)
Notation "a ↦ₘ□ v" := (mem_pointsto a DfracDiscarded v)
  (at level 20, format "a  ↦ₘ□  v") : bi_scope.
(* default: full (writable) ownership. *)
Notation "a ↦ₘ v" := (mem_pointsto a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₘ  v") : bi_scope.

(* TIMELESS -- registered, because typeclass search does not unfold the
   [Definition] on its own: without this instance the [>] intro pattern on a
   byte taken out of an invariant fails with "iMod: cannot eliminate modality"
   on a hypothesis that visibly IS timeless. *)
Global Instance mem_pointsto_timeless `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (v : bv 8) :
  Timeless (mem_pointsto a dq v).
Proof. rewrite /mem_pointsto. apply _. Qed.

(* ---------------------------------------------------------------------- *)
(* SHARING a byte: agreement and the fractional split.  [↦ₘ] carries a real
   [dfrac], so a resource that is read-only-while-shared (a reference-counted
   kernel object: [struct file]'s immutable fields, an inode's, a buf's) can
   be handed out at a fraction and RECOMBINED when the last share comes back.
   Agreement is what makes the value-knowledge come for free: two holders of
   the same byte cannot disagree, so no separate [agree] ghost is needed.
   The byte-window forms below lift straight to [↦₂]/[↦₄]/[↦₈].              *)
Section mem_pointsto_share.
  Context `{!riscvGS Σ}.

  (* two owners of the same byte, at ANY two dfracs, agree on its value. *)
  Lemma mem_pointsto_agree a dq1 b1 dq2 b2 :
    a ↦ₘ{dq1} b1 -∗ a ↦ₘ{dq2} b2 -∗ ⌜b1 = b2⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H1 H2".
    iDestruct "H1" as (ppn1) "(Hk1 & _ & _ & Hp1)".
    iDestruct "H2" as (ppn2) "(Hk2 & _ & _ & Hp2)".
    iDestruct (kmap_at_agree with "Hk1 Hk2") as %[-> _].
    by iDestruct (pointsto_agree with "Hp1 Hp2") as %->.
  Qed.

  (* ...and the DUAL of agreement: full ownership of a byte is EXCLUSIVE, so an
     address owned outright cannot be an address owned at any dfrac at all.
     This is what makes SEPARATION carry the disjointness of two buffers -- a
     function whose contract takes two byte ranges as separate conjuncts never
     needs a pure non-aliasing side condition; the aliasing case is refuted from
     the resources themselves (see [mem_bytes_notin]). *)
  Lemma mem_pointsto_ne a1 a2 dq b1 b2 :
    a1 ↦ₘ b1 -∗ a2 ↦ₘ{dq} b2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H1 H2".
    iDestruct "H1" as (ppn1) "(Hk1 & _ & _ & Hp1)".
    iDestruct "H2" as (ppn2) "(Hk2 & _ & _ & Hp2)".
    destruct (decide (a1 = a2)) as [->|Hne]; [| by iPureIntro ].
    iDestruct (kmap_at_agree with "Hk1 Hk2") as %[-> _].
    by iDestruct (pointsto_ne with "Hp1 Hp2") as %Hne.
  Qed.

  (* the fractional split.  [kmap_at] is persistent, so the claim and the two
     pure conjuncts ride along on both halves at no cost. *)
  Lemma mem_pointsto_frac_split a q1 q2 b :
    a ↦ₘ{DfracOwn (q1 + q2)} b ⊣⊢ a ↦ₘ{DfracOwn q1} b ∗ a ↦ₘ{DfracOwn q2} b.
  Proof.
    rewrite /mem_pointsto. iSplit.
    - iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & Hp)".
      rewrite -dfrac_op_own pointsto_fractional.
      iDestruct "Hp" as "[Hp1 Hp2]".
      iSplitL "Hp1"; iExists ppn.
      + by iFrame "Hk Hp1".
      + by iFrame "Hk Hp2".
    - iIntros "[H1 H2]".
      iDestruct "H1" as (ppn1) "(#Hk1 & %Hc & %Hd & Hp1)".
      iDestruct "H2" as (ppn2) "(#Hk2 & _ & _ & Hp2)".
      iDestruct (kmap_at_agree with "Hk1 Hk2") as %[-> _].
      iDestruct (pointsto_combine with "Hp1 Hp2") as "[Hp _]".
      rewrite dfrac_op_own. iExists ppn2. by iFrame "Hk1 Hp".
  Qed.

  (* ---- the same two facts over a WINDOW of bytes, which is the form the
     [↦₂]/[↦₄]/[↦₈] bundles are built from.  Stated over an arbitrary start
     index [k] so the induction goes through. ---- *)

  Lemma mem_bytes_agree {m : N} (a : Arch.pa) (k n : nat) (dq1 dq2 : dfrac) (w1 w2 : bv m) :
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{dq1} nth_byte w1 j) -∗
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{dq2} nth_byte w2 j) -∗
    ⌜forall j, (k <= j < k + n)%nat -> nth_byte w1 j = nth_byte w2 j⌝.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. lia.
    - iIntros "[Hh1 Ht1] [Hh2 Ht2]".
      iDestruct (mem_pointsto_agree with "Hh1 Hh2") as %Heq.
      iDestruct (IH (S k) with "Ht1 Ht2") as %Hrest.
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hne]; [exact Heq|].
      apply Hrest. lia.
  Qed.

  (* an address held SEPARATELY from a byte buffer lies OUTSIDE that buffer.
     The two-buffer disjointness a copy loop needs ([memmove]'s src vs dst)
     follows by peeling one byte off the second buffer and applying this. *)
  Lemma mem_bytes_notin (a c : Arch.pa) (k n : nat) (dq : dfrac) (f : nat -> bv 8) (v : bv 8) :
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ f j) -∗
    c ↦ₘ{dq} v -∗
    ⌜forall j, (k <= j < k + n)%nat -> pa_add a j <> c⌝.
  Proof.
    revert k. induction n as [|n IH]; intros k; simpl.
    - iIntros "_ _". iPureIntro. intros j Hj. lia.
    - iIntros "[Hh Ht] Hc".
      iDestruct (mem_pointsto_ne with "Hh Hc") as %Hne0.
      iDestruct (IH (S k) with "Ht Hc") as %Hrest.
      iPureIntro. intros j Hj.
      destruct (decide (j = k)) as [->|Hjk]; [exact Hne0|].
      apply Hrest. lia.
  Qed.

  Lemma mem_bytes_frac_split {m : N} (a : Arch.pa) (k n : nat) (q1 q2 : Qp) (w : bv m) :
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{DfracOwn (q1 + q2)} nth_byte w j) ⊣⊢
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{DfracOwn q1} nth_byte w j) ∗
    ([∗ list] j ∈ seq k n, (pa_add a j) ↦ₘ{DfracOwn q2} nth_byte w j).
  Proof.
    rewrite -big_sepL_sep. apply big_sepL_proper. intros ? j _.
    apply mem_pointsto_frac_split.
  Qed.

End mem_pointsto_share.

(* CODE points-to, VA-BASED (uniform-claims): the KP_rx analogue -- the
   claim + ownership of the mapped physical byte; identity for the static
   kernel-text fragments, non-identity for the TRAMPOLINE va once its
   fragment is minted at the boot switch.  [↦ₓ□] is the form the immutable
   kernel image lives at ([kernel_text]/[instr_bytes]). *)
Definition text_pointsto `{!riscvGS Σ} (va : Arch.pa) (dq : dfrac) (v : bv 8) : iProp Σ :=
  (∃ ppn : mword 44,
     kmap_at (svpn_of va) ppn KP_rx ∗
     ⌜(uint va < 274877906944)%Z⌝ ∗          (* 2^38: canonical, positive half *)
     ⌜addr_is_text (pa_of ppn va)⌝ ∗
     pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn va) dq v)%I.
Notation "a ↦ₓ{ dq } v" := (text_pointsto a dq v)
  (at level 20, format "a  ↦ₓ{ dq }  v") : bi_scope.
(* discarded (persistent, duplicable) read-only code ownership. *)
Notation "a ↦ₓ□ v" := (text_pointsto a DfracDiscarded v)
  (at level 20, format "a  ↦ₓ□  v") : bi_scope.
(* full ownership (pre-persist, e.g. at adequacy init). *)
Notation "a ↦ₓ v" := (text_pointsto a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₓ  v") : bi_scope.

(* ---------------------------------------------------------------------- *)
(* PHYSICAL points-to (uniform-claims PHYSICAL TIER): ownership of the byte
   at the PHYSICAL address [pa], with no kernel-mapping claim -- the form for
   memory that is accessed UNTRANSLATED (the kernel page-table's own slots,
   read physically by the hardware walker; M-mode data/fetch, which has no
   translation).  This is the OLD pa-era [mem_pointsto] body verbatim.  The
   VA-based [↦ₘ]/[↦ₓ] above are for TRANSLATED kernel-variable/instruction
   access; a static (identity) va bridges the two tiers via the [pa_of_id]
   assembly/disassembly lemmas (KptPt/KMap). *)
Definition phys_pointsto `{!riscvGS Σ} (pa : Arch.pa) (dq : dfrac) (b : bv 8) : iProp Σ :=
  (pointsto (L:=Arch.pa) (V:=bv 8) pa dq b ∗ ⌜addr_is_ram pa⌝)%I.
Notation "a ↦ₚ{ dq } b" := (phys_pointsto a dq b)
  (at level 20, format "a  ↦ₚ{ dq }  b") : bi_scope.
Notation "a ↦ₚ□ b" := (phys_pointsto a DfracDiscarded b)
  (at level 20, format "a  ↦ₚ□  b") : bi_scope.
Notation "a ↦ₚ b" := (phys_pointsto a (DfracOwn 1) b)
  (at level 20, format "a  ↦ₚ  b") : bi_scope.

(* ---------------------------------------------------------------------- *)
(* word points-to: an 8-byte (doubleword) value [w] stored little-endian at a
   DOUBLEWORD-ALIGNED address [a].  Bundling the 8 byte points-to facts with
   the alignment lets an 8-byte load/store WP take a single [a ↦₈ w] hypothesis
   instead of a byte window PLUS a separate [is_aligned_paddr ... 8 = true]
   side condition -- the alignment travels with the ownership.  Both the paddr
   and (definitionally identical) vaddr alignment forms are recoverable.       *)
Definition word_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
   [∗ list] j ∈ seq 0 8, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₈{ dq } w" := (word_pointsto a dq w)
  (at level 20, format "a  ↦₈{ dq }  w") : bi_scope.
Notation "a ↦₈ w" := (word_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₈  w") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership of the doubleword. *)
Notation "a ↦₈□ w" := (word_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦₈□  w") : bi_scope.

Section word_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word_pointsto_aligned_p a dq w :
    word_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word_pointsto_bytes a dq w :
    word_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  (* repackage a byte window + its alignment fact into a word points-to *)
  Lemma word_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word_pointsto_unfold a dq w :
    word_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.

  (* ---- sharing (see [mem_pointsto_share]) ---- *)
  Lemma word_pointsto_agree a dq1 w1 dq2 w2 :
    a ↦₈{dq1} w1 -∗ a ↦₈{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (mem_bytes_agree with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=8)). intros j Hj. apply Hb. lia.
  Qed.
  Lemma word_pointsto_frac_split a q1 q2 w :
    a ↦₈{DfracOwn (q1 + q2)} w ⊣⊢ a ↦₈{DfracOwn q1} w ∗ a ↦₈{DfracOwn q2} w.
  Proof.
    rewrite /word_pointsto mem_bytes_frac_split.
    iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
  Qed.
End word_pointsto.

(* ---------------------------------------------------------------------- *)
(* PHYSICAL 8-byte word points-to [↦ₚ₈]: the [↦₈] body over the PHYSICAL
   [↦ₚ] tier -- an 8-byte doubleword owned at physical addresses, for the
   page-table slots and M-mode.  Kept SEPARATE from the VA-based [↦₈]. *)
Definition phys_word_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 64) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
   [∗ list] j ∈ seq 0 8, phys_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦ₚ₈{ dq } w" := (phys_word_pointsto a dq w)
  (at level 20, format "a  ↦ₚ₈{ dq }  w") : bi_scope.
Notation "a ↦ₚ₈ w" := (phys_word_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦ₚ₈  w") : bi_scope.
Notation "a ↦ₚ₈□ w" := (phys_word_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦ₚ₈□  w") : bi_scope.

Section phys_word_pointsto.
  Context `{!riscvGS Σ}.

  Lemma phys_word_pointsto_aligned_p a dq w :
    phys_word_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma phys_word_pointsto_bytes a dq w :
    phys_word_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₚ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  Lemma phys_word_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₚ{dq} nth_byte w j) ⊢ phys_word_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma phys_word_pointsto_unfold a dq w :
    phys_word_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗
    ([∗ list] j ∈ seq 0 8, (pa_add a j) ↦ₚ{dq} nth_byte w j).
  Proof. reflexivity. Qed.
End phys_word_pointsto.

(* ---------------------------------------------------------------------- *)
(* 2-byte halfword points-to: a 2-byte value [w] stored little-endian at a
   HALFWORD-ALIGNED address [a].  The exact 2-byte analogue of [word4_pointsto]
   ([↦₄]) -- what an [lh]/[sh] to a C [short] field takes (e.g. [struct
   file]'s [major]).                                                          *)
Definition word2_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 16) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 2 = true⌝ ∗
   [∗ list] j ∈ seq 0 2, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₂{ dq } w" := (word2_pointsto a dq w)
  (at level 20, format "a  ↦₂{ dq }  w") : bi_scope.
Notation "a ↦₂ w" := (word2_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₂  w") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership of the halfword. *)
Notation "a ↦₂□ w" := (word2_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦₂□  w") : bi_scope.

Section word2_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word2_pointsto_aligned_p a dq w :
    word2_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 2 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word2_pointsto_bytes a dq w :
    word2_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 2, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  Lemma word2_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] j ∈ seq 0 2, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word2_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word2_pointsto_unfold a dq w :
    word2_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 2 = true⌝ ∗
    ([∗ list] j ∈ seq 0 2, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.

  (* ---- sharing (see [mem_pointsto_share]) ---- *)
  Lemma word2_pointsto_agree a dq1 w1 dq2 w2 :
    a ↦₂{dq1} w1 -∗ a ↦₂{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (mem_bytes_agree with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=2)). intros j Hj. apply Hb. lia.
  Qed.
  Lemma word2_pointsto_frac_split a q1 q2 w :
    a ↦₂{DfracOwn (q1 + q2)} w ⊣⊢ a ↦₂{DfracOwn q1} w ∗ a ↦₂{DfracOwn q2} w.
  Proof.
    rewrite /word2_pointsto mem_bytes_frac_split.
    iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
  Qed.
End word2_pointsto.

(* ---------------------------------------------------------------------- *)
(* 4-byte word points-to: a 4-byte (word) value [w] stored little-endian at a
   WORD-ALIGNED address [a].  The exact 4-byte analogue of [word_pointsto]
   ([↦₈]): bundling the 4 byte points-to facts with the 4-byte alignment lets
   a 4-byte load/store WP take a single [a ↦₄ w] hypothesis instead of a byte
   window PLUS a separate [is_aligned_paddr ... 4 = true] side condition.      *)
Definition word4_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 32) : iProp Σ :=
  (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
   [∗ list] j ∈ seq 0 4, mem_pointsto (pa_add a j) dq (nth_byte w j))%I.
Notation "a ↦₄{ dq } w" := (word4_pointsto a dq w)
  (at level 20, format "a  ↦₄{ dq }  w") : bi_scope.
Notation "a ↦₄ w" := (word4_pointsto a (DfracOwn 1) w)
  (at level 20, format "a  ↦₄  w") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership of the word. *)
Notation "a ↦₄□ w" := (word4_pointsto a DfracDiscarded w)
  (at level 20, format "a  ↦₄□  w") : bi_scope.

(* TIMELESS, for the same reason as [mem_pointsto_timeless] above: this is what
   lets an invariant over a 4-byte cell ([StartedInv.started_body], the panic
   flags) hand the cell out from under the [▷]. *)
Global Instance word4_pointsto_timeless `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac) (w : bv 32) :
  Timeless (word4_pointsto a dq w).
Proof. rewrite /word4_pointsto. apply _. Qed.

Section word4_pointsto.
  Context `{!riscvGS Σ}.

  Lemma word4_pointsto_aligned_p a dq w :
    word4_pointsto a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true⌝.
  Proof. iIntros "[$ _]". Qed.
  Lemma word4_pointsto_bytes a dq w :
    word4_pointsto a dq w ⊢ [∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j.
  Proof. iIntros "[_ $]". Qed.
  (* repackage a byte window + its alignment fact into a word points-to *)
  Lemma word4_pointsto_intro a dq w :
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j) ⊢ word4_pointsto a dq w.
  Proof. iIntros (Hal) "H". by iFrame. Qed.
  Lemma word4_pointsto_unfold a dq w :
    word4_pointsto a dq w ⊣⊢
    ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗
    ([∗ list] j ∈ seq 0 4, (pa_add a j) ↦ₘ{dq} nth_byte w j).
  Proof. reflexivity. Qed.

  (* ---- sharing (see [mem_pointsto_share]) ---- *)
  Lemma word4_pointsto_agree a dq1 w1 dq2 w2 :
    a ↦₄{dq1} w1 -∗ a ↦₄{dq2} w2 -∗ ⌜w1 = w2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iDestruct (mem_bytes_agree with "H1 H2") as %Hb.
    iPureIntro. apply (bv_eq_of_bytes (n:=4)). intros j Hj. apply Hb. lia.
  Qed.
  Lemma word4_pointsto_frac_split a q1 q2 w :
    a ↦₄{DfracOwn (q1 + q2)} w ⊣⊢ a ↦₄{DfracOwn q1} w ∗ a ↦₄{DfracOwn q2} w.
  Proof.
    rewrite /word4_pointsto mem_bytes_frac_split.
    iSplit; [iIntros "[#$ [$ $]]" | iIntros "[[#$ $] [_ $]]"].
  Qed.

  (* THE 1/2 + 1/2 SPLIT, which is the fraction a shared 4-byte cell is
     actually held at all over the kernel: [p->pid]'s permanent half in the
     scheduler invariant against allocproc's (ProcInv.v), and the bio layer's
     [b->dev] / [b->blockno], whose bcache half and escrow half are joined for
     every write and re-split after it.  Stated with the fractions PINNED --
     [rewrite -(Qp.div_2 1)] would also match the [1] inside a [1/2] already in
     the goal and produce [(1/2 + 1/2)/2] -- and given in all three shapes,
     because the join direction is used as a wand and the split as a rewrite. *)
  Lemma word4_pointsto_half a w :
    a ↦₄ w ⊣⊢ a ↦₄{DfracOwn (1/2)} w ∗ a ↦₄{DfracOwn (1/2)} w.
  Proof. rewrite -word4_pointsto_frac_split Qp.div_2. reflexivity. Qed.

  Lemma word4_pointsto_half_split a w :
    a ↦₄ w -∗ a ↦₄{DfracOwn (1/2)} w ∗ a ↦₄{DfracOwn (1/2)} w.
  Proof. rewrite word4_pointsto_half. iIntros "$". Qed.

  Lemma word4_pointsto_half_join a w :
    a ↦₄{DfracOwn (1/2)} w -∗ a ↦₄{DfracOwn (1/2)} w -∗ a ↦₄ w.
  Proof. iIntros "H1 H2". rewrite word4_pointsto_half. iFrame "H1 H2". Qed.
End word4_pointsto.

(* ---------------------------------------------------------------------- *)
(* string points-to: a NUL-terminated C string [s] resident byte-by-byte at
   consecutive addresses starting at [a].  Built DIRECTLY on the single-byte
   memory points-to [↦ₘ] -- character [j] of [s] at [a+j], the terminating NUL
   at [a+|s|] -- with no alignment side condition, a C string being
   byte-addressed (this is what distinguishes it from [↦₈]/[↦₄]).

   The intended fraction is [DfracDiscarded]: the kernel's string literals are
   read-only image bytes that nothing ever writes, so [a ↦ₛ□ s] is PERSISTENT
   and hence freely DUPLICABLE -- it can be passed to a callee and kept, and it
   can sit inside a persistent predicate.  That is what lets a lock carry its
   own name ([lock_name], WpLock.v) at no ownership cost.                     *)
(* ---------------------------------------------------------------------- *)

(* the characters of [s] as bytes (no terminator) *)
Fixpoint string_bytes (s : string) : list (bv 8) :=
  match s with
  | String.EmptyString => []
  | String.String c s' => Z_to_bv 8 (Z.of_N (Ascii.N_of_ascii c)) :: string_bytes s'
  end.

(* the C representation of [s]: its characters followed by the NUL byte *)
Definition cstring_bytes (s : string) : list (bv 8) :=
  string_bytes s ++ [Z_to_bv 8 0].

Definition string_pointsto `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac)
    (s : string) : iProp Σ :=
  ([∗ list] j ↦ b ∈ cstring_bytes s, mem_pointsto (pa_add a j) dq b)%I.
Notation "a ↦ₛ{ dq } s" := (string_pointsto a dq s)
  (at level 20, format "a  ↦ₛ{ dq }  s") : bi_scope.
(* discarded (persistent, duplicable) read-only ownership -- the default for a
   kernel string literal. *)
Notation "a ↦ₛ□ s" := (string_pointsto a DfracDiscarded s)
  (at level 20, format "a  ↦ₛ□  s") : bi_scope.
Notation "a ↦ₛ s" := (string_pointsto a (DfracOwn 1) s)
  (at level 20, format "a  ↦ₛ  s") : bi_scope.

Section string_pointsto.
  Context `{!riscvGS Σ}.

  Global Instance string_pointsto_persistent a s : Persistent (a ↦ₛ□ s).
  Proof. rewrite /string_pointsto /mem_pointsto. apply _. Qed.

  Lemma string_pointsto_bytes a dq s :
    string_pointsto a dq s ⊣⊢
    [∗ list] j ↦ b ∈ cstring_bytes s, (pa_add a j) ↦ₘ{dq} b.
  Proof. reflexivity. Qed.

  (* the terminating NUL is the last byte owned *)
  Lemma cstring_bytes_length s :
    length (cstring_bytes s) = S (String.length s).
  Proof.
    rewrite /cstring_bytes length_app /=.
    induction s as [|c s IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.
End string_pointsto.

(* ---------------------------------------------------------------------- *)
(* 2. The bridge: an existential register map agreeing with [regstate].    *)
(* ---------------------------------------------------------------------- *)

Definition reg_agree (m : gmap register (sigT type_of_register))
    (rs : regstate) : Prop :=
  forall r dv, m !! r = Some dv -> dv = existT r (register_lookup r rs).

(* the register bridge for a GIVEN hart's ghost name [γ]. *)
Definition reg_interp_at `{!riscvGS Σ} (γ : gname) (rs : regstate) : iProp Σ :=
  (∃ m, ghost_map_auth γ 1 m ∗ ⌜reg_agree m rs⌝)%I.

(* the bridge for the AMBIENT hart -- what the WPs manipulate.  Original arity
   ([rs] only): the hart is [cpu_id], carried by [reg_name]. *)
Definition reg_interp `{!riscvGS Σ} `{CpuId} (rs : regstate) : iProp Σ :=
  reg_interp_at reg_name rs.

(* ---------------------------------------------------------------------- *)
(* device-fabric ownership: the halves pattern over two [ghost_var]s.       *)
(* [uart_auth]/[plic_auth] live inside [state_interp]; [uart_frag]/         *)
(* [plic_frag] are the user-facing halves.  Agreement + joint update are    *)
(* the two bridge lemmas, mirroring [reg_valid]/[reg_update].               *)
(* ---------------------------------------------------------------------- *)

Definition uart_auth `{!riscvGS Σ} (u : uart_state) : iProp Σ :=
  ghost_var uart_name (1/2) u.
Definition uart_frag `{!riscvGS Σ} (u : uart_state) : iProp Σ :=
  ghost_var uart_name (1/2) u.
Definition plic_auth `{!riscvGS Σ} (p : plic_state) : iProp Σ :=
  ghost_var plic_name (1/2) p.
Definition plic_frag `{!riscvGS Σ} (p : plic_state) : iProp Σ :=
  ghost_var plic_name (1/2) p.
Definition virtio_auth `{!riscvGS Σ} (v : virtio_state) : iProp Σ :=
  ghost_var virtio_name (1/2) v.
Definition virtio_frag `{!riscvGS Σ} (v : virtio_state) : iProp Σ :=
  ghost_var virtio_name (1/2) v.

(* the state_interp conjunct for the shared device state *)
Definition dev_interp `{!riscvGS Σ} (d : dev_state) : iProp Σ :=
  (uart_auth d.(duart) ∗ plic_auth d.(dplic) ∗ virtio_auth d.(dvirtio))%I.

Section DevBridge.
  Context `{!riscvGS Σ}.

  Lemma uart_agree u u' : uart_auth u -∗ uart_frag u' -∗ ⌜u' = u⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->.
  Qed.
  Lemma uart_update u u' u'' :
    uart_auth u -∗ uart_frag u' ==∗ uart_auth u'' ∗ uart_frag u''.
  Proof. iApply ghost_var_update_halves. Qed.

  Lemma plic_agree p p' : plic_auth p -∗ plic_frag p' -∗ ⌜p' = p⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->.
  Qed.
  Lemma plic_update p p' p'' :
    plic_auth p -∗ plic_frag p' ==∗ plic_auth p'' ∗ plic_frag p''.
  Proof. iApply ghost_var_update_halves. Qed.

  Lemma virtio_agree v v' : virtio_auth v -∗ virtio_frag v' -∗ ⌜v' = v⌝.
  Proof.
    iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %->.
  Qed.
  Lemma virtio_update v v' v'' :
    virtio_auth v -∗ virtio_frag v' ==∗ virtio_auth v'' ∗ virtio_frag v''.
  Proof. iApply ghost_var_update_halves. Qed.
End DevBridge.

(* one hart's view (its registers + the shared memory + the shared device
   fabric); the single-CPU [state_interp σ ns κs nt] of the leaf lemmas is
   replaced by [mstate_interp σ].  The device conjunct rides in LAST
   position: a leaf that only touches registers/memory frames it through
   untouched (an exec over set_reg/write_bytes preserves [mdev]
   definitionally). *)
Definition mstate_interp `{!riscvGS Σ} `{CpuId} (σ : mstate) : iProp Σ :=
  (reg_interp σ.(sregs) ∗ gen_heap_interp σ.(mem) ∗ dev_interp σ.(mdev))%I.

(* the GLOBAL register bridge: one authoritative map per hart, over the whole
   finite [CPU] set.  [gregs] is a total function, so there is no membership
   side condition -- [gregs_interp_acc] focuses any [cpu_id] unconditionally. *)
Definition gregs_interp `{!riscvGS Σ} (gr : CPU -> regstate) : iProp Σ :=
  ([∗ set] cpu ∈ (fin_to_set CPU : gset CPU), reg_interp_at (cpu_reg_name cpu) (gr cpu))%I.

(* ---------------------------------------------------------------------- *)
(* 3. irisGS instance: state_interp = (per-hart register bridges) * memory. *)
(* ---------------------------------------------------------------------- *)

Global Program Instance riscv_irisGS `{!riscvGS Σ} : irisGS riscv_lang Σ := {
  iris_invGS := riscv_invGS;
  state_interp g _ _ _ :=
    (gregs_interp g.(gregs) ∗ gen_heap_interp g.(gmem) ∗ dev_interp g.(gdev))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
}.
Next Obligation. intros. iIntros "H". by iModIntro. Qed.

(* Focus the ambient hart's register bridge out of the global one, with a
   frame-preserving update handle to put an updated bridge back.  This is the
   single point where per-hart framing happens; leaf WPs never see it. *)
Lemma gregs_interp_acc `{!riscvGS Σ} `{CpuId} (gr : CPU -> regstate) :
  gregs_interp gr ⊢ reg_interp (gr cpu_id) ∗
    (∀ rs', reg_interp rs' -∗ gregs_interp (<[cpu_id := rs']> gr)).
Proof.
  rewrite /gregs_interp /reg_interp /reg_name.
  iIntros "H".
  iDestruct (big_sepS_delete _ _ cpu_id with "H") as "[Hcur Hrest]";
    [ apply elem_of_fin_to_set |].
  iFrame "Hcur".
  iIntros (rs') "Hrs'".
  iApply (big_sepS_delete _ _ cpu_id); [ apply elem_of_fin_to_set |].
  rewrite /insert /greg_insert decide_True //.
  iFrame "Hrs'".
  iApply (big_sepS_mono with "Hrest").
  intros cpu Hcpu. apply elem_of_difference in Hcpu as [_ Hne].
  rewrite decide_False; [ done | ].
  intros ->. apply Hne, elem_of_singleton. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. Per-hart register ownership for an EXPLICIT (non-ambient) hart:      *)
(*     [reg_pointsto_at c r] is the [↦ᵣ]-analogue for hart [c], with its    *)
(*     bridge lemmas against [reg_interp_at] and the explicit-hart focusing  *)
(*     lemma [gregs_interp_acc_at].  Needed by any proof that touches        *)
(*     ANOTHER hart's registers -- e.g. the device thread's wire step        *)
(*     writes hart [c]'s [sig_seip] pin (WpUart.v), and the wire invariant   *)
(*     (WireInv.v) owns every hart's interrupt pins.                          *)
(* ---------------------------------------------------------------------- *)

Section RegAt.
  Context `{!riscvGS Σ}.

  (* [r ↦ᵣ v] for an EXPLICIT hart [c] (the ambient-[CpuId] [reg_pointsto]
     is [reg_pointsto_at cpu_id]). *)
  Definition reg_pointsto_at (c : CPU) (r : register) (dq : dfrac)
      (v : type_of_register r) : iProp Σ :=
    ghost_map_elem (cpu_reg_name c) r dq (existT r v).

  Global Instance reg_pointsto_at_timeless c r dq v :
    Timeless (reg_pointsto_at c r dq v).
  Proof. rewrite /reg_pointsto_at. apply _. Qed.

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

(* ---------------------------------------------------------------------- *)
(* 4. Bridge lemmas.                                                       *)
(* ---------------------------------------------------------------------- *)

Section Bridge.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* reading a register cell agrees with the model's [register_lookup]. *)
  Lemma reg_valid rs r v :
    reg_interp rs -∗ r ↦ᵣ v -∗ ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  (* writing a register cell tracks the model's [register_set]. *)
  Lemma reg_update rs r v v' :
    reg_interp rs -∗ r ↦ᵣ v ==∗
      reg_interp (register_set r v' rs) ∗ r ↦ᵣ v'.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
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

  (* reading a register cell at ANY fraction -- in particular a persistent
     [r ↦ᵣ□ v].  ([reg_valid] is the [DfracOwn 1] special case.) *)
  Lemma reg_valid_dq rs r dq v :
    reg_interp rs -∗ reg_pointsto r dq v -∗ ⌜register_lookup r rs = v⌝.
  Proof.
    rewrite /reg_pointsto /reg_interp /reg_interp_at.
    iIntros "Hi Hr". iDestruct "Hi" as (m) "[Hm %Hag]".
    iDestruct (ghost_map_lookup with "Hm Hr") as %Hlk.
    iPureIntro. symmetry. by apply reg_existT_inj, (Hag r _ Hlk).
  Qed.

  (* a discarded (read-only) register cell is persistent -- hence duplicable and
     never consumed, so a WP that only READS it need neither take a fresh copy nor
     hand one back. *)
  Global Instance reg_pointsto_discarded_persistent r v : Persistent (r ↦ᵣ□ v).
  Proof. rewrite /reg_pointsto. apply _. Qed.

  (* KEEP-UNREFERENCED: public bridge API (fraction-discard / duplication).  Kept
     for downstream use even though currently unreferenced -- do not delete. *)
  (* discard the fraction: turn an owned register cell into the persistent one. *)
  Lemma reg_pointsto_persist r dq v : reg_pointsto r dq v ==∗ r ↦ᵣ□ v.
  Proof. rewrite /reg_pointsto. iIntros "Hr". by iMod (ghost_map_elem_persist with "Hr"). Qed.

  (* ---- the VA-based ↦ₘ ACCESSOR (uniform-claims) ---- *)
  (* THE primitive the ↦ₘ suite rests on: expose the mapping claim, the
     canonicality/kdata facts, and OWNERSHIP of the mapped PHYSICAL byte
     [pa_of ppn a], with a re-fold wand.  A tower does its gen_heap op at
     [pa_of ppn a] (the pa its regime absorbs [a] to) and re-folds. *)
  Lemma mem_pointsto_acc a dq b :
    a ↦ₘ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗
      ⌜(uint a < 274877906944)%Z⌝ ∗
      ⌜addr_is_ram (pa_of ppn a)⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b -∗ a ↦ₘ{dq} b).
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & Hp)".
    iExists ppn. iFrame "Hk Hp".
    iSplit; [iPureIntro; exact Hc|]. iSplit; [iPureIntro; exact Hd|].
    iIntros "Hp". iExists ppn. by iFrame "Hk Hp".
  Qed.

  (* the canonicality conjunct (positive Sv39 half): pins [a ↔ (vpn,off)]. *)
  Lemma mem_canonical a dq b : a ↦ₘ{dq} b -∗ ⌜(uint a < 274877906944)%Z⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(_ & %Hc & _ & _)".
    iPureIntro; exact Hc.
  Qed.

  (* PA-SIDE region fact: the byte's PHYSICAL address is in RAM (the
     claim ppn identifies the page).  Identity consumers recover the va-side
     fact via [pa_of_id] (KptPt). *)
  Lemma mem_ram a dq b :
    a ↦ₘ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗ ⌜addr_is_ram (pa_of ppn a)⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & _)".
    iExists ppn. iFrame "Hk". iPureIntro; exact Hd.
  Qed.

  (* reading a memory byte agrees with the byte heap AT ITS PHYSICAL address. *)
  Lemma mem_valid (mm : gmap Arch.pa (bv 8)) a dq b :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₘ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rw ∗ ⌜addr_is_ram (pa_of ppn a)⌝ ∗
      ⌜mm !! (pa_of ppn a) = Some b⌝.
  Proof.
    rewrite /mem_pointsto. iIntros "Hm H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & Hp)".
    iDestruct (gen_heap_valid with "Hm Hp") as %Hlk.
    iExists ppn. iFrame "Hk". iPureIntro. split; [exact Hd | exact Hlk].
  Qed.

  (* a discarded (read-only) memory byte is persistent — hence FREELY duplicable.
     This is what makes [kernel_text] (built from [↦ₓ□] code bytes) duplicable. *)
  Global Instance mem_pointsto_discarded_persistent a b :
    Persistent (a ↦ₘ□ b).
  Proof. rewrite /mem_pointsto. apply _. Qed.

  (* discard the fraction: turn any memory byte into the persistent read-only one. *)
  Lemma mem_pointsto_persist a dq b : a ↦ₘ{dq} b ==∗ a ↦ₘ□ b.
  Proof.
    rewrite /mem_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & Hp)".
    iMod (pointsto_persist with "Hp") as "Hp". iModIntro. iExists ppn.
    iFrame "Hk Hp". iPureIntro. split; [exact Hc | exact Hd].
  Qed.

  (* KEEP-UNREFERENCED: public bridge API (kept though currently unreferenced).
     a persistent (discarded) byte can be handed out repeatedly. *)
  Lemma mem_pointsto_dup a b : a ↦ₘ□ b -∗ a ↦ₘ□ b ∗ a ↦ₘ□ b.
  Proof. iIntros "#H". by iSplitR. Qed.

  (* ---- the CODE points-to bridge (rwx-kmap; mirrors the ↦ₘ suite) ---- *)

  Lemma text_pointsto_acc a dq b :
    a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗
      ⌜(uint a < 274877906944)%Z⌝ ∗
      ⌜addr_is_text (pa_of ppn a)⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn a) dq b -∗ a ↦ₓ{dq} b).
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & Hp)".
    iExists ppn. iFrame "Hk Hp".
    iSplit; [iPureIntro; exact Hc|]. iSplit; [iPureIntro; exact Hd|].
    iIntros "Hp". iExists ppn. by iFrame "Hk Hp".
  Qed.

  Lemma text_canonical a dq b : a ↦ₓ{dq} b -∗ ⌜(uint a < 274877906944)%Z⌝.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(_ & %Hc & _ & _)".
    iPureIntro; exact Hc.
  Qed.

  (* PA-SIDE: the byte's PHYSICAL address is kernel TEXT ... *)
  Lemma code_text a dq b :
    a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗ ⌜addr_is_text (pa_of ppn a)⌝.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & _)".
    iExists ppn. iFrame "Hk". iPureIntro; exact Hd.
  Qed.

  (* ... and hence real RAM (what the M-mode no-perm-check fetch path and
     the PMP/MMIO geometry facts consume, at the physical address). *)
  Lemma code_ram a dq b :
    a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗ ⌜addr_is_ram (pa_of ppn a)⌝.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & _)".
    iExists ppn. iFrame "Hk". iPureIntro; exact (addr_is_text_ram _ Hd).
  Qed.

  Lemma text_valid (mm : gmap Arch.pa (bv 8)) a dq b :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₓ{dq} b -∗ ∃ ppn : mword 44,
      kmap_at (svpn_of a) ppn KP_rx ∗ ⌜addr_is_text (pa_of ppn a)⌝ ∗
      ⌜mm !! (pa_of ppn a) = Some b⌝.
  Proof.
    rewrite /text_pointsto. iIntros "Hm H". iDestruct "H" as (ppn) "(#Hk & _ & %Hd & Hp)".
    iDestruct (gen_heap_valid with "Hm Hp") as %Hlk.
    iExists ppn. iFrame "Hk". iPureIntro. split; [exact Hd | exact Hlk].
  Qed.

  Global Instance text_pointsto_discarded_persistent a b :
    Persistent (a ↦ₓ□ b).
  Proof. rewrite /text_pointsto. apply _. Qed.

  (* discard the fraction: turn any code byte into the persistent read-only
     one (adequacy init persists the whole sub-etext image this way). *)
  Lemma text_pointsto_persist a dq b : a ↦ₓ{dq} b ==∗ a ↦ₓ□ b.
  Proof.
    rewrite /text_pointsto. iIntros "H". iDestruct "H" as (ppn) "(#Hk & %Hc & %Hd & Hp)".
    iMod (pointsto_persist with "Hp") as "Hp". iModIntro. iExists ppn.
    iFrame "Hk Hp". iPureIntro. split; [exact Hc | exact Hd].
  Qed.

  (* ---- the PHYSICAL points-to bridge (the OLD pa-era [mem_*] bodies) ---- *)

  Lemma phys_valid (mm : gmap Arch.pa (bv 8)) a dq b :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₚ{dq} b -∗ ⌜mm !! a = Some b⌝.
  Proof.
    iIntros "Hm [Ha _]". by iDestruct (gen_heap_valid with "Hm Ha") as %?.
  Qed.

  Lemma phys_ram a dq b : a ↦ₚ{dq} b -∗ ⌜addr_is_ram a⌝.
  Proof. by iIntros "[_ %H]". Qed.

  (* the PHYSICAL word cell (a PT slot post-flip) sits in RAM -- trivial from
     [phys_ram] at byte 0.  Beside [phys_word_pointsto]'s suite; consumed by the
     walk's "slot address is nonzero because it is RAM" argument. *)
  Lemma phys_word_pointsto_ram a dq w : a ↦ₚ₈{dq} w ⊢ ⌜addr_is_ram a⌝.
  Proof.
    iIntros "Hw". iDestruct (phys_word_pointsto_bytes with "Hw") as "Hbs".
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "Hb0".
    { rewrite lookup_seq_lt; [reflexivity | lia]. }
    iDestruct (phys_ram with "Hb0") as %Hram0.
    (* [pa_add a 0 = a] (RiscvExtras' [pa_add_0]/[avi0] cannot be imported here
       -- it depends on RiscvPtsto -- so its proof is inlined). *)
    assert (Hpa0 : pa_add a 0 = a).
    { unfold pa_add. change (Z.of_nat 0) with 0%Z.
      unfold add_vec_int, add_vec, Operators_mwords.word_binop,
             Operators_mwords.with_word', SailStdpp.Values.with_word,
             SailStdpp.Values.mword_of_int,
             MachineWord.MachineWord.add, MachineWord.MachineWord.Z_to_word.
      apply bv_eq. rewrite bv_add_unsigned Z_to_bv_unsigned.
      rewrite bv_wrap_0 Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
    rewrite Hpa0 in Hram0. iPureIntro. exact Hram0.
  Qed.

  Global Instance phys_pointsto_discarded_persistent a b : Persistent (a ↦ₚ□ b).
  Proof. rewrite /phys_pointsto. apply _. Qed.

  Lemma phys_pointsto_persist a dq b : a ↦ₚ{dq} b ==∗ a ↦ₚ□ b.
  Proof.
    iIntros "[Ha %Hr]". iMod (pointsto_persist with "Ha") as "Ha".
    iModIntro. by iFrame.
  Qed.

  Lemma phys_pointsto_dup a b : a ↦ₚ□ b -∗ a ↦ₚ□ b ∗ a ↦ₚ□ b.
  Proof. iIntros "#H". by iSplitR. Qed.

  Lemma phys_update (mm : _) (a : Arch.pa) (b b' : bv 8) :
    gen_heap_interp (hG:=riscv_memGS) mm -∗ a ↦ₚ{DfracOwn 1} b ==∗
      gen_heap_interp (hG:=riscv_memGS) (<[a := b']> mm) ∗ a ↦ₚ{DfracOwn 1} b'.
  Proof.
    iIntros "Hm [Ha %Hr]". iMod (gen_heap_update with "Hm Ha") as "[Hm Ha]".
    iModIntro. iFrame "Hm Ha". iPureIntro. exact Hr.
  Qed.

  (* ---- the agreement CORE of the tier bridge (uniform-claims PHYSICAL
     TIER): given a claim for [pa]'s vpn, the VA-based [↦ₘ]'s existential ppn
     is PINNED to that claim's ppn -- so its byte sits at [pa_of ppn0 pa].
     The [pa_of ppn0 pa = pa] step (identity, via [pa_of_id] with ppn0 =
     [kpt_leaf_ppn]) is done by the KptPt/KMap assembly lemmas built on
     this.  Only [kmap_at_agree] is needed here, so it stays in RiscvPtsto. *)
  Lemma mem_pointsto_pin (pa : mword 64) dq b (ppn0 : mword 44) :
    kmap_at (svpn_of pa) ppn0 KP_rw -∗ pa ↦ₘ{dq} b -∗
      ⌜(uint pa < 274877906944)%Z⌝ ∗ ⌜addr_is_ram (pa_of ppn0 pa)⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b -∗ pa ↦ₘ{dq} b).
  Proof.
    iIntros "#Hk0 H".
    iDestruct (mem_pointsto_acc with "H") as (ppn) "(#Hk & %Hc & %Hd & Hp & Hcl)".
    iDestruct (kmap_at_agree with "Hk0 Hk") as %[<- _].
    iFrame "Hp Hcl". iPureIntro. split; [exact Hc | exact Hd].
  Qed.

  (* GENERAL (non-identity) VA-tier introduction: a physical byte sitting at
     [pa_of ppn va] -- the pa the claim [kmap_at (svpn_of va) ppn KP_rw] takes
     [va] to -- IS the [↦ₘ] byte at [va].  This is the primary form of the
     [↦ₚ -> ↦ₘ] direction: [va] and its physical page [ppn] are ARBITRARY (the
     claim need not be an identity leaf), so it constructs a genuinely
     non-identity [↦ₘ] -- e.g. a kstack byte owned at its virtual address but
     physically living at a kalloc-chosen page.  The caller supplies only the
     RAM/canonicality facts about the physical target; the claim carries the
     translation. *)
  Lemma phys_to_mem_map (va : mword 64) (ppn : mword 44) dq b :
    addr_is_ram (pa_of ppn va) -> (uint va < 274877906944)%Z ->
    kmap_at (svpn_of va) ppn KP_rw -∗ (pa_of ppn va) ↦ₚ{dq} b -∗ va ↦ₘ{dq} b.
  Proof.
    intros Hram Hcan. iIntros "#Hk [Hp _]".
    rewrite /mem_pointsto. iExists ppn. iFrame "Hk Hp".
    iPureIntro. split; [exact Hcan | exact Hram].
  Qed.

  (* Claim-keyed byte conversions ↦ₚ ⇄ ↦ₘ for an IDENTITY-mapped kdata va
     ([pa_of ppn pa = pa]): the [kmap_at] supplies the mapping, the caller the
     pure kdata/canonical facts.  These are what let a physical PT-slot cell
     ([↦ₚ₈], owned by [ptree_own]) become a VA-tier [↦₈] for a software walk's
     S-mode load, carrying NOTHING but the node's own claim
     ([pt_node_claim] = this [kmap_at] + [node_kdata]).  [phys_to_mem_claim] is
     now a RESTATEMENT of the general [phys_to_mem_map] above (the identity
     premise [pa_of ppn pa = pa] specializes [pa_of ppn pa] to [pa]). *)
  Lemma phys_to_mem_claim (pa : mword 64) (ppn : mword 44) dq b :
    pa_of ppn pa = pa -> addr_is_ram pa -> (uint pa < 274877906944)%Z ->
    kmap_at (svpn_of pa) ppn KP_rw -∗ pa ↦ₚ{dq} b -∗ pa ↦ₘ{dq} b.
  Proof.
    intros Hid Hkd Hcan. iIntros "#Hk Hp".
    iApply (phys_to_mem_map pa ppn dq b with "Hk [Hp]").
    { rewrite Hid. exact Hkd. }
    { exact Hcan. }
    { rewrite Hid. iExact "Hp". }
  Qed.

  Lemma mem_to_phys_claim (pa : mword 64) (ppn : mword 44) dq b :
    pa_of ppn pa = pa ->
    kmap_at (svpn_of pa) ppn KP_rw -∗ pa ↦ₘ{dq} b -∗ pa ↦ₚ{dq} b.
  Proof.
    intros Hid. iIntros "#Hk H".
    iDestruct (mem_pointsto_pin pa dq b ppn with "Hk H") as "(%Hc & %Hd & Hp & _)".
    rewrite Hid in Hd. iEval (rewrite Hid) in "Hp".
    rewrite /phys_pointsto. iFrame "Hp". iPureIntro. exact Hd.
  Qed.

  Lemma text_pointsto_pin (pa : mword 64) dq b (ppn0 : mword 44) :
    kmap_at (svpn_of pa) ppn0 KP_rx -∗ pa ↦ₓ{dq} b -∗
      ⌜(uint pa < 274877906944)%Z⌝ ∗ ⌜addr_is_text (pa_of ppn0 pa)⌝ ∗
      pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b ∗
      (pointsto (L:=Arch.pa) (V:=bv 8) (pa_of ppn0 pa) dq b -∗ pa ↦ₓ{dq} b).
  Proof.
    iIntros "#Hk0 H".
    iDestruct (text_pointsto_acc with "H") as (ppn) "(#Hk & %Hc & %Hd & Hp & Hcl)".
    iDestruct (kmap_at_agree with "Hk0 Hk") as %[<- _].
    iFrame "Hp Hcl". iPureIntro. split; [exact Hc | exact Hd].
  Qed.

End Bridge.

(* ---------------------------------------------------------------------- *)
(* Persisting a MULTI-byte cell: [mem_pointsto_persist] lifted over the byte
   windows of [↦₈] / [↦₄] / [↦ₛ].  Discarding the fraction turns a cell
   read-only forever and hence duplicable -- how a freshly-initialised
   immutable structure (a lock's name field, a string) becomes a persistent
   resource that no longer has to be threaded through every WP.              *)
(* ---------------------------------------------------------------------- *)
Section pointsto_persist.
  Context `{!riscvGS Σ}.

  Global Instance word_pointsto_discarded_persistent a w : Persistent (a ↦₈□ w).
  Proof. rewrite /word_pointsto. apply _. Qed.
  Global Instance word4_pointsto_discarded_persistent a w : Persistent (a ↦₄□ w).
  Proof. rewrite /word4_pointsto. apply _. Qed.

  Lemma word_pointsto_persist a dq w : a ↦₈{dq} w ==∗ a ↦₈□ w.
  Proof.
    iIntros "[%Hal Hbs]".
    iAssert (|==> [∗ list] j ∈ seq 0 8,
               (pa_add a j) ↦ₘ□ nth_byte w j)%I with "[Hbs]" as ">Hbs".
    { iApply big_sepL_bupd. iApply (big_sepL_mono with "Hbs").
      iIntros (k j _) "H". by iApply mem_pointsto_persist. }
    iModIntro. by iFrame.
  Qed.

  Lemma word4_pointsto_persist a dq w : a ↦₄{dq} w ==∗ a ↦₄□ w.
  Proof.
    iIntros "[%Hal Hbs]".
    iAssert (|==> [∗ list] j ∈ seq 0 4,
               (pa_add a j) ↦ₘ□ nth_byte w j)%I with "[Hbs]" as ">Hbs".
    { iApply big_sepL_bupd. iApply (big_sepL_mono with "Hbs").
      iIntros (k j _) "H". by iApply mem_pointsto_persist. }
    iModIntro. by iFrame.
  Qed.

  Lemma string_pointsto_persist a dq s : a ↦ₛ{dq} s ==∗ a ↦ₛ□ s.
  Proof.
    iIntros "Hs". iApply big_sepL_bupd. iApply (big_sepL_mono with "Hs").
    iIntros (k b _) "H". by iApply mem_pointsto_persist.
  Qed.

  Global Instance phys_word_pointsto_discarded_persistent a w : Persistent (a ↦ₚ₈□ w).
  Proof. rewrite /phys_word_pointsto. apply _. Qed.

  Lemma phys_word_pointsto_persist a dq w : a ↦ₚ₈{dq} w ==∗ a ↦ₚ₈□ w.
  Proof.
    iIntros "[%Hal Hbs]".
    iAssert (|==> [∗ list] j ∈ seq 0 8,
               (pa_add a j) ↦ₚ□ nth_byte w j)%I with "[Hbs]" as ">Hbs".
    { iApply big_sepL_bupd. iApply (big_sepL_mono with "Hbs").
      iIntros (k j _) "H". by iApply phys_pointsto_persist. }
    iModIntro. by iFrame.
  Qed.
End pointsto_persist.

(* Seal [mem_pointsto] for typeclass (Frame) resolution: without this, [iFrame]
   over a large memory region unfolds every [a ↦ₘ v] into its [pointsto ∗ ⌜..⌝]
   conjunction and recursively re-searches the [Frame] instance per byte.  Making
   it typeclass-opaque keeps each [a ↦ₘ v] an atomic frameable unit (~37% off the
   big region [iFrame]s).  Placed AFTER [End Bridge] so the bridge lemmas above,
   which destruct the raw conjunction, still typecheck.  [Typeclasses Opaque]
   (not [Opaque]) leaves [rewrite /mem_pointsto] / [unfold] working. *)
Typeclasses Opaque mem_pointsto.
Typeclasses Opaque text_pointsto.
Typeclasses Opaque phys_pointsto.

(* ... and re-supply the TIMELESS instances the seals hide.  A page-table
   node's ownership must be timeless for the SHARED kernel table to live in
   an Iris [inv] (KptShare.v): opening the invariant yields the body under a
   [▷], and the Svadu A/D write-back needs the slot NOW. *)
Global Instance text_pointsto_timeless `{!riscvGS Σ} a dq b :
  Timeless (text_pointsto a dq b).
Proof. rewrite /text_pointsto. apply _. Qed.
Global Instance phys_pointsto_timeless `{!riscvGS Σ} a dq b :
  Timeless (phys_pointsto a dq b).
Proof. rewrite /phys_pointsto. apply _. Qed.
Global Instance phys_word_pointsto_timeless `{!riscvGS Σ} a dq w :
  Timeless (phys_word_pointsto a dq w).
Proof. rewrite /phys_word_pointsto. apply _. Qed.

