(* ====================================================================== *)
(* DiskInv.v -- struct disk's geometry and [disk_res], the resource the    *)
(* vdisk_lock protects.                                                    *)
(*                                                                         *)
(* Layout of the static [struct disk] at KernelSyms.disk (virtio_disk.c):  *)
(*   +0x000 desc   (page ptr)   +0x008 avail (page ptr)  +0x010 used (ptr) *)
(*   +0x018 free[8]  (1 byte each)                                         *)
(*   +0x020 used_idx (2 bytes)                                             *)
(*   +0x028 info[8]: { b : buf* @ +0x28+16i ; status : char @ +0x30+16i }  *)
(*   +0x0a8 ops[8]:  { type @ +0 ; reserved @ +4 ; sector @ +8 } (16 B)    *)
(*   +0x128 vdisk_lock                                                     *)
(*                                                                         *)
(* Ownership discipline (design/virtio-driver.md):                         *)
(*  - the three page-pointer cells are written once by init and then       *)
(*    immutable: they live OUTSIDE disk_res as the persistent [disk_geom]; *)
(*  - a FREE descriptor slot i owns its descriptor-table entry, its ops    *)
(*    header, its status byte and its info.b cell ([free_slot_res]);       *)
(*    allocation (free[i] <- 0) hands the bundle to the caller;            *)
(*  - an IN-FLIGHT position p keeps in disk_res exactly what the           *)
(*    interrupt handler touches: the receipt, the b->disk word (value 1)   *)
(*    and the info[head].b cell ([flight_res]); everything else about the  *)
(*    request is either in the DMA lease (the pin, the status byte, a      *)
(*    read request's buffer) or stays framed in the sleeping rw;           *)
(*  - a PROCESSED position p ([parked_res]) holds the withdrawn payoff     *)
(*    until its publisher collects it: b->disk back at 0, the pin bytes,   *)
(*    the status byte at 0, the buffer contents, the disk fragments;       *)
(*  - [dn_claim] (auth here, fragment with the publisher) is what lets a   *)
(*    sleeping rw RE-FIND its position: dom claims = dom flight ∪ parked;  *)
(*  - the avail-ring entry cells for mod-8 slots not used by any live      *)
(*    position are here ([ring_slots_res]); an occupied one's bytes are    *)
(*    in its position's pin (leased, or inside a parked payoff).           *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var mono_nat invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import VirtioModel.
Require Import VirtioQueue.
Require Import DiskPtsto.
Require Import VirtioProto.
Require Import Xv6Cameras.
Require Import KptPt.
Require Import KMap.
Require Export BufOwn.
Require Export DiskAddrs.   (* [struct disk]'s field addresses, moved below VirtioProto *)
From Kernel Require KernelSyms.
Require Import RiscvExtras.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.
Require Import TsoCtx.
Require Import CtxMorphTac.   (* [ctx_morph_solve] -- the λ payload's transport driver *)
Require Import WpLock.     (* [lk_floor]: the payload floors (A6.126 §6.6) *)
Require Import DiskAvail.  (* the ledger window bridges + the boot carves *)

(* ---------------------------------------------------------------------- *)
(* geometry                                                                *)
(* ---------------------------------------------------------------------- *)

(* The [struct disk] field addresses moved to DiskAddrs.v, below
   VirtioProto.v: the per-descriptor receipt lives in the device invariant
   and has to name [disk.info[i].b] (finding 5).  Re-exported above, so
   every spelling here and downstream is unchanged. *)

(* struct buf fields (b_disk / b_blockno / b_data / ...) come from BufOwn.v,
   re-exported above -- the common home shared with the bio.c layer. *)

(* ---------------------------------------------------------------------- *)
(* ALIGNMENT of an offset inside a queue page.                             *)
(*                                                                         *)
(* Every word-granular cell the driver owns on the three queue pages is    *)
(* named by an offset from a 4096-aligned base, so its [is_aligned_paddr]  *)
(* is one divisibility argument -- and one that has to be redone at each of *)
(* the descriptor entry's four fields, at the avail-ring entry and at the  *)
(* used-ring element.  THE lemma is [pa_add_aligned_in_page]; the named    *)
(* instances below are the ones [desc_entry_own] / [ring_slots_res] need,  *)
(* so that a consumer never re-derives them.  The arithmetic is factored   *)
(* into [Z]-only helpers: [lia] is unreliable in a goal that mentions      *)
(* [bv_unsigned] (durable-notes' zify-hook gotcha).                        *)
(* ---------------------------------------------------------------------- *)

Lemma pa_wrap_in_page (x k : Z) :
  0 <= x -> x < 18446744073709551616 -> x `mod` 4096 = 0 ->
  0 <= k -> k < 4096 ->
  (x + k) `mod` 18446744073709551616 = x + k.
Proof.
  intros H0 H1 Hm Hk0 Hk1. apply Z.mod_small. split; [lia|].
  apply Z.mod_divide in Hm; [| lia]. destruct Hm as [c ->]. lia.
Qed.

Lemma pa_rem_in_page (x k d : Z) :
  0 <= x -> x < 18446744073709551616 -> x `mod` 4096 = 0 ->
  0 <= k -> k < 4096 -> 0 < d -> 4096 `mod` d = 0 -> k `mod` d = 0 ->
  Z.rem ((x + k) `mod` 18446744073709551616) d = 0.
Proof.
  intros H0 H1 Hm Hk0 Hk1 Hd Hdd Hkd.
  rewrite (pa_wrap_in_page x k H0 H1 Hm Hk0 Hk1).
  rewrite Z.rem_mod_nonneg; [| lia | lia].
  apply Z.mod_divide; [lia|].
  apply Z.mod_divide in Hm; [| lia]. apply Z.mod_divide in Hdd; [| lia].
  apply Z.mod_divide in Hkd; [| lia].
  apply Z.divide_add_r; [ apply (Z.divide_trans d 4096 x Hdd Hm) | exact Hkd ].
Qed.

Lemma pa_add_aligned_in_page (p : Arch.pa) (k : nat) (d : Z) :
  bv_unsigned (p : SailStdpp.Values.mword 64) `mod` 4096 = 0 ->
  (Z.of_nat k < 4096)%Z -> (0 < d)%Z -> (4096 `mod` d = 0)%Z ->
  (Z.of_nat k `mod` d = 0)%Z ->
  is_aligned_paddr (Physaddr (pa_add p k)) d = true.
Proof.
  intros Hm Hk Hd Hdd Hkd. unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite RiscvExtras.uint_unsigned pa_add_unsigned.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  pose proof (bv_unsigned_in_range 64 p) as Hr.
  unfold bv_modulus in Hr. change (Z.of_N 64) with 64%Z in Hr.
  change (2 ^ 64)%Z with 18446744073709551616%Z in Hr.
  apply pa_rem_in_page;
    [ exact (proj1 Hr) | exact (proj2 Hr) | exact Hm
    | exact (Nat2Z.is_nonneg k) | exact Hk | exact Hd | exact Hdd | exact Hkd ].
Qed.

(* the four fields of descriptor-table entry [i] *)
Lemma d_desc_aligned8 (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (d_desc pd i)) 8 = true.
Proof.
  intros Hm Hi. unfold d_desc.
  apply (pa_add_aligned_in_page pd (16 * i)%nat 8 Hm); [ lia | lia | reflexivity |].
  replace (Z.of_nat (16 * i)) with ((2 * Z.of_nat i) * 8)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma d_desc_len_aligned4 (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add pd (16 * i + 8))) 4 = true.
Proof.
  intros Hm Hi.
  apply (pa_add_aligned_in_page pd (16 * i + 8)%nat 4 Hm); [ lia | lia | reflexivity |].
  replace (Z.of_nat (16 * i + 8)) with ((2 + 4 * Z.of_nat i) * 4)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma d_desc_flags_aligned2 (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add pd (16 * i + 12))) 2 = true.
Proof.
  intros Hm Hi.
  apply (pa_add_aligned_in_page pd (16 * i + 12)%nat 2 Hm); [ lia | lia | reflexivity |].
  replace (Z.of_nat (16 * i + 12)) with ((6 + 8 * Z.of_nat i) * 2)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma d_desc_next_aligned2 (pd : Arch.pa) (i : nat) :
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
  is_aligned_paddr (Physaddr (pa_add pd (16 * i + 14))) 2 = true.
Proof.
  intros Hm Hi.
  apply (pa_add_aligned_in_page pd (16 * i + 14)%nat 2 Hm); [ lia | lia | reflexivity |].
  replace (Z.of_nat (16 * i + 14)) with ((7 + 8 * Z.of_nat i) * 2)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

(* avail-ring entry [j] *)
Lemma d_ring_aligned2 (pav : Arch.pa) (j : nat) :
  bv_unsigned (pav : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (j < 8)%nat ->
  is_aligned_paddr (Physaddr (d_ring pav j)) 2 = true.
Proof.
  intros Hm Hj. unfold d_ring.
  apply (pa_add_aligned_in_page pav (4 + 2 * j)%nat 2 Hm); [ lia | lia | reflexivity |].
  replace (Z.of_nat (4 + 2 * j)) with ((2 + Z.of_nat j) * 2)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

(* Opts back out of [RiscvPtsto]'s [word_pointsto] seal: the disk resource is stated byte-wise and this file destructs the word.
   Local, so nothing above this file inherits the transparency. *)
Local Typeclasses Transparent word_pointsto word4_pointsto.

Section DiskInv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{XI : CurCtx}.

  (* -- the immutable page pointers (persistent after boot wiring) ------- *)

  (* The three queue pages, as the driver knows them:
     - the three immutable pointer cells (written once by init);
     - the pages' 4096-byte alignment (what rebuilds aligned word points-tos
       out of the protocol's byte-granular lease);
     - the FROZEN configuration [disk_cfg], the persistent witness init left
       behind.  Every live [virtio_proto] accessor exports the same witness
       for [v_cfg v], so [disk_cfg_agree] pins [v_cfg v = virtio_init_cfg pd
       pav pu] -- which is what makes the accessors' [used_idx_pa (v_cfg v)]
       / [ring_entry_pa (v_cfg v) p] the very addresses the CODE computes off
       [disk.desc]/[disk.avail]/[disk.used];
     - that all three pages are kernel DATA.  [addr_is_ram] (all a physical
       points-to carries) is not enough: the VA<->PA tier bridge and the
       dev_inv-opening leaves need [kmap_static (svpn_of a) KP_rw], which
       comes from [addr_is_kdata] via [KptPt.kdata_svpn_class]. *)
  Definition disk_geom (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64)
    : iProp Σ :=
    (d_desc_ptr ↦₈□ pd ∗ d_avail_ptr ↦₈□ pav ∗ d_used_ptr ↦₈□ pu ∗
     ⌜virtio_pages_aligned (virtio_init_cfg pd pav pu)⌝ ∗
     disk_cfg γ (virtio_init_cfg pd pav pu) ∗
     ⌜forall j, (j < 4096)%nat -> addr_is_kdata (pa_add pd j)⌝ ∗
     ⌜forall j, (j < 4096)%nat -> addr_is_kdata (pa_add pav j)⌝ ∗
     ⌜forall j, (j < 4096)%nat -> addr_is_kdata (pa_add pu j)⌝)%I.

  Global Instance disk_geom_persistent γ pd pav pu :
    Persistent (disk_geom γ pd pav pu).
  Proof. apply _. Qed.

  (* the kdata facts, in the form the tier bridges below consume *)
  Lemma disk_geom_static (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64) :
    disk_geom γ pd pav pu -∗
    ⌜(forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add pd j)) KP_rw)
     /\ (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add pav j)) KP_rw)
     /\ (forall j, (j < 4096)%nat -> kmap_static (svpn_of (pa_add pu j)) KP_rw)⌝.
  Proof.
    iIntros "(_ & _ & _ & _ & _ & %Hd & %Ha & %Hu)". iPureIntro.
    split_and!; intros j Hj; apply kdata_svpn_class;
      [ exact (Hd j Hj) | exact (Ha j Hj) | exact (Hu j Hj) ].
  Qed.

  Lemma disk_geom_canonical (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64) :
    disk_geom γ pd pav pu -∗
    ⌜(forall j, (j < 4096)%nat ->
        (uint (pa_add pd j : SailStdpp.Values.mword 64) < 274877906944)%Z)
     /\ (forall j, (j < 4096)%nat ->
        (uint (pa_add pav j : SailStdpp.Values.mword 64) < 274877906944)%Z)
     /\ (forall j, (j < 4096)%nat ->
        (uint (pa_add pu j : SailStdpp.Values.mword 64) < 274877906944)%Z)⌝.
  Proof.
    iIntros "(_ & _ & _ & _ & _ & %Hd & %Ha & %Hu)". iPureIntro.
    assert (Hk : forall a : Arch.pa, addr_is_kdata a ->
              (uint (a : SailStdpp.Values.mword 64) < 274877906944)%Z).
    { intros a Hka. unfold addr_is_kdata, ram_base, ram_size, text_end in Hka.
      (* [Arch.pa]'s width is an unreduced [if 64 =? 32 ...] match, so the
         ascribed [uint] is a DIFFERENT atom from the one in [addr_is_kdata]
         even though the two are convertible -- bridge them explicitly. *)
      first [ lia
            | (assert (Heq : (uint (a : SailStdpp.Values.mword 64) = uint a)%Z)
                 by reflexivity; rewrite Heq; lia) ]. }
    split_and!; intros j Hj; apply Hk; [ exact (Hd j Hj) | exact (Ha j Hj) | exact (Hu j Hj) ].
  Qed.

  (* -- per-descriptor bundles ------------------------------------------- *)

  (* one descriptor-table entry, word-granular (matching the sd/sw/sh/sh
     access pattern), any contents *)
  Definition desc_entry_own (pd : Arch.pa) (i : nat) : iProp Σ :=
    (∃ (va : SailStdpp.Values.mword 64) (vl : SailStdpp.Values.mword 32) (vf vn : SailStdpp.Values.mword 16),
       d_desc pd i ↦₈ va ∗
       pa_add pd (16 * i + 8)  ↦₄ vl ∗
       pa_add pd (16 * i + 12) ↦₂ vf ∗
       pa_add pd (16 * i + 14) ↦₂ vn)%I.

  Definition ops_own (i : nat) : iProp Σ :=
    (∃ (t r : SailStdpp.Values.mword 32) (s : SailStdpp.Values.mword 64),
       d_ops i ↦₄ t ∗ pa_add disk_base (168 + 16 * i + 4) ↦₄ r ∗
       pa_add disk_base (168 + 16 * i + 8) ↦₈ s)%I.

  (* everything a FREE descriptor slot owns.  [disk.info[i].b] IS here: no
     descriptor ever names that cell, so the device cannot touch it, and
     while the slot is free it is ordinary driver state like the rest.  It
     leaves for the receipt only at the publish and comes back when the poll
     reads [b->disk] as 0 (finding 5) -- that in-flight window is exactly the
     stretch when its reader is the interrupt handler rather than the thread
     that allocated the slot. *)
  Definition free_slot_res (pd : Arch.pa) (i : nat) : iProp Σ :=
    (desc_entry_own pd i ∗ ops_own i ∗
     (∃ sb : bv 8, d_info_status i ↦ₘ sb) ∗
     (∃ w : SailStdpp.Values.mword 64, d_info_b i ↦₈ w))%I.

  (* The part of [free_slot_res] that lives in [struct disk]'s .bss rather
     than on the descriptor page: slot [i]'s [ops] header, its
     [info[i].status] byte and its [info[i].b] pointer cell.  The loader
     zeroes all three and [virtio_disk_init] never touches any of them, so
     this is what a BOOT chain can honestly claim about them, and it is what
     [SpecMain.main_globals_raw] hands over (contents existential, exactly
     like the other raw-global cells).  Splitting it out is what makes
     [free_slot_res] assemblable at boot: the other half,
     [desc_entry_own pd i], comes off the freshly-zeroed descriptor page. *)
  Definition disk_slot_raw (i : nat) : iProp Σ :=
    (ops_own i ∗
     (∃ sb : bv 8, d_info_status i ↦ₘ sb) ∗
     (∃ w : SailStdpp.Values.mword 64, d_info_b i ↦₈ w))%I.

  Lemma free_slot_res_split (pd : Arch.pa) (i : nat) :
    free_slot_res pd i ⊣⊢ desc_entry_own pd i ∗ disk_slot_raw i.
  Proof. reflexivity. Qed.

  (* -- the linkage between a slot and its struct buf -------------------- *)

  (* the pure connection [virtio_disk_rw] establishes at publish: the head
     index is a real descriptor, the status byte is info[head].status, the
     buffer is b->data, and the request length is one block *)
  Definition slot_buf_link (sl : vslot) (b : Arch.pa) : Prop :=
    exists h : nat,
      (h < 8)%nat
      /\ bv_unsigned (vr_head (vs_req sl)) = Z.of_nat h
      /\ vr_status (vs_req sl) = d_info_status h
      /\ vr_buf (vs_req sl) = b_data b
      /\ vs_len sl = 1024%nat.

  Definition sl_head (sl : vslot) : nat :=
    Z.to_nat (bv_unsigned (vr_head (vs_req sl))).

  (* -- per-position states ---------------------------------------------- *)

  (* [flight_res] and [parked_res] ARE GONE (finding 5).  They were the
     driver's per-request state, split by whether the interrupt handler had
     processed the position yet.  Both are now the device invariant's
     per-descriptor receipt: its two disjuncts ARE that split, keyed by
     [b->disk] rather than by which of two maps the entry sat in, and the
     handler moves one to the other in a single store. *)

  (* -- the descriptor triple, as vocabulary ----------------------------- *)

  (* A chain is three descriptors; these say which three and that they are
     three distinct real ones.  Pure vocabulary for the rw proof (the
     allocator's result, [free_desc]'s [i < 8] premise) -- nothing is
     COUNTED with them: the ring window is a pigeonhole over heads inside the
     device invariant ([VirtioProto.heads_res_at_window]). *)
  Definition tri_set (T : nat * nat * nat) : gset nat :=
    {[ T.1.1 ]} ∪ {[ T.1.2 ]} ∪ {[ T.2 ]}.

  Definition tri_ok (T : nat * nat * nat) : Prop :=
    T.1.1 <> T.1.2 /\ T.1.1 <> T.2 /\ T.1.2 <> T.2
    /\ (T.1.1 < 8)%nat /\ (T.1.2 < 8)%nat /\ (T.2 < 8)%nat.

  (* THE AVAIL-RING CELLS ARE NOT HERE ANY MORE (finding 5).  All eight
     belong to the device invariant's lease; the driver reaches its cell only
     through [VirtioProto.virtio_proto_ring_acc], for the one instruction that
     writes it.  Dropping them from this resource is what dropped the interval
     clause below with them: the cells were the only reason the live positions
     had to be a contiguous window. *)

  (* -- THE lock resource ------------------------------------------------ *)

  (* WHAT THE LOCK OWNS (finding 5): the free array, the counters, and the
     CLAIM MAP -- and nothing per-request.  The buffer, the pinned chain, the
     crash permit, [b->disk] and [disk.info[i].b] all live in the device
     invariant's per-descriptor RECEIPT: that is where the publisher left
     them at its [avail->idx] bump and where the interrupt handler puts the
     completed chain back.  A sleeping [virtio_disk_rw] re-finds its own
     request through the [HActive] receipt fragment it never let go of.

     THE CLAIM MAP [dn_claim] is what the interrupt handler carries between
     its openings of the device invariant.  It holds this lock for its whole
     loop, so the map is stable in its hands; each receipt's [HActive] arm
     holds the fragment for its own position, and an accessor agrees the two
     -- so the claim the handler read off its own map at the used-element
     load is the claim every later opening is about.  The publisher inserts
     its row here (fresh: every row is below [np]) and hands the fragment to
     the publish; the woken publisher gets it back with the chain and deletes
     the row at free_chain.  Nothing is COUNTED: the ring window that the
     descriptor triples used to bound is a pigeonhole over heads inside the
     device invariant ([VirtioProto.heads_res_at_window]). *)
  (* THE ROW DESIGN (virtio-tso-port.md): the two driver-written cells of a
     live claim -- [disk.info[id].b], pinned to the claim's buffer, and
     [b->disk] -- live HERE, in the vdisk-lock payload, one row per claim.
     Every access to them in xv6 is under [vdisk_lock]: the publish writes
     them, the sleeper's [while (b->disk == 1)] reads [b->disk], the
     interrupt handler reads [info[id].b] and stores [b->disk = 0].  Under
     TSO a cell parked in the device invariant would be RAW and no hart
     could load or store it again (A6.9/A6.18); in the payload the cells
     are ctx cells, transported to each holder by acquire ([disk_res_at]'s
     CtxMorph).  The Right arm's witness is the position's completion record
     BELOW the payload's own watermark [nr]: the handler flips the row after
     depositing record [u] with [disk_read_at γ u] in hand, leaving
     [nr = S u], and [nr] only grows.  [VirtioProto.virtio_proto_collect_acc]
     cashes it. *)
  Definition claim_cells (γ : disk_names) (nr p : nat) (dc : dclaim) : iProp Σ :=
    (d_info_b (sl_head (dc_slot dc)) ↦₈ (dc_buf dc : SailStdpp.Values.mword 64) ∗
     (* A6.125 step 3: the publisher's HALF CTX CELLS of the pin (the arms
        with half the stamps and half the memory; the lease holds the sealed
        halves) -- what makes the pin's cells ctx cells again at collect *)
     hcell_map cur_ctx (dc_pin dc) ∗
     (b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1)
      ∨ (b_disk (dc_buf dc) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 0) ∗
         ∃ u : nat, disk_ord γ p u ∗ ⌜(u < nr)%nat⌝)))%I.

  (* the rows survive the handler's watermark bump *)
  Lemma claim_cells_nr_mono (γ : disk_names) (nr nr' p : nat) (dc : dclaim) :
    (nr <= nr')%nat -> claim_cells γ nr p dc -∗ claim_cells γ nr' p dc.
  Proof.
    iIntros (Hle) "(Hib & Hhc & [Hbd | (Hbd & %u & #Hord & %Hlt)])".
    - iFrame "Hib Hhc". iLeft. iExact "Hbd".
    - iFrame "Hib Hhc". iRight. iFrame "Hbd". iExists u. iFrame "Hord". iPureIntro. lia.
  Qed.

  Definition disk_res (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64) : iProp Σ :=
    (∃ (np nr : nat) (cm : gmap nat dclaim) (fr : nat -> bool),
       (* every row is below the published count (so the publisher's is
          fresh), names its own position, and links its slot to its buffer
          -- which is how the handler, reading the claim off this map, knows
          the status byte is [info[h].status] and the head is [h] *)
       ⌜forall p dc, cm !! p = Some dc ->
          (p < np)%nat /\ dc_pos dc = p /\ slot_buf_link (dc_slot dc) (dc_buf dc)⌝ ∗
       (* the protocol tokens *)
       disk_pub γ np ∗
       disk_done_lb γ nr ∗
       (* THE READ WATERMARK, exactly: [nr] is how far the handler has walked
          the used ring, and [d_used_idx] below is the driver's own copy of
          it.  Depositing a completed chain REQUIRES this half at that
          record's index ([VirtioProto.virtio_proto_deposit_acc]), which is
          what forces the handler to drain in order (finding 5). *)
       disk_read_at γ nr ∗
       (* A6.126 §6: THE READER'S FLOORS -- the two floor stamps of the used
          index word (the init hart's own byte writes, transported to every
          later holder by [lk_floor]) and the reader floor [F]: a VIEW bound
          (left arm only; the reclaim raises it to the read's view) under
          which every reclaimed completion's position sits.  What
          [VirtioProto.virtio_proto_used_rel_read_ok] cashes: a holder reads
          the index as [wrap16 k] with [nr ≤ k ≤ nc].  The reclaimed count
          itself is [disk_read_at γ nr] above (the T-leg's [disk_nr]: same
          ghost, same watermark -- virtio-tso-port.md decision 5). *)
       (∃ t0 t1 F : nat,
          disk_fl γ t0 t1 ∗ disk_flr γ F ∗
          lk_floor cur_ctx t0 ∗ lk_floor cur_ctx t1 ∗ TsoCtx.ctx_floor cur_ctx F) ∗
       (* NOTHING IS HALF-PUBLISHED while the lock is free: a publisher sets
          the staged head at its ring store and spends it at the index bump,
          both under [vdisk_lock]. *)
       disk_stage γ None ∗
       ghost_map_auth (dn_claim γ) 1 cm ∗
       (* the claim ROWS (the row design, above) *)
       ([∗ map] p ↦ dc ∈ cm, claim_cells γ nr p dc) ∗
       d_used_idx ↦₂ wrap16 nr ∗
       (* THE FREE DESCRIPTORS, and each one's RECEIPT at [HInactive].  The
          allocator hands both over together, which is what gives
          [virtio_disk_rw] the token it flips to [HActive] and then holds
          across [sleep()]. *)
       ([∗ list] i ∈ seq 0 8,
          d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
          (if fr i then free_slot_res pd i ∗ i ↪[dn_head γ] HInactive
           else emp)) ∗
       (* A6.126 §6 ON THE POP MODEL (virtio-tso-port.md decision 4): the
          eight ring cells stay in the lease's control set at HALF/HALF, and
          THIS is the other half -- the holder's half ctx cells (half the
          stamp with its arm, half the memory) of the whole ring, at
          whatever contents [rg] the cells hold.  A publisher carves its
          cell out of the list, joins it with the lease's sealed half
          ([VirtioProto.virtio_proto_ring_acc] + [DiskAvail.hcell_map_join])
          into a full ctx cell, stores through it, and splits the new cell
          back the same way ([DiskAvail.ring_hcells]).  The T-leg's
          per-publish pin/unpin of ring cells is NOT this design. *)
       ring_hcells cur_ctx pav ∗
       (* A6.124: the holder's HALF of the avail-index word, stamps exposed,
          floors beside them -- what a holder reads with and what the
          publish store re-mints (DiskAvail.v).  LAST, so every destructuring
          pattern in the tree is a one-name change. *)
       avail_half pav np)%I.



  (* ==================================================================== *)
  (* Tier bridges over an ARBITRARY byte window.                          *)
  (*                                                                      *)
  (* Everything the driver formats -- the descriptor entries, the request  *)
  (* header, the avail-ring entry -- is owned word-granularly at the       *)
  (* VA-based tier ([↦₈]/[↦₄]/[↦₂]/[↦ₘ]), while the protocol accessors     *)
  (* ([virtio_proto_publish_acc] / [_reclaim_acc]) speak the PHYSICAL byte *)
  (* tier ([phys_map]/[phys_list]).  KMap.v has the pointwise bridge and   *)
  (* its 4096-byte instance; these are the same conversion at an arbitrary *)
  (* window length, in both directions -- the pin is assembled through the *)
  (* first and the reclaimed payoff is taken apart through the second.     *)
  (* ==================================================================== *)

  Lemma phys_pointsto_ram (a : Arch.pa) (dq : dfrac) (b : bv 8) :
    phys_pointsto a dq b ⊢ ⌜addr_is_ram a⌝.
  Proof. rewrite /phys_pointsto. iIntros "[_ $]". Qed.

  (* ---- THE TWO DIRECTIONS ARE NO LONGER SYMMETRIC (the machine flip;
     tso-machine-flip.md §6 amendments A6.8/A6.9).  Before it, this file's
     bridges all ran through the VA-tier [↦ₘ], which the M1 flip had made
     CONTEXT-indexed, and the shim silently crossed ctx<->raw at both ends.
     Post-flip:

       ctx -> raw  is [TsoCtx.ctx_pointsto_forget]: sound, one-way, and it
                   DROPS the byte's latest-write timestamp fragment and its
                   clean/dirty bit;
       raw -> ctx  is IMPOSSIBLE above the interpretation.  The timestamp is
                   a [ghost_map] element of [era_ts_name] and the era's tie
                   is [dom TM = dom mem], so every byte's element was handed
                   out once and there is no rule that can mint another.  A
                   raw byte has left the ledger for good.

     So the CORE of the window bridge is stated at the RAW fact in BOTH
     directions -- it is a pure kmap/identity-mapping fact and never wanted a
     context -- and the ctx entry point is a thin [_forget] wrapper on the
     to-phys side only.  The four consumers that need a DMA-written byte back
     IN the ledger are named at [phys_to_word8] / [phys_to_byte] below. ---- *)

  (* [mem_win_to_phys_raw] / [ctx_ident_ledger] / [mem_win_to_phys] moved to
     DiskAvail.v (A6.126 §6: [used_split_init] needs them and this file
     imports that one). *)

  Lemma phys_win_to_mem (p : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8) :
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add p j)) KP_rw) ->
    (forall j, (j < n)%nat ->
       (uint (pa_add p j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 n, phys_ledger (pa_add p j) dq (f j)) -∗
    ([∗ list] j ∈ seq 0 n, mem_pointsto (pa_add p j) dq (f j)).
  Proof.
    iIntros (Hstat Hcan) "#Hb Hbytes".
    iApply (big_sepL_impl with "Hbytes").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    (* the ledger element is DROPPED here, and that half of A6.9 stands: the
       re-entry to the CONTEXT tier still needs a clean/dirty bit no law can
       mint.  This direction lands at the RAW VA byte, as before. *)
    iDestruct (phys_ledger_forget with "H") as "H".
    iDestruct (phys_pointsto_ram with "H") as %Hram.
    iApply (phys_ident_mem (pa_add p (0 + k)%nat) dq (f (0 + k)%nat)
              (Hstat (0 + k)%nat ltac:(lia)) Hram (Hcan (0 + k)%nat ltac:(lia))
              with "Hb H").
  Qed.

  (* the canonicality side condition of [phys_win_to_mem] is not an
     assumption at a call site that still holds the VA-tier window: every
     owned byte is canonical. *)
  Lemma mem_win_canonical (p : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8) (j : nat) :
    (j < n)%nat ->
    ([∗ list] k ∈ seq 0 n, (pa_add p k) ↦ₘ{dq} f k) -∗
    ⌜(uint (pa_add p j : SailStdpp.Values.mword 64) < 274877906944)%Z⌝.
  Proof.
    iIntros (Hj) "Hbytes".
    iDestruct (big_sepL_lookup _ (seq 0 n) j j with "Hbytes") as "Hb".
    { rewrite lookup_seq_lt; [reflexivity | exact Hj]. }
    (* the canonicality conjunct rides inside the ctx fact
       ([TsoCtx.ctx_pointsto_canonical]) -- no crossing *)
    iApply (ctx_pointsto_canonical with "Hb").
  Qed.

  (* ---- the WORD-granular bridges, both directions.  These are the ones
     the driver actually uses: it formats the descriptors with sd/sw/sh into
     [↦₈]/[↦₄]/[↦₂] and must hand the protocol [phys_word*]/[phys_pointsto]
     byte windows; the reclaimed payoff travels the other way.

     AFTER M1 STAGE 2 ALL THREE WIDTHS ARE CTX, so all three [_to_phys]
     directions forget and all three [phys_to_] directions are stated at
     the RAW fact -- the ledger re-entry is the same missing gate for a
     halfword as for a doubleword (§6 amendment A6.9, spelled out at
     [phys_to_word8]).  The
     alignment premise is discharged at the call site from
     [virtio_pages_aligned] (or from the [↦₂]/[↦₄]/[↦₈] itself in the
     to-phys direction, where it is already carried). ---- *)

  Lemma word2_to_phys (a : Arch.pa) (w : bv 16) :
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₂ w -∗ phys_word2 a w.
  Proof.
    (* M1 STAGE 2: [↦₂] is a CTX tower now, so the window LEAVES THE LEDGER
       here, through the [_forget] entry point. *)
    iIntros (Hs) "#Hb [_ Hbytes]". rewrite /phys_word2.
    iApply (mem_win_to_phys a 2 (DfracOwn 1) (fun j => nth_byte w j) Hs
              with "Hb Hbytes").
  Qed.

  Lemma phys_to_word2 (a : Arch.pa) (w : bv 16) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 2)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_word2 a w -∗
    word2_pointsto a (DfracOwn 1) w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb Hbytes". rewrite /phys_word2.
    iDestruct (phys_win_to_mem a 2 (DfracOwn 1) (fun j => nth_byte w j) Hs Hc
                 with "Hb Hbytes") as "Hm".
    rewrite /word2_pointsto. iFrame "Hm". iPureIntro. exact Hal.
  Qed.

  Lemma word4_to_phys (a : Arch.pa) (w : bv 32) :
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₄ w -∗ phys_word4 a w.
  Proof.
    (* M1 STAGE 2: [↦₄] is a CTX tower now, so the window LEAVES THE LEDGER
       here, through the [_forget] entry point -- which is what a DMA lease
       is (§6 amendment A6.9). *)
    iIntros (Hs) "#Hb [_ Hbytes]". rewrite /phys_word4.
    iApply (mem_win_to_phys a 4 (DfracOwn 1) (fun j => nth_byte w j) Hs
              with "Hb Hbytes").
  Qed.

  Lemma phys_to_word4 (a : Arch.pa) (w : bv 32) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 4)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_word4 a w -∗
    word4_pointsto a (DfracOwn 1) w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb Hbytes". rewrite /phys_word4.
    iDestruct (phys_win_to_mem a 4 (DfracOwn 1) (fun j => nth_byte w j) Hs Hc
                 with "Hb Hbytes") as "Hm".
    rewrite /word4_pointsto. iFrame "Hm". iPureIntro. exact Hal.
  Qed.

  (* the doubleword has no [phys_word8] in VirtioProto, so it bridges to the
     bare byte window (the same shape [phys_map]/[phys_list] consume) *)
  Definition phys_word8 (a : Arch.pa) (w : bv 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, phys_ledger (pa_add a j) (DfracOwn 1) (nth_byte w j))%I.

  Lemma word8_to_phys (a : Arch.pa) (w : bv 64) :
    (forall j, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₈ w -∗ phys_word8 a w.
  Proof.
    iIntros (Hs) "#Hb [_ Hbytes]". rewrite /phys_word8.
    iApply (mem_win_to_phys a 8 (DfracOwn 1) (fun j => nth_byte w j) Hs
              with "Hb Hbytes").
  Qed.

  (* THE LEDGER RE-ENTRY IS MISSING, AND IT IS MISSING ON PURPOSE
     (tso-machine-flip.md §6 amendment A6.9).  The doubleword and the status
     byte are the two windows whose consumers want the CONTEXT-indexed fact
     back ([↦₈] and [↦ₘ] are flipped spellings), and raw -> ctx cannot be
     proven above the interpretation -- see the block at
     [mem_win_to_phys_raw].  Both are therefore stated at the RAW fact, so
     the error lands at the four call sites that actually need a DMA-touched
     byte to re-enter the ledger ([ProofVirtioDiskRwF] x3,
     [ProofVirtioDiskIntr] x1), each of which is one worklist entry.

     WHAT THOSE SITES WILL NEED, so the entry is written down rather than
     implied: the lease must hold the window's context PARKED
     ([TsoCtx.ctx_parked ξ T]) together with the timestamp fragments, the
     DMA's own [wp_disk_step] callback must move those fragments to the
     appended log (§6 amendment A6.2), and the reclaiming thread -- whose
     lock acquire put its view at the log top -- mints [ctx_dom ξ cur_ctx]
     with [TsoCtxLedger.ctx_dom_of_parked] and re-registers the bytes through
     [ctx_morph_word].  That is the ctx_dom handoff tso-port.md §1's
     RULING 2 promised; nothing shorter is sound, because a byte the DEVICE
     wrote is visible to a hart for exactly one reason -- the hart's view
     passed the DMA's timestamp -- and only an acquire says so. *)
  Lemma phys_to_word8 (a : Arch.pa) (w : bv 64) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    (forall j, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 8)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_word8 a w -∗ word_pointsto a (DfracOwn 1) w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb Hbytes". rewrite /phys_word8.
    iDestruct (phys_win_to_mem a 8 (DfracOwn 1) (fun j => nth_byte w j) Hs Hc
                 with "Hb Hbytes") as "Hm".
    rewrite /word_pointsto. iFrame "Hm". iPureIntro. exact Hal.
  Qed.

  (* the single byte, for the status cell *)
  Lemma byte_to_phys (a : Arch.pa) (b : bv 8) :
    kmap_static (svpn_of a) KP_rw ->
    kmap_static_claims -∗ a ↦ₘ b -∗ phys_ledger a (DfracOwn 1) b.
  Proof.
    iIntros (Hs) "#Hb H".
    iApply (ctx_ident_ledger a (DfracOwn 1) b Hs with "Hb H").
  Qed.

  (* the status byte's re-entry: RAW, for the reason spelled out at
     [phys_to_word8] above *)
  Lemma phys_to_byte (a : Arch.pa) (b : bv 8) :
    kmap_static (svpn_of a) KP_rw ->
    (uint (a : SailStdpp.Values.mword 64) < 274877906944)%Z ->
    kmap_static_claims -∗ phys_ledger a (DfracOwn 1) b -∗
    mem_pointsto a (DfracOwn 1) b.
  Proof.
    iIntros (Hs Hc) "#Hb H".
    iDestruct (phys_ledger_forget with "H") as "H".
    iDestruct (phys_pointsto_ram with "H") as %Hram.
    iApply (phys_ident_mem a (DfracOwn 1) b Hs Hram Hc with "Hb H").
  Qed.

  (* [phys_map] over a disjoint union splits -- how the pin is assembled out
     of its six regions and taken apart again. *)
  Lemma phys_map_union (m1 m2 : gmap Arch.pa (bv 8)) :
    m1 ##ₘ m2 -> phys_map (m1 ∪ m2) ⊣⊢ phys_map m1 ∗ phys_map m2.
  Proof. intro Hd. rewrite /phys_map. apply big_sepM_union. exact Hd. Qed.

  (* ==================================================================== *)
  (* Surgery on the two eight-element bundles.                            *)
  (*                                                                      *)
  (* Both [ring_slots_res] and [disk_res]'s free-descriptor conjunct are   *)
  (* [big_sepL] over [seq 0 8] whose BODY depends on the index; taking one *)
  (* slot out therefore has to change the predicate at that index alone.   *)
  (* [seq8_delete] is that peel, once, for an arbitrary body.              *)
  (* ==================================================================== *)

  Lemma seq8_delete (F : nat -> iProp Σ) (j : nat) :
    (j < 8)%nat ->
    ([∗ list] k ∈ seq 0 8, F k)
    ⊣⊢ F j ∗ ([∗ list] k ∈ seq 0 8, if bool_decide (k = j) then emp else F k).
  Proof.
    intro Hj.
    assert (Hlk : seq 0 8 !! j = Some j).
    { rewrite lookup_seq_lt; [reflexivity | exact Hj]. }
    rewrite (big_sepL_delete (fun _ k => F k) (seq 0 8) j j Hlk).
    apply bi.sep_proper; [reflexivity|].
    apply big_sepL_proper. intros k y Hk.
    apply lookup_seq in Hk as [-> _].
    destruct (decide (k = j)) as [->|Hne].
    - rewrite bool_decide_eq_true_2; [reflexivity|]. reflexivity.
    - rewrite bool_decide_eq_false_2; [reflexivity|]. cbn. exact Hne.
  Qed.

  (* THE THREE RING-POOL LEMMAS ARE GONE (finding 5).  They moved a cell
     between the driver's pool and a request's pin at publish and reclaim;
     all eight cells are the device invariant's now, and the driver touches
     one only through [VirtioProto.virtio_proto_ring_acc]. *)

  (* the free-descriptor bundle for slot [i], taken out of [disk_res]'s
     eight-element conjunct.  [fr i = true] hands over the whole bundle and
     leaves the cell behind; the caller clears the cell with a plain store
     and re-closes at [fr' := <i := false> fr]. *)
  (* A FREE DESCRIPTOR CARRIES ITS RECEIPT (finding 5).  That is what makes
     "allocating a descriptor hands the caller the receipt" fall out of the
     allocator with nothing extra threaded: the token comes with the bytes. *)
  Definition free_bundles (γ : disk_names) (pd : Arch.pa) (fr : nat -> bool)
    : iProp Σ :=
    ([∗ list] i ∈ seq 0 8,
       d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
       (if fr i then free_slot_res pd i ∗ i ↪[dn_head γ] HInactive else emp))%I.

  Lemma free_bundles_unfold (γ : disk_names) (pd : Arch.pa) (fr : nat -> bool) :
    free_bundles γ pd fr ⊣⊢
    ([∗ list] i ∈ seq 0 8,
       d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
       (if fr i then free_slot_res pd i ∗ i ↪[dn_head γ] HInactive else emp)).
  Proof. reflexivity. Qed.

  Definition fr_upd (fr : nat -> bool) (i : nat) (b : bool) : nat -> bool :=
    fun k => if Nat.eq_dec k i then b else fr k.

  Lemma fr_upd_eq (fr : nat -> bool) (i : nat) (b : bool) : fr_upd fr i b i = b.
  Proof. unfold fr_upd. destruct (Nat.eq_dec i i); [reflexivity | congruence]. Qed.

  Lemma fr_upd_ne (fr : nat -> bool) (i k : nat) (b : bool) :
    k <> i -> fr_upd fr i b k = fr k.
  Proof. intro Hne. unfold fr_upd. destruct (Nat.eq_dec k i); [congruence|reflexivity]. Qed.

  (* the residual bundle, with slot [i] cut out *)
  Definition free_bundles_but (γ : disk_names) (pd : Arch.pa) (fr : nat -> bool)
      (i : nat) : iProp Σ :=
    ([∗ list] k ∈ seq 0 8,
       if bool_decide (k = i) then emp
       else (d_free_cell k ↦ₘ (if fr k then Z_to_bv 8 1 else byte_zero) ∗
             (if fr k then free_slot_res pd k ∗ k ↪[dn_head γ] HInactive
              else emp)))%I.

  Lemma free_bundles_split (γ : disk_names) (pd : Arch.pa) (fr : nat -> bool)
      (i : nat) :
    (i < 8)%nat ->
    free_bundles γ pd fr ⊣⊢
    (d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
     (if fr i then free_slot_res pd i ∗ i ↪[dn_head γ] HInactive else emp)) ∗
    free_bundles_but γ pd fr i.
  Proof.
    intro Hi. rewrite /free_bundles /free_bundles_but.
    apply (seq8_delete
             (fun k => d_free_cell k ↦ₘ (if fr k then Z_to_bv 8 1 else byte_zero) ∗
                       (if fr k then free_slot_res pd k ∗ k ↪[dn_head γ] HInactive
                        else emp))%I i Hi).
  Qed.

  (* the residual does not see slot [i], so it survives any update there *)
  Lemma free_bundles_but_upd (γ : disk_names) (pd : Arch.pa) (fr : nat -> bool)
      (i : nat) (b : bool) :
    free_bundles_but γ pd fr i ⊣⊢ free_bundles_but γ pd (fr_upd fr i b) i.
  Proof.
    rewrite /free_bundles_but. apply big_sepL_proper. intros k y Hk.
    apply lookup_seq in Hk as [-> _].
    case_bool_decide as Hd; [reflexivity|].
    rewrite (fr_upd_ne fr i (0 + k)%nat b Hd). reflexivity.
  Qed.

End DiskInv.

(* [tso DiskInv.v:920]: the geometry's transport (three discarded pointer
   words + pure facts + the ghost cfg). *)
Section DiskGeomMorph.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Global Instance disk_geom_morph (γ : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) :
    CtxMorph (λ ξ0 : CtxId, disk_geom (XI := ξ0) γ pd pav pu).
  Proof.
    iIntros (ξ ξ') "Hd H". rewrite /disk_geom.
    iDestruct "H" as "(H1 & H2 & H3 & %Hal & Hcfg & %Hk1 & %Hk2 & %Hk3)".
    iMod (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H1") as "[Hd H1]".
    iMod (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H2") as "[Hd H2]".
    iMod (ctx_morph_word _ _ _ _ ξ ξ' with "Hd H3") as "[Hd H3]".
    iModIntro. iFrame "Hd H1 H2 H3 Hcfg". iPureIntro. auto.
  Qed.
End DiskGeomMorph.

(* ====================================================================== *)
(* A6.121 (tso-flip DiskInv.v:880): THE PAYLOAD OVER AN EXPLICIT CONTEXT.   *)
(* [disk_res_at γ pd pav pu] is what the vdisk lock surface takes as its    *)
(* [CtxId → iProp]; the transport obligation is discharged structurally     *)
(* ([CtxMorphTac.ctx_morph_solve]) down to the component instances below,  *)
(* applied by name.  Main's [disk_res] body is its own (one claim map, the  *)
(* stage and read cursors); only the component list differs from the       *)
(* T-leg's.                                                                 *)
(* ====================================================================== *)
Section DiskResAt.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Global Instance desc_entry_own_morph pd i :
    CtxMorph (λ ξ, desc_entry_own (XI := ξ) pd i).
  Proof. rewrite /desc_entry_own. ctx_morph_solve. Qed.
  Global Instance ops_own_morph i : CtxMorph (λ ξ, ops_own (XI := ξ) i).
  Proof. rewrite /ops_own. ctx_morph_solve. Qed.
  Global Instance free_slot_res_morph pd i :
    CtxMorph (λ ξ, free_slot_res (XI := ξ) pd i).
  Proof.
    rewrite /free_slot_res. ctx_morph_solve.
    all: first [ apply desc_entry_own_morph | apply ops_own_morph ].
  Qed.
  (* A6.126 §6: a bare view floor transports like [lk_floor]'s left arm *)
  Global Instance ctx_floor_morph (lo : nat) : CtxMorph (λ ξ, TsoCtx.ctx_floor ξ lo).
  Proof.
    iIntros (ξ ξ') "Hd #Hfl".
    iDestruct (TsoCtx.ctx_floor_dom with "Hd Hfl") as "[Hd #Hfl']".
    iModIntro. iFrame "Hd Hfl'".
  Qed.

  Global Instance claim_cells_morph γ nr p dc :
    CtxMorph (λ ξ, claim_cells (XI := ξ) γ nr p dc).
  Proof. rewrite /claim_cells. ctx_morph_solve. all: apply _. Qed.

  Definition disk_res_at (γ : disk_names)
      (pd pav pu : SailStdpp.Values.mword 64) : CtxId → iProp Σ :=
    λ ξ, disk_res (XI := ξ) γ pd pav pu.
  Global Instance disk_res_at_morph γ pd pav pu :
    CtxMorph (disk_res_at γ pd pav pu).
  Proof.
    rewrite /disk_res_at /disk_res. ctx_morph_solve.
    all: first [ apply free_slot_res_morph | apply claim_cells_morph
               | apply ring_hcells_morph
               | apply hcell_map_morph | apply avail_half_morph
               | apply WpLock.lk_floor_morph | apply ctx_floor_morph ].
  Qed.
End DiskResAt.

(* ====================================================================== *)
(* Building [slot_pin_ok] for the three-descriptor chain rw formats.       *)
(*                                                                        *)
(* WHICH bytes are in the pin is an OWNERSHIP fact (the publisher owns the *)
(* ring cell, the three descriptor entries and the request header, so      *)
(* their byte maps are disjoint and their union is the pin); what is PURE  *)
(* is that a pin whose fields READ as below parses -- from every agreeing  *)
(* view -- to exactly the request the driver meant.  So the field contents *)
(* arrive as [read_bytes] hypotheses and the whole proof is               *)
(* [view_word_read] plus the two flag computations.                       *)
(* ====================================================================== *)

(* the four words of descriptor-table entry [i], as the pin reads them *)
Definition desc_reads (pin : gmap Arch.pa (bv 8)) (pd : Arch.pa) (i : nat)
    (a : bv 64) (l : bv 32) (f n : bv 16) : Prop :=
  read_bytes pin (d_desc pd i) 8 = Some a
  /\ read_bytes pin (pa_add pd (16 * i + 8)) 4 = Some l
  /\ read_bytes pin (pa_add pd (16 * i + 12)) 2 = Some f
  /\ read_bytes pin (pa_add pd (16 * i + 14)) 2 = Some n.

Lemma desc_at_of_reads (c : virtio_cfg) (mv : vmem) (pin : gmap Arch.pa (bv 8))
    (pd : Arch.pa) (i : nat) (a : bv 64) (l : bv 32) (f n : bv 16) :
  vc_desc c = pd -> mem_view pin mv ->
  desc_reads pin pd i a l f n ->
  desc_at c mv (Z.of_nat i) = VqDesc a l f n.
Proof.
  intros Hc Hv (H0 & H8 & H12 & H14).
  unfold desc_at. cbv zeta. rewrite Hc.
  assert (Hb : pa_off pd (vq_desc_size * Z.of_nat i) = d_desc pd i).
  { unfold pa_off, d_desc, vq_desc_size. f_equal; lia. }
  rewrite Hb.
  assert (H8a : pa_off (d_desc pd i) 8 = pa_add pd (16 * i + 8)%nat).
  { unfold pa_off, d_desc. rewrite pa_add_add. f_equal; lia. }
  assert (H12a : pa_off (d_desc pd i) 12 = pa_add pd (16 * i + 12)%nat).
  { unfold pa_off, d_desc. rewrite pa_add_add. f_equal; lia. }
  assert (H14a : pa_off (d_desc pd i) 14 = pa_add pd (16 * i + 14)%nat).
  { unfold pa_off, d_desc. rewrite pa_add_add. f_equal; lia. }
  rewrite H8a H12a H14a.
  rewrite (view_word_read pin mv (d_desc pd i) 8 a Hv H0).
  rewrite (view_word_read pin mv _ 4 l Hv H8).
  rewrite (view_word_read pin mv _ 2 f Hv H12).
  rewrite (view_word_read pin mv _ 2 n Hv H14).
  reflexivity.
Qed.

(* the slot rw publishes: head [hd], the request type/sector out of the
   header, the caller's 1024-byte buffer, info[hd].status *)
(* [bs] is the BLOCK's content, in both directions: an OUT request's payload
   (which the pin covers) or an IN request's current disk content (which the
   published pending resource pins).  See [VirtioQueue.vs_data]. *)
(* [kq] is the CRASH-PERMIT key ([VirtioQueue.vs_perm]): the permit-invariant
   map key and the saved-prop gname [PermInv.perm_deposit] chose for this
   request.  Pure data; it is what lets the woken publisher recognize its own
   receipt, since its claim pins the slot. *)
Definition rw_slot (hd : nat) (ty : bv 32) (sec : bv 64) (buf sts : Arch.pa)
    (bs : list (bv 8)) (kq : nat * positive)
  : vslot :=
  VSlot (VioReq (Z_to_bv 16 (Z.of_nat hd)) ty sec buf (Z_to_bv 32 1024) sts
                (* the data descriptor is WRITABLE exactly when the driver
                   marked it so, and xv6 marks it for a read: the flag word
                   it publishes is 3 (NEXT|WRITE) for a read and 1 (NEXT) for
                   a write, so this is that word's WRITE bit and not a second
                   opinion about the request type.  [vd_has] reads only the
                   flags, so the descriptor's other fields are immaterial
                   here. *)
                (vd_has (VqDesc buf (Z_to_bv 32 1024)
                           (Z_to_bv 16 (if bv_unsigned ty =? virtio_blk_t_out
                                        then 1 else 3))
                           (Z_to_bv 16 0))
                        vring_desc_f_write))
        bs kq.

(* THE PUBLISHED SLOT'S WRITE IDENTITY (phase C2a), by conversion: what the
   crash permit deposited with this request has to be indexed by. *)
Lemma rw_slot_wr (hd : nat) (ty : bv 32) (sec : bv 64) (buf sts : Arch.pa)
    (bs : list (bv 8)) (kq : nat * positive) :
  vs_wr (rw_slot hd ty sec buf sts bs kq)
  = (if bv_unsigned ty =? virtio_blk_t_out
     then Some (bv_unsigned sec * 512, bs) else None).
Proof. reflexivity. Qed.

Lemma bv16_small (k : nat) : (k < 8)%nat -> bv_unsigned (Z_to_bv 16 (Z.of_nat k)) = Z.of_nat k.
Proof.
  intro Hk. apply Z_to_bv_small.
  assert (H2 : bv_modulus 16 = 65536) by (vm_compute; reflexivity).
  rewrite H2. lia.
Qed.

Lemma mk_pin_slot_ok
    (c : virtio_cfg) (p : nat) (pd : Arch.pa) (pin : gmap Arch.pa (bv 8))
    (hd md td : nat) (hops buf sts : Arch.pa) (ty : bv 32) (sec : bv 64)
    (bs : list (bv 8)) (kq : nat * positive) :
  vc_qnum c = Z_to_bv 32 8 ->
  vc_desc c = pd ->
  (hd < 8)%nat -> (md < 8)%nat -> (td < 8)%nat ->
  (* NO avail-ring premise: the cell is the LEASE's, not the pin's (finding
     5), so a publisher owes nothing about it here. *)
  (* desc[hd] : the 16-byte header, chained *)
  desc_reads pin pd hd (hops : bv 64) (Z_to_bv 32 16) (Z_to_bv 16 1)
             (Z_to_bv 16 (Z.of_nat md)) ->
  (* desc[md] : the 1024-byte data buffer, chained; direction bit free *)
  desc_reads pin pd md (buf : bv 64) (Z_to_bv 32 1024)
             (Z_to_bv 16 (if bv_unsigned ty =? virtio_blk_t_out then 1 else 3))
             (Z_to_bv 16 (Z.of_nat td)) ->
  (* desc[td] : the one status byte, device-writable, ends the chain *)
  desc_reads pin pd td (sts : bv 64) (Z_to_bv 32 1) (Z_to_bv 16 2)
             (Z_to_bv 16 0) ->
  (* the request header at [hops] *)
  read_bytes pin (hops : Arch.pa) 4 = Some ty ->
  read_bytes pin (pa_add hops 8) 8 = Some sec ->
  (* the type is one of the two block-request types *)
  (bv_unsigned ty = virtio_blk_t_in \/ bv_unsigned ty = virtio_blk_t_out) ->
  (* a WRITE additionally pins its payload *)
  (bv_unsigned ty = virtio_blk_t_out -> read_byte_list pin buf 1024 = Some bs) ->
  (* the status byte is in [struct disk], the buffer in a [struct buf]: the
     device's status write never lands inside the data it is filling in *)
  sts ∉ pa_range buf 1024 ->
  slot_pin_ok c p (rw_slot hd ty sec buf sts bs kq) pin.
Proof.
  intros Hq Hc Hh Hm Ht Hdh Hdm Hdt Hty Hsec Htyv Hout Hstat.
  (* the two flag computations *)
  assert (Hf1 : vd_has (VqDesc (hops : bv 64) (Z_to_bv 32 16) (Z_to_bv 16 1)
                          (Z_to_bv 16 (Z.of_nat md))) vring_desc_f_next = true)
    by (vm_compute; reflexivity).
  assert (Hf2 : forall (a : bv 64) (l : bv 32) (n : bv 16),
            vd_has (VqDesc a l (Z_to_bv 16 (if bv_unsigned ty =? virtio_blk_t_out
                                            then 1 else 3)) n)
                   vring_desc_f_next = true).
  { intros a l n. unfold vd_has, vring_desc_f_next. cbn [vd_flags].
    destruct (bv_unsigned ty =? virtio_blk_t_out); vm_compute; reflexivity. }
  assert (Hf3 : forall (a : bv 64) (l : bv 32) (n : bv 16),
            vd_has (VqDesc a l (Z_to_bv 16 2) n) vring_desc_f_next = false)
    by (intros; vm_compute; reflexivity).
  constructor.
  (* NO [spo_ring]: the avail-ring cell belongs to the LEASE now, not to the
     request's pin (finding 5).  The device reads it at the pop, out of the
     invariant's own cell ([VirtioQueue.vpo_ring]), so a published chain owes
     nothing about it -- which is exactly what frees the in-flight positions
     from having to be an interval. *)
  - (* spo_type *) cbn [rw_slot vs_req vr_type]. exact Htyv.
  - (* spo_len *) cbn [rw_slot vs_req vr_len]. vm_compute. reflexivity.
  - (* spo_out *) intro Hoo. unfold vs_is_out in Hoo. cbn [rw_slot vs_req vr_type] in Hoo.
    cbn [rw_slot vs_req vr_buf vs_data].
    apply Hout. apply Z.eqb_eq. exact Hoo.
  - (* spo_stat *) intros _.
    unfold rw_slot, vs_len. cbn [vs_req vr_status vr_buf vr_len].
    assert (H1024 : Z.to_nat (bv_unsigned (Z_to_bv 32 1024)) = 1024%nat)
      by (vm_compute; reflexivity).
    rewrite H1024. exact Hstat.
  - (* spo_req: the chain parses *)
    intros mv Hv.
    pose proof (desc_at_of_reads c mv pin pd hd _ _ _ _ Hc Hv Hdh) as Dh.
    pose proof (desc_at_of_reads c mv pin pd md _ _ _ _ Hc Hv Hdm) as Dm.
    pose proof (desc_at_of_reads c mv pin pd td _ _ _ _ Hc Hv Hdt) as Dt.
    assert (Hqn : bv_unsigned (vc_qnum c) = 8)
      by (rewrite Hq; vm_compute; reflexivity).
    (* NO RING LOOKUP: the chain is read from the HEAD the slot names, which
       for an [rw_slot] is [hd] itself. *)
    unfold req_from, chain_from. cbv zeta.
    cbn [rw_slot vs_hd vs_req vr_head].
    rewrite Hqn.
    rewrite (bv16_small hd Hh).
    assert (Hlth : (Z.of_nat hd <? 8) = true) by (apply Z.ltb_lt; lia).
    rewrite Hlth. cbn [negb].
    rewrite Dh. rewrite Hf1. cbn [negb vd_next].
    rewrite (bv16_small md Hm).
    assert (Hltm : (Z.of_nat md <? 8) = true) by (apply Z.ltb_lt; lia).
    rewrite Hltm. cbn [negb].
    rewrite Dm. rewrite Hf2. cbn [negb vd_next].
    rewrite (bv16_small td Ht).
    assert (Hltt : (Z.of_nat td <? 8) = true) by (apply Z.ltb_lt; lia).
    rewrite Hltt. cbn [negb].
    rewrite Dt. rewrite Hf3.
    cbn [vd_addr vd_len].
    rewrite (view_word_read pin mv (hops : Arch.pa) 4 ty Hv Hty).
    assert (Hoff : pa_off (hops : Arch.pa) 8 = pa_add hops 8%nat)
      by (unfold pa_off; f_equal).
    rewrite Hoff.
    rewrite (view_word_read pin mv (pa_add hops 8%nat) 8 sec Hv Hsec).
    reflexivity.
  - (* spo_desc: the head descriptor's own bytes are pinned, which is what
       makes the head EXCLUSIVE to this chain (VirtioQueue.vproto_hd_fresh) *)
    cbn [rw_slot vs_hd vs_req vr_head].
    rewrite (bv16_small hd Hh).
    assert (Hbase : pa_off (vc_desc c) (vq_desc_size * Z.of_nat hd)
                    = d_desc pd hd).
    { rewrite Hc. unfold pa_off, d_desc, vq_desc_size, pa_add.
      f_equal. lia. }
    rewrite Hbase.
    destruct Hdh as (Ha & _ & _ & _).
    apply (read_bytes_dom_sub pin (d_desc pd hd) 8 _ Ha).
    apply pa_range_base. change (N.to_nat 8) with 8%nat. lia.
  - (* spo_hd: a head is a descriptor index, so under eight -- which is what
       bounds the outstanding requests and hence the unread used records *)
    cbn [rw_slot vs_hd vs_req vr_head].
    rewrite (bv16_small hd Hh). lia.
Qed.
