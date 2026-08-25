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

Section DiskInv.
  Context `{!riscvGS Σ, !xv6G Σ}.

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

  (* everything a FREE descriptor slot owns *)
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

  (* published, not yet processed by the interrupt handler.

     NOTHING here is existential any more: buffer, slot and pin all come out
     of the position's [dclaim] value, so a woken publisher's claim fragment
     pins exactly the request IT published. *)
  Definition flight_res (γ : disk_names) (p : nat) (v : dclaim) : iProp Σ :=
    (⌜slot_buf_link (dc_slot v) (dc_buf v)⌝ ∗
     disk_receipt γ p (dc_slot v) (dc_pin v) ∗
     b_disk (dc_buf v) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 1) ∗
     d_info_b (sl_head (dc_slot v)) ↦₈ (dc_buf v : SailStdpp.Values.mword 64))%I.

  (* processed by the interrupt handler, not yet collected by its publisher:
     the payoff of VirtioProto.virtio_proto_reclaim_acc, parked.  The pin
     comes back WHOLE now (finding 5): it never held an avail-ring entry to
     begin with, so there is nothing for the handler to split off and
     nothing a later publisher of ring slot [p mod 8] could have to reach
     into an uncollected payoff for.  [dc_ring_map] and [dc_pinr] are gone
     with that step. *)
  Definition parked_res (γ : disk_names) (pav : Arch.pa) (p : nat)
      (v : dclaim) : iProp Σ :=
    (∃ bs : list (bv 8),
       ⌜slot_buf_link (dc_slot v) (dc_buf v)⌝ ∗
       ⌜length bs = vs_len (dc_slot v)⌝ ∗
       ⌜bs = vs_data (dc_slot v)⌝ ∗
       b_disk (dc_buf v) ↦₄ (SailStdpp.Values.mword_of_int (len := 32) 0) ∗
       d_info_b (sl_head (dc_slot v)) ↦₈ (dc_buf v : SailStdpp.Values.mword 64) ∗
       phys_map (dc_pin v) ∗
       phys_pointsto (vr_status (vs_req (dc_slot v))) (DfracOwn 1) byte_zero ∗
       disk_bytes γ (vs_sector_off (dc_slot v)) bs ∗
       (* THE SPENT CRASH PERMIT's token (PermInv.v).  It is named at the
          CLAIM's own slot, so a woken publisher -- whose claim fragment pins
          [dc_slot v], hence [vs_perm (dc_slot v)] -- gets it back at exactly
          the key IT deposited, and can therefore match the invariant's
          receipt against its own saved proposition.  An existential key here
          would come back opaque and no receipt could ever be collected (the
          [vs_data] rule, one layer up).  ONE token, not one per sector: the
          request's whole obligation is a single SEQUENTIAL permit whose cell
          was re-indexed at each landing and spent at the completion
          (sector-atomic-disk.md §6e). *)
       slot_perms_done γ (dc_slot v) ∗
       (if vs_is_out (dc_slot v) then emp
        else phys_list (vr_buf (vs_req (dc_slot v))) bs))%I.


  (* -- descriptor-triple bookkeeping ------------------------------------ *)

  (* Each published-but-unfreed chain uses exactly three descriptors.  The
     triples are recorded (pure) per position so a PUBLISHER can bound the
     live window: at publish it holds a fourth disjoint triple, and
     4 * 3 > 8 forces |flight ∪ parked| <= 1 -- which is what makes its
     avail-ring slot [np mod 8] provably unclaimed. *)
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

  Definition disk_res (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64) : iProp Σ :=
    (∃ (np nr : nat) (fl pk : gmap nat dclaim)
       (tr : gmap nat (nat * nat * nat)) (fr : nat -> bool),
       (* THE WINDOW BOOKKEEPING, no longer an interval.  The device may
          complete in any order, so the positions still in flight after [nr]
          reclaims are SOME [np - nr] of [0, np), not the top [np - nr] of it.
          What the publisher actually needed from the old interval clause was
          only these two facts -- that [np] itself is fresh, and how many
          positions are live -- and both survive reordering. *)
       ⌜forall p, p ∈ dom fl -> (p < np)%nat⌝ ∗
       ⌜size fl = (np - nr)%nat⌝ ∗
       (* a PARKED position is one whose record was reclaimed but whose claim
          its sleeping publisher has not yet picked up.  It is below [np] like
          any other live position; being below [nr] is what it no longer is. *)
       ⌜forall p, p ∈ dom pk -> (p < np)%nat⌝ ∗
       (* ...and the two are disjoint, which the interval clause used to give
          for free (flight at or above [nr], parked below it) *)
       ⌜dom fl ## dom pk⌝ ∗
       (* descriptor triples: one per live position, well formed, pairwise
          disjoint, and none of their members is marked free *)
       ⌜dom tr = dom fl ∪ dom pk⌝ ∗
       (* the triple map AGREES with the claims: this is what lets a woken
          publisher read "my three descriptors are still allocated" off the
          sixth conjunct below, using only its claim fragment. *)
       ⌜forall p v, (fl ∪ pk) !! p = Some v -> tr !! p = Some (dc_tri v)⌝ ∗
       ⌜forall p T, tr !! p = Some T -> tri_ok T⌝ ∗
       ⌜forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
          tri_set Tp ## tri_set Tq⌝ ∗
       ⌜forall p T i, tr !! p = Some T -> i ∈ tri_set T -> fr i = false⌝ ∗
       (* the protocol tokens *)
       disk_pub γ np ∗
       disk_done_lb γ nr ∗
       (* THE READ WATERMARK, exactly: [nr] is how far the handler has walked
          the used ring, and [d_used_idx] below is the driver's own copy of
          it.  Reclaiming a record REQUIRES this half at that record's index
          ([VirtioProto.virtio_proto_reclaim_acc]), which is what forces the
          handler to drain in order (finding 5). *)
       disk_read_at γ nr ∗
       (* NOTHING IS HALF-PUBLISHED while the lock is free: a publisher sets
          the staged head at its ring store and spends it at the index bump,
          both under [vdisk_lock]. *)
       disk_stage γ None ∗
       ghost_map_auth (dn_claim γ) 1 (fl ∪ pk) ∗
       (* driver counters and cells *)
       d_used_idx ↦₂ wrap16 nr ∗
       ([∗ map] p ↦ v ∈ fl, flight_res γ p v) ∗
       ([∗ map] p ↦ v ∈ pk, parked_res γ pav p v) ∗
       (* free descriptors *)
       ([∗ list] i ∈ seq 0 8,
          d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
          (if fr i then free_slot_res pd i else emp)))%I.
       (* the free-descriptor pool is the LAST conjunct now: the avail-ring
          cells that used to follow it are the lease's (finding 5). *)

  (* the publisher's claim on its own position *)
  Definition disk_claim (γ : disk_names) (p : nat) (v : dclaim) : iProp Σ :=
    p ↪[dn_claim γ] v.

  (* a claim locates its position in the live window and pins its value *)
  Lemma disk_claim_agree (γ : disk_names) (p : nat) (v : dclaim)
      (fl pk : gmap nat dclaim) :
    ghost_map_auth (dn_claim γ) 1 (fl ∪ pk) -∗ disk_claim γ p v -∗
    ⌜fl !! p = Some v \/ (fl !! p = None /\ pk !! p = Some v)⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (ghost_map_lookup with "Hauth Hfrag") as %Hl.
    iPureIntro. apply lookup_union_Some_raw in Hl. exact Hl.
  Qed.

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

  Lemma mem_win_to_phys (p : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8) :
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add p j)) KP_rw) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 n, (pa_add p j) ↦ₘ{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, phys_pointsto (pa_add p j) dq (f j)).
  Proof.
    iIntros (Hstat) "#Hb Hbytes".
    iApply (big_sepL_impl with "Hbytes").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
    iApply (mem_ident_phys (pa_add p (0 + k)%nat) dq (f (0 + k)%nat)
              (Hstat (0 + k)%nat ltac:(lia)) with "Hb H").
  Qed.

  Lemma phys_win_to_mem (p : Arch.pa) (n : nat) (dq : dfrac) (f : nat -> bv 8) :
    (forall j, (j < n)%nat -> kmap_static (svpn_of (pa_add p j)) KP_rw) ->
    (forall j, (j < n)%nat ->
       (uint (pa_add p j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗
    ([∗ list] j ∈ seq 0 n, phys_pointsto (pa_add p j) dq (f j)) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add p j) ↦ₘ{dq} f j).
  Proof.
    iIntros (Hstat Hcan) "#Hb Hbytes".
    iApply (big_sepL_impl with "Hbytes").
    iIntros "!>" (k x Hk) "H".
    apply lookup_seq in Hk. destruct Hk as [-> Hlt].
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
    iApply (mem_canonical with "Hb").
  Qed.

  (* ---- the WORD-granular bridges, both directions.  These are the ones
     the driver actually uses: it formats the descriptors with sd/sw/sh into
     [↦₈]/[↦₄]/[↦₂] and must hand the protocol [phys_word*]/[phys_pointsto]
     byte windows; the reclaimed payoff travels the other way.  The
     alignment premise is discharged at the call site from
     [virtio_pages_aligned] (or from the [↦₂]/[↦₄]/[↦₈] itself in the
     to-phys direction, where it is already carried). ---- *)

  Lemma word2_to_phys (a : Arch.pa) (w : bv 16) :
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₂ w -∗ phys_word2 a w.
  Proof.
    iIntros (Hs) "#Hb [_ Hbytes]". rewrite /phys_word2.
    iApply (mem_win_to_phys a 2 (DfracOwn 1) (fun j => nth_byte w j) Hs
              with "Hb Hbytes").
  Qed.

  Lemma phys_to_word2 (a : Arch.pa) (w : bv 16) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    (forall j, (j < 2)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 2)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_word2 a w -∗ a ↦₂ w.
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
    iIntros (Hs) "#Hb [_ Hbytes]". rewrite /phys_word4.
    iApply (mem_win_to_phys a 4 (DfracOwn 1) (fun j => nth_byte w j) Hs
              with "Hb Hbytes").
  Qed.

  Lemma phys_to_word4 (a : Arch.pa) (w : bv 32) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    (forall j, (j < 4)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 4)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_word4 a w -∗ a ↦₄ w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb Hbytes". rewrite /phys_word4.
    iDestruct (phys_win_to_mem a 4 (DfracOwn 1) (fun j => nth_byte w j) Hs Hc
                 with "Hb Hbytes") as "Hm".
    rewrite /word4_pointsto. iFrame "Hm". iPureIntro. exact Hal.
  Qed.

  (* the doubleword has no [phys_word8] in VirtioProto, so it bridges to the
     bare byte window (the same shape [phys_map]/[phys_list] consume) *)
  Definition phys_word8 (a : Arch.pa) (w : bv 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 8, phys_pointsto (pa_add a j) (DfracOwn 1) (nth_byte w j))%I.

  Lemma word8_to_phys (a : Arch.pa) (w : bv 64) :
    (forall j, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    kmap_static_claims -∗ a ↦₈ w -∗ phys_word8 a w.
  Proof.
    iIntros (Hs) "#Hb [_ Hbytes]". rewrite /phys_word8.
    iApply (mem_win_to_phys a 8 (DfracOwn 1) (fun j => nth_byte w j) Hs
              with "Hb Hbytes").
  Qed.

  Lemma phys_to_word8 (a : Arch.pa) (w : bv 64) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    (forall j, (j < 8)%nat -> kmap_static (svpn_of (pa_add a j)) KP_rw) ->
    (forall j, (j < 8)%nat ->
       (uint (pa_add a j : SailStdpp.Values.mword 64) < 274877906944)%Z) ->
    kmap_static_claims -∗ phys_word8 a w -∗ a ↦₈ w.
  Proof.
    iIntros (Hal Hs Hc) "#Hb Hbytes". rewrite /phys_word8.
    iDestruct (phys_win_to_mem a 8 (DfracOwn 1) (fun j => nth_byte w j) Hs Hc
                 with "Hb Hbytes") as "Hm".
    rewrite /word_pointsto. iFrame "Hm". iPureIntro. exact Hal.
  Qed.

  (* the single byte, for the status cell *)
  Lemma byte_to_phys (a : Arch.pa) (b : bv 8) :
    kmap_static (svpn_of a) KP_rw ->
    kmap_static_claims -∗ a ↦ₘ b -∗ phys_pointsto a (DfracOwn 1) b.
  Proof. iIntros (Hs) "#Hb H". iApply (mem_ident_phys a (DfracOwn 1) b Hs with "Hb H"). Qed.

  Lemma phys_to_byte (a : Arch.pa) (b : bv 8) :
    kmap_static (svpn_of a) KP_rw ->
    (uint (a : SailStdpp.Values.mword 64) < 274877906944)%Z ->
    kmap_static_claims -∗ phys_pointsto a (DfracOwn 1) b -∗ a ↦ₘ b.
  Proof.
    iIntros (Hs Hc) "#Hb H".
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
  Definition free_bundles (pd : Arch.pa) (fr : nat -> bool) : iProp Σ :=
    ([∗ list] i ∈ seq 0 8,
       d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
       (if fr i then free_slot_res pd i else emp))%I.

  Lemma free_bundles_unfold (pd : Arch.pa) (fr : nat -> bool) :
    free_bundles pd fr ⊣⊢
    ([∗ list] i ∈ seq 0 8,
       d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
       (if fr i then free_slot_res pd i else emp)).
  Proof. reflexivity. Qed.

  Definition fr_upd (fr : nat -> bool) (i : nat) (b : bool) : nat -> bool :=
    fun k => if Nat.eq_dec k i then b else fr k.

  Lemma fr_upd_eq (fr : nat -> bool) (i : nat) (b : bool) : fr_upd fr i b i = b.
  Proof. unfold fr_upd. destruct (Nat.eq_dec i i); [reflexivity | congruence]. Qed.

  Lemma fr_upd_ne (fr : nat -> bool) (i k : nat) (b : bool) :
    k <> i -> fr_upd fr i b k = fr k.
  Proof. intro Hne. unfold fr_upd. destruct (Nat.eq_dec k i); [congruence|reflexivity]. Qed.

  (* the residual bundle, with slot [i] cut out *)
  Definition free_bundles_but (pd : Arch.pa) (fr : nat -> bool) (i : nat) : iProp Σ :=
    ([∗ list] k ∈ seq 0 8,
       if bool_decide (k = i) then emp
       else (d_free_cell k ↦ₘ (if fr k then Z_to_bv 8 1 else byte_zero) ∗
             (if fr k then free_slot_res pd k else emp)))%I.

  Lemma free_bundles_split (pd : Arch.pa) (fr : nat -> bool) (i : nat) :
    (i < 8)%nat ->
    free_bundles pd fr ⊣⊢
    (d_free_cell i ↦ₘ (if fr i then Z_to_bv 8 1 else byte_zero) ∗
     (if fr i then free_slot_res pd i else emp)) ∗
    free_bundles_but pd fr i.
  Proof.
    intro Hi. rewrite /free_bundles /free_bundles_but.
    apply (seq8_delete
             (fun k => d_free_cell k ↦ₘ (if fr k then Z_to_bv 8 1 else byte_zero) ∗
                       (if fr k then free_slot_res pd k else emp))%I i Hi).
  Qed.

  (* the residual does not see slot [i], so it survives any update there *)
  Lemma free_bundles_but_upd (pd : Arch.pa) (fr : nat -> bool) (i : nat) (b : bool) :
    free_bundles_but pd fr i ⊣⊢ free_bundles_but pd (fr_upd fr i b) i.
  Proof.
    rewrite /free_bundles_but. apply big_sepL_proper. intros k y Hk.
    apply lookup_seq in Hk as [-> _].
    case_bool_decide as Hd; [reflexivity|].
    rewrite (fr_upd_ne fr i (0 + k)%nat b Hd). reflexivity.
  Qed.

End DiskInv.

(* ====================================================================== *)
(* The descriptor-triple counting argument (pure).                        *)
(*                                                                        *)
(* A publisher holds a fourth, disjoint, well-formed triple while the      *)
(* lock is held, so 3 * (|live positions| + 1) <= 8 bounds the live        *)
(* window at one -- which is what makes its avail-ring slot [np mod 8]     *)
(* provably unclaimed (design/virtio-driver.md, the descriptor-triple  *)
(* window argument).                                                                                                          *)
(* ====================================================================== *)

Lemma tri_set_size (T : nat * nat * nat) : tri_ok T -> size (tri_set T) = 3%nat.
Proof.
  destruct T as [[a b] c]. unfold tri_ok, tri_set. cbn.
  intros (Hab & Hac & Hbc & _ & _ & _).
  rewrite size_union; [| set_solver].
  rewrite size_union; [| set_solver].
  rewrite !size_singleton. reflexivity.
Qed.

(* k pairwise-disjoint well-formed triples inside [X] need 3k elements *)
Lemma tri_card (tr : gmap nat (nat * nat * nat)) (X : gset nat) :
  (forall p T, tr !! p = Some T -> tri_ok T) ->
  (forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
     tri_set Tp ## tri_set Tq) ->
  (forall p T, tr !! p = Some T -> tri_set T ⊆ X) ->
  (3 * size tr <= size X)%nat.
Proof.
  revert X. induction tr as [|i T tr Hi IH] using map_ind;
    intros X Hok Hdisj Hsub.
  { rewrite map_size_empty. lia. }
  assert (HTok : tri_ok T)
    by (apply (Hok i); rewrite lookup_insert; reflexivity).
  assert (HTX : tri_set T ⊆ X)
    by (apply (Hsub i); rewrite lookup_insert; reflexivity).
  assert (Hne : forall p T', tr !! p = Some T' -> p <> i).
  { intros p T' Hp ->. rewrite Hi in Hp. discriminate. }
  assert (Hnei : forall p T', tr !! p = Some T' -> i <> p).
  { intros p T' Hp Hc. exact (Hne p T' Hp (eq_sym Hc)). }
  assert (Hother : forall p T', tr !! p = Some T' -> tri_set T' ## tri_set T).
  { intros p T' Hp. apply (Hdisj p i T' T (Hne p T' Hp)).
    - rewrite lookup_insert_ne; [exact Hp | exact (Hnei p T' Hp)].
    - rewrite lookup_insert; reflexivity. }
  assert (HIH : (3 * size tr <= size (X ∖ tri_set T))%nat).
  { apply IH.
    - intros p T' Hp. apply (Hok p).
      rewrite lookup_insert_ne; [exact Hp | exact (Hnei p T' Hp)].
    - intros p q Tp Tq Hpq Hp Hq. apply (Hdisj p q); [exact Hpq | | ].
      + rewrite lookup_insert_ne; [exact Hp | exact (Hnei p Tp Hp)].
      + rewrite lookup_insert_ne; [exact Hq | exact (Hnei q Tq Hq)].
    - intros p T' Hp. intros x Hx. apply elem_of_difference. split.
      + apply (Hsub p T'); [| exact Hx].
        rewrite lookup_insert_ne; [exact Hp | exact (Hnei p T' Hp)].
      + intro Hc.
        exact (proj1 (elem_of_disjoint _ _) (Hother p T' Hp) x Hx Hc). }
  rewrite map_size_insert_None; [| exact Hi].
  rewrite size_difference in HIH; [| exact HTX].
  rewrite (tri_set_size T HTok) in HIH.
  pose proof (subseteq_size _ _ HTX) as Hle.
  rewrite (tri_set_size T HTok) in Hle. lia.
Qed.

(* eight descriptors, three per chain: at most two live chains *)
Lemma tri_card_8 (tr : gmap nat (nat * nat * nat)) :
  (forall p T, tr !! p = Some T -> tri_ok T) ->
  (forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
     tri_set Tp ## tri_set Tq) ->
  (size tr <= 2)%nat.
Proof.
  intros Hok Hdisj.
  pose proof (tri_card tr (set_seq 0 8) Hok Hdisj) as Hc.
  rewrite size_set_seq in Hc.
  assert (Hsub : forall p T, tr !! p = Some T -> tri_set T ⊆ set_seq 0 8).
  { intros p T Hp. pose proof (Hok p T Hp) as Hok'.
    destruct T as [[a b] c]. unfold tri_ok in Hok'. cbn in Hok'.
    destruct Hok' as (_ & _ & _ & Ha & Hb & Hcc).
    intros x Hx. unfold tri_set in Hx. cbn in Hx.
    rewrite !elem_of_union !elem_of_singleton in Hx.
    apply elem_of_set_seq.
    destruct Hx as [[->| ->]| ->]; lia. }
  specialize (Hc Hsub). lia.
Qed.

(* THE window bound: a lock holder about to publish position [np] owns a
   fourth triple disjoint from every recorded one, hence at most one
   position is live and [np - nr <= 1]. *)
Lemma disk_window_le {A : Type} (np nr : nat) (fl pk : gmap nat A)
    (tr : gmap nat (nat * nat * nat)) (T0 : nat * nat * nat) :
  (nr <= np)%nat ->
  (* the interval clause split in two when the completion order came free *)
  (forall p, p ∈ dom fl -> (p < np)%nat) ->
  size fl = (np - nr)%nat ->
  (forall p, p ∈ dom pk -> (p < np)%nat) ->
  dom tr = dom fl ∪ dom pk ->
  (forall p T, tr !! p = Some T -> tri_ok T) ->
  (forall p q Tp Tq, p <> q -> tr !! p = Some Tp -> tr !! q = Some Tq ->
     tri_set Tp ## tri_set Tq) ->
  tri_ok T0 ->
  (forall p T, tr !! p = Some T -> tri_set T ## tri_set T0) ->
  (np - nr <= 1)%nat.
Proof.
  intros Hnrnp Hfl Hcount Hpk Htr Hok Hdisj HT0 Hdisj0.
  assert (Hfresh : tr !! np = None).
  { destruct (tr !! np) as [T|] eqn:Hn; [| reflexivity]. exfalso.
    assert (Hin : np ∈ dom tr) by (apply elem_of_dom; eexists; exact Hn).
    rewrite Htr in Hin. apply elem_of_union in Hin as [Hin|Hin].
    - pose proof (Hfl np Hin). lia.
    - pose proof (Hpk np Hin). lia. }
  set (tr' := <[ np := T0 ]> tr).
  assert (Hok' : forall p T, tr' !! p = Some T -> tri_ok T).
  { intros p T Hp. subst tr'. destruct (decide (p = np)) as [->|Hne].
    - rewrite lookup_insert in Hp. injection Hp as <-. exact HT0.
    - rewrite (lookup_insert_ne tr np p T0 (not_eq_sym Hne)) in Hp. exact (Hok p T Hp). }
  assert (Hdisj' : forall p q Tp Tq, p <> q -> tr' !! p = Some Tp ->
            tr' !! q = Some Tq -> tri_set Tp ## tri_set Tq).
  { intros p q Tp Tq Hpq Hp Hq. subst tr'.
    destruct (decide (p = np)) as [->|Hpn]; destruct (decide (q = np)) as [->|Hqn].
    - congruence.
    - rewrite lookup_insert in Hp. injection Hp as <-.
      rewrite (lookup_insert_ne tr np q T0 (not_eq_sym Hqn)) in Hq.
      apply gset_disj_sym. exact (Hdisj0 q Tq Hq).
    - rewrite lookup_insert in Hq. injection Hq as <-.
      rewrite (lookup_insert_ne tr np p T0 (not_eq_sym Hpn)) in Hp.
      exact (Hdisj0 p Tp Hp).
    - rewrite (lookup_insert_ne tr np p T0 (not_eq_sym Hpn)) in Hp.
      rewrite (lookup_insert_ne tr np q T0 (not_eq_sym Hqn)) in Hq.
      exact (Hdisj p q Tp Tq Hpq Hp Hq). }
  pose proof (tri_card_8 tr' Hok' Hdisj') as Hsz.
  assert (Hsz' : (S (size tr) <= 2)%nat)
    by (subst tr'; rewrite map_size_insert_None in Hsz; [exact Hsz | exact Hfresh]).
  assert (Hsub2 : dom fl ⊆ dom tr) by (rewrite Htr; apply union_subseteq_l).
  pose proof (subseteq_size (dom fl) (dom tr) Hsub2) as Hdom.
  (* [size_dom] on both sides, as facts rather than rewrites: the two are
     different instances and a single [rewrite ... in] only takes one. *)
  pose proof (size_dom fl) as Hdf.
  pose proof (size_dom tr) as Hdt2.
  lia.
Qed.

(* [mod8_set_seq_fresh] is gone with them: it said the cell the publisher is
   about to write is not one of the flight positions' cells, which is now the
   device invariant's business ([VirtioQueue.vproto_ok_ring]). *)

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
