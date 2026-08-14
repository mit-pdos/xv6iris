(* ====================================================================== *)
(* DiskBoot.v -- THE BOOT SEAM of the virtio disk driver.                   *)
(*                                                                         *)
(* main() finishes the disk's bring-up with                                *)
(*                                                                         *)
(*     initlock(&disk.vdisk_lock, "virtio_disk")                           *)
(*                                                                         *)
(* i.e. a [newlock] whose resource is [DiskInv.disk_res] -- so somewhere    *)
(* between [virtio_disk_init]'s return and that [newlock] the whole of      *)
(* [disk_res] has to be ASSEMBLED, once, out of                             *)
(*                                                                         *)
(*   - [SpecVirtioDiskInit.vdi_post]'s device-side outputs: the publisher   *)
(*     token [disk_pub γ 0], the freshly-zeroed descriptor page, the        *)
(*     avail page's ring entries (bytes 4..4095 -- the flags+index words    *)
(*     went into the DMA lease), and the eight [disk.free[i]] bytes at 1;   *)
(*   - the BOOT TOKENS, which no callee produces: the [dn_claim] ghost-map  *)
(*     authority at ∅ and the persistent [disk_done_lb γ 0] (both minted    *)
(*     in [VirtioProto.disk_ghosts_alloc] and threaded through adequacy      *)
(*     into [SpecMain]'s precondition), plus the [struct disk] .bss cells   *)
(*     the loader zeroed and [virtio_disk_init] never touches:              *)
(*     [d_used_idx] and the eight [DiskInv.disk_slot_raw i] bundles         *)
(*     ([info[i].b], [info[i].status], [ops[i]]).                            *)
(*                                                                         *)
(* [disk_res_boot] is that assembly.  At boot every map in [disk_res] is    *)
(* empty ([np = nr = 0], [fl = pk = tr = ∅], every descriptor free), so     *)
(* all seven pure conjuncts are empty-domain facts and the two per-position *)
(* big-ops are [emp]; the work is entirely in the WORD-GRANULAR cells:      *)
(* [desc_entry_own] and the avail-ring halfwords have to be rebuilt out of  *)
(* the pages' BYTE windows, which is what [ByteBuf]'s chunking algebra plus *)
(* [DiskInv]'s in-page alignment lemmas are for.                            *)
(*                                                                         *)
(* WHY A SEPARATE FILE: the statement spans two vocabularies -- [disk_res] /*)
(* [d_free_cell] / [d_used_idx] (DiskInv.v) and [disk_free] as [vdi_post]   *)
(* spells it (SpecVirtioDiskInit.v) -- and needs ByteBuf.v, which sits      *)
(* above KallocInv and so must stay out of DiskInv's deliberately light      *)
(* Require chain.  Nothing here is a proof of a kernel function, so a       *)
(* SpecMain-level consumer reaches it without importing any [Proof*] file.  *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvPtsto.
Require Import ByteBuf.
Require Import PageGeom.
Require Import VirtioModel VirtioQueue DiskPtsto VirtioProto DiskInv.
Require Import SpecVirtioDiskInit.
Require Import Riscv.rv64d_types Riscv.rv64d.
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

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* every byte of a zero-valued word is the zero byte                       *)
(* ---------------------------------------------------------------------- *)
Lemma nth_byte_of_zero {m : N} (w : bv m) (j : nat) :
  bv_unsigned w = 0 -> nth_byte w j = byte_zero.
Proof.
  intro Hz. apply bv_eq.
  rewrite nth_byte_unsigned Hz Z.shiftr_0_l Zmod_0_l.
  assert (Hb : bv_unsigned byte_zero = 0) by (vm_compute; reflexivity).
  rewrite Hb. reflexivity.
Qed.

(* the two queue-page alignments, out of the frozen configuration's *)
Lemma init_cfg_pages_aligned (pd pav pu : Arch.pa) :
  virtio_pages_aligned (virtio_init_cfg pd pav pu) ->
  bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0
  /\ bv_unsigned (pav : SailStdpp.Values.mword 64) `mod` 4096 = 0.
Proof. intros (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* ...and how the caller GETS it: [vdi_post] hands out [page_valid] for the
   three pages, whose alignment half is the same fact spelled with Sail's
   [uint].  Stated here so no consumer has to walk into the [uint]-vs-
   [bv_unsigned] width trap (durable-notes) on its own. *)
Lemma init_cfg_pages_aligned_of_valid (pd pav pu : Arch.pa) :
  page_valid pd -> page_valid pav -> page_valid pu ->
  virtio_pages_aligned (virtio_init_cfg pd pav pu).
Proof.
  intros [Hd _] [Ha _] [Hu _].
  unfold page_aligned, PGSIZE in Hd, Ha, Hu.
  rewrite RiscvExtras.uint_unsigned in Hd.
  rewrite RiscvExtras.uint_unsigned in Ha.
  rewrite RiscvExtras.uint_unsigned in Hu.
  split_and!; [exact Hd | exact Ha | exact Hu].
Qed.

Section DiskBoot.
  Context `{!riscvGS Σ, !diskGhostG Σ}.

  (* ==================================================================== *)
  (* §1  ZEROED BYTE WINDOWS.                                             *)
  (*                                                                      *)
  (* [ByteBuf]'s algebra at the one naming function this file uses, with   *)
  (* the window length given as a LITERAL premise so the rewrites match    *)
  (* syntactically ([bb_split3]'s discipline).                             *)
  (* ==================================================================== *)

  Local Lemma zsplit (p : Arch.pa) (k n L : nat) :
    (k + n = L)%nat ->
    ([∗ list] j ∈ seq 0 L, pa_add p j ↦ₘ byte_zero)
    ⊣⊢ ([∗ list] j ∈ seq 0 k, pa_add p j ↦ₘ byte_zero) ∗
       ([∗ list] j ∈ seq 0 n, pa_add (pa_add p k) j ↦ₘ byte_zero).
  Proof. intros <-. exact (bb_split p k n (fun _ => byte_zero)). Qed.

  Local Lemma zchunk (p : Arch.pa) (k n L : nat) :
    (k * n = L)%nat ->
    ([∗ list] j ∈ seq 0 L, pa_add p j ↦ₘ byte_zero)
    ⊢ [∗ list] i ∈ seq 0 k,
        [∗ list] j ∈ seq 0 n, pa_add (pa_add p (i * n)) j ↦ₘ byte_zero.
  Proof.
    intros <-. iIntros "H".
    iDestruct (bb_chunk n k p (fun _ => byte_zero) with "H") as "H". iExact "H".
  Qed.

  (* offset normalisation: [pa_add_add] flattens a nest of [pa_add]s into ONE
     offset whose exact parenthesisation depends on the nesting order, so the
     closing step is this congruence plus [lia] rather than a [rewrite] of a
     hand-guessed sum. *)
  Local Lemma pa_add_eq (a : Arch.pa) (i j : nat) :
    (i = j)%nat -> pa_add a i = pa_add a j.
  Proof. intros ->. reflexivity. Qed.

  Local Lemma zshift (p : Arch.pa) (o n : nat) :
    ([∗ list] j ∈ seq o n, pa_add p j ↦ₘ byte_zero)
    ⊢ [∗ list] j ∈ seq 0 n, pa_add (pa_add p o) j ↦ₘ byte_zero.
  Proof.
    rewrite (bb_seq_shift (fun j => pa_add p j ↦ₘ byte_zero)%I o n).
    apply big_sepL_mono. intros i j Hj. apply lookup_seq in Hj as [-> _].
    rewrite pa_add_add. reflexivity.
  Qed.

  (* ...and the three word cells a zeroed window rebuilds *)
  Local Lemma zbytes_word8 (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, pa_add a j ↦ₘ byte_zero)
    ⊢ a ↦₈ (mword_of_int 0 : mword 64).
  Proof.
    intro Hal.
    assert (Hfg : forall j, (j < 8)%nat ->
              byte_zero = nth_byte (mword_of_int 0 : mword 64) j).
    { intros j _. symmetry. apply nth_byte_of_zero. vm_compute. reflexivity. }
    rewrite (bb_ext a 8 (fun _ => byte_zero)
               (fun j => nth_byte (mword_of_int 0 : mword 64) j) Hfg).
    apply (word_pointsto_intro a (DfracOwn 1) _ Hal).
  Qed.

  Local Lemma zbytes_word4 (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ byte_zero)
    ⊢ a ↦₄ (mword_of_int 0 : mword 32).
  Proof.
    intro Hal.
    assert (Hfg : forall j, (j < 4)%nat ->
              byte_zero = nth_byte (mword_of_int 0 : mword 32) j).
    { intros j _. symmetry. apply nth_byte_of_zero. vm_compute. reflexivity. }
    rewrite (bb_ext a 4 (fun _ => byte_zero)
               (fun j => nth_byte (mword_of_int 0 : mword 32) j) Hfg).
    apply (word4_pointsto_intro a (DfracOwn 1) _ Hal).
  Qed.

  Local Lemma zbytes_word2 (a : Arch.pa) :
    is_aligned_paddr (Physaddr a) 2 = true ->
    ([∗ list] j ∈ seq 0 2, pa_add a j ↦ₘ byte_zero)
    ⊢ a ↦₂ (mword_of_int 0 : mword 16).
  Proof.
    intro Hal.
    assert (Hfg : forall j, (j < 2)%nat ->
              byte_zero = nth_byte (mword_of_int 0 : mword 16) j).
    { intros j _. symmetry. apply nth_byte_of_zero. vm_compute. reflexivity. }
    rewrite (bb_ext a 2 (fun _ => byte_zero)
               (fun j => nth_byte (mword_of_int 0 : mword 16) j) Hfg).
    apply (word2_pointsto_intro a (DfracOwn 1) _ Hal).
  Qed.

  (* ==================================================================== *)
  (* §2  THE DESCRIPTOR PAGE -> the eight [desc_entry_own]s.               *)
  (* ==================================================================== *)

  Lemma desc_entry_of_zeros (pd : Arch.pa) (i : nat) :
    bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 -> (i < 8)%nat ->
    ([∗ list] j ∈ seq 0 16, pa_add (pa_add pd (i * 16)) j ↦ₘ byte_zero)
    ⊢ desc_entry_own pd i.
  Proof.
    intros Hm Hi.
    assert (Hc : (i * 16)%nat = (16 * i)%nat) by lia. rewrite Hc.
    assert (A1 : pa_add (pa_add pd (16 * i)) 8 = pa_add pd (16 * i + 8)%nat).
    { rewrite !pa_add_add. apply pa_add_eq. lia. }
    assert (A2 : pa_add (pa_add (pa_add pd (16 * i)) 8) 4
                 = pa_add pd (16 * i + 12)%nat).
    { rewrite !pa_add_add. apply pa_add_eq. lia. }
    assert (A3 : pa_add (pa_add (pa_add (pa_add pd (16 * i)) 8) 4) 2
                 = pa_add pd (16 * i + 14)%nat).
    { rewrite !pa_add_add. apply pa_add_eq. lia. }
    rewrite (zsplit (pa_add pd (16 * i)) 8 8 16 ltac:(lia)).
    rewrite (zsplit (pa_add (pa_add pd (16 * i)) 8) 4 4 8 ltac:(lia)).
    rewrite (zsplit (pa_add (pa_add (pa_add pd (16 * i)) 8) 4) 2 2 4 ltac:(lia)).
    rewrite A3 A2 A1.
    iIntros "(H8 & H4 & H2a & H2b)".
    rewrite /desc_entry_own /d_desc.
    iExists (mword_of_int 0 : mword 64), (mword_of_int 0 : mword 32),
            (mword_of_int 0 : mword 16), (mword_of_int 0 : mword 16).
    iSplitL "H8".
    { iApply (zbytes_word8 (pa_add pd (16 * i))
                (d_desc_aligned8 pd i Hm Hi)); iExact "H8". }
    iSplitL "H4".
    { iApply (zbytes_word4 (pa_add pd (16 * i + 8)%nat)
                (d_desc_len_aligned4 pd i Hm Hi)); iExact "H4". }
    iSplitL "H2a".
    { iApply (zbytes_word2 (pa_add pd (16 * i + 12)%nat)
                (d_desc_flags_aligned2 pd i Hm Hi)); iExact "H2a". }
    iApply (zbytes_word2 (pa_add pd (16 * i + 14)%nat)
              (d_desc_next_aligned2 pd i Hm Hi)); iExact "H2b".
  Qed.

  Lemma desc_page_entries (pd : Arch.pa) :
    bv_unsigned (pd : SailStdpp.Values.mword 64) `mod` 4096 = 0 ->
    ([∗ list] j ∈ seq 0 4096, pa_add pd j ↦ₘ byte_zero)
    ⊢ [∗ list] i ∈ seq 0 8, desc_entry_own pd i.
  Proof.
    intro Hm.
    rewrite (zsplit pd 128 3968 4096 ltac:(lia)).
    iIntros "[Hh _]".
    iDestruct (zchunk pd 8 16 128 ltac:(lia) with "Hh") as "Hc".
    iApply (big_sepL_mono with "Hc"). intros k y Hy.
    apply lookup_seq in Hy as [-> Hlt]. iIntros "H".
    iApply (desc_entry_of_zeros pd (0 + k) Hm ltac:(lia)); iExact "H".
  Qed.

  (* ==================================================================== *)
  (* §3  THE AVAIL PAGE -> the unclaimed ring cells.                       *)
  (* ==================================================================== *)

  (* no position is live at boot, so every ring cell is in the pool *)
  Local Lemma ring_slots_empty (pav : Arch.pa) :
    ([∗ list] j ∈ seq 0 8, ∃ w : mword 16, d_ring pav j ↦₂ w)
    ⊢ ring_slots_res pav ∅.
  Proof.
    rewrite /ring_slots_res. apply big_sepL_mono. intros k y Hy.
    rewrite (bool_decide_eq_false_2 (y ∈ (∅ : gset nat)) (not_elem_of_empty y)).
    reflexivity.
  Qed.

  Lemma avail_page_ring (pav : Arch.pa) :
    bv_unsigned (pav : SailStdpp.Values.mword 64) `mod` 4096 = 0 ->
    ([∗ list] j ∈ seq 4 4092, pa_add pav j ↦ₘ byte_zero)
    ⊢ ring_slots_res pav ∅.
  Proof.
    intro Hm. iIntros "H".
    iDestruct (zshift pav 4 4092 with "H") as "H".
    rewrite (zsplit (pa_add pav 4) 16 4076 4092 ltac:(lia)).
    iDestruct "H" as "[Hh _]".
    iDestruct (zchunk (pa_add pav 4) 8 2 16 ltac:(lia) with "Hh") as "Hc".
    iApply ring_slots_empty.
    iApply (big_sepL_mono with "Hc"). intros k y Hy.
    apply lookup_seq in Hy as [-> Hlt].
    assert (Ar : pa_add (pa_add pav 4) ((0 + k) * 2)%nat = d_ring pav (0 + k)).
    { rewrite pa_add_add. rewrite /d_ring. apply pa_add_eq. lia. }
    rewrite Ar. iIntros "H".
    iExists (mword_of_int 0 : mword 16).
    iApply (zbytes_word2 (d_ring pav (0 + k))
              (d_ring_aligned2 pav (0 + k) Hm ltac:(lia))); iExact "H".
  Qed.

  (* ==================================================================== *)
  (* §4  THE FREE-DESCRIPTOR BUNDLE.                                       *)
  (* ==================================================================== *)

  (* [vdi_post] names the eight [free[]] bytes off [SpecVirtioDiskInit]'s
     [disk_free]; [disk_res] names them [d_free_cell].  Same cells. *)
  Lemma disk_free_cell_eq (j : nat) :
    pa_add SpecVirtioDiskInit.disk_free j = d_free_cell j.
  Proof.
    rewrite /d_free_cell.
    assert (Hb : SpecVirtioDiskInit.disk_free = pa_add DiskInv.disk_base 24)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hb pa_add_add. reflexivity.
  Qed.

  Lemma free_slots_boot (pd : Arch.pa) :
    ([∗ list] i ∈ seq 0 8, desc_entry_own pd i) -∗
    ([∗ list] i ∈ seq 0 8, disk_slot_raw i) -∗
    ([∗ list] i ∈ seq 0 8, free_slot_res pd i).
  Proof.
    iIntros "Hd Hr".
    iAssert ([∗ list] i ∈ seq 0 8, desc_entry_own pd i ∗ disk_slot_raw i)%I
      with "[Hd Hr]" as "H".
    { rewrite big_sepL_sep. iFrame "Hd Hr". }
    iApply (big_sepL_mono with "H"). intros k y Hy.
    iIntros "H". rewrite free_slot_res_split. iExact "H".
  Qed.

  Lemma free_bundles_boot (pd : Arch.pa) :
    ([∗ list] j ∈ seq 0 8, pa_add SpecVirtioDiskInit.disk_free j ↦ₘ (Z_to_bv 8 1)) -∗
    ([∗ list] i ∈ seq 0 8, desc_entry_own pd i) -∗
    ([∗ list] i ∈ seq 0 8, disk_slot_raw i) -∗
    free_bundles pd (fun _ => true).
  Proof.
    iIntros "Hc Hd Hr".
    iDestruct (free_slots_boot pd with "Hd Hr") as "Hs".
    rewrite /free_bundles. cbn [andb].
    rewrite big_sepL_sep. iSplitL "Hc".
    - iApply (big_sepL_mono with "Hc"). intros k y Hy.
      rewrite disk_free_cell_eq. iIntros "$".
    - iExact "Hs".
  Qed.

  (* ==================================================================== *)
  (* §5  THE COMPOSITION.                                                  *)
  (* ==================================================================== *)

  Lemma disk_res_boot (γ : disk_names) (pd pav pu : SailStdpp.Values.mword 64) :
    virtio_pages_aligned (virtio_init_cfg pd pav pu) ->
    (* --- what [SpecVirtioDiskInit.vdi_post] hands its caller --- *)
    disk_pub γ 0%nat -∗
    ([∗ list] j ∈ seq 0 4096, pa_add pd j ↦ₘ byte_zero) -∗
    ([∗ list] j ∈ seq 4 4092, pa_add pav j ↦ₘ byte_zero) -∗
    ([∗ list] j ∈ seq 0 8, pa_add SpecVirtioDiskInit.disk_free j ↦ₘ (Z_to_bv 8 1)) -∗
    (* --- the boot tokens: [struct disk]'s untouched .bss cells... --- *)
    d_used_idx ↦₂ wrap16 0%nat -∗
    ([∗ list] i ∈ seq 0 8, disk_slot_raw i) -∗
    (* --- ...and the two ghosts [disk_ghosts_alloc] minted at power-on --- *)
    disk_done_lb γ 0%nat -∗
    ghost_map_auth (dn_claim γ) 1 (∅ : gmap nat dclaim) -∗
    disk_res γ pd pav pu.
  Proof.
    intro Hal. destruct (init_cfg_pages_aligned pd pav pu Hal) as [Hpd Hpav].
    iIntros "Hpub Hdesc Havail Hfree Huidx Hraw Hlb Hclaim".
    iDestruct (desc_page_entries pd Hpd with "Hdesc") as "Hde".
    iDestruct (avail_page_ring pav Hpav with "Havail") as "Hring".
    iDestruct (free_bundles_boot pd with "Hfree Hde Hraw") as "Hfb".
    assert (Hu : (∅ : gmap nat dclaim) ∪ ∅ = ∅)
      by (apply map_eq; intro k; rewrite lookup_union !lookup_empty; reflexivity).
    rewrite /disk_res.
    iExists 0%nat, 0%nat, ∅, ∅, ∅, (fun _ => true).
    rewrite Hu !dom_empty_L !big_sepM_empty.
    iSplitR.
    { iPureIntro. reflexivity. }
    iSplitR.
    { iPureIntro. intros p Hp. exfalso. exact (not_elem_of_empty p Hp). }
    iSplitR.
    { iPureIntro. set_solver. }
    iSplitR.
    { iPureIntro. intros p v Hp. rewrite lookup_empty in Hp. discriminate. }
    iSplitR.
    { iPureIntro. intros p T Hp. rewrite lookup_empty in Hp. discriminate. }
    iSplitR.
    { iPureIntro. intros p q Tp Tq _ Hp _. rewrite lookup_empty in Hp.
      discriminate. }
    iSplitR.
    { iPureIntro. intros p T i Hp _. rewrite lookup_empty in Hp. discriminate. }
    iFrame "Hpub Hlb Hclaim Huidx".
    assert (Hm8 : mod8 (∅ : gset nat) = ∅) by (rewrite /mod8; set_solver).
    rewrite Hm8.
    iFrame "Hfb Hring".
  Qed.

End DiskBoot.
