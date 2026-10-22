/-
MachCSL: translation at the SHARED kernel table, and in the `satp`-switch window -- the rules
that step through the model's step-7 compare and its retry loop (`update_and_write_pte`'s
`PTE_Update_Retry`, `translate_TLB_miss_retry`; fork commit 7 of `dongjaelee1/sail-riscv`).

* `swp_update_and_write_pte_kpt`: the hardware's `A`/`D` write-back on a kernel leaf, its two
  outcomes a choice of continuations (`∧`): `PTE_Update_Done p`, or `PTE_Update_Retry ()` with
  the reservation the failed compare left standing.  The compare can fail: the walk's racy read
  and the exclusive re-read may see different `A`/`D` variants of the leaf.
* `swp_translate_TLB_hit_kpt`: a hit on a cached kernel leaf; a failed compare falls into
  `translate_TLB_miss` at `satp`'s root, which the caller proves (the right conjunct).
* The miss (route R2 of the C3 design, owner ruling 2026-10-22, with S1: an exclusive read
  stamps its footprint's coherence floors): while the hart holds the reservation a failed
  compare left, its reads of the entry return the reserved value (`swp_read_pte_resv`,
  `swp_read_pte_exclusive_resv`), so the walk that follows reads the leaf exactly
  (`swp_pt_walk_kpt_resv`) and its compare succeeds (`swp_update_and_write_pte_kpt_resv`, no
  Retry).  The retry worker therefore walks at most twice: `swp_translate_TLB_miss_retry_kpt_resv`
  (any count), `swp_translate_TLB_miss_retry_kpt` (count `n + 1`), and `swp_translate_TLB_miss_kpt`
  (`translate_TLB_miss` = the worker at `pte_update_max_retries = 15 + 1`); the bound is never
  exhausted.  `swp_translateAddr_kpt` puts the lookup, the hit and the miss together.
* `satp`-switch window: `swp_translate_TLB_hit_kptE`, `swp_translate_TLB_miss_kptE` (no claim
  about the rest of the TLB) and `swp_translateAddr_via` (`translateAddr` with the hit and the
  miss as obligations, the hit's obligation given the miss's).
-/
import MachCSL.WpPtWalkOwn

noncomputable section

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ArchSem
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

variable {GF : BundledGFunctors.{0}} [MachGS GF]

/-! ## The hardware's `A`/`D` write-back -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `update_and_write_pte` on the kernel leaf `kLeaf ppn perm a d` that the walk
(or a cached entry) reported, the canonical entry at `addr` being
`kLeaf ppn perm a0 d0`.  Either nothing to do (`PTE_Update_Done none`, the
reservation untouched), or an exclusive re-read of the entry, which sees some
variant `kLeaf ppn perm a1 d1`, and the step-7 compare: equal, the conditional
write-back of the reported leaf with `A` (and `D`) set
(`PTE_Update_Done (some _)`, the reservation consumed) -- the left conjunct;
different, `PTE_Update_Retry ()`, the reservation on the variant read handed
to the caller -- the right conjunct.  The compare can fail: the walk's read
and the exclusive re-read may see different variants (`pteCell` pins a leaf
only up to `A`/`D`, and other harts' write-backs change them). -/
theorem swp_update_and_write_pte_kpt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64))
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (a d a0 d0 : BitVec 1)
    (hmem : (addr, kLeaf ppn perm a0 d0) ∈ t.entries 2) (u : Unit)
    (r0 : Option Resv) (Φ : Result (PTE_Update_Result 39 × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗ resvFragAny cpu r0 ∗
    ((confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (p : Option (BitVec 64)), ⌜pteOptVariant ppn perm p⌝ -∗ Φ (.Ok (.PTE_Update_Done p, u))) ∧
     (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (a1 d1 : BitVec 1), ⌜kLeaf ppn perm a1 d1 ≠ kLeaf ppn perm a d⌝ -∗
        resvFrag cpu (some (snapOf addr 8 (kLeaf ppn perm a1 d1))) false -∗
        Φ (.Ok (.PTE_Update_Retry (), u))))
    ⊢ swp cpu (update_and_write_pte39 (physaddr.Physaddr addr) (kLeaf ppn perm a d) acc u) Φ := by
  iintro ⟨HmConf, #Hkpt, Hctx, Hfrag, HΦ⟩
  icases kptOn_facts t M $$ Hkpt with %hfacts
  obtain ⟨-, -, hents, -⟩ := hfacts
  have hpl : accPlain acc := kernelAccess_plain acc hacc
  unfold update_and_write_pte39 update_and_write_pte
  reduce_closed_widths
  obtain ⟨o, hupd, ho⟩ := update_PTE_Bits_kLeaf ppn perm a d acc hpl TranslationStage.S_Stage
  rw [hupd]
  rcases ho with rfl | ⟨ap, dp, rfl⟩
  · swp_run 40
    icases HΦ with ⟨HΦ, -⟩
    iapply HΦ $$ HmConf Hctx %r0 Hfrag %none
    ipureintro; trivial
  · conf_cases HmConf
    swp_run 60
    conf_intro HmConf
    ihave HAU := kpt_exclReadAU t M addr _ hmem $$ Hkpt
    iapply swp_bind
    iapply (swp_read_pte_exclusive cpu dq c sie hok addr (hents _ hmem).1 (hents _ hmem).2 r0
      (fun w => iprop(⌜pteVariant (kLeaf ppn perm a0 d0) w⌝ ∗ resvFrag cpu (some (snapOf addr 8 w)) false)))
    iframe HmConf Hfrag
    isplitl [HAU]
    · iapply exclReadAU_wand addr 8 _ _ $$ HAU
      inext
      iintro %w %hw Hfrag
      iframe Hfrag
      ipureintro; exact hw
    inext
    iintro HmConf %w ⟨%hw, Hfrag⟩
    obtain ⟨a1, d1, rfl⟩ := pteVariant_of_kLeaf ppn perm a0 d0 hw
    by_cases heq : kLeaf ppn perm a1 d1 = kLeaf ppn perm a d
    · -- the compare succeeds: the conditional write-back of the walked leaf's new bits
      have hb : (kLeaf ppn perm a1 d1 != BitVec.setWidth (8 * 8) (kLeaf ppn perm a d)) = false := by
        rw [heq]; simp
      simp only [hb, Bool.false_eq_true, ite_false]
      swp_run 40
      ihave HW := kpt_exclWriteAU cpu t M addr _ hmem (kLeaf ppn perm a1 d1) (kLeaf ppn perm ap dp)
        (pteVariant_kLeaf ppn perm a0 d0 ap dp) $$ Hkpt
      iapply swp_bind
      iapply (swp_write_pte_conditional cpu dq c sie hok addr (kLeaf ppn perm a1 d1) (kLeaf ppn perm ap dp)
        (hents _ hmem).1 (hents _ hmem).2 emp)
      iframe HmConf Hfrag HW
      inext
      iintro HmConf Hfrag _
      swp_run 40
      ihave Hfrag := resvFragAny_of cpu none false $$ Hfrag
      icases HΦ with ⟨HΦ, -⟩
      iapply HΦ $$ HmConf Hctx %none Hfrag %(some (kLeaf ppn perm ap dp))
      ipureintro; exact ⟨ap, dp, rfl⟩
    · -- the compare fails: the caller walks again, the reservation standing
      have hb : (kLeaf ppn perm a1 d1 != BitVec.setWidth (8 * 8) (kLeaf ppn perm a d)) = true := by
        simpa using heq
      simp only [hb, ite_true]
      swp_run 40
      icases HΦ with ⟨-, HΦ⟩
      iapply HΦ $$ HmConf Hctx %a1 %d1 %heq Hfrag

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- A TLB hit on a mapped `vpn`: the permission check on the cached leaf,
the `A`/`D` write-back through the cached entry's address, the cached entry
refreshed if the write-back changed the leaf (the left conjunct).  If the
step-7 compare fails, the hit walks `root` (`translate_TLB_miss`), which is
the caller's to prove (the right conjunct): the TLB as it was, the
reservation the failed compare left standing handed over as `resvFragAny`. -/
theorem swp_translate_TLB_hit_kpt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (htlb : tlbOk t tlb) (root : BitVec 44) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (i : Nat) (ent : TLB_Entry) (hres : lookupRes t tlb vpn (some (i, ent)))
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps vpn addr ppn perm)
    (hperm : perm.allows acc = true) (u : Unit)
    (r0 : Option Resv) (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗ resvFragAny cpu r0 ∗
    Register.tlb ↦ᵣ[cpu] tlb ∗
    ((confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbOk t tlb'⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u))) ∧
     (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗ Register.tlb ↦ᵣ[cpu] tlb -∗
        swp cpu (translate_TLB_miss39 0#16 root vpn acc Privilege.Supervisor mxr do_sum u) Φ))
    ⊢ swp cpu (translate_TLB_hit39 0#16 root vpn acc Privilege.Supervisor mxr do_sum u i ent) Φ := by
  iintro ⟨HmConf, #Hkpt, Hctx, Hfrag, Htlb, HΦ⟩
  obtain ⟨rfl, hget, addr₁, ppn₁, perm₁, a, d, a', d', hw, rfl⟩ := hres
  obtain ⟨rfl, rfl, rfl⟩ := PTree.maps_walk_inj t vpn addr addr₁ ppn ppn₁ perm perm₁ a d hmaps hw
  have hmem := PTree.walk_mem_entries 2 t vpn _ _ hw
  unfold translate_TLB_hit39 translate_TLB_hit
  reduce_closed_widths
  swp_run 20
  rw [tlb_get_pte_tlbEntryOf]
  simp only [ext_of_kLeaf]
  iapply swp_bind
  iapply (swp_check_PTE_permission_kLeaf cpu acc hacc mxr do_sum ppn₁ perm₁ a' d' hperm)
  swp_run 20
  rw [pteAddr_tlbEntryOf, update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt cpu dq c sie hok hadue t M acc hacc addr₁ ppn₁ perm₁
    a' d' a d hmem u r0)
  iframe HmConf Hkpt Hctx Hfrag
  isplit
  · iintro HmConf Hctx %r Hfrag %p %hp
    icases HΦ with ⟨HΦ, -⟩
    rw [tlb_get_ppn_tlbEntryOf, tlb_get_pbmt_kLeaf]
    cases p with
    | none =>
      swp_run 20
      iapply HΦ $$ HmConf Hctx %r Hfrag %tlb Htlb
      ipureintro; exact htlb
    | some p =>
      obtain ⟨a2, d2, rfl⟩ := hp
      swp_run 20
      iapply HΦ $$ HmConf Hctx %r Hfrag %_ Htlb
      ipureintro
      exact tlbOk_setPte t tlb htlb (tlbHash vpn) (tlbHash_lt vpn) _ hget ppn₁ perm₁ a' d' a2 d2
        (tlb_get_pte_tlbEntryOf _ _ _ _ _)
  · iintro HmConf Hctx %a1 %d1 %_ Hfrag
    icases HΦ with ⟨-, HΦ⟩
    swp_run 20
    rw [translate_TLB_miss39_eq]
    ihave Hfrag := resvFragAny_of cpu _ false $$ Hfrag
    iapply HΦ $$ HmConf Hctx %_ Hfrag Htlb

/-! ## The entry under a held reservation

After a failed compare the hart still holds the reservation its exclusive read
took on the entry's head (nothing inside the translation releases it).  While
it is held, a read of those bytes by the hart, plain or exclusive, returns the
reserved value (`swp_sail_mem_read_plain_resv`, `swp_sail_mem_read_excl_resv`:
the reservation invariant `resvInv` and an exclusive read's coherence stamp).
So the walk that follows a failed compare reads the leaf exactly, and its
compare cannot fail. -/

set_option maxHeartbeats 4000000 in
set_option swp_run.memStop true in
/-- The physical read of an entry this hart holds reserved: the reserved value. -/
theorem swp_checked_mem_read_pte8_S_resv (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (w : BitVec (8 * 8)) (b : Bool)
    (Φ : Result ((BitVec (8 * 8)) × Unit) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu (some (snapOf pa 8 w)) b ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ resvFrag cpu (some (snapOf pa 8 w)) b -∗ Φ (.Ok (w, ())))
    ⊢ swp cpu (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) page_based_mem_type.PBMT_PMA
        Privilege.Supervisor (physaddr.Physaddr pa) 8 false false false false) Φ := by
  iintro ⟨HmConf, Hfrag, HΦ⟩
  unfold checked_mem_read
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  mem_iapply (swp_sail_mem_read_plain_resv cpu) rfl (by decide) w b
  iframe Hfrag
  inext
  iintro Hfrag
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf Hfrag

set_option maxHeartbeats 4000000 in
set_option swp_run.memStop true in
/-- `read_pte` of an entry this hart holds reserved: the reserved value. -/
theorem swp_read_pte_resv (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (w : BitVec (8 * 8)) (b : Bool)
    (Φ : Result (BitVec (8 * 8)) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu (some (snapOf pa 8 w)) b ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ resvFrag cpu (some (snapOf pa 8 w)) b -∗ Φ (.Ok w))
    ⊢ swp cpu (read_pte (physaddr.Physaddr pa) 8) Φ := by
  iintro ⟨HmConf, Hfrag, HΦ⟩
  unfold read_pte mem_read mem_read_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_read_pte8_S_resv cpu dq c sie hok pa hram hal w b)
  iframe HmConf Hfrag
  inext
  iintro HmConf Hfrag
  swp_run 20
  simp only [MemoryOpResult_drop_meta]
  iapply HΦ $$ HmConf Hfrag

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- The exclusive physical read of an entry this hart holds reserved: the
reserved value, the reservation taken again. -/
theorem swp_checked_mem_read_pte8_excl_S_resv (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (w : BitVec (8 * 8)) (b : Bool)
    (Φ : Result ((BitVec (8 * 8)) × Unit) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu (some (snapOf pa 8 w)) b ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ resvFrag cpu (some (snapOf pa 8 w)) false -∗ Φ (.Ok (w, ())))
    ⊢ swp cpu (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) page_based_mem_type.PBMT_PMA
        Privilege.Supervisor (physaddr.Physaddr pa) 8 false false true false) Φ := by
  iintro ⟨HmConf, Hfrag, HΦ⟩
  unfold checked_mem_read
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  mem_iapply (swp_sail_mem_read_excl_resv cpu) false rfl rfl (by decide) w b
  iframe Hfrag
  inext
  iintro Hfrag
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf Hfrag

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- `read_pte_exclusive` of an entry this hart holds reserved: the reserved
value, the reservation taken again. -/
theorem swp_read_pte_exclusive_resv (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (w : BitVec (8 * 8)) (b : Bool)
    (Φ : Result (BitVec (8 * 8)) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu (some (snapOf pa 8 w)) b ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ resvFrag cpu (some (snapOf pa 8 w)) false -∗ Φ (.Ok w))
    ⊢ swp cpu (read_pte_exclusive (physaddr.Physaddr pa) 8) Φ := by
  iintro ⟨HmConf, Hfrag, HΦ⟩
  unfold read_pte_exclusive mem_read mem_read_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_read_pte8_excl_S_resv cpu dq c sie hok pa hram hal w b)
  iframe HmConf Hfrag
  inext
  iintro HmConf Hfrag
  swp_run 20
  simp only [MemoryOpResult_drop_meta]
  iapply HΦ $$ HmConf Hfrag

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The three-level walk of the kernel page table for a `vpn` it maps, the
hart holding the reservation on the leaf's entry: the pointer entries are
read exactly, the leaf as reserved. -/
theorem swp_pt_walk_kpt_resv [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (t : PTree) (M : RegMapF (BitVec 64)) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps vpn addr ppn perm)
    (hperm : perm.allows acc = true) (u : Unit) (a1 d1 : BitVec 1)
    (Φ : Result (PTW_Output 39 × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗
    resvFrag cpu (some (snapOf addr 8 (kLeaf ppn perm a1 d1))) false ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        resvFrag cpu (some (snapOf addr 8 (kLeaf ppn perm a1 d1))) false -∗
        Φ (.Ok (kptWalkOut ppn (kLeaf ppn perm a1 d1) addr, u)))
    ⊢ swp cpu (pt_walk39 vpn acc Privilege.Supervisor mxr do_sum t.base 2 false u) Φ := by
  iintro ⟨HmConf, #Hkpt, Hctx, Hfrag, HΦ⟩
  unfold pt_walk39
  icases kptOn_facts t M $$ Hkpt with %hfacts
  obtain ⟨hwf, -, hents, -⟩ := hfacts
  obtain ⟨a, d, hw⟩ := hmaps
  obtain ⟨b1, b0, m2, m1, haddr, m0, -⟩ := PTree.walk_levels t vpn addr _ hwf hw
  have hnlp : pte_is_non_leaf (Mk_PTE_Flags ptrFlags) = true := nonLeaf_ptr
  -- level 2
  rw [pt_walk]
  delta Functions.pagesize_bits
  reduce_closed_widths
  swp_run 40
  reduce_closed_widths
  rw [vpnIdx_two']; erw [pteAddr_setWidth]
  icases kpt_readAU cpu t M _ _ m2 $$ [Hkpt Hctx] with ⟨Hctx, %K, %tsl, HK, HAU⟩
  · iframe Hctx; iexact Hkpt
  iapply swp_bind
  iapply (swp_read_pte cpu dq c sie hok (pteAddr t.base (vpnIdx vpn 2)) (hents _ m2).1 (hents _ m2).2 K tsl _)
  iframe HmConf HK HAU
  inext
  iintro HmConf %w %hw2
  have hw2' : w = kPtr b1 := by
    rcases hw2 with h | ⟨_, _, _, _, _, _, h1, _⟩
    · exact h
    · exact absurd h1 (kPtr_ne_kLeaf _ _ _ _ _)
  subst hw2'
  swp_run 40
  simp only [flags_of_kPtr', ext_of_kPtr, ppn_of_kPtr]
  iapply swp_bind
  iapply (swp_pte_is_invalid_kPtr cpu dq c b1)
  iframe HmConf
  iintro HmConf
  swp_run 40
  -- level 1
  rw [pt_walk]
  delta Functions.pagesize_bits
  reduce_closed_widths
  swp_run 40
  reduce_closed_widths
  rw [vpnIdx_one']; erw [pteAddr_setWidth]
  icases kpt_readAU cpu t M _ _ m1 $$ [Hkpt Hctx] with ⟨Hctx, %K1, %tsl1, HK, HAU⟩
  · iframe Hctx; iexact Hkpt
  iapply swp_bind
  iapply (swp_read_pte cpu dq c sie hok (pteAddr b1 (vpnIdx vpn 1)) (hents _ m1).1 (hents _ m1).2 K1 tsl1 _)
  iframe HmConf HK HAU
  inext
  iintro HmConf %w %hw1
  have hw1' : w = kPtr b0 := by
    rcases hw1 with h | ⟨_, _, _, _, _, _, h1, _⟩
    · exact h
    · exact absurd h1 (kPtr_ne_kLeaf _ _ _ _ _)
  subst hw1'
  swp_run 40
  simp only [flags_of_kPtr', ext_of_kPtr, ppn_of_kPtr]
  iapply swp_bind
  iapply (swp_pte_is_invalid_kPtr cpu dq c b0)
  iframe HmConf
  iintro HmConf
  swp_run 40
  -- level 0: the reserved leaf
  rw [pt_walk]
  delta Functions.pagesize_bits
  reduce_closed_widths
  swp_run 40
  reduce_closed_widths
  rw [vpnIdx_zero']; erw [pteAddr_setWidth]
  subst haddr
  iapply swp_bind
  iapply (swp_read_pte_resv cpu dq c sie hok (pteAddr b0 (vpnIdx vpn 0)) (hents _ m0).1 (hents _ m0).2
    (kLeaf ppn perm a1 d1) false)
  iframe HmConf Hfrag
  inext
  iintro HmConf Hfrag
  have hnl : pte_is_non_leaf (Mk_PTE_Flags (BitVec.extractLsb' 0 8 (kLeaf ppn perm a1 d1))) = false := by
    rw [flags_of_kLeaf']; exact nonLeaf_kLeaf perm a1 d1
  have hG : _get_PTE_Flags_G (Mk_PTE_Flags (BitVec.extractLsb' 0 8 (kLeaf ppn perm a1 d1))) = 0#1 := by
    rw [flags_of_kLeaf']; exact (kLeaf_flag_bits perm a1 d1).2.2.1
  swp_run 40
  simp only [ext_of_kLeaf]
  iapply swp_bind
  iapply (swp_pte_is_invalid_kLeaf cpu dq c ppn perm a1 d1)
  iframe HmConf
  iintro HmConf
  swp_run 40
  iapply swp_bind
  rw [check_leaf_pte39_eq]
  iapply (swp_check_leaf_pte_kLeaf cpu dq c vpn acc hacc mxr do_sum ppn perm a1 d1 hperm _ u)
  iframe HmConf
  inext
  iintro HmConf
  swp_run 40
  simp only [hG]
  swp_run 10
  rw [vpnIdx_zero']
  erw [pteAddr_setWidth]
  unfold kptWalkOut
  iapply HΦ $$ HmConf Hctx Hfrag

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `update_and_write_pte` on the kernel leaf `kLeaf ppn perm a1 d1` that this
hart holds reserved (the walk after a failed compare): nothing to do (the
reservation left standing), or the exclusive re-read returns the reserved
value, the compare succeeds, and the leaf is written back with `A` (and `D`)
set.  No `PTE_Update_Retry`. -/
theorem swp_update_and_write_pte_kpt_resv [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64))
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (a1 d1 a0 d0 : BitVec 1)
    (hmem : (addr, kLeaf ppn perm a0 d0) ∈ t.entries 2) (u : Unit)
    (Φ : Result (PTE_Update_Result 39 × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗
    resvFrag cpu (some (snapOf addr 8 (kLeaf ppn perm a1 d1))) false ∗
    (confCells cpu dq Privilege.Supervisor c -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (p : Option (BitVec 64)), ⌜pteOptVariant ppn perm p⌝ -∗ Φ (.Ok (.PTE_Update_Done p, u)))
    ⊢ swp cpu (update_and_write_pte39 (physaddr.Physaddr addr) (kLeaf ppn perm a1 d1) acc u) Φ := by
  iintro ⟨HmConf, #Hkpt, Hfrag, HΦ⟩
  icases kptOn_facts t M $$ Hkpt with %hfacts
  obtain ⟨-, -, hents, -⟩ := hfacts
  have hpl : accPlain acc := kernelAccess_plain acc hacc
  unfold update_and_write_pte39 update_and_write_pte
  reduce_closed_widths
  obtain ⟨o, hupd, ho⟩ := update_PTE_Bits_kLeaf ppn perm a1 d1 acc hpl TranslationStage.S_Stage
  rw [hupd]
  rcases ho with rfl | ⟨ap, dp, rfl⟩
  · swp_run 40
    ihave Hfrag := resvFragAny_of cpu _ false $$ Hfrag
    iapply HΦ $$ HmConf %_ Hfrag %none
    ipureintro; trivial
  · conf_cases HmConf
    swp_run 60
    conf_intro HmConf
    iapply swp_bind
    iapply (swp_read_pte_exclusive_resv cpu dq c sie hok addr (hents _ hmem).1 (hents _ hmem).2
      (kLeaf ppn perm a1 d1) false)
    iframe HmConf Hfrag
    inext
    iintro HmConf Hfrag
    -- the compare of the reserved value with itself
    have hb : (kLeaf ppn perm a1 d1 != BitVec.setWidth (8 * 8) (kLeaf ppn perm a1 d1)) = false := by simp
    simp only [hb, Bool.false_eq_true, ite_false]
    swp_run 40
    ihave HW := kpt_exclWriteAU cpu t M addr _ hmem (kLeaf ppn perm a1 d1) (kLeaf ppn perm ap dp)
      (pteVariant_kLeaf ppn perm a0 d0 ap dp) $$ Hkpt
    iapply swp_bind
    iapply (swp_write_pte_conditional cpu dq c sie hok addr (kLeaf ppn perm a1 d1) (kLeaf ppn perm ap dp)
      (hents _ hmem).1 (hents _ hmem).2 emp)
    iframe HmConf Hfrag HW
    inext
    iintro HmConf Hfrag _
    swp_run 40
    ihave Hfrag := resvFragAny_of cpu none false $$ Hfrag
    iapply HΦ $$ HmConf %none Hfrag %(some (kLeaf ppn perm ap dp))
    ipureintro; exact ⟨ap, dp, rfl⟩

/-! ## The kernel-table miss: the retry worker

`translate_TLB_miss` is the worker `translate_TLB_miss_retry` at
`pte_update_max_retries = 16`.  The first walk reads the leaf racily
(`swp_pt_walk_kpt`); if its compare fails, the worker recurses holding the
reservation on the value the exclusive read saw, and that walk's compare
succeeds (`swp_translate_TLB_miss_retry_kpt_resv`).  So at most two walks,
and the bound is never exhausted.  Both workers report the slot the miss
refilled: `vpn`'s, caching the leaf at some `A`/`D`. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The retry worker, at any count, the hart holding the reservation on the
leaf's entry: one walk, one write-back, the entry cached. -/
theorem swp_translate_TLB_miss_retry_kpt_resv [CurCtx] (n : Nat) (cpu : CPU) (dq : DFrac) (c : MConf)
    (sie : Bool) (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps vpn addr ppn perm)
    (hperm : perm.allows acc = true) (u : Unit) (a1 d1 : BitVec 1)
    (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗
    resvFrag cpu (some (snapOf addr 8 (kLeaf ppn perm a1 d1))) false ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (a d : BitVec 1), Register.tlb ↦ᵣ[cpu]
          (vectorUpdate tlb (tlbHash vpn) (some (tlbEntryOf 0#16 vpn ppn (kLeaf ppn perm a d) addr))) -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_miss_retry39 n 0#16 t.base vpn acc Privilege.Supervisor mxr do_sum u) Φ := by
  iintro ⟨HmConf, #Hkpt, Hctx, Hfrag, Htlb, HΦ⟩
  unfold translate_TLB_miss_retry39
  rw [translate_TLB_miss_retry]
  reduce_closed_widths
  swp_run 20
  rw [get_root_level_39, pt_walk39_eq]
  iapply swp_bind
  iapply (swp_pt_walk_kpt_resv cpu dq c sie hok t M vpn acc hacc mxr do_sum addr ppn perm hmaps hperm u a1 d1)
  iframe HmConf Hkpt Hctx Hfrag
  inext
  iintro HmConf Hctx Hfrag
  obtain ⟨a₀, d₀, hw⟩ := hmaps
  have hmem := PTree.walk_mem_entries 2 t vpn _ _ hw
  unfold kptWalkOut
  swp_run 20
  rw [update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt_resv cpu dq c sie hok hadue t M acc hacc addr ppn perm
    a1 d1 a₀ d₀ hmem u)
  iframe HmConf Hkpt Hfrag
  iintro HmConf %r Hfrag %p %hp
  cases p with
  | none =>
    swp_run 20
    rw [add_to_TLB39_eq]
    iapply swp_bind
    iapply (swp_add_to_TLB_kpt cpu tlb vpn ppn (kLeaf ppn perm a1 d1) addr)
    iframe Htlb
    inext
    iintro Htlb
    swp_run 20
    iapply HΦ $$ HmConf Hctx %r Hfrag %a1 %d1 Htlb
  | some p =>
    obtain ⟨a2, d2, rfl⟩ := hp
    swp_run 20
    rw [add_to_TLB39_eq]
    iapply swp_bind
    iapply (swp_add_to_TLB_kpt cpu tlb vpn ppn (kLeaf ppn perm a2 d2) addr)
    iframe Htlb
    inext
    iintro Htlb
    swp_run 20
    iapply HΦ $$ HmConf Hctx %r Hfrag %a2 %d2 Htlb

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The retry worker with at least one retry left: the racy walk, the
write-back; on a failed compare, the worker again, holding the reservation
(`swp_translate_TLB_miss_retry_kpt_resv`). -/
theorem swp_translate_TLB_miss_retry_kpt [CurCtx] (n : Nat) (cpu : CPU) (dq : DFrac) (c : MConf)
    (sie : Bool) (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps vpn addr ppn perm)
    (hperm : perm.allows acc = true) (u : Unit) (r0 : Option Resv)
    (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗
    resvFragAny cpu r0 ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (a d : BitVec 1), Register.tlb ↦ᵣ[cpu]
          (vectorUpdate tlb (tlbHash vpn) (some (tlbEntryOf 0#16 vpn ppn (kLeaf ppn perm a d) addr))) -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_miss_retry39 (n + 1) 0#16 t.base vpn acc Privilege.Supervisor mxr do_sum u) Φ := by
  iintro ⟨HmConf, #Hkpt, Hctx, Hfrag, Htlb, HΦ⟩
  unfold translate_TLB_miss_retry39
  rw [translate_TLB_miss_retry]
  reduce_closed_widths
  swp_run 20
  rw [get_root_level_39, pt_walk39_eq]
  iapply swp_bind
  iapply (swp_pt_walk_kpt cpu dq c sie hok t M vpn acc hacc mxr do_sum addr ppn perm hmaps hperm u)
  iframe HmConf Hkpt Hctx
  inext
  iintro HmConf Hctx %a %d
  have hmaps' := hmaps
  obtain ⟨a₀, d₀, hw⟩ := hmaps'
  have hmem := PTree.walk_mem_entries 2 t vpn _ _ hw
  unfold kptWalkOut
  swp_run 20
  rw [update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt cpu dq c sie hok hadue t M acc hacc addr ppn perm
    a d a₀ d₀ hmem u r0)
  iframe HmConf Hkpt Hctx Hfrag
  isplit
  · iintro HmConf Hctx %r Hfrag %p %hp
    cases p with
    | none =>
      swp_run 20
      rw [add_to_TLB39_eq]
      iapply swp_bind
      iapply (swp_add_to_TLB_kpt cpu tlb vpn ppn (kLeaf ppn perm a d) addr)
      iframe Htlb
      inext
      iintro Htlb
      swp_run 20
      iapply HΦ $$ HmConf Hctx %r Hfrag %a %d Htlb
    | some p =>
      obtain ⟨a2, d2, rfl⟩ := hp
      swp_run 20
      rw [add_to_TLB39_eq]
      iapply swp_bind
      iapply (swp_add_to_TLB_kpt cpu tlb vpn ppn (kLeaf ppn perm a2 d2) addr)
      iframe Htlb
      inext
      iintro Htlb
      swp_run 20
      iapply HΦ $$ HmConf Hctx %r Hfrag %a2 %d2 Htlb
  · -- the compare failed: walk again, the reservation held
    iintro HmConf Hctx %a1 %d1 %_ Hfrag
    swp_run 20
    have hpos : decide (n + 1 > 0) = true := by simp
    have hdec : ((((n + 1 : Nat) : Int) - 1).toNat) = n := by omega
    simp only [hpos, hdec, ite_true]
    rw [translate_TLB_miss_retry39_eq]
    iapply (swp_translate_TLB_miss_retry_kpt_resv n cpu dq c sie hok hadue t M tlb vpn acc hacc mxr do_sum
      addr ppn perm hmaps hperm u a1 d1)
    iframe HmConf Hkpt Hctx Hfrag Htlb HΦ

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- A TLB miss on a mapped `vpn`: the walk (again, after a failed compare),
the write-back, the entry cached. -/
theorem swp_translate_TLB_miss_kpt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (htlb : tlbOk t tlb) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps vpn addr ppn perm)
    (hperm : perm.allows acc = true) (u : Unit)
    (r0 : Option Resv) (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗ resvFragAny cpu r0 ∗
    Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbOk t tlb'⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_miss39 0#16 t.base vpn acc Privilege.Supervisor mxr do_sum u) Φ := by
  iintro ⟨HmConf, #Hkpt, Hctx, Hfrag, Htlb, HΦ⟩
  have hmaps' := hmaps
  obtain ⟨a₀, d₀, hw⟩ := hmaps'
  rw [translate_TLB_miss39_eq_retry, show pte_update_max_retries = 15 + 1 from rfl]
  iapply (swp_translate_TLB_miss_retry_kpt 15 cpu dq c sie hok hadue t M tlb vpn acc hacc mxr do_sum
    addr ppn perm hmaps hperm u r0)
  iframe HmConf Hkpt Hctx Hfrag Htlb
  iintro HmConf Hctx %r Hfrag %a %d Htlb
  iapply HΦ $$ HmConf Hctx %r Hfrag %_ Htlb
  ipureintro; exact tlbOk_write t tlb htlb vpn addr ppn perm a₀ d₀ a d hw

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- `translateAddr` at the kernel page table, for a canonical address whose
page the table maps with a permission allowing the access: the physical
address is the mapped page with the offset; the TLB may have been refilled
or refreshed; a reservation may be left standing. -/
theorem swp_translateAddr_kpt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool) (root : BitVec 44)
    (hok : SConfKpt (GF := GF) c root sie) (t : PTree) (M : RegMapF (BitVec 64)) (hbase : t.base = root)
    (tlb : Tlb) (htlb : tlbOk t tlb) (va : BitVec 64)
    (hcanon : BitVec.signExtend 64 (BitVec.extractLsb' 0 39 va) = va)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps (vpnOf va) addr ppn perm)
    (hperm : perm.allows acc = true)
    (r0 : Option Resv) (Φ : Result (physaddr × page_based_mem_type × Unit) (ExceptionContext × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗ resvFragAny cpu r0 ∗
    Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbOk t tlb'⌝ -∗
        Φ (.Ok (physaddr.Physaddr (BitVec.setWidth 64 (ppn ++ BitVec.extractLsb' 0 12 va)),
          page_based_mem_type.PBMT_PMA, ())))
    ⊢ swp cpu (translateAddr (virtaddr.Virtaddr va) acc Privilege.Supervisor) Φ := by
  iintro ⟨HmConf, #Hkpt, Hctx, Hfrag, Htlb, HΦ⟩
  conf_cases HmConf
  have hok0 := hok
  obtain ⟨⟨hpmp, hms, hpmm, hlpe⟩, hmode, hasid, hroot, hadue⟩ := hok
  obtain ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩ := hms
  have hok' : SConfPhys (GF := GF) c sie :=
    ⟨hpmp, ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩, hpmm, hlpe⟩
  subst hbase
  have hcanon' := canon_truncate va hcanon
  unfold translateAddr
  rw [is_shadow_stack_access_kernel acc hacc]
  swp_run 40
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_translationMode_kpt cpu dq c sie t.base hok0)
  iframe HmConf
  inext
  iintro HmConf
  conf_cases HmConf
  -- the Svukte check, then `translate_vs_stage` reads the mode again
  swp_run 120
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_translationMode_kpt cpu dq c sie t.base hok0)
  iframe HmConf
  inext
  iintro HmConf
  conf_cases HmConf
  swp_run 120
  reduce_closed_widths
  rw [extract_vpnOf, extract_offset_truncate, satp_to_asid_of c.satp hasid, satp_to_ppn_of c.satp t.base hroot]
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_lookup_TLB_kpt cpu t tlb htlb (vpnOf va))
  iframe Htlb
  inext
  iintro Htlb %r %hres
  cases r with
  | none =>
    -- the miss event (`generate_event`) reads the privilege
    conf_cases HmConf
    swp_run 10
    conf_intro HmConf
    rw [translate_TLB_miss39_eq]
    iapply swp_bind
    iapply (swp_translate_TLB_miss_kpt cpu dq c sie hok' hadue t M tlb htlb (vpnOf va) acc hacc _ _ addr ppn perm
      hmaps hperm _ r0)
    iframe HmConf Hkpt Hctx Hfrag Htlb
    iintro HmConf Hctx %r Hfrag %tlb' Htlb %htlb'
    swp_run 20
    iapply HΦ $$ HmConf Hctx %r Hfrag %tlb' Htlb
    ipureintro; exact htlb'
  | some ie =>
    obtain ⟨i, ent⟩ := ie
    swp_run 10
    rw [translate_TLB_hit39_eq]
    iapply swp_bind
    iapply (swp_translate_TLB_hit_kpt cpu dq c sie hok' hadue t M tlb htlb t.base (vpnOf va) acc hacc _ _ i ent
      hres addr ppn perm hmaps hperm _ r0)
    iframe HmConf Hkpt Hctx Hfrag Htlb
    isplit
    · iintro HmConf Hctx %r Hfrag %tlb' Htlb %htlb'
      swp_run 20
      iapply HΦ $$ HmConf Hctx %r Hfrag %tlb' Htlb
      ipureintro; exact htlb'
    · -- the compare failed: the miss walks the kernel table
      iintro HmConf Hctx %r Hfrag Htlb
      iapply (swp_translate_TLB_miss_kpt cpu dq c sie hok' hadue t M tlb htlb (vpnOf va) acc hacc _ _ addr ppn
        perm hmaps hperm _ r)
      iframe HmConf Hkpt Hctx Hfrag Htlb
      iintro HmConf Hctx %r' Hfrag %tlb' Htlb %htlb'
      swp_run 20
      iapply HΦ $$ HmConf Hctx %r' Hfrag %tlb' Htlb
      ipureintro; exact htlb'

/-! ## Translation with the hit and the miss as obligations

Between a `csrw satp` and the following `sfence.vma` the TLB holds entries
of two tables (Rocq `TransPt`): a hit may be on either table's entry, a miss
walks the table `satp` now names, and so does a hit whose step-7 compare
fails.  So the translation is proved here once, with what happens on a hit
(for each entry the lookup can answer) and on a miss as the caller's
obligations, over a resource `R`. -/

/-- The TLB after a translation of `vpn` that cached (or refreshed) a leaf
`kLeaf ppn perm _ _` at `addr`, the bits unknown. -/
def tlbAfterE (tlb tlb' : Tlb) (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm) (addr : BitVec 64) : Prop :=
  tlb' = tlb ∨ ∃ a d : BitVec 1,
    tlb' = vectorUpdate tlb (tlbHash vpn) (some (tlbEntryOf 0#16 vpn ppn (kLeaf ppn perm a d) addr))

theorem tlbAfter.E {tlb tlb' : Tlb} {vpn : BitVec 27} {ppn : BitVec 44} {perm : KPerm} {a d : BitVec 1}
    {addr : BitVec 64} (h : tlbAfter tlb tlb' vpn ppn perm a d addr) : tlbAfterE tlb tlb' vpn ppn perm addr := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨a, d, h⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **A TLB hit on an entry caching a leaf of the SHARED kernel table**
(`kptOn`), without any claim about the rest of the TLB: the write-back goes
through the kernel table's invariant; the entry may be refreshed (the left
conjunct).  If the step-7 compare fails, the hit walks `root`, which in the
`satp`-switch window may be either table's: that miss is the caller's to
prove (the right conjunct), with the TLB as it was and the token re-formed
around the reservation the failed compare left standing. -/
theorem swp_translate_TLB_hit_kptE [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (root : BitVec 44) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (i : Nat) (ent : TLB_Entry) (hi : i = tlbHash vpn) (hget : tlb[tlbHash vpn]'(tlbHash_lt vpn) = some ent)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (a d a' d' : BitVec 1)
    (hw : t.walk 2 vpn = some (addr, kLeaf ppn perm a d))
    (hent : ent = tlbEntryOf 0#16 vpn ppn (kLeaf ppn perm a' d') addr)
    (hperm : perm.allows acc = true) (u : Unit)
    (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ctxTok cpu curCtx ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    ((confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbAfterE tlb tlb' vpn ppn perm addr⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u))) ∧
     (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗ Register.tlb ↦ᵣ[cpu] tlb -∗
        swp cpu (translate_TLB_miss39 0#16 root vpn acc Privilege.Supervisor mxr do_sum u) Φ))
    ⊢ swp cpu (translate_TLB_hit39 0#16 root vpn acc Privilege.Supervisor mxr do_sum u i ent) Φ := by
  iintro ⟨HmConf, #Hkpt, Htok, Htlb, HΦ⟩
  icases ctxTok_cases cpu curCtx $$ Htok with ⟨Hctx, %r0, Hfrag⟩
  subst hent hi
  have hmem := PTree.walk_mem_entries 2 t vpn _ _ hw
  unfold translate_TLB_hit39 translate_TLB_hit
  reduce_closed_widths
  swp_run 20
  rw [tlb_get_pte_tlbEntryOf]
  simp only [ext_of_kLeaf]
  iapply swp_bind
  iapply (swp_check_PTE_permission_kLeaf cpu acc hacc mxr do_sum ppn perm a' d' hperm)
  swp_run 20
  rw [pteAddr_tlbEntryOf, update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt cpu dq c sie hok hadue t M acc hacc addr ppn perm
    a' d' a d hmem u r0)
  iframe HmConf Hkpt Hctx Hfrag
  isplit
  · iintro HmConf Hctx %r Hfrag %p %hp
    icases HΦ with ⟨HΦ, -⟩
    rw [tlb_get_ppn_tlbEntryOf, tlb_get_pbmt_kLeaf]
    cases p with
    | none =>
      swp_run 20
      iapply HΦ $$ HmConf [Hctx Hfrag] %tlb Htlb
      · iapply ctxTok_intro cpu curCtx r; iframe Hctx Hfrag
      · ipureintro; exact Or.inl rfl
    | some p =>
      obtain ⟨a2, d2, rfl⟩ := hp
      swp_run 20
      iapply HΦ $$ HmConf [Hctx Hfrag] %_ Htlb
      · iapply ctxTok_intro cpu curCtx r; iframe Hctx Hfrag
      · ipureintro
        right
        exact ⟨a2, d2, by rw [tlb_set_pte_tlbEntryOf]⟩
  · iintro HmConf Hctx %a1 %d1 %_ Hfrag
    icases HΦ with ⟨-, HΦ⟩
    swp_run 20
    rw [translate_TLB_miss39_eq]
    iapply HΦ $$ HmConf [Hctx Hfrag] Htlb
    iapply ctxTok_introB cpu curCtx _ false; iframe Hctx Hfrag

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **A TLB miss walking the SHARED kernel table**, without any claim about
the rest of the TLB: the walk (again, after a failed compare), the
write-back, the kernel entry cached. -/
theorem swp_translate_TLB_miss_kptE [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps vpn addr ppn perm)
    (hperm : perm.allows acc = true) (u : Unit)
    (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ctxTok cpu curCtx ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbAfterE tlb tlb' vpn ppn perm addr⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_miss39 0#16 t.base vpn acc Privilege.Supervisor mxr do_sum u) Φ := by
  iintro ⟨HmConf, #Hkpt, Htok, Htlb, HΦ⟩
  icases ctxTok_cases cpu curCtx $$ Htok with ⟨Hctx, %r0, Hfrag⟩
  rw [translate_TLB_miss39_eq_retry, show pte_update_max_retries = 15 + 1 from rfl]
  iapply (swp_translate_TLB_miss_retry_kpt 15 cpu dq c sie hok hadue t M tlb vpn acc hacc mxr do_sum
    addr ppn perm hmaps hperm u r0)
  iframe HmConf Hkpt Hctx Hfrag Htlb
  iintro HmConf Hctx %r Hfrag %a %d Htlb
  iapply HΦ $$ HmConf [Hctx Hfrag] %_ Htlb
  · iapply ctxTok_intro cpu curCtx r; iframe Hctx Hfrag
  · ipureintro; exact Or.inr ⟨a, d, rfl⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`translateAddr` with the hit and the miss as obligations** (`satp` at
Sv39 / ASID 0 / `root`): for every entry the lookup can answer the hit lands
on `ppn` giving `Q`, and so does the miss (walking `root`).  The resource
`R` carries whatever both need beyond the TLB cell.  A hit whose step-7
compare fails walks `root` (`translate_TLB_miss`), so the hit obligation may
use the miss's. -/
theorem swp_translateAddr_via [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool) (root : BitVec 44)
    (hok : SConfKpt (GF := GF) c root sie) (tlb : Tlb) (va : BitVec 64)
    (hcanon : BitVec.signExtend 64 (BitVec.extractLsb' 0 39 va) = va)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (ppn : BitVec 44) (R Q : IProp GF)
    (hhit : ∀ (mxr do_sum : Bool) (i : Nat) (ent : TLB_Entry), lookupHit tlb (vpnOf va) (some (i, ent)) →
      (∀ Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF,
        confCells cpu dq Privilege.Supervisor c ∗ Register.tlb ↦ᵣ[cpu] tlb ∗ R ∗
        (confCells cpu dq Privilege.Supervisor c -∗ Q -∗ Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, ())))
        ⊢ swp cpu (translate_TLB_miss39 0#16 root (vpnOf va) acc Privilege.Supervisor mxr do_sum ()) Φ) →
      ∀ Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF,
      confCells cpu dq Privilege.Supervisor c ∗ Register.tlb ↦ᵣ[cpu] tlb ∗ R ∗
      (confCells cpu dq Privilege.Supervisor c -∗ Q -∗ Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, ())))
      ⊢ swp cpu (translate_TLB_hit39 0#16 root (vpnOf va) acc Privilege.Supervisor mxr do_sum () i ent) Φ)
    (hmiss : ∀ (mxr do_sum : Bool),
      ∀ Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF,
      confCells cpu dq Privilege.Supervisor c ∗ Register.tlb ↦ᵣ[cpu] tlb ∗ R ∗
      (confCells cpu dq Privilege.Supervisor c -∗ Q -∗ Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, ())))
      ⊢ swp cpu (translate_TLB_miss39 0#16 root (vpnOf va) acc Privilege.Supervisor mxr do_sum ()) Φ)
    (Φ : Result (physaddr × page_based_mem_type × Unit) (ExceptionContext × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ Register.tlb ↦ᵣ[cpu] tlb ∗ R ∗
    (confCells cpu dq Privilege.Supervisor c -∗ Q -∗
        Φ (.Ok (physaddr.Physaddr (BitVec.setWidth 64 (ppn ++ BitVec.extractLsb' 0 12 va)),
          page_based_mem_type.PBMT_PMA, ())))
    ⊢ swp cpu (translateAddr (virtaddr.Virtaddr va) acc Privilege.Supervisor) Φ := by
  iintro ⟨HmConf, Htlb, HR, HΦ⟩
  conf_cases HmConf
  have hok0 := hok
  obtain ⟨⟨hpmp, hms, hpmm, hlpe⟩, hmode, hasid, hroot, hadue⟩ := hok
  obtain ⟨hSIE, hMPRV, hSXL, hMXR, hTSR, hTVM, hFS, hXS, hVS, hSD, hMPP⟩ := hms
  have hcanon' := canon_truncate va hcanon
  unfold translateAddr
  rw [is_shadow_stack_access_kernel acc hacc]
  swp_run 40
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_translationMode_kpt cpu dq c sie root hok0)
  iframe HmConf
  inext
  iintro HmConf
  conf_cases HmConf
  -- the Svukte check, then `translate_vs_stage` reads the mode again
  swp_run 120
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_translationMode_kpt cpu dq c sie root hok0)
  iframe HmConf
  inext
  iintro HmConf
  conf_cases HmConf
  swp_run 120
  reduce_closed_widths
  rw [extract_vpnOf, extract_offset_truncate, satp_to_asid_of c.satp hasid, satp_to_ppn_of c.satp root hroot]
  conf_intro HmConf
  iapply swp_bind
  iapply (swp_lookup_TLB_gen cpu tlb (vpnOf va))
  iframe Htlb
  inext
  iintro Htlb %r %hres
  cases r with
  | none =>
    -- the miss event (`generate_event`) reads the privilege
    conf_cases HmConf
    swp_run 10
    conf_intro HmConf
    rw [translate_TLB_miss39_eq]
    iapply swp_bind
    iapply (hmiss _ _)
    iframe HmConf Htlb HR
    iintro HmConf HQ
    swp_run 20
    iapply HΦ $$ HmConf HQ
  | some ie =>
    obtain ⟨i, ent⟩ := ie
    swp_run 10
    rw [translate_TLB_hit39_eq]
    iapply swp_bind
    iapply (hhit _ _ i ent hres (hmiss _ _))
    iframe HmConf Htlb HR
    iintro HmConf HQ
    swp_run 20
    iapply HΦ $$ HmConf HQ

end MachCSL
