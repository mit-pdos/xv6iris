/-
MachCSL: translation at the SHARED kernel table, and in the `satp`-switch window -- the rules
that step through the model's step-7 retry loop (`translate_TLB_miss_retry`, fork commit 7 of
`dongjaelee1/sail-riscv`): the hardware's `A`/`D` write-back on a kernel leaf
(`swp_update_and_write_pte_kpt`), the kernel-table hit and miss, `swp_translateAddr_kpt`, the
`_kptE` twins and `swp_translateAddr_via`.

PARKED at the start of the C3 lane (2026-10-22): the bodies below are the pre-C3 proofs, moved
verbatim out of `WpPtWalk` and `WpPtWalkOwn`; they do not compile against the regenerated model
until they are re-proved under the route the owner rules on
(local-plan/c3-ad-compare/kpt-monotone-design.md).  Everything else in MachCSL builds meanwhile.
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
/-- `update_and_write_pte` on the kernel leaf the walk read (canonical entry
`kLeaf ppn perm a0 d0` at `addr`): either nothing to do, or an exclusive
re-read of the entry and, if its bits are still short, the conditional
write-back of the leaf with `A` (and `D`) set.  The reservation may be left
standing (a re-read that found the bits already set). -/
theorem swp_update_and_write_pte_kpt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (a d a0 d0 : BitVec 1)
    (hmem : (addr, kLeaf ppn perm a0 d0) ∈ t.entries 2) (hperm : perm.allows acc = true) (u : Unit)
    (r0 : Option Resv) (Φ : Result (Option (BitVec 64) × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗ resvFragAny cpu r0 ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (p : Option (BitVec 64)), ⌜pteOptVariant ppn perm p⌝ -∗ Φ (.Ok (p, u)))
    ⊢ swp cpu (update_and_write_pte39 vpn (physaddr.Physaddr addr) (kLeaf ppn perm a d) 0 acc
        Privilege.Supervisor mxr do_sum u) Φ := by
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
    swp_run 40
    rw [check_leaf_pte39_eq]
    iapply swp_bind
    iapply (swp_check_leaf_pte_kLeaf cpu dq c vpn acc hacc mxr do_sum ppn perm a1 d1 hperm addr u)
    iframe HmConf
    inext
    iintro HmConf
    obtain ⟨o2, hupd2, ho2⟩ := update_PTE_Bits_kLeaf ppn perm a1 d1 acc hpl TranslationStage.S_Stage
    rw [hupd2]
    rcases ho2 with rfl | ⟨a2, d2, rfl⟩
    · swp_run 40
      ihave Hfrag := resvFragAny_of cpu (some (snapOf addr 8 (kLeaf ppn perm a1 d1))) false $$ Hfrag
      iapply HΦ $$ HmConf Hctx %(some (snapOf addr 8 (kLeaf ppn perm a1 d1))) Hfrag %(some (kLeaf ppn perm a1 d1))
      ipureintro; exact ⟨a1, d1, rfl⟩
    · swp_run 40
      ihave HW := kpt_exclWriteAU cpu t M addr _ hmem (kLeaf ppn perm a1 d1) (kLeaf ppn perm a2 d2)
        (pteVariant_kLeaf ppn perm a0 d0 a2 d2) $$ Hkpt
      iapply swp_bind
      iapply (swp_write_pte_conditional cpu dq c sie hok addr (kLeaf ppn perm a1 d1) (kLeaf ppn perm a2 d2)
        (hents _ hmem).1 (hents _ hmem).2 emp)
      iframe HmConf Hfrag HW
      inext
      iintro HmConf Hfrag _
      swp_run 40
      ihave Hfrag := resvFragAny_of cpu none false $$ Hfrag
      iapply HΦ $$ HmConf Hctx %none Hfrag %(some (kLeaf ppn perm a2 d2))
      ipureintro; exact ⟨a2, d2, rfl⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- A TLB hit on a mapped `vpn`: the permission check on the cached leaf,
the `A`/`D` write-back through the cached entry's address, the cached entry
refreshed if the write-back changed the leaf. -/
theorem swp_translate_TLB_hit_kpt [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (htlb : tlbOk t tlb) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (i : Nat) (ent : TLB_Entry) (hres : lookupRes t tlb vpn (some (i, ent)))
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (hmaps : t.maps vpn addr ppn perm)
    (hperm : perm.allows acc = true) (u : Unit)
    (r0 : Option Resv) (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ownCtx cpu curCtx ∗ resvFragAny cpu r0 ∗
    Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗
        ∀ (r : Option Resv), resvFragAny cpu r -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbOk t tlb'⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_hit39 0#16 vpn acc Privilege.Supervisor mxr do_sum u i ent) Φ := by
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
  rw [pteAddr_tlbEntryOf, tlb_get_level_tlbEntryOf, update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt cpu dq c sie hok hadue t M vpn acc hacc mxr do_sum addr₁ ppn₁ perm₁
    a' d' a d hmem hperm u r0)
  iframe HmConf Hkpt Hctx Hfrag
  iintro HmConf Hctx %r Hfrag %p %hp
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- A TLB miss on a mapped `vpn`: the walk, the write-back, the entry cached. -/
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
  unfold translate_TLB_miss39 translate_TLB_miss
  reduce_closed_widths
  swp_run 20
  rw [get_root_level_39, pt_walk39_eq]
  iapply swp_bind
  iapply (swp_pt_walk_kpt cpu dq c sie hok t M vpn acc hacc mxr do_sum addr ppn perm hmaps hperm u)
  iframe HmConf Hkpt Hctx
  inext
  iintro HmConf Hctx %a %d
  obtain ⟨a₀, d₀, hw⟩ := hmaps
  have hmem := PTree.walk_mem_entries 2 t vpn _ _ hw
  unfold kptWalkOut
  swp_run 20
  rw [update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt cpu dq c sie hok hadue t M vpn acc hacc mxr do_sum addr ppn perm
    a d a₀ d₀ hmem hperm u r0)
  iframe HmConf Hkpt Hctx Hfrag
  iintro HmConf Hctx %r Hfrag %p %hp
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
    iapply HΦ $$ HmConf Hctx %r Hfrag %_ Htlb
    ipureintro; exact tlbOk_write t tlb htlb vpn addr ppn perm a₀ d₀ a d hw
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
    iapply HΦ $$ HmConf Hctx %r Hfrag %_ Htlb
    ipureintro; exact tlbOk_write t tlb htlb vpn addr ppn perm a₀ d₀ a2 d2 hw


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
    iapply (swp_translate_TLB_hit_kpt cpu dq c sie hok' hadue t M tlb htlb (vpnOf va) acc hacc _ _ i ent hres
      addr ppn perm hmaps hperm _ r0)
    iframe HmConf Hkpt Hctx Hfrag Htlb
    iintro HmConf Hctx %r Hfrag %tlb' Htlb %htlb'
    swp_run 20
    iapply HΦ $$ HmConf Hctx %r Hfrag %tlb' Htlb
    ipureintro; exact htlb'

/-! ## Translation with the hit and the miss as obligations

Between a `csrw satp` and the following `sfence.vma` the TLB holds entries
of two tables (Rocq `TransPt`): a hit may be on either table's entry, a miss
walks the table `satp` now names.  So the translation is proved here once,
with what happens on a hit (for each entry the lookup can answer) and on a
miss as the caller's obligations, over a resource `R`. -/

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
through the kernel table's invariant; the entry may be refreshed. -/
theorem swp_translate_TLB_hit_kptE [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie) (hadue : BitVec.extractLsb' 61 1 c.menvcfg = 1#1)
    (t : PTree) (M : RegMapF (BitVec 64)) (tlb : Tlb) (vpn : BitVec 27)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (mxr do_sum : Bool)
    (i : Nat) (ent : TLB_Entry) (hi : i = tlbHash vpn) (hget : tlb[tlbHash vpn]'(tlbHash_lt vpn) = some ent)
    (addr : BitVec 64) (ppn : BitVec 44) (perm : KPerm) (a d a' d' : BitVec 1)
    (hw : t.walk 2 vpn = some (addr, kLeaf ppn perm a d))
    (hent : ent = tlbEntryOf 0#16 vpn ppn (kLeaf ppn perm a' d') addr)
    (hperm : perm.allows acc = true) (u : Unit)
    (Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ kptOn t M ∗ ctxTok cpu curCtx ∗ Register.tlb ↦ᵣ[cpu] tlb ∗
    (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗
        ∀ (tlb' : Tlb), Register.tlb ↦ᵣ[cpu] tlb' -∗ ⌜tlbAfterE tlb tlb' vpn ppn perm addr⌝ -∗
        Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, u)))
    ⊢ swp cpu (translate_TLB_hit39 0#16 vpn acc Privilege.Supervisor mxr do_sum u i ent) Φ := by
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
  rw [pteAddr_tlbEntryOf, tlb_get_level_tlbEntryOf, update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt cpu dq c sie hok hadue t M vpn acc hacc mxr do_sum addr ppn perm
    a' d' a d hmem hperm u r0)
  iframe HmConf Hkpt Hctx Hfrag
  iintro HmConf Hctx %r Hfrag %p %hp
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **A TLB miss walking the SHARED kernel table**, without any claim about
the rest of the TLB: the walk, the write-back, the kernel entry cached. -/
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
  unfold translate_TLB_miss39 translate_TLB_miss
  reduce_closed_widths
  swp_run 20
  rw [get_root_level_39, pt_walk39_eq]
  iapply swp_bind
  iapply (swp_pt_walk_kpt cpu dq c sie hok t M vpn acc hacc mxr do_sum addr ppn perm hmaps hperm u)
  iframe HmConf Hkpt Hctx
  inext
  iintro HmConf Hctx %a %d
  obtain ⟨a₀, d₀, hw⟩ := hmaps
  have hmem := PTree.walk_mem_entries 2 t vpn _ _ hw
  unfold kptWalkOut
  swp_run 20
  rw [update_and_write_pte39_eq]
  iapply swp_bind
  iapply (swp_update_and_write_pte_kpt cpu dq c sie hok hadue t M vpn acc hacc mxr do_sum addr ppn perm
    a d a₀ d₀ hmem hperm u r0)
  iframe HmConf Hkpt Hctx Hfrag
  iintro HmConf Hctx %r Hfrag %p %hp
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
    iapply HΦ $$ HmConf [Hctx Hfrag] %_ Htlb
    · iapply ctxTok_intro cpu curCtx r; iframe Hctx Hfrag
    · ipureintro; exact Or.inr ⟨a, d, rfl⟩
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
    iapply HΦ $$ HmConf [Hctx Hfrag] %_ Htlb
    · iapply ctxTok_intro cpu curCtx r; iframe Hctx Hfrag
    · ipureintro; exact Or.inr ⟨a2, d2, rfl⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`translateAddr` with the hit and the miss as obligations** (`satp` at
Sv39 / ASID 0 / `root`): for every entry the lookup can answer the hit lands
on `ppn` giving `Q`, and so does the miss (walking `root`).  The resource
`R` carries whatever both need beyond the TLB cell. -/
theorem swp_translateAddr_via [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool) (root : BitVec 44)
    (hok : SConfKpt (GF := GF) c root sie) (tlb : Tlb) (va : BitVec 64)
    (hcanon : BitVec.signExtend 64 (BitVec.extractLsb' 0 39 va) = va)
    (acc : MemoryAccessType mem_payload) (hacc : kernelAccess acc) (ppn : BitVec 44) (R Q : IProp GF)
    (hhit : ∀ (mxr do_sum : Bool) (i : Nat) (ent : TLB_Entry), lookupHit tlb (vpnOf va) (some (i, ent)) →
      ∀ Φ : Result (BitVec 44 × page_based_mem_type × Unit) (PTW_Error × Unit) → IProp GF,
      confCells cpu dq Privilege.Supervisor c ∗ Register.tlb ↦ᵣ[cpu] tlb ∗ R ∗
      (confCells cpu dq Privilege.Supervisor c -∗ Q -∗ Φ (.Ok (ppn, page_based_mem_type.PBMT_PMA, ())))
      ⊢ swp cpu (translate_TLB_hit39 0#16 (vpnOf va) acc Privilege.Supervisor mxr do_sum () i ent) Φ)
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
    iapply (hhit _ _ i ent hres)
    iframe HmConf Htlb HR
    iintro HmConf HQ
    swp_run 20
    iapply HΦ $$ HmConf HQ

end MachCSL
