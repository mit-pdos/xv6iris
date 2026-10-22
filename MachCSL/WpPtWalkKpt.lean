/-
MachCSL: translation at the SHARED kernel table, and in the `satp`-switch window -- the rules
that step through the model's step-7 compare and its retry loop (`update_and_write_pte`'s
`PTE_Update_Retry`, `translate_TLB_miss_retry`; fork commit 7 of `dongjaelee1/sail-riscv`).

Proved (their truth does not depend on how the retry loop is bounded):
* `swp_update_and_write_pte_kpt`: the hardware's `A`/`D` write-back on a kernel leaf, its two
  outcomes a choice of continuations (`∧`): `PTE_Update_Done p`, or `PTE_Update_Retry ()` with
  the reservation the failed compare left standing;
* `swp_translate_TLB_hit_kpt`, `swp_translate_TLB_hit_kptE`: a hit on a cached kernel leaf; a
  failed compare falls into `translate_TLB_miss` at `satp`'s root, which the caller proves (the
  right conjunct of the continuation);
* `swp_translateAddr_via`: `translateAddr` with the hit and the miss as obligations, the hit's
  obligation given the miss's.

PARKED (C3 lane, 2026-10-22), at the end of the file: `swp_translate_TLB_miss_kpt`,
`swp_translateAddr_kpt`, `swp_translate_TLB_miss_kptE`, still the pre-C3 proofs (moved verbatim
out of `WpPtWalk` and `WpPtWalkOwn`), which do not compile against the regenerated model.  A
failed compare at the kernel table makes the miss walk again, and bounding those walks waits for
the owner's ruling (local-plan/c3-ad-compare/kpt-monotone-design.md).
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

/-! ## PARKED: the miss rules

The three theorems below are the pre-C3 proofs, verbatim; they do not compile against the
regenerated model and are not used by the theorems above.  Each waits for the owner's ruling
on the kernel table's retry loop: the semantics change S1 (an exclusive read stamps its
footprint's coherence floors) with route R2 (the reservation held across the re-walk; at most
two walks), or option C (the kernel's `A`/`D` preset, under which the compare never runs).  The
R2 statements of the worker rules are in local-plan/c3-ad-compare/kpt-monotone-design.md §4.1. -/

/-! PARKED: `swp_translate_TLB_miss_kpt` waits for the owner's S1/C ruling (design memo §4.1:
under R2 it unfolds `translate_TLB_miss` to the worker at `16 = 15 + 1` and applies
`swp_translate_TLB_miss_retry_kpt`).  Its proof still applies the old
`swp_update_and_write_pte_kpt` and has no Retry arm. -/
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


/-! PARKED: `swp_translateAddr_kpt` waits for `swp_translate_TLB_miss_kpt` (the owner's S1/C
ruling).  Its statement need not move; its hit case must pass `t.base` as the root and prove the
new right conjunct with `swp_translate_TLB_miss_kpt`. -/
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

/-! PARKED: `swp_translate_TLB_miss_kptE` waits for the owner's S1/C ruling: it is the kernel-table
miss without the `tlbOk` claim, so it needs the same retry-loop rule as
`swp_translate_TLB_miss_kpt` (design memo §4.1; proof inventory §3.7 asks for one loop rule whose
post names the refilled slot, from which both follow). -/
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

end MachCSL
