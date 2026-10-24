/-
MachCSL: owned bytes, exclusively -- the owned exclusive pair and the owned page-table entry
leaves (Rocq `UptWalkPt.v`, the memory half).  A user page table is not shared: its entry words
are the running context's own bytes (`ctxBytes`), so a walk reads them exactly (no variants), and
the hardware's `A`/`D` write-back is an exclusive pair on owned bytes.  This file provides,
bottom-up: `ctxBytes_hist` (the byte histories behind owned bytes), `ctxBytes_exclReadAU` (the
read half's accessor, built from ownership), `ctx_store_excl` / `swp_sail_mem_write_excl_ctx`
(the write half: the running context stamps the new position, as `ctx_store` does for a plain
store); the entry leaves `swp_read_pte_ctx`, `swp_read_pte_exclusive_ctx`,
`swp_write_pte_conditional_ctx`; and `pteAddrOk`.  Split out of `WpPtWalkOwn` at the start of
the C3 lane (2026-10-22) so that the user tier (`URunRW`) builds without the walk rules.
-/
import MachCSL.WpPtWalk

noncomputable section

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ArchSem
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

variable {GF : BundledGFunctors.{0}} [MachGS GF]

/-! ## Owned bytes, exclusively -/

/-- The byte histories behind owned bytes: their heads spell the bytes, and
the same histories give the bytes back (the keys are persistent). -/
theorem ctxBytes_hist (ξ : CtxId) (pa : PAddr) (dq : DFrac) (bs : Nat → BitVec 8) : ∀ n : Nat,
    ([∗list] j ∈ List.range n, ctxByte ξ (pa + BitVec.ofNat 64 j) dq (bs j)) ⊢@{IProp GF}
      ∃ Hs : Nat → Hist, ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq} Hs j) ∗
        ⌜∀ j, j < n → Hs j ≠ [] ∧ (Hs j).head?.map HEnt.v = some (bs j)⌝ ∗
        (([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq} Hs j) -∗
          [∗list] j ∈ List.range n, ctxByte ξ (pa + BitVec.ofNat 64 j) dq (bs j))
  | 0 => by
    iintro _
    iexists (fun _ => [])
    isplitl []
    · simp only [List.range_zero, Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
    isplit
    · ipureintro; intro j hj; omega
    · iintro _
      simp only [List.range_zero, Iris.Algebra.BigOpL.bigOpL_nil]; iempintro
  | n + 1 => by
    rw [List.range_succ]
    iintro Hb
    icases BigSepL.bigSepL_snoc.1 $$ Hb with ⟨Hb1, Hb2⟩
    icases ctxBytes_hist ξ pa dq bs n $$ Hb1 with ⟨%Hs1, H1, %h1, W1⟩
    icases ctxByte_cases ξ _ _ _ $$ Hb2 with ⟨%e, %H, Hpt, %he, #Hkey⟩
    have hmem : ∀ {k x : Nat}, (List.range n)[k]? = some x → x ≠ n := by
      intro k x hk hx
      have := List.mem_of_getElem? hk
      rw [List.mem_range] at this
      omega
    iexists (fun j => if j = n then e :: H else Hs1 j)
    have heq : ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq}
        (fun j => if j = n then e :: H else Hs1 j) j) =
        ([∗list] j ∈ List.range n, (pa + BitVec.ofNat 64 j) ↦ₕ{dq} Hs1 j : IProp GF) := by
      apply BigSepL.bigSepL_eq
      intro k x hk
      simp only [hmem hk, ite_false]
    isplitl [H1 Hpt]
    · iapply BigSepL.bigSepL_snoc.2
      simp only [ite_true]
      rw [heq]
      iframe H1 Hpt
    isplit
    · ipureintro
      intro j hj
      by_cases hjn : j = n
      · subst hjn; simp [he]
      · simp only [hjn, ite_false]; exact h1 j (by omega)
    · iintro Hh
      icases BigSepL.bigSepL_snoc.1 $$ Hh with ⟨Hh1, Hh2⟩
      simp only [ite_true]
      rw [heq]
      iapply BigSepL.bigSepL_snoc.2
      isplitl [Hh1 W1]
      · iapply W1 $$ Hh1
      · try simp only [List.length_range]
        rw [← he]
        iapply ctxByte_intro ξ _ dq e H $$ [Hh2]
        iframe Hh2 Hkey

/-- **The read half of an exclusive pair, from ownership**: owned bytes
give the accessor directly (no invariant to open); the heads read are the
owned value. -/
theorem ctxBytes_exclReadAU (ξ : CtxId) (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    ctxBytes (GF := GF) ξ pa n dq w ⊢ exclReadAU pa n (fun w0 => iprop(⌜w0 = w⌝ ∗ ctxBytes ξ pa n dq w)) := by
  unfold ctxBytes exclReadAU histBytes
  iintro H
  icases ctxBytes_hist ξ pa dq (nthByte w) n $$ H with ⟨%Hs, Hh, %h, W⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  iexists (fun _ => dq), Hs
  iframe Hh
  isplit
  · ipureintro; exact fun j hj => (h j hj).1
  inext
  iintro %w0 %hheads Hh _
  imod Hmask
  imodintro
  isplit
  · ipureintro
    apply bv_eq_of_bytes
    intro j hj
    have h1 := hheads j hj
    have h2 := (h j hj).2
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  · iapply W $$ Hh

/-- A store of an exclusive pair by the running context: the memory model
moves, the new timestamp enters ξ's dirty set (`ctx_store`, over
`memModel_store_excl_any`).  From ANY reservation state (Rocq `resv_any`):
the machine lets the conditional write through whenever no other hart
reserves the footprint, whatever this hart holds; an acquire pair's view
receipt is dropped. -/
theorem ctx_store_excl (σ : MState) (cpu : CPU) (ξ : CtxId) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (r : Option Resv) (hram : ramBytes pa n) (hno : ¬ othersReserve σ.resv cpu pa n) :
    memModel σ ∗ ownCtx cpu ξ ∗ resvFragAny cpu r ⊢@{IProp GF} |==>
      (memModel (σ.store cpu pa n w true) ∗ ownCtx cpu ξ ∗ resvFrag cpu none false ∗
       keyAt (MachGS.era (GF := GF)) ξ (σ.top + 1)) := by
  unfold ownCtx ownCtxAt resvFragAny resvFragAnyAt resvFrag memModel
  iintro ⟨Hmm, ⟨%B, %K, %W, %D, Hctx, #HK, %hBK, #HW, %hDW, #Hels⟩, %acq, Hfrag⟩
  ihave %hW : ⌜W ≤ σ.top⌝ $$ [Hmm HW]
  · iapply memModel_topLb _ σ W $$ [Hmm HW]
    iframe Hmm
    iexact HW
  imod memModel_store_excl_any _ σ cpu pa n w r acq hram hno $$ [$Hmm $Hfrag] with ⟨Hmm, Hfrag, #Hau, #Htop', _⟩
  unfold ctxAt
  icases Hctx with ⟨Hbound, Hdirty⟩
  have hfresh : get? D (σ.top + 1) = none := by
    cases hD : get? D (σ.top + 1) with
    | none => rfl
    | some h =>
      have := (hDW (σ.top + 1) h hD).1
      omega
  imod ghost_map_insert_persist (σ.top + 1) cpu hfresh $$ Hdirty with ⟨Hdirty, #Hdin⟩
  imodintro
  iframe Hmm Hfrag
  isplitr []
  · iexists B, K, (σ.top + 1), (Iris.Std.PartialMap.insert D (σ.top + 1) cpu)
    iframe Hbound Hdirty HK Htop'
    isplit
    · ipureintro; exact hBK
    isplit
    · ipureintro
      intro k h hk
      by_cases hkt : k = σ.top + 1
      · subst hkt
        rw [LawfulPartialMap.get?_insert_eq rfl] at hk
        exact ⟨Nat.le_refl _, Or.inr (Option.some.inj hk).symm⟩
      · rw [LawfulPartialMap.get?_insert_ne (Ne.symm hkt)] at hk
        obtain ⟨h1, h2⟩ := hDW k h hk
        exact ⟨by omega, h2⟩
    · unfold dirtyElems
      imodintro
      iintro %k %h %hk
      by_cases hkt : k = σ.top + 1
      · subst hkt
        rw [LawfulPartialMap.get?_insert_eq rfl] at hk
        obtain rfl := Option.some.inj hk
        unfold dirtyIn
        isplit
        · iexact Hdin
        · iexact Hau
      · rw [LawfulPartialMap.get?_insert_ne (Ne.symm hkt)] at hk
        iapply Hels $$ %k %h %hk
  · unfold keyAt
    iright
    iexists cpu
    isplit
    · unfold dirtyIn
      iexact Hdin
    · iexact Hau

/-! ## The memory leaves -/

/-- **The write half of an exclusive pair, on owned bytes**: full ownership
and the hart's reservation fragment in ANY state (Rocq `resv_any`: the read
half's snapshot, none -- an `SC` whose `LR` a store or a trap already spent,
the model's `match_reservation` having let it through -- or a pending
acquire); the bytes come back at the new value, justified at ξ as ξ's own
store.  The value written is the bits of the model's bytes (`hv`; callers
discharge it with the `SailBytes` round trip); the interface answers `.Ok none`
(concurrency interface v2 reports no success flag, the model supplies it). -/
theorem swp_sail_mem_write_excl_ctx (cpu : CPU) {n nt : Nat}
    (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc)
    (bytes : Vector (BitVec 8) n) (tags : Vector Bool nt)
    (ξ : CtxId) (r : Option Resv) (w w' : BitVec (8 * n)) (hv : vecbytes_to_bitvec bytes = w')
    (hk : akExcl req.access_kind = true)
    (Φ : Result (Option Bool) Unit → IProp GF) :
    ownCtx cpu ξ ∗ resvFragAny cpu r ∗ ctxBytes ξ req.address n (DFrac.own 1) w ∗
    ▷ (ownCtx cpu ξ -∗ resvFrag cpu none false -∗ ctxBytes ξ req.address n (DFrac.own 1) w' -∗ Φ (.Ok none))
    ⊢ swp cpu (LeanRV64D.ArchSem.sail_mem_write req bytes tags) Φ := by
  subst hv
  iintro ⟨Hctx, Hfrag, Hb, HΦ⟩
  iloeb as IH
  iapply swp_event_step_at cpu (LeanRV64D.ArchSem.sail_mem_write req bytes tags)
    (.memWrite (memReq req) (vecbytes_to_bitvec bytes) (vecbool_to_bitvec tags))
    (fun v => FreeM.pure (memWriteAns v)) (sail_mem_write_def req bytes tags) Φ
  iintro %σ Hσ
  icases machInterp_acc_mem σ cpu $$ Hσ with ⟨Hregs, Hmem, Hmm, Hclose⟩
  ihave %hram : ⌜ramBytes req.address n⌝ $$ [Hctx Hb Hmem Hmm]
  · ihave %hrd : ⌜∀ tvn, σ.tv cpu ≤ tvn → σ.mem.readBytes (hartAgent cpu) tvn req.address n w⌝
        $$ [Hmm Hctx Hmem Hb]
    · iapply ctxBytes_readable σ cpu ξ req.address n (DFrac.own 1) w $$ [Hmm Hctx Hmem Hb]
      iframe
    ihave %hmm : ⌜mmOk σ⌝ $$ [Hmm]
    · iapply memModel_mmOk $$ Hmm
    ipureintro
    exact ramBytes_of_readBytes hmm.2.2.2.1 (hrd _ (Nat.le_refl _))
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  isplit
  · ipureintro
    by_cases hno : othersReserve σ.resv cpu req.address n
    · exact Or.inr ⟨σ, hno, by rw [ite_eq_left (by simp [hk])]⟩
    · exact Or.inl ⟨.ok (), _, Or.inr ⟨hram, hno, rfl, rfl⟩⟩
  inext
  iintro %σ'
  isplit
  · iintro %v %Hev
    rcases Hev with ⟨hdev, ds₀, hdw, _, _⟩ | ⟨_, hno, rfl, rfl⟩
    · exact absurd hdev (not_devBytes_of_ramBytes hram (devWrite_pos hdw))
    imod ctx_store_excl σ cpu ξ req.address n (vecbytes_to_bitvec bytes) r hram hno
      $$ [$Hmm $Hctx $Hfrag] with ⟨Hmm, Hctx, Hfrag, #Hkey⟩
    imod ctxBytes_update ξ σ.mem req.address n w (vecbytes_to_bitvec bytes) (σ.top + 1) (hartAgent cpu)
      $$ [$Hkey $Hmem $Hb] with ⟨Hmem, Hb⟩
    imod Hmask
    imodintro
    rw [hk]
    isplitl [Hregs Hmem Hmm Hclose]
    · iapply Hclose $$ %(σ.store cpu req.address n (vecbytes_to_bitvec bytes) true)
        %⟨fun _ _ => rfl, rfl⟩ Hregs Hmem Hmm
    · iapply swp_ret
      iapply HΦ $$ Hctx Hfrag Hb
  · iintro %Hbk
    obtain ⟨_, hσ⟩ := Hbk
    rw [ite_eq_left (by simp [hk])] at hσ
    subst σ'
    imod Hmask
    imodintro
    isplitl [Hregs Hmem Hmm Hclose]
    · iapply Hclose $$ %σ %⟨fun _ _ => rfl, rfl⟩ Hregs Hmem Hmm
    · iapply IH $$ Hctx Hfrag Hb
      inext
      iexact HΦ

/-! ## The entry leaves on owned words -/

set_option maxHeartbeats 4000000 in
set_option swp_run.memStop true in
/-- The physical read of an owned entry (`Load PageTableEntry`). -/
theorem swp_checked_mem_read_pte8_S_ctx [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (dq' : DFrac) (w : BitVec (8 * 8))
    (Φ : Result ((BitVec (8 * 8)) × Unit) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ctxTok cpu curCtx ∗ bytesPointsTo pa 8 dq' w ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗ bytesPointsTo pa 8 dq' w -∗
        Φ (.Ok (w, ())))
    ⊢ swp cpu (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) page_based_mem_type.PBMT_PMA
        Privilege.Supervisor (physaddr.Physaddr pa) 8 false false false false) Φ := by
  iintro ⟨HmConf, Htok, Hb, HΦ⟩
  unfold checked_mem_read
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  mem_iapply (swp_sail_mem_read_plain cpu) curCtx dq' w rfl
  iframe Htok Hb
  inext
  iintro Htok Hb
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf Htok Hb

set_option maxHeartbeats 4000000 in
set_option swp_run.memStop true in
/-- `read_pte` of an owned entry: its value. -/
theorem swp_read_pte_ctx [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (dq' : DFrac) (w : BitVec (8 * 8))
    (Φ : Result (BitVec (8 * 8)) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ctxTok cpu curCtx ∗ bytesPointsTo pa 8 dq' w ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ctxTok cpu curCtx -∗ bytesPointsTo pa 8 dq' w -∗ Φ (.Ok w))
    ⊢ swp cpu (read_pte (physaddr.Physaddr pa) 8) Φ := by
  iintro ⟨HmConf, Htok, Hb, HΦ⟩
  unfold read_pte mem_read mem_read_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_read_pte8_S_ctx cpu dq c sie hok pa hram hal dq' w)
  iframe HmConf Htok Hb
  inext
  iintro HmConf Htok Hb
  swp_run 20
  simp only [MemoryOpResult_drop_meta]
  iapply HΦ $$ HmConf Htok Hb

set_option maxHeartbeats 4000000 in
set_option swp_run.memStop true in
/-- `read_pte_exclusive` of an owned entry: its value, the reservation on it. -/
theorem swp_read_pte_exclusive_ctx [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (r : Option Resv) (dq' : DFrac) (w : BitVec (8 * 8))
    (Φ : Result (BitVec (8 * 8)) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFragAny cpu r ∗ bytesPointsTo pa 8 dq' w ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ resvFrag cpu (some (snapOf pa 8 w .pte)) false -∗
        bytesPointsTo pa 8 dq' w -∗ Φ (.Ok w))
    ⊢ swp cpu (read_pte_exclusive (physaddr.Physaddr pa) 8) Φ := by
  iintro ⟨HmConf, Hfrag, Hb, HΦ⟩
  iapply (swp_read_pte_exclusive cpu dq c sie hok pa hram hal r
    (fun w0 => iprop(⌜w0 = w⌝ ∗ resvFrag cpu (some (snapOf pa 8 w0 .pte)) false ∗ bytesPointsTo pa 8 dq' w)))
  iframe HmConf Hfrag
  isplitl [Hb]
  · iapply exclReadAU_wand pa 8 _ _ $$ [Hb]
    · iapply ctxBytes_exclReadAU curCtx pa 8 dq' w $$ Hb
    inext
    iintro %w0 ⟨%hw, Hb⟩ Hfrag
    iframe Hb Hfrag
    ipureintro; exact hw
  inext
  iintro HmConf %w0 ⟨%hw, Hfrag, Hb⟩
  subst hw
  iapply HΦ $$ HmConf Hfrag Hb

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- The conditional physical write of an owned entry, after the exclusive
read. -/
theorem swp_checked_mem_write_pte8_cond_S_ctx [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (w0 w data : BitVec (8 * 8)) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0)
    (Φ : Result Bool (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ownCtx cpu curCtx ∗ resvFrag cpu (some (snapOf pa 8 w0 .pte)) false ∗
    bytesPointsTo pa 8 (DFrac.own 1) w ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗ resvFrag cpu none false -∗
        bytesPointsTo pa 8 (DFrac.own 1) data -∗ Φ (.Ok true))
    ⊢ swp cpu (checked_mem_write (physaddr.Physaddr pa) 8 data (MemoryAccessType.Store mem_payload.PageTableEntry)
        page_based_mem_type.PBMT_PMA Privilege.Supervisor () false false true) Φ := by
  iintro ⟨HmConf, Hctx, Hfrag, Hb, HΦ⟩
  unfold checked_mem_write
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  mem_iapply (swp_sail_mem_write_excl_ctx cpu) curCtx (some (snapOf pa 8 w0 .pte)) w data
    (vecbytes_to_bitvec_to_bytes_le_8 _) rfl
  ihave Hfrag := resvFragAny_of cpu (some (snapOf pa 8 w0 .pte)) false $$ Hfrag
  iframe Hctx Hfrag Hb
  inext
  iintro Hctx Hfrag Hb
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf Hctx Hfrag Hb

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- `write_pte_conditional` on an owned entry: the entry takes `data`. -/
theorem swp_write_pte_conditional_ctx [CurCtx] (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (w0 w data : BitVec (8 * 8)) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0)
    (Φ : Result Bool (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ ownCtx cpu curCtx ∗ resvFrag cpu (some (snapOf pa 8 w0 .pte)) false ∗
    bytesPointsTo pa 8 (DFrac.own 1) w ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ownCtx cpu curCtx -∗ resvFrag cpu none false -∗
        bytesPointsTo pa 8 (DFrac.own 1) data -∗ Φ (.Ok true))
    ⊢ swp cpu (write_pte_conditional (physaddr.Physaddr pa) 8 data) Φ := by
  iintro ⟨HmConf, Hctx, Hfrag, Hb, HΦ⟩
  unfold write_pte_conditional mem_write_value mem_write_value_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_write_pte8_cond_S_ctx cpu dq c sie hok pa w0 w data hram hal)
  iframe HmConf Hctx Hfrag Hb
  inext
  iintro HmConf Hctx Hfrag Hb
  swp_run 20
  iapply HΦ $$ HmConf Hctx Hfrag Hb

/-! ## The walk over owned entries -/

/-- An entry address the hardware can read: an aligned RAM word. -/
def pteAddrOk (a : BitVec 64) : Prop := inRam a 8 ∧ a.toNat % 8 = 0

end MachCSL
