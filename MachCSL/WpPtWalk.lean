/-
MachCSL: the page walk's memory leaves.

The model reads a page-table entry with `read_pte` (a privileged plain
load of kind `PageTableEntry`), and writes its A/D bits back with the
exclusive pair `read_pte_exclusive`/`write_pte_conditional`.  All three
are the physical accesses of `WpSmodeAtomic` at another access kind, over
the accessors the shared table's invariant provides (`MachCSL.KptInv`).
-/
import MachCSL.WpSmodeAtomic
import MachCSL.KptInv

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

set_option maxHeartbeats 4000000 in
set_option swp_run.memStop true in
/-- The physical read of an entry (`Load PageTableEntry`): the accessor's read. -/
theorem swp_checked_mem_read_pte8_S_au (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (K : Nat) (Ψ : BitVec (8 * 8) → IProp GF)
    (Φ : Result ((BitVec (8 * 8)) × Unit) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ viewLb cpu K ∗ readAU cpu pa 8 K Ψ ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ∀ w, Ψ w -∗ Φ (.Ok (w, ())))
    ⊢ swp cpu (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) page_based_mem_type.PBMT_PMA
        Privilege.Supervisor (physaddr.Physaddr pa) 8 false false false false) Φ := by
  iintro ⟨HmConf, #HK, HAU, HΦ⟩
  unfold checked_mem_read
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  iapply (swp_sail_mem_read_plain_au cpu _ rfl K)
  isplit
  · iexact HK
  iapply readAU_wand cpu pa 8 K Ψ $$ HAU
  inext
  iintro %w HΨ
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf %w HΨ

set_option maxHeartbeats 4000000 in
set_option swp_run.memStop true in
/-- `read_pte`: the entry at `pa`, through the accessor. -/
theorem swp_read_pte (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (K : Nat) (Ψ : BitVec (8 * 8) → IProp GF)
    (Φ : Result (BitVec (8 * 8)) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ viewLb cpu K ∗ readAU cpu pa 8 K Ψ ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ∀ w, Ψ w -∗ Φ (.Ok w))
    ⊢ swp cpu (read_pte (physaddr.Physaddr pa) 8) Φ := by
  iintro ⟨HmConf, #HK, HAU, HΦ⟩
  unfold read_pte mem_read_priv mem_read_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_read_pte8_S_au cpu dq c sie hok pa hram hal K Ψ)
  iframe HmConf HAU
  isplit
  · iexact HK
  inext
  iintro HmConf %w HΨ
  swp_run 20
  simp only [MemoryOpResult_drop_meta]
  iapply HΦ $$ HmConf %w HΨ

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- The exclusive physical read of an entry (the write-back's read half). -/
theorem swp_checked_mem_read_pte8_excl_S (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (Ψ : BitVec (8 * 8) → IProp GF)
    (Φ : Result ((BitVec (8 * 8)) × Unit) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu none false ∗
    exclReadAU pa 8 (fun w => iprop(resvFrag cpu (some (snapOf pa 8 w)) false -∗ Ψ w)) ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ∀ w, Ψ w -∗ Φ (.Ok (w, ())))
    ⊢ swp cpu (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) page_based_mem_type.PBMT_PMA
        Privilege.Supervisor (physaddr.Physaddr pa) 8 false false true false) Φ := by
  iintro ⟨HmConf, Hfrag, HAU, HΦ⟩
  unfold checked_mem_read
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  iapply (swp_sail_mem_read_excl_au cpu _ false rfl rfl (by decide))
  iframe Hfrag
  iapply exclReadAU_wand pa 8 _ _ $$ HAU
  inext
  iintro %w HΨ Hfrag
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf %w
  iapply HΨ $$ Hfrag

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- `read_pte_exclusive`: the entry at `pa`, taking the reservation. -/
theorem swp_read_pte_exclusive (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (Ψ : BitVec (8 * 8) → IProp GF)
    (Φ : Result (BitVec (8 * 8)) (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu none false ∗
    exclReadAU pa 8 (fun w => iprop(resvFrag cpu (some (snapOf pa 8 w)) false -∗ Ψ w)) ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ ∀ w, Ψ w -∗ Φ (.Ok w))
    ⊢ swp cpu (read_pte_exclusive (physaddr.Physaddr pa) 8) Φ := by
  iintro ⟨HmConf, Hfrag, HAU, HΦ⟩
  unfold read_pte_exclusive mem_read_priv mem_read_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_read_pte8_excl_S cpu dq c sie hok pa hram hal Ψ)
  iframe HmConf Hfrag HAU
  inext
  iintro HmConf %w HΨ
  swp_run 20
  simp only [MemoryOpResult_drop_meta]
  iapply HΦ $$ HmConf %w HΨ

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- The conditional physical write of an entry (the write-back's write
half), after an exclusive read that saw `w0`. -/
theorem swp_checked_mem_write_pte8_cond_S (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (w0 data : BitVec (8 * 8)) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (Ψ : IProp GF)
    (Φ : Result Bool (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu (some (snapOf pa 8 w0)) false ∗
    exclWriteAU cpu pa 8 false w0 data Ψ ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ resvFrag cpu none false -∗ Ψ -∗ Φ (.Ok true))
    ⊢ swp cpu (checked_mem_write (physaddr.Physaddr pa) 8 data (MemoryAccessType.Store mem_payload.PageTableEntry)
        page_based_mem_type.PBMT_PMA Privilege.Supervisor () false false true) Φ := by
  iintro ⟨HmConf, Hfrag, HAU, HΦ⟩
  unfold checked_mem_write
  checked_mem_S_au_prefix pa 8 hram hal
  iapply swp_bind
  iapply (swp_sail_mem_write_excl_au cpu _ w0 data false rfl rfl (by decide))
  iframe Hfrag
  iapply exclWriteAU_wand cpu pa 8 false w0 data Ψ $$ HAU
  inext
  iintro HΨ Hfrag
  swp_run 60
  conf_intro HmConf
  iapply HΦ $$ HmConf Hfrag HΨ

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option swp_run.memStop true in
/-- `write_pte_conditional`: the write-back of `data` to `pa`. -/
theorem swp_write_pte_conditional (cpu : CPU) (dq : DFrac) (c : MConf) (sie : Bool)
    (hok : SConfPhys (GF := GF) c sie)
    (pa : BitVec 64) (w0 data : BitVec (8 * 8)) (hram : inRam pa 8) (hal : pa.toNat % 8 = 0) (Ψ : IProp GF)
    (Φ : Result Bool (physaddr × ExceptionType) → IProp GF) :
    confCells cpu dq Privilege.Supervisor c ∗ resvFrag cpu (some (snapOf pa 8 w0)) false ∗
    exclWriteAU cpu pa 8 false w0 data Ψ ∗
    ▷ (confCells cpu dq Privilege.Supervisor c -∗ resvFrag cpu none false -∗ Ψ -∗ Φ (.Ok true))
    ⊢ swp cpu (write_pte_conditional (physaddr.Physaddr pa) 8 data) Φ := by
  iintro ⟨HmConf, Hfrag, HAU, HΦ⟩
  unfold write_pte_conditional mem_write_value_priv mem_write_value_priv_meta
  swp_run 20
  iapply swp_bind
  iapply (swp_checked_mem_write_pte8_cond_S cpu dq c sie hok pa w0 data hram hal Ψ)
  iframe HmConf Hfrag HAU
  inext
  iintro HmConf Hfrag HΨ
  swp_run 20
  iapply HΦ $$ HmConf Hfrag HΨ

end MachCSL
