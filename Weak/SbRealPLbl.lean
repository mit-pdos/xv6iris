/-
Weak: **allocproc route P, row P-W6 — THE REALIZING pf LABEL, dispatched to the hart rows**
(`SbWalk.evData`'s `lblRealizes` arm; `PROGRESS-PW6.md` CP-PW6-4 resume step 1).  Lean-only, no Rocq
twin.  A PRIMED TWIN: nothing registered imports this file.

After an event item's admin star (`SbRealPEv.adminEvP`), the hart's next pf node step carries the label
that realizes the twin's event.  Each lemma here takes that node step (`WeakEvInst.pnodeStep`) at a
memory outcome, the walk's gate fact for the twin label in TWIN terms, and the related MachCSL state,
and gives the pf's answer, MachCSL's `evStep` with that answer and `rmemP` at the twin's post-state —
through the rows of `Weak/SbRealPHart.lean`:

* `loadLblP` — a plain RAM read (`LLoad`): the walk's top-read gate (`SbReplay.topVals`, stated on the
  twin state as `topValsC`) gives the row's byte premise through `PfStepTsoMem.histOfTop` (the twin's
  latest byte IS the top of the pf projection);
* `storeLblP` — a plain RAM write (`LStore`): the pf's bytes `wbytes n v` are the write's (`bytesOfGet`);
* `mmioReadLblP` / `mmioWriteLblP` — an MMIO access (`LDev`), the device state the pf's (`R-dev` at
  equality off the capture segment; the general `diskSide` form is `SimRelP`'s).

Spec: FAITHFUL (proof organisation).  Lean-only helpers `SbRealPLbl.*`.
-/
import Weak.SbRealPHart
import Weak.SbReplay

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D
open Lbl PfStepTsoMem SbRealP SbRealPHart

namespace SbRealPLbl

/-- The walk's top-read gate (`SbReplay.topVals`) read on a twin state. -/
def topValsC (c : SbCand.CandS) (x : Nat) (base : Int) (vs : List (BitVec 8)) : Prop :=
  ∀ j v, vs[j]? = some v →
    SbCand.fwdByte (c.sb x) (accAddr base j) = some v ∨
    (SbCand.fwdByte (c.sb x) (accAddr base j) = none ∧
      ∃ t, latest c.ms.msImg c.ms.msLog (accAddr base j) t ∧
        logByte c.ms.msImg c.ms.msLog t (accAddr base j) = some v)

theorem topValsCOf (w : SbWalk.WS) (x : Nat) (base : Int) (vs : List (BitVec 8)) :
    SbReplay.topVals w x base vs → topValsC w.σ x base vs := id

/-- The twin's latest byte is the top of the pf projection. -/
theorem topByteOfLatest (img : Image) (log : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8)
    (hl : latest img log a t) (hv : logByte img log t a = some v) : topByte img log a = some v :=
  (histOfTop img log a v).2 ⟨t, hl, hv⟩

/-- **THE REALIZING PLAIN READ**: the pf node step of a plain RAM read with label `LLoad`, whose bytes pass
the walk's top-read gate at the twin state, is MachCSL's plain read at the landed top (`evLoadP`). -/
theorem loadLblP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : (Outcome.memRead (Register := Register) (RegisterType := RegisterType) n va req).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc)
    (hst : pnodeStep (.impure (.ok (.memRead n va req)) k) rs ib d (.LLoad aq lat base tvs asrc) m' ors fn'
      d' oib obar)
    (hR : rmemP img c σ) (hram : devAddr req.pa = false → ramBytes req.pa n)
    (htop : topValsC c (hartAgent cpu) base (tvs.map Prod.snd)) (ts : List Nat) :
    ∃ w : BitVec (8 * n), m' = k (.Ok (w, none)) ∧
      evStep cpu (.memRead n va req) σ (.Ok (w, none)) (σ.afterLoad cpu req.pa n σ.ltop) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LLoad aq base ts (tvs.map Prod.snd)))
        (σ.afterLoad cpu req.pa n σ.ltop) := by
  simp only [pnodeStep] at hst
  split at hst
  · obtain ⟨w, -, h, -⟩ := hst; cases h
  · rename_i hda
    have hda' : devAddr req.pa = false := by simpa using hda
    rcases hst with ⟨-, w, tvs', -, -, h, -⟩ | ⟨hif, ⟨hlat, w, tvs', hlen, hb, hl, hm, -⟩ | ⟨-, w, tvs', -, -, h, -⟩⟩
    · cases h
    · injection hl with h1 h2 h3 h4 h5
      subst h3 h4
      have hram' := hram hda'
      have hnw := noWrapOfRam req.pa n hram'
      refine ⟨w, hm, ?_⟩
      have hpl : akPlain req.access_kind = true := by
        have h1 : akIfetch req.access_kind = false := hif
        have h2 : akExcl req.access_kind = false := hlat
        simp [akPlain, h1, h2]
      refine evLoadP img c σ cpu n va req w aq (paZ req.pa) ts (tvs.map Prod.snd) hR hram' hpl req.pa rfl
        (fun j hj => ?_)
      rw [paZAddJ req.pa n j hnw hj]
      have himg : c.ms.msImg = img := hR.1
      rcases htop j (nthByte w j) (hb j hj) with h | ⟨hn, t, hlt, hv⟩
      · rw [h]; rfl
      · rw [← himg, hn, topByteOfLatest _ _ _ t _ hlt hv]; rfl
    · cases h

/-- **THE REALIZING PLAIN WRITE**: the pf node step of a plain RAM write with label `LStore` is MachCSL's
issue (`evStoreP`), the twin's `LStore` with the pf's bytes. -/
theorem storeLblP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : (Outcome.memWrite (Register := Register) (RegisterType := RegisterType) n va req).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (hst : pnodeStep (.impure (.ok (.memWrite n va req)) k) rs ib d (.LStore rl base data asrc vsrc) m'
      ors fn' d' oib obar)
    (hR : rmemP img c σ) (hram : devAddr req.pa = false → ramBytes req.pa n) (kc : WmClass) :
    ∃ w : BitVec (8 * n), m' = k (.Ok (some true)) ∧ rl = akAcq req.access_kind ∧
      base = paZ req.pa ∧ data = WeakInterpProj.wbytes n w ∧
      evStep cpu (.memWrite n va req) σ (.Ok (some true)) (σ.issue cpu req.pa n w) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LStore false (paZ req.pa) data kc))
        (σ.issue cpu req.pa n w) := by
  simp only [pnodeStep] at hst
  split at hst
  · split at hst
    · obtain ⟨-, h, -⟩ := hst; cases h
    · exact hst.elim
  · rename_i hda
    have hda' : devAddr req.pa = false := by simpa using hda
    split at hst
    · rename_i v hv
      obtain ⟨-, ⟨hlat, hl, hm, -⟩ | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩⟩ := hst
      · injection hl with h1 h2 h3 h4 h5
        subst h1 h2 h3
        have hram' := hram hda'
        have hlen : (WeakInterpProj.wbytes n v).length = n := wbytesLength n v
        have hb : ∀ j, j < n → (WeakInterpProj.wbytes n v)[j]? = some (nthByte v j) :=
          fun j hj => wbytesLookup n v j hj
        obtain ⟨hev, hRm⟩ := evStoreP img c σ cpu n va req v (WeakInterpProj.wbytes n v) kc hR hram' hlat hv
          hlen hb
        exact ⟨v, hm, rfl, rfl, rfl, hev, hRm⟩
      · cases h
      · cases h
    · exact hst.elim

/-- **THE REALIZING MMIO READ**: label `LDev .rd`, the device answer the pf's (devices EQUAL). -/
theorem mmioReadLblP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : (Outcome.memRead (Register := Register) (RegisterType := RegisterType) n va req).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (kd : IoKind) (base : Int) (vs : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (hst : pnodeStep (.impure (.ok (.memRead n va req)) k) rs ib σ.devs (.LDev kd base vs asrc vsrc) m'
      ors fn' d' oib obar)
    (hR : rmemP img c σ) (hdev : devAddr req.pa = true → devBytes req.pa n) (kd' : IoKind) (base' : Int)
    (vs' : List (BitVec 8)) :
    ∃ w : BitVec (8 * n), m' = k (.Ok (w, none)) ∧
      evStep cpu (.memRead n va req) σ (.Ok (w, none)) { σ with devs := d' } ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LIo kd' base' vs')) { σ with devs := d' } := by
  simp only [pnodeStep] at hst
  split at hst
  · rename_i hda
    obtain ⟨w, hrd, -, hm, -⟩ := hst
    obtain ⟨hev, hRm⟩ := evMmioReadP img c σ cpu n va req w d' kd' base' vs' hR (hdev hda) hrd
    exact ⟨w, hm, hev, hRm⟩
  · rcases hst with ⟨-, w, tvs', -, -, h, -⟩ | ⟨-, ⟨-, w, tvs', -, -, h, -⟩ | ⟨-, w, tvs', -, -, h, -⟩⟩ <;>
      cases h

/-- **THE REALIZING MMIO WRITE**: label `LDev .wr`, the device move the pf's; the `DRIVER_OK` guard from
the I/O gate's empty buffer ([OWN.152]). -/
theorem mmioWriteLblP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : (Outcome.memWrite (Register := Register) (RegisterType := RegisterType) n va req).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (kd : IoKind) (base : Int) (vs : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (hst : pnodeStep (.impure (.ok (.memWrite n va req)) k) rs ib σ.devs (.LDev kd base vs asrc vsrc) m'
      ors fn' d' oib obar)
    (hR : rmemP img c σ) (hdev : devAddr req.pa = true → devBytes req.pa n)
    (hemp : c.sb (hartAgent cpu) = []) (kd' : IoKind) (base' : Int) (vs' : List (BitVec 8)) :
    m' = k (.Ok (some true)) ∧
      evStep cpu (.memWrite n va req) σ (.Ok (some true)) { σ with devs := d' } ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LIo kd' base' vs')) { σ with devs := d' } := by
  simp only [pnodeStep] at hst
  split at hst
  · rename_i hda
    split at hst
    · rename_i v hv
      obtain ⟨hwr, -, hm, -⟩ := hst
      obtain ⟨hev, hRm⟩ := evMmioWriteP img c σ cpu n va req v d' kd' base' vs' hR (hdev hda) hv hwr hemp
      exact ⟨hm, hev, hRm⟩
    · exact hst.elim
  · split at hst
    · obtain ⟨-, ⟨-, h, -⟩ | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩⟩ := hst <;> cases h
    · exact hst.elim

/-- **THE REALIZING BARRIER**: the pf node step of a barrier (label `ebarLabel b`) is MachCSL's fence
(`evFenceP`): every kind but `fence.tso`, its drain from the twin's, `fence.i`'s from the walk's gate. -/
theorem fenceLblP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (b : barrier_kind)
    (k : (Outcome.barrier (Register := Register) (RegisterType := RegisterType) b).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind)
    (hst : pnodeStep (.impure (.ok (.barrier b)) k) rs ib d l m' ors fn' d' oib obar)
    (pr pw sr sw : Bool) (hl : l = .LFence pr pw sr sw) (hR : rmemP img c σ)
    (htso : b ≠ .Barrier_RISCV_tso)
    (hdr : SbCand.drains pw sr = true → c.sb (hartAgent cpu) = [])
    (hfi : fenceIfetch b = true → σ.sb cpu = []) :
    m' = k () ∧ fn' = ebarPark b ∧ evStep cpu (.barrier b) σ () (σ.fence cpu b) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LFence pr pw sr sw)) (σ.fence cpu b) := by
  obtain ⟨hl', hm, -, hfn, -⟩ := hst
  rw [hl] at hl'
  obtain ⟨hev, hRm⟩ := evFenceP img c σ cpu b pr pw sr sw hR htso hl'.symm hdr hfi
  exact ⟨hm, hfn, hev, hRm⟩

/-- The AMO gate's read bytes in twin terms: every byte is the twin's LATEST byte (`rmwLatest`). -/
def latestValsC (c : SbCand.CandS) (base : Int) (vs : List (BitVec 8)) : Prop :=
  ∀ j v, vs[j]? = some v → ∃ t, latest c.ms.msImg c.ms.msLog (accAddr base j) t ∧
    logByte c.ms.msImg c.ms.msLog t (accAddr base j) = some v

/-- **THE REALIZING EXCLUSIVE READ** (the pair's first half, label `LExLoad`): MachCSL's exclusive read
at the landed top (`evExReadP`), the pair relation `rmemPMid` after it. -/
theorem exReadLblP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : (Outcome.memRead (Register := Register) (RegisterType := RegisterType) n va req).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc)
    (hst : pnodeStep (.impure (.ok (.memRead n va req)) k) rs ib d (.LExLoad aq base tvs asrc) m' ors fn'
      d' oib obar)
    (hR : rmemP img c σ) (hram : devAddr req.pa = false → ramBytes req.pa n)
    (hlat : latestValsC c base (tvs.map Prod.snd))
    (hamo : SbCand.amoOk (c.sb (hartAgent cpu)) (paZ req.pa) n) :
    ∃ w : BitVec (8 * n), m' = k (.Ok (w, none)) ∧ base = paZ req.pa ∧
      evStep cpu (.memRead n va req) σ (.Ok (w, none)) (σ.afterExcl cpu req.pa n w (akAcq req.access_kind)) ∧
      rmemPMid img c (σ.afterExcl cpu req.pa n w (akAcq req.access_kind)) cpu req.pa n w
        (akAcq req.access_kind) := by
  simp only [pnodeStep] at hst
  split at hst
  · obtain ⟨w, -, h, -⟩ := hst; cases h
  · rename_i hda
    have hda' : devAddr req.pa = false := by simpa using hda
    rcases hst with ⟨-, w, tvs', -, -, h, -⟩ | ⟨-, ⟨-, w, tvs', -, -, h, -⟩ | ⟨hx, w, tvs', hlen, hb, hl, hm, -⟩⟩
    · cases h
    · cases h
    · injection hl with h1 h2 h3 h4
      subst h2 h3
      have hram' := hram hda'
      have hnw := noWrapOfRam req.pa n hram'
      have himg : c.ms.msImg = img := hR.1
      have htop : σ.mem.topBytesL σ.lp req.pa n w := topBytesOfTwin img c σ hR req.pa n w hram' (fun j hj => by
        rw [paZAddJ req.pa n j hnw hj]
        obtain ⟨t, hlt, hv⟩ := hlat j (nthByte w j) (hb j hj)
        rw [← himg]; exact topByteOfLatest _ _ _ t _ hlt hv)
      obtain ⟨hev, hM⟩ := evExReadP img c σ cpu n va req w hR hram' hx htop hamo
      exact ⟨w, hm, rfl, hev, hM⟩

/-- **THE REALIZING EXCLUSIVE WRITE** (the pair's second half, label `LExStore`): MachCSL's write landing
at once (`evExWriteP`); with the read half, the twin's `LRmw`. -/
theorem exWriteLblP (img : Image) (c : SbCand.CandS) (σ : MState) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : (Outcome.memWrite (Register := Register) (RegisterType := RegisterType) n va req).ret → SailM Unit)
    (rs : RegFile) (ib : Ibch) (d : DevStates) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
    (hst : pnodeStep (.impure (.ok (.memWrite n va req)) k) rs ib d (.LExStore rl base data asrc vsrc) m'
      ors fn' d' oib obar)
    (r : BitVec (8 * n)) (acq : Bool) (hM : rmemPMid img c σ cpu req.pa n r acq)
    (hram : devAddr req.pa = false → ramBytes req.pa n)
    (hamo : SbCand.amoOk (c.sb (hartAgent cpu)) (paZ req.pa) n)
    (hrl : akRel req.access_kind = true → c.sb (hartAgent cpu) = [])
    (aq rl' : Bool) (ts : List Nat) (rvs : List (BitVec 8)) (kc : WmClass) :
    ∃ w : BitVec (8 * n), m' = k (.Ok (some true)) ∧ base = paZ req.pa ∧
      data = WeakInterpProj.wbytes n w ∧
      evStep cpu (.memWrite n va req) σ (.Ok (some true)) (σ.storeL cpu req.pa n w) ∧
      rmemP img (SbCand.nextE c (hartAgent cpu) (LRmw aq rl' (paZ req.pa) ts rvs data kc))
        (σ.storeL cpu req.pa n w) := by
  simp only [pnodeStep] at hst
  split at hst
  · split at hst
    · obtain ⟨-, h, -⟩ := hst; cases h
    · exact hst.elim
  · rename_i hda
    have hda' : devAddr req.pa = false := by simpa using hda
    split at hst
    · rename_i v hv
      obtain ⟨-, ⟨-, h, -⟩ | ⟨hx, ⟨hl, hm, -⟩ | ⟨h, -⟩⟩⟩ := hst
      · cases h
      · injection hl with h1 h2 h3 h4 h5
        subst h2 h3
        have hram' := hram hda'
        obtain ⟨hev, hRm⟩ := evExWriteP img c σ cpu n va req r v acq aq rl' ts rvs
          (WeakInterpProj.wbytes n v) kc hM hram' hx hv hamo hrl (wbytesLength n v)
          (fun j hj => wbytesLookup n v j hj)
        exact ⟨v, hm, rfl, rfl, hev, hRm⟩
      · cases h
    · exact hst.elim

#print axioms Weak.SbRealPLbl.loadLblP
#print axioms Weak.SbRealPLbl.storeLblP
#print axioms Weak.SbRealPLbl.mmioReadLblP
#print axioms Weak.SbRealPLbl.mmioWriteLblP
#print axioms Weak.SbRealPLbl.fenceLblP
#print axioms Weak.SbRealPLbl.exReadLblP
#print axioms Weak.SbRealPLbl.exWriteLblP

end SbRealPLbl

end Weak
