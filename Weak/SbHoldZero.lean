/-
Weak: **allocproc route P — [R46.3] `HoldZero`, THE GF SIDE of the `holding+0x12` exemption**
(`notes/weak-allocproc-plan-review-R46.md` §4 "Shared by (a) and (b)", §7 [R46.3]; PROGRESS-P.md
§HEADHOP2 (iii), §HH2A).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing registered imports this file.

**Spec, stated first.**  RVWMO's load-value axiom (per byte: the source is the coherence-latest write
visible to the read — gmo-before it or po-before it, store forwarding) and rule 1 (a same-byte access
po-before a write is gmo-before it) are all this file uses (`SbOrd.CatH`'s `lv` and `ppo`); RVWMO says
nothing about VALUES, so the value facts come from the program: which stores write a live lock's
`lk->cpu` word and with what (the residual interfaces below).  FAITHFUL.

**The argument** (`SbHoldZero.cpuNeOfFloor`).  Row `x`'s `holding+0x12` read `r` (`ld a5,16(a0)`, 8
bytes at `L + 16`) inside `acquire(L)` reads a value other than `&cpus[x]` (`cpuB x`), given a FLOOR `f`
(a write index; 0 = the image) with
  (Z1) `CpuWordWin` — every write of a byte of `[L+16, L+24)` at index ≥ `f` is a hart's plain 8-byte
       store at `L + 16` of 0 or of its writer's own `&cpus[...]` (the cpu-word discipline over the
       lock's LIVE window: `Lk` = live published locks — `kfree`'s 1-fill of a recycled page lies below
       the floor);
  (Z2) `CpuFloor` — every byte of `r` reads at index ≥ `f` (publication), and at `f = 0` the image is 0
       there;
  (Z3) `NotHolder` — every own `&cpus[x]` store to `L + 16` po-before `r` is followed, po-before `r`, by
       an own zero store (`release`'s `sd zero,16(s1)`): `x` does not hold `L` when it calls `acquire(L)`.
Then: (i) all eight bytes have ONE source (every write above the floor covers all eight bytes, so the
co-latest visible one is the same at each — load value's maximality), or all read the image (0);
(ii) the source writes 0 or `cpuB u`; (iii) `u = x` is impossible — the source is po-before `r` (a
po-later own write would be gmo-after `r` by rule 1), so (Z3) gives an own zero store po-between,
which is co-later (rule 1) and visible (po-before `r`): load value's maximality fails; (iv) `cpuB` is
injective on harts and never 0 (`decide +kernel`).

  §1  the residual interfaces (Z1)–(Z3) as definitions;
  §2  the byte-level facts and **`cpuNeOfFloor`**; **`holdZeroOf`** — `SbHeadHop2.HoldZero` at `cpuB`
      from a floor per `acquire`-context read;
  §3  the emission's value at `acquire+0x28` (`sd a0,16(s1)` after `jal mycpu`): **`acqCpuStoreVal`** —
      a store of `stBytes 8 (mycpuRet tp)` with `tp = hartId c` writes `cpuB c` (REUSES
      `AxSpinT2a.mycpuRetHart`), the value half of (Z1) at the pending / unissued acquire stores.

**Who discharges the residuals** (all FAITHFUL; WEAKER only while named):
* (Z1) — REALIZED writes: P-W6's state map + the export twin `lockWordDiscAtP` (`lockRegionOk` /
  `lockWinAtP`: the owner word's entries are 0 or the writer's own `&cpus[c]`); PENDING / UNISSUED writes:
  the realization's label ↔ pc transport (T) for the stores that can write a live lock's `[L+16, L+24)`
  (`acquire+0x28`, `release+0x12`, `initlock` at the floor) + `acqCpuStoreVal` with the emission's
  `a0 = mycpuRet tp` (AxSpinE8's `mycpu` spec) and the `tp = row` invariant at kernel pcs (boot `start`;
  `uservec`'s reload of `kernel_hartid`, the trapframe custody [OWN.77]/[OWN.87]).  No MachCSL record.
* (Z2) — static locks: `f = 0` and the boot image's zero `lk->cpu` (`.bss`; an image fact of `gxImg`);
  pipe locks: `f` = the write index of `initlock`'s `lk->cpu = 0` and CoWR along the publication chain
  (`pipealloc` → `filealloc`'s `ftable.lock` release → the reader's acquire), the kill's `l2ClaimP` kind
  (row 6n).
* (Z3) — P-W6's state map at the realized prefix (row `x`'s events before `r` are realized) + the holder
  fold of the lock's merged word histories (`lockWordDiscAtP`, the same `st` `SbHoldX.NonHolderRd` uses):
  the acquiring hart is not `st`'s holder.  No MachCSL record (R46 §4).
Lean-only helpers `SbHoldZero.*`.
-/
import Weak.SbHoldX

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbReplay

/-! # 1. The residual interfaces -/

/-- Eight zero bytes. -/
def SbHoldZero.zero8 : List (BitVec 8) := List.replicate 8 0#8

/-- **(Z1) THE CPU-WORD DISCIPLINE OVER THE LIVE WINDOW** of the lock at `L` above the floor `f`: every
write of a byte of `[L+16, L+24)` at write index ≥ `f` is a hart's plain 8-byte store at `L + 16` of 0
or of its writer's own `&cpus[...]`. -/
def SbHoldZero.CpuWordWin (G : Gexec) (L : Int) (f : Nat) : Prop :=
  ∀ w a v, L + 16 ≤ a → a < L + 24 → gwritesByte G w a v → f ≤ gwix G w →
    w.1 < NCPU ∧ ∃ rl vs kc, gxLbl G w = some (LStore rl (L + 16) vs kc) ∧
      (vs = SbHoldZero.zero8 ∨ vs = cpuB w.1)

/-- **(Z2) THE FLOOR IS PUBLISHED TO THE READ**: every byte of `r` reads at write index ≥ `f`; at
`f = 0` the image holds 0 at `[L+16, L+24)`. -/
def SbHoldZero.CpuFloor (G : Gexec) (r : Geid) (L : Int) (f : Nat) : Prop :=
  (∀ a t v, greadsByte G r a t v → f ≤ t) ∧
    (f = 0 → ∀ a v, L + 16 ≤ a → a < L + 24 → G.gxImg a = some v → v = 0#8)

/-- **(Z3) THE READER DOES NOT HOLD THE LOCK**: every own store of `&cpus[r.1]` to `L + 16` po-before
`r` is followed, po-before `r`, by an own zero store to `L + 16`. -/
def SbHoldZero.NotHolder (G : Gexec) (r : Geid) (L : Int) : Prop :=
  ∀ w rl kc, WeakRvwmoGraph.gpo G w r → gxLbl G w = some (LStore rl (L + 16) (cpuB r.1) kc) →
    ∃ z rl' kc', WeakRvwmoGraph.gpo G w z ∧ WeakRvwmoGraph.gpo G z r ∧
      gxLbl G z = some (LStore rl' (L + 16) SbHoldZero.zero8 kc')

/-! # 2. The argument -/

theorem SbHoldZero.cpuBInj : ∀ u x : Fin NCPU, cpuB u.val = cpuB x.val → u = x := by decide +kernel

theorem SbHoldZero.zeroNeCpuB : ∀ x : Fin NCPU, SbHoldZero.zero8 ≠ cpuB x.val := by decide +kernel

theorem SbHoldZero.zero8Length : SbHoldZero.zero8.length = 8 := rfl

/-- Byte `j` of a load label is a read byte. -/
theorem SbHoldZero.rdByte (G : Gexec) (r : Geid) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (j t : Nat) (v : BitVec 8) :
    gxLbl G r = some (LLoad false base ts vs) → ts[j]? = some t → vs[j]? = some v →
    greadsByte G r (base + j) t v :=
  fun hl ht hv => ⟨_, base, ts, vs, j, hl, rfl, ht, hv, rfl⟩

/-- Byte `j` of a store label is a written byte. -/
theorem SbHoldZero.wrByte (G : Gexec) (w : Geid) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (kc : WmClass) (j : Nat) (v : BitVec 8) :
    gxLbl G w = some (LStore rl base vs kc) → vs[j]? = some v → gwritesByte G w (base + j) v :=
  fun hl hv => ⟨_, base, vs, j, hl, rfl, hv, rfl⟩

/-- A written byte of a store at `base` is its byte at the offset. -/
theorem SbHoldZero.wrByteInv (G : Gexec) (w : Geid) (rl : Bool) (base : Int) (vs : List (BitVec 8))
    (kc : WmClass) (j : Nat) (v : BitVec 8) :
    gxLbl G w = some (LStore rl base vs kc) → gwritesByte G w (base + j) v → vs[j]? = some v := by
  rintro hl ⟨l, b', vs', j', hl', hwr, hv, ha⟩
  rw [hl, Option.some.injEq] at hl'
  subst hl'
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
  obtain ⟨rfl, rfl⟩ := hwr
  have : j' = j := by unfold accAddr at ha; omega
  subst this
  exact hv

/-- **THE READ IS NOT THE HOLDER'S OWN POINTER** (the floor argument, see the header). -/
theorem SbHoldZero.cpuNeOfFloor (G : Gexec) (hc : SbOrd.CatH G) (r : Geid) (L : Int) (f : Nat)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : gxLbl G r = some (LLoad false (L + 16) ts vs))
    (h8 : ts.length = 8) (hr : r.1 < NCPU)
    (hW : SbHoldZero.CpuWordWin G L f) (hF : SbHoldZero.CpuFloor G r L f)
    (hN : SbHoldZero.NotHolder G r L) : vs ≠ cpuB r.1 := by
  have hnd : G.gxGmo.Nodup := hc.wf.1
  have hvl : vs.length = 8 := by rw [SbOrd.lblShapeLd G hc.wf _ _ _ _ _ hl, h8]
  -- the per-byte data
  have hbt : ∀ j, j < 8 → ∃ t v, ts[j]? = some t ∧ vs[j]? = some v :=
    fun j hj => ⟨ts[j]'(by omega), vs[j]'(by omega), List.getElem?_eq_getElem _,
      List.getElem?_eq_getElem _⟩
  -- a write above the floor covering one byte of the word covers all eight
  have hcov : ∀ w a v, L + 16 ≤ a → a < L + 24 → gwritesByte G w a v → f ≤ gwix G w →
      ∃ rl vs8 kc, gxLbl G w = some (LStore rl (L + 16) vs8 kc) ∧ vs8.length = 8 ∧
        (vs8 = SbHoldZero.zero8 ∨ vs8 = cpuB w.1) := by
    intro w a v h1 h2 hw hf
    obtain ⟨-, rl, vs8, kc, hlw, hv8⟩ := hW w a v h1 h2 hw hf
    refine ⟨rl, vs8, kc, hlw, ?_, hv8⟩
    rcases hv8 with rfl | rfl
    · rfl
    · exact SbHoldX.cpuBLength w.1
  -- (i) the sources: every byte's index is ≤ every other byte's
  have hle : ∀ j k tj tk vj vk, j < 8 → k < 8 → ts[j]? = some tj → ts[k]? = some tk →
      vs[j]? = some vj → vs[k]? = some vk → tj ≤ tk := by
    intro j k tj tk vj vk hj hk htj htk hvj hvk
    cases tj with
    | zero => omega
    | succ i =>
      have hrj := SbHoldZero.rdByte G r _ ts vs j _ vj hl htj hvj
      obtain ⟨⟨w, hwa, hwb, hwv⟩, -⟩ := hc.lv r _ _ vj hrj
      have hfi : f ≤ i + 1 := hF.1 _ _ _ hrj
      have hgw : gwix G w = i + 1 := (gwriteAtInv G _ w hnd hwa).2
      obtain ⟨rl, vs8, kc, hlw, hl8, -⟩ := hcov w _ vj (by omega) (by omega) hwb (by omega)
      have hk8 : k < vs8.length := by omega
      have hwk := SbHoldZero.wrByte G w rl (L + 16) vs8 kc k (vs8[k]'hk8) hlw
        (List.getElem?_eq_getElem hk8)
      have hrk := SbHoldZero.rdByte G r _ ts vs k _ vk hl htk hvk
      have := (hc.lv r _ _ vk hrk).2 w _ hwk hwv
      omega
  -- one index for all bytes
  obtain ⟨t0, v0, ht0, hv0⟩ := hbt 0 (by omega)
  have hall : ∀ j t v, j < 8 → ts[j]? = some t → vs[j]? = some v → t = t0 :=
    fun j t v hj ht hv => Nat.le_antisymm (hle j 0 t t0 v v0 hj (by omega) ht ht0 hv hv0)
      (hle 0 j t0 t v0 v (by omega) hj ht0 ht hv0 hv)
  intro hcpu
  have hx : r.1 < NCPU := hr
  cases t0 with
  | zero =>
    -- every byte reads the image: zero
    have hf0 : f = 0 := by have := hF.1 _ _ _ (SbHoldZero.rdByte G r _ ts vs 0 _ v0 hl ht0 hv0); omega
    have hz : vs = SbHoldZero.zero8 := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < 8
      · obtain ⟨t, v, ht, hv⟩ := hbt j hj
        have := hall j t v hj ht hv
        subst this
        have hrj := SbHoldZero.rdByte G r _ ts vs j _ v hl ht hv
        have him := (hc.lv r _ _ v hrj).1
        have hv' := hF.2 hf0 _ v (by omega) (by omega) him
        rw [hv, hv']
        show some 0#8 = (List.replicate 8 0#8)[j]?
        rw [List.getElem?_replicate, if_pos hj]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [SbHoldZero.zero8]; omega)]
    exact SbHoldZero.zeroNeCpuB ⟨r.1, hx⟩ (hz.symm.trans hcpu)
  | succ i =>
    -- one source write `w` for all bytes
    have hr0 := SbHoldZero.rdByte G r _ ts vs 0 _ v0 hl ht0 hv0
    obtain ⟨⟨w, hwa, hwb, hwv⟩, -⟩ := hc.lv r _ _ v0 hr0
    have hgw : gwix G w = i + 1 := (gwriteAtInv G _ w hnd hwa).2
    have hfi : f ≤ i + 1 := hF.1 _ _ _ hr0
    obtain ⟨rl, vs8, kc, hlw, hl8, hv8⟩ := hcov w _ v0 (by omega) (by omega) hwb (by omega)
    have heq : vs = vs8 := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < 8
      · obtain ⟨t, v, ht, hv⟩ := hbt j hj
        have := hall j t v hj ht hv
        subst this
        have hrj := SbHoldZero.rdByte G r _ ts vs j _ v hl ht hv
        obtain ⟨⟨w', hwa', hwb', -⟩, -⟩ := hc.lv r _ _ v hrj
        rw [hwa, Option.some.injEq] at hwa'
        subst hwa'
        rw [hv, SbHoldZero.wrByteInv G w rl (L + 16) vs8 kc j v hlw hwb']
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    subst heq
    rcases hv8 with h0 | hc'
    · exact SbHoldZero.zeroNeCpuB ⟨r.1, hx⟩ (h0.symm.trans hcpu)
    · -- the source wrote its writer's pointer: the writer is `r`'s own hart
      have hwx : w.1 < NCPU := (hW w _ v0 (by omega) (by omega) hwb (by omega)).1
      have hu : w.1 = r.1 := by
        have := SbHoldZero.cpuBInj ⟨w.1, hwx⟩ ⟨r.1, hx⟩ (hc'.symm.trans hcpu)
        exact congrArg Fin.val this
      have hlw' : gxLbl G w = some (LStore rl (L + 16) (cpuB r.1) kc) := by
        rw [hlw, hc', hu]
      -- the source is po-before `r`
      have hpo : WeakRvwmoGraph.gpo G w r := by
        rcases hwv with hgm | hpo
        · refine ⟨hu, ?_, by rw [hlw]; rfl, by rw [hl]; rfl⟩
          rcases Nat.lt_trichotomy w.2 r.2 with h | h | h
          · exact h
          · exfalso
            have : w = r := Prod.ext hu h
            rw [this, hl] at hlw
            cases hlw
          · exfalso
            have hpo' : WeakRvwmoGraph.gpo G r w := ⟨hu.symm, h, by rw [hl]; rfl, by rw [hlw]; rfl⟩
            have hlt := SbOrd.rule1Lt G r w _ _ hc.ppo hpo' (.inr ⟨_, _, hr0⟩) hwb
            exact gmoLtIrrefl G r (gmoLtTrans G _ _ _ hlt hgm)
        · exact hpo
      -- (Z3): an own zero store po-between, co-later and visible
      obtain ⟨z, rl', kc', hwz, hzr, hlz⟩ := hN w rl kc hpo hlw'
      have hz0 : gwritesByte G z (L + 16 + (0 : Nat)) 0#8 :=
        SbHoldZero.wrByte G z rl' (L + 16) SbHoldZero.zero8 kc' 0 0#8 hlz rfl
      have hw0 : gwritesByte G w (L + 16 + (0 : Nat)) v0 := hwb
      have hwzg := SbOrd.rule1Lt G w z _ _ hc.ppo hwz (.inl ⟨v0, hw0⟩) hz0
      have hwW := SbOrd.gwritesOf G w _ v0 hc.wf hw0
      have hzW := SbOrd.gwritesOf G z _ _ hc.wf hz0
      have hlt : gwix G w < gwix G z := (gwixGposLt G w z hnd hwW hzW).2 hwzg.2.2
      have hmax := (hc.lv r _ _ v0 hr0).2 z _ hz0 (.inr hzr)
      omega

/-- **`HoldZero` FROM THE FLOOR DECOMPOSITION**: at every `acquire`-context `holding+0x12` read (an
8-byte `LLoad` at `L + 16` of a hart row) with a floor meeting (Z1)–(Z3), `SbHeadHop2.HoldZero` holds at
`cpuB`. -/
theorem SbHoldZero.holdZeroOf (G : Gexec) (hc : SbOrd.CatH G) (AcqCpuRd : Geid → Int → Prop)
    (hA : ∀ r L base ts vs, AcqCpuRd r L → gxLbl G r = some (LLoad false base ts vs) → base = L + 16 →
      ts.length = 8 ∧ r.1 < NCPU ∧ ∃ f, SbHoldZero.CpuWordWin G L f ∧ SbHoldZero.CpuFloor G r L f ∧
        SbHoldZero.NotHolder G r L) :
    SbHeadHop2.HoldZero G cpuB AcqCpuRd := by
  intro r L base ts vs hacq hl hb
  obtain ⟨h8, hr, f, hW, hF, hN⟩ := hA r L base ts vs hacq hl hb
  subst hb
  exact SbHoldZero.cpuNeOfFloor G hc r L f ts vs hl h8 hr hW hF hN

/-! # 3. The emission's value at `acquire+0x28` -/

/-- **THE ACQUIRE STORE'S VALUE** (`acquire+0x28`, `sd a0,16(s1)` after `jal mycpu`): its data is
`stBytes 8 a0` with `a0 = mycpuRet tp` (AxSpinE8's `mycpu` spec), and at `tp = hartId c` (the kernel-pc
invariant) that is `cpuB c` — `AxSpinT2a.mycpuRetHart` + `SbHoldX.cpuBStBytes`. -/
theorem SbHoldZero.acqCpuStoreVal (c : CPU) (tp : BitVec 64) (vs : List (BitVec 8)) :
    tp = hartId c → vs = stBytes 8 (AxSpinE8.mycpuRet tp) → vs = cpuB c.val := by
  rintro rfl rfl
  rw [AxSpinT2a.mycpuRetHart c, SbHoldX.cpuBStBytes c]

end Weak
