/-
Weak: **the S-R `DomAt` lift, increment I-7 — `SbHoldR`, the census `NoAqLd` and the discharge of `ExValMin`**
(ruling [OWN.150]; coordinator decision on Q-DomAt-1 (a); `PROGRESS-DomAt.md` F-DomAt-1, F-DomAt-2).
Lean-only, no Rocq twin.  A leaf: nothing registered imports this file.

**REVISIT [OWN.124]** — the `holding+0x12` exemption stays (the owner asked to look at it again).

**Spec, stated first.**
* F-DomAt-1: in this label alphabet a plain acquire load (`LLoad true`) is the access of an `lr.aq`
  (`WeakRvwmoGraph.lbRcsc`'s doc; Sail's `LOAD` decodes `aq = false`).  The kernel text contains NO LR
  word (`imgNoLr`, `decide +kernel` over the text walk, like `SbOrd.imgAmoAq`); `SbOrdR.NoAqLd` is its
  GF form, through the same realization transport (label ↔ instruction) as `SbOrd.ImgFacts`.
* F-DomAt-2: the exempt read's min-rule word.  riscv.cat's load value makes the sources of an 8-byte load
  whose every byte is written only by full 8-byte stores ONE write (or all the image): every byte reads the
  same timestamp (`uniTsOfFloor`, from `SbHoldZero`'s (Z1)/(Z2) residuals — the ones [OWN.124]'s GF side
  already uses).  At an S-P walk state that timestamp is either landed — then no own entry is pending on
  the word and the min-rule word IS GF's (`ExValGF`) — or not — then it IS the landed top (`ExValTop`)
  (`exValMinOf`).  So `ExValMin` needs NO new named input: `exValMinOfHold` derives it from exactly the
  inputs of `SbHoldX.holdCpuExempt` (`CpuTopMap`, `HoldZero`'s residuals, the acquire-context transport),
  with the `ip->ref` halves (`IrefTop`/`IrefGF`, MachCSL Q5/Q6) VACUOUS: under S-R the only exempt reads
  are the 8-byte `holding+0x12` loads.

  §1  `imgNoLr` (the image half of `NoAqLd`).
  §2  `UniTs`, `uniTsOfFloor`.
  §3  **`exValMinOf`**, **`exValMinOfHold`**; the kill-level form `SbKillR.stateIfcCZROf`.

Spec: FAITHFUL.  Lean-only helpers `SbOrdR.*`, `SbKillR.*`.

**ROW H3′'s CENSUS DISCHARGE** (§5–§7, after the `PInv` split `SbOrd.PInvB`; the `…B` lemmas of `SbOrd`,
`SbBlocked`, `SbVirtio`).  riscv.cat's load value: a non-census plain load reads, per byte, the image, an own
write, or a write that a chain of RVWMO ordering facts from the head's realized prefix has LANDED
(`SbBlocked.Hb`; virtio: `SbVirtio.Hv`).  On the top-read walk that made the head pass the value gate
through `PInv.rd`; on the S-R walk the landedness ALONE passes the S-R read gate (`srGate`: an own pending
source is forwarded with GF's value, `ownFwdB`; a landed one is at a GF index inside the landed prefix and
no own entry is pending on the byte, `SbOrdR.noFwdLanded`).  So the census discharge of row H3′ needs, per
census head, "never blocked (`srGate`) or the static write hop (`WrHop`)" — NO (A2) read window: the
`holding+0x0` held-context rows (`SbHeldPin`, a VALUE argument for the top read) are table entries whose
hop is the static `bnez` control hop (`SbHeadHop.holding0CtrlNext` + `wrHopOfCtl`).

  §1  `PInvR.toB`, the landed byte (`byteLandedR`).
  §2  `srGateOfClsR` / `srGateOfClsVR` (the S-R gate from the source classes), `blockedIsCensusRC`,
      the PTE rows `pteNeverBlockedR`, the virtio rows `virtioTableR`.
  §3  **`headOrdWOfCensus`**, **`headOrdWOfCensusP`**: `HeadOrdW` from the transport `NonCensusSrc`, PTE
      custody `PteCustSrc` and the census table (`srGate ∨ WrHop`).

-/
import Weak.SbKillR
import Weak.SbHoldZero
import Weak.SbPteCust
import Weak.SbVirtio

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd SpikeSP SbDom

namespace SbOrdR

/-! # 1. The image half of `NoAqLd` -/

/-- **NO LR WORD IN THE KERNEL TEXT** (the image half of `NoAqLd`, F-DomAt-1): no instruction word of the
text walk is an LR (`lr.w`/`lr.d`, opcode `0101111`, funct5 `00010`) — the only acquire LOADS of this
alphabet.  (xv6's only atomic is `acquire`'s `amoswap.w.aq`, `LockFacts.amoCensus`.) -/
theorem imgNoLr : textPcs.all (fun p => !wIsLr (kw p)) = true := by decide +kernel

/-- The realization's label ↔ instruction transport for an acquire load (as for `SbOrd.ImgFacts`): an
`LLoad true` event is realized by an LR word of the text walk. -/
def AqLdT (G : Gexec) : Prop :=
  ∀ e base ts vs, gxLbl G e = some (LLoad true base ts vs) → ∃ p, p ∈ textPcs ∧ wIsLr (kw p) = true

/-- **`NoAqLd` FROM THE IMAGE**: through the transport, `imgNoLr` excludes every acquire load. -/
theorem noAqLdOfT (G : Gexec) (h : AqLdT G) : NoAqLd G := by
  intro e base ts vs hl
  obtain ⟨p, hp, hlr⟩ := h e base ts vs hl
  have := List.all_eq_true.1 imgNoLr p hp
  simp [hlr] at this

/-! # 2. One timestamp for every byte of an exempt read -/

/-- Every exempt read reads all its bytes at ONE timestamp. -/
def UniTs (G : Gexec) (X : Geid → Prop) : Prop :=
  ∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) →
    ∀ (j k t t' : Nat), ts[j]? = some t → ts[k]? = some t' → t = t'

theorem len8 (x : Nat) (vs : List (BitVec 8)) : vs = SbHoldZero.zero8 ∨ vs = cpuB x → vs.length = 8 := by
  rintro (rfl | rfl)
  · rfl
  · exact SbHoldX.cpuBLength x

/-- **`UniTs` FROM THE FLOOR DECOMPOSITION** (load value + (Z1) "every write of the word above the floor is a
full 8-byte store at `L + 16`" + (Z2) "every byte reads above the floor"): a source of one byte writes every
byte and is visible to the read, so no byte reads below it. -/
theorem uniTsOfFloor (G : Gexec) (hc : CatH G) (X : Geid → Prop) (AcqCpuRd : Geid → Int → Prop)
    (hT : ∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) → AcqCpuRd e (base - 16))
    (hA : ∀ r L base ts vs, AcqCpuRd r L → gxLbl G r = some (LLoad false base ts vs) → base = L + 16 →
      ts.length = 8 ∧ r.1 < NCPU ∧ ∃ f, SbHoldZero.CpuWordWin G L f ∧ SbHoldZero.CpuFloor G r L f ∧
        SbHoldZero.NotHolder G r L) :
    UniTs G X := by
  intro e base ts vs hx hl
  obtain ⟨h8, -, f, hW, hF, -⟩ := hA e (base - 16) base ts vs (hT e base ts vs hx hl) hl (by omega)
  have hlen := lblShapeLd G hc.wf _ _ _ _ _ hl
  have hrd : ∀ j t, ts[j]? = some t → ∃ v, greadsByte G e (accAddr base j) t v := by
    intro j t hj
    have hjv : j < vs.length := by rw [hlen]; exact lookup_lt_Some hj
    exact ⟨vs[j], _, base, ts, vs, j, hl, rfl, hj, List.getElem?_eq_getElem hjv, rfl⟩
  have key : ∀ (j k t t' : Nat), ts[j]? = some t → ts[k]? = some t' → t ≤ t' := by
    intro j k t t' hj hk
    obtain ⟨v, hrj⟩ := hrd j t hj
    obtain ⟨v', hrk⟩ := hrd k t' hk
    have hjl := lookup_lt_Some hj
    have hkl := lookup_lt_Some hk
    cases t with
    | zero => exact Nat.zero_le _
    | succ i =>
      obtain ⟨⟨s, hs, hsw, hvis⟩, -⟩ := hc.lv _ _ _ _ hrj
      obtain ⟨-, hsix⟩ := gwriteAtInv G _ s hc.wf.1 hs
      have hfl := hF.1 _ _ _ hrj
      obtain ⟨-, rl, vs0, kc, hls, hv0⟩ := hW s _ _ (by unfold accAddr; omega) (by unfold accAddr; omega)
        hsw (by omega)
      have h0 := len8 s.1 vs0 hv0
      have hk8 : k < vs0.length := by omega
      have hswk : gwritesByte G s (accAddr base k) vs0[k] :=
        ⟨_, base - 16 + 16, vs0, k, hls, rfl, List.getElem?_eq_getElem hk8, by unfold accAddr; omega⟩
      have := (hc.lv e _ t' v' hrk).2 s _ hswk hvis
      omega
  intro j k t t' hj hk
  exact Nat.le_antisymm (key j k t t' hj hk) (key k j t' t hk hj)

/-! # 3. `ExValMin` -/

section Min

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- At a landed timestamp no own entry is pending on a byte the head reads (the pending entry would be a
visible write of index at most the timestamp, hence landed). -/
theorem noFwdLanded (hP : PInvR N img G X dev w) (hc : CatH G) (x : Nat) (a : Int) (t : Nat)
    (v : BitVec 8) (hrd : greadsByte G (hd w x) a t v) (ht : t ≤ (wrW w).length) :
    SbCand.fwdByte (w.σ.sb x) a = none := by
  cases hf : SbCand.fwdByte (w.σ.sb x) a with
  | none => rfl
  | some u =>
    exfalso
    rcases fwdRel (w.pend x) a with ⟨-, h2⟩ | ⟨p, hp, -, h2, -⟩
    · rw [← hP.inv.sb x, hf] at h2; cases h2
    · rw [← hP.inv.sb x, hf] at h2
      have hsw : gwritesByte G (x, p.1) a u := pendWritesVR hP x p a u hp h2.symm
      have hpr := pendRealizedR hP x p hp
      obtain ⟨rl', base', vs', kc', hl', -, -⟩ := pendLblR hP x p hp
      have hlr : (gxLbl G (hd w x)).isSome := by
        obtain ⟨l, b, ts, vs, j, hl, -⟩ := hrd; rw [hl]; rfl
      have hpo : WeakRvwmoGraph.gpo G (x, p.1) (hd w x) :=
        ⟨rfl, hpr, by rw [hl']; rfl, hlr⟩
      have hle := (hc.lv _ a t v hrd).2 _ u hsw (.inr hpo)
      have hsG := gwritesOf G _ a u hc.wf hsw
      have hin := landedOfIx hP.spw _ _ (gwriteAtGwix G _ hsG) (by omega)
      exact hP.inv.pendGmo x p hp (wrWSub _ hin)

/-- **`ExValMin` FROM THE TWO OLD HALVES** at an S-P walk state, given one timestamp per exempt read: a
landed timestamp makes the min-rule word GF's (`ExValGF`), an unlanded one the landed top (`ExValTop`). -/
theorem exValMinOf (hP : PInvR N img G X dev w) (hc : CatH G) (himg : G.gxImg = img) (hU : UniTs G X)
    (hGF : ExValGF G X) (hTop : ExValTop G X w) : ExValMin G X w := by
  intro x base ts vs vs' hx hl hlen' hmin
  have hlen := lblShapeLd G hc.wf _ _ _ _ _ hl
  by_cases hall : ∀ (j t : Nat), ts[j]? = some t → t ≤ (wrW w).length
  · have hvs : vs' = vs := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < ts.length
      · have hjv : j < vs.length := by rw [hlen]; exact hj
        have hjv' : j < vs'.length := by rw [hlen']; exact hj
        obtain ⟨t, htj⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem hj⟩
        have hrd : greadsByte G (hd w x) (accAddr base j) t vs[j] :=
          ⟨_, base, ts, vs, j, hl, rfl, htj, List.getElem?_eq_getElem hjv, rfl⟩
        have hland := hall j t htj
        rw [List.getElem?_eq_getElem hjv, List.getElem?_eq_getElem hjv']
        rcases hmin j vs'[j] (List.getElem?_eq_getElem hjv') with h | ⟨-, t', htj', hlb⟩
        · rw [noFwdLanded hP hc x _ t _ hrd hland] at h; cases h
        · rw [htj, Option.some.injEq] at htj'
          subst htj'
          rw [if_pos hland] at hlb
          obtain ⟨hv1, -⟩ := SpikeSR.staleStep img G X w hP.inv hP.pf hP.spw hc.wf.1 hc.lv himg _ _ t _ hrd
            hland 0 (fun n u hn _ => SbOrd.gwixPos G n (gwritesOf G n _ u hc.wf hn))
          rw [hP.inv.img, hv1] at hlb
          exact hlb.symm
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    obtain ⟨b0, ts0, vs0, he, hex⟩ := hGF _ _ hx hl
    simp only [LLoad.injEq] at he
    obtain ⟨-, -, -, rfl⟩ := he
    rw [hvs]; exact hex
  · obtain ⟨j0, t0, hj0, ht0⟩ : ∃ j t, ts[j]? = some t ∧ (wrW w).length < t := by
      refine Classical.byContradiction (fun hn => hall (fun j t h => ?_))
      exact Nat.le_of_not_lt (fun hlt => hn ⟨j, t, h, hlt⟩)
    refine hTop x base ts vs vs' hx hl hlen' (fun j v' hv' => ?_)
    rcases hmin j v' hv' with h | ⟨hn, t, htj, hlb⟩
    · exact .inl h
    · have : t = t0 := hU _ base ts vs hx hl j j0 t t0 htj hj0
      rw [if_neg (by omega)] at hlb
      exact .inr ⟨hn, _, latestTsLatest _ _ _ (by rw [hlb]; rfl), hlb⟩

/-- **REVISIT [OWN.124]**.  **`ExValMin` FROM [OWN.124]'s OWN INPUTS** (`SbHoldX.holdCpuExempt`'s, with the
`ip->ref` halves vacuous): every exempt read is an acquire-context `holding+0x12` read (the transport `hT`),
the floor residuals of `SbHoldZero.holdZeroOf` (`hA`), and P-W6's `CpuTopMap` at the state. -/
theorem exValMinOfHold (hP : PInvR N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (AcqCpuRd : Geid → Int → Prop)
    (hXL : ∀ e l, X e → gxLbl G e = some l → ∃ base ts vs, l = LLoad false base ts vs)
    (hT : ∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) → AcqCpuRd e (base - 16))
    (hA : ∀ r L base ts vs, AcqCpuRd r L → gxLbl G r = some (LLoad false base ts vs) → base = L + 16 →
      ts.length = 8 ∧ r.1 < NCPU ∧ ∃ f, SbHoldZero.CpuWordWin G L f ∧ SbHoldZero.CpuFloor G r L f ∧
        SbHoldZero.NotHolder G r L)
    (hCT : SbHoldX.CpuTopMap G X w) : ExValMin G X w := by
  have h8 : ∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) → ts.length = 8 :=
    fun e base ts vs hx hl => (hA e (base - 16) base ts vs (hT e base ts vs hx hl) hl (by omega)).1
  have hIT : IrefTop G X w := fun x base ts vs vs' hx hl _ h4 _ => by
    have := h8 _ base ts vs hx hl; omega
  have hIG : IrefGF G X := fun e base ts vs hx hl h4 => by
    have := h8 e base ts vs hx hl
    have := lblShapeLd G hc.wf _ _ _ _ _ hl; omega
  obtain ⟨hTop, hGF, -, -⟩ := SbHoldX.holdCpuExempt G X w AcqCpuRd hXL hIT hCT hIG
    (fun e base ts vs hx hl _ => hT e base ts vs hx hl) (SbHoldZero.holdZeroOf G hc AcqCpuRd hA)
  exact exValMinOf hP hc himg (uniTsOfFloor G hc X AcqCpuRd hT hA) hGF hTop

end Min

end SbOrdR

/-! # 4. The kill-level form -/

/-- **`stateIfcCZR` FROM ROW H3′ AND [OWN.124]'s INPUTS** (REVISIT [OWN.124]): the min-rule exempt value is
no longer a separate named input. -/
theorem SbKillR.stateIfcCZROf (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (AcqCpuRd : Gfexec → Geid → Int → Prop)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof)
    (hT : ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      (∀ e base ts vs, Xof GF e → gxLbl GF.gfGd.gdG e = some (LLoad false base ts vs) →
        AcqCpuRd GF e (base - 16)) ∧
      (∀ r L base ts vs, AcqCpuRd GF r L → gxLbl GF.gfGd.gdG r = some (LLoad false base ts vs) →
        base = L + 16 → ts.length = 8 ∧ r.1 < NCPU ∧ ∃ f, SbHoldZero.CpuWordWin GF.gfGd.gdG L f ∧
          SbHoldZero.CpuFloor GF.gfGd.gdG r L f ∧ SbHoldZero.NotHolder GF.gfGd.gdG r L))
    (hS : ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF →
      ∀ c, validW SbPol.epoch c → SbOrdR.gatedWR GF.gfGd.gdG (Xof GF) GF.gfDev c → c.img = im →
        SbOrdR.PInvR GF.gfGd.gdG.gxProg.length im GF.gfGd.gdG (Xof GF) GF.gfDev (SbWalk.cur c) →
        SbOrdR.HeadOrdW GF.gfGd.gdG (Xof GF) GF.gfDev (SbWalk.cur c) ∧ SbHoldX.CpuTopMap GF.gfGd.gdG (Xof GF) (SbWalk.cur c)) :
    SbKillR.stateIfcCZR boot d0 fab im Xof := by
  intro GF ad him hc hconf hres c hv hg hci hP
  obtain ⟨hH, hCT⟩ := hS GF ad him hc hconf hres c hv hg hci hP
  obtain ⟨-, hXL, -⟩ := hW.1 GF ad him hc hconf
  obtain ⟨hT1, hA⟩ := hT GF ad him hc hconf
  exact ⟨hH, SbOrdR.exValMinOfHold hP ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩ him (AcqCpuRd GF) hXL hT1 hA hCT⟩

namespace SbOrdR

/-! # 5. The census discharge of row H3′ -/

/-! ## 5.1 The base view of `PInvR` -/

theorem PInvR.toB {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}
    (hP : PInvR N img G X dev w) : PInvB N img G X dev w :=
  ⟨hP.inv, hP.pf, hP.ex, hP.len, hP.ag, hP.dvP, hP.ord, hP.fs0, hP.fs2, hP.nrl⟩

section Cls

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- A byte whose GF source is the image or a LANDED write is inside the landed prefix and not forwarded. -/
theorem byteLandedR (hP : PInvR N img G X dev w) (hc : CatH G) (x : Nat) (a : Int) (t : Nat)
    (v : BitVec 8) (hrd : greadsByte G (hd w x) a t v)
    (hL : t = 0 ∨ ∃ s, gwriteAt G t = some s ∧ SbBlocked.Landed w s) :
    SbCand.fwdByte (w.σ.sb x) a = none ∧ t ≤ (wrW w).length := by
  have ht : t ≤ (wrW w).length := by
    rcases hL with rfl | ⟨s, hs, hsL⟩
    · exact Nat.zero_le _
    · obtain ⟨hsG, hsix⟩ := gwriteAtInv G t s hc.wf.1 hs
      have hsW : gisW G s = true := ((gwritesElemOf G s).1 hsG).2
      have hsm := SbBlocked.landedGmoB hP.toB s hsL hsW
      have hsw : s ∈ wrW w := List.mem_filter.2 ⟨hsm, by
        obtain ⟨l', hl', -⟩ := hP.inv.gmoMem s hsm
        obtain ⟨l, hlg, hrel⟩ := hP.pf.1 s.1 s.2 l' hl'
        unfold rwW; rw [hl']; show lbIsW l' = true; rw [relXIsW _ l l' hrel]
        unfold gisW at hsW; rw [show gxLbl G s = gxLbl G (s.1, s.2) from rfl, hlg] at hsW; exact hsW⟩
      have := wixLeOfPfx _ s hc.wf.1 hP.spw hsw
      omega
  exact ⟨noFwdLanded hP hc x a t v hrd ht, ht⟩

/-- **THE S-R GATE FROM THE SOURCE CLASSES** (`SbBlocked.srcGateOfCls` without `PInv.rd`). -/
theorem srGateOfClsR (hP : PInvR N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad false base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd w x) a t v → SbBlocked.SrcCls G dev (hd w x) t) :
    srGate G w x false base ts vs := by
  intro j t v htj hvj
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have landed : (t = 0 ∨ ∃ s, gwriteAt G t = some s ∧ SbBlocked.Landed w s) →
      SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
        (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ t ≤ (wrW w).length ∧
          (false = true → ∀ s, gwriteAt G t = some s → s.1 = x → gmoLt G s (hd w x))) := by
    intro hL
    obtain ⟨h1, h2⟩ := byteLandedR hP hc x _ t v hrd hL
    exact .inr ⟨h1, h2, fun h => by cases h⟩
  rcases hcls _ t v hrd with h0 | ⟨s, hs, hown | hhb⟩
  · exact landed (.inl h0)
  · have hsx : s.1 = x := hown
    by_cases hpen : ∃ p, p ∈ w.pend x ∧ p.1 = s.2
    · obtain ⟨p, hp, hp1⟩ := hpen
      exact .inl (SbBlocked.ownFwdB hP.toB hc x false base ts vs hl _ t v hrd s hs hsx p hp hp1)
    · obtain ⟨hpo, -⟩ := SbBlocked.ownPo hc (hd w x) false base ts vs hl _ t v hrd s hs hown
      refine landed (.inr ⟨s, hs, ?_, fun p hp hp1 => hpen ⟨p, by rw [← hsx]; exact hp, hp1⟩⟩)
      show s.2 < (w.rows s.1).length
      rw [hsx]; exact hpo
  · exact landed (.inr ⟨s, hs, (SbBlocked.hbSoundB hP.toB hc hE hD x true s hhb).2 rfl⟩)

/-- **… over the virtio chain** (`SbVirtio.srcGateOfClsV` without `PInv.rd`). -/
theorem srGateOfClsVR (hP : PInvR N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) {Ctr : Geid → Prop} (hC : SbVirtio.CtrLanded G Ctr w) (x : Nat)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad false base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd w x) a t v → SbVirtio.SrcClsV G dev Ctr (hd w x) t) :
    srGate G w x false base ts vs := by
  intro j t v htj hvj
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have landed : (t = 0 ∨ ∃ s, gwriteAt G t = some s ∧ SbBlocked.Landed w s) →
      SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
        (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ t ≤ (wrW w).length ∧
          (false = true → ∀ s, gwriteAt G t = some s → s.1 = x → gmoLt G s (hd w x))) := by
    intro hL
    obtain ⟨h1, h2⟩ := byteLandedR hP hc x _ t v hrd hL
    exact .inr ⟨h1, h2, fun h => by cases h⟩
  rcases hcls _ t v hrd with h0 | ⟨s, hs, hown | hhv⟩
  · exact landed (.inl h0)
  · have hsx : s.1 = x := hown
    by_cases hpen : ∃ p, p ∈ w.pend x ∧ p.1 = s.2
    · obtain ⟨p, hp, hp1⟩ := hpen
      exact .inl (SbBlocked.ownFwdB hP.toB hc x false base ts vs hl _ t v hrd s hs hsx p hp hp1)
    · obtain ⟨hpo, -⟩ := SbBlocked.ownPo hc (hd w x) false base ts vs hl _ t v hrd s hs hown
      refine landed (.inr ⟨s, hs, ?_, fun p hp hp1 => hpen ⟨p, by rw [← hsx]; exact hp, hp1⟩⟩)
      show s.2 < (w.rows s.1).length
      rw [hsx]; exact hpo
  · exact landed (.inr ⟨s, hs, (SbVirtio.hvSoundB hP.toB hc hE hD hC x true s hhv).2 rfl⟩)

end Cls

/-! ## 5.2 At reachable S-R states -/

section Reach

variable {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}

/-- **`blockedIsCensus` ON THE S-R WALK**: a non-`.aq` plain-load head all of whose byte sources are in a
source class passes the S-R gate ((EP) and (DR) from validity, `SbBlocked.histStAt`). -/
theorem blockedIsCensusRC (c : CandW) (hv : validW SbPol.epoch c) (hP : PInvR N c.img G X dev (SbWalk.cur c))
    (hc : CatH G) (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (SbWalk.cur c) x) = some (LLoad false base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd (SbWalk.cur c) x) a t v → SbBlocked.SrcCls G dev (hd (SbWalk.cur c) x) t) :
    srGate G (SbWalk.cur c) x false base ts vs :=
  have hh := SbBlocked.histStAt c hv c.its.length
  srGateOfClsR hP hc hh.1 hh.2 x base ts vs hl hcls

/-- **THE 9 PTE SITES ARE NEVER BLOCKED** on the S-R walk. -/
theorem pteNeverBlockedR (PteHd : Geid → Prop) (c : CandW) (hv : validW SbPol.epoch c)
    (hP : PInvR N c.img G X dev (SbWalk.cur c)) (hc : CatH G) (hT : SbPteCust.PteCustSrc G dev PteHd (SbWalk.cur c))
    (x : Nat) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (SbWalk.cur c) x) = some (LLoad false base ts vs)) (hH : PteHd (hd (SbWalk.cur c) x)) :
    srGate G (SbWalk.cur c) x false base ts vs :=
  blockedIsCensusRC c hv hP hc x base ts vs hl (hT x base ts vs hl hH)

/-- **THE VIRTIO ROWS** on the S-R walk (`SbVirtio.virtioTable`'s three gates from N6–N8 + `CtrLanded`). -/
theorem virtioTableR {DiskRd IdxExit CplRd Ctr : Geid → Prop} (c : CandW)
    (hv : validW SbPol.epoch c) (hP : PInvR N c.img G X dev (SbWalk.cur c)) (hc : CatH G)
    (hC : SbVirtio.CtrLanded G Ctr (SbWalk.cur c))
    (hDD : SbVirtio.DiskDesc G dev Ctr DiskRd) (hVI : SbVirtio.VirtioIdx G dev Ctr IdxExit)
    (hVD : SbVirtio.VirtioDesc G dev Ctr CplRd) :
    ∀ x base ts vs, gxLbl G (hd (SbWalk.cur c) x) = some (LLoad false base ts vs) →
      (DiskRd (hd (SbWalk.cur c) x) ∨ IdxExit (hd (SbWalk.cur c) x) ∨ CplRd (hd (SbWalk.cur c) x)) →
      srGate G (SbWalk.cur c) x false base ts vs := by
  intro x base ts vs hl hx
  have hh := SbBlocked.histStAt c hv c.its.length
  refine srGateOfClsVR hP hc hh.1 hh.2 hC x base ts vs hl (fun a t v hrd => ?_)
  rcases hx with hx | hx | hx
  · rcases hDD _ a t v hx hrd with h0 | ⟨s, hs, hp | hh⟩
    · exact .inl h0
    · exact .inr ⟨s, hs, .inr (SbVirtio.clsOfPub hc hp)⟩
    · exact .inr ⟨s, hs, .inr hh⟩
  · rcases hVI _ a t v hx hrd with h0 | ⟨s, hs, hp | hh⟩
    · exact .inl h0
    · exact .inr ⟨s, hs, .inr (SbVirtio.clsOfCo hc
        (gwrBOf G s a v hc.wf (SbVirtio.srcWrites hc _ a t v hrd s hs)).1 hp)⟩
    · exact .inr ⟨s, hs, .inr hh⟩
  · rcases hVD _ a t v hx hrd with h0 | ⟨s, hs, hp⟩
    · exact .inl h0
    · exact .inr ⟨s, hs, .inr (SbVirtio.clsOfPub hc hp)⟩

/-! ## 5.3 Row H3′ from the census -/

/-- **ROW H3′ FROM THE CENSUS TABLE**: given the transport for non-census heads (`NonCensusSrc`), `HeadOrdW`
needs the per-head table — never blocked (`srGate`) or the static write hop — ONLY at census sites. -/
theorem headOrdWOfCensus (Census : Geid → Prop) (c : CandW) (hv : validW SbPol.epoch c)
    (hP : PInvR N c.img G X dev (SbWalk.cur c)) (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hwio2 : ∀ d, d ∈ dev → gisWIo G d = true)
    (hNC : SbBlocked.NonCensusSrc G dev X Census (SbWalk.cur c))
    (hT : ∀ x base ts vs, gxLbl G (hd (SbWalk.cur c) x) = some (LLoad false base ts vs) → ¬ X (hd (SbWalk.cur c) x) →
      Census (hd (SbWalk.cur c) x) → srGate G (SbWalk.cur c) x false base ts vs ∨ SbHeadHop.WrHop G (hd (SbWalk.cur c) x)) :
    HeadOrdW G X dev (SbWalk.cur c) := by
  apply SbOrdR.headOrdWOf G X dev (SbWalk.cur c) hc hr1 hwio2
  intro x base ts vs hl hX hns
  by_cases hC : Census (hd (SbWalk.cur c) x)
  · rcases hT x base ts vs hl hX hC with h | h
    · exact absurd h hns
    · exact h
  · exact absurd (blockedIsCensusRC c hv hP hc x base ts vs hl (hNC x base ts vs hl hX hC)) hns

/-- **… with the PTE rows discharged by custody** (`SbPteCust.headOrdRdOfCensusPH`'s S-R form; the held-context
`holding+0x0` rows are table entries: their hop is `bnez`'s control dependency). -/
theorem headOrdWOfCensusP (Census PteHd : Geid → Prop) (c : CandW) (hv : validW SbPol.epoch c)
    (hP : PInvR N c.img G X dev (SbWalk.cur c)) (hc : CatH G)
    (hr1 : ∀ s m, WeakRvwmoGraph.gpo G s m → gmem G s → gisIo G s = false → gisIo G m = true →
      gmoLt G s m)
    (hwio2 : ∀ d, d ∈ dev → gisWIo G d = true)
    (hNC : SbBlocked.NonCensusSrc G dev X Census (SbWalk.cur c))
    (hPte : SbPteCust.PteCustSrc G dev PteHd (SbWalk.cur c))
    (hT : ∀ x base ts vs, gxLbl G (hd (SbWalk.cur c) x) = some (LLoad false base ts vs) → ¬ X (hd (SbWalk.cur c) x) →
      Census (hd (SbWalk.cur c) x) → ¬ PteHd (hd (SbWalk.cur c) x) →
      srGate G (SbWalk.cur c) x false base ts vs ∨ SbHeadHop.WrHop G (hd (SbWalk.cur c) x)) :
    HeadOrdW G X dev (SbWalk.cur c) := by
  apply headOrdWOfCensus Census c hv hP hc hr1 hwio2 hNC
  intro x base ts vs hl hX hC
  by_cases hp : PteHd (hd (SbWalk.cur c) x)
  · exact .inl (pteNeverBlockedR PteHd c hv hP hc hPte x base ts vs hl hp)
  · exact hT x base ts vs hl hX hC hp

end Reach

end SbOrdR

/-! # 6. The kill-level per-state interface from the census -/

/-- **`stateIfcCZR` FROM THE CENSUS** (REVISIT [OWN.124]): row H3′ from the non-census transport, PTE custody
and the census table (`srGate ∨ WrHop`, no (A2) window), the exempt value from [OWN.124]'s own inputs. -/
theorem SbKillR.stateIfcCZROfCensus (boot : Nat → Pexv6) (d0 : Efab) (fab : Nat → Efab) (im : Image)
    (Xof : Gfexec → Geid → Prop) (AcqCpuRd : Gfexec → Geid → Int → Prop)
    (Census PteHd : Gfexec → Geid → Prop)
    (hwio : CatLin.gfDevWIoCZ boot d0 fab im)
    (hW : SbKillR.walkHypCZR boot d0 fab im Xof)
    (hT : ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      (∀ e base ts vs, Xof GF e → gxLbl GF.gfGd.gdG e = some (LLoad false base ts vs) →
        AcqCpuRd GF e (base - 16)) ∧
      (∀ r L base ts vs, AcqCpuRd GF r L → gxLbl GF.gfGd.gdG r = some (LLoad false base ts vs) →
        base = L + 16 → ts.length = 8 ∧ r.1 < NCPU ∧ ∃ f, SbHoldZero.CpuWordWin GF.gfGd.gdG L f ∧
          SbHoldZero.CpuFloor GF.gfGd.gdG r L f ∧ SbHoldZero.NotHolder GF.gfGd.gdG r L))
    (hS : ∀ (GF : Gfexec) (ad : List (Geid × Geid)),
      GF.gfGd.gdG.gxImg = im → CatLin.rvwmoCatAD GF.gfGd ad → GraphFabConf.gfexecConfZF boot d0 fab GF →
      ioResidueGmo GF →
      ∀ c, validW SbPol.epoch c → SbOrdR.gatedWR GF.gfGd.gdG (Xof GF) GF.gfDev c → c.img = im →
        SbOrdR.PInvR GF.gfGd.gdG.gxProg.length im GF.gfGd.gdG (Xof GF) GF.gfDev (SbWalk.cur c) →
        SbBlocked.NonCensusSrc GF.gfGd.gdG GF.gfDev (Xof GF) (Census GF) (SbWalk.cur c) ∧
        SbPteCust.PteCustSrc GF.gfGd.gdG GF.gfDev (PteHd GF) (SbWalk.cur c) ∧
        (∀ x base ts vs, gxLbl GF.gfGd.gdG (hd (SbWalk.cur c) x) = some (LLoad false base ts vs) →
          ¬ Xof GF (hd (SbWalk.cur c) x) → Census GF (hd (SbWalk.cur c) x) → ¬ PteHd GF (hd (SbWalk.cur c) x) →
          SbOrdR.srGate GF.gfGd.gdG (SbWalk.cur c) x false base ts vs ∨
            SbHeadHop.WrHop GF.gfGd.gdG (hd (SbWalk.cur c) x)) ∧
        SbHoldX.CpuTopMap GF.gfGd.gdG (Xof GF) (SbWalk.cur c)) :
    SbKillR.stateIfcCZR boot d0 fab im Xof := by
  refine SbKillR.stateIfcCZROf boot d0 fab im Xof AcqCpuRd hW hT
    (fun GF ad him hc hconf hres c hv hg hci hP => ?_)
  obtain ⟨hNC, hPte, hTab, hCT⟩ := hS GF ad him hc hconf hres c hv hg hci hP
  have hr1 : ∀ s m, WeakRvwmoGraph.gpo GF.gfGd.gdG s m → gmem GF.gfGd.gdG s →
      gisIo GF.gfGd.gdG s = false → gisIo GF.gfGd.gdG m = true → gmoLt GF.gfGd.gdG s m :=
    fun s m hpo hgm hn hi => hres s m (.inl ⟨hpo, hgm, hn, hi⟩)
  have hP' : SbOrdR.PInvR GF.gfGd.gdG.gxProg.length c.img GF.gfGd.gdG (Xof GF) GF.gfDev (SbWalk.cur c) :=
    hci ▸ hP
  exact ⟨SbOrdR.headOrdWOfCensusP (Census GF) (PteHd GF) c hv hP' ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
    hr1 (hwio GF ad him hc hconf) hNC hPte hTab, hCT⟩

end Weak
