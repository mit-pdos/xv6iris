/-
Weak: **allocproc route P — row P-W3r-e: `drainLanded` + `DiskDesc` + `VirtioIdx` + `VirtioDesc`**
(plan rev 56 row P-W3r-e, named inputs N6/N7/N8; design §3.4 per-site table; review R46 [R46.6];
PROGRESS-P-ref.md §HEADHOP2; PROGRESS-P-W3r-e.md).  Lean-only, no Rocq twin.  A PRIMED TWIN: nothing
registered imports this file.

**Spec, stated first.**  riscv.cat: the load value axiom (a read byte returns the gmo-latest visible
write), rule 4 (a `fence rw,rw` — the device's `DFence` = `LFence true true true true`, the driver's
`fence iorw,iorw` — orders every earlier access before every later one), co ⊆ gmo.  Sail / Zifencei /
the PMAs say nothing about the virtio device: its program (`Weak/VirtioProg.lean`) is MODEL text.  In
the gated walk (`SbOrd`) a plain-load head is blocked iff some byte's GF source is a FOREIGN write that
has not landed; so a census site is "never blocked" once every byte's GF source is shown LANDED from
the head's realized prefix.  The four virtio rows of the per-site table:
* **the 7 plain device `DRead`s** (ring entry, 3 descriptors, type, sector, payload; the avail-index
  read is `.aq` — `availIdxAq` — so it is a rule-5 head (H1), outside `HeadOrdRd`): the source is a
  driver store po-before the driver's `fence iorw,iorw`, which is po-before the avail-index store the
  burst's avail-index read (po-before the head on the disk row) has seen ⇒ landed;
* **vdi+0x36 taken / vdi+0x82 fall-through** (`used->idx` read with GF value = `used_idx`): the source
  is co-at-or-before the source of the driver's previous realized `used->idx` read ⇒ landed;
* **vdi+0x4e / vdi+0x5a** (`used->ring[..].id`, `info[id].status`): the source is the device's
  completion write (used element / status byte), po-before the device's `DFence`, po-before the
  used-index write the driver's realized `used->idx` read has seen (or a co-later one) ⇒ landed.
All three need ONE realized-prefix fact the walk does not carry: a REALIZED read of a COUNTER word
(the avail index, the used index) has a LANDED source (`CtrLanded`).

  §1  the extended chain **`SbVirtio.Hv`** = `SbBlocked.Hb` + `co` (a GF write co-before a landed
      write of the byte has landed: the landed list is a gmo-prefix, `landedDown`) + `ctr` (a realized
      counter read's source has landed: `CtrLanded`); `hvOfHb`; **`hvSound`**.
  §2  `SrcClsV`, **`srcGateOfClsV`**, **`valGateOfClsV`**, `valGateOfClsVC` (reachable states: (EP)
      and (DR) = `drainLanded` from `SbBlocked.histStAt`).
  §3  **`pubHop`** — THE PUBLICATION HOP: a store po-before a draining fence po-before a write `I`
      co-at-or-before the source of a realized counter read has landed (`ctr`, `co`, `lr`, `po`,
      `drain`); `coHop` (the same without the fence).
  §4  the three sites as EXACT NAMED GF-level statements — **`DiskDesc`**, **`VirtioIdx`**,
      **`VirtioDesc`** — and their gates **`diskDescGate`**, **`virtioIdxGate`**,
      **`virtioDescGate`**; **`virtioTable`** (the virtio rows of `headOrdRdOfCensus`'s `hT`).
  §5  the device-text half (`rfl`): `availIdxAq`, `availRingPlain`, `descPlain`, `usedTailFence`,
      `statusTail` (the completion writes are po-before the `DFence` po-before the used index).

Spec mark: FAITHFUL (proof organisation over load value, rule 4, co ⊆ gmo as the walk honours them;
`drainLanded` is the PROVED (DR) of `SbBlocked`, no `PInv` / SbOrd / SbOrdWalk edit).  The named inputs
(`DiskDesc` / `VirtioIdx` / `VirtioDesc`: GF-level, the Xv6 virtio driver discipline + (T), P-W6;
`CtrLanded`: realized-prefix, P-W6 + the Xv6 window invariant) are FAITHFUL and WEAKER while named.
Lean-only helpers `SbVirtio.*`.
-/
import Weak.SbBlocked

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. The extended chain -/

/-- **(NAMED, realized prefix) A REALIZED COUNTER READ HAS A LANDED SOURCE**: at walk state `w`, every
byte source of a realized read in `Ctr` (the realization's counter reads: the disk row's avail-index
`DRead`s, the driver's `used->idx` reads at vdi+0x36 / vdi+0x82 — the label ↔ pc map (T)) is the image
or a landed write.
Truth for xv6, along a GATED walk (every realized read passed `valGate`: its top word was GF's word):
the counter's writes are full-width and consecutive (the device's `used->idx := ui + 1` after a
`DFence` that drains the previous one; the driver's `avail->idx += 1` under `vdisk_lock`, after a
fence), so all realized writes of the word but the latest have landed; GF's source is within `NUM`
of the latest landed write (the driver invariant `0 ≤ idx − used_idx ≤ NUM`, `avail − seen ≤ NUM`,
with the earlier counter reads' sources landed by induction), and `NUM < 2^16`, so equal words are
the same write.  NOT a consequence of `validW` + `PInv` alone (finding F-W2-V-1): a validW member may
read a STALE landed message per byte (`byteRd` at the views), so a torn / wrapped value can equal GF's
without GF's source being landed; the gated walk built by `walkRunP` never does.  Discharger: P-W6
(the walk's gate history + the Xv6 virtio window invariant).  FAITHFUL; WEAKER while named. -/
def SbVirtio.CtrLanded (G : Gexec) (Ctr : Geid → Prop) (w : WS) : Prop :=
  ∀ r a t v, Ctr r → realized w r → greadsByte G r a t v → landedSrc G w a t

/-- **THE EXTENDED CHAIN** from the head `h`'s realized prefix (`SbBlocked.Hb`'s seven arms, plus):
`co` — a GF write `s` of byte `a` gmo-before a landed write `s'` of `a` has landed (the landed list of
a byte is a gmo-prefix of GF's); `ctr` — the byte source of a realized counter read has landed
(`CtrLanded`). -/
inductive SbVirtio.Hv (G : Gexec) (dev : List Geid) (Ctr : Geid → Prop) (h : Geid) :
    Bool → Geid → Prop where
  | root (e : Geid) : e.1 = h.1 → e.2 < h.2 → SbVirtio.Hv G dev Ctr h false e
  | po (e e' : Geid) : SbVirtio.Hv G dev Ctr h false e → e'.1 = e.1 → e'.2 < e.2 →
      SbVirtio.Hv G dev Ctr h false e'
  | fab (e e' : Geid) : SbVirtio.Hv G dev Ctr h false e → before dev e' e →
      SbVirtio.Hv G dev Ctr h false e'
  | lr (e : Geid) : SbVirtio.Hv G dev Ctr h true e → SbVirtio.Hv G dev Ctr h false e
  | amo (A s : Geid) (aq rl : Bool) (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8))
      (kc : WmClass) (j t : Nat) : SbVirtio.Hv G dev Ctr h false A →
      gxLbl G A = some (LRmw aq rl base ts rvs wvs kc) → ts[j]? = some t → gwriteAt G t = some s →
      SbVirtio.Hv G dev Ctr h true s
  | epoch (r s : Geid) : SbVirtio.Hv G dev Ctr h true r → gisW G r = true → s.1 = r.1 →
      fenceSw G s.1 s.2 r.2 → SbVirtio.Hv G dev Ctr h true s
  | drain (f s : Geid) (pr sw : Bool) : SbVirtio.Hv G dev Ctr h false f →
      gxLbl G f = some (LFence pr true true sw) → s.1 = f.1 → s.2 < f.2 →
      SbVirtio.Hv G dev Ctr h true s
  | co (s s' : Geid) (a : Int) : SbVirtio.Hv G dev Ctr h true s' → gwrB G a s' = true →
      gwrB G a s = true → s ∈ G.gxGmo → gpos G s < gpos G s' → SbVirtio.Hv G dev Ctr h true s
  | ctr (r s : Geid) (a : Int) (t : Nat) (v : BitVec 8) : SbVirtio.Hv G dev Ctr h false r → Ctr r →
      greadsByte G r a t v → gwriteAt G t = some s → SbVirtio.Hv G dev Ctr h true s

/-- Every `Hb` chain is an `Hv` chain. -/
theorem SbVirtio.hvOfHb {G : Gexec} {dev : List Geid} (Ctr : Geid → Prop) {h : Geid} {b : Bool}
    {e : Geid} (hh : SbBlocked.Hb G dev h b e) : SbVirtio.Hv G dev Ctr h b e := by
  induction hh with
  | root e h1 h2 => exact .root e h1 h2
  | po e e' _ h1 h2 ih => exact .po e e' ih h1 h2
  | fab e e' _ hb ih => exact .fab e e' ih hb
  | lr e _ ih => exact .lr e ih
  | amo A s aq rl base ts rvs wvs kc j t _ hl htj hs ih => exact .amo A s aq rl base ts rvs wvs kc j t ih hl htj hs
  | epoch r s _ hrW h1 hf ih => exact .epoch r s ih hrW h1 hf
  | drain f s pr sw _ hfl h1 h2 ih => exact .drain f s pr sw ih hfl h1 h2

section Inv

variable {N : Nat} {img : Image} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {w : WS}

/-- **THE EXTENDED CHAIN IS SOUND** at a walk state with (EP), (DR) and `CtrLanded`. -/
theorem SbVirtio.hvSoundB (hP : PInvB N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) {Ctr : Geid → Prop} (hC : SbVirtio.CtrLanded G Ctr w) (x : Nat)
    (b : Bool) (e : Geid) (hh : SbVirtio.Hv G dev Ctr (hd w x) b e) :
    (b = false → realized w e) ∧ (b = true → SbBlocked.Landed w e) := by
  induction hh with
  | root e h1 h2 =>
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    show e.2 < (w.rows e.1).length
    rw [h1]; exact h2
  | po e e' _ h1 h2 ih =>
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    have := ih.1 rfl
    show e'.2 < (w.rows e'.1).length
    rw [h1]; unfold realized at this; omega
  | fab e e' _ hb ih => exact ⟨fun _ => hP.dvP e' e hb (ih.1 rfl), fun h => by cases h⟩
  | lr e _ ih => exact ⟨fun _ => (ih.2 rfl).1, fun h => by cases h⟩
  | amo A s aq rl base ts rvs wvs kc j t _ hl htj hs ih =>
    exact ⟨(fun h => nomatch h), fun _ =>
      SbBlocked.amoSrcLandedB hP hc A s aq rl base ts rvs wvs kc j t hl (ih.1 rfl) htj hs⟩
  | epoch r s _ hrW h1 hf ih =>
    exact ⟨(fun h => nomatch h), fun _ => SbBlocked.epochLandedB hP hE r s (ih.2 rfl) hrW h1 hf⟩
  | drain f s pr sw _ hfl h1 h2 ih =>
    exact ⟨(fun h => nomatch h), fun _ => SbBlocked.drainLandedB hP hD f s pr sw (ih.1 rfl) hfl h1 h2⟩
  | co s s' a _ hb' hb hsm hlt ih =>
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    have hs'W : s' ∈ wrAtW w a := SbBlocked.landedWrB hP s' a (ih.2 rfl) hb'
    have hsW := landedDown G w a s s' (hP.pf.2 a) hc.wf.1 hs'W (List.mem_filter.2 ⟨hsm, hb⟩) hlt
    exact SbBlocked.landedOfGmoB hP s (List.mem_filter.1 hsW).1
  | ctr r s a t v _ hCr hrd hs ih =>
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    rcases hC r a t v hCr (ih.1 rfl) hrd with rfl | ⟨s0, hs0, hs0W⟩
    · simp [gwriteAt] at hs
    · rw [hs] at hs0
      cases hs0
      exact SbBlocked.landedOfGmoB hP s (List.mem_filter.1 hs0W).1

theorem SbVirtio.hvSound (hP : PInv N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) {Ctr : Geid → Prop} (hC : SbVirtio.CtrLanded G Ctr w) (x : Nat)
    (b : Bool) (e : Geid) (hh : SbVirtio.Hv G dev Ctr (hd w x) b e) :
    (b = false → realized w e) ∧ (b = true → SbBlocked.Landed w e) :=
  SbVirtio.hvSoundB hP.toB hc hE hD hC x b e hh

/-! # 2. Source classes and the gate -/

/-- **THE SOURCE CLASSES OF A VIRTIO CENSUS BYTE** (GF + the head's position): the image, an own write,
or a write the extended chain lands. -/
def SbVirtio.SrcClsV (G : Gexec) (dev : List Geid) (Ctr : Geid → Prop) (h : Geid) (t : Nat) : Prop :=
  t = 0 ∨ ∃ s, gwriteAt G t = some s ∧ (s.1 = h.1 ∨ SbVirtio.Hv G dev Ctr h true s)

/-- A GF byte source writes the byte (load value). -/
theorem SbVirtio.srcWrites (hc : CatH G) (r : Geid) (a : Int) (t : Nat) (v : BitVec 8)
    (hrd : greadsByte G r a t v) (s : Geid) (hs : gwriteAt G t = some s) : gwritesByte G s a v := by
  obtain ⟨hsrc, -⟩ := hc.lv _ _ t v hrd
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ n =>
    obtain ⟨s', hs', hsw, -⟩ := hsrc
    rw [hs] at hs'
    cases hs'
    exact hsw

/-- **A HEAD WHOSE EVERY BYTE IS IN A VIRTIO SOURCE CLASS PASSES THE SOURCE GATE** (as
`SbBlocked.srcGateOfCls`, over `Hv`). -/
theorem SbVirtio.srcGateOfClsV (hP : PInv N img G X dev w) (hc : CatH G) (hE : SbBlocked.EpochOk w)
    (hD : SbBlocked.DrainOk w) {Ctr : Geid → Prop} (hC : SbVirtio.CtrLanded G Ctr w) (x : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd w x) a t v → SbVirtio.SrcClsV G dev Ctr (hd w x) t) :
    srcGate G w x base ts vs := by
  intro j t v htj hvj
  have hrd : greadsByte G (hd w x) (accAddr base j) t v := ⟨_, base, ts, vs, j, hl, rfl, htj, hvj, rfl⟩
  have landedCase : ∀ s, gwriteAt G t = some s → gwritesByte G s (accAddr base j) v →
      SbBlocked.Landed w s →
      SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
        (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧ srcLatest G w (accAddr base j) t) :=
    fun s hs hsw hL => .inr (SbBlocked.byteOfLanded hP hc x aq base ts vs hl _ t v hrd
      (.inr ⟨s, hs, SbBlocked.landedWr hP s _ hL (gwrBOf G s _ _ hc.wf hsw).1⟩))
  rcases hcls _ t v hrd with h0 | ⟨s, hs, hown | hhv⟩
  · exact .inr (SbBlocked.byteOfLanded hP hc x aq base ts vs hl _ t v hrd (.inl h0))
  · have hsx : s.1 = x := hown
    by_cases hpen : ∃ p, p ∈ w.pend x ∧ p.1 = s.2
    · obtain ⟨p, hp, hp1⟩ := hpen
      exact .inl (SbBlocked.ownFwd hP hc x aq base ts vs hl _ t v hrd s hs hsx p hp hp1)
    · obtain ⟨hpo, hsw⟩ := SbBlocked.ownPo hc (hd w x) aq base ts vs hl _ t v hrd s hs hown
      refine landedCase s hs hsw ⟨?_, fun p hp hp1 => hpen ⟨p, by rw [← hsx]; exact hp, hp1⟩⟩
      show s.2 < (w.rows s.1).length
      rw [hsx]; exact hpo
  · exact landedCase s hs (SbVirtio.srcWrites hc _ _ t v hrd s hs)
      ((SbVirtio.hvSound hP hc hE hD hC x true s hhv).2 rfl)

/-- ... hence the VALUE gate. -/
theorem SbVirtio.valGateOfClsV (hP : PInv N img G X dev w) (hc : CatH G) (himg : G.gxImg = img)
    (hE : SbBlocked.EpochOk w) (hD : SbBlocked.DrainOk w) {Ctr : Geid → Prop}
    (hC : SbVirtio.CtrLanded G Ctr w) (x : Nat) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (hl : gxLbl G (hd w x) = some (LLoad aq base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd w x) a t v → SbVirtio.SrcClsV G dev Ctr (hd w x) t) :
    valGate w x base ts vs :=
  valGateMono hP hc.wf hc.lv himg x aq base ts vs hl
    (SbVirtio.srcGateOfClsV hP hc hE hD hC x aq base ts vs hl hcls)

end Inv

/-- **… AT EVERY REACHABLE STATE** of a valid candidate: (EP) and (DR) — `drainLanded`'s invariant —
are theorems (`SbBlocked.histStAt`); only `CtrLanded` stays an input. -/
theorem SbVirtio.valGateOfClsVC {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid}
    {Ctr : Geid → Prop} (c : CandW) (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c))
    (hc : CatH G) (himg : G.gxImg = c.img) (hC : SbVirtio.CtrLanded G Ctr (cur c)) (x : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs))
    (hcls : ∀ a t v, greadsByte G (hd (cur c) x) a t v → SbVirtio.SrcClsV G dev Ctr (hd (cur c) x) t) :
    valGate (cur c) x base ts vs :=
  have hh := SbBlocked.histStAt c hv c.its.length
  SbVirtio.valGateOfClsV hP hc himg hh.1 hh.2 hC x aq base ts vs hl hcls

/-! # 3. The publication hop -/

/-- **THE CO HOP**: a write `I` of byte `a`, co-at-or-before the source `s'` of a counter read `r`
of `a` that the chain realizes, is chain-landed. -/
theorem SbVirtio.coHop {G : Gexec} {dev : List Geid} {Ctr : Geid → Prop} {h : Geid} (hc : CatH G)
    (r s' I : Geid) (a : Int) (t : Nat) (v : BitVec 8) (hr : SbVirtio.Hv G dev Ctr h false r)
    (hCr : Ctr r) (hrd : greadsByte G r a t v) (hs' : gwriteAt G t = some s')
    (hI : I = s' ∨ (gwrB G a I = true ∧ I ∈ G.gxGmo ∧ gpos G I < gpos G s')) :
    SbVirtio.Hv G dev Ctr h true I := by
  have hs'L : SbVirtio.Hv G dev Ctr h true s' := .ctr r s' a t v hr hCr hrd hs'
  rcases hI with rfl | ⟨hb, hm, hlt⟩
  · exact hs'L
  · exact .co I s' a hs'L (gwrBOf G s' a v hc.wf (SbVirtio.srcWrites hc r a t v hrd s' hs')).1 hb hm hlt

/-- **THE PUBLICATION HOP**: a store `s` po-before a draining fence `f` po-before a write `I`
co-at-or-before the source of a counter read the chain realizes has landed (`ctr` → `co` → `lr` →
`po` → `drain`: [R46.6]'s `drainLanded` at the driver's `fence iorw,iorw` / the device's `DFence`). -/
theorem SbVirtio.pubHop {G : Gexec} {dev : List Geid} {Ctr : Geid → Prop} {h : Geid} (hc : CatH G)
    (r s' I f s : Geid) (a : Int) (t : Nat) (v : BitVec 8) (pr sw : Bool)
    (hr : SbVirtio.Hv G dev Ctr h false r) (hCr : Ctr r) (hrd : greadsByte G r a t v)
    (hs' : gwriteAt G t = some s')
    (hI : I = s' ∨ (gwrB G a I = true ∧ I ∈ G.gxGmo ∧ gpos G I < gpos G s'))
    (hfI1 : f.1 = I.1) (hfI2 : f.2 < I.2) (hfl : gxLbl G f = some (LFence pr true true sw))
    (hsf1 : s.1 = f.1) (hsf2 : s.2 < f.2) : SbVirtio.Hv G dev Ctr h true s :=
  .drain f s pr sw (.po I f (.lr I (SbVirtio.coHop hc r s' I a t v hr hCr hrd hs' hI)) hfI1 hfI2) hfl
    hsf1 hsf2

/-! # 4. The three sites -/

/-- **THE PUBLICATION ARM** (GF-level) of a write `s` for a head `h`: `s` is po-before a draining fence
`f` (`fence iorw,iorw` / `DFence`), `f` po-before a write `I`, and `I` is co-at-or-before the source
`s'` of a counter read `r` (of a byte `a` of `I`) in `h`'s chain. -/
def SbVirtio.PubArm (G : Gexec) (dev : List Geid) (Ctr : Geid → Prop) (h s : Geid) : Prop :=
  ∃ f pr sw I r a t v s', s.1 = f.1 ∧ s.2 < f.2 ∧ gxLbl G f = some (LFence pr true true sw) ∧
    f.1 = I.1 ∧ f.2 < I.2 ∧ SbVirtio.Hv G dev Ctr h false r ∧ Ctr r ∧ greadsByte G r a t v ∧
    gwriteAt G t = some s' ∧ (I = s' ∨ (gwrB G a I = true ∧ I ∈ G.gxGmo ∧ gpos G I < gpos G s'))

/-- **THE COUNTER ARM** (GF-level) of a write `s` at byte `a` for a head `h`: `s` is co-at-or-before
the source `s'` of a counter read `r` of the same byte in `h`'s chain. -/
def SbVirtio.CoArm (G : Gexec) (dev : List Geid) (Ctr : Geid → Prop) (h s : Geid) (a : Int) : Prop :=
  ∃ r t v s', SbVirtio.Hv G dev Ctr h false r ∧ Ctr r ∧ greadsByte G r a t v ∧ gwriteAt G t = some s' ∧
    (s = s' ∨ (s ∈ G.gxGmo ∧ gpos G s < gpos G s'))

theorem SbVirtio.clsOfPub {G : Gexec} {dev : List Geid} {Ctr : Geid → Prop} {h s : Geid}
    (hc : CatH G) (hp : SbVirtio.PubArm G dev Ctr h s) : SbVirtio.Hv G dev Ctr h true s := by
  obtain ⟨f, pr, sw, I, r, a, t, v, s', hsf1, hsf2, hfl, hfI1, hfI2, hr, hCr, hrd, hs', hI⟩ := hp
  exact SbVirtio.pubHop hc r s' I f s a t v pr sw hr hCr hrd hs' hI hfI1 hfI2 hfl hsf1 hsf2

theorem SbVirtio.clsOfCo {G : Gexec} {dev : List Geid} {Ctr : Geid → Prop} {h s : Geid} {a : Int}
    (hc : CatH G) (hb : gwrB G a s = true) (hp : SbVirtio.CoArm G dev Ctr h s a) :
    SbVirtio.Hv G dev Ctr h true s := by
  obtain ⟨r, t, v, s', hr, hCr, hrd, hs', hI⟩ := hp
  refine SbVirtio.coHop hc r s' s a t v hr hCr hrd hs' ?_
  rcases hI with rfl | ⟨hm, hlt⟩
  · exact .inl rfl
  · exact .inr ⟨hb, hm, hlt⟩

/-- **N8 `DiskDesc` (NAMED, GF-level)**: every byte of a plain device read (`DiskRd`: the disk row's
ring-entry, descriptor, type, sector and payload `DRead`s — (T)) is sourced by the image, or by a write
with the PUBLICATION ARM (a driver store of `virtio_disk_rw` — `avail->ring[..]`, `desc[..]`, the
`virtio_blk_req` header — po-before its `fence iorw,iorw`, po-before the `avail->idx` store that the
burst's avail-index read (po-before the head on the disk row: `Hv.root`) has seen or a co-later one),
or by a write the chain lands (the OUT payload: `b->data`, written under the buffer's sleeplock — own,
lock-chained or an earlier fill's DMA before its `DFence`).  Truth: the virtio driver discipline (the
descriptors of an avail slot are written before the slot is published and not rewritten until its
completion is processed) + (T).  Discharger: P-W6 + the Xv6 virtio driver invariant.  FAITHFUL; WEAKER
while named. -/
def SbVirtio.DiskDesc (G : Gexec) (dev : List Geid) (Ctr DiskRd : Geid → Prop) : Prop :=
  ∀ h a t v, DiskRd h → greadsByte G h a t v → t = 0 ∨ ∃ s, gwriteAt G t = some s ∧
    (SbVirtio.PubArm G dev Ctr h s ∨ SbVirtio.Hv G dev Ctr h true s)

/-- **N6 `VirtioIdx` (NAMED, GF-level)**: every byte of a `used->idx` read whose GF value is the
driver's `used_idx` (`IdxExit`: vdi+0x36 taken, vdi+0x82 fall-through — (T) + the arm) is sourced by
the image, or by a write with the COUNTER ARM (co-at-or-before the source of the driver's previous
realized `used->idx` read — on the same hart, or on the hart that last held `vdisk_lock`, reached by
`Hv`'s lock arms), or by a write the chain lands (the `memset` of `virtio_disk_init`, before any
completion).  Truth: device idx writes are consecutive and full-width, `0 ≤ idx − used_idx ≤ NUM`, and
the driver's `used_idx` only advances to values its realized reads have seen (CoRR along the
`vdisk_lock` chain).  Discharger: P-W6 + the Xv6 virtio driver invariant.  FAITHFUL; WEAKER while
named. -/
def SbVirtio.VirtioIdx (G : Gexec) (dev : List Geid) (Ctr IdxExit : Geid → Prop) : Prop :=
  ∀ h a t v, IdxExit h → greadsByte G h a t v → t = 0 ∨ ∃ s, gwriteAt G t = some s ∧
    (SbVirtio.CoArm G dev Ctr h s a ∨ SbVirtio.Hv G dev Ctr h true s)

/-- **N7 `VirtioDesc` (NAMED, GF-level)**: every byte of a completion read (`CplRd`: vdi+0x4e
`used->ring[used_idx % NUM].id`, vdi+0x5a `info[id].status` — (T)) is sourced by a write with the
PUBLICATION ARM: the device's used-element / status write for that completion, po-before the device's
`DFence` (`usedTailFence`, `statusTail`), po-before its used-index write, co-at-or-before the source of
the driver's realized `used->idx` read that showed the entry (the slot is not recycled before the
driver processes it: the device reuses a used slot only `NUM` completions later, after the avail slot
it answers is republished).  Discharger: P-W6 + the Xv6 virtio driver invariant (+ the device text,
§5).  FAITHFUL; WEAKER while named. -/
def SbVirtio.VirtioDesc (G : Gexec) (dev : List Geid) (Ctr CplRd : Geid → Prop) : Prop :=
  ∀ h a t v, CplRd h → greadsByte G h a t v → t = 0 ∨ ∃ s, gwriteAt G t = some s ∧
    SbVirtio.PubArm G dev Ctr h s

section Gate

variable {N : Nat} {G : Gexec} {X : Geid → Prop} {dev : List Geid} {Ctr : Geid → Prop}

/-- **`DiskDesc` ⇒ the plain device reads pass the value gate** (never blocked). -/
theorem SbVirtio.diskDescGate {DiskRd : Geid → Prop} (c : CandW) (hv : validW SbPol.epoch c)
    (hP : PInv N c.img G X dev (cur c)) (hc : CatH G) (himg : G.gxImg = c.img)
    (hC : SbVirtio.CtrLanded G Ctr (cur c)) (hDD : SbVirtio.DiskDesc G dev Ctr DiskRd) (x : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs)) (hx : DiskRd (hd (cur c) x)) :
    valGate (cur c) x base ts vs := by
  refine SbVirtio.valGateOfClsVC c hv hP hc himg hC x aq base ts vs hl (fun a t v hrd => ?_)
  rcases hDD _ a t v hx hrd with h0 | ⟨s, hs, hp | hh⟩
  · exact .inl h0
  · exact .inr ⟨s, hs, .inr (SbVirtio.clsOfPub hc hp)⟩
  · exact .inr ⟨s, hs, .inr hh⟩

/-- **`VirtioIdx` ⇒ vdi+0x36 taken / vdi+0x82 fall-through pass the value gate** (top = GF). -/
theorem SbVirtio.virtioIdxGate {IdxExit : Geid → Prop} (c : CandW) (hv : validW SbPol.epoch c)
    (hP : PInv N c.img G X dev (cur c)) (hc : CatH G) (himg : G.gxImg = c.img)
    (hC : SbVirtio.CtrLanded G Ctr (cur c)) (hVI : SbVirtio.VirtioIdx G dev Ctr IdxExit) (x : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs)) (hx : IdxExit (hd (cur c) x)) :
    valGate (cur c) x base ts vs := by
  refine SbVirtio.valGateOfClsVC c hv hP hc himg hC x aq base ts vs hl (fun a t v hrd => ?_)
  rcases hVI _ a t v hx hrd with h0 | ⟨s, hs, hp | hh⟩
  · exact .inl h0
  · exact .inr ⟨s, hs, .inr (SbVirtio.clsOfCo hc
      (gwrBOf G s a v hc.wf (SbVirtio.srcWrites hc _ a t v hrd s hs)).1 hp)⟩
  · exact .inr ⟨s, hs, .inr hh⟩

/-- **`VirtioDesc` ⇒ vdi+0x4e / vdi+0x5a pass the value gate.** -/
theorem SbVirtio.virtioDescGate {CplRd : Geid → Prop} (c : CandW) (hv : validW SbPol.epoch c)
    (hP : PInv N c.img G X dev (cur c)) (hc : CatH G) (himg : G.gxImg = c.img)
    (hC : SbVirtio.CtrLanded G Ctr (cur c)) (hVD : SbVirtio.VirtioDesc G dev Ctr CplRd) (x : Nat)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8))
    (hl : gxLbl G (hd (cur c) x) = some (LLoad aq base ts vs)) (hx : CplRd (hd (cur c) x)) :
    valGate (cur c) x base ts vs := by
  refine SbVirtio.valGateOfClsVC c hv hP hc himg hC x aq base ts vs hl (fun a t v hrd => ?_)
  rcases hVD _ a t v hx hrd with h0 | ⟨s, hs, hp⟩
  · exact .inl h0
  · exact .inr ⟨s, hs, .inr (SbVirtio.clsOfPub hc hp)⟩

/-- **THE VIRTIO ROWS OF THE PER-SITE TABLE** (the `hT` arm of `SbBlocked.headOrdRdOfCensus` at the
census heads `DiskRd ∪ IdxExit ∪ CplRd`): "never blocked" (`valGate`) from N6–N8 + `CtrLanded`.  The
other two virtio arms (vdi+0x36 fall-through / vdi+0x82 back edge) are `fenceNextHop`'s. -/
theorem SbVirtio.virtioTable {DiskRd IdxExit CplRd : Geid → Prop} (c : CandW)
    (hv : validW SbPol.epoch c) (hP : PInv N c.img G X dev (cur c)) (hc : CatH G)
    (himg : G.gxImg = c.img) (hC : SbVirtio.CtrLanded G Ctr (cur c))
    (hDD : SbVirtio.DiskDesc G dev Ctr DiskRd) (hVI : SbVirtio.VirtioIdx G dev Ctr IdxExit)
    (hVD : SbVirtio.VirtioDesc G dev Ctr CplRd) :
    ∀ x base ts vs, gxLbl G (hd (cur c) x) = some (LLoad false base ts vs) →
      (DiskRd (hd (cur c) x) ∨ IdxExit (hd (cur c) x) ∨ CplRd (hd (cur c) x)) →
      valGate (cur c) x base ts vs := by
  intro x base ts vs hl hx
  rcases hx with hx | hx | hx
  · exact SbVirtio.diskDescGate c hv hP hc himg hC hDD x false base ts vs hl hx
  · exact SbVirtio.virtioIdxGate c hv hP hc himg hC hVI x false base ts vs hl hx
  · exact SbVirtio.virtioDescGate c hv hP hc himg hC hVD x false base ts vs hl hx

end Gate

/-! # 5. The device-text half (`rfl` on `Weak/VirtioProg.lean`) -/

/-- The avail-index read carries the ACQUIRE bit: an `.aq` head (rule 5, row H1), not a `HeadOrdRd`
site — so the plain device census is the OTHER seven `DRead`s. -/
theorem SbVirtio.availIdxAq (c : VirtioCfg) (k : BitVec 16 → DM Dres) :
    ∃ k', dreadAvailIdx c k = DRead (Virtio.availIdxAddr c) 2 true k' := ⟨_, rfl⟩

/-- The ring-entry read is plain. -/
theorem SbVirtio.availRingPlain (c : VirtioCfg) (i : BitVec 16) (k : BitVec 16 → DM Dres) :
    ∃ k', dreadAvailRing c i k = DRead (Virtio.availRingAddr c i) 2 false k' := ⟨_, rfl⟩

/-- A descriptor read is plain (one 16-byte read). -/
theorem SbVirtio.descPlain (c : VirtioCfg) (i : Nat) (k : Virtio.VqDesc → DM Dres) :
    ∃ k', dreadDesc c i k = DRead (Virtio.descAddr c i) 16 false k' := ⟨_, rfl⟩

/-- The used element is followed by the `DFence`, then the used-index write (`idxNode`). -/
theorem SbVirtio.usedTailFence (h : BitVec 16) (r : VioReq) :
    ∃ pre g pa bs, dusedTail h r =
      DWriteDev pre g pa bs (fun s => DFence (VirtioProg.idxNode h r s.usedIdx s.cfg)) :=
  ⟨_, _, _, _, rfl⟩

/-- The status byte is followed by the used-ring report (`dusedTail`). -/
theorem SbVirtio.statusTail (h : BitVec 16) (r : VioReq) (pre : VirtioState → VirtioState × Bool) :
    ∃ pre' g pa bs, dtail h r pre = DWriteDev pre' g pa bs (fun _ => dusedTail h r) :=
  ⟨_, _, _, _, rfl⟩

end Weak
