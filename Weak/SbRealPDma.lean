/-
Weak: **allocproc route P, row P-W6 — THE DMA ROW of the state map `rmemP`** ([OWN.151], F-CM-1 (b′);
`notes/twin-machine-conformance.md` cells l/m; `PROGRESS-PW6.md` CP-PW6-2).  Lean-only, no Rocq twin.  A
PRIMED TWIN: nothing registered imports this file.

Under [OWN.151] the walk issues a device store only when it can land, and lands it in the same walk unit
(`SbOrd.devLandOk`, `SbOrd.devQuiet`, `SbOrd.devUnit`).  The realization therefore maps the twin's PAIR
"device `LStore` issue, then the landing of that (only) device entry" to MachCSL's ONE DMA transition
(`devOpStep .dmaWrite`, memory half `MState.storeDma`): the disk's entry lands at once, inserted below every
pending entry of its bytes.  Between items every non-hart twin buffer stays EMPTY, as `rmemP` asks.

* **`SbRealPDma.rmemPDma`**: `rmemP` is kept by the twin pair (issue by agent `NCPU` = `diskAgent`, then
  `SbCand.nextL … NCPU 0`) against `σ.storeDma pa n w` (`n ≠ 0`, a DRAM footprint, no reservation —
  `rmemP`'s `R-resv`).
* **`SbRealPDma.dmaReadTop`**: the device's DMA read (`dmaView`, the LANDED top) answers the twin's top
  bytes (`SbRealP.topLEq`): the device row's own buffer is empty at its heads, so the twin does not
  forward.

Spec: FAITHFUL (proof organisation; the device model is platform text, MachCSL's DMA lands at once).
Lean-only helpers `SbRealPDma.*`.
-/
import Weak.SbRealP

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std LeanRV64D
open Lbl PfStepTsoMem SbRealP

namespace SbRealPDma

/-- The twin's device pair (issue by the disk agent, then the landing of its only entry): the image and
buffers are kept, the landed log grows by the store's message. -/
theorem pairFields (c : SbCand.CandS) (base : Int) (vs : List (BitVec 8)) (k : WmClass)
    (hnil : c.sb NCPU = []) :
    (SbCand.nextL (SbCand.nextE c NCPU (LStore false base vs k)) NCPU 0).ms.msImg = c.ms.msImg ∧
    (SbCand.nextL (SbCand.nextE c NCPU (LStore false base vs k)) NCPU 0).ms.msLog =
      c.ms.msLog ++ [⟨base, vs, some NCPU, k⟩] ∧
    (SbCand.nextL (SbCand.nextE c NCPU (LStore false base vs k)) NCPU 0).sb = c.sb := by
  have hsb : (SbCand.nextE c NCPU (LStore false base vs k)).sb NCPU =
      [SbCand.issueEnt c NCPU false base vs k] := by
    show SbCand.updSb c.sb NCPU (c.sb NCPU ++ [_]) NCPU = _
    rw [SbCand.updSbEq, hnil]; rfl
  have hget : ((SbCand.nextE c NCPU (LStore false base vs k)).sb NCPU)[0]? =
      some (SbCand.issueEnt c NCPU false base vs k) := by rw [hsb]; rfl
  unfold SbCand.nextL
  rw [hget]
  refine ⟨rfl, rfl, ?_⟩
  show SbCand.updSb (SbCand.nextE c NCPU (LStore false base vs k)).sb NCPU
    (((SbCand.nextE c NCPU (LStore false base vs k)).sb NCPU).eraseIdx 0) = c.sb
  rw [hsb]
  funext j
  by_cases hj : j = NCPU
  · subst hj; rw [SbCand.updSbEq, hnil]; rfl
  · rw [SbCand.updSbNe _ _ _ _ hj]
    show SbCand.updSb c.sb NCPU (c.sb NCPU ++ [_]) j = c.sb j
    rw [SbCand.updSbNe _ _ _ _ hj]

/-- **THE DMA ROW**: the twin's device pair (the disk agent issues `LStore false (paZ pa) wvs k` and lands
it at once) is MachCSL's DMA write `σ.storeDma pa n w` (the label's bytes = `w`). -/
theorem rmemPDma (img : Image) (c : SbCand.CandS) (σ : MState) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) (wvs : List (BitVec 8)) (k : WmClass)
    (hram : ramBytes pa n) (hn0 : n ≠ 0) (hd : wvs.length = n)
    (hb : ∀ j, j < n → wvs[j]? = some (nthByte w j)) (hR : rmemP img c σ) :
    rmemP img (SbCand.nextL (SbCand.nextE c NCPU (LStore false (paZ pa) wvs k)) NCPU 0)
      (σ.storeDma pa n w) := by
  obtain ⟨himg, hlog, hlogB, hH, hsb, hoth, hresv, hnd, hok⟩ := hR
  have hnil : c.sb NCPU = [] := hoth NCPU (fun cpu => Nat.ne_of_gt (hartAgent_lt cpu))
  obtain ⟨hf1, hf2, hf3⟩ := pairFields c (paZ pa) wvs k hnil
  have hnw := noWrapOfRam pa n hram
  have hn := ramLen pa n hram
  have hll := hok.2.2.2.2.1
  have hnoR : ¬ anyReserve σ.resv pa n := by
    rintro ⟨c', rr, hrr, -⟩
    rw [hresv c'] at hrr; cases hrr
  have hok2 := σ.okP_storeDma pa n w hnoR hok
  have hfresh : ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ σ.top + 1 :=
    fun a H hH e he het => by have := stampLeTop hok hH he; omega
  have hlp2 : lpOf (σ.llog ++ [σ.top + 1]) (σ.top + 1) = some (σ.ltop + 1) := σ.okP_snoc_self hok
  have hcong : ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H →
      Hist.lview (lpOf (σ.llog ++ [σ.top + 1])) H = Hist.lview σ.lp H := fun a H hH =>
    Hist.lview_congr _ _ H (fun e he => σ.okP_lp_snoc hok a H hH e he)
  have hll' : σ.llog.length = c.ms.msLog.length := by
    have := congrArg List.length hlog
    simp [landAuthors] at this; omega
  have hE := MState.storeDma_of_ne σ pa n w hn0
  rw [hE] at hok2 ⊢
  have hstamp : ∀ (a : PAddr) (t : Nat), t ≠ σ.top + 1 →
      memStamp (σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) diskAgent) a t =
        memStamp σ.mem a t := by
    intro a t ht
    unfold memStamp
    by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      rw [landBytesIn _ _ pa n w _ _ (Nat.le_of_lt hn) hj, Option.bind_some,
        stampByteInsLanded _ _ _ t (Ne.symm ht), Std.ExtTreeMap.getD_eq_getD_getElem?]
      cases σ.mem[pa + BitVec.ofNat 64 j]? with
      | none => rfl
      | some H => rfl
    · rw [FlatMem.landBytes_get?_notin _ _ _ _ _ _ _ (fun j hj he => hfp ⟨j, hj, he⟩)]
  refine ⟨by rw [hf1]; exact himg, ?_, ?_, ⟨fun a ha => ?_, fun a ha => ?_⟩, fun c' => ?_, ?_,
    fun c' => hresv c', ?_, hok2⟩
  · show (SbCand.nextL (SbCand.nextE c NCPU (LStore false (paZ pa) wvs k)) NCPU 0).ms.msLog.map
        Wmsg.wmTid = (landAuthors (σ.log ++ [diskAgent]) (σ.llog ++ [σ.top + 1])).map some
    rw [hf2, landAuthorsSnoc, landAuthorsSnocLog σ.log σ.llog _ (fun t ht => hll t ht), List.map_append,
      List.map_append, hlog]
    simp [MState.top, diskAgent]
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hlogB a ha
    · simp at ha; rw [ha]; exact Nat.le_refl _
  · show ((σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) diskAgent).lview
      (lpOf (σ.llog ++ [σ.top + 1])))[a]? = some (TsoOfPf.histOf img
        (SbCand.nextL (SbCand.nextE c NCPU (LStore false (paZ pa) wvs k)) NCPU 0).ms.msLog (paZ a))
    rw [hf2]
    obtain ⟨H, hm, hl⟩ := lviewSomeInv (hH.1 a ha)
    rw [FlatMem.lview_get?, histOfSnoc]
    by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      rw [landBytesIn _ _ pa n w _ _ (Nat.le_of_lt hn) hj, getDOfSome hm, Option.map_some,
        Hist.lview_insLanded _ _ hlp2, hcong _ H hm, hl, msgByteIn pa n j wvs _ k hnw hj, hb j hj]
      simp [hll', diskAgent]
    · have hne : ∀ j, j < n → a ≠ pa + BitVec.ofNat 64 j := fun j hj he => hfp ⟨j, hj, he⟩
      rw [FlatMem.landBytes_get?_notin _ _ _ _ _ _ _ hne, hm, Option.map_some, hcong a H hm, hl,
        msgByteOut pa a n wvs _ k hd hne]
  · rw [FlatMem.lview_get?, FlatMem.landBytes_get?_notin _ _ _ _ _ _ _
      (fun j hj he => ha (by rw [he]; exact hram j hj)), lviewNoneOf (hH.2 a ha)]
    rfl
  · rw [hf3]
    refine forall2ImpMem (hsb c') ?_
    intro p e hp hr
    refine ⟨hr.1, hr.2.1, hr.2.2.1, fun a => ?_⟩
    have := sbStampBound hok hp
    show memStamp (σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) diskAgent) a p.1 = _
    rw [hstamp a p.1 (by omega)]
    exact hr.2.2.2 a
  · rw [hf3]; exact hoth
  · intro a H hH
    by_cases hfp : ∃ j, j < n ∧ a = pa + BitVec.ofNat 64 j
    · obtain ⟨j, hj, rfl⟩ := hfp
      change (σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) diskAgent)[_]? = _ at hH
      rw [landBytesIn _ _ pa n w _ _ (Nat.le_of_lt hn) hj] at hH
      obtain rfl := Option.some.inj hH
      refine ((insLandedPerm _ _ _).map HEnt.t).nodup_iff.2 ?_
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?]
      cases hm : σ.mem[pa + BitVec.ofNat 64 j]? with
      | none => simp
      | some H0 =>
        simp only [Option.getD_some, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
        exact ⟨fun e he het => hfresh _ H0 hm e he het, hnd _ H0 hm⟩
    · change (σ.mem.landBytes (lpOf (σ.llog ++ [σ.top + 1])) pa n w (σ.top + 1) diskAgent)[a]? = _ at hH
      rw [FlatMem.landBytes_get?_notin _ _ _ _ _ _ _ (fun j hj he => hfp ⟨j, hj, he⟩)] at hH
      exact hnd a H hH

/-- **THE DEVICE'S DMA READ** at a related state: MachCSL's `dmaView` (every byte the memory covers at its
LANDED top) holds of the twin's top bytes (`SbRealP.topLEq`) — a twin top read of the device row, whose
buffer is empty at its heads ([OWN.151]: no forwarding), answers MachCSL's DMA read. -/
theorem dmaReadTop (img : Image) (c : SbCand.CandS) (σ : MState) (hR : rmemP img c σ) (pa : PAddr)
    (n : Nat) (w : BitVec (8 * n)) (hram : ramBytes pa n)
    (htw : ∀ j, j < n → topByte img c.ms.msLog (paZ (pa + BitVec.ofNat 64 j)) = some (nthByte w j)) :
    dmaView σ pa n w := by
  intro j hj b hb
  rw [topLEq img c σ hR _ (hram j hj), htw j hj] at hb
  exact Option.some.inj hb

#print axioms Weak.SbRealPDma.rmemPDma
#print axioms Weak.SbRealPDma.dmaReadTop

end SbRealPDma

end Weak
