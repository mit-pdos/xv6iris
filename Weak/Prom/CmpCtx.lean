/-
Weak/Prom: **completeness S3a — the hart context** (the reference execution seen from one hart, and its memory
`memOf X` seen by machine v2).

`HCtx T trs ν X h sf` bundles what the simulation of hart `h` assumes: `X` is the concrete execution of the paths
`trs` under the load values `ν` (RefProg.lean `conc`), it is RVWMO-consistent (`rvwmoRef`), has no I/O regions, is
single-size (NA-6), its path conditions hold (`condsOk`), the program is in S3a's scope, and `sf` is hart `h`'s final
symbolic state.  Lemmas: hart `h`'s events of `X` are `sf`'s concretised events (`HCtx.sk`, `HCtx.ev`, `HCtx.id`);
program order is the order of `ii` (`HCtx.po`); answered and written bytes are bytes (`HCtx.rdat_lt`, `wdat_lt`);
`memOf X` holds each store's bytes at its view (`memByte_st`) and nothing else (`writesIn_memOf`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CmpStep

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref

/-- THE HART CONTEXT of the simulation. -/
structure HCtx (T : Test) (trs : List SSt) (ν : Val) (X : Exec) (h : Nat) (sf : SSt) : Prop where
  xc : X = conc T trs ν X.gmo
  ref : rvwmoRef X
  io : X.io = []
  ss : singleSize X
  cond : condsOk ν trs = true
  scope : progS3aB T = true
  tr : trs[h]? = some sf

namespace HCtx

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem sevAt_eq (c : HCtx T trs ν X h sf) {j : Nat} {se : SEv} (hj : sf.evs[j]? = some se) :
    sevAt trs (h, j) = se := by
  simp [sevAt, c.tr, hj]

theorem sk (c : HCtx T trs ν X h sf) {j : Nat} {se : SEv} (hj : sf.evs[j]? = some se) :
    X.sk (h, j) = se.sk := by
  rw [c.xc, conc_sk, sskOf, c.sevAt_eq hj]

theorem id (c : HCtx T trs ν X h sf) {j : Nat} {se : SEv} (hj : sf.evs[j]? = some se) : (h, j) ∈ X.ids := by
  rw [c.xc, conc_ids]
  refine (mem_idsOf _ _).2 ⟨sf.evs, by simp [c.tr], (List.getElem?_eq_some_iff.1 hj).1⟩

theorem ev (c : HCtx T trs ν X h sf) {j : Nat} {se : SEv} (hj : sf.evs[j]? = some se) :
    X.ev (h, j) = concEv ν h j se := by
  have hid := c.id hj
  rw [c.xc, conc_ids] at hid
  rw [c.xc, conc_ev _ _ _ _ _ hid, c.sevAt_eq hj]

theorem img (c : HCtx T trs ν X h sf) : X.img = T.imgF := by rw [c.xc]; rfl

theorem io' (c : HCtx T trs ν X h sf) (e : EvId) : isIo X e = false := isIo_nil X c.io e

theorem po (c : HCtx T trs ν X h sf) {j j' : Nat} {se se' : SEv} (hj : sf.evs[j]? = some se)
    (hj' : sf.evs[j']? = some se') : poX X (h, j) (h, j') = decide (se.sk.ii < se'.sk.ii) := by
  simp [poX, poS, c.sk hj, c.sk hj']

theorem po_of (c : HCtx T trs ν X h sf) {j j' : Nat} {se se' : SEv} (hj : sf.evs[j]? = some se)
    (hj' : sf.evs[j']? = some se') (hlt : se.sk.ii < se'.sk.ii) : poX X (h, j) (h, j') = true := by
  rw [c.po hj hj']; simpa using hlt

/-- Every symbolic state of `sf`'s hart satisfies the path conditions and alignment (RefProg `condsOk`). -/
theorem condsSf (c : HCtx T trs ν X h sf) :
    sf.conds.all (fun (cc, a, b, t) => brEval cc (a.eval ν) (b.eval ν) == t) = true ∧
    sf.evs.all (fun se => !se.sk.kind.isAcc || (se.addr.eval ν % se.sk.sz == 0)) = true := by
  have := List.all_eq_true.1 c.cond sf (List.mem_of_getElem? c.tr)
  simpa only [Bool.and_eq_true] using this

theorem gmo_of (c : HCtx T trs ν X h sf) {j : Nat} {se : SEv} (hj : sf.evs[j]? = some se)
    (hm : se.sk.kind.isMem = true) : (h, j) ∈ X.gmo :=
  (mem_gmo c.ref _).2 ⟨c.id hj, by rw [c.sk hj]; exact hm⟩

/-- A load returns its size in bytes (rvwmoRef's `evWf`). -/
theorem rdat_len (c : HCtx T trs ν X h sf) {e : EvId} (he : e ∈ X.ids) (hl : (X.sk e).kind.isLoad = true) :
    (X.ev e).rdat.length = (X.sk e).sz := (c.ref.1.2.1 e he).1 hl

theorem wdat_len' (hX : rvwmoRef X) {e : EvId} (he : e ∈ X.ids) (hs : (X.sk e).kind.isStore = true) :
    (X.ev e).wdat.length = (X.sk e).sz := (hX.1.2.1 e he).2 hs

end HCtx

/-! ## Bytes -/

theorem byteList_lt (v sz : Nat) : ∀ b ∈ byteList v sz, b < 256 := by
  intro b hb
  simp only [byteList, List.mem_map, List.mem_range] at hb
  obtain ⟨k, _, rfl⟩ := hb
  exact Nat.mod_lt _ (by decide)

theorem lookup_getD_lt : ∀ (l : List (Nat × Nat)) (x : Nat), (∀ xv ∈ l, xv.2 < 256) → (l.lookup x).getD 0 < 256
  | [], _, _ => by simp
  | (k, v) :: ps, x, h => by
    simp only [List.lookup]
    split
    · exact h (k, v) (List.mem_cons_self ..)
    · exact lookup_getD_lt ps x (fun xv hxv => h xv (List.mem_cons_of_mem _ hxv))

theorem imgF_lt (T : Test) (hT : progS3aB T = true) (x : Nat) : T.imgF x < 256 := by
  unfold Test.imgF
  apply lookup_getD_lt
  have := hT
  simp only [progS3aB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.2

/-- A store's written bytes are bytes. -/
theorem wdat_lt {ν : Val} {h i : Nat} {se : SEv} : ∀ b ∈ (concEv ν h i se).wdat, b < 256 := by
  intro b hb
  simp only [concEv] at hb
  split at hb
  · exact byteList_lt _ _ b hb
  · simp at hb

theorem wbyte_lt {X : Exec} (hXw : ∀ e, ∀ b ∈ (X.ev e).wdat, b < 256) (e : EvId) (x : Nat) :
    wbyte (X.ev e) x < 256 := by
  unfold wbyte
  cases hb : (X.ev e).wdat[x - (X.ev e).pa]? with
  | none => simp
  | some b => simpa using hXw e b (List.mem_of_getElem? hb)

namespace HCtx

variable {T : Test} {trs : List SSt} {ν : Val} {X : Exec} {h : Nat} {sf : SSt}

theorem wdatAll (c : HCtx T trs ν X h sf) : ∀ e, ∀ b ∈ (X.ev e).wdat, b < 256 := by
  intro e b hb
  rw [c.xc] at hb
  unfold Exec.ev conc at hb
  simp only [List.getElem?_mapIdx] at hb
  have hd : (default : Ev).wdat = [] := rfl
  cases h1 : trs[e.1]? with
  | none => rw [h1] at hb; simp only [Option.map_none, Option.bind_none, Option.getD_none, hd] at hb; cases hb
  | some s =>
    rw [h1] at hb
    simp only [Option.map_some, Option.bind_some, List.getElem?_mapIdx] at hb
    cases h2 : s.evs[e.2]? with
    | none => rw [h2] at hb; simp only [Option.map_none, Option.getD_none, hd] at hb; cases hb
    | some se => rw [h2] at hb; exact wdat_lt b hb

theorem lvVal_lt (c : HCtx T trs ν X h sf) (r : EvId) (x : Nat) : lvVal X r x < 256 := by
  unfold lvVal
  split
  · exact wbyte_lt c.wdatAll _ _
  · rw [c.img]; exact imgF_lt T c.scope x

/-- A load's answered bytes are bytes (the load value axiom). -/
theorem rdat_lt (c : HCtx T trs ν X h sf) {r : EvId} (hr : r ∈ X.ids) (hl : (X.sk r).kind.isLoad = true) :
    ∀ b ∈ (X.ev r).rdat, b < 256 := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hk' : k < (X.sk r).sz := by rw [← c.rdat_len hr hl]; exact hk
  have := ldVal c.ref c.io hr hl hk'
  rw [List.getElem?_eq_getElem hk] at this
  rw [Option.some.inj this]
  exact c.lvVal_lt _ _

end HCtx

/-! ## The memory `memOf X`, as machine v2 reads it -/

theorem msgOf_byteAt {X : Exec} (hX : rvwmoRef X) {w : EvId} (hw : w ∈ X.ids) (hs : isSt X w = true) (x : Nat) :
    (msgOf X w).byteAt (x : Int) =
      if touches (X.ev w) x then some (bv8 (wbyte (X.ev w) x)) else none := by
  have hlen := HCtx.wdat_len' hX hw hs
  unfold PMsg.byteAt msgOf
  simp only
  unfold Exec.sk at hlen
  by_cases ht : touches (X.ev w) x = true
  · rw [if_pos ht]
    simp only [touches, decide_eq_true_eq] at ht
    rw [if_pos (by omega)]
    have hi : x - (X.ev w).pa < (X.ev w).wdat.length := by omega
    have : ((x : Int) - ((X.ev w).pa : Int)).toNat = x - (X.ev w).pa := by omega
    rw [this, List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [wbyte, List.getElem?_eq_getElem hi]
  · rw [if_neg ht]
    simp only [touches, decide_eq_true_eq, not_and, Nat.not_lt] at ht
    split
    · rename_i hle
      have hx : (X.ev w).pa ≤ x := by omega
      have : ((x : Int) - ((X.ev w).pa : Int)).toNat = x - (X.ev w).pa := by omega
      rw [this, List.getElem?_map, List.getElem?_eq_none (by have := ht hx; omega)]
      rfl
    · rfl

theorem isSt_of_store {X : Exec} {w : EvId} (h : (X.sk w).kind.isStore = true) : isSt X w = true := h

/-- A store's bytes are at its view in `memOf X`. -/
theorem memByte_st {X : Exec} (hX : rvwmoRef X) (img : Image) {w : EvId} (hw : w ∈ X.gmo)
    (hs : isSt X w = true) {x : Nat} (ht : touches (X.ev w) x = true) :
    memByte img (memOf X) (vo X w) (x : Int) = some (bv8 (wbyte (X.ev w) x)) := by
  have hpos := voG_st_pos X X.gmo w hw hs
  obtain ⟨k, hk⟩ : ∃ k, vo X w = k + 1 := ⟨vo X w - 1, by unfold vo; omega⟩
  have hm := memG_voG X X.gmo w hw hs
  rw [hk]
  simp only [memByte]
  unfold memOf
  unfold vo at hk
  rw [hk] at hm
  simp only [Nat.add_sub_cancel] at hm
  rw [hm, Option.bind_some, msgOf_byteAt hX ((mem_gmo hX w).1 hw).1 hs, if_pos ht]

/-- Every write `memOf X` holds in a window is a store of `X` with its view in the window. -/
theorem writesIn_memOf {X : Exec} (hX : rvwmoRef X) {x : Nat} {lo hi : Nat}
    (h : writesIn (memOf X) (x : Int) lo hi) :
    ∃ w, w ∈ X.gmo ∧ isSt X w = true ∧ writesB (X.ev w) x = true ∧ lo < vo X w ∧ vo X w ≤ hi := by
  obtain ⟨t, h1, h2, m, hm, hb⟩ := h
  have hlen : t ≤ (memOf X).length := by
    have := (List.getElem?_eq_some_iff.1 hm).1; omega
  obtain ⟨w, hw, hws, hv, hm'⟩ := memG_at X X.gmo (gmo_nodup hX) t (by omega) hlen
  unfold memOf at hm
  rw [hm'] at hm
  cases hm
  rw [msgOf_byteAt hX ((mem_gmo hX w).1 hw).1 hws] at hb
  have ht : touches (X.ev w) x = true := by
    cases htt : touches (X.ev w) x
    · rw [htt] at hb; simp at hb
    · rfl
  refine ⟨w, hw, hws, ?_, by unfold vo; omega, by unfold vo; omega⟩
  simp [writesB, ht]
  exact hws

end Weak.Prom.Cmp
