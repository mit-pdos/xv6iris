/-
Weak: **W5d-G G7 — the kill arms for cycles through instruction-fetch entries** (plan rev 52
§C top "G7-a"; owner ruling [OWN.101] = option 2; `PROGRESS-G7.md`).  Lean-only, no Rocq twin.

A cycle of the guarded kill (`racyDIO`, `CatLin.cycleKillCZ`) may cross into a segment `s` by the
FETCH ARM `gfetchE prev s.sgEntry` — an edge of the stored fragment, for a fetch item of hart `i`
at slot `k` one of `GraphFetch.fetchEdge`'s three kinds: E1′ (a fetched byte's source → an own
memory event at/after the slot), E2 (a contributor → a write `w′` to a fetched byte co-after its
source), E3 (another fetched byte's source → such a `w′`).  This file certifies such a segment
(`CatLin.CertC`, the cat certificate the Zifencei kill consumes):

* **E1′ — free** (`g7E1Chained`): the segment runs on the fetcher's hart from an event at/after the
  slot, so its exit is too; (Z2) in E1′ form (`gzFetch`) puts the source gmo-before it: `CSchained`.
* **E2/E3, `w′` realized BEFORE the fetch** (`gwix w′ ≤ gfcut G i k`: `w′` is in the log the fetch
  is replayed at) — **refuted from O1** (`g7EarlyRefuted`): at the replay state hart `i` is in user
  mode on a user-text byte of its table, so the export's `utextDiscAt` puts every history entry of
  the byte at or below `itv i`, the fetch reads at a view at or above `itv i` (`Lang.lean:395`) —
  so it reads the LATEST entry (`G7Fetch.utextLatest`), never one below `w′`'s; a kernel-text byte
  has no `w′` at all.  The replay state is the NAMED interface `fetchReplayOk` (W11-F's).
* **E2/E3, `w′` realized AFTER the fetch** — the NAMED premise `fetchLateChained` ([OWN.101]): the
  segment is `chainHyps`-certified from the edge's source (O2's after-direction; its proof comes
  after the capstone).
* **The fragment's provenance** — the NAMED interface `fetchProv`: every pair of `gdFetch` is a
  fetch edge of an item satisfying `gzFetch` (`GraphFabConf.gfexecConfZF` only has `F_em ⊆
  gdFetch`); `fetchProvOfEm` reduces it to "`gdFetch` ⊆ ⋃ the rows' fragments".
**`g7FetchCert`** assembles the four.

Spec (FIRST): RVWMO / riscv.cat have no instruction-fetch events; Zifencei — `fence.i` makes this
hart's later fetches see the stores visible to it, and says nothing about other harts' later
writes; Sail `fetch` (`Fetch.lean:233-288`) reads each halfword/word at `PC`; PMAs — Ziccif
atomicity only.  E1′ and (Z3) are the plan's NAMED hardware readings (§B(11)); the arms add no
trusted text beyond the three named interfaces/premises below.  Every helper is `Weak.G7Fetch.*`.
-/
import Weak.GraphFetchRetime
import Weak.RvwmoXv6Adequacy

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail LeanRV64D

/-! # 1. The segment of a cycle -/

/-- A same-hart run keeps the hart and does not go back in program order. -/
theorem G7Fetch.rtcSameLex (GD : Gdexec) (ad : List (Geid × Geid)) (hc : CatLin.rvwmoCatAD GD ad) :
    ∀ x y, rtc (CatLin.rsameC GD) x y → x.1 = y.1 ∧ x.2 ≤ y.2 := by
  intro x y h
  induction h with
  | refl => exact ⟨rfl, Nat.le_refl _⟩
  | tail _ h ih =>
    obtain ⟨h1, h2⟩ := CatLin.rsameCLex GD ad _ _ hc h
    exact ⟨ih.1.trans h1, by omega⟩

/-! # 2. E1′ — free -/

/-- The E1′ kind of a fetch edge. -/
def G7Fetch.fetchEdge1 (G : Gexec) (i k : Nat) (tvs : List (Nat × BitVec 8)) (x y : Geid) : Prop :=
  ∃ (j t : Nat) (v : BitVec 8) (k' : Nat), tvs[j]? = some (t, v) ∧ gwriteAt G t = some x ∧ k ≤ k' ∧
    gmem G (i, k') ∧ y = (i, k')

/-- **THE E1′ ARM**: a segment entered by an E1′ edge is CS-chained by (Z2). -/
theorem g7E1Chained (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (C : Geid → Prop) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (prev : Geid) (s : Seg)
    (hc : CatLin.rvwmoCatAD GD ad) (hz : gzFetch GD.gdG C i k base tvs)
    (he : G7Fetch.fetchEdge1 GD.gdG i k tvs prev s.sgEntry) (hrun : CatLin.segRunC GD s)
    (hm : gmem GD.gdG s.sgExit) : CatLin.CertC GD.gdG X prev s := by
  obtain ⟨j, t, v, k', hj, hx, hk, -, hy⟩ := he
  obtain ⟨h1, h2⟩ := G7Fetch.rtcSameLex GD ad hc _ _ hrun
  rw [hy] at h1 h2
  have hex : s.sgExit = (i, s.sgExit.2) := Prod.ext (by simpa using h1.symm) rfl
  refine .CSchained ?_
  rw [hex]
  rw [hex] at hm
  exact (hz j t v hj).2.1 prev s.sgExit.2 hx (by simp only at h2; omega) hm

/-! # 3. E2/E3 before the fetch — refuted from O1 -/

/-- **O1 at a user fetch** (`MachCSL.uTextDiscAt`): on a user-text byte of a user-mode hart's table,
an instruction fetch at a view at or above the hart's `itv` reads the LATEST entry of the byte's
(timestamp-descending) history: no entry is above the one it reads. -/
theorem G7Fetch.utextLatest (σ : MState) (h : CPU) (r : BitVec 44) (a : PAddr) (v : BitVec 64)
    (jj : Nat) (H : Hist) (tvn : Nat) (e e' : HEnt) (hD : uTextDiscAt σ)
    (hu : σ.regs h Register.cur_privilege = Privilege.User)
    (hs : satpTable (σ.regs h Register.satp) = some r) (hslot : uSlotNow σ.mem r a v)
    (ht : uepTextB v = true) (hj : jj < 4096)
    (hH : σ.mem[uepLeafPA v + BitVec.ofNat 64 jj]? = some H)
    (hdesc : H.Pairwise (fun x y => y.t < x.t)) (hitv : σ.itv h ≤ tvn)
    (hrd : Hist.readEnt (ifetchAgent h) tvn H = some e) (he' : e' ∈ H) : e'.t ≤ e.t := by
  have hall : ∀ x ∈ H, x.t ≤ σ.itv h := hD h r hu hs a v hslot ht jj hj H hH
  cases H with
  | nil => cases he'
  | cons x xs =>
    have hvis : x.visible (ifetchAgent h) tvn = true :=
      HEnt.visible_of_le _ _ _ (Nat.le_trans (hall x List.mem_cons_self) hitv)
    have hex : e = x := by
      unfold Hist.readEnt at hrd
      simp only [List.find?, hvis] at hrd
      exact (Option.some.inj hrd).symm
    subst hex
    rcases List.mem_cons.1 he' with rfl | hin
    · exact Nat.le_refl _
    · exact Nat.le_of_lt ((List.pairwise_cons.1 hdesc).1 e' hin)

/-- The E2/E3 kinds of a fetch edge: the target is a write to a fetched byte co-after its source. -/
def G7Fetch.fetchEdge23 (G : Gexec) (C : Geid → Prop) (base : Int) (tvs : List (Nat × BitVec 8))
    (x y : Geid) : Prop :=
  ∃ (j t : Nat) (v v' : BitVec 8), tvs[j]? = some (t, v) ∧ gwritesByte G y (base + (j : Int)) v' ∧
    t < gwix G y ∧
    (C x ∨ ∃ (l tl : Nat) (vl : BitVec 8), tvs[l]? = some (tl, vl) ∧ gwriteAt G tl = some x)

/-- A fetch edge is E1′ or E2/E3. -/
theorem G7Fetch.fetchEdgeCases (G : Gexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (x y : Geid) :
    GraphFetch.fetchEdge G C i k base tvs x y →
    G7Fetch.fetchEdge1 G i k tvs x y ∨ G7Fetch.fetchEdge23 G C base tvs x y := by
  rintro (h | ⟨j, t, v, v', hj, hy, ht, hc⟩ | ⟨j, t, v, v', l, tl, vl, hj, hy, ht, hl, hx⟩)
  · exact .inl h
  · exact .inr ⟨j, t, v, v', hj, hy, ht, .inl hc⟩
  · exact .inr ⟨j, t, v, v', hj, hy, ht, .inr ⟨l, tl, vl, hl, hx⟩⟩

/-- **THE FETCH'S REPLAY STATE (NAMED INTERFACE, W11-F's; `segRealized`/`readAt` style).**  For
every fetched byte of hart `i`'s fetch item at slot `k`: the byte is never written in the graph
(kernel text), or every write `w′` to it co-after the source and realized at the fetch's cut has,
at the fetch's replay state `σ` (the export holds), the fetch in USER mode on a user-text byte of
its table, reading at a view at or above `itv i` the entry `e` of the byte's descending history,
while `w′`'s entry `e′` is in that history above it.  *Truth reason*: W11-F replays the fetch at
`gwlog.take (gfcut G i k)` (`GraphFetchSpike.fetchCutPrefix`), `R` maps that log to `σ.mem`
(histories descending, stamp = position + 1, so `t < gwix w′ ≤ cut` puts `e′` above `e`), the fetch
step is MachCSL's i-fetch rule (`Lang.lean:395`), a user fetch's byte is on a `U∧X∧¬W` leaf of the
running table (xv6 maps user text R|X, `exec`'s `flags2perm`), a kernel fetch's on the never-written
kernel text (W3 `textPristine`). -/
def fetchReplayOk (G : Gexec) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    (∀ (w' : Geid) (v' : BitVec 8), ¬ gwritesByte G w' (base + (j : Int)) v') ∨
    ∀ (w' : Geid) (v' : BitVec 8), gwritesByte G w' (base + (j : Int)) v' → t < gwix G w' →
      gwix G w' ≤ gfcut G i k →
      ∃ (σ : MState) (h : CPU) (r : BitVec 44) (a : PAddr) (vs : BitVec 64) (jj : Nat) (H : Hist)
        (tvn : Nat) (e e' : HEnt),
        h.val = i ∧ Xv6.AccessDiscipline.xv6AccessDisc σ ∧ σ.mem.eagerOn σ.lp ∧
        σ.regs h Register.cur_privilege = Privilege.User ∧
        satpTable (σ.regs h Register.satp) = some r ∧ uSlotNow σ.mem r a vs ∧ uepTextB vs = true ∧
        jj < 4096 ∧ σ.mem[uepLeafPA vs + BitVec.ofNat 64 jj]? = some H ∧
        H.Pairwise (fun x y => y.t < x.t) ∧ σ.itv h ≤ tvn ∧
        Hist.readEnt (ifetchAgent h) tvn H = some e ∧ e' ∈ H ∧ e.t < e'.t

/-- **O1 under eager landing** (route P, D5): every entry has landed at its own stamp, so the
export's landed-view O1 (`uTextDiscAtP`) is the stamp form. -/
theorem G7Fetch.uTextDisc_ofP (σ : MState) (heo : σ.mem.eagerOn σ.lp) (h : uTextDiscAtP σ) : uTextDiscAt σ := by
  intro hc r hu hs a v hsl htx j hj H hH e he
  have := h hc r hu hs a v hsl htx j hj H hH e he
  rw [HEnt.landedLe_eager _ _ e (heo _ H hH e he)] at this
  exact of_decide_eq_true this

/-- **THE BEFORE-DIRECTION REFUTATION**: an E2/E3 edge whose target is realized at the fetch's cut
does not exist (O1, at the replay state). -/
theorem g7EarlyRefuted (G : Gexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) (x y : Geid) (hrep : fetchReplayOk G i k base tvs)
    (he : G7Fetch.fetchEdge23 G C base tvs x y) (hcut : gwix G y ≤ gfcut G i k) :
    False := by
  obtain ⟨j, t, v, v', hj, hy, ht, -⟩ := he
  rcases hrep j t v hj with hnw | hrp
  · exact hnw y v' hy
  · obtain ⟨σ, h, r, a, vs, jj, H, tvn, e, e', -, hD, heo, hu, hs, hslot, htx, hjj, hH, hdesc, hitv, hrd,
      he', hlt⟩ := hrp y v' hy ht hcut
    have := G7Fetch.utextLatest σ h r a vs jj H tvn e e' (G7Fetch.uTextDisc_ofP σ heo hD.2.2.2.2.2.1) hu hs
      hslot htx hjj hH hdesc hitv hrd he'
    omega

/-! # 4. E2/E3 after the fetch — the named premise ([OWN.101]) -/

/-- **THE AFTER-DIRECTION (NAMED PREMISE, [OWN.101]; O2's, proof after the capstone).**  A segment
entered by an E2/E3 edge of hart `i`'s fetch item at slot `k` whose target `w′` is realized AFTER
the fetch's cut is `chainHyps`-certified from the edge's source.  *Truth reason*: xv6 rewrites a
byte it fetched as user text only after the fetching process's epoch has ended (`exit`/`exec`
→ `freeproc`/`uvmfree`/`kfree`, `loadseg`), through a lock hand-off (`p->lock`, `wait_lock`,
`kmem.lock`) from the fetcher's hart — whose release's `fence rw,w` orders the contributors and the
sources before it — to the writer's acquire before `w′`. -/
def fetchLateChained (GD : Gdexec) (C : Geid → Prop) (i k : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ (x y : Geid) (s : Seg), G7Fetch.fetchEdge23 GD.gdG C base tvs x y →
    gfcut GD.gdG i k < gwix GD.gdG y → s.sgEntry = y → CatLin.segRunC GD s →
    chainHyps GD x s

/-! # 5. The fragment's provenance, and the assembly -/

/-- **THE FRAGMENT'S PROVENANCE (NAMED INTERFACE, W11-F's).**  Every pair of the stored fragment is
a fetch edge of a fetch item satisfying the trusted-base item `gzFetch`.  *Truth reason*: the
certifier's tagged graph stores exactly the rows' fragments (`gtFetch`, `forget` carries it), and
the hull (`gdHull`'s filter) and the re-timing (renaming both ends with the emissions) keep every
pair one; the bundle states only `F_em ⊆ gdFetch` (`GraphFetch.emFetchIn`). -/
def fetchProv (GD : Gdexec) : Prop :=
  ∀ x y, (x, y) ∈ GD.gdFetch →
    ∃ (C : Geid → Prop) (i k : Nat) (base : Int) (tvs : List (Nat × BitVec 8)),
      gzFetch GD.gdG C i k base tvs ∧ GraphFetch.fetchEdge GD.gdG C i k base tvs x y

/-- `fetchProv` from "every stored pair is a fetch edge of a row emission satisfying the slot". -/
theorem fetchProvOfEm (GD : Gdexec)
    (h : ∀ x y, (x, y) ∈ GD.gdFetch → ∃ (i : Nat) (em : Hemission),
      GraphFetch.emZif GD.gdG i em ∧ GraphFetch.emFetchEdge GD.gdG i em x y) :
    fetchProv GD := by
  intro x y hxy
  obtain ⟨i, em, hz, n, base, tvs, hn, he⟩ := h x y hxy
  exact ⟨_, i, _, base, tvs, hz n base tvs hn, he⟩

/-- **THE FETCH-ENTRY CERTIFICATE** (header): a segment of a cycle entered by the fetch arm is
certified — E1′ CS-chained, E2/E3 refuted before the cut, `chainHyps` after it. -/
theorem g7FetchCert (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (prev : Geid) (s : Seg) (hc : CatLin.rvwmoCatAD GD ad) (hx : gfetchE GD prev s.sgEntry)
    (hprov : fetchProv GD)
    (hrep : ∀ C i k base tvs, gzFetch GD.gdG C i k base tvs → fetchReplayOk GD.gdG i k base tvs)
    (hlate : ∀ C i k base tvs, gzFetch GD.gdG C i k base tvs → fetchLateChained GD C i k base tvs)
    (hrun : CatLin.segRunC GD s) (hm : gmem GD.gdG s.sgExit) : CatLin.CertC GD.gdG X prev s := by
  obtain ⟨C, i, k, base, tvs, hz, he⟩ := hprov _ _ hx.1
  rcases G7Fetch.fetchEdgeCases _ C i k base tvs _ _ he with h1 | h23
  · exact g7E1Chained GD ad X C i k base tvs prev s hc hz h1 hrun hm
  · by_cases hcut : gwix GD.gdG s.sgEntry ≤ gfcut GD.gdG i k
    · exact (g7EarlyRefuted GD.gdG C i k base tvs prev s.sgEntry (hrep C i k base tvs hz) h23 hcut).elim
    · exact chainHypsCertC GD ad X prev s hc
        (hlate C i k base tvs hz prev s.sgEntry s h23 (by omega) rfl hrun)

end Weak
