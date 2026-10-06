/-
Weak: **projecting `WeakInterp.wrun` onto `WeakAxiomatic.execWf`** (M6 / W4
"Projection lemmas").

Rocq: `iris/WeakInterpProj.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: `WeakPromiseBridge` projects the FULL promising
machine onto the canonical axiomatic LTS; this file does the same for the OTHER
consumer of `WeakMem` — the Sail interpreter `WeakInterp.wrun`:

    one agent's `wrun` step  ⟶  an extension of a `WeakAxiomatic` execution

The projection is PER AGENT.  A `Wmstate` is one hart's view of the machine; an
`Mstate` carries the log plus EVERY agent's `Wstate`.  So the state relation
`wsMatch i s σ` constrains only agent `i`'s slot and FRAMES the others, and the
extension lemma reports that the framed slots did not move.

WHAT THE PROJECTION KEEPS AND WHAT IT DROPS (sound for THIS direction: every
emitted step is legal; the projection is not claimed onto):
(1) REGISTERS, DEVICES AND TRACE OUTCOMES ARE INVISIBLE: `wsetReg`/`wsetDev` and
    every announce/exception/cycle outcome move neither the image, the log nor
    the `Wstate`, so those arms emit no event.  MMIO is silent (no device label).
(2) (Rocq: COHERENT READS ARE SILENT.)  REPLACED under O2 — see deviation 3: an
    i-cache FETCH now projects to a plain `LLoad` under extra premises.
(3) THE `akLatest` PINNING IS DROPPED: `rdOk` asks only for readability, so a
    pinned read projects to a plain `LLoad` (cf. `WeakMem.latestReadable`).
(4) AN AMO IS SPLIT, NOT FUSED: the Sail model emits an exclusive `memRead` and a
    conditional `memWrite`; they project to an `LLoad` and an `LStore`, never an
    `LRmw` (the atomicity LINK is lost; `rmwLatest` is not needed).  IF W5 EVER
    NEEDS THE RMW FUSED, THIS FILE IS WHERE IT CHANGES.
(5) AN HONEST ADDED PREMISE: `nzWrites` — `mstep`'s store arm demands a nonempty
    message, while `wwritePost` appends a zero-byte message for a width-0
    `memWrite`; widths are 1/2/4/8 in every RISC-V access.
ADDRESSING: `WeakInterp.accAddr pa j = paZ pa + j` and `WeakAxiomatic`'s
`accAddr base j = base + j` agree at `base = paZ pa` by conversion.

DEPENDENCIES: `WeakInterp` (hence the Sail model), `WeakAxiomatic`, and (Lean
only, deviation 3) `WeakPromiseBridge` for `wsEqr`.  Nothing Iris.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1.  The Rocq `Reflexive`/`Transitive`
   instances of `exec_extends` are the theorems `execExtendsRefl`/
   `execExtendsTrans`.  File-qualified (orchestrator duplicated-name rule):
   `WeakInterpProj.wbytes`, `WeakInterpProj.wstep`.
2. VOCABULARY: `M X` ↦ `SailM X`, `prefix_of` ↦ `List.IsPrefix` (`<+:`),
   `seq 0 n` ↦ `List.range' 0 n`, `N` widths ↦ `Nat`.  `wrunFetchOk`'s write arms
   resume with `.Ok (some true)`, `wrun`'s answer (WeakInterp deviation 5).
   `wbytes` is width-generic as in Rocq, spelled with `extractLsb'` (MachCSL's `nthByte` is at width `8*n`
   only; `wbytesLookup` states it at `8*m` with `nthByte`, the definitional
   unfolding, and `wbytesLookupGen` at any width).  `nzWrites` has one arm per
   lean-sail `Outcome` constructor (Rocq: a wildcard), plus `True` at a model
   `.error` node (`wrun` is stuck there).  The barrier arm of `wrun` is
   `wbarrierPost` (Stage B: it also moves `wmItv`, which `wsMatch` does not see),
   so `execBarrier` is stated, as in Rocq, at `wsetWs s (barrierPost s.wmWs b)`,
   and `wrunExec` converts by conversion.
3. O2 — THE INSTRUCTION FETCH (owner decision (B), 2026-10-06).  Rocq's arm (2)
   projected an `ak_coh` read to NO event (dead for rv64d then).  Under O2 an
   `akIfetch` read is a LIVE i-cache read (`WeakInterp` header) and the AxSL tier
   keeps fetches as graph reads (D1), so the fetch projects to the axiomatic
   PLAIN load `LLoad false (paZ pa) ts (wbytes n w)`.  It cannot do so
   unconditionally: `MStepLoad` needs `rdOk` (readability at `loadVpre`), which
   `ifetchByteOk` does not imply (a stale pre-`fence.i` fetch), and its post-state
   `loadPostRun` differs from the fetch's IDENTITY post-state.  Changes:
   - THE EXTRA PREMISES (`wFetchLoadOk s pa n ts`), at each fetch:
     (i)  every fetched byte is `readable (wimg s) s.wmLog s.wmWs (loadVpre
          s.wmWs false) (accAddr pa j) ts[j]!` (`rdOk` minus the value
          conjunct, which `wreadOk` gives);
     (ii) `wsEqr (loadPostRun s.wmWs false (paZ pa) ts) s.wmWs` (field form:
          `WeakPromiseBridge.wsEqrLoadPostRunSelf`).
     `execRead` takes `akIfetch = true → wFetchLoadOk …`; the run-level form is
     `wrunFetchOk tid m s x s'` (Lean-only): every fetch on a `wrun` from `s` to
     `(x, s')` satisfies it — a recursion mirroring `wrun` arm for arm.
     `wrunExec` and `WeakInterpProj.wstep` (hence `wrunChainExec`,
     `wrunExecWf`) carry it.  Discharge for fetch-free code:
     `wrunFetchOkNoIfetch` (`noIfetch m`, Lean-only, `nzWrites`-shaped).
   - THE MATCH IS WEAKENED: `wsMatch`'s third conjunct `ms_ws σ i = wm_ws s`
     becomes `wsEqr (σ.msWs i) s.wmWs` (the bridge's T1-D relation), and
     `wrunExecWf`'s `ews E _ i = wm_ws s` becomes `wsEqr (ews E _ i) s.wmWs`
     (image, log and the framed agents are still EQUAL).  Why not keep
     equality and ask `loadPostRun … = s.wmWs`: `loadPostAt` inserts a `wCoh`
     entry unconditionally, so the equality FAILS whenever `wCoh` lacks a
     fetched address — every fetch from `wsInit` — and it would also demand
     `wRes = none` and `wLdv`/`wVcap` pre-raised.  `wsEqr` ignores exactly
     `wRegv`/`wVcap`/`wLdv`/`wTbank`/`wRes`, none of which `wrun`'s admissibility
     or post-states read (no register views here; `wmClassOf` reads `wRelp`),
     and compares `coh` pointwise; `coh`/`wVrOld` cannot be ignored (later
     reads check them), so (ii) constrains exactly those.  (i) is `MStepLoad`'s
     own side condition and (ii) is necessary and sufficient for the `wsEqr`
     step: the smallest sound pair.
   - Lean-only helpers: `wFetchLoadOk`, `wrunFetchOk`, `noIfetch`,
     `wrunFetchOkNoIfetch`, `wsEqrStorePostRun`, `execLoad` (the common load
     step of both read arms), `wbytesLookupGen`.

**Rocq → Lean name map.**  `wbytes` ↦ `WeakInterpProj.wbytes`; `wbytes_length`
↦ `wbytesLength`; `wbytes_lookup` ↦ `wbytesLookup`; `wbytes_nonnil` ↦
`wbytesNonnil`; `wwrite_msg_wbytes` ↦ `wwriteMsgWbytes`; `ws_match` ↦
`wsMatch`; `exec_extends` ↦ `execExtends`; `exec_extends_refl/trans` ↦
`execExtendsRefl/Trans`; `exec_extends_img` ↦ `execExtendsImg`; `exec_extend` ↦
`execExtend`; `proj_ext` ↦ `projExt`; `proj_ext_refl/trans` ↦
`projExtRefl/Trans`; `exec_fence` ↦ `execFence`; `exec_barrier` ↦
`execBarrier`; `exec_read` ↦ `execRead`; `exec_write` ↦ `execWrite`;
`nz_writes` ↦ `nzWrites`; `wrun_exec` ↦ `wrunExec`; `wstep` ↦
`WeakInterpProj.wstep`; `wrun_chain_exec` ↦ `wrunChainExec`; `wrun_exec_wf` ↦
`wrunExecWf`.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**Statements checked** (by hand, against Rocq): all of them; the changed ones
are `wsMatch`, `execRead`, `wrunExec`, `WeakInterpProj.wstep`, `wrunExecWf`
(deviation 3) and `wbytes`/`wbytesLookup` (deviation 2).
-/
import Weak.WeakInterp
import Weak.WeakPromiseBridge

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 1. The byte list of an access

Both sides spell a multi-byte access's payload as the little-endian byte list
of its value; `wwriteMsg` already uses exactly this list (`wwriteMsgWbytes` is
`rfl`). -/

def WeakInterpProj.wbytes (n : Nat) {w : Nat} (v : BitVec w) : List (BitVec 8) :=
  (List.range' 0 n).map (fun j : Nat => v.extractLsb' (8 * j) 8)

theorem wbytesLength (n : Nat) {w : Nat} (v : BitVec w) :
    (WeakInterpProj.wbytes n v).length = n := by
  simp [WeakInterpProj.wbytes]

theorem wbytesLookupGen (n : Nat) {w : Nat} (v : BitVec w) (j : Nat) :
    j < n → (WeakInterpProj.wbytes n v)[j]? = some (v.extractLsb' (8 * j) 8) := by
  intro hj
  simp [WeakInterpProj.wbytes, hj]

theorem wbytesLookup (n : Nat) {m : Nat} (v : BitVec (8 * m)) (j : Nat) :
    j < n → (WeakInterpProj.wbytes n v)[j]? = some (nthByte v j) :=
  wbytesLookupGen n v j

theorem wbytesNonnil (n : Nat) {w : Nat} (v : BitVec w) : n ≠ 0 → WeakInterpProj.wbytes n v ≠ [] := by
  intro hn hc
  have := congrArg List.length hc
  rw [wbytesLength] at this
  exact hn this

theorem wwriteMsgWbytes (tid : Option Nat) (k : WmClass) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) :
    wwriteMsg tid k pa n v = ⟨paZ pa, WeakInterpProj.wbytes n v, tid, k⟩ := rfl

/-! ## 2. The state relation and execution extension -/

/-- Agent `i`'s slot is pinned (up to `wsEqr`, deviation 3); every other agent's
`Wstate` is framed. -/
def wsMatch (i : Nat) (s : Wmstate) (σ : Mstate) : Prop :=
  σ.msImg = wimg s ∧ σ.msLog = s.wmLog ∧ wsEqr (σ.msWs i) s.wmWs

/-- "`E'` continues `E`": both components grow at the end. -/
def execExtends (E E' : Exec) : Prop :=
  E.exSt <+: E'.exSt ∧ E.exTr <+: E'.exTr

theorem execExtendsRefl (E : Exec) : execExtends E E :=
  ⟨List.prefix_refl _, List.prefix_refl _⟩

theorem execExtendsTrans {E1 E2 E3 : Exec} :
    execExtends E1 E2 → execExtends E2 E3 → execExtends E1 E3 := by
  rintro ⟨h1, h2⟩ ⟨h3, h4⟩
  exact ⟨h1.trans h3, h2.trans h4⟩

theorem execExtendsImg (E E' : Exec) : execWf E → execExtends E E' → exImg E' = exImg E := by
  rintro hwf ⟨hst, _⟩
  obtain ⟨σ0, hσ0⟩ := someOfIsSome (execStLen E 0 hwf (Nat.zero_le _))
  simp only [exImg, eimg]
  rw [sttLookup _ _ _ hσ0, sttLookup _ _ _ (prefix_lookup_Some hσ0 hst)]

/-- Appending ONE machine step, with the new final state named. -/
theorem execExtend (E : Exec) (i : Nat) (lb : Lbl) (σ' : Mstate) :
    execWf E → mstep (stt E E.exTr.length) i lb σ' →
    ∃ E', execWf E' ∧ execExtends E E' ∧ stt E' E'.exTr.length = σ' := by
  intro hE hms
  have hlen := hE.1
  refine ⟨⟨E.exSt ++ [σ'], E.exTr ++ [⟨i, lb⟩]⟩, execSnoc E ⟨i, lb⟩ σ' hE hms,
    ⟨List.prefix_append _ _, List.prefix_append _ _⟩, ?_⟩
  simp only [stt, List.length_append, List.length_singleton]
  rw [lookup_app_r (by omega)]
  have h0 : E.exTr.length + 1 - E.exSt.length = 0 := by omega
  rw [h0]
  rfl

/-- The shape every arm below produces. -/
def projExt (i : Nat) (s' : Wmstate) (E E' : Exec) : Prop :=
  execWf E' ∧ execExtends E E' ∧
  wsMatch i s' (stt E' E'.exTr.length) ∧
  ∀ j, j ≠ i → (stt E' E'.exTr.length).msWs j = (stt E E.exTr.length).msWs j

theorem projExtRefl (i : Nat) (s : Wmstate) (E : Exec) :
    execWf E → wsMatch i s (stt E E.exTr.length) → projExt i s E E :=
  fun hE hm => ⟨hE, execExtendsRefl E, hm, fun _ _ => rfl⟩

theorem projExtTrans (i : Nat) (s1 s2 : Wmstate) (E E1 E2 : Exec) :
    projExt i s1 E E1 → projExt i s2 E1 E2 → projExt i s2 E E2 := by
  rintro ⟨_, hx1, _, hf1⟩ ⟨h2, hx2, hm2, hf2⟩
  exact ⟨h2, execExtendsTrans hx1 hx2, hm2, fun j hne => by rw [hf2 j hne, hf1 j hne]⟩

/-! ## 3. The event-emitting arms -/

/-- (Lean-only) `storePostRun` is a `wsEqr` congruence. -/
theorem wsEqrStorePostRun (w1 w2 : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    wsEqr w1 w2 → wsEqr (storePostRun w1 rl base n t) (storePostRun w2 rl base n t) := by
  intro he
  have := wsEqrStorePostRunD w1 w2 rl 0 0 base n t he
  rwa [storePostRunD0] at this

/-- FENCE: the one-step case. -/
theorem execFence (E : Exec) (i : Nat) (s : Wmstate) (pr pw sr sw : Bool) :
    execWf E → wsMatch i s (stt E E.exTr.length) →
    ∃ E', projExt i (wsetWs s (fencePost s.wmWs pr pw sr sw)) E E' := by
  intro hE hm
  obtain ⟨himg, hlog, hws⟩ := hm
  obtain ⟨E', hE', hext, hst⟩ := execExtend E i (.LFence pr pw sr sw) _ hE
    (mstep.MStepFence pr pw sr sw)
  refine ⟨E', hE', hext, ?_, ?_⟩ <;> rw [hst]
  · refine ⟨himg, hlog, ?_⟩
    show wsEqr (updWs _ i _ i) _
    rw [updWsEq]
    exact wsEqrFencePost _ _ _ _ _ _ hws
  · intro j hne
    exact updWsNe _ _ _ _ hne

/-- The whole barrier lattice: nine single fences, `fence.tso` = two chained
fences, `fence.i` = no event (the identity on `Wstate`s). -/
theorem execBarrier (E : Exec) (i : Nat) (s : Wmstate) (b : barrier_kind) :
    execWf E → wsMatch i s (stt E E.exTr.length) →
    ∃ E', projExt i (wsetWs s (barrierPost s.wmWs b)) E E' := by
  intro hE hm
  cases b
  case Barrier_RISCV_rw_rw => exact execFence E i s true true true true hE hm
  case Barrier_RISCV_r_rw => exact execFence E i s true false true true hE hm
  case Barrier_RISCV_r_r => exact execFence E i s true false true false hE hm
  case Barrier_RISCV_rw_w => exact execFence E i s true true false true hE hm
  case Barrier_RISCV_w_w => exact execFence E i s false true false true hE hm
  case Barrier_RISCV_w_rw => exact execFence E i s false true true true hE hm
  case Barrier_RISCV_rw_r => exact execFence E i s true true true false hE hm
  case Barrier_RISCV_r_w => exact execFence E i s true false false true hE hm
  case Barrier_RISCV_w_r => exact execFence E i s false true true false hE hm
  case Barrier_RISCV_tso =>
    -- fence.tso = fence r,r ; fence rw,w
    obtain ⟨E1, hp1⟩ := execFence E i s true false true false hE hm
    obtain ⟨E2, hp2⟩ := execFence E1 i (wsetWs s (fencePost s.wmWs true false true false))
      true true false true hp1.1 hp1.2.2.1
    exact ⟨E2, projExtTrans _ _ _ _ _ _ hp1 hp2⟩
  case Barrier_RISCV_i => exact ⟨E, projExtRefl i _ E hE hm⟩

/-- THE FETCH PROJECTION PREMISE (Lean-only, deviation 3): the fetched bytes are
also readable as a PLAIN load, and the plain load's update is `wsEqr`-inert. -/
def wFetchLoadOk (s : Wmstate) (pa : PAddr) (n : Nat) (ts : List Nat) : Prop :=
  (∀ j : Nat, j < n →
    readable (wimg s) s.wmLog s.wmWs (loadVpre s.wmWs false) (WeakInterp.accAddr pa j) ts[j]!) ∧
  wsEqr (loadPostRun s.wmWs false (paZ pa) ts) s.wmWs

/-- (Lean-only) The common load step: an `rdOk` read at `s`, whose `loadPostRun`
is `wsEqr` to the interpreter's new `Wstate` `ws'`. -/
theorem execLoad (E : Exec) (i : Nat) (s : Wmstate) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (ws' : Wstate) :
    execWf E → wsMatch i s (stt E E.exTr.length) →
    rdOk (wimg s) s.wmLog s.wmWs aq base ts vs →
    wsEqr (loadPostRun s.wmWs aq base ts) ws' →
    ∃ E', projExt i (wsetWs s ws') E E' := by
  intro hE hm hrd hharm
  obtain ⟨himg, hlog, hws⟩ := hm
  have hrd' : rdOk (stt E E.exTr.length).msImg (stt E E.exTr.length).msLog
      ((stt E E.exTr.length).msWs i) aq base ts vs := by
    rw [himg, hlog]
    exact wsEqrRdOk _ _ _ _ _ _ _ _ (wsEqrSym hws) hrd
  obtain ⟨E', hE', hext, hst⟩ := execExtend E i (.LLoad aq base ts vs) _ hE
    (mstep.MStepLoad aq base ts vs hrd')
  refine ⟨E', hE', hext, ?_, ?_⟩ <;> rw [hst]
  · refine ⟨himg, hlog, ?_⟩
    show wsEqr (updWs _ i _ i) _
    rw [updWsEq]
    exact wsEqrTrans (wsEqrLoadPostRun _ _ _ _ _ hws) hharm
  · intro j hne
    exact updWsNe _ _ _ _ hne

/-- LOAD.  A weak read emits one `LLoad` whose `rdOk` is `wreadOk` minus the
`akLatest` pinning (header (3)); deviation 3: an i-cache FETCH emits the plain
`LLoad false …` under `wFetchLoadOk` (Rocq: no event). -/
theorem execRead (E : Exec) (i : Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (ts : List Nat) (w : BitVec (8 * n)) :
    execWf E → wsMatch i s (stt E E.exTr.length) →
    wreadOk s ak pa n ts w →
    (ak.akIfetch = true → wFetchLoadOk s pa n ts) →
    ∃ E', projExt i (wreadPost s ak pa ts) E E' := by
  intro hE hm hok hfe
  obtain ⟨hlen, hbytes⟩ := hok
  -- the per-byte shape both arms share
  have hshape : ∀ (aq : Bool),
      (∀ j : Nat, j < n →
        readable (wimg s) s.wmLog s.wmWs (loadVpre s.wmWs aq) (WeakInterp.accAddr pa j) ts[j]!) →
      rdOk (wimg s) s.wmLog s.wmWs aq (paZ pa) ts (WeakInterpProj.wbytes n w) := by
    intro aq hrdb
    refine ⟨by rw [wbytesLength, hlen], fun j t v ht hv => ?_⟩
    obtain ⟨hjl, hjt⟩ := List.getElem?_eq_some_iff.1 ht
    have hj : j < n := by omega
    rw [wbytesLookup n w j hj] at hv
    injection hv with hv
    subst hv
    have htj : ts[j]! = t := by rw [getBangLt _ _ hjl]; exact hjt
    have hb := hbytes j hj
    rw [htj] at hb
    have hr := hrdb j hj
    rw [htj] at hr
    exact ⟨hb.1, hr⟩
  cases hc : ak.akIfetch with
  | true =>
    obtain ⟨hrdb, hharm⟩ := hfe hc
    rw [wreadPostIfetchId s ak pa ts hc]
    exact execLoad E i s false (paZ pa) ts (WeakInterpProj.wbytes n w) s.wmWs hE hm
      (hshape false hrdb) hharm
  | false =>
    have hpost : wreadPost s ak pa ts = wsetWs s (loadPostRun s.wmWs ak.akSync (paZ pa) ts) := by
      simp [wreadPost, hc]
    rw [hpost]
    refine execLoad E i s ak.akSync (paZ pa) ts (WeakInterpProj.wbytes n w) _ hE hm
      (hshape ak.akSync (fun j hj => ?_)) (wsEqrRefl _)
    have hb := (hbytes j hj).2
    rw [hc] at hb
    simp only [Bool.false_eq_true, ↓reduceIte] at hb
    exact hb.1

/-- STORE.  `wwritePost` appends `wwriteMsg` at the log's fresh top and applies
`storePostRun` at `|log| + 1` — literally `MStepStore`'s post-state. -/
theorem execWrite (E : Exec) (i : Nat) (s : Wmstate) (ak : AkInfo) (pa : PAddr) (n : Nat)
    (v : BitVec (8 * n)) :
    execWf E → wsMatch i s (stt E E.exTr.length) → n ≠ 0 →
    ∃ E', projExt i (wwritePost (some i) s ak pa n v) E E' := by
  intro hE hm hn
  obtain ⟨himg, hlog, hws⟩ := hm
  obtain ⟨E', hE', hext, hst⟩ := execExtend E i
    (.LStore ak.akSync (paZ pa) (WeakInterpProj.wbytes n v) (wmClassOf ak s.wmWs)) _ hE
    (mstep.MStepStore ak.akSync (paZ pa) (WeakInterpProj.wbytes n v) (wmClassOf ak s.wmWs)
      (wbytesNonnil n v hn))
  refine ⟨E', hE', hext, ?_, ?_⟩ <;> rw [hst]
  · refine ⟨himg, ?_, ?_⟩
    · show (stt E E.exTr.length).msLog ++ _ = s.wmLog ++ _
      rw [hlog]; rfl
    · show wsEqr (updWs _ i _ i) _
      rw [updWsEq, wbytesLength, hlog]
      exact wsEqrStorePostRun _ _ _ _ _ _ hws
  · intro j hne
    exact updWsNe _ _ _ _ hne

/-! ## 4. The side conditions on the monad

`nzWrites`: every non-device `memWrite` node of `m` has a nonzero width (over the
WHOLE monad, all continuations).  See header (5). -/

def nzWrites {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .regRead _, k => ∀ r, nzWrites (k r)
    | .regWrite _ _, k => ∀ r, nzWrites (k r)
    | .memRead _ _ _, k => ∀ r, nzWrites (k r)
    | .memWrite n _ req, k => (devAddr req.pa = true ∨ n ≠ 0) ∧ ∀ r, nzWrites (k r)
    | .barrier _, k => ∀ r, nzWrites (k r)
    | .instrAnnounce _ _, k => ∀ r, nzWrites (k r)
    | .branchAnnounce _ _, k => ∀ r, nzWrites (k r)
    | .cacheOp _, k => ∀ r, nzWrites (k r)
    | .tlbi _, k => ∀ r, nzWrites (k r)
    | .takeException _, k => ∀ r, nzWrites (k r)
    | .returnException _, k => ∀ r, nzWrites (k r)
    | .translationStart _, k => ∀ r, nzWrites (k r)
    | .translationEnd _, k => ∀ r, nzWrites (k r)
    | .cycleCount, k => ∀ r, nzWrites (k r)
    | .message _, k => ∀ r, nzWrites (k r)
    | .getCycleCount, k => ∀ r, nzWrites (k r)
    | .choose _, k => ∀ r, nzWrites (k r)
    | .readRam .., k => ∀ r, nzWrites (k r)
    | .writeRam .., k => ∀ r, nzWrites (k r)

/-- THE RUN-LEVEL FETCH PREMISE (Lean-only, deviation 3): every i-cache read on a
`wrun` of `m` from `s` to `(x, s')` satisfies `wFetchLoadOk` at the state it
reads in.  Arm for arm `wrun`; at a RAM read and at `choose` it quantifies over
the choices that continue to `(x, s')`. -/
def wrunFetchOk (tid : Option Nat) {X : Type} : SailM X → Wmstate → X → Wmstate → Prop
  | .pure _, _, _, _ => True
  | .impure (.error _) _, _, _, _ => True
  | .impure (.ok o) k, s, x, s' =>
    match o, k with
    | .regRead r, k => wrunFetchOk tid (k (s.wmRegs r)) s x s'
    | .regWrite r v, k => wrunFetchOk tid (k PUnit.unit) (wsetReg s r v) x s'
    | .memRead n _ req, k =>
      if devAddr req.pa then
        match devRead s.wmDev req.pa n with
        | some (w, d') => wrunFetchOk tid (k (.Ok (w, none))) (wsetDev s d') x s'
        | none => True
      else
        ∀ (w : BitVec (8 * n)) (ts : List Nat),
          wreadOk s (classify req.access_kind) req.pa n ts w →
          wrun tid (k (.Ok (w, none))) (wreadPost s (classify req.access_kind) req.pa ts) x s' →
          ((classify req.access_kind).akIfetch = true → wFetchLoadOk s req.pa n ts) ∧
          wrunFetchOk tid (k (.Ok (w, none))) (wreadPost s (classify req.access_kind) req.pa ts) x s'
    | .memWrite n _ req, k =>
      if devAddr req.pa then
        match req.value with
        | some v =>
          match devWrite s.wmDev req.pa n v with
          | some d' => wrunFetchOk tid (k (.Ok (some true))) (wsetDev s d') x s'
          | none => True
        | none => True
      else
        match req.value with
        | some v =>
          wrunFetchOk tid (k (.Ok (some true))) (wwritePost tid s (classify req.access_kind) req.pa n v) x s'
        | none => True
    | .barrier b, k => wrunFetchOk tid (k ()) (wbarrierPost s b) x s'
    | .instrAnnounce _ _, k => wrunFetchOk tid (k ()) s x s'
    | .branchAnnounce _ _, k => wrunFetchOk tid (k ()) s x s'
    | .cacheOp _, k => wrunFetchOk tid (k ()) s x s'
    | .tlbi _, k => wrunFetchOk tid (k ()) s x s'
    | .takeException _, k => wrunFetchOk tid (k ()) s x s'
    | .returnException _, k => wrunFetchOk tid (k ()) s x s'
    | .translationStart _, k => wrunFetchOk tid (k ()) s x s'
    | .translationEnd _, k => wrunFetchOk tid (k ()) s x s'
    | .cycleCount, k => wrunFetchOk tid (k ()) s x s'
    | .message _, k => wrunFetchOk tid (k ()) s x s'
    | .getCycleCount, k => wrunFetchOk tid (k (0 : Nat)) s x s'
    | .choose _, k => ∀ c, wrun tid (k c) s x s' → wrunFetchOk tid (k c) s x s'
    | .readRam .., _ => True
    | .writeRam .., _ => True

/-- (Lean-only) The monad-level discharge: no RAM read of `m` is an i-cache read. -/
def noIfetch {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .regRead _, k => ∀ r, noIfetch (k r)
    | .regWrite _ _, k => ∀ r, noIfetch (k r)
    | .memRead _ _ req, k =>
        (devAddr req.pa = true ∨ (classify req.access_kind).akIfetch = false) ∧ ∀ r, noIfetch (k r)
    | .memWrite _ _ _, k => ∀ r, noIfetch (k r)
    | .barrier _, k => ∀ r, noIfetch (k r)
    | .instrAnnounce _ _, k => ∀ r, noIfetch (k r)
    | .branchAnnounce _ _, k => ∀ r, noIfetch (k r)
    | .cacheOp _, k => ∀ r, noIfetch (k r)
    | .tlbi _, k => ∀ r, noIfetch (k r)
    | .takeException _, k => ∀ r, noIfetch (k r)
    | .returnException _, k => ∀ r, noIfetch (k r)
    | .translationStart _, k => ∀ r, noIfetch (k r)
    | .translationEnd _, k => ∀ r, noIfetch (k r)
    | .cycleCount, k => ∀ r, noIfetch (k r)
    | .message _, k => ∀ r, noIfetch (k r)
    | .getCycleCount, k => ∀ r, noIfetch (k r)
    | .choose _, k => ∀ r, noIfetch (k r)
    | .readRam .., k => ∀ r, noIfetch (k r)
    | .writeRam .., k => ∀ r, noIfetch (k r)

theorem wrunFetchOkNoIfetch (tid : Option Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate), noIfetch m → wrunFetchOk tid m s x s' := by
  induction m with
  | pure y => intro _ _ _ _; trivial
  | impure call k ih =>
    intro s x s' hni
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [noIfetch] at hni
        simp only [wrunFetchOk]
        split
        · split
          · exact ih _ _ _ _ (hni.2 _)
          · trivial
        · rename_i hd
          intro w ts _ _
          refine ⟨fun hc => ?_, ih _ _ _ _ (hni.2 _)⟩
          rcases hni.1 with h | h
          · exact absurd h hd
          · rw [h] at hc; cases hc
      case memWrite n va req =>
        simp only [noIfetch] at hni
        simp only [wrunFetchOk]
        split
        · split
          · split
            · exact ih _ _ _ _ (hni _)
            · trivial
          · trivial
        · split
          · exact ih _ _ _ _ (hni _)
          · trivial
      case choose p =>
        simp only [noIfetch] at hni
        simp only [wrunFetchOk]
        intro c _
        exact ih _ _ _ _ (hni c)
      case readRam => trivial
      case writeRam => trivial
      all_goals (simp only [noIfetch] at hni; simp only [wrunFetchOk]; exact ih _ _ _ _ (hni _))

/-! ## 5. THE CORE LEMMA

One `wrun` of agent `i` extends any `execWf` execution whose final state matches
`i`'s pre-state, to one whose final state matches `i`'s post-state — leaving
every other agent's `Wstate` where it was.  The induction mirrors `wrun`. -/

theorem wrunExec (i : Nat) {X : Type} (m : SailM X) :
    ∀ (s : Wmstate) (x : X) (s' : Wmstate) (E : Exec),
      nzWrites m →
      wrunFetchOk (some i) m s x s' →
      wrun (some i) m s x s' →
      execWf E → wsMatch i s (stt E E.exTr.length) →
      ∃ E', projExt i s' E E' := by
  induction m with
  | pure y =>
    intro s x s' E _ _ h hE hm
    rw [h.2]
    exact ⟨E, projExtRefl i s E hE hm⟩
  | impure call k ih =>
    intro s x s' E hnz hfo h hE hm
    cases call with
    | error e => exact h.elim
    | ok o =>
      cases o
      case memRead n va req =>
        simp only [nzWrites] at hnz
        simp only [wrunFetchOk] at hfo
        simp only [wrun] at h
        split at h
        · rename_i hd
          rw [if_pos hd] at hfo
          split at h
          · rename_i w d' hdr
            simp only [hdr] at hfo
            exact ih _ _ _ _ _ (hnz _) hfo h hE hm
          · exact h.elim
        · rename_i hd
          rw [if_neg hd] at hfo
          obtain ⟨w, ts, hok, h⟩ := h
          obtain ⟨hf1, hf2⟩ := hfo w ts hok h
          obtain ⟨E1, hp1⟩ := execRead E i s _ _ _ ts w hE hm hok hf1
          obtain ⟨E2, hp2⟩ := ih _ _ _ _ E1 (hnz _) hf2 h hp1.1 hp1.2.2.1
          exact ⟨E2, projExtTrans _ _ _ _ _ _ hp1 hp2⟩
      case memWrite n va req =>
        simp only [nzWrites] at hnz
        obtain ⟨hn, hnz⟩ := hnz
        simp only [wrunFetchOk] at hfo
        simp only [wrun] at h
        split at h
        · rename_i hd
          rw [if_pos hd] at hfo
          split at h
          · rename_i v hv
            simp only [hv] at hfo
            split at h
            · rename_i d' hdw
              simp only [hdw] at hfo
              exact ih _ _ _ _ _ (hnz _) hfo h hE hm
            · exact h.elim
          · exact h.elim
        · rename_i hd
          rw [if_neg hd] at hfo
          have hn0 : n ≠ 0 := by
            rcases hn with h' | h'
            · exact absurd h' hd
            · exact h'
          split at h
          · rename_i v hv
            simp only [hv] at hfo
            obtain ⟨E1, hp1⟩ := execWrite E i s (classify req.access_kind) req.pa n v hE hm hn0
            obtain ⟨E2, hp2⟩ := ih _ _ _ _ E1 (hnz _) hfo h hp1.1 hp1.2.2.1
            exact ⟨E2, projExtTrans _ _ _ _ _ _ hp1 hp2⟩
          · exact h.elim
      case barrier b =>
        simp only [nzWrites] at hnz
        simp only [wrunFetchOk] at hfo
        simp only [wrun] at h
        obtain ⟨E1, hp1⟩ := execBarrier E i s b hE hm
        obtain ⟨E2, hp2⟩ := ih _ _ _ _ E1 (hnz _) hfo h hp1.1 hp1.2.2.1
        exact ⟨E2, projExtTrans _ _ _ _ _ _ hp1 hp2⟩
      case choose p =>
        simp only [nzWrites] at hnz
        simp only [wrunFetchOk] at hfo
        simp only [wrun] at h
        obtain ⟨c, h⟩ := h
        exact ih _ _ _ _ _ (hnz c) (hfo c h) h hE hm
      case readRam => exact h.elim
      case writeRam => exact h.elim
      all_goals
        (simp only [nzWrites] at hnz
         simp only [wrunFetchOk] at hfo
         simp only [wrun] at h
         exact ih _ _ _ _ _ (hnz _) hfo h hE hm)

/-! ## 6. Whole runs

A chain of instruction executions by ONE agent (multi-agent interleaving is
W5's composition job). -/

def WeakInterpProj.wstep (i : Nat) (s s' : Wmstate) : Prop :=
  ∃ (X : Type) (m : SailM X) (x : X),
    nzWrites m ∧ wrunFetchOk (some i) m s x s' ∧ wrun (some i) m s x s'

theorem wrunChainExec (i : Nat) (s0 s : Wmstate) :
    rtc (WeakInterpProj.wstep i) s0 s →
    ∀ E, execWf E → wsMatch i s0 (stt E E.exTr.length) →
    ∃ E', projExt i s E E' := by
  intro hrun
  induction hrun with
  | refl => intro E hE hm; exact ⟨E, projExtRefl i _ E hE hm⟩
  | tail _ hst ih =>
    intro E hE hm
    obtain ⟨E1, hp1⟩ := ih E hE hm
    obtain ⟨X, m, x, hnz, hfo, hr⟩ := hst
    obtain ⟨E2, hp2⟩ := wrunExec i m _ x _ E1 hnz hfo hr hp1.1 hp1.2.2.1
    exact ⟨E2, projExtTrans _ _ _ _ _ _ hp1 hp2⟩

/-- THE PROJECTION THEOREM.  From a fresh `Wmstate` (empty log, `wsInit`), any
chain of `wrun` instruction executions by agent `i` (every fetch satisfying
`wFetchLoadOk`, deviation 3) induces a well-formed `WeakAxiomatic` execution
with the same era-initial image, the same final log, and `i`'s final `Wstate`
up to `wsEqr`; every other agent is still at `wsInit`. -/
theorem wrunExecWf (i : Nat) (s0 s : Wmstate) :
    s0.wmLog = [] → s0.wmWs = wsInit →
    rtc (WeakInterpProj.wstep i) s0 s →
    ∃ E, execWf E ∧
      exImg E = wimg s0 ∧
      exLog E = s.wmLog ∧
      wsEqr (ews E E.exTr.length i) s.wmWs ∧
      (∀ j, j ≠ i → ews E E.exTr.length j = wsInit) := by
  intro hlog0 hws0 hrun
  let σ0 : Mstate := ⟨wimg s0, [], fun _ => wsInit⟩
  have hE0 : execWf ⟨[σ0], []⟩ := execNil σ0 rfl (fun _ => rfl)
  have hm0 : wsMatch i s0 (stt ⟨[σ0], []⟩ (List.length ([] : List Estep))) := by
    refine ⟨rfl, ?_, ?_⟩
    · show ([] : List Wmsg) = s0.wmLog
      rw [hlog0]
    · show wsEqr wsInit s0.wmWs
      rw [hws0]; exact wsEqrRefl _
  obtain ⟨E, hE, hext, ⟨_, hlog, hws⟩, hfr⟩ := wrunChainExec i s0 s hrun ⟨[σ0], []⟩ hE0 hm0
  refine ⟨E, hE, ?_, hlog, hws, fun j hne => hfr j hne⟩
  rw [execExtendsImg _ _ hE0 hext]
  rfl

end Weak
