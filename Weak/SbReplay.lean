/-
Weak: **allocproc route P, increment P-W2 (3/3) — `SbReplay`, VALUES BY CONSTRUCTION: the read arms,
the two exempt `ip->ref` reads, and the lockstep datum** (`notes/weak-allocproc-routeP-design.md` §3.2;
plan rev 55 row P-W2; rulings [OWN.112] (the two-site exemption) [OWN.113]).  Lean-only, no Rocq twin.

  §1  **THE TWO EXEMPT SITES** ([OWN.112]): `SbReplay.ipRefPc` (`ilock+0xe`, `iunlock+0x1c`: the
      unlocked `lw a5,8(..)` of `ip->ref`, `fs.c:300,325`), the exempt GF events `ipRefX D` (the
      emission's block realizes at one of the two pcs, `SilSite.blockPc`), and the two-site taint
      RE-HOSTED from the landed static census: `ipRefTaint` (`SilSite.siteOk` with `ruIlock` /
      `ruIunlock`: the loaded `a5` reaches only the `blez` at `+0x10` / `+0x1e`, where it dies),
      `ipRefNeedsRule` (the rule is load-bearing), `ipRefRule` (`SilSite.ruleOfIrefPos`: two words in
      `[1, 2^31)` take the same `blez` arm);
  §2  the walk's machine facts: the view bound `sbInvStAt` (every `SbCand` view ≤ the landed log) and
      **`relpStAt` / `relpAgree`** (an agent's release-pending bit is its row's fold — so the member
      hart and the emission agree on it, the input of every re-timed realization);
  §3  **THE MEMBER-LATEST BYTE**: `latestOfLast` (the last landed write of a byte is the log's latest
      message there, with that write's byte) and `latestOfNil` (no landed write: the image), and
      **`srcVal`** — a GF read whose GF source is the member-latest (or, with nothing landed, the image)
      sees GF's value in the member's log (from `pfx`: the member's write labels ARE GF's);
      §3.1 forwarding: `fwdRel` (the forwarded byte and the forwarding TAG come from the same,
      youngest, entry), **`fwdArm`** (GF's source is the agent's own youngest pending store covering
      the byte ⇒ the member forwards GF's value), and **`memberFwdSrc`** — THE FORWARDED-BYTE
      TIMESTAMP settled: the member label names the forwarding store's member write index, whose
      write IS that store (the member's rf at a forwarded byte is the own store);
  §4  **THE READ ARMS** (the gate's `rd` / `wr` / `rdX`, design §3.2): `loadArm` — a load all of whose
      bytes are forwarded with GF's values or have a member-latest GF source IS an `SbCand` step with
      GF's values (re-timed); `rmwArm` — an AMO whose sources are member-latest reads GF's bytes at the
      landed log, with `rmwLatest` (the AMO's side conditions — `amoOk`, `.rl`, `.aq` — are the gate's);
      `rdXArm` — an exempt read ALWAYS has an `SbCand` step reading the top (`topVals`), a plain load of
      GF's footprint (`lblReidxSub`); **`valEqX`** (values exact off the exempt reads; at them both words
      satisfy the exempt-value fact `exValV` — told apart by WIDTH: `ip->ref`'s `lw` both in `[1, 2^31)`,
      `holding+0x12`'s `ld` ([OWN.124], the THIRD exempt pc, `Weak/SbHoldX.lean`) neither the row's own
      `&cpus[x]` (`cpuB`)) and `valEqXOfAgree` (from `SbAgree.agreeX` and the exempt-value facts);
      the exempt-value facts are the INTERFACE **`ExValGF`** / **`ExValTop`**; their `ip->ref` halves
      `IrefGF` / `IrefTop` (finding F-P-W2-1: reference counting over the whole kernel heap — NOT a
      GF-level fact; see PROGRESS), their `lk->cpu` halves in `Weak/SbHoldX.lean` / `SbHoldZero.lean`;
  §5  **THE LOCKSTEP DATUM** at `CertZ13.relT`'s lockstep arm: `lockBlk` — in lockstep (the member's
      program state IS the emission's), the emission's block with its read RE-TIMED to the member's
      timestamps is the member's program step (`SbWalk.evData`), given text custody of the star's
      fetches at the landed log (`fetchOk`, the twin's `SilSiteStep.fetchQ`).  At the two exempt pcs
      the member is TAINTED (`CertZ13.relT`'s `csync` arm) until the `blez`: the Sail meaning of
      `ipRefTaint` stays the named datum `SilSiteStep.sailQ` restricted to the two pcs (unchanged
      status: never proved in route T either).
  §6  **`memberOfWalk`** — the FINISHED walk (complete rows, drained buffers, `pfx`, `exOk`): the
      member is well-formed, its writes are the landed log, its AMOs read the latest bytes, it agrees
      with GF (`agreeX`), hence `agreeW4` with `nf = True` and `agreeW3` at every lock set, and
      `valEqX` given `ExValGF` (the agent bound from the program data, `agOkWalk`).

Spec: FAITHFUL (proof organisation; the exemption is [OWN.112] (a), FAITHFUL; the exempt-value
interface is NOT a memory-model statement — RVWMO/riscv.cat say nothing about values — it is the
program's reference-counting fact, F-P-W2-1).  Lean-only helpers `SbReplay.*`.
-/
import Weak.SbAgree
import Weak.SilSiteStep

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open Lbl

namespace SbReplay

open SbWalk SbAgree

/-! # 1. The two exempt sites -/

/-- **THE TWO VALUE-INSENSITIVE RACY READS** (`fs.c:300,325`, `ip->ref < 1`; census 6m §3.3). -/
def ipRefPc (pc : Int) : Prop :=
  pc = SilSite.sym KernelSyms.«ilock» 0xe ∨ pc = SilSite.sym KernelSyms.«iunlock» 0x1c

/-- The exempt GF events: the emission's block of the event realizes at one of the two pcs. -/
def ipRefX (D : Nat → CertZ7.EmData) (e : Geid) : Prop :=
  ∃ pc, SilSite.blockPc ((D e.1).g e.2) = some pc ∧ ipRefPc pc

/-- **THE TWO-SITE TAINT, RE-HOSTED** (`SilSiteTaint`'s static walk, landed): from each pc, with the
loaded word fully poisoned, the taint dies at the `blez` (`ruIlock` / `ruIunlock`). -/
theorem ipRefTaint (pc : Int) : ipRefPc pc →
    ∃ ru, SilSite.siteOk pc SilSite.FULL ru = true ∧
      (ru = SilSite.ruIlock ∨ ru = SilSite.ruIunlock) := by
  rintro (rfl | rfl)
  · exact ⟨_, SilSite.ilockOk, .inl rfl⟩
  · exact ⟨_, SilSite.iunlockOk, .inr rfl⟩

/-- The rule is load-bearing: without the `blez` kill the walk from either pc fails. -/
theorem ipRefNeedsRule :
    SilSite.siteOk (SilSite.sym KernelSyms.«ilock» 0xe) SilSite.FULL SilSite.noRules = false ∧
    SilSite.siteOk (SilSite.sym KernelSyms.«iunlock» 0x1c) SilSite.FULL SilSite.noRules = false := by
  constructor <;> decide +kernel

/-- **THE VALUE RULE** of the two pcs (`SilSite.ruleOfIrefPos`): two words in `[1, 2^31)` take the
same `blez` arm. -/
theorem ipRefRule (pc : Int) (me : Nat) (vs vs' : List (BitVec 8)) :
    ipRefPc pc → SilSite.pos32 vs → SilSite.pos32 vs' → SilSite.vRule pc me vs vs' :=
  SilSite.ruleOfIrefPos pc me vs vs'

/-! # 2. The walk's machine facts -/

/-- The `SbCand` view bound along a valid walk. -/
theorem sbInvStAt (pol : SbPol) (c : CandW) : validW pol c → ∀ k, SbCand.Inv (stAt c k).σ := by
  intro hv k
  induction k with
  | zero => exact SbCand.invInit _ ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      show SbCand.Inv (match c.its[k]? with
        | some it => nextI (stAt c k) it
        | none => stAt c k).σ
      rw [hk]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      have hok := hv k it hk
      cases it with
      | ev s => exact SbCand.invStepE _ _ _ _ ih hok
      | land i j =>
        cases hp : ((stAt c k).pend i)[j]? with
        | none => simp only [nextI, hp]; exact ih
        | some p => simp only [nextI, hp]; exact SbCand.invNextL _ i j ih

/-- An event moves the acting agent's release-pending bit by `lpostRelp`, the others' not at all. -/
theorem relpNextE (σ : SbCand.CandS) (i : Nat) (l : Lbl) (j : Nat) :
    SbCand.stepE σ i l (SbCand.nextE σ i l) →
    ((SbCand.nextE σ i l).ms.msWs j).wRelp =
      if j = i then lpostRelp (σ.ms.msWs i).wRelp l else (σ.ms.msWs j).wRelp := by
  intro hst
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl]
    cases hst with
    | load aq base ts vs _ _ =>
      show (updWs _ j _ j).wRelp = _
      rw [updWsEq, WeakRvwmoConf.loadPostRunRelp]; rfl
    | issue rl base vs k hne _ =>
      show (updWs _ j _ j).wRelp = _
      rw [updWsEq]
      cases vs with
      | nil => exact absurd rfl hne
      | cons => rfl
    | fence pr pw sr sw _ =>
      show (updWs _ j _ j).wRelp = _
      rw [updWsEq]
      exact lblPostRelp 0 _ (.LFence pr pw sr sw)
    | rmw aq rl base ts rvs wvs k hne _ _ _ _ _ _ =>
      show (updWs _ j _ j).wRelp = _
      rw [updWsEq]
      exact lblPostRelp _ _ (.LRmw aq rl base ts rvs wvs k)
    | io => rfl
  · rw [if_neg hj]
    cases hst with
    | io => rfl
    | _ => exact congrArg Wstate.wRelp (updWsNe _ _ _ _ hj)

/-- **AN AGENT'S RELEASE-PENDING BIT IS ITS ROW'S FOLD** (landings keep it). -/
theorem relpStAt (pol : SbPol) (c : CandW) (x : Nat) : validW pol c → ∀ k,
    (((stAt c k).σ.ms.msWs x).wRelp = ((stAt c k).rows x).foldl lpostRelp false) := by
  intro hv k
  induction k with
  | zero => rfl
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      have e : stAt c (k + 1) = stAt c k := by
        show (match c.its[k]? with
          | some it => nextI (stAt c k) it
          | none => stAt c k) = _
        rw [hk]
      rw [e]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      have hok := hv k it hk
      cases it with
      | ev s =>
        show ((SbCand.nextE (stAt c k).σ s.esAg s.esLb).ms.msWs x).wRelp =
          (upd (stAt c k).rows s.esAg ((stAt c k).rows s.esAg ++ [s.esLb]) x).foldl lpostRelp false
        rw [relpNextE _ _ _ _ hok]
        by_cases hx : x = s.esAg
        · subst hx; rw [if_pos rfl, updEq, List.foldl_append, ← ih]; rfl
        · rw [if_neg hx, updNe _ _ _ _ hx]; exact ih
      | land i j =>
        cases hp : ((stAt c k).pend i)[j]? with
        | none => simp only [nextI, hp]; exact ih
        | some p =>
          simp only [nextI, hp]
          have hsb : ((stAt c k).σ.sb i)[j]? = some p.2 := by
            rw [(invStAt pol c hv k).sb i, List.getElem?_map, hp]; rfl
          simp only [SbCand.nextL, hsb]
          by_cases hx : x = i
          · subst hx; rw [updWsEq]; exact ih
          · rw [updWsNe _ _ _ _ hx]; exact ih

/-- Related labels move the release-pending bit alike. -/
theorem relXRelp (x : Prop) (b : Bool) (l l' : Lbl) : lblRelX x l l' → lpostRelp b l' = lpostRelp b l := by
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · exact lblReidxRelp b l l' h
  · cases l <;> cases l' <;> simp_all [lblReidxSub, lpostRelp]

theorem foldRelpRel (X : Geid → Prop) (x : Nat) : ∀ (n : Nat) (row row' : List Lbl) (b : Bool),
    row'.length ≤ row.length →
    (∀ m l', row'[m]? = some l' → ∃ l, row[m]? = some l ∧ lblRelX (X (x, n + m)) l l') →
    row'.foldl lpostRelp b = (row.take row'.length).foldl lpostRelp b
  | _, _, [], _, _, _ => rfl
  | n, [], _ :: _, _, hle, _ => by simp at hle
  | n, l :: row, l' :: row', b, hle, h => by
    obtain ⟨l0, hl0, hrel⟩ := h 0 l' rfl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl0
    subst hl0
    simp only [List.foldl_cons, List.length_cons, List.take_succ_cons]
    rw [relXRelp _ b l l' hrel]
    refine foldRelpRel X x (n + 1) row row' _ (by simp at hle; omega) (fun m l2 hm => ?_)
    obtain ⟨l3, hl3, hr3⟩ := h (m + 1) l2 (by simpa using hm)
    exact ⟨l3, by simpa using hl3, by rw [show n + 1 + m = n + (m + 1) by omega]; exact hr3⟩

/-- **THE MEMBER HART AND THE ROW PREFIX AGREE ON THE RELEASE-PENDING BIT** (`relpAgreeS`'s twin). -/
theorem relpAgree (pol : SbPol) (c : CandW) (G : Gexec) (X : Geid → Prop) (x : Nat) :
    validW pol c → pfx G X (cur c) →
    ((cur c).σ.ms.msWs x).wRelp =
      (rowWsAux 0 wsInit ((G.gxProg.getD x []).take ((cur c).rows x).length)).wRelp := by
  rintro hv ⟨hR, -⟩
  rw [show cur c = stAt c c.its.length from rfl] at hR ⊢
  rw [relpStAt pol c x hv, rowWsAuxRelp]
  have hlen : ((cur c).rows x).length ≤ (G.gxProg.getD x []).length := by
    by_cases h0 : ((cur c).rows x).length = 0
    · omega
    · obtain ⟨l', hl'⟩ : ∃ l', ((cur c).rows x)[((cur c).rows x).length - 1]? = some l' :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨l, hl, -⟩ := hR x _ l' hl'
      unfold gxLbl at hl
      cases hr : G.gxProg[x]? with
      | none => rw [hr] at hl; cases hl
      | some row =>
        rw [hr] at hl
        simp only [Option.bind_some] at hl
        have := lookup_lt_Some hl
        rw [List.getD_eq_getElem?_getD, hr]; simp only [Option.getD_some]; omega
  have := foldRelpRel X x 0 (G.gxProg.getD x []) ((cur c).rows x) false hlen (fun m l' hm => by
    obtain ⟨l, hl, hrel⟩ := hR x m l' hm
    refine ⟨l, ?_, by rw [Nat.zero_add]; exact hrel⟩
    unfold gxLbl at hl
    cases hr : G.gxProg[x]? with
    | none => rw [hr] at hl; cases hl
    | some row => rw [hr] at hl; rw [List.getD_eq_getElem?_getD, hr]; simpa using hl)
  exact this

/-! # 3. The member-latest byte -/

/-- The last element satisfying `r` splits the list. -/
theorem lastSplit {α : Type} (r : α → Bool) : ∀ (g : List α) (e : α), (g.filter r).getLast? = some e →
    ∃ A B, g = A ++ e :: B ∧ r e = true ∧ B.filter r = []
  | [], _, h => by simp at h
  | z :: g, e, h => by
    by_cases hg : g.filter r = []
    · by_cases hz : r z = true
      · rw [List.filter_cons, if_pos hz, hg] at h
        simp only [List.getLast?_singleton, Option.some.injEq] at h
        subst h
        exact ⟨[], g, rfl, hz, hg⟩
      · rw [List.filter_cons, if_neg hz, hg] at h; simp at h
    · have h' : (g.filter r).getLast? = some e := by
        rw [List.filter_cons] at h
        split at h
        · rw [List.getLast?_cons] at h
          cases hl : (g.filter r).getLast? with
          | none => rw [List.getLast?_eq_none_iff] at hl; exact absurd hl hg
          | some y => rw [hl] at h; simpa using h
        · exact h
      obtain ⟨A, B, h1, h2, h3⟩ := lastSplit r g e h'
      exact ⟨z :: A, B, by rw [h1]; rfl, h2, h3⟩

/-- A message of the log writes `a` only if its event writes `a`. -/
theorem msgWr (rows : Nat → List Lbl) (a : Int) (e : Geid) (m : Wmsg) :
    wmsgOf rows e = some m → ((msgByte m a).isSome ↔ rwrB rows a e = true) := by
  intro h
  unfold wmsgOf at h
  unfold rwrB
  cases hl : (rows e.1)[e.2]? with
  | none => rw [hl] at h; cases h
  | some l =>
    rw [hl] at h
    dsimp only at h ⊢
    rw [wrsBIff]
    cases hw : lbWr l with
    | none => rw [hw] at h; cases h
    | some q =>
      obtain ⟨base, vs⟩ := q
      rw [hw] at h
      simp only [Option.some.injEq] at h
      subst h
      constructor
      · intro hs
        obtain ⟨j, hj, rfl⟩ := msgByteIndex base vs _ _ _ hs
        exact ⟨base, vs, j, vs[j], rfl, List.getElem?_eq_getElem hj, rfl⟩
      · rintro ⟨base', vs', j, v, he, hv, rfl⟩
        cases he
        exact msgByteAt base vs _ _ j (lookup_lt_Some hv)

theorem msgByteVal (base : Int) (vs : List (BitVec 8)) (tid : Option Nat) (k : WmClass) (j : Nat) :
    msgByte ⟨base, vs, tid, k⟩ (accAddr base j) = vs[j]? := by
  have h : base + (j : Int) - base = j := by omega
  simp only [msgByte, accAddr]
  rw [if_pos (by omega), h, Int.toNat_natCast]

/-- **THE LAST LANDED WRITE OF `a` IS THE LOG'S LATEST MESSAGE THERE, with its byte.** -/
theorem latestOfLast (img : Image) (w : WS) (a : Int) (e : Geid) :
    Inv img w → (wrAtW w a).getLast? = some e →
    ∃ t m, latest img w.σ.ms.msLog a t ∧ wmsgOf w.rows e = some m ∧
      logByte img w.σ.ms.msLog t a = msgByte m a := by
  intro hI hlast
  obtain ⟨A, B, hg, hre, hB⟩ := lastSplit _ w.gmo e hlast
  have hsome : ∃ m, wmsgOf w.rows e = some m := by
    unfold rwrB at hre
    unfold wmsgOf
    cases hl : (w.rows e.1)[e.2]? with
    | none => rw [hl] at hre; cases hre
    | some l =>
      rw [hl] at hre
      dsimp only at hre ⊢
      unfold wrsB at hre
      cases hw : lbWr l with
      | none => rw [hw] at hre; cases hre
      | some q => exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := hsome
  have hlog : w.σ.ms.msLog = A.filterMap (wmsgOf w.rows) ++ m :: B.filterMap (wmsgOf w.rows) := by
    rw [hI.log, hg, List.filterMap_append, List.filterMap_cons, hm]
  have hms : (msgByte m a).isSome := (msgWr w.rows a e m hm).2 hre
  refine ⟨(A.filterMap (wmsgOf w.rows)).length + 1, m, ⟨?_, ?_⟩, hm, ?_⟩
  · rw [logByteS, hlog]; simpa using hms
  · rintro ⟨t, hlo, hhi, m', hm', hs'⟩
    rw [hlog] at hm' hhi
    have hq : m' ∈ B.filterMap (wmsgOf w.rows) := by
      rw [List.getElem?_append_right (by omega)] at hm'
      obtain ⟨d, hd⟩ : ∃ d, t - 1 - (A.filterMap (wmsgOf w.rows)).length = d + 1 :=
        ⟨t - 2 - (A.filterMap (wmsgOf w.rows)).length, by omega⟩
      rw [hd, List.getElem?_cons_succ] at hm'
      exact List.mem_of_getElem? hm'
    obtain ⟨e', he', hme'⟩ := List.mem_filterMap.1 hq
    have hr' := (msgWr w.rows a e' m' hme').1 hs'
    have : e' ∈ B.filter (rwrB w.rows a) := List.mem_filter.2 ⟨he', hr'⟩
    rw [hB] at this; simp at this
  · rw [logByteS, hlog]; simp

/-- **NO LANDED WRITE OF `a`: THE LOG NEVER WRITES IT** (the image is latest). -/
theorem latestOfNil (img : Image) (w : WS) (a : Int) :
    Inv img w → wrAtW w a = [] → ¬ writesIn w.σ.ms.msLog a 0 w.σ.ms.msLog.length := by
  intro hI hnil ⟨t, _, _, m, hm, hs⟩
  rw [hI.log] at hm
  obtain ⟨e, he, hme⟩ := List.mem_filterMap.1 (List.mem_of_getElem? hm)
  have hr := (msgWr w.rows a e m hme).1 hs
  have : e ∈ wrAtW w a := List.mem_filter.2 ⟨he, hr⟩
  rw [hnil] at this; simp at this

/-- **THE GATE'S SOURCE CONDITION** for one byte `a` read from GF timestamp `t`: GF's source write is
the member-latest at `a`, or (`t = 0`) nothing has landed at `a`. -/
def srcLatest (G : Gexec) (w : WS) (a : Int) (t : Nat) : Prop :=
  (t = 0 ∧ wrAtW w a = []) ∨ (∃ src, gwriteAt G t = some src ∧ (wrAtW w a).getLast? = some src)

/-- **THE MEMBER SEES GF'S VALUE AT A MEMBER-LATEST SOURCE.** -/
theorem srcVal (img : Image) (G : Gexec) (X : Geid → Prop) (w : WS) (e : Geid) (a : Int) (t : Nat)
    (v : BitVec 8) :
    Inv img w → pfx G X w → gloadValue G → G.gxImg = img →
    greadsByte G e a t v → srcLatest G w a t →
    ∃ t', latest img w.σ.ms.msLog a t' ∧ logByte img w.σ.ms.msLog t' a = some v := by
  intro hI hpf hlv himg hrd hsrc
  have hlv' := (hlv e a t v hrd).1
  rcases hsrc with ⟨rfl, hnil⟩ | ⟨src, hsrc, hlast⟩
  · refine ⟨0, ⟨?_, latestOfNil img w a hI hnil⟩, ?_⟩
    · show (img a).isSome
      rw [← himg]; simp only at hlv'; rw [hlv']; rfl
    · show img a = some v
      rw [← himg]; exact hlv'
  · obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + 1 := by
      cases t with
      | zero => simp [gwriteAt] at hsrc
      | succ t0 => exact ⟨t0, rfl⟩
    obtain ⟨src', hsrc', hwr, -⟩ := hlv'
    rw [hsrc, Option.some.injEq] at hsrc'
    subst hsrc'
    obtain ⟨t', m, hlat, hm, hlb⟩ := latestOfLast img w a src hI hlast
    refine ⟨t', hlat, ?_⟩
    rw [hlb]
    -- the member's label of `src` writes GF's bytes
    obtain ⟨l, base, vs, j, hl, hwrl, hv, ha⟩ := hwr
    unfold wmsgOf at hm
    cases hr : (w.rows src.1)[src.2]? with
    | none => rw [hr] at hm; cases hm
    | some l' =>
      rw [hr] at hm
      obtain ⟨l0, hl0, hrel⟩ := hpf.1 src.1 src.2 l' hr
      rw [show ((src.1, src.2) : Geid) = src from rfl, hl, Option.some.injEq] at hl0
      subst hl0
      dsimp only at hm
      rw [relXWr _ _ _ hrel, hwrl] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rw [← ha, msgByteVal]; exact hv


/-! ## 3.1 Forwarding: the youngest tagged entry -/

/-- The forwarded byte and the forwarding tag come from the SAME (youngest) entry. -/
theorem fwdRelGen (a : Int) (L : List (Nat × SbEnt)) : ∀ (ps : List (Nat × SbEnt)) (o1 : Option Nat)
    (o2 : Option (BitVec 8)), (∀ p, p ∈ ps → p ∈ L) →
    ((o1 = none ∧ o2 = none) ∨
      ∃ p, p ∈ L ∧ o1 = some p.1 ∧ o2 = msgByte p.2.msg a ∧ (msgByte p.2.msg a).isSome) →
    let r1 := ps.foldl (fun o p => if (msgByte p.2.msg a).isSome then some p.1 else o) o1
    let r2 := (ps.map Prod.snd).foldl (fun o e => (msgByte e.msg a).or o) o2
    (r1 = none ∧ r2 = none) ∨
      ∃ p, p ∈ L ∧ r1 = some p.1 ∧ r2 = msgByte p.2.msg a ∧ (msgByte p.2.msg a).isSome
  | [], _, _, _, h => h
  | q :: ps, o1, o2, hsub, h => by
    simp only [List.foldl_cons, List.map_cons]
    apply fwdRelGen a L ps _ _ (fun p hp => hsub p (List.mem_cons_of_mem _ hp))
    by_cases hq : (msgByte q.2.msg a).isSome
    · right
      refine ⟨q, hsub q List.mem_cons_self, by rw [if_pos hq], ?_, hq⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hq
      rw [hv]; rfl
    · have hn : msgByte q.2.msg a = none := by simpa using hq
      rw [if_neg hq, hn, Option.none_or]
      exact h

theorem fwdRel (ps : List (Nat × SbEnt)) (a : Int) :
    (fwdId ps a = none ∧ SbCand.fwdByte (ps.map Prod.snd) a = none) ∨
      ∃ p, p ∈ ps ∧ fwdId ps a = some p.1 ∧ SbCand.fwdByte (ps.map Prod.snd) a = msgByte p.2.msg a ∧
        (msgByte p.2.msg a).isSome :=
  fwdRelGen a ps ps none none (fun _ h => h) (.inl ⟨rfl, rfl⟩)

/-- No forwarding tag: no forwarded byte. -/
theorem fwdNone (img : Image) (w : WS) (x : Nat) (a : Int) :
    Inv img w → fwdId (w.pend x) a = none → SbCand.fwdByte (w.σ.sb x) a = none := by
  intro hI h
  rw [hI.sb x]
  rcases fwdRel (w.pend x) a with ⟨-, h2⟩ | ⟨p, -, h1, -, -⟩
  · exact h2
  · rw [h] at h1; cases h1

/-- **THE OWN-PENDING SOURCE** (the gate's forwarding alternative): if GF's source of a byte is the
agent's own store whose tag is the youngest pending one covering the byte, the member FORWARDS GF's
value there. -/
theorem fwdArm (img : Image) (G : Gexec) (X : Geid → Prop) (w : WS) (e : Geid) (x r : Nat) (a : Int)
    (t : Nat) (v : BitVec 8) :
    Inv img w → pfx G X w → gloadValue G → greadsByte G e a t v → gwriteAt G t = some (x, r) →
    fwdId (w.pend x) a = some r → SbCand.fwdByte (w.σ.sb x) a = some v := by
  intro hI hpf hlv hrd hsrc hid
  rw [hI.sb x]
  rcases fwdRel (w.pend x) a with ⟨h1, -⟩ | ⟨p, hp, h1, h2, h3⟩
  · rw [hid] at h1; cases h1
  · rw [hid, Option.some.injEq] at h1
    subst h1
    rw [h2]
    obtain ⟨rl, base, vs, kc, hrow, hmsg⟩ := hI.pendSt x p hp
    -- GF's source writes `v` at `a`, and its label is the member's store (verbatim)
    have hlv' := (hlv e a t v hrd).1
    obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + 1 := by
      cases t with
      | zero => simp [gwriteAt] at hsrc
      | succ t0 => exact ⟨t0, rfl⟩
    obtain ⟨src, hs, hwr, -⟩ := hlv'
    rw [hsrc, Option.some.injEq] at hs
    subst hs
    obtain ⟨l, base', vs', j, hl, hwrl, hv, ha⟩ := hwr
    obtain ⟨l0, hl0, hrel⟩ := hpf.1 x p.1 _ hrow
    rw [hl, Option.some.injEq] at hl0
    subst hl0
    rw [← relXWr _ _ _ hrel] at hwrl
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwrl
    obtain ⟨rfl, rfl⟩ := hwrl
    rw [hmsg, ← ha, msgByteVal]
    exact hv

/-- Every forwarding record names a STORE of the same agent. -/
def fwSt (w : WS) : Prop :=
  ∀ (x n : Nat) (f : List (Option Nat)) (j r : Nat), (w.fw x)[n]? = some f → f[j]? = some (some r) →
    ∃ rl base vs kc, (w.rows x)[r]? = some (LStore rl base vs kc)

theorem fwStInit (img : Image) : fwSt (init img) := fun _ _ _ _ _ h => by simp [init] at h

theorem fwStEv (img : Image) (w : WS) (s : Estep) : Inv img w → fwSt w → fwSt (nextI w (.ev s)) := by
  intro hI h x n f j r hf hr
  change (upd w.fw s.esAg (w.fw s.esAg ++ [fwOf (w.pend s.esAg) s.esLb]) x)[n]? = some f at hf
  have hold : ∀ rl base vs kc, (w.rows x)[r]? = some (LStore rl base vs kc) →
      ∃ rl base vs kc, ((nextI w (.ev s)).rows x)[r]? = some (LStore rl base vs kc) :=
    fun rl base vs kc h' => ⟨rl, base, vs, kc, rowsEvOld w s x r _ h'⟩
  by_cases hx : x = s.esAg
  · subst hx
    rw [updEq] at hf
    rcases getAppInv _ _ _ _ hf with hf | ⟨-, rfl⟩
    · obtain ⟨rl, base, vs, kc, h'⟩ := h _ n f j r hf hr
      exact hold rl base vs kc h'
    · cases hlb : s.esLb with
      | LLoad aq base ts vs =>
        rw [hlb] at hr
        simp only [fwOf, List.getElem?_map] at hr
        cases hj : (List.range ts.length)[j]? with
        | none => rw [hj] at hr; cases hr
        | some j' =>
          rw [hj] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          rcases fwdRel (w.pend s.esAg) (accAddr base j') with ⟨h1, -⟩ | ⟨p, hp, h1, -, -⟩
          · rw [h1] at hr; cases hr
          · rw [h1, Option.some.injEq] at hr
            subst hr
            obtain ⟨rl, base', vs', kc, hrow, -⟩ := hI.pendSt _ p hp
            exact hold rl base' vs' kc hrow
      | _ => rw [hlb] at hr; simp [fwOf] at hr
  · rw [updNe _ _ _ _ hx] at hf
    obtain ⟨rl, base, vs, kc, h'⟩ := h x n f j r hf hr
    exact hold rl base vs kc h'

theorem fwStLand (w : WS) (i k : Nat) : fwSt w → fwSt (nextI w (.land i k)) := by
  intro h
  cases hp : (w.pend i)[k]? with
  | none => simp only [nextI, hp]; exact h
  | some p => simp only [nextI, hp]; exact h

theorem fwStAt (pol : SbPol) (c : CandW) : validW pol c → ∀ k, fwSt (stAt c k) := by
  intro hv k
  induction k with
  | zero => exact fwStInit c.img
  | succ k ih =>
    cases hk : c.its[k]? with
    | none =>
      have e : stAt c (k + 1) = stAt c k := by
        show (match c.its[k]? with
          | some it => nextI (stAt c k) it
          | none => stAt c k) = _
        rw [hk]
      rw [e]; exact ih
    | some it =>
      rw [stAtSucc c k it hk]
      cases it with
      | ev s => exact fwStEv c.img _ s (invStAt pol c hv k) ih
      | land i j => exact fwStLand _ i j ih

/-- **THE FORWARDED-BYTE TIMESTAMP** (the P-W1 open item, settled): at a drained state, a member load's
forwarded byte names its forwarding store's member write index — the member's rf at that byte is the
own store. -/
theorem memberFwdSrc (N : Nat) (img : Image) (w : WS) (x n : Nat) (l : Lbl) (j r : Nat) :
    Inv img w → fwSt w → agOk N w → drained w → (w.rows x)[n]? = some l →
    ((w.fw x).getD n [])[j]? = some (some r) →
    ∀ aq base ts vs, l = LLoad aq base ts vs → j < ts.length →
    ∃ ts', gxLbl (memberW N img w) (x, n) = some (LLoad aq base ts' vs) ∧
      ts'[j]? = some (gwix (memberW N img w) (x, r)) ∧
      gwriteAt (memberW N img w) (gwix (memberW N img w) (x, r)) = some (x, r) := by
  intro hI hfw hag hdr hl hf aq base ts vs hle hj
  subst hle
  have hx : x < N := agOfRow N w (x, n) _ hag hl
  have hf' : ∃ f, (w.fw x)[n]? = some f ∧ f[j]? = some (some r) := by
    have hnl : n < (w.fw x).length := by rw [hI.fwLen x]; exact lookup_lt_Some hl
    refine ⟨(w.fw x)[n], List.getElem?_eq_getElem hnl, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnl] at hf
    exact hf
  obtain ⟨f, hfn, hfj⟩ := hf'
  obtain ⟨rl, base', vs', kc, hst⟩ := hfw x n f j r hfn hfj
  -- the store has landed: it is in gmo, a member write
  have hin : (x, r) ∈ w.gmo := by
    rcases hI.memIn x r _ hst (by rfl) with h | h
    · exact h
    · rw [hdr x] at h; simp at h
  have hW : (x, r) ∈ gwrites (memberW N img w) := by
    refine List.mem_filter.2 ⟨hin, ?_⟩
    simp only [gisW, memLblSome N img w (x, r) _ hx hst, fixLbl, lbIsW]
  refine ⟨fixTs (rawG N img w) x ts ((w.fw x).getD n []), memLblSome N img w (x, n) _ hx hl, ?_,
    gwriteAtGwix _ _ hW⟩
  rw [gwixEq]
  simp only [fixTs, List.getElem?_mapIdx, List.getElem?_eq_getElem hj, Option.map_some]
  rw [List.getD_eq_getElem?_getD, hf]
  rfl

/-! # 4. The read arms -/

/-- The top bytes of a load at the walk state: per byte, forwarded from the own buffer, or the
latest byte of the landed log. -/
def topVals (w : WS) (x : Nat) (base : Int) (vs : List (BitVec 8)) : Prop :=
  ∀ j v, vs[j]? = some v →
    SbCand.fwdByte (w.σ.sb x) (accAddr base j) = some v ∨
    (SbCand.fwdByte (w.σ.sb x) (accAddr base j) = none ∧
      ∃ t, latest w.σ.ms.msImg w.σ.ms.msLog (accAddr base j) t ∧
        logByte w.σ.ms.msImg w.σ.ms.msLog t (accAddr base j) = some v)

/-- Timestamps for top bytes: the latest one where not forwarded. -/
theorem topTs (σ : SbCand.CandS) (x : Nat) (aq : Bool) (base : Int) :
    SbCand.Inv σ → ∀ (vs : List (BitVec 8)),
    (∀ j v, vs[j]? = some v →
      SbCand.fwdByte (σ.sb x) (accAddr base j) = some v ∨
      (SbCand.fwdByte (σ.sb x) (accAddr base j) = none ∧
        ∃ t, latest σ.ms.msImg σ.ms.msLog (accAddr base j) t ∧
          logByte σ.ms.msImg σ.ms.msLog t (accAddr base j) = some v)) →
    ∃ ts, ts.length = vs.length ∧
      SbCand.rdOkSb σ.ms.msImg σ.ms.msLog (σ.ms.msWs x) aq base ts vs (σ.sb x) ∧
      ∀ j t, ts[j]? = some t → SbCand.fwdByte (σ.sb x) (accAddr base j) = none →
        latest σ.ms.msImg σ.ms.msLog (accAddr base j) t := by
  intro hI vs hv
  classical
  let tf : Nat → Nat := fun j =>
    if h : ∃ t, latest σ.ms.msImg σ.ms.msLog (accAddr base j) t then Classical.choose h else 0
  have hts : ∀ j t, ((List.range vs.length).map tf)[j]? = some t → j < vs.length ∧ t = tf j := by
    intro j t hj
    have hjl : j < vs.length := by
      have := lookup_lt_Some hj; simpa using this
    simp only [List.getElem?_map, List.getElem?_range hjl, Option.map_some, Option.some.injEq] at hj
    exact ⟨hjl, hj.symm⟩
  have hlatOf : ∀ j v, vs[j]? = some v → SbCand.fwdByte (σ.sb x) (accAddr base j) = none →
      latest σ.ms.msImg σ.ms.msLog (accAddr base j) (tf j) ∧
      logByte σ.ms.msImg σ.ms.msLog (tf j) (accAddr base j) = some v := by
    intro j v hvj hn
    rcases hv j v hvj with h | ⟨-, t0, hlat, hlb⟩
    · rw [hn] at h; cases h
    · have hex : ∃ t, latest σ.ms.msImg σ.ms.msLog (accAddr base j) t := ⟨t0, hlat⟩
      have hct : tf j = Classical.choose hex := dif_pos hex
      have heq : Classical.choose hex = t0 :=
        latestUnique _ _ _ _ _ (Classical.choose_spec hex) hlat
      rw [hct, heq]; exact ⟨hlat, hlb⟩
  refine ⟨(List.range vs.length).map tf, by simp, ⟨by simp, fun j t v hj hvj => ?_⟩, fun j t hj hn => ?_⟩
  · obtain ⟨-, rfl⟩ := hts j t hj
    cases hf : SbCand.fwdByte (σ.sb x) (accAddr base j) with
    | some v' =>
      rcases hv j v hvj with h | ⟨h, -⟩
      · rw [hf] at h; exact .inl h
      · rw [hf] at h; cases h
    | none =>
      obtain ⟨hlat, hlb⟩ := hlatOf j v hvj hf
      refine .inr ⟨rfl, hlb, latestReadable _ _ _ _ _ _ ?_ hlat⟩
      exact Nat.max_le.2 ⟨loadVpreBounded _ aq _ (hI x), (hI x).2.2.2.2.2.2.1 (accAddr base j)⟩
  · obtain ⟨hjl, rfl⟩ := hts j t hj
    exact (hlatOf j vs[j] (List.getElem?_eq_getElem hjl) hn).1

/-- **THE `rd` ARM**: a GF load of agent `x` (its next event `(x, n)`) every byte of which is forwarded
with GF's value or has a member-latest GF source is an `SbCand` step with GF's VALUES (timestamps
re-chosen). -/
theorem loadArm (pol : SbPol) (c : CandW) (G : Gexec) (X : Geid → Prop) (x n : Nat) (aq : Bool)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    validW pol c → pfx G X (cur c) → gloadValue G → G.gxImg = c.img →
    gxLbl G (x, n) = some (LLoad aq base ts vs) → vs.length = ts.length →
    (∀ j t v, ts[j]? = some t → vs[j]? = some v →
      SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) = some v ∨
      (SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) = none ∧
        srcLatest G (cur c) (accAddr base j) t)) →
    (aq = true → SbCand.noRl ((cur c).σ.sb x)) →
    ∃ ts', ts'.length = ts.length ∧
      SbCand.stepE (cur c).σ x (LLoad aq base ts' vs) (SbCand.nextE (cur c).σ x (LLoad aq base ts' vs)) := by
  intro hv hpf hlv himg hl hlen hb hrl
  have hI : Inv c.img (cur c) := invStAt pol c hv c.its.length
  have hS : SbCand.Inv (cur c).σ := sbInvStAt pol c hv c.its.length
  obtain ⟨ts', hl', hrd, -⟩ := topTs (cur c).σ x aq base hS vs (fun j v hvj => by
    have hjl : j < ts.length := by rw [← hlen]; exact lookup_lt_Some hvj
    obtain ⟨t, ht⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem hjl⟩
    rcases hb j t v ht hvj with h | ⟨hn, hsrc⟩
    · exact .inl h
    · refine .inr ⟨hn, ?_⟩
      rw [hI.img]
      exact srcVal c.img G X (cur c) (x, n) _ t v hI hpf hlv himg
        ⟨_, base, ts, vs, j, hl, rfl, ht, hvj, rfl⟩ hsrc)
  exact ⟨ts', by rw [hl', hlen], .load aq base ts' vs hrd hrl⟩

/-- **THE `wr` ARM'S READ**: a GF AMO all of whose byte sources are member-latest reads GF's bytes at
the landed log, the latest ones. -/
theorem rmwArm (pol : SbPol) (c : CandW) (G : Gexec) (X : Geid → Prop) (x n : Nat) (aq rl : Bool)
    (base : Int) (ts : List Nat) (rvs wvs : List (BitVec 8)) (kc : WmClass) :
    validW pol c → pfx G X (cur c) → gloadValue G → G.gxImg = c.img →
    gxLbl G (x, n) = some (LRmw aq rl base ts rvs wvs kc) → rvs.length = ts.length →
    (∀ j t, ts[j]? = some t → srcLatest G (cur c) (accAddr base j) t) →
    ∃ ts', ts'.length = ts.length ∧
      rdOk (cur c).σ.ms.msImg (cur c).σ.ms.msLog ((cur c).σ.ms.msWs x) aq base ts' rvs ∧
      rmwLatest (cur c).σ.ms.msImg (cur c).σ.ms.msLog base ts' := by
  intro hv hpf hlv himg hl hlen hb
  have hI : Inv c.img (cur c) := invStAt pol c hv c.its.length
  have hS : SbCand.Inv (cur c).σ := sbInvStAt pol c hv c.its.length
  have hval : ∀ j v, rvs[j]? = some v → ∃ t, latest (cur c).σ.ms.msImg (cur c).σ.ms.msLog
      (accAddr base j) t ∧ logByte (cur c).σ.ms.msImg (cur c).σ.ms.msLog t (accAddr base j) = some v := by
    intro j v hvj
    have hjl : j < ts.length := by rw [← hlen]; exact lookup_lt_Some hvj
    obtain ⟨t, ht⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem hjl⟩
    rw [hI.img]
    exact srcVal c.img G X (cur c) (x, n) _ t v hI hpf hlv himg
      ⟨_, base, ts, rvs, j, hl, rfl, ht, hvj, rfl⟩ (hb j t ht)
  -- at the EMPTY buffer the top read is a plain `rdOk` read
  let σ0 : SbCand.CandS := ⟨(cur c).σ.ms, fun _ => []⟩
  have hS0 : SbCand.Inv σ0 := hS
  obtain ⟨ts', hl', hrd, hlat⟩ := topTs σ0 x aq base hS0 rvs (fun j v hvj => .inr ⟨rfl, hval j v hvj⟩)
  exact ⟨ts', by rw [hl', hlen], (SbCand.rdOkSbNil _ _ _ _ _ _ _).1 hrd,
    fun j t ht => hlat j t ht rfl⟩

/-- A byte always has a top value: forwarded, the last landed write's, or (nothing landed) the image's. -/
theorem topExists (img : Image) (w : WS) (x : Nat) (a : Int) :
    Inv img w → (img a).isSome →
    ∃ v, SbCand.fwdByte (w.σ.sb x) a = some v ∨
      (SbCand.fwdByte (w.σ.sb x) a = none ∧
        ∃ t, latest w.σ.ms.msImg w.σ.ms.msLog a t ∧ logByte w.σ.ms.msImg w.σ.ms.msLog t a = some v) := by
  intro hI himg
  cases hf : SbCand.fwdByte (w.σ.sb x) a with
  | some v => exact ⟨v, .inl rfl⟩
  | none =>
    rw [hI.img]
    cases hl : (wrAtW w a).getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hl
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 himg
      exact ⟨v, .inr ⟨rfl, 0, ⟨by rw [logByte0, hv]; rfl, latestOfNil img w a hI hl⟩, by rw [logByte0, hv]⟩⟩
    | some e =>
      obtain ⟨t, m, hlat, hm, hlb⟩ := latestOfLast img w a e hI hl
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hlat.1
      exact ⟨v, .inr ⟨rfl, t, hlat, hv⟩⟩

/-- **THE `rdX` ARM** ([OWN.112]): an exempt read is NOT gated — whatever has landed, the member reads
the TOP (forwarded or latest bytes), a plain load of GF's footprint (`lblReidxSub`); its values are the
top values `topVals`. -/
theorem rdXArm (pol : SbPol) (c : CandW) (G : Gexec) (x n : Nat) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    validW pol c → gxLbl G (x, n) = some (LLoad false base ts vs) →
    (∀ j, j < ts.length → (c.img (accAddr base j)).isSome) →
    ∃ ts' vs', ts'.length = ts.length ∧ vs'.length = ts.length ∧ topVals (cur c) x base vs' ∧
      lblReidxSub (LLoad false base ts vs) (LLoad false base ts' vs') ∧
      SbCand.stepE (cur c).σ x (LLoad false base ts' vs')
        (SbCand.nextE (cur c).σ x (LLoad false base ts' vs')) := by
  intro hv _ himg
  classical
  have hI : Inv c.img (cur c) := invStAt pol c hv c.its.length
  have hS : SbCand.Inv (cur c).σ := sbInvStAt pol c hv c.its.length
  have hex : ∀ j, j < ts.length → ∃ v, SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) = some v ∨
      (SbCand.fwdByte ((cur c).σ.sb x) (accAddr base j) = none ∧
        ∃ t, latest (cur c).σ.ms.msImg (cur c).σ.ms.msLog (accAddr base j) t ∧
          logByte (cur c).σ.ms.msImg (cur c).σ.ms.msLog t (accAddr base j) = some v) :=
    fun j hj => topExists c.img (cur c) x _ hI (himg j hj)
  let g : Nat → BitVec 8 := fun j => if h : j < ts.length then Classical.choose (hex j h) else 0
  let vs' := (List.range ts.length).map g
  have htop : topVals (cur c) x base vs' := by
    intro j v hj
    have hjl : j < ts.length := by have := lookup_lt_Some hj; simpa [vs'] using this
    simp only [vs', List.getElem?_map, List.getElem?_range hjl, Option.map_some, Option.some.injEq] at hj
    subst hj
    have e : g j = Classical.choose (hex j hjl) := dif_pos hjl
    rw [e]
    exact Classical.choose_spec (hex j hjl)
  obtain ⟨ts', hl', hrd, -⟩ := topTs (cur c).σ x false base hS vs' htop
  have hlv : vs'.length = ts.length := by simp [vs']
  refine ⟨ts', vs', by rw [hl', hlv], hlv, htop, ⟨rfl, rfl, rfl, by rw [hl', hlv], by rw [hl']⟩,
    .load false base ts' vs' hrd (fun h => by cases h)⟩

/-! ## 4.1 Value agreement by construction -/

/-- An exempt read's word is in `[1, 2^31)` (`ip->ref ≥ 1`). -/
def irefOkL (l : Lbl) : Prop := ∃ base ts vs, l = LLoad false base ts vs ∧ SilSite.pos32 vs

/-- `&cpus[x]`'s eight little-endian bytes (`cpus + 128·x`; `sizeof (struct cpu)` = 128). -/
def cpuB (x : Nat) : List (BitVec 8) :=
  (List.range 8).map (fun j => BitVec.ofNat 8 ((KernelSyms.«cpus» + 128 * x) / 256 ^ j))

/-- **THE EXEMPT-VALUE FACT of a read word of row `x`** ([OWN.112], [OWN.124]): the exempt classes are
told apart by WIDTH — the two `ip->ref` reads are `lw` (4 bytes: the word is in `[1, 2^31)`, `pos32`), the
`holding+0x12` read is `ld` (8 bytes: the word is NOT the row's own `&cpus[x]`). -/
def exValV (x : Nat) (vs : List (BitVec 8)) : Prop :=
  (vs.length = 4 → SilSite.pos32 vs) ∧ (vs.length = 8 → vs ≠ cpuB x)

/-- An exempt read label of row `x`: a plain load whose word satisfies `exValV x`. -/
def exValL (x : Nat) (l : Lbl) : Prop := ∃ base ts vs, l = LLoad false base ts vs ∧ exValV x vs

/-- **VALUE AGREEMENT** (design §3.2 `SbAgree.valEqX`): every read of `G` other than the exempt ones
returns, in `GR`, exactly `G`'s bytes; at the exempt ones both words satisfy the exempt-value fact
(`ip->ref`: both in `[1, 2^31)`; `holding+0x12` from `acquire`: neither is the row's `&cpus[x]`). -/
def valEqX (G GR : Gexec) (X : Geid → Prop) : Prop :=
  ∀ e l l', gxLbl G e = some l → gxLbl GR e = some l' → lbIsR l = true →
    (¬ X e → (lbRd l').map (fun r => r.2.2) = (lbRd l).map (fun r => r.2.2)) ∧
    (X e → exValL e.1 l ∧ exValL e.1 l')

/-- **THE EXEMPT-VALUE INTERFACE, GF SIDE** (both exempt classes): GF's exempt reads satisfy `exValV`. -/
def ExValGF (G : Gexec) (X : Geid → Prop) : Prop := ∀ e l, X e → gxLbl G e = some l → exValL e.1 l

/-- **THE `ip->ref` HALF, GF SIDE** (F-P-W2-1): GF's 4-byte exempt reads see `ip->ref ≥ 1`. -/
def IrefGF (G : Gexec) (X : Geid → Prop) : Prop :=
  ∀ e base ts vs, X e → gxLbl G e = some (LLoad false base ts vs) → vs.length = 4 → SilSite.pos32 vs

/-- **THE EXEMPT-VALUE INTERFACE, MEMBER SIDE** (both exempt classes): at a walk state, the top word an
exempt read of a row's next GF event would read satisfies `exValV`. -/
def ExValTop (G : Gexec) (X : Geid → Prop) (w : WS) : Prop :=
  ∀ (x : Nat) (base : Int) (ts : List Nat) (vs vs' : List (BitVec 8)), X (x, (w.rows x).length) →
    gxLbl G (x, (w.rows x).length) = some (LLoad false base ts vs) → vs'.length = ts.length →
    topVals w x base vs' → exValV x vs'

/-- **THE `ip->ref` HALF, MEMBER SIDE** (F-P-W2-1): at a walk state, the top word a 4-byte exempt read of
a row's next GF event would read is in `[1, 2^31)`.

Both `ip->ref` halves are the REFERENCE-COUNTING fact of the design's `irefGe1` ("every write of
`ip->ref` co-between the reader's own last `ref++` and its next own `ref--` is ≥ 1" — per HOLDER, not per
hart: PROGRESS F-12-1): GF's source lies in that interval (CoWR from the opening increment, CoRW to the
closing decrement), and so does the member's top (the opening increment is landed or forwarded; the
closing decrement is not yet issued, hence every landed write is co-before it by the co-prefix invariant
`pfx`).  That fact is a property of the WHOLE kernel's reference discipline, not of the graph: it is NOT
derivable from GF (see PROGRESS F-P-W2-1). -/
def IrefTop (G : Gexec) (X : Geid → Prop) (w : WS) : Prop :=
  ∀ (x : Nat) (base : Int) (ts : List Nat) (vs vs' : List (BitVec 8)), X (x, (w.rows x).length) →
    gxLbl G (x, (w.rows x).length) = some (LLoad false base ts vs) → vs'.length = ts.length →
    ts.length = 4 → topVals w x base vs' → SilSite.pos32 vs'

/-- The member rows' exempt reads carry the exempt-value fact of their row. -/
def exOk (X : Geid → Prop) (w : WS) : Prop :=
  ∀ (x n : Nat) (l' : Lbl), (w.rows x)[n]? = some l' → X (x, n) → exValL x l'

theorem exOkInit (X : Geid → Prop) (img : Image) : exOk X (init img) :=
  fun _ _ _ h => by simp [init] at h

/-- `exOk` along an event: the appended label, if exempt, is an `exValL` load (the `rdX` arm with
`ExValTop`). -/
theorem exOkEv (X : Geid → Prop) (w : WS) (s : Estep) :
    exOk X w → (X (s.esAg, (w.rows s.esAg).length) → exValL s.esAg s.esLb) → exOk X (nextI w (.ev s)) := by
  intro h hnew x n l' hl' hx
  rcases rowsEvInv w s x n l' hl' with h' | ⟨rfl, rfl, rfl⟩
  · exact h x n l' h' hx
  · exact hnew hx

theorem exOkLand (X : Geid → Prop) (w : WS) (i k : Nat) : exOk X w → exOk X (nextI w (.land i k)) := by
  intro h
  cases hp : (w.pend i)[k]? with
  | none => simp only [nextI, hp]; exact h
  | some p => simp only [nextI, hp]; exact h

/-- **THE `rdX` STEP KEEPS `exOk`**: the arm's top word has the exempt-value fact by `ExValTop`. -/
theorem rdXIref (G : Gexec) (X : Geid → Prop) (w : WS) (x : Nat) (base : Int) (ts ts' : List Nat)
    (vs vs' : List (BitVec 8)) :
    ExValTop G X w → X (x, (w.rows x).length) →
    gxLbl G (x, (w.rows x).length) = some (LLoad false base ts vs) → vs'.length = ts.length →
    topVals w x base vs' → exValL x (LLoad false base ts' vs') :=
  fun h hx hl hlen htop => ⟨base, ts', vs', rfl, h x base ts vs vs' hx hl hlen htop⟩

/-- **VALUE AGREEMENT FROM THE AGREEMENT**: exact values off the exempt reads (`lblReidx`), and the
exempt-value facts at them. -/
theorem valEqXOfAgree (G GR : Gexec) (X : Geid → Prop) :
    agreeX G GR X → ExValGF G X → (∀ e l', X e → gxLbl GR e = some l' → exValL e.1 l') →
    valEqX G GR X := by
  rintro ⟨-, hl, -⟩ hG hR e l l' h1 h2 hRd
  refine ⟨fun hx => ?_, fun hx => ⟨hG e l hx h1, hR e l' hx h2⟩⟩
  rcases hl e with ⟨h, -⟩ | ⟨l0, l1, h3, h4, hrel⟩
  · rw [h] at h1; cases h1
  · rw [h1, Option.some.injEq] at h3; subst h3
    rw [h2, Option.some.injEq] at h4; subst h4
    rcases hrel with ⟨-, h⟩ | ⟨hx', -⟩
    · cases l with
      | LLoad aq base ts vs =>
        cases l' with
        | LLoad aq' base' ts' vs' => obtain ⟨-, -, rfl, -⟩ := h; rfl
        | _ => cases h
      | LRmw aq rl base ts rvs wvs kc =>
        cases l' with
        | LRmw aq' rl' base' ts' rvs' wvs' kc' => obtain ⟨-, -, -, rfl, -⟩ := h; rfl
        | _ => cases h
      | _ => simp [lbIsR] at hRd
    · exact absurd hx' hx

/-- The member's exempt labels carry `exOk`'s words (the fix-up keeps load values). -/
theorem memberExOk (N : Nat) (img : Image) (X : Geid → Prop) (w : WS) :
    exOk X w → ∀ e l', X e → gxLbl (memberW N img w) e = some l' → exValL e.1 l' := by
  intro h e l' hx hl'
  obtain ⟨-, l, hl, rfl⟩ := memLblInv N img w e l' hl'
  obtain ⟨base, ts, vs, rfl, hp⟩ := h e.1 e.2 l hl hx
  exact ⟨base, _, vs, rfl, hp⟩

/-! # 5. The lockstep datum -/

/-- **TEXT CUSTODY AT THE LANDED LOG** (the twin's `SilSiteStep.fetchQ`): every fetch of the star reads
bytes the member can fetch at view 0 (equal values, its own timestamps). -/
def fetchOk (w : WS) (ls : List Wlabel) : Prop :=
  ∀ (base : Int) (tvs : List (Nat × BitVec 8)), Wlabel.LIFetch base tvs ∈ ls →
    ∃ tvs' : List (Nat × BitVec 8), tvs'.map Prod.snd = tvs.map Prod.snd ∧
      ifetchOk w.σ.ms.msImg w.σ.ms.msLog 0 base tvs'

/-- **THE LOCKSTEP BLOCK** (`CertZ13.relT`'s lockstep arm at P): the member's program state is the
emission's; the emission's block with its fetches re-timed (text custody) and its read RE-TIMED to the
member's timestamps `ts'` (values kept: value agreement) is the member's program step, given the
release-pending bit agreement (`relpAgree`). -/
theorem lockBlk (w : WS) (x : Nat) (D : Nat → CertZ7.EmData) (rows : List (List Lbl)) (n : Nat)
    (lb : Lbl) (d d' : Efab) (ts' : List Nat) :
    (w.σ.ms.msWs x).wRelp = (rowWsAux 0 wsInit ((rows.getD x []).take n)).wRelp →
    SilSiteStep.emBlk D rows x n lb d d' → fetchOk w ((D x).g n) →
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → ts'.length = ts.length) →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc → ts'.length = ts.length) →
    evData w x (SilSiteStep.setTs lb ts') ((D x).f n) d ((D x).f (n + 1)) d' := by
  intro hr hblk hfq hl hrm
  have hstar : ∀ (p pa : Pexv6) (da : Efab), admRunG pstepEv true p d ((D x).g n) pa da →
      ∃ lsC, admRunG pstepEv true p d lsC pa da ∧
        ∀ base tvs, Wlabel.LIFetch base tvs ∈ lsC → ifetchOk w.σ.ms.msImg w.σ.ms.msLog 0 base tvs := by
    intro p pa da hrun
    obtain ⟨lsC, h1, h2, -⟩ := SilSiteStep.starRetS (fun base tvs => ifetchOk w.σ.ms.msImg
      w.σ.ms.msLog 0 base tvs) true p d _ pa da hrun (fun base tvs hm => hfq base tvs hm)
    exact ⟨lsC, h1, h2⟩
  rcases hblk with ⟨hfu, pa, da, hrun, hre, hst⟩ |
      ⟨pa, da, pm, dm, ls2, pm2, dm2, l2, hrun, hpair, hst1, hrun2, hst2⟩
  · obtain ⟨l', hre', hst'⟩ := SilSiteStep.oneRetS pa da _ _ lb _ _ d' ts' hr hfu hre hst hl
    obtain ⟨lsC, h1, h2⟩ := hstar _ pa da hrun
    exact ⟨pa, da, lsC, h1, h2, .inl ⟨l', hre', hst'⟩⟩
  · obtain ⟨l1', hpair', hst1'⟩ := SilSiteStep.pairRetS pa pm2 _ _ lb _ l2 ts' hr hpair hrm
    obtain ⟨lsC, h1, h2⟩ := hstar _ pa da hrun
    exact ⟨pa, da, lsC, h1, h2, .inr ⟨pm, dm, ls2, pm2, dm2, l1', l2, hpair', hst1' da pm dm hst1,
      hrun2, hst2⟩⟩

/-- The re-timed label is `lblReidx` of the row's (the member's label of a lockstep step). -/
theorem setTsReidx (lb : Lbl) (ts' : List Nat) :
    (∀ aq base ts vs, lb = .LLoad aq base ts vs → ts'.length = ts.length) →
    (∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc → ts'.length = ts.length) →
    lblReidx lb (SilSiteStep.setTs lb ts') := by
  intro hl hrm
  cases lb with
  | LLoad aq base ts vs => exact ⟨rfl, rfl, rfl, hl aq base ts vs rfl⟩
  | LRmw aq rl base ts rvs wvs kc => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hrm aq rl base ts rvs wvs kc rfl⟩
  | _ => exact lblReidxRefl _

/-- **THE LOCKSTEP RELATION AT P**: `CertZ13.relT` with the taint bound EMPTY off the exempt reads —
lockstep (`pE = pC`) is its left arm. -/
theorem relTLock (TT : Nat → Nat → List Nat) (x n : Nat) (p : Pexv6) : CertZ13.relT TT x n p p :=
  .inl rfl

/-! # 6. The finished walk: the member, its facts, the agreement -/

/-- A nonempty row has an event of its agent. -/
theorem rowsEv (c : CandW) (i : Nat) : ∀ k, (stAt c k).rows i ≠ [] →
    ∃ k' s, k' < k ∧ c.its[k']? = some (Item.ev s) ∧ s.esAg = i := by
  intro k
  induction k with
  | zero => intro h; exact absurd rfl h
  | succ k ih =>
    intro h
    cases hk : c.its[k]? with
    | none =>
      have e : stAt c (k + 1) = stAt c k := by
        show (match c.its[k]? with
          | some it => nextI (stAt c k) it
          | none => stAt c k) = _
        rw [hk]
      rw [e] at h
      obtain ⟨k', s, h1, h2, h3⟩ := ih h
      exact ⟨k', s, by omega, h2, h3⟩
    | some it =>
      rw [stAtSucc c k it hk] at h
      cases it with
      | ev s =>
        by_cases hi : s.esAg = i
        · exact ⟨k, s, by omega, hk, hi⟩
        · have h' : (stAt c k).rows i ≠ [] := by
            change upd (stAt c k).rows s.esAg _ i ≠ [] at h
            rwa [updNe _ _ _ _ (Ne.symm hi)] at h
          obtain ⟨k', s', h1, h2, h3⟩ := ih h'
          exact ⟨k', s', by omega, h2, h3⟩
      | land j m =>
        have h' : (stAt c k).rows i ≠ [] := by
          cases hp : ((stAt c k).pend j)[m]? with
          | none => simp only [nextI, hp] at h; exact h
          | some p => simp only [nextI, hp] at h; exact h
        obtain ⟨k', s', h1, h2, h3⟩ := ih h'
        exact ⟨k', s', by omega, h2, h3⟩

/-- The walk's agents are below `N` (the program data's agent count). -/
theorem agOkWalk (pol : SbPol) (d0 : Efab) (S : St) (N : Nat) :
    ok pol d0 S → (S.pst 0).length = N → agOk N (cur S.c) := by
  rintro ⟨-, hp, -⟩ h0 i hi
  obtain ⟨k', s, -, hk, rfl⟩ := rowsEv S.c i _ hi
  exact agBound S.pst S.dv S.c N hp h0 k' s hk

/-- **THE FINISHED WALK** (complete rows, drained buffers): the member is a well-formed graph whose
writes are the landed log, whose AMOs read the latest bytes, which AGREES with GF up to the exempt
reads — hence CertZ24's `agreeW4` with `nf = True`, CertZ18's `agreeW3` at every lock set — and whose
values agree by construction (`valEqX`), given the exempt-value interface. -/
theorem memberOfWalk (pol : SbPol) (d0 : Efab) (S : St) (N : Nat) (G : Gexec) (X : Geid → Prop) :
    ok pol d0 S → (S.pst 0).length = N → pfx G X (cur S.c) → exOk X (cur S.c) →
    drained (cur S.c) → gwf G → G.gxImg = S.c.img → G.gxProg.length = N →
    (∀ x, x < N → ((cur S.c).rows x).length = (G.gxProg.getD x []).length) →
    gwf (memberP N S.c) ∧ logOf (memberP N S.c) (logP S.c) ∧
    CertZ18.rmwLatest (memberP N S.c) (logP S.c) ∧ agreeX G (memberP N S.c) X ∧
    CertZ24.agreeW4 G (memberP N S.c) (fun _ => False) ∧
    (∀ L, CertZ18.agreeW3 G (memberP N S.c) L) ∧
    (ExValGF G X → valEqX G (memberP N S.c) X) := by
  intro hok h0 hpf hex hdr hwf himg hN hlen
  have hv := hok.1
  have hI : Inv S.c.img (cur S.c) := invStAt pol S.c hv _
  have hR : RmwInv S.c.img (cur S.c) := rmwInvStAt pol S.c hv _
  have hag := agOkWalk pol d0 S N hok h0
  have hagr := agreeXOfPfx N S.c.img G X (cur S.c) hI hag hdr hwf himg hN hlen hpf
  exact ⟨memberGwf N _ _ hI hag hdr, memberLogOf N _ _ hI hag, memberRmwLatest N _ _ hI hR hag hdr,
    hagr, agreeW4OfX _ _ X hagr, fun L => agreeW3OfX _ _ X L hagr,
    fun hG => valEqXOfAgree _ _ X hagr hG (memberExOk N _ X _ hex)⟩

end SbReplay

end Weak
