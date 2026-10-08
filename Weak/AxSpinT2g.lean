/-
Weak: **THEOREM 2, STAGE 2, row `AxSpinT2g` — the PURE graph side of the D4 readback** (stage-2
design `notes/weak-lb-thm2-stage2.md` §B, §C row `AxSpinT2g`).  NEW Lean file (no Rocq source).
Every lemma here is a Lean-level fact about a `Gexec` (no iProp): the designated cut arms of
`AxSpinT2h` (`cutAq`, `cutRelS`, `cutRelL`, `cutPpN`, `cutPpI`) close their `HRQ` by one of them.

## VERDICT ON THE TWO DESIGN RISKS (checked first, 2026-10-08)

**(1) BYTE MIXING — MATERIALISES.**  `protXv6`'s lk->cpu class does NOT admit only 8-byte stores.
Its σ conjunct `CPUOK (clb L) cvx` is PER BYTE (`cpuOk` = `wval … (replicate 8 0) ∨ wval … (cvx
w.1)`, `wval` index-wise on the bytes the write touches, AxSpinProt5:131-136), `WOK` is per byte,
and the owned-write flow `fxRVLWrite` (AxSpinX2:710) is generic in the written sub-list
`Cw ⊆ XO` with `RVL` a `[∗list]` over bytes (AxSpinX:238, splittable).  So a lock holder C may
legally `sb` ONE byte of its own `cvx C` (only `fxCpuWrite`, the xv6 `sd`, is full-width).  The
racy deposit `ORacy` (AxSpinHdB:240) is ONLY `rdFact` (per byte: image / external source with
`cpuOk` / same-hart visible).  Then `rdFact + Himgc + layout + position ⇒ value ≠ cvx i` is FALSE
as a pure graph statement: cpus = 0x80012530, stride 128, so for A = 0, B = 1, C = 2 the graph
"B: `sd cvx 1`; C: `sb 0x30` at lk->cpu+0 (= byte 0 of `cvx 2`), gmo after; A reads" gives A the
bytes `30 25 01 80 00 00 00 00` = `cvx 0`, and every byte satisfies `rdFact` (gloadValue's
latest clause is per byte; it yields one source only under ALIGNED writes, `clSingleSource`).
(The real protocol forbids this interleaving through lock exclusivity, but that fact lives in
`lkInv`, not in the deposit.)  Hence `racyNotMine` is proved here under an EXPLICIT premise
`AxSpinT2g.clSrcAligned` — "every write the read takes a lk->cpu byte from touches all 8 bytes"
— which BOTH repair options supply: (A) a graph/code premise `clAligned (clb L) GD.gdG`
(the Rocq precedent: `AxSpinU.wpdCpuRacyX`, `AxSpinX7.xv6Handoff`), by
`AxSpinT2g.srcAlignedOfAligned`; (B) a protocol strengthening (a full-width σ conjunct for
`clb`, deposited by `fxCpuRacy`).  The choice is an owner question: see
`PROGRESS-AxSpinT2g.md`.  NOTHING in this file weakens the statement silently: the premise is a
named hypothesis of `racyNotMine`.

**(2) PO5's NOFF FLOW — MATERIALISES (as the design anticipated).**  pop_off's `lw a5,120(a0)`
(PO5:395, `XL4`) and pop_off's intena load (PO6:180, `XL4`) and push_off's noff loads (PO1:395, PO3:284) all run
`AxSpinPOx.XxLd4` — "frame rule: no annotation" (POx:367; field flow `dokFld`, output `OutLdF`,
value-agnostic: the continuation gets only `graphValue (i, k) = some vs`).  No deposit exists.
The P lane needs a 4-byte private-reload leaf, the `FldSlot`/`OutLd`/`RLfact` pattern of
AxSpinE5:227-318 at width 4: `FldFld4` running `fxPrivReadn L GT nm HL Hcons (i, kr) (i, kw)
(clRange pa 4) vw` (AxSpinX2:927) at the reload position `kr` against the po-latest own store
`kw` (push_off's `sw noff` at `tk + 5`, data `stBytes 4 (addiw1 (ldRes false 4 vn))`, already
exposed by `wpdPushOff`'s continuation, PO4:188; pop_off's intena load against push_off's
`sw intena` at `k + 12`, data `stBytes 4 0`, PO4:186), and the GENESIS arm `fxPrivRead0`
(AxSpinX2:952, per byte) at push_off's noff loads (`k + 7`, `tk + 4`), each handing its
annotation (`⌜∀ j a t b, (clRange pa 4)[j]? = some a → greadsByte … → vw[j]? = some b⌝`,
resp. `⌜∀ t v, greadsByte … a t v → t = 0 ∧ img a = some v⌝` for the four bytes) to the
continuation.  `wpdPushOff` must then also hand its first/second noff-load annotations on (it
drops nothing of that kind today because it deposits nothing).  The pure consumers are here:
`AxSpinT2g.privReadEq`, `AxSpinT2g.imgReadEq`, `noffPop`, `noffArmZero`, `intenaZero`.

## What this file proves (all PURE; `G : Gexec`)

§1 bridge (graphValue / greadsByte): `graphValueLoad` (a load label's graph value is its
  values), `privReadEq` (a per-byte read fact "byte `j` read = `tgt[j]`" + the load label ⇒
  the read values ARE `tgt`, via `readFactWord` AxSpinX5:102), `imgReadEq` (the genesis form:
  per-byte "read the image" + the image word ⇒ the values are the image word's bytes),
  `ldRes8Wbytes`/`ldRes4Wbytes`/`ldRes4StBytes` (load results of byte lists).
§2 `ownIsMine` (rlL): `OOwn`'s byte fact (AxSpinHdB:335) + the `ld lk->cpu` label ⇒
  `ldRes false 8 vs = val`.  `heldNonzero` (rlS): `lkBodyReadHeld`'s `≠ b0` byte fact
  (AxSpinProt5 §3) + the `lw lk->locked` label ⇒ `ldRes false 4 vs ≠ 0`.
§3 `clbSameSrc` (the 8 bytes of a lk->cpu read have ONE source write index, under
  `clSrcAligned`); `cpuReadNotMineSrc` (AxSpinProt5's `cpuReadNotMine` re-proved with the
  alignment needed only of the read's SOURCES and the value table injective only at the
  writers); `racyNotMine` (aq): `rdFact` + `Himgc` + writers are harts < NCPU + no own
  lk->cpu write po-before + `clSrcAligned` ⇒ `ldRes false 8 vs ≠ cpuAddr (cpuOf i)`;
  `racyNotMineAl` (the option-(A) corollary from `clAligned`); position / writer helpers
  `noOwnBefore`, `writerInGmo`, `writerLt`.
§4 noff / intena: `subw1` (= PO5's `addiwm1` BY `rfl`; restated so PO5/PO6 may import this
  file), `noffPop` (ppN: pop_off's noff = image + 1, so `bge zero,a5` falls through iff
  `0 ≤ img < 2³¹ − 1`, and `noff − 1` = the image), `noffArmZero` (ppI: the `q.c = false` arm
  forces image noff = 0, so push_off took `q.b = true`), `intenaZero` (ppI: the intena reload
  of push_off's `stBytes 4 0` gives `beqz` taken).

## Deviations / pins / honesty

* `racyNotMine` carries the named premise `clSrcAligned` (risk 1 above).  Not a pin on A/B's
  rows: it is about the SOURCES of A's read, i.e. it constrains C.  Under option (A) it is a
  graph scope premise; under option (B) it is derived from `HwpC`.
* The image noff is a `BitVec 32` word `w` with `w.toNat < 2^31 - 1` (the design's
  `Himgnoff`, `0 ≤ noffImg < 2³¹ − 1`, in unsigned form; T2f fixes the final spelling).
* `subw1` duplicates `AxSpinPO5.addiwm1`'s body (import-cycle avoidance, design §C row PO5/6);
  `addiwm1 v = AxSpinT2g.subw1 v` holds by `rfl`.

Reused: `readFactWord`, `loadnReads`, `lblTsLen` (AxSpinX5), `clRangeLookup`/`clRangeLookup2`
(AxSpinX4), `gwriteAtInv`, `WeakRvwmoGraph.gwixPos`, `gmoLtIrrefl`, `gmoLtTrans`
(WeakRvwmoGraph), `cvxInj`, `cvxNz`, `cvxLength` (AxSpinX), `wordOfBytesWbytes`,
`wbytesWordOfBytes`, `wbytesLookup`, `wbytesLength`.  All names file-qualified `AxSpinT2g.*`.
-/
import Weak.AxSpinX5
import Weak.AxSpinPO1

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail
open LeanRV64D LeanRV64D.Functions

/-! # 1. The graphValue / greadsByte bridge -/

/-- A load label's graph value is its values. -/
theorem AxSpinT2g.graphValueLoad (GD : Gdexec) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl GD.gdG e = some (.LLoad aq base ts vs) → graphValue GD e = some vs := by
  intro Hl
  unfold graphValue
  rw [Hl]
  rfl

/-- A per-byte read fact pins a plain load's values. -/
theorem AxSpinT2g.privReadEq (G : Gexec) (Hwf : gwf G) (e : Geid) (base : Int) (ts : List Nat)
    (n : Nat) (vs tgt : List (BitVec 8)) :
    gxLbl G e = some (.LLoad false base ts vs) → vs.length = n → tgt.length = n →
    (∀ (j : Nat) a t b, (clRange base n)[j]? = some a → greadsByte G e a t b →
      tgt[j]? = some b) →
    vs = tgt := by
  intro Hl Hvl Htl Hf
  have Hl' : gxLbl G e =
      some (.LLoad false base ts (WeakInterpProj.wbytes n (wordOfBytes n vs))) := by
    rw [wbytesWordOfBytes n vs Hvl]
    exact Hl
  have H := readFactWord G Hwf e base ts n (wordOfBytes n vs) tgt Hl' Htl Hf
  rw [wbytesWordOfBytes n vs Hvl] at H
  exact H

/-- The GENESIS form: every byte of the load read the image, and the image holds `w`'s bytes. -/
theorem AxSpinT2g.imgReadEq (G : Gexec) (Hwf : gwf G) (e : Geid) (base : Int) (ts : List Nat)
    (n : Nat) (vs : List (BitVec 8)) (w : BitVec (8 * n)) :
    gxLbl G e = some (.LLoad false base ts vs) → vs.length = n →
    (∀ a, a ∈ clRange base n → ∀ t v, greadsByte G e a t v → t = 0 ∧ G.gxImg a = some v) →
    (∀ (j : Nat) a b, (clRange base n)[j]? = some a →
      (WeakInterpProj.wbytes n w)[j]? = some b → G.gxImg a = some b) →
    vs = WeakInterpProj.wbytes n w := by
  intro Hl Hvl Hrd Himg
  apply AxSpinT2g.privReadEq G Hwf e base ts n vs _ Hl Hvl (wbytesLength n w)
  intro j a t b Hj Hr
  have Ha : a ∈ clRange base n := List.mem_of_getElem? Hj
  have Hjn : j < n := (AxSpinX4.clRangeLookup base n j a Hj).2
  have Hw : (WeakInterpProj.wbytes n w)[j]? = some (nthByte w j) := wbytesLookup n w j Hjn
  have H1 := (Hrd a Ha t b Hr).2
  have H2 := Himg j a _ Hj Hw
  rw [H1, Option.some.injEq] at H2
  rw [Hw, H2]

theorem AxSpinT2g.ldRes8Wbytes (v : BitVec 64) :
    ldRes false 8 (WeakInterpProj.wbytes 8 v) = v := by
  unfold ldRes rrv
  rw [wordOfBytesWbytes]
  unfold extend_value sign_extend
  simp only [Bool.false_eq_true, ↓reduceIte]
  ext j hj
  simp [Sail.BitVec.signExtend]

theorem AxSpinT2g.ldRes8Eq (vs : List (BitVec 8)) (h : vs.length = 8) :
    ldRes false 8 vs = wordOfBytes 8 vs := by
  have H := AxSpinT2g.ldRes8Wbytes (wordOfBytes 8 vs)
  rw [wbytesWordOfBytes 8 vs h] at H
  exact H

theorem AxSpinT2g.ldRes4Wbytes (w : BitVec 32) :
    ldRes false 4 (WeakInterpProj.wbytes 4 w) = w.signExtend 64 := by
  unfold ldRes rrv
  rw [wordOfBytesWbytes]
  unfold extend_value sign_extend
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl

theorem AxSpinT2g.ldRes4StBytes (v : BitVec 64) :
    ldRes false 4 (stBytes 4 v) = (v.setWidth 32).signExtend 64 := by
  unfold ldRes stBytes rrv AxDataX.wrb
  rw [wordOfBytesWbytes]
  unfold AxDataX.stData extend_value sign_extend
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1

/-! # 2. The holder's reads: rlL (`ownIsMine`) and rlS (`heldNonzero`) -/

/-- rlL: `OOwn`'s byte fact at release's `ld lk->cpu` pins the loaded word to `val` (acquire's
`mycpuRet tp`). -/
theorem AxSpinT2g.ownIsMine (L : Xlay) (G : Gexec) (Hwf : gwf G) (e : Geid) (ts : List Nat)
    (vs : List (BitVec 8)) (val : BitVec 64) :
    gxLbl G e = some (.LLoad false (L.xlLk + 16) ts vs) → vs.length = 8 →
    (∀ (j : Nat) a t b, (clb L)[j]? = some a → greadsByte G e a t b →
      (WeakInterpProj.wbytes 8 val)[j]? = some b) →
    vs = WeakInterpProj.wbytes 8 val ∧ ldRes false 8 vs = val := by
  intro Hl Hvl Hf
  have H : vs = WeakInterpProj.wbytes 8 val :=
    AxSpinT2g.privReadEq G Hwf e (L.xlLk + 16) ts 8 vs _ Hl Hvl (wbytesLength 8 val) Hf
  refine ⟨H, ?_⟩
  rw [H]
  exact AxSpinT2g.ldRes8Wbytes val

theorem AxSpinT2g.sext32Zero (x : BitVec 32) :
    x.signExtend 64 = 0#64 → x.extractLsb' 0 8 = 0#8 := by
  intro h
  bv_decide

/-- rlS: the holder's `lw lk->locked` reads a nonzero low byte, so the loaded word is nonzero
(holding's short arm `ldRes … = 0` is refuted). -/
theorem AxSpinT2g.heldNonzero (G : Gexec) (Hwf : gwf G) (e : Geid) (lk : Int) (ts : List Nat)
    (vs : List (BitVec 8)) :
    gxLbl G e = some (.LLoad false lk ts vs) → vs.length = 4 →
    (∀ t v, greadsByte G e lk t v → v ≠ b0) →
    ldRes false 4 vs ≠ 0#64 := by
  intro Hl Hvl Hne Hz
  have Hl' : gxLbl G e =
      some (.LLoad false lk ts (WeakInterpProj.wbytes 4 (wordOfBytes 4 vs))) := by
    rw [wbytesWordOfBytes 4 vs Hvl]
    exact Hl
  obtain ⟨t, Ht⟩ := loadnReads G Hwf e lk ts 4 (wordOfBytes 4 vs) 0 Hl' (by decide)
  rw [show lk + ((0 : Nat) : Int) = lk by simp] at Ht
  apply Hne t _ Ht
  rw [← wbytesWordOfBytes 4 vs Hvl, AxSpinT2g.ldRes4Wbytes] at Hz
  unfold nthByte b0
  exact AxSpinT2g.sext32Zero _ Hz

/-! # 3. The non-holder's racy read: aq (`clbSameSrc`, `racyNotMine`) -/

section racy
variable (Cl : List Int) (cv : Agent → List (BitVec 8))

/-- RISK 1's premise: every write the read `r` takes a `Cl` byte from touches ALL of `Cl`. -/
def AxSpinT2g.clSrcAligned (G : Gexec) (r : Geid) : Prop :=
  ∀ a t v w, a ∈ Cl → greadsByte G r a t v → gwriteAt G t = some w →
    ∀ a', a' ∈ Cl → ∃ v', gwritesByte G w a' v'

/-- Option (A): global alignment of `Cl` writes gives it at every read. -/
theorem AxSpinT2g.srcAlignedOfAligned (G : Gexec) (r : Geid) :
    gloadValue G → clAligned Cl G → AxSpinT2g.clSrcAligned Cl G r := by
  intro Hlv Hal a t v w Ha Hr Hat
  cases t with
  | zero => cases Hat
  | succ j =>
    obtain ⟨w', Hat', Hw', -⟩ := (Hlv r a (j + 1) v Hr).1
    rw [Hat] at Hat'
    cases Hat'
    exact Hal w a v Ha Hw'

/-- THE 8 BYTES HAVE ONE SOURCE: under source alignment, every `Cl` byte `r` reads is read at
the same write index (gloadValue's co-maximality clause). -/
theorem AxSpinT2g.clbSameSrc (G : Gexec) (r : Geid) (a a' : Int) (t t' : Nat)
    (v v' : BitVec 8) :
    gwf G → gloadValue G → AxSpinT2g.clSrcAligned Cl G r → a ∈ Cl → a' ∈ Cl →
    greadsByte G r a t v → greadsByte G r a' t' v' → t = t' := by
  intro Hwf Hlv Hsa Ha Ha' Hr Hr'
  have Hnd := Hwf.1
  have Hm := (Hlv r a t v Hr).2
  have Hm' := (Hlv r a' t' v' Hr').2
  cases t with
  | zero =>
    cases t' with
    | zero => rfl
    | succ j' =>
      obtain ⟨w', Hat', -, Hvis'⟩ := (Hlv r a' (j' + 1) v' Hr').1
      obtain ⟨v0, Hw0⟩ := Hsa a' (j' + 1) v' w' Ha' Hr' Hat' a Ha
      have Hle := Hm w' v0 Hw0 Hvis'
      have Hin := (gwriteAtInv G (j' + 1) w' Hnd Hat').1
      have Hp := WeakRvwmoGraph.gwixPos G w' Hin
      omega
  | succ j =>
    obtain ⟨w, Hat, -, Hvis⟩ := (Hlv r a (j + 1) v Hr).1
    obtain ⟨v0, Hw0⟩ := Hsa a (j + 1) v w Ha Hr Hat a' Ha'
    have H1 := Hm' w v0 Hw0 Hvis
    have Hix := (gwriteAtInv G (j + 1) w Hnd Hat).2
    cases t' with
    | zero =>
      have Hin := (gwriteAtInv G (j + 1) w Hnd Hat).1
      have Hp := WeakRvwmoGraph.gwixPos G w Hin
      omega
    | succ j' =>
      obtain ⟨w', Hat', -, Hvis'⟩ := (Hlv r a' (j' + 1) v' Hr').1
      obtain ⟨v1, Hw1⟩ := Hsa a' (j' + 1) v' w' Ha' Hr' Hat' a Ha
      have H2 := Hm w' v1 Hw1 Hvis'
      have Hix' := (gwriteAtInv G (j' + 1) w' Hnd Hat').2
      omega

/-- AxSpinProt5's `cpuReadNotMine`, with alignment needed only of `r`'s SOURCES and the value
table injective only at the WRITERS. -/
theorem AxSpinT2g.cpuReadNotMineSrc (G : Gexec) (r : Geid) (vs : List (BitVec 8)) :
    gwf G → gloadValue G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) →
    AxSpinT2g.clSrcAligned Cl G r →
    (∀ k, (cv k).length = Cl.length) →
    vs.length = Cl.length →
    (∀ (j : Nat) a, Cl[j]? = some a → ∃ t v, greadsByte G r a t v ∧ vs[j]? = some v) →
    (∀ a, a ∈ Cl → G.gxImg a = some b0) →
    cv r.1 ≠ List.replicate Cl.length b0 →
    (∀ w a v, a ∈ Cl → gwritesByte G w a v → w.1 ≠ r.1 → cv w.1 ≠ cv r.1) →
    (∀ w a v, a ∈ Cl → gwritesByte G w a v → WeakRvwmoGraph.gpo G w r → False) →
    rdFact Cl cv G r → vs ≠ cv r.1 := by
  intro Hwf Hlv Hppo1 Hsa Hcvl Hlen Hrd Himg Hnz Hinj Hnself Hrf
  cases H0 : Cl[0]? with
  | none =>
    have Hl0 : Cl.length = 0 := by
      have := List.getElem?_eq_none_iff.1 H0
      omega
    have Hvs : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    intro Heq
    apply Hnz
    rw [← Heq, Hvs, Hl0]
    rfl
  | some a0 =>
    obtain ⟨t0, v0, Hr0, -⟩ := Hrd 0 a0 H0
    have Ha0 : a0 ∈ Cl := List.mem_of_getElem? H0
    have Hall : ∀ (j : Nat) a, Cl[j]? = some a →
        ∃ v, greadsByte G r a t0 v ∧ vs[j]? = some v := by
      intro j a Hj
      obtain ⟨t, v, Hr, Hv⟩ := Hrd j a Hj
      have Ha : a ∈ Cl := List.mem_of_getElem? Hj
      have Ht := AxSpinT2g.clbSameSrc Cl G r a a0 t t0 v v0 Hwf Hlv Hsa Ha Ha0 Hr Hr0
      subst Ht
      exact ⟨v, Hr, Hv⟩
    have Hval : ∀ tgt : List (BitVec 8), tgt.length = Cl.length →
        (∀ (j : Nat) a v, Cl[j]? = some a → greadsByte G r a t0 v → tgt[j]? = some v) →
        vs = tgt := by
      intro tgt Hlt Hj
      apply List.ext_getElem?
      intro j
      cases Hja : Cl[j]? with
      | some a =>
        obtain ⟨v, Hr, Hv⟩ := Hall j a Hja
        rw [Hv]
        exact (Hj j a v Hja Hr).symm
      | none =>
        have := List.getElem?_eq_none_iff.1 Hja
        rw [List.getElem?_eq_none_iff.2 (by omega), List.getElem?_eq_none_iff.2 (by omega)]
    cases t0 with
    | zero =>
      have Hz : vs = List.replicate Cl.length b0 := by
        apply Hval _ List.length_replicate
        intro j a v Hj Hr
        have Hi := (Hlv r a 0 v Hr).1
        have Ha : a ∈ Cl := List.mem_of_getElem? Hj
        simp only at Hi
        rw [Himg a Ha, Option.some.injEq] at Hi
        subst Hi
        rw [List.getElem?_replicate, if_pos (List.getElem?_eq_some_iff.1 Hj).1]
      intro Heq
      apply Hnz
      rw [← Heq, Hz]
    | succ j0 =>
      rcases Hrf a0 (j0 + 1) v0 Ha0 Hr0 with ⟨Ht, -⟩ | ⟨w, Hat, Hw0, Hcase⟩
      · cases Ht
      rcases Hcase with ⟨Hext, Hok⟩ | ⟨Hsame, Hvis⟩
      · have Hsrc : ∀ (j : Nat) a v, Cl[j]? = some a → greadsByte G r a (j0 + 1) v →
            gwritesByte G w a v := by
          intro j a v _ Hr
          obtain ⟨w', Hat', Hw', -⟩ := (Hlv r a (j0 + 1) v Hr).1
          rw [Hat] at Hat'
          cases Hat'
          exact Hw'
        rcases Hok with Hz | Hc
        · have Hz' : vs = List.replicate Cl.length b0 :=
            Hval _ List.length_replicate fun j a v Hj Hr => Hz j a v Hj (Hsrc j a v Hj Hr)
          intro Heq
          apply Hnz
          rw [← Heq, Hz']
        · have Hc' : vs = cv w.1 :=
            Hval _ (Hcvl _) fun j a v Hj Hr => Hc j a v Hj (Hsrc j a v Hj Hr)
          rw [Hc']
          exact Hinj w a0 v0 Ha0 Hw0 Hext
      · exfalso
        have Hlw : (gxLbl G w).isSome := by
          obtain ⟨l, _, _, _, Hl, _⟩ := Hw0
          rw [Hl]
          rfl
        have Hlr : (gxLbl G r).isSome := by
          obtain ⟨l, _, _, _, _, Hl, _⟩ := Hr0
          rw [Hl]
          rfl
        rcases Hvis with Hlt | Hpo
        · by_cases Hwr : w.2 < r.2
          · exact Hnself w a0 v0 Ha0 Hw0 ⟨Hsame, Hwr, Hlw, Hlr⟩
          · by_cases Heq : w.2 = r.2
            · have : w = r := Prod.ext Hsame Heq
              subst this
              exact gmoLtIrrefl G w Hlt
            · have Hrw : gmoLt G r w :=
                Hppo1 r w ⟨⟨Hsame.symm, by omega, Hlr, Hlw⟩, a0, .inr ⟨j0 + 1, v0, Hr0⟩, v0, Hw0⟩
              exact gmoLtIrrefl G w (gmoLtTrans G w r w Hlt Hrw)
        · exact Hnself w a0 v0 Ha0 Hw0 Hpo

end racy

/-- Position helper: no write of hart `i` touching `Cl` sits before row position `k` ⇒ no `Cl`
write is po-before `(i, k)`. -/
theorem AxSpinT2g.noOwnBefore (Cl : List Int) (G : Gexec) (i k : Nat) :
    (∀ k' l base wv, k' < k → gxLbl G (i, k') = some l → lbWr l = some (base, wv) →
      ∀ j : Nat, j < wv.length → accAddr base j ∉ Cl) →
    ∀ w a v, a ∈ Cl → gwritesByte G w a v → WeakRvwmoGraph.gpo G w (i, k) → False := by
  rintro Hrow ⟨wi, wk⟩ a v Ha ⟨l, base, wv, j, Hl, Hwr, Hj, rfl⟩ ⟨Hi, Hk, -, -⟩
  simp only at Hi Hk
  subst Hi
  exact Hrow wk l base wv Hk Hl Hwr j (List.getElem?_eq_some_iff.1 Hj).1 Ha

/-- A writer is a gmo member. -/
theorem AxSpinT2g.writerInGmo (G : Gexec) (Hwf : gwf G) (w : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte G w a v → w ∈ G.gxGmo := by
  rintro ⟨l, base, vs, j, Hl, Hwr, -, -⟩
  refine (Hwf.2.1 w).2 ⟨l, Hl, ?_⟩
  cases l <;> simp_all [lbWr, lbIsMem, lbIsW, lbIsR]

/-- Writers are harts of the layout (`Hharts` + `T2LayHyp.ncpu` form). -/
theorem AxSpinT2g.writerLt (G : Gexec) (Hwf : gwf G) (hs : List Agent) :
    (∀ e, e ∈ G.gxGmo → e.1 ∈ hs) → (∀ j, j ∈ hs → j < NCPU) →
    ∀ w a v, gwritesByte G w a v → w.1 < NCPU := by
  intro Hh Hlt w a v Hw
  exact Hlt _ (Hh w (AxSpinT2g.writerInGmo G Hwf w a v Hw))

/-- aq: THE NON-HOLDER'S RACY `ld lk->cpu` at `(i, k)` does not read `cpuAddr (cpuOf i)` —
`rdFact` (the `ORacy` deposit) + `Himgc` + the writers are harts < NCPU + no own lk->cpu write
po-before + RISK 1's `clSrcAligned`. -/
theorem AxSpinT2g.racyNotMine (L : Xlay) (G : Gexec) (i k : Nat) (ts : List Nat)
    (vs : List (BitVec 8)) :
    gwf G → gloadValue G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) →
    gxLbl G (i, k) = some (.LLoad false (L.xlLk + 16) ts vs) → vs.length = 8 →
    (∀ a, a ∈ clb L → G.gxImg a = some b0) →
    i < NCPU →
    (∀ w a v, a ∈ clb L → gwritesByte G w a v → w.1 < NCPU) →
    (∀ w a v, a ∈ clb L → gwritesByte G w a v → WeakRvwmoGraph.gpo G w (i, k) → False) →
    AxSpinT2g.clSrcAligned (clb L) G (i, k) →
    rdFact (clb L) cvx G (i, k) →
    ldRes false 8 vs ≠ cpuAddr (cpuOf i) := by
  intro Hwf Hlv Hppo1 Hl Hvl Himgc Hi Hwlt Hns Hsa HF Heq
  have Hcl8 : (clb L).length = 8 := by simp [clb, clRange]
  have Hl' : gxLbl G (i, k) =
      some (.LLoad false (L.xlLk + 16) ts (WeakInterpProj.wbytes 8 (wordOfBytes 8 vs))) := by
    rw [wbytesWordOfBytes 8 vs Hvl]
    exact Hl
  have Hrd : ∀ (j : Nat) a, (clb L)[j]? = some a →
      ∃ t b, greadsByte G (i, k) a t b ∧ vs[j]? = some b := by
    intro j a Hj
    have Hj' : (clRange (L.xlLk + 16) 8)[j]? = some a := Hj
    obtain ⟨rfl, Hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj'
    obtain ⟨t, Ht⟩ := loadnReads G Hwf (i, k) (L.xlLk + 16) ts 8 (wordOfBytes 8 vs) j Hl' Hjl
    refine ⟨t, _, Ht, ?_⟩
    rw [← wbytesLookup 8 (m := 8) (wordOfBytes 8 vs) j Hjl, wbytesWordOfBytes 8 vs Hvl]
  have Hcvx : vs = cvx i := by
    unfold cvx
    rw [← Heq, AxSpinT2g.ldRes8Eq vs Hvl, wbytesWordOfBytes 8 vs Hvl]
  apply AxSpinT2g.cpuReadNotMineSrc (clb L) cvx G (i, k) vs Hwf Hlv Hppo1 Hsa
    (fun k' => by rw [cvxLength, Hcl8]) (by rw [Hvl, Hcl8]) Hrd Himgc
    (by rw [Hcl8]; exact cvxNz i)
    (fun w a v Ha Hw Hne Hc => Hne (cvxInj w.1 i (Hwlt w a v Ha Hw) Hi Hc)) Hns HF Hcvx

/-- Option (A)'s corollary: global alignment of lk->cpu writes. -/
theorem AxSpinT2g.racyNotMineAl (L : Xlay) (G : Gexec) (i k : Nat) (ts : List Nat)
    (vs : List (BitVec 8)) :
    gwf G → gloadValue G → (∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2) →
    gxLbl G (i, k) = some (.LLoad false (L.xlLk + 16) ts vs) → vs.length = 8 →
    (∀ a, a ∈ clb L → G.gxImg a = some b0) →
    i < NCPU →
    (∀ w a v, a ∈ clb L → gwritesByte G w a v → w.1 < NCPU) →
    (∀ w a v, a ∈ clb L → gwritesByte G w a v → WeakRvwmoGraph.gpo G w (i, k) → False) →
    clAligned (clb L) G →
    rdFact (clb L) cvx G (i, k) →
    ldRes false 8 vs ≠ cpuAddr (cpuOf i) := by
  intro Hwf Hlv Hppo1 Hl Hvl Himgc Hi Hwlt Hns Hal HF
  exact AxSpinT2g.racyNotMine L G i k ts vs Hwf Hlv Hppo1 Hl Hvl Himgc Hi Hwlt Hns
    (AxSpinT2g.srcAlignedOfAligned (clb L) G (i, k) Hlv Hal) HF

/-! # 4. noff / intena: ppN and ppI -/

/-- `addiw a5,a5,-1`'s result — the body of `AxSpinPO5.addiwm1` (equal by `rfl`; restated so
PO5/PO6 may import this file). -/
def AxSpinT2g.subw1 (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (sign_extend (m := 12) (63#6))) 31 0)

/-- The loaded value after push_off's increment: `ldRes (stBytes 4 (addiw1 (ldRes img)))` is
the sign-extended `img + 1`. -/
theorem AxSpinT2g.incrLoad (w : BitVec 32) :
    ldRes false 4 (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w)))) =
      (w + 1#32).signExtend 64 := by
  rw [AxSpinT2g.ldRes4Wbytes, AxSpinT2g.ldRes4StBytes]
  unfold AxSpinPO3.addiw1 sign_extend
  simp only [Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
  bv_decide

/-- ppN: pop_off's noff = image + 1.  Under `img < 2³¹ − 1` the `bge zero,a5` falls through
(`zopz0zKzJ_s zero_reg noff = false`) and `noff − 1` is push_off's loaded image value. -/
theorem AxSpinT2g.noffPop (w : BitVec 32) (vp : List (BitVec 8)) :
    w.toNat < 2 ^ 31 - 1 →
    vp = stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w))) →
    zopz0zKzJ_s zero_reg (ldRes false 4 vp) = false ∧
      AxSpinT2g.subw1 (ldRes false 4 vp) = ldRes false 4 (WeakInterpProj.wbytes 4 w) := by
  intro Hw Hvp
  subst Hvp
  rw [AxSpinT2g.incrLoad, AxSpinT2g.ldRes4Wbytes]
  have Hlt : w < 0x7fffffff#32 := by
    rw [BitVec.lt_def]
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_⟩
  · unfold zopz0zKzJ_s
    rw [show (zero_reg : BitVec 64) = 0#64 by decide]
    have H : ¬ ((w + 1#32).signExtend 64).sle 0#64 = true := by bv_decide
    rw [BitVec.sle_iff_toInt_le] at H
    simp only [decide_eq_false_iff_not, ge_iff_le]
    exact H
  · unfold AxSpinT2g.subw1 sign_extend
    simp only [Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
    bv_decide

/-- ppI, step 1: the `q.c = false` arm (`noff − 1 = 0`) forces the image noff to 0, so push_off's
`beqz` took `q.b = true`. -/
theorem AxSpinT2g.noffArmZero (w : BitVec 32) (vp : List (BitVec 8)) :
    w.toNat < 2 ^ 31 - 1 →
    vp = stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w))) →
    (AxSpinT2g.subw1 (ldRes false 4 vp) != zero_reg) = false →
    w = 0#32 ∧ (ldRes false 4 (WeakInterpProj.wbytes 4 w) == zero_reg) = true := by
  intro Hw Hvp Hc
  rw [(AxSpinT2g.noffPop w vp Hw Hvp).2, AxSpinT2g.ldRes4Wbytes] at Hc
  rw [AxSpinT2g.ldRes4Wbytes]
  rw [show (zero_reg : BitVec 64) = 0#64 by decide] at Hc ⊢
  simp only [bne_eq_false_iff_eq] at Hc
  have Hw0 : w = 0#32 := by bv_decide
  subst Hw0
  exact ⟨rfl, by decide⟩

/-- ppI, step 2: pop_off's intena reload of push_off's `sw intena` (`stBytes 4 0`) is 0, so its
`beqz` is taken (no `intr_on`). -/
theorem AxSpinT2g.intenaZero (G : Gexec) (Hwf : gwf G) (e : Geid) (base : Int)
    (ts : List Nat) (vi : List (BitVec 8)) :
    gxLbl G e = some (.LLoad false base ts vi) → vi.length = 4 →
    (∀ (j : Nat) a t b, (clRange base 4)[j]? = some a → greadsByte G e a t b →
      (stBytes 4 0#64)[j]? = some b) →
    (ldRes false 4 vi == zero_reg) = true := by
  intro Hl Hvl Hf
  have H := AxSpinT2g.privReadEq G Hwf e base ts 4 vi _ Hl Hvl
    (by unfold stBytes AxDataX.wrb; exact wbytesLength 4 _) Hf
  rw [H, AxSpinT2g.ldRes4StBytes]
  decide

end Weak
