/-
Weak: **THEOREM 2, STAGE 2, row `AxSpinT2h` — THE FIVE DESIGNATED CUT ARMS** (stage-2 design
`notes/weak-lb-thm2-stage2.md` §B, §C row `AxSpinT2h`, §D Q-S2-2 / Q-S2-5).  NEW Lean file (no
Rocq source; Rocq's ID-8 `HΨend` + `wpd_bnd` readback is the model).

## What this file proves

Each arm is a CLOSED (`⊢`) proof of EXACTLY the end-continuation premise the merged P-forms
expose (`KShortEnd`/`KLongEnd`, AxSpinHdA; `KppN`/`KppI`, AxSpinPO5/PO6), i.e. "the deposit
annotations in hand -∗ ⌜LEN = cutPos⌝ → ∀ pr, WPd ⟨pr, cutPos⟩ Ψ".  Each is proved by the
ROW-END READBACK (`AxSpinT2h.wpdEnd1` / `wpdEnd2P`, from the local copy `AxSpinT2h.wpdEndAnn` of
`AxSpinApA.wpdEndAnn`): at a position `≥ LEN` no row item is left, every step is administrative,
and AxWpD's row-end clause (`postLifting`) hands the hart's own annotations back as PURE facts;
the fact refutes the flipped gate (pure lemmas of `AxSpinT2g`), so the gate took the NORMAL arm
and the caller's resource-free premise `HΨ` ("LEN = cutPos ∧ gate normal ⇒ Ψ") closes the post.

| arm       | P-form premise shape          | deposit read back                    | refutation (pure)               |
| `cutAq`   | `KLongEnd … True (ORacy …(k+4))` | `rdFact (clb L) cvx G (i, k+4)`  | `AxSpinT2g.cpuReadNotMineSrc` (= `racyNotMine`, aq-generic) |
| `cutRelS` | `KShortEnd … (OHeld … k ∗ handle)` | `OHeld`'s `∀ t b, greadsByte … → b ≠ b0` | `heldNonzero`'s argument     |
| `cutRelL` | `KLongEnd … (OHeld …) (OOwn …(k+4))` | `OOwn`'s bytes = `wbytes 8 val` | `ownIsMine`'s argument        |
| `cutPpN`  | `KppN` (PO5/PO6)              | `rlFact4` at `k+6` (push_off's `sw noff`) | `AxSpinT2g.noffPop`         |
| `cutPpI`  | `KppI` (PO6)                  | `rlFact4` at `k+6` AND at `k+8` (`sw intena`) | `noffArmZero` + `intenaZero` |

In the P-forms' generic positions: `k` = holding's entry (`aq`: acquire's `t2KHd q`; `rlS`/`rlL`:
release's `t2KRh q`) resp. pop_off's entry `t2KPp q`, so the arms' ends `k + 12`, `k + 1`,
`k + 12`, `k + 7`, `k + 9` are `cutPos .aq/.rlS/.rlL/.ppN/.ppI q` (AxSpinT2f; `AxSpinT2h.cutPosEqs`,
`rfl`).  The caller's `HΨ` receives the gate in graph-value form; `AxSpinT2h.gateAq` …
`AxSpinT2h.gatePpI` turn it into AxSpinT2f's `t2GateOk j (grow GD i) q i` (via `AxSpinT2f.gvGrow`).
`AxSpinT2h.noffImgRead` is the image bridge for the noff premises: push_off's genesis load fact
(`AxSpinLd4P.genFact4`, read back) + `noffImgOk` (AxSpinT2f's `HimgNoff` form, Q-S2-3) ⇒ the
loaded bytes are the image word `BitVec.ofInt 32 v` with `toNat < 2³¹ − 1`.

## Deviations / honesty / open points

1. **Q-S2-B OPEN (byte mixing, `AxSpinT2g` header risk 1).**  `cutAq` carries the explicit, named
   premise `AxSpinT2g.clSrcAligned (clb L) G (i, k + 4)` ("every write the racy `ld lk->cpu` takes
   a byte from touches all 8 `lk->cpu` bytes").  Without it the statement is FALSE as a pure graph
   statement (protXv6 lets a lock holder `sb` one byte of its own `cvx`).  The owner chooses (A) a
   graph premise (`clAligned`, discharged by `AxSpinT2g.srcAlignedOfAligned`) or (B) a protocol
   strengthening; nothing here weakens the arm silently.
2. **The end lemma is COPIED** (`AxSpinT2h.wpdEndAnn` = `AxSpinApA.wpdEndAnn`, same statement and
   proof): AxSpinApA imports AxSpinAq2/AxSpinRl4b and will import this file (the ApA P-form), so
   importing it here would be a cycle.  `AxSpinApA.rowEndShape` is copied likewise
   (`AxSpinT2h.rowEndShape`).  Imports: HdC, PO6, T2g, T2f only.
3. **Load labels are aq-GENERIC.**  The row shapes (`lshape`/`sshape`/`ishape .RL`) only say
   `aident lb = .IRead aq pa n`; AxSpinT2g's consumers are stated for `.LLoad false …`.  The
   arms take the row item in that shape form (`AxSpinT2h.RdAt`, guarded by its position) and use
   the aq-generic readers `AxSpinT2h.ldReads` / `AxSpinT2h.ldEq` (re-proving the 4-line label
   steps of `privReadEq`/`heldNonzero`/`racyNotMine`; the core `cpuReadNotMineSrc`, `noffPop`,
   `noffArmZero`, `ldRes*` lemmas are reused as is).
4. **`cutRelL` takes `val = cpuAddr (cpuOf i)`** (`OOwn`'s `val` is acquire's `mycpuRet tp`; the
   caller has `AxSpinT2a.mycpuRetHart`).
5. **The noff arms take push_off's store data as a pure premise** `rlN = some (kw, stBytes 4
   (addiw1 (ldRes false 4 (wbytes 4 w))), cls)` with `w.toNat < 2³¹ − 1`, i.e. push_off's noff
   load read the image word `w`.  OPEN POINT for the PO5/PO6/ApA lanes: that fact is push_off's
   GENESIS annotation (`genFact4`, PO4's continuation), a RESOURCE, but `KppN`/`KppI` are
   resource-free (`⊢ ann4O … -∗ WPd`), so the annotation cannot be carried into the arm; either
   the caller obtains `w` purely, or `KppN`/`KppI` get a frame (as `wpdPpMidP` already does for
   its `KppI`), in which case `AxSpinT2h.noffImgRead` + `AxSpinT2h.wpdEnd2P` give the arm with
   the genesis annotation as a second readback.  `cutPpI` additionally takes `w = 0 → rlI = some
   (kwi, stBytes 4 0, clsi)` (image noff 0 ⇒ push_off took `b = true` (`poArm`) and stored
   intena 0, PO4) and PO6's arm pin `Hvc` (`addiwm1 … != zero_reg = c`).
6. `HΨ` is resource-free and receives `LEN = cutPos` and the gate (normal arm) in graph-value
   form; it is the designated-cut counterpart of the P-forms' resource-free hook (Q-S2-2).

**Reused:** `AxSpinT2g.cpuReadNotMineSrc`/`clSrcAligned`/`ldRes8Eq`/`ldRes8Wbytes`/`ldRes4Wbytes`/
`ldRes4StBytes`/`sext32Zero`/`noffPop`/`noffArmZero` (AxSpinT2g), `KShortEnd`/`KLongEnd`
(AxSpinHdA), `ORacy`/`OHeld`/`OOwn` (AxSpinHdB), `AxSpinPO5.ann4O`, `AxSpinLd4P.rlFact4`,
`addiwm1` (AxSpinPO5), `AxSpinPO3.addiw1`, `cutPos`/`t2GateOk`/`AxSpinT2f.gvGrow`/`noffImgOk`
(AxSpinT2f), `lblTsLen` (AxSpinX5), `clRangeLookup2`/`AxSpinX4.clRangeLookup` (AxSpinX4),
`AxWp.growLookup`, `annotAgreeBig`, `AxSpinProt7.readbackBig`, `shSkip`, `AxSpinWit.gconstEq`,
`progressOblMaybestuck`, `AxWpD.wpdMUnfoldStep`, `cvxInj`/`cvxNz`/`cvxLength` (AxSpinX).
New unqualified names (design names, grepped absent): `cutAq`, `cutRelS`, `cutRelL`, `cutPpN`,
`cutPpI`; every helper is `AxSpinT2h.*`.
-/
import Weak.AxSpinHdC
import Weak.AxSpinPO6
import Weak.AxSpinT2g
import Weak.AxSpinT2f

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Pure: aq-generic load readers and the five gates -/

/-- Row item `k` is a read of `n` bytes at `pa` (the shape the row families give: `lshape`,
`sshape`, `ishape (.RL pa n)`). -/
def AxSpinT2h.RdAt (row : List Lbl) (k : Nat) (pa : Int) (n : Nat) : Prop :=
  ∃ lb, row[k]? = some lb ∧ ∃ aq, aident lb = .IRead aq pa n

/-- A read item with a graph value is a load label carrying that value. -/
theorem AxSpinT2h.ldOfRd (GD : Gdexec) (i k : Nat) (pa : Int) (n : Nat) (vs : List (BitVec 8)) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k pa n → graphValue GD (i, k) = some vs →
    ∃ aq ts, gxLbl GD.gdG (i, k) = some (.LLoad aq pa ts vs) ∧ vs.length = n := by
  rintro ⟨lb, Hlb, aq, Hid⟩ Hgv
  have Hl := AxWp.growLookup GD i k lb Hlb
  unfold graphValue at Hgv
  rw [Hl] at Hgv
  cases lb with
  | LLoad aq' b ts vs' =>
    simp only [aident] at Hid
    injection Hid with h1 h2 h3
    subst h1 h2
    simp only [Option.bind, lblValue, Option.some.injEq] at Hgv
    subst Hgv
    exact ⟨aq', ts, Hl, h3⟩
  | LStore _ _ _ _ => simp [aident] at Hid
  | LFence _ _ _ _ => simp [aident] at Hid
  | LRmw _ _ _ _ _ _ _ => simp [aident] at Hid

/-- (aq-generic `loadnReads`) every byte of a load label is read. -/
theorem AxSpinT2h.ldReads (G : Gexec) (Hwf : gwf G) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (j : Nat) (v : BitVec 8) :
    gxLbl G e = some (.LLoad aq base ts vs) → vs[j]? = some v →
    ∃ t, greadsByte G e (base + (j : Int)) t v := by
  intro Hl Hv
  have Hlen := lblTsLen G Hwf e aq base ts vs Hl
  have Hj : j < ts.length := by
    have := (List.getElem?_eq_some_iff.1 Hv).1
    omega
  exact ⟨ts[j], _, base, ts, vs, j, Hl, rfl, List.getElem?_eq_getElem Hj, Hv, rfl⟩

/-- (aq-generic `privReadEq`) a per-byte read fact pins a load's values. -/
theorem AxSpinT2h.ldEq (G : Gexec) (Hwf : gwf G) (e : Geid) (aq : Bool) (base : Int)
    (ts : List Nat) (n : Nat) (vs tgt : List (BitVec 8)) :
    gxLbl G e = some (.LLoad aq base ts vs) → vs.length = n → tgt.length = n →
    (∀ (j : Nat) a t b, (clRange base n)[j]? = some a → greadsByte G e a t b →
      tgt[j]? = some b) →
    vs = tgt := by
  intro Hl Hvl Htl Hf
  apply List.ext_getElem?
  intro j
  by_cases Hj : j < n
  · have Hv : vs[j]? = some (vs[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
    obtain ⟨t, Hr⟩ := AxSpinT2h.ldReads G Hwf e aq base ts vs j _ Hl Hv
    rw [Hv]
    exact (Hf j _ t _ (clRangeLookup2 base n j Hj) Hr).symm
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem AxSpinT2h.stBytes4Len (v : BitVec 64) : (stBytes 4 v).length = 4 := by
  unfold stBytes AxDataX.wrb
  exact wbytesLength 4 _

/-- aq: the racy `ld lk->cpu`'s `rdFact` deposit refutes "= this hart's cpu" (Q-S2-B premise
`clSrcAligned`). -/
theorem AxSpinT2h.racyGate (L : Xlay) (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (i k : Nat) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k (L.xlLk + 16) 8 →
    (∀ a, a ∈ clb L → GD.gdG.gxImg a = some b0) → i < NCPU →
    (∀ w a v, a ∈ clb L → gwritesByte GD.gdG w a v → w.1 < NCPU) →
    (∀ w a v, a ∈ clb L → gwritesByte GD.gdG w a v →
      WeakRvwmoGraph.gpo GD.gdG w (i, k) → False) →
    AxSpinT2g.clSrcAligned (clb L) GD.gdG (i, k) →
    rdFact (clb L) cvx GD.gdG (i, k) →
    ∀ vs, graphValue GD (i, k) = some vs → ldRes false 8 vs ≠ cpuAddr (cpuOf i) := by
  intro Hrd Himgc Hi Hwlt Hns Hsa HF vs Hgv Heq
  obtain ⟨aq, ts, Hl, Hvl⟩ := AxSpinT2h.ldOfRd GD i k _ _ vs Hrd Hgv
  obtain ⟨Hwf, Hppo, Hlv, -⟩ := Hcons
  have Hppo1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
    fun e1 e2 H => Hppo e1 e2 (Or.inl (Or.inl H))
  have Hcl8 : (clb L).length = 8 := by simp [clb, clRange]
  have Hrd' : ∀ (j : Nat) a, (clb L)[j]? = some a →
      ∃ t b, greadsByte GD.gdG (i, k) a t b ∧ vs[j]? = some b := by
    intro j a Hj
    have Hj' : (clRange (L.xlLk + 16) 8)[j]? = some a := Hj
    obtain ⟨rfl, Hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj'
    have Hv : vs[j]? = some (vs[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
    obtain ⟨t, Ht⟩ := AxSpinT2h.ldReads GD.gdG Hwf (i, k) aq _ ts vs j _ Hl Hv
    exact ⟨t, _, Ht, Hv⟩
  have Hcvx : vs = cvx i := by
    unfold cvx
    rw [← Heq, AxSpinT2g.ldRes8Eq vs Hvl, wbytesWordOfBytes 8 vs Hvl]
  exact AxSpinT2g.cpuReadNotMineSrc (clb L) cvx GD.gdG (i, k) vs Hwf Hlv Hppo1 Hsa
    (fun k' => by rw [cvxLength, Hcl8]) (by rw [Hvl, Hcl8]) Hrd' Himgc
    (by rw [Hcl8]; exact cvxNz i)
    (fun w a v Ha Hw Hne Hc => Hne (cvxInj w.1 i (Hwlt w a v Ha Hw) Hi Hc)) Hns HF Hcvx

/-- rlS: the holder's lock-word read deposit (every byte read ≠ 0) refutes "read 0". -/
theorem AxSpinT2h.heldGate (GD : Gdexec) (Hwf : gwf GD.gdG) (i k : Nat) (lk : Int) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k lk 4 →
    (∀ t b, greadsByte GD.gdG (i, k) lk t b → b ≠ b0) →
    ∀ vs, graphValue GD (i, k) = some vs → ldRes false 4 vs ≠ 0#64 := by
  intro Hrd Hne vs Hgv Hz
  obtain ⟨aq, ts, Hl, Hvl⟩ := AxSpinT2h.ldOfRd GD i k _ _ vs Hrd Hgv
  have Hv0 : vs[0]? = some (nthByte (wordOfBytes 4 vs) 0) := by
    have H := wbytesLookup 4 (wordOfBytes 4 vs) 0 (by decide)
    rw [wbytesWordOfBytes 4 vs Hvl] at H
    exact H
  obtain ⟨t, Ht⟩ := AxSpinT2h.ldReads GD.gdG Hwf (i, k) aq lk ts vs 0 _ Hl Hv0
  rw [show lk + ((0 : Nat) : Int) = lk by simp] at Ht
  apply Hne t _ Ht
  rw [← wbytesWordOfBytes 4 vs Hvl, AxSpinT2g.ldRes4Wbytes] at Hz
  unfold nthByte b0
  exact AxSpinT2g.sext32Zero _ Hz

/-- rlL: the holder's owned `ld lk->cpu` deposit (bytes = `val`'s) gives the value `val`. -/
theorem AxSpinT2h.ownGate (L : Xlay) (GD : Gdexec) (Hwf : gwf GD.gdG) (i k : Nat)
    (val : BitVec 64) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k (L.xlLk + 16) 8 →
    (∀ (j : Nat) a t b, (clb L)[j]? = some a → greadsByte GD.gdG (i, k) a t b →
      (WeakInterpProj.wbytes 8 val)[j]? = some b) →
    ∀ vs, graphValue GD (i, k) = some vs → ldRes false 8 vs = val := by
  intro Hrd Hf vs Hgv
  obtain ⟨aq, ts, Hl, Hvl⟩ := AxSpinT2h.ldOfRd GD i k _ _ vs Hrd Hgv
  have H := AxSpinT2h.ldEq GD.gdG Hwf (i, k) aq (L.xlLk + 16) ts 8 vs _ Hl Hvl
    (wbytesLength 8 val) Hf
  rw [H]
  exact AxSpinT2g.ldRes8Wbytes val

/-- ppN: pop_off's noff reload of push_off's `sw noff` (image `w` + 1) passes `bge`. -/
theorem AxSpinT2h.noffGate (GD : Gdexec) (Hwf : gwf GD.gdG) (i k : Nat) (pa : Int)
    (w : BitVec 32) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k pa 4 → w.toNat < 2 ^ 31 - 1 →
    (∀ (j : Nat) a t b, (clRange pa 4)[j]? = some a → greadsByte GD.gdG (i, k) a t b →
      (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w))))[j]? = some b) →
    ∀ vs, graphValue GD (i, k) = some vs →
      vs = stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w))) ∧
      zopz0zKzJ_s zero_reg (ldRes false 4 vs) = false := by
  intro Hrd Hw Hf vs Hgv
  obtain ⟨aq, ts, Hl, Hvl⟩ := AxSpinT2h.ldOfRd GD i k _ _ vs Hrd Hgv
  have H := AxSpinT2h.ldEq GD.gdG Hwf (i, k) aq pa ts 4 vs _ Hl Hvl
    (AxSpinT2h.stBytes4Len _) Hf
  exact ⟨H, (AxSpinT2g.noffPop w vs Hw H).1⟩

/-- ppI: pop_off's intena reload of push_off's `sw intena` (`stBytes 4 0`) is 0. -/
theorem AxSpinT2h.intenaGate (GD : Gdexec) (Hwf : gwf GD.gdG) (i k : Nat) (pa : Int) :
    AxSpinT2h.RdAt (AxOpsem.grow GD i) k pa 4 →
    (∀ (j : Nat) a t b, (clRange pa 4)[j]? = some a → greadsByte GD.gdG (i, k) a t b →
      (stBytes 4 0#64)[j]? = some b) →
    ∀ vs, graphValue GD (i, k) = some vs → (ldRes false 4 vs == zero_reg) = true := by
  intro Hrd Hf vs Hgv
  obtain ⟨aq, ts, Hl, Hvl⟩ := AxSpinT2h.ldOfRd GD i k _ _ vs Hrd Hgv
  have H := AxSpinT2h.ldEq GD.gdG Hwf (i, k) aq pa ts 4 vs _ Hl Hvl
    (AxSpinT2h.stBytes4Len _) Hf
  rw [H, AxSpinT2g.ldRes4StBytes]
  decide

/-- The image bridge for the noff premises: push_off's GENESIS noff load (`genFact4` read back)
of `cpus[cpuOf i].noff` + `noffImgOk` ⇒ the loaded bytes are the image word, in `noffPop`'s
range. -/
theorem AxSpinT2h.noffImgRead (G : Gexec) (Hwf : gwf G) (e : Geid) (aq : Bool) (i : Agent)
    (ts : List Nat) (vp : List (BitVec 8)) (v : Int) :
    gxLbl G e = some (.LLoad aq (cpuZ i + 120) ts vp) → vp.length = 4 →
    (∀ a, a ∈ clRange (cpuZ i + 120) 4 → ∀ t b, greadsByte G e a t b →
      t = 0 ∧ G.gxImg a = some b) →
    noffImgOk G.gxImg i v →
    vp = WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v) ∧ (BitVec.ofInt 32 v).toNat < 2 ^ 31 - 1 := by
  intro Hl Hvl Hg ⟨H0, H1, Himg⟩
  refine ⟨AxSpinT2h.ldEq G Hwf e aq _ ts 4 vp _ Hl Hvl (wbytesLength 4 _) ?_, ?_⟩
  · intro j a t b Hj Hr
    obtain ⟨rfl, Hjl⟩ := AxSpinX4.clRangeLookup _ _ _ _ Hj
    have Hb := (Hg _ (List.mem_of_getElem? Hj) t b Hr).2
    have Hw := wbytesLookupGen 4 (BitVec.ofInt 32 v) j Hjl
    have H2 := Himg j _ Hw
    rw [Hb] at H2
    rw [Hw, H2]
  · rw [BitVec.toNat_ofInt]
    omega

/-! # 2. The gates in AxSpinT2f's vocabulary -/

/-- The arms' ends are AxSpinT2f's `cutPos` at the callers' entry positions. -/
theorem AxSpinT2h.cutPosEqs (q : T2Prm) :
    cutPos .aq q = t2KHd q + 12 ∧ cutPos .rlS q = t2KRh q + 1 ∧ cutPos .rlL q = t2KRh q + 12 ∧
      cutPos .ppN q = t2KPp q + 7 ∧ cutPos .ppI q = t2KPp q + 9 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem AxSpinT2h.gateAq (GD : Gdexec) (i : Agent) (q : T2Prm) :
    (∀ vs, graphValue GD (i, t2KHd q + 4) = some vs → ldRes false 8 vs ≠ cpuAddr (cpuOf i)) →
    t2GateOk .aq (AxOpsem.grow GD i) q i :=
  fun H _ vs Hv => H vs (by rw [AxSpinT2f.gvGrow]; exact Hv)

theorem AxSpinT2h.gateRlS (GD : Gdexec) (i : Agent) (q : T2Prm) :
    (∀ vs, graphValue GD (i, t2KRh q) = some vs → ldRes false 4 vs ≠ 0#64) →
    t2GateOk .rlS (AxOpsem.grow GD i) q i :=
  fun H vs Hv => H vs (by rw [AxSpinT2f.gvGrow]; exact Hv)

theorem AxSpinT2h.gateRlL (GD : Gdexec) (i : Agent) (q : T2Prm) :
    (∀ vs, graphValue GD (i, t2KRh q + 4) = some vs → ldRes false 8 vs = cpuAddr (cpuOf i)) →
    t2GateOk .rlL (AxOpsem.grow GD i) q i :=
  fun H vs Hv => H vs (by rw [AxSpinT2f.gvGrow]; exact Hv)

theorem AxSpinT2h.gatePpN (GD : Gdexec) (i : Agent) (q : T2Prm) :
    (∀ vs, graphValue GD (i, t2KPp q + 6) = some vs →
      zopz0zKzJ_s zero_reg (ldRes false 4 vs) = false) →
    t2GateOk .ppN (AxOpsem.grow GD i) q i :=
  fun H vs Hv => H vs (by rw [AxSpinT2f.gvGrow]; exact Hv)

theorem AxSpinT2h.gatePpI (GD : Gdexec) (i : Agent) (q : T2Prm) (c : Bool) :
    (c = false → ∀ vs, graphValue GD (i, t2KPp q + 8) = some vs →
      (ldRes false 4 vs == zero_reg) = true) → c = q.c →
    t2GateOk .ppI (AxOpsem.grow GD i) q i := by
  intro H hc hq vs Hv
  exact H (hc.trans hq) vs (by rw [AxSpinT2f.gvGrow]; exact Hv)

/-! # 3. Past the row end (local copy of `AxSpinApA.wpdEndAnn`, deviation 2) -/

/-- (= `AxSpinApA.rowEndShape`) past the row end, a program step is administrative and keeps
the position. -/
theorem AxSpinT2h.rowEndShape (row : List Lbl) (s : Athread) (l : Wlabel) (s' : Athread)
    (Hnone : row[s.atK]? = none) :
    AxOpsem.astepProg row s l s' → lbAdmin true l ∧ s'.atK = s.atK := by
  intro h
  cases h with
  | AStepAdmin p k d l p' d' hadm hst => exact ⟨hadm, rfl⟩
  | AStepWrite p k d l lb p' d' hlk _ _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone
  | AStepFence p k d l lb p' d' hlk _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone

section rowend
open Iris.Std.PartialMap
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- (= `AxSpinApA.wpdEndAnn`, same statement and proof) PAST THE ROW END, an annotation
readback: from `k0 ≥ LEN` every program state's WPd holds for a state-independent post that
follows from owned annotations of hart `i`. -/
theorem AxSpinT2h.wpdEndAnn (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (m : Mea GF)
    (Hm : ∀ e, e ∈ (FiniteMap.dom_set m : GSet Geid) → e.1 = i) (Φ : Athread → IProp GF)
    (HRQ : ∀ s, ([∗map] R ∈ m, R) ⊢ Φ s) :
    ⊢ ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗ ∀ pr : Pexv6,
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have Hnone : (AxOpsem.grow (gtAdGd GT) i)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ pr : Pexv6, ([∗map] e ↦ R ∈ m, AxAnnot.annotOwn e R) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
    iloeb as IH
    iintro %pr Hp
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT)
      rvwmoCatConsistent .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (AxSpinX2.xG L GT nm) _ i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := (AxSpinWit.gconstEq (gtAdGd GT) Xv6N Unit (protXv6 L) nm GD') $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk'⟩ := AxSpinT2h.rowEndShape _ _ l s' Hnone Hst
      rw [AxSpinRow.lbAdminWdata l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p' Hp
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply (shSkip (gtAdGd GT) Xv6N Unit (protXv6 L) nm i)
      inext
      iapply IH $$ %p' Hp
    · iintro %-
      unfold postLifting
      iintro %na Hna
      ihave ⟨%Hdomi, #Hw⟩ := annotAgreeBig na m $$ Hna Hp
      imodintro
      isplitl [Hna]
      · iexact Hna
      iintro Hbig
      ihave HR := AxSpinProt7.readbackBig na m i Hdomi Hm $$ Hbig Hw
      inext
      imodintro
      iapply (HRQ _) $$ HR
  iintro Hp %pr
  iapply H $$ %pr Hp

/-- ONE pure annotation of hart `i` read back past the row end. -/
theorem AxSpinT2h.wpdEnd1 (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (e : Geid) (he : e.1 = i) (P : Prop)
    (Φ : Athread → IProp GF) (HRQ : P → ∀ s, ⊢ Φ s) (pr : Pexv6) :
    ⊢ AxAnnot.annotOwn e iprop(⌜P⌝) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have hn : get? (∅ : Mea GF) e = none := lookupEmpty
  have Hm : ∀ e', e' ∈ (FiniteMap.dom_set (insert (∅ : Mea GF) e iprop(⌜P⌝)) : GSet Geid) →
      e'.1 = i := by
    intro e' he'
    rw [domInsert, domEmpty] at he'
    rcases elemOfUnion.1 he' with h | h
    · rw [elemOfSingleton.1 h]; exact he
    · exact absurd h (fun h' => (elemOfEmpty (S := GSet Geid)).1 h')
  have HR : ∀ s, ([∗map] R ∈ insert (∅ : Mea GF) e iprop(⌜P⌝), R) ⊢ Φ s := by
    intro s
    iintro Hb
    icases (BigSepM.bigSepM_insert hn).1 $$ Hb with ⟨%HP, -⟩
    iapply (HRQ HP s)
  iintro A
  ihave W := (AxSpinT2h.wpdEndAnn L GT nm i k0 Hend _ Hm Φ HR) $$ [A]
  · iapply (BigSepM.bigSepM_insert hn).2
    isplitl [A]
    · iexact A
    iapply BigSepM.bigSepM_empty.2
    itrivial
  iapply W $$ %pr

/-- TWO pure annotations at distinct events of hart `i` read back past the row end. -/
theorem AxSpinT2h.wpdEnd2P (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (k0 : Nat)
    (Hend : (AxOpsem.grow (gtAdGd GT) i).length ≤ k0) (e1 e2 : Geid) (h1 : e1.1 = i)
    (h2 : e2.1 = i) (hne : e1 ≠ e2) (P1 P2 : Prop) (Φ : Athread → IProp GF)
    (HRQ : P1 → P2 → ∀ s, ⊢ Φ s) (pr : Pexv6) :
    ⊢ AxAnnot.annotOwn e1 iprop(⌜P1⌝) -∗ AxAnnot.annotOwn e2 iprop(⌜P2⌝) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨pr, k0⟩ Φ := by
  have hn1 : get? (∅ : Mea GF) e1 = none := lookupEmpty
  have hn2 : get? (insert (∅ : Mea GF) e1 iprop(⌜P1⌝)) e2 = none := by
    rw [lookupInsertNe hne]; exact lookupEmpty
  have Hm : ∀ e, e ∈ (FiniteMap.dom_set (insert (insert (∅ : Mea GF) e1 iprop(⌜P1⌝)) e2
      iprop(⌜P2⌝)) : GSet Geid) → e.1 = i := by
    intro e he
    rw [domInsert, domInsert, domEmpty] at he
    rcases elemOfUnion.1 he with h | h
    · rw [elemOfSingleton.1 h]; exact h2
    · rcases elemOfUnion.1 h with h | h
      · rw [elemOfSingleton.1 h]; exact h1
      · exact absurd h (fun h' => (elemOfEmpty (S := GSet Geid)).1 h')
  have HR : ∀ s, ([∗map] R ∈ insert (insert (∅ : Mea GF) e1 iprop(⌜P1⌝)) e2 iprop(⌜P2⌝), R) ⊢
      Φ s := by
    intro s
    iintro Hb
    icases (BigSepM.bigSepM_insert hn2).1 $$ Hb with ⟨%H2, Hb⟩
    icases (BigSepM.bigSepM_insert hn1).1 $$ Hb with ⟨%H1, -⟩
    iapply (HRQ H1 H2 s)
  iintro A1 A2
  ihave W := (AxSpinT2h.wpdEndAnn L GT nm i k0 Hend _ Hm Φ HR) $$ [A1 A2]
  · iapply (BigSepM.bigSepM_insert hn2).2
    isplitl [A2]
    · iexact A2
    iapply (BigSepM.bigSepM_insert hn1).2
    isplitl [A1]
    · iexact A1
    iapply BigSepM.bigSepM_empty.2
    itrivial
  iapply W $$ %pr

end rowend

/-! # 4. The five designated cut arms -/

section arms
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N) (Hcons : rvwmoCatConsistent (gtAdGd GT))

include Hcons in
/-- **`aq`** (acquire's holding, LONG arm: the racy `ld lk->cpu` at `k + 4`; the row ends at
`k + 12 = cutPos .aq q` before `c.bnez a0,panic`): the `ORacy` deposit refutes "read this hart's
own cpu" — `KLongEnd` as `holdingFromAcquireP` exposes it.  **OWNER QUESTION Q-S2-B OPEN:**
`HsrcAl` (`AxSpinT2g.clSrcAligned`, the read's lk->cpu sources are full-width) is an explicit
premise (deviation 1). -/
theorem cutAq (i : Agent) (k : Nat) (rs0 : RegFile) (Pra Ps0 Ps1 Pram Ps0m : BitVec 64)
    (Ψ : Athread → IProp GF) :
    (k + 4 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (k + 4) (L.xlLk + 16) 8) →
    (∀ a, a ∈ clb L → (gtAdGd GT).gdG.gxImg a = some b0) →
    i < NCPU →
    (∀ w a v, a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v → w.1 < NCPU) →
    (∀ w a v, a ∈ clb L → gwritesByte (gtAdGd GT).gdG w a v →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w (i, k + 4) → False) →
    -- OWNER QUESTION Q-S2-B (byte mixing): the racy read's lk->cpu sources are full-width
    (HsrcAl : AxSpinT2g.clSrcAligned (clb L) (gtAdGd GT).gdG (i, k + 4)) →
    -- the caller's post at the cut, given the NORMAL arm
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 12 →
      (∀ vs, graphValue (gtAdGd GT) (i, k + 4) = some vs →
        ldRes false 8 vs ≠ cpuAddr (cpuOf i)) →
      ∀ s, ⊢ Ψ s) →
    ⊢ KLongEnd (hlc := hlc) L GT nm i Ψ k rs0 Pra Ps0 Ps1 Pram Ps0m (fun _ => iprop(True))
        (ORacy L GT i (k + 4)) := by
  intro Hrd Himgc Hi Hwlt Hns Hsa HΨ
  unfold KLongEnd ORacy
  iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp - Hc - - - - -
  have hL : (AxOpsem.grow (gtAdGd GT) i).length = k + 12 := Hp.1
  iapply (AxSpinT2h.wpdEnd1 L GT nm i (k + 12) (by omega) (i, k + 4) rfl _ Ψ
    (fun HF s => HΨ hL (AxSpinT2h.racyGate L (gtAdGd GT) Hcons i (k + 4) (Hrd (by omega))
      Himgc Hi Hwlt Hns Hsa HF) s) pr)
  iexact Hc

include Hcons in
/-- **`rlS`** (release's holding, SHORT arm: the holder's `lw lk->locked` at `k`; the row ends
at `k + 1 = cutPos .rlS q` before `c.bnez`): `OHeld`'s deposit (every byte read ≠ 0) refutes
"read 0" — `KShortEnd` as `holdingFromReleaseP` (`hb = false`) exposes it. -/
theorem cutRelS (i : Agent) (k kc kw : Nat) (val : BitVec 64) (Qc Qw : IProp GF)
    (Ψ : Athread → IProp GF) :
    (k < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) k L.xlLk 4) →
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 1 →
      (∀ vs, graphValue (gtAdGd GT) (i, k) = some vs → ldRes false 4 vs ≠ 0#64) →
      ∀ s, ⊢ Ψ s) →
    ⊢ KShortEnd (hlc := hlc) L GT nm i Ψ k
        (fun v => iprop(OHeld L GT nm i kc k Qc k v ∗ AxAnnot.annotOwn (i, kw)
          iprop(Qw ∗ RVL nm.xnH (gtAdGd GT) (clb L) (i, kw) (WeakInterpProj.wbytes 8 val)))) := by
  intro Hrd HΨ
  unfold KShortEnd
  simp only [OHeld, ↓reduceIte]
  iintro %vlk %pr %Hp ⟨⟨-, Hf⟩, -⟩
  have hL : (AxOpsem.grow (gtAdGd GT) i).length = k + 1 := Hp.1
  iapply (AxSpinT2h.wpdEnd1 L GT nm i (k + 1) (by omega) (i, k) rfl _ Ψ
    (fun HF s => HΨ hL (AxSpinT2h.heldGate (gtAdGd GT) Hcons.1 i k L.xlLk (Hrd (by omega)) HF) s)
    pr)
  iexact Hf

include Hcons in
/-- **`rlL`** (release's holding, LONG arm: the holder's owned `ld lk->cpu` at `k + 4`; the row
ends at `k + 12 = cutPos .rlL q` before `c.beqz a0,panic`): `OOwn`'s deposit (bytes = `val`'s,
`val` = this hart's cpu) refutes "≠ own cpu" — `KLongEnd` as `holdingFromReleaseP` (`hb = true`)
exposes it. -/
theorem cutRelL (i : Agent) (k kc kw : Nat) (rs0 : RegFile) (Pra Ps0 Ps1 Pram Ps0m : BitVec 64)
    (val : BitVec 64) (Qc Qw : IProp GF) (Ψ : Athread → IProp GF) :
    val = cpuAddr (cpuOf i) →
    (k + 4 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (k + 4) (L.xlLk + 16) 8) →
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 12 →
      (∀ vs, graphValue (gtAdGd GT) (i, k + 4) = some vs →
        ldRes false 8 vs = cpuAddr (cpuOf i)) →
      ∀ s, ⊢ Ψ s) →
    ⊢ KLongEnd (hlc := hlc) L GT nm i Ψ k rs0 Pra Ps0 Ps1 Pram Ps0m
        (OHeld L GT nm i kc k Qc k) (OOwn L GT nm i kw (k + 4) val Qw (k + 4)) := by
  intro Hval Hrd HΨ
  unfold KLongEnd
  simp only [OOwn, ↓reduceIte]
  iintro %vlk %vcpu %vram %vs0m %vra %vs0 %vs1 %pr %Hp - ⟨-, Hf⟩ - - - - -
  have hL : (AxOpsem.grow (gtAdGd GT) i).length = k + 12 := Hp.1
  iapply (AxSpinT2h.wpdEnd1 L GT nm i (k + 12) (by omega) (i, k + 4) rfl _ Ψ
    (fun HF s => HΨ hL (fun vs Hv => (AxSpinT2h.ownGate L (gtAdGd GT) Hcons.1 i (k + 4) val
      (Hrd (by omega)) HF vs Hv).trans Hval) s) pr)
  iexact Hf

include Hcons in
/-- **`ppN`** (pop_off's `lw noff` at `k + 6`; the row ends at `k + 7 = cutPos .ppN q` before
`bge zero,a5,panic`): the reload annotation (`rlN` = push_off's `sw noff`, data `image + 1`)
refutes `noff < 1` (`noffPop`) — EXACTLY PO5/PO6's premise `KppN`. -/
theorem cutPpN (i : Agent) (k : Nat) (Pn : BitVec 64)
    (rlN : Option (Nat × List (BitVec 8) × WmClass)) (kw : Nat) (cls : WmClass) (w : BitVec 32)
    (Ψ : Athread → IProp GF) :
    rlN = some (kw, stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w))),
      cls) →
    w.toNat < 2 ^ 31 - 1 →
    (k + 6 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (k + 6) (paZ Pn) 4) →
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 7 →
      (∀ vs, graphValue (gtAdGd GT) (i, k + 6) = some vs →
        zopz0zKzJ_s zero_reg (ldRes false 4 vs) = false) →
      ∀ s, ⊢ Ψ s) →
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 7 →
      ∀ (vn : List (BitVec 8)) (pr : Pexv6), graphValue (gtAdGd GT) (i, k + 6) = some vn →
        ⊢ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, k + 7⟩ Ψ) := by
  intro HrlN Hw Hrd HΨ hL vn pr _
  subst HrlN
  simp only [AxSpinPO5.ann4O]
  exact AxSpinT2h.wpdEnd1 L GT nm i (k + 7) (by omega) (i, k + 6) rfl _ Ψ
    (fun HF s => HΨ hL (fun vs Hv => (AxSpinT2h.noffGate (gtAdGd GT) Hcons.1 i (k + 6) (paZ Pn) w
      (Hrd (by omega)) Hw HF vs Hv).2) s) pr

include Hcons in
/-- **`ppI`** (arm `c = false`: pop_off's `lw intena` at `k + 8`; the row ends at `k + 9 =
cutPos .ppI q` where `beqz` would fall into `intr_on` — the regime exit, not a panic): BOTH reload
annotations — the noff one gives image noff `w = 0` (`noffArmZero`, via the arm pin `Hvc`), so
push_off took `b = true` and stored intena 0 (`Hb`), and the intena one then reads 0
(`intenaGate`) — EXACTLY PO6's premise `KppI`. -/
theorem cutPpI (i : Agent) (k : Nat) (c : Bool) (Pn Pi : BitVec 64)
    (rlN rlI : Option (Nat × List (BitVec 8) × WmClass)) (kw : Nat) (cls : WmClass)
    (w : BitVec 32) (kwi : Nat) (clsi : WmClass) (Ψ : Athread → IProp GF) :
    rlN = some (kw, stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w))),
      cls) →
    w.toNat < 2 ^ 31 - 1 →
    (w = 0#32 → rlI = some (kwi, stBytes 4 0#64, clsi)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = c) →
    (k + 6 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (k + 6) (paZ Pn) 4) →
    (k + 8 < (AxOpsem.grow (gtAdGd GT) i).length →
      AxSpinT2h.RdAt (AxOpsem.grow (gtAdGd GT) i) (k + 8) (paZ Pi) 4) →
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 9 →
      (c = false → ∀ vs, graphValue (gtAdGd GT) (i, k + 8) = some vs →
        (ldRes false 4 vs == zero_reg) = true) →
      ∀ s, ⊢ Ψ s) →
    (c = false → (AxOpsem.grow (gtAdGd GT) i).length = k + 9 →
      ∀ (vn vi : List (BitVec 8)) (pr : Pexv6), graphValue (gtAdGd GT) (i, k + 6) = some vn →
        graphValue (gtAdGd GT) (i, k + 8) = some vi →
        ⊢ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
          AxSpinPO5.ann4O (GF := GF) GT i (paZ Pi) (k + 8) rlI -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, k + 9⟩ Ψ) := by
  intro HrlN Hw Hb Hvc Hrd6 Hrd8 HΨ hc hL vn vi pr Hgv6 _
  subst HrlN
  -- the noff readback forces the image noff to 0
  have Hw0 : AxSpinLd4P.rlFact4 GT i (paZ Pn) (k + 6)
      (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 (WeakInterpProj.wbytes 4 w)))) → w = 0#32 := by
    intro HF
    have Hn := (AxSpinT2h.noffGate (gtAdGd GT) Hcons.1 i (k + 6) (paZ Pn) w (Hrd6 (by omega)) Hw
      HF vn Hgv6).1
    have Hc := Hvc vn Hgv6
    rw [hc, Hn] at Hc
    exact (AxSpinT2g.noffArmZero w _ Hw rfl Hc).1
  cases rlI with
  | none =>
    simp only [AxSpinPO5.ann4O]
    iintro A -
    iapply (AxSpinT2h.wpdEnd1 L GT nm i (k + 9) (by omega) (i, k + 6) rfl _ Ψ
      (fun HF _ => nomatch Hb (Hw0 HF)) pr)
    iexact A
  | some x =>
    obtain ⟨kwi', vwi, clsi'⟩ := x
    simp only [AxSpinPO5.ann4O]
    exact AxSpinT2h.wpdEnd2P L GT nm i (k + 9) (by omega) (i, k + 6) (i, k + 8) rfl rfl
      (by intro h; have := congrArg Prod.snd h; simp at this) _ _ Ψ
      (fun HF HI s => by
        have Hs := Hb (Hw0 HF)
        simp only [Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨-, rfl, -⟩ := Hs
        exact HΨ hL (fun _ vs Hv => AxSpinT2h.intenaGate (gtAdGd GT) Hcons.1 i (k + 8) (paZ Pi)
          (Hrd8 (by omega)) HI vs Hv) s) pr

end arms

end Weak
