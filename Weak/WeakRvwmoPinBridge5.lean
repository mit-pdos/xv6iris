/-
Weak: **W9a (B) B5 PARTIAL — r3, the assembly, the B5 headlines, non-vacuity** (plan
`notes/weak-allocproc-plan.md` rev 52 §C "W9a (B)", "(B5) assembly" / "B5 partial"; rulings
[OWN.60], [OWN.68], [OWN.75]).  Lean-only, no Rocq twin.  Report: `PROGRESS-W9aB5.md`.

§1  **r3 — the pristine text at the graph** (FAITHFUL, no menu): `kTextUnwritten G` (B4's
    `Weak/WeakRvwmoPinBridge4.lean:428`) from the realization.  The graph half
    (`kTextUnwrittenOfLog`): a well-formed graph whose writes are ALL logged by a log `log`
    (`logOf G log`, the dictionary "log position `p` IS graph write index `p + 1`", and
    `(gwrites G).length ≤ log.length`) in which no message writes a text byte writes no text
    byte.  The machine half (`kTextUnwrittenOfRealized`): the log of a pf configuration `c`
    related by W4's `SimRel` to a MachCSL state reached from the machine off (`MRun`, generation
    0, power off, `fs.img`) writes no byte of `[bcRoLo, bcRoHi) ⊇ [textLo, textHi)` —
    `MachOfPf.noWriteOfPristine` at W3's sibling root `Xv6.xv6TextAdequacy_closed` (through
    `SrvwmoXv6Adequacy.winOfText`).  Composed with B4: `xv6ConfSZFetchTextOfRealized` (every
    row's emission fetches the tracked text bytes, `kFetchText`, under G6-2's `xv6ConfSZ`).
§2  **The named premises** (each its own Prop): r1 `fetchAnnR1`, r2 `fetchPaR2` (Q-B5-FETCH), FR
    `trapFrameRf` and W9b1-FRAME `w9b1Frame` (Q-TRAPRES (T3)) — and r4 `cycRun`, the CYCLE
    ALIGNMENT, NEW at B5 (Q-B5-CYCLE, the report's spec-first question): the plan's B5 list
    (r1/r2/r3/FR) does not cover how the real run's instructions line up with the walk (the cut
    of the emission at Sail's cycle boundaries, the run's next pc, the decode on the run's
    configuration, the absence of an exception at a walk instruction); `psitesA`'s dynamic
    content minus everything B1–B4 and the table prove is exactly `cycRun`'s per-cycle record
    `CycCert` (fetch arm, announced role, B1's slot scan FULL at that role) + "the next walk
    state is a `pstep` successor" + the excursions' run content `texcRes`.
§3  **The assembly** `reachesTOfCycRun` / `psitesTOfCycRun`: at a walk-certifying row of
    `pinsW9a`, `cycRun` (r1, r2, r4, FR) + `kFetchText` (r3 + B4) give B2's `reachesT` with real
    excursions `texcFree` — `grpOkb` from B4's arms (`FetchArm.annRoleText`: the announced role IS
    `krole pc`) and B1's `dfScanGrpOkb`; `taintSub`, the text bounds and the excursions'
    `presRegs` conjunct from the generated table (`Weak/PinWalkTab.lean`: `walkTaint`,
    `walkText`, `walkPres`).  At a pin state: a fed store (`pinStoreFed`) / a tainted branch
    (`pinCtrlTainted`), by the walk.
§4  **The B5 headlines** `pinSegPinStoreB5`, `pinSegPinCtrlB5`: PDep / PCtrl `segPinC` in the
    published quantifier (`forget GT`, `gtAd`) — `psitesA`/`psitesT` ABSENT; premises: the
    conformance and dependency clauses, the site row of `pinsW9a`, `kFetchText`, `cycRun`, the
    exit item's shape (as B2's `pinSegPinStoreFree`), the walk's pin at the end.
§5  **Non-vacuity, a STEP on real kernel bytes** (`printk`'s va-arg idiom, `0x800005d2`): the
    cycle's items, its `CycCert` with r1/r2, `cycRunStepReal`, through the assembly
    `psitesTReal` (a `reachesT` with an `rtStep`); the fall-through `reaches` with an `rcStep`
    (`nvReaches`, PinBridge2 §8 had only `rcStop`).
§6  **Non-vacuity, a REAL fence-free trap excursion** (`trapExcursionReal`): along B2's witness
    path (a) (117 states, `kernelvec` → `sret`) with the canonical items of each decoded role,
    `texcM FR` from `tStart` to `tEnd` for every `FR` containing the slot map's 29 spill → restore
    pairs (`trapExcPairs`, `trapExcPairsCount`), by the boolean checker `texcChk` and its
    soundness `texcChkSound`.

Spec: Sail (`Fetch.lean`, `Step.lean`, the decoder) is the reference for the arms and the
cycle; RVWMO/riscv.cat: rules 4, 5, 10–12 only (B1–B4's); Zifencei: G1's `gzFetch` (B4,
unchanged); PMAs silent.  r3 is FAITHFUL (a theorem); r1, r2, r4, FR are NAMED — WEAKER interim,
each a FAITHFUL proof obligation (Sail value walk / Sv39 identity / the Sail cycle decomposition /
Q-TRAPRES (T2)).  Every Lean-only helper is file-qualified `WeakRvwmoPinBridge5.*`.
-/
import Weak.WeakRvwmoPinBridge4
import Weak.SrvwmoXv6Adequacy
import Weak.PinWalkTab
import Weak.PinTrap
import Weak.PinDataflowGlue
import Weak.PinHoldingCtrl

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open CatLin
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinTrap

/-! # 1. r3 — `kTextUnwritten` from the realization -/

/-- The two message dictionaries agree (`WeakRvwmoKillArms.gmsg` is `WeakRvwmoLin.gmsg`
restated). -/
theorem WeakRvwmoPinBridge5.gmsgEq (G : Gexec) (w : Geid) :
    WeakRvwmoKillArms.gmsg G w = WeakRvwmoLin.gmsg G w := rfl

/-- **r3, the graph half**: a well-formed graph whose writes are all logged, in a log no message
of which writes a text byte, writes no text byte. -/
theorem kTextUnwrittenOfLog (G : Gexec) (log : List Wmsg) (hwf : gwf G) (hlog : logOf G log)
    (hlen : (gwrites G).length ≤ log.length)
    (hnw : ∀ a : Int, textLo ≤ a → a < textHi →
      ∀ i : Nat, log[i]?.bind (fun m => msgByte m a) = none) :
    kTextUnwritten G := by
  intro w a v h1 h2 hb
  have hw : w ∈ gwrites G := gwritesByteGwrites G w a v hwf hb
  obtain ⟨i, hi, -⟩ := gwixLookup G w hw
  have hil : i < log.length := Nat.lt_of_lt_of_le (lookup_lt_Some hi) hlen
  obtain ⟨m, hm⟩ : ∃ m, log[i]? = some m := ⟨_, List.getElem?_eq_getElem hil⟩
  obtain ⟨w', hw', hg⟩ := (hlog i m).1 hm
  have hww : w' = w := by
    have e : gwriteAt G (i + 1) = (gwrites G)[i]? := rfl
    rw [e, hi] at hw'
    exact (Option.some.inj hw').symm
  subst hww
  obtain ⟨m', hm', hb'⟩ := WeakRvwmoLin.gmsgByte G w' a v hb
  rw [WeakRvwmoPinBridge5.gmsgEq, hm'] at hg
  have hmm : m' = m := Option.some.inj hg
  subst hmm
  have := hnw a h1 h2 i
  rw [hm] at this
  simp only [Option.bind_some, hb'] at this
  cases this

/-- The tracked text lies in W3's pristine window: `[textLo, textHi) ⊆ [bcRoLo, bcRoHi)`. -/
theorem WeakRvwmoPinBridge5.textInWin :
    ((Xv6.bcRoLo : Nat) : Int) ≤ textLo ∧ textHi ≤ ((Xv6.bcRoHi : Nat) : Int) := by
  decide

/-- **r3, the machine half**: a pf configuration related by `SimRel` to a MachCSL state reached
from the machine off logs no write of a text byte (W3's sibling root, `noWriteOfPristine`). -/
theorem WeakRvwmoPinBridge5.logTextClean (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)}
    {t : List Expr} {g : GState} {n : Nat} {κ : List Obs}
    (hm : MachOfPf.MRun n ([Expr.power], g0) κ (t, g)) (hR : MachOfPf.SimRel c st t g) :
    ∀ a : Int, textLo ≤ a → a < textHi →
      ∀ i : Nat, c.pcLog[i]?.bind (fun m => msgByte m a) = none := by
  intro a h1 h2
  obtain ⟨hlo, hhi⟩ := WeakRvwmoPinBridge5.textInWin
  exact MachOfPf.noWriteOfPristine Xv6.bcRoLo Xv6.bcRoHi (Nat.le_refl _)
    SrvwmoXv6Adequacy.bcRoHiLe hR
    (SrvwmoXv6Adequacy.winOfText g0 hg0 hp0 hfs n κ t g hm hR.pow) a (by omega) (by omega)

/-- **r3 (header)**: `kTextUnwritten` at a graph whose writes are all logged by the log of a pf
configuration `SimRel`-related to a MachCSL state reached from the machine off — the
realization's interface (W11-F supplies `c`, `st`, `t`, `g` from the certified run, as it does
`readAt`). -/
theorem kTextUnwrittenOfRealized (G : Gexec) (hwf : gwf G) (g0 : GState) (hg0 : g0.gen = 0)
    (hp0 : g0.pow = false) (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) {c : Wpcfg Pexv6 Efab}
    {st : List (Nat × Wlabel)} {t : List Expr} {g : GState} {n : Nat} {κ : List Obs}
    (hm : MachOfPf.MRun n ([Expr.power], g0) κ (t, g)) (hR : MachOfPf.SimRel c st t g)
    (hlog : logOf G c.pcLog) (hlen : (gwrites G).length ≤ c.pcLog.length) :
    kTextUnwritten G :=
  kTextUnwrittenOfLog G c.pcLog hwf hlog hlen
    (WeakRvwmoPinBridge5.logTextClean g0 hg0 hp0 hfs hm hR)

/-- **r3 composed with B4**: under G6-2's Zifencei bundle, at a realized graph, every row's
emission fetches the tracked text bytes (`kFetchText`). -/
theorem xv6ConfSZFetchTextOfRealized (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat)
    (GT : GfexecT) (hwf : gwf GT.gfGd.gtG) (g0 : GState) (hg0 : g0.gen = 0)
    (hp0 : g0.pow = false) (hfs : diskOf g0.m.devs = Xv6.fsImgDisk) {c : Wpcfg Pexv6 Efab}
    {st : List (Nat × Wlabel)} {t : List Expr} {g : GState} {n : Nat} {κ : List Obs}
    (hm : MachOfPf.MRun n ([Expr.power], g0) κ (t, g)) (hR : MachOfPf.SimRel c st t g)
    (hlog : logOf GT.gfGd.gtG c.pcLog) (hlen : (gwrites GT.gfGd.gtG).length ≤ c.pcLog.length) :
    xv6ConfSZ boot d0 im nh GT → kTextImg im →
    ∀ (i : Nat) (row : List Lbl), GT.gfGd.gtG.gxProg[i]? = some row →
      ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
        hartConff i row (boot i) dvi dvo tq em ∧ kFetchText em :=
  fun hz hti => xv6ConfSZFetchText boot d0 im nh GT hz hti
    (kTextUnwrittenOfRealized _ hwf g0 hg0 hp0 hfs hm hR hlog hlen)

/-! # 2. The NAMED premises and the cycle alignment (r4)

`psitesA`/`psitesT`'s run content, cut into what B1–B4 and this item's table PROVE and what stays
NAMED.  A walk step of `reachesT` owes: (a) the instruction's group passes `grpOkb` at the pc,
(b) the next walk state is a `pstep` successor whose taint is below the decoded update, (c) at an
interrupt, a certified excursion.  PROVED here (§3): the role half of (a) — the cycle's announced
role IS `krole pc` (B4's arms + r3's `kFetchText`, given r1 and r2), and then B1's group test
(`PinDataflowGlue.dfScanGrpOkb`) from the cycle's slot scan; the taint half of (b)
(`walkTaint`); the census-decidable conjunct of (c) (`walkPres`).  NAMED (each its own Prop):
  * **r1** `fetchAnnR1` — Sail's `fetch ()` passes the i-cache read value to `instr_announce` in
    one of the four arm shapes (`Fetch.lean:233-288`, `Step.lean:335-404`; Q-B5-FETCH);
  * **r2** `fetchPaR2` — the fetch's physical address is the pc (`translateAddr` identity on
    kernel text, Sv39 after `kvminithart`; Q-B5-FETCH);
  * **FR** `trapFrameRf` — `texcM`'s frame relation: a fence-free excursion's restore READS FROM
    its slot's last spill (B2's `texcFree :1255`; Q-TRAPRES (T3));
  * **W9b1-FRAME** `w9b1Frame` — W9b-1's two `ld ra` restores (`mycpu`'s and `holding`'s) read
    their own `sd ra` spills, and `holding` is entered only by its three direct calls
    (`PinHoldingCtrl`; Q-TRAPRES) — the frame fact of the `holding+0x12` certificate, recorded
    here as its own Prop (that certificate is not over `pinsW9a`: B5 does not restate it);
  * **r4** `cycRun` (NEW at B5, not in the plan's list — the report's spec-first question
    Q-B5-CYCLE): the hart's emission, from the load's instruction on, is cut into Sail instruction
    CYCLES; each retired cycle at walk state `s` comes with a `CycCert` (its fetch arm, the
    announced role, and B1's slot scan of its items FULL at that role — the post `dfDone` of
    `dfInstrB5` carried along the cycle's execute stretch, `dfPevrun`), and the run's next pc is
    the walk state `s'` chosen among `pstep own s`'s successors; an interrupted cycle is a
    fence-free excursion `texcRes` (B2's `texcFree` without its census-decidable conjunct). -/

/-- **Sail's four fetch arms** (`LeanRV64D/Fetch.lean:233-288`): the i-cache read VALUES of one
cycle — a 4-byte read whose word is announced (`F_Base w`) or whose low half is (`F_RVC`), a
2-byte read announced compressed (`F_RVC ilo`), or two 2-byte reads announced as one word
(`F_Base (ihi ++ ilo)`). -/
inductive FetchArm where
  | base4 (w : BitVec 32)
  | rvc4 (w : BitVec 32)
  | rvc2 (ilo : BitVec 16)
  | base22 (ilo ihi : BitVec 16)

/-- The role of the bits each arm announces (`ibAnn (ibOfBvn …)`, `WeakEvInst.pnodeStep`'s
announce arm). -/
def FetchArm.annRole : FetchArm → OpRoles
  | .base4 w => depsOfIb (ibAnn (ibOfBvn w)).ibBits
  | .rvc4 w => depsOfIb (ibAnn (ibOfBvn (Sail.BitVec.extractLsb w 15 0))).ibBits
  | .rvc2 ilo => depsOfIb (ibAnn (ibOfBvn ilo)).ibBits
  | .base22 ilo ihi => depsOfIb (ibAnn (ibOfBvn (ihi ++ ilo))).ibBits

/-- An i-cache read of `k` bytes at `a` among a cycle's items `g`, returning `x` (the node clause
of `WeakEvInst.pnodeStep`'s fetch arm: the item's bytes are `x`'s). -/
def fetchItem (g : List Eitem) (a : Int) (k : Nat) (x : BitVec (8 * k)) : Prop :=
  ∃ tvs : List (Nat × BitVec 8), (Wlabel.LIFetch a tvs, none) ∈ g ∧
    tvs.length = k ∧ ∀ j : Nat, j < k → (tvs.map Prod.snd)[j]? = some (nthByte x j)

/-- The arm's reads among the cycle's items, at fetch address `a`. -/
def FetchArm.items (g : List Eitem) (a : Int) : FetchArm → Prop
  | .base4 w => fetchItem g a 4 w
  | .rvc4 w => fetchItem g a 4 w ∧ LeanRV64D.Functions.isRVC (Sail.BitVec.extractLsb w 15 0) = true
  | .rvc2 ilo => fetchItem g a 2 ilo ∧ LeanRV64D.Functions.isRVC ilo = true
  | .base22 ilo ihi => fetchItem g a 2 ilo ∧ fetchItem g (a + 2) 2 ihi

/-- A cycle's read is an emission item. -/
theorem WeakRvwmoPinBridge5.fetchItemEm (em : Hemission) (g : List Eitem) (a : Int) (k : Nat)
    (x : BitVec (8 * k)) (hsub : ∀ it, it ∈ g → it ∈ em.emItems) :
    fetchItem g a k x →
    ∃ (n : Nat) (tvs : List (Nat × BitVec 8)), em.emItems[n]? = some (Wlabel.LIFetch a tvs, none) ∧
      tvs.length = k ∧ ∀ j : Nat, j < k → (tvs.map Prod.snd)[j]? = some (nthByte x j) := by
  rintro ⟨tvs, hm, hl, hb⟩
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (hsub _ hm)
  exact ⟨n, tvs, hn, hl, hb⟩

/-- **B4 at a cycle**: an arm read at a text pc of a `kFetchText` emission announces `krole pc`'s
role (`annRoleFetch4`, `annRoleFetch2`). -/
theorem FetchArm.annRoleText (em : Hemission) (hft : kFetchText em) (g : List Eitem)
    (hsub : ∀ it, it ∈ g → it ∈ em.emItems) (pc : Int) (fa : FetchArm) :
    fa.items g pc → textLo ≤ pc → pc + 3 < textHi → fa.annRole = krole pc := by
  intro hit hlo hhi
  have hE := WeakRvwmoPinBridge5.fetchItemEm em g
  cases fa with
  | base4 w =>
    obtain ⟨n, tvs, hn, hl, hb⟩ := hE pc 4 w hsub hit
    exact ((annRoleFetch4 em hft n pc tvs w hn hl hb hlo).1 hhi).1
  | rvc4 w =>
    obtain ⟨n, tvs, hn, hl, hb⟩ := hE pc 4 w hsub hit.1
    exact (annRoleFetch4 em hft n pc tvs w hn hl hb hlo).2 (by omega) hit.2
  | rvc2 ilo =>
    obtain ⟨n, tvs, hn, hl, hb⟩ := hE pc 2 ilo hsub hit.1
    exact (annRoleFetch2 em hft n pc tvs ilo hn hl hb hlo (by omega)).1 hit.2
  | base22 ilo ihi =>
    obtain ⟨n, tvs, hn, hl, hb⟩ := hE pc 2 ilo hsub hit.1
    obtain ⟨n', tvs', hn', hl', hb'⟩ := hE (pc + 2) 2 ihi hsub hit.2
    exact ((annRoleFetch2 em hft n pc tvs ilo hn hl hb hlo (by omega)).2 n' tvs' ihi hn' hl' hb'
      hhi).2

/-- **THE CYCLE CERTIFICATE** of one retired instruction whose items are `g`: the fetch address,
the arm's read values, the role of the announced bits, the arm's reads in the emission, and B1's
slot scan of the cycle's labels FULL at that role (`dfDone`'s retired disjunct, carried by
`PinDataflowGlue.dfPevrun` along the cycle's execute stretch from `dfInstrB5`). -/
structure CycCert (g : List Eitem) where
  ccAddr : Int
  ccArm : FetchArm
  ccRole : OpRoles
  ccItems : ccArm.items g ccAddr
  ccScan : PinDataflow.dfScan ccRole (0, true) (g.map Prod.fst) =
    ((PinDataflow.dfDests ccRole).length, true)

/-- **r1 (NAMED, Q-B5-FETCH)**: the announced bits are the arm's — Sail's `fetch ()` passes the
i-cache read value to `instr_announce` (`F_Base w` / `F_RVC h`, `Step.lean:335-404`). -/
def fetchAnnR1 {g : List Eitem} (c : CycCert g) : Prop :=
  c.ccRole = c.ccArm.annRole

/-- **r2 (NAMED, Q-B5-FETCH)**: the fetch's physical address is the pc (`translateAddr
(Virtaddr PC)` the identity on kernel text, `Fetch.lean:217-232`). -/
def fetchPaR2 {g : List Eitem} (pc : Int) (c : CycCert g) : Prop :=
  c.ccAddr = pc

/-- **FR (NAMED, Q-TRAPRES (T3))**: `texcM`'s frame relation at the graph — the restore at row
position `k` READS FROM the spill at `w` (B2's `texcFree` instantiation, `PinTrap.lean:1255`). -/
def trapFrameRf (G : Gexec) (i : Nat) : Nat → Nat → Prop :=
  fun w k => WeakRvwmoAcyc.grf G (i, w) (i, k)

/-- **The fence-free excursion, run content** (B2's `texcFree` without its census-decidable
first conjunct, which the table proves at every walk state, `walkPres`): the trap entry's and the
`sret`'s neutral items around an alignment `texcM` with a fence-free census run from `kernelvec`'s
entry to its `sret`, WITH the frame relation FR. -/
def texcRes (G : Gexec) (i : Nat) (em : Hemission) (pfx gx : List Eitem) : Prop :=
  ∃ (gi gk gs rest : List Eitem) (S0 : Int → Option Nat),
    gx = gi ++ (gk ++ gs) ∧ em.emItems = pfx ++ gx ++ rest ∧
    gi.all provNeutralb = true ∧ gs.all provNeutralb = true ∧
    texcM (trapFrameRf G i) PinTrapSites.tStart S0 gk PinTrapSites.tEnd

/-- **W9b1-FRAME (NAMED, Q-TRAPRES)**: the `holding+0x12` certificate's frame fact, at the two
`ret`s of its alignment: the cycle after `mycpu`'s `ret` (`ld ra,8(sp)`) runs at `mycpu`'s call's
return point in `holding` (`holding+0x1a`), and the cycle after `holding`'s own `ret`
(`ld ra,24(sp)`, `holdingRetPc`) runs at the return point `aRet` of one of `holding`'s three
direct calls (`PinHoldingCtrl.holdingCallSites`) — each `ld ra` reads its own `sd ra` spill
(own-stack rfi) and `holding` is entered only by a direct call.  `aMy`/`aRet` are the pcs the
hart's run resumes at; `PinHoldingCtrl.holdingCtrlSegPinC` consumes the second conjunct as its
premise `(a, b) ∈ holdingCallSites` (that certificate is not over `pinsW9a`; B5 does not restate
it). -/
def w9b1Frame (aMy aRet : Int) : Prop :=
  aMy = (KernelSyms.«holding» : Int) + 0x1a ∧ ∃ b, (aRet, b) ∈ holdingCallSites

/-- **r4 — THE CYCLE ALIGNMENT (NAMED, NEW: Q-B5-CYCLE)** (header): hart `i`'s emission items
`g` after the prefix `pfx`, from walk state `s` to `s''`, cut into retired cycles (each with its
`CycCert` and r1/r2, the next walk state a `pstep` successor) and fence-free trap excursions
(`texcRes`, with FR).  No `grpOkb`, no `taintSub`, no `presRegs`: those are PROVED (§3). -/
inductive cycRun (G : Gexec) (i : Nat) (em : Hemission) (own : Bool) :
    List Eitem → PState → List Eitem → PState → Prop where
  | stop (pfx : List Eitem) (s : PState) : cycRun G i em own pfx s [] s
  | step (pfx : List Eitem) (s : PState) (g : List Eitem) (l : List PState) (s' : PState)
      (mid : List Eitem) (s'' : PState) (c : CycCert g) :
      fetchAnnR1 c → fetchPaR2 s.psPc c →
      pstep own s = some l → s' ∈ l →
      cycRun G i em own (pfx ++ g) s' mid s'' →
      cycRun G i em own pfx s (g ++ mid) s''
  | trap (pfx : List Eitem) (s : PState) (gx mid : List Eitem) (s'' : PState) :
      texcRes G i em pfx gx → cycRun G i em own (pfx ++ gx) s mid s'' →
      cycRun G i em own pfx s (gx ++ mid) s''

/-! # 3. THE ASSEMBLY: r1, r2, r3, r4, FR and the table give `psitesT` -/

/-- Reachability extends by one successor at the END. -/
theorem WeakRvwmoPinBridge5.preachSnoc (own : Bool) (a s s' : PState) (l : List PState) :
    ∀ n, preach own a s n → pstep own s = some l → s' ∈ l → preach own a s' (n + 1) := by
  intro n h
  induction h with
  | prRefl x =>
    intro hp hm
    exact .prStep x s' s' l 0 hp hm (.prRefl s')
  | prStep x y z l' n hp hm _ ih =>
    intro hp' hm'
    exact .prStep x y s' l' (n + 1) hp hm (ih hp' hm')

/-- **THE ASSEMBLY (header)**: at a claimed walk-certifying site of `pinsW9a`, a cycle alignment
(r4, with r1, r2 and FR) of a `kFetchText` emission (r3 + B4) from a walk state the site's walk
reaches IS `reachesT` with B2's real excursions `texcFree` — `grpOkb` by B4 + B1, `taintSub`
and the excursions' `presRegs` conjunct by the generated table. -/
theorem reachesTOfCycRun (G : Gexec) (i : Nat) (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (hm : (pcL, w) ∈ pinsW9a) (hw : walkOwn w = some own) (hft : kFetchText em) :
    ∀ (pfx : List Eitem) (s : PState) (g : List Eitem) (s'' : PState) (n : Nat),
      preach own (pinStart pcL) s n → (∃ rest, em.emItems = pfx ++ g ++ rest) →
      cycRun G i em own pfx s g s'' →
      reachesT (texcFree G i em) own pfx s g s'' := by
  intro pfx s g s'' n hreach hpre hrun
  induction hrun generalizing n with
  | stop pfx s => exact .rtStop pfx s
  | step pfx s g l s' mid s'' c h1 h2 hp hmem _ ih =>
    obtain ⟨rest, hes⟩ := hpre
    have hne : l ≠ [] := by rintro rfl; cases hmem
    obtain ⟨hlo, hhi⟩ := walkText pcL w own s n l hm hw hreach hp hne
    have hsub : ∀ it, it ∈ g → it ∈ em.emItems := by
      intro it hit
      rw [hes]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hit))
    have hrole : c.ccRole = krole s.psPc := by
      rw [h1]
      have hit := c.ccItems
      rw [h2] at hit
      exact FetchArm.annRoleText em hft g hsub s.psPc c.ccArm hit hlo hhi
    have hscan := c.ccScan
    rw [hrole] at hscan
    obtain ⟨g1, g2, rfl, hg⟩ := PinDataflow.dfScanGrpOkb s.psPc g hscan
    have hsub := walkTaint pcL w own s n l s' hm hw hreach hp hmem
    have := ih (n + 1) (WeakRvwmoPinBridge5.preachSnoc own _ s s' l n hreach hp hmem)
      ⟨rest, by rw [hes]; simp only [List.append_assoc]⟩
    rw [List.append_assoc]
    exact .rtStep pfx s g1 g2 l s' mid s'' hg hp hmem hsub this
  | trap pfx s gx mid s'' hx _ ih =>
    obtain ⟨rest, hes⟩ := hpre
    refine .rtTrap pfx s gx mid s'' ?_ (ih n hreach ⟨rest, by rw [hes]; simp only [List.append_assoc]⟩)
    exact ⟨walkPres pcL w own s n hm hw hreach, hx⟩

/-- **`psitesT` FROM THE NAMED PREMISES (header)**: a cycle alignment from the site's walk start
discharges B2's site oracle. -/
theorem psitesTOfCycRun (G : Gexec) (i : Nat) (em : Hemission) (pcL : Int) (w : Pin) (own : Bool)
    (base mid : List Eitem) (s : PState) :
    (pcL, w) ∈ pinsW9a → walkOwn w = some own → kFetchText em →
    (∃ rest, em.emItems = base ++ mid ++ rest) →
    cycRun G i em own base (pinStart pcL) mid s →
    psitesT (texcFree G i em) pcL own base (base ++ mid) s := by
  intro hm hw hft hpre hrun
  exact ⟨mid, rfl,
    reachesTOfCycRun G i em pcL w own hm hw hft base _ mid s 0 (.prRefl _) hpre hrun⟩

/-- A cycle alignment from the site's walk start ends at a state the walk reaches. -/
theorem WeakRvwmoPinBridge5.cycRunReach (G : Gexec) (i : Nat) (em : Hemission) (own : Bool) :
    ∀ (pfx : List Eitem) (s : PState) (g : List Eitem) (s'' : PState) (a : PState) (n : Nat),
      preach own a s n → cycRun G i em own pfx s g s'' → ∃ m, preach own a s'' m := by
  intro pfx s g s'' a n hr hrun
  induction hrun generalizing n with
  | stop => exact ⟨n, hr⟩
  | step pfx s g l s' mid s'' c _ _ hp hmem _ ih =>
    exact ih (n + 1) (WeakRvwmoPinBridge5.preachSnoc own a s s' l n hr hp hmem)
  | trap pfx s gx mid s'' _ _ ih => exact ih n hr

/-- At a PIN state the walk reaches, a store that is no fence is FED by the taint. -/
theorem WeakRvwmoPinBridge5.pinStoreFed (own : Bool) (s : PState) :
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = true →
    (srcsTainted s.psT (depsAddr (krole s.psPc))
      || srcsTainted s.psT (depsVsrc (krole s.psPc))) = true := by
  obtain ⟨pc, t, rs⟩ := s
  dsimp only
  intro h hf hst
  cases hb : (srcsTainted t (depsAddr (krole pc)) || srcsTainted t (depsVsrc (krole pc)))
  · exfalso
    unfold pstep at h
    simp only [hf, hst, hb, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h <;> simp_all
  · rfl

/-- At a PIN state the walk reaches, a conditional branch that is no store or fence tests the
taint. -/
theorem WeakRvwmoPinBridge5.pinCtrlTainted (own : Bool) (s : PState) (tgt : Int) :
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = false →
    kflowOf s.psPc = .FLbranch tgt → srcsTainted s.psT (depsCtrl (krole s.psPc)) = true := by
  obtain ⟨pc, t, rs⟩ := s
  dsimp only
  intro h hf hst hk
  cases hb : srcsTainted t (depsCtrl (krole pc))
  · exfalso
    unfold pstep at h
    simp only [hf, hst, hk, hb, Bool.false_eq_true, ↓reduceIte] at h
    split at h <;> simp_all
  · rfl

/-! # 4. THE B5 HEADLINES — `psitesA`/`psitesT` absent -/

/-- **PDep, B5 (header)**: at a walk-certifying site `(pcL, w)` of the claimed pin set
`pinsW9a`, for hart `i`'s conformant emission, a segment entering at the load (row position `j`)
and exiting at the FIRST pin's store (row position `k`, the walk's pin state `s` a fed store) is
`segPinC` in the published quantifier (`forget GT`, `ad := gtAd`) — from r3's `kFetchText` and
the cycle alignment r4 (with r1, r2, FR): no `psitesA`, no `psitesT`. -/
theorem pinSegPinStoreB5 (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (sg : Seg) (pcL : Int) (w : Pin) (j k : Nat) (own : Bool)
    (base mid g0 post : List Eitem) (s : PState) (rl : Bool) (a : Int) (v : List (BitVec 8))
    (asrc vsrc : List Dsrc) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    (pcL, w) ∈ pinsW9a → walkOwn w = some own →
    kFetchText em →
    cycRun GT.gtG i em own base (pinStart pcL) mid s →
    em.emItems = base ++ mid ++ g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post →
    g0.all provNeutralb = true →
    dsubb (depsAddr (krole s.psPc)) asrc = true → dsubb (depsVsrc (krole s.psPc)) vsrc = true →
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = true →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hm hw hft hrun hes hg0 hca hcv hpin hf hst
  exact pinSegPinStoreFree GT i row p0 dv em sg pcL j k own base (base ++ mid) g0 post s rl a v
    asrc vsrc hrow hcf hdeps he hx hbase hes
    (psitesTOfCycRun GT.gtG i em pcL w own base mid s hm hw hft
      ⟨g0 ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post,
        by rw [hes]; simp only [List.append_assoc]⟩ hrun) hg0 hca hcv
    (WeakRvwmoPinBridge5.pinStoreFed own s hpin hf hst)

/-- **PCtrl, B5 (header)**: a segment entering at the load and exiting at a store po-after the
FIRST pin's branch (the walk's pin state `s` a conditional branch, its control item `LCtrl srcs`
covering the decoded list) is `segPinC` — no `psitesA`, no `psitesT`. -/
theorem pinSegPinCtrlB5 (GT : GdexecT) (i : Nat) (row : List Lbl) (p0 : Pexv6)
    (dv : Nat → Efab) (em : Hemission) (sg : Seg) (pcL : Int) (w : Pin) (j k : Nat) (own : Bool)
    (base mid g0 mid' post : List Eitem) (s : PState) (srcs : List Dsrc) (kc : Option Nat)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) (tgt : Int) :
    GT.gtG.gxProg[i]? = some row → hartConf i row p0 dv em →
    (∀ x, x ∈ rowDepsT em.emItems → (((i, x.1.1), (i, x.1.2)), x.2) ∈ GT.gtDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 pcL) →
    (pcL, w) ∈ pinsW9a → walkOwn w = some own →
    kFetchText em →
    cycRun GT.gtG i em own base (pinStart pcL) mid s →
    em.emItems = base ++ mid ++ g0 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid' ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    g0.all provNeutralb = true →
    dsubb (depsCtrl (krole s.psPc)) srcs = true →
    pstep own s = some [] → wIsFence (kw s.psPc) = false → roleIsStore (krole s.psPc) = false →
    kflowOf s.psPc = .FLbranch tgt →
    segPinC (forget GT) (gtAd GT.gtG GT.gtDeps) sg := by
  intro hrow hcf hdeps he hx hbase hm hw hft hrun hes hg0 hcov hpin hf hst hk
  exact pinSegPinCtrlFree GT i row p0 dv em sg pcL j k own base (base ++ mid) g0 mid' post s srcs
    kc rl a v asrc vsrc hrow hcf hdeps he hx hbase hes
    (psitesTOfCycRun GT.gtG i em pcL w own base mid s hm hw hft
      ⟨g0 ++ (Wlabel.LCtrl srcs, kc) :: (mid' ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post),
        by rw [hes]; simp only [List.append_assoc]⟩ hrun) hg0 hcov
    (WeakRvwmoPinBridge5.pinCtrlTainted own s tgt hpin hf hst hk)


/-! # 5. Non-vacuity: the alignment with a STEP on real kernel bytes

The row `printk`'s va-arg idiom at `0x800005d2` (`ld a5,-120(s0)`, `PDep` at `0x800005da`,
`sd a4,-120(s0)`): its walk is `0x800005d6` (`addi a4,a5,8`, a 4-byte word at a 2-aligned pc —
Sail's `F_Base (ihi ++ ilo)` arm, two halfword reads) then the pin.  An emission whose items are
that instruction's cycle — the two i-cache reads of the image bytes, the announce, the `LRegW 14`
the role names — carries a `CycCert` with r1 and r2; the cycle alignment `cycRun` has a STEP;
through the assembly it is a `reachesT` with an `rtStep` (PinBridge2 §8 had only `rcStop`), and
`psitesT` holds at the pin state.  The fall-through alignment `reaches` gets its `rcStep` on the
same bytes (`nvReachesStep`). -/

/-- The site. -/
def WeakRvwmoPinBridge5.nvLd : Int := 0x800005d2
/-- The instruction after it (`addi a4,a5,8`) and the pin (`sd a4,-120(s0)`). -/
def WeakRvwmoPinBridge5.nvPc : Int := 0x800005d6
def WeakRvwmoPinBridge5.nvPin : Int := 0x800005da

open WeakRvwmoPinBridge5 (nvLd nvPc nvPin)

theorem WeakRvwmoPinBridge5.nvRow : (nvLd, Pin.PDep nvPin false) ∈ pinsW9a := by decide +kernel

/-- The image's halfwords of the word at `nvPc`. -/
def WeakRvwmoPinBridge5.nvLo : BitVec 16 := BitVec.ofNat 16 (kw nvPc % 65536)
def WeakRvwmoPinBridge5.nvHi : BitVec 16 := BitVec.ofNat 16 (kw nvPc / 65536 % 65536)

open WeakRvwmoPinBridge5 (nvLo nvHi)

/-- An i-cache read of two image bytes at `a`. -/
def WeakRvwmoPinBridge5.nvTvs (a : Int) : List (Nat × BitVec 8) :=
  [(0, BitVec.ofNat 8 (kbyte a)), (0, BitVec.ofNat 8 (kbyte (a + 1)))]

open WeakRvwmoPinBridge5 (nvTvs)

/-- THE CYCLE'S ITEMS: the two reads, the announce, the destination write of `a4` from `a5`. -/
def WeakRvwmoPinBridge5.nvG : List Eitem :=
  [(Wlabel.LIFetch nvPc (nvTvs nvPc), none), (Wlabel.LIFetch (nvPc + 2) (nvTvs (nvPc + 2)), none),
   (Wlabel.LInstr, none), (Wlabel.LRegW 14 [.DReg 15], none)]

open WeakRvwmoPinBridge5 (nvG)

def WeakRvwmoPinBridge5.nvEm : Hemission := ⟨nvG, .PDisk none⟩

open WeakRvwmoPinBridge5 (nvEm)

theorem WeakRvwmoPinBridge5.nvItems :
    (FetchArm.base22 nvLo nvHi).items nvG nvPc :=
  ⟨⟨nvTvs nvPc, List.mem_cons_self .., rfl, by decide +kernel⟩,
   ⟨nvTvs (nvPc + 2), List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, by decide +kernel⟩⟩

theorem WeakRvwmoPinBridge5.nvScan :
    PinDataflow.dfScan (FetchArm.base22 nvLo nvHi).annRole (0, true) (nvG.map Prod.fst) =
      ((PinDataflow.dfDests (FetchArm.base22 nvLo nvHi).annRole).length, true) := by
  decide +kernel

/-- The cycle's certificate. -/
def WeakRvwmoPinBridge5.nvCert : CycCert nvG :=
  ⟨nvPc, .base22 nvLo nvHi, (FetchArm.base22 nvLo nvHi).annRole,
    WeakRvwmoPinBridge5.nvItems, WeakRvwmoPinBridge5.nvScan⟩

/-- The walk's step and its successor. -/
def WeakRvwmoPinBridge5.nvS1 : PState := PState.PSt nvPin (taintStep (pinT0 nvLd) nvPc) []

/-- Decided equality of walk successor lists. -/
def WeakRvwmoPinBridge5.succEqb : Option (List PState) → Option (List PState) → Bool
  | none, none => true
  | some a, some b => a.length == b.length && (a.zip b).all (fun p => pstateEqb p.1 p.2)
  | _, _ => false

theorem WeakRvwmoPinBridge5.succEqbEq (a b : Option (List PState)) :
    WeakRvwmoPinBridge5.succEqb a b = true → a = b := by
  cases a with
  | none => cases b with
    | none => intro _; rfl
    | some _ => intro h; cases h
  | some a => cases b with
    | none => intro h; cases h
    | some b =>
      intro h
      simp only [WeakRvwmoPinBridge5.succEqb, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hl, hz⟩ := h
      congr 1
      induction a generalizing b with
      | nil => cases b with
        | nil => rfl
        | cons _ _ => cases hl
      | cons x a ih => cases b with
        | nil => cases hl
        | cons y b =>
          simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hz
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ hz.1, ih b hl hz.2]

theorem WeakRvwmoPinBridge5.nvStep :
    pstep false (pinStart nvLd) = some [WeakRvwmoPinBridge5.nvS1] :=
  WeakRvwmoPinBridge5.succEqbEq _ _ (by decide +kernel)

theorem WeakRvwmoPinBridge5.nvPinState : pstep false WeakRvwmoPinBridge5.nvS1 = some [] :=
  WeakRvwmoPinBridge5.succEqbEq _ _ (by decide +kernel)

/-- **THE CYCLE ALIGNMENT HAS A STEP on real bytes** (with r1 and r2), at any graph. -/
theorem cycRunStepReal (G : Gexec) (i : Nat) (pfx : List Eitem) :
    cycRun G i nvEm false pfx (pinStart nvLd) (nvG ++ []) WeakRvwmoPinBridge5.nvS1 :=
  .step pfx _ nvG _ _ [] _ WeakRvwmoPinBridge5.nvCert rfl
    (by unfold fetchPaR2; decide +kernel)
    WeakRvwmoPinBridge5.nvStep (List.mem_singleton_self _) (.stop _ _)

/-- A list-level form of `kFetchText`. -/
theorem WeakRvwmoPinBridge5.kFetchTextOfAll (em : Hemission)
    (h : ∀ it, it ∈ em.emItems → ∀ (base : Int) (tvs : List (Nat × BitVec 8)),
      it = (Wlabel.LIFetch base tvs, none) →
      ∀ j : Nat, j < tvs.length → textLo ≤ base + (j : Int) → base + (j : Int) < textHi →
        (tvs.map Prod.snd)[j]? = some (BitVec.ofNat 8 (kbyte (base + (j : Int))))) :
    kFetchText em :=
  fun n base tvs hn => h _ (List.mem_of_getElem? hn) base tvs rfl

theorem WeakRvwmoPinBridge5.nvFetchText : kFetchText nvEm := by
  apply WeakRvwmoPinBridge5.kFetchTextOfAll
  intro it hit base tvs he j hj _ _
  simp only [nvEm, nvG, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl
  · simp only [Prod.mk.injEq, Wlabel.LIFetch.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, -⟩ := he
    simp only [nvTvs, List.length_cons, List.length_nil] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [nvTvs]
  · simp only [Prod.mk.injEq, Wlabel.LIFetch.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, -⟩ := he
    simp only [nvTvs, List.length_cons, List.length_nil] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [nvTvs, Int.add_assoc]
  · cases he
  · cases he

/-- **THROUGH THE ASSEMBLY: `reachesT` with an `rtStep`, and `psitesT` at the pin**. -/
theorem psitesTReal (G : Gexec) (i : Nat) :
    psitesT (texcFree G i nvEm) nvLd false [] ([] ++ (nvG ++ [])) WeakRvwmoPinBridge5.nvS1 :=
  psitesTOfCycRun G i nvEm nvLd (Pin.PDep nvPin false) false [] _ _ WeakRvwmoPinBridge5.nvRow
    rfl WeakRvwmoPinBridge5.nvFetchText ⟨[], by simp [nvEm]⟩ (cycRunStepReal G i [])

/-- The fall-through alignment's `rcStep` on the same bytes (`reaches`, PinBridge2). -/
theorem nvReachesStep (g1 g2 : List Eitem) :
    nvG = g1 ++ g2 → grpOkb nvPc g1 g2 = true →
    reaches false nvPin (pinStart nvLd) (g1 ++ (g2 ++ [])) WeakRvwmoPinBridge5.nvS1 := by
  intro _ hg
  refine .rcStep _ g1 g2 WeakRvwmoPinBridge5.nvS1 [] _ (by decide +kernel) hg ?_ ?_
    (.rcStop _ (by decide +kernel))
  · unfold WeakRvwmoPinBridge2.wstep; rw [WeakRvwmoPinBridge5.nvStep]
  · exact taintSubRefl _

/-- ... and its group test holds on the cycle's items (the split at the destination write). -/
theorem nvGrpOk : grpOkb nvPc nvG [] = true := by decide +kernel

/-- **THE `rcStep` ON REAL BYTES** (PinBridge2 §8 had only `rcStop`). -/
theorem nvReaches :
    reaches false nvPin (pinStart nvLd) (nvG ++ ([] ++ [])) WeakRvwmoPinBridge5.nvS1 :=
  nvReachesStep nvG [] (List.append_nil _).symm nvGrpOk


/-! # 6. Non-vacuity: a REAL fence-free trap excursion

B2's census witness path (a) (`PinTrapSites.trapWitnessTail`: `kernelvec` → `kerneltrap` →
`devintr` → `plic_claim` → irq 0 → back → `sret`, the spurious PLIC claim) with, at each of its
instructions, the CANONICAL items of the decoded role (`canonItems`: one `LRegW` per decoded
destination with the decoded sources; at a spill its store item, at a restore its load item
first): `texcM FR` holds from `tStart` to `tEnd` for EVERY frame relation `FR` containing the
spill → restore pairs the slot map produces (`trapExcPairs`) — the alignment B2-free consumes is
inhabited on real kernel bytes, and the frame fact it names is exactly those pairs.  Decided by a
boolean checker (`texcChk`) with a once-proven soundness (`texcChkSound`). -/

/-- One destination write per decoded destination, with the decoded sources. -/
def WeakRvwmoPinBridge5.regws (d : Option (Nat × List Dsrc)) : List Eitem :=
  match d with
  | some (rd, dec) => [(Wlabel.LRegW rd dec, none)]
  | none => []

open WeakRvwmoPinBridge5 (regws)

/-- THE CANONICAL ITEMS of the instruction at `pc` (row position `k` for its memory item). -/
def canonItems (pc : Int) (k : Nat) : List Eitem × List Eitem :=
  match PinTrapSites.spSt pc with
  | some _ =>
      ([(Wlabel.LStore false 0 [] (depsAddr (krole pc)) (depsVsrc (krole pc)), some k)], [])
  | none =>
      match PinTrapSites.spLd pc with
      | some _ => ((Wlabel.LLoad false false 0 [] [], some k) :: regws (depsRd (krole pc)),
          regws (depsRd2 (krole pc)))
      | none => (regws (depsRd (krole pc)), regws (depsRd2 (krole pc)))

/-- The steps along a census path: `(next state, g1, g2)` for the instruction at the current
state. -/
def excSteps : PinTrapSites.TSt → List PinTrapSites.TSt → Nat →
    List (PinTrapSites.TSt × List Eitem × List Eitem)
  | _, [], _ => []
  | s, s' :: rest, k => (s', canonItems s.tPc k) :: excSteps s' rest (k + 1)

def WeakRvwmoPinBridge5.itemsOf : List (PinTrapSites.TSt × List Eitem × List Eitem) → List Eitem
  | [] => []
  | (_, g1, g2) :: rest => g1 ++ (g2 ++ WeakRvwmoPinBridge5.itemsOf rest)

open WeakRvwmoPinBridge5 (itemsOf)

/-- The slot map as a list (newest first). -/
def WeakRvwmoPinBridge5.lookS (S : List (Int × Nat)) (o : Int) : Option Nat :=
  (S.find? (fun p => p.1 == o)).map (·.2)

open WeakRvwmoPinBridge5 (lookS)

/-- The first store item of a list whose data sources cover `dec`: its row position. -/
def WeakRvwmoPinBridge5.findStore (dec : List Dsrc) : List Eitem → Option Nat
  | [] => none
  | (Wlabel.LStore _ _ _ _ vsrc, some w) :: rest =>
      if dsubb dec vsrc then some w else WeakRvwmoPinBridge5.findStore dec rest
  | _ :: rest => WeakRvwmoPinBridge5.findStore dec rest

open WeakRvwmoPinBridge5 (findStore)

/-- A list headed by a load item: its row position and the rest. -/
def WeakRvwmoPinBridge5.ldHead : List Eitem → Option (Nat × List Eitem)
  | (Wlabel.LLoad _ _ _ _ _, some k) :: gb => some (k, gb)
  | _ => none

open WeakRvwmoPinBridge5 (ldHead)

/-- `memOk`, decided against a pair list for `FR`: the new slot map. -/
def WeakRvwmoPinBridge5.memChk (prs : List (Nat × Nat)) (s : PinTrapSites.TSt)
    (S : List (Int × Nat)) (g1 g2 : List Eitem) : Option (List (Int × Nat)) :=
  match PinTrapSites.spSt s.tPc with
  | some o => (findStore (depsVsrc (krole s.tPc)) (g1 ++ g2)).map (fun w => (spAt s + o, w) :: S)
  | none =>
      match PinTrapSites.spLd s.tPc with
      | some o =>
          match ldHead g1 with
          | some (k, gb) =>
              if gb.all notInstrb &&
                  (match lookS S (spAt s + o) with
                   | some w => prs.contains (w, k)
                   | none => true)
              then some S else none
          | none => none
      | none => some S

open WeakRvwmoPinBridge5 (memChk)

/-- `texcM`, decided. -/
def texcChk (prs : List (Nat × Nat)) :
    PinTrapSites.TSt → List (Int × Nat) → List (PinTrapSites.TSt × List Eitem × List Eitem) →
      PinTrapSites.TSt → Bool
  | s, _, [], e => s == e
  | s, S, (s', g1, g2) :: rest, e =>
      grpOkb s.tPc g1 g2 && PinTrapSites.tmoveb s s' &&
        match memChk prs s S g1 g2 with
        | some S' => texcChk prs s' S' rest e
        | none => false

/-- The spill → restore pairs a census run's slot map produces. -/
def excPairs : PinTrapSites.TSt → List (Int × Nat) →
    List (PinTrapSites.TSt × List Eitem × List Eitem) → List (Nat × Nat)
  | _, _, [] => []
  | s, S, (s', g1, g2) :: rest =>
      let here : List (Nat × Nat) :=
        match PinTrapSites.spSt s.tPc, PinTrapSites.spLd s.tPc, ldHead g1 with
        | none, some o, some (k, _) =>
            match lookS S (spAt s + o) with
            | some w => [(w, k)]
            | none => []
        | _, _, _ => []
      let S' := (memChk [] s S g1 g2).getD S
      let S'' := match PinTrapSites.spSt s.tPc with
        | some _ => S'
        | none => S
      here ++ excPairs s' S'' rest

theorem WeakRvwmoPinBridge5.findStoreSound (dec : List Dsrc) (g : List Eitem) (w : Nat) :
    findStore dec g = some w →
    ∃ (ga gb : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc),
      g = ga ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: gb ∧ dsubb dec vsrc = true := by
  induction g with
  | nil => intro h; cases h
  | cons it g ih =>
    intro h
    obtain ⟨l, k⟩ := it
    have hrest : findStore dec g = some w →
        ∃ (ga gb : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc),
          (l, k) :: g = ga ++ (Wlabel.LStore rl a v asrc vsrc, some w) :: gb ∧
            dsubb dec vsrc = true := by
      intro h'
      obtain ⟨ga, gb, rl, a, v, asrc, vsrc, rfl, hd⟩ := ih h'
      exact ⟨(l, k) :: ga, gb, rl, a, v, asrc, vsrc, rfl, hd⟩
    cases l
    case LStore rl a v asrc vsrc =>
      cases k with
      | none => exact hrest h
      | some k =>
        simp only [findStore] at h
        split at h
        · rename_i hd
          cases h
          exact ⟨[], g, rl, a, v, asrc, vsrc, rfl, hd⟩
        · exact hrest h
    all_goals exact hrest h

theorem WeakRvwmoPinBridge5.ldHeadSound (g : List Eitem) (k : Nat) (gb : List Eitem) :
    ldHead g = some (k, gb) →
    ∃ (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc),
      g = (Wlabel.LLoad aq lat base tvs asrc, some k) :: gb := by
  intro h
  match g, h with
  | (Wlabel.LLoad aq lat base tvs asrc, some k') :: gb', h =>
    simp only [ldHead, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨aq, lat, base, tvs, asrc, rfl⟩

theorem WeakRvwmoPinBridge5.lookSCons (S : List (Int × Nat)) (x : Int) (w : Nat) :
    lookS ((x, w) :: S) = slotSet (lookS S) x w := by
  funext o
  unfold lookS slotSet
  by_cases h : o = x
  · subst h; simp
  · have h' : (x == o) = false := by simp only [beq_eq_false_iff_ne]; exact fun e => h e.symm
    simp [h', h]

theorem WeakRvwmoPinBridge5.memChkLd (prs : List (Nat × Nat)) (s : PinTrapSites.TSt)
    (S : List (Int × Nat)) (g1 g2 : List Eitem) (o : Int) (S' : List (Int × Nat))
    (hst : PinTrapSites.spSt s.tPc = none) (hld : PinTrapSites.spLd s.tPc = some o)
    (hm : memChk prs s S g1 g2 = some S') :
    S' = S ∧ ∃ k gb, ldHead g1 = some (k, gb) ∧ gb.all notInstrb = true ∧
      ∀ w, lookS S (spAt s + o) = some w → (w, k) ∈ prs := by
  unfold memChk at hm
  rw [hst, hld] at hm
  rcases hh : ldHead g1 with _ | ⟨k, gb⟩
  · simp only [hh] at hm; cases hm
  · simp only [hh] at hm
    rcases hl : lookS S (spAt s + o) with _ | w
    · simp only [hl] at hm
      by_cases hgb : gb.all notInstrb = true
      · simp only [hgb, Bool.and_true, ite_true, Option.some.injEq] at hm
        exact ⟨hm.symm, k, gb, rfl, hgb, fun w hw => by cases hw⟩
      · simp [hgb] at hm
    · simp only [hl] at hm
      by_cases hc : (gb.all notInstrb && prs.contains (w, k)) = true
      · rw [if_pos hc] at hm
        simp only [Option.some.injEq] at hm
        simp only [Bool.and_eq_true] at hc
        refine ⟨hm.symm, k, gb, rfl, hc.1, fun w' hw' => ?_⟩
        simp only [Option.some.injEq] at hw'
        subst hw'
        exact List.contains_iff_mem.mp hc.2
      · rw [if_neg hc] at hm; cases hm

/-- **THE CHECKER IS SOUND** (header). -/
theorem texcChkSound (FR : Nat → Nat → Prop) (prs : List (Nat × Nat))
    (hFR : ∀ p, p ∈ prs → FR p.1 p.2) :
    ∀ (steps : List (PinTrapSites.TSt × List Eitem × List Eitem)) (s : PinTrapSites.TSt)
      (S : List (Int × Nat)) (e : PinTrapSites.TSt),
      texcChk prs s S steps e = true → texcM FR s (lookS S) (itemsOf steps) e := by
  intro steps
  induction steps with
  | nil =>
    intro s S e h
    simp only [texcChk, beq_iff_eq] at h
    subst h
    exact .stop _ _
  | cons st rest ih =>
    obtain ⟨s', g1, g2⟩ := st
    intro s S e h
    simp only [texcChk, Bool.and_eq_true] at h
    obtain ⟨⟨hg, ht⟩, h⟩ := h
    cases hm : memChk prs s S g1 g2 with
    | none => rw [hm] at h; cases h
    | some S' =>
      rw [hm] at h
      refine .step s (lookS S) g1 g2 s' (lookS S') (itemsOf rest) e hg
        (PinTrapSites.tmovebSound _ _ ht) ?_ (ih s' S' e h)
      -- the memory items
      unfold memChk at hm
      unfold memOk
      cases hst : PinTrapSites.spSt s.tPc with
      | some o =>
        rw [hst] at hm
        simp only [Option.map_eq_some_iff] at hm
        obtain ⟨w, hf, rfl⟩ := hm
        obtain ⟨ga, gb, rl, a, v, asrc, vsrc, hgs, hd⟩ :=
          WeakRvwmoPinBridge5.findStoreSound _ _ _ hf
        exact ⟨ga, gb, rl, a, v, asrc, vsrc, w, hgs, hd, WeakRvwmoPinBridge5.lookSCons _ _ _⟩
      | none =>
        cases hld : PinTrapSites.spLd s.tPc with
        | none =>
          rw [hst, hld] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          simp only []
        | some o =>
          obtain ⟨rfl, k, gb, hh, hgb, hfr⟩ :=
            WeakRvwmoPinBridge5.memChkLd prs s S g1 g2 o S' hst hld (by unfold memChk; exact hm)
          obtain ⟨aq, lat, base, tvs, asrc, rfl⟩ := WeakRvwmoPinBridge5.ldHeadSound _ _ _ hh
          simp only []
          exact ⟨⟨[], gb, aq, lat, base, tvs, asrc, k, rfl, by first | rfl | trivial, hgb,
            fun w hw => hFR _ (hfr w hw)⟩, by first | rfl | trivial⟩

/-- The excursion's steps along B2's witness path, with the canonical items. -/
def trapExcSteps : List (PinTrapSites.TSt × List Eitem × List Eitem) :=
  excSteps PinTrapSites.tStart PinTrapSites.trapWitnessTail 0

/-- The spill → restore pairs of that excursion. -/
def trapExcPairs : List (Nat × Nat) := excPairs PinTrapSites.tStart [] trapExcSteps

set_option maxRecDepth 100000 in
theorem trapExcChk : texcChk trapExcPairs PinTrapSites.tStart [] trapExcSteps PinTrapSites.tEnd = true := by
  decide +kernel

/-- **A REAL FENCE-FREE TRAP EXCURSION** (header): along B2's witness path, with the canonical
items, `texcM FR` holds from `kernelvec`'s entry to its `sret` for every frame relation
containing the slot map's spill → restore pairs. -/
theorem trapExcursionReal (FR : Nat → Nat → Prop) (hFR : ∀ p, p ∈ trapExcPairs → FR p.1 p.2) :
    texcM FR PinTrapSites.tStart (fun _ => none) (itemsOf trapExcSteps) PinTrapSites.tEnd := by
  have h := texcChkSound FR trapExcPairs hFR trapExcSteps PinTrapSites.tStart [] PinTrapSites.tEnd
    trapExcChk
  exact h

set_option maxRecDepth 100000 in
/-- The excursion's frame obligation: 29 spill → restore pairs (`kernelvec`'s 16, the callees'
callee-saved registers and return addresses). -/
theorem trapExcPairsCount : trapExcPairs.length = 29 := by decide +kernel



end Weak
