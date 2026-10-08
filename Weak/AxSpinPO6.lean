/-
Weak: **PHASE 5, stage 5: THE CERTIFICATE `wpdPopOff`** — xv6's REAL `pop_off` (the 19
instructions of `popOffText` on its non-panic paths, the real mycpu composed with
`AxSpinE8.wpdMycpu`) as a POSITIONAL, CALLER-INDEXED CPS WPd at the joint instance Ixv6,
interrupts off (`ctrlOkSW`: S-mode, SIE = 0), WARM TLB.  Pieces: `AxSpinPO5.wpdPpHead`
(`+ 0x00 … + 0x1e`), `wpdPpMid` (`+ 0x20`, `+ 0x22`: the intena load and its beqz),
`wpdPpTail` (`+ 0x28 …` c.ret).

Rocq: `iris/AxSpinPO6.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

`ppSh c` = `ppHead ++ ((if c then [] else ppMid) ++ ppTail)` (AxSpinPOr windows): 10 items
(`c` = "noff − 1 ≠ 0") or 11.  THE THREE NON-RETURN EXITS: `intr_get() → panic` is refuted at
register level (SIE = 0, inside `wpdPpHead`); `noff < 1 → panic` and the `noff == 0 && intena →
intr_on()` arm (csrsi, which would LEAVE the SIE = 0 regime) are excluded by GRAPH-VALUE PINS
(below).  The continuation receives the corresponding facts about the loaded bytes as pure facts
(`¬ (0 ≥ noff)`; `(noff − 1 ≠ 0) = c`; `c = false → intena == 0`) — refuting those arms from
ownership is the caller's business.  For every `k`, `c` and every row with
`RowSh k row (ppSh c …)`:
  WPd (boundary at k, regs rs0) {{Ψ}}
  ⇐ (∀ vn vi vra' vs0' rs' ib',
       ⌜regime ∧ PC = ret ∧ TLB kept ∧ sp = sp0 ∧ a0 = mycpuRet tp ∧ ra / s0 = the RELOADED
        words ∧ every GPR but ra / sp / s0 / a0 / a5 kept ∧ the spills' row data ∧ the noff
        load = vn with ¬ (0 ≥ noff) ∧ the noff store's row data = stBytes 4 (noff − 1) ∧
        (noff − 1 ≠ 0) = c ∧ (c = false → the intena load = vi with intena == 0) ∧ the
        reloads' graph values⌝
       -∗ the two reload annotations (reload bytes = spill bytes)
       -∗ WPd (boundary at tk + 2, regs rs') {{Ψ}})
with `tk = k + 8 + (if c then 0 else 1)` (the tail's start).

GRAPH-VALUE PINNING (Q20', provisional Option V, `notes/weak-port-q20-offrow.md` §C.2 item 4;
Rocq: "TEMPORARY ASSUMPTION — ROW PINNING", owner decision 2026-10-03).  The row fixes which
positions are loads / stores and the data base addresses; control flow is pinned by GRAPH
VALUES: mycpu's return (ra reload at `k + 4`), the noff load at `k + 6` (the bge fall-through
and the arm `c`), the intena load at `k + 8` (arm `c = false` only: the beqz is taken) and
pop_off's own return (`tk`, + `Hret`).  The theorem proves nothing about a graph whose values
differ; the follow-up ROW-INTEGRITY theorem is to discharge the pins.  Ownership is load-bearing
for data values (the reload annotations come from hart `i`'s private ownership of the slots).

Kernel words: checked against `Xv6/KernelImage.lean` (pop_off = 0x80000c98): `+ 0x20` `0x5d7c`
(`lw a5,124(a0)`), `+ 0x22` `0xc399` (`beqz a5,+0x28`), `+ 0x24` `0x10016073` (`csrsi
sstatus,2`, not executed), `+ 0x28` `0x60a2`, `+ 0x2a` `0x6402`, `+ 0x2c` `0x0141`, `+ 0x2e`
`0x8082` — all as in Rocq (`popOffText`'s last seven conjuncts).

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C row `AxSpinPO5/PO6`)

`wpdPpMidP`, `wpdPpTailP`, `wpdPopOffP` are the scripts of `wpdPpMid`, `wpdPpTail`, `wpdPopOff`
on PREFIX rows (`RowShP`, AxSpinRowP), one `by_cases` per row position, every value pin GUARDED
by the position after it, no length premise.  `wpdPopOffP`'s row ends (with `tk = k + 8 + (if c
then 0 else 1)`):
* the WINDOWED, RESOURCE-FREE hook (`AxSpinE8.wpdMycpuP`'s header form):
  `HΨend : ∀ k', k ≤ k' → k' ≤ tk + 2 → k' ≠ k + 7 → (c = false → k' ≠ k + 9) → LEN ≤ k' →
     ∀ pr, ⊢ wpdM … ⟨pr, k'⟩ Ψ`;
* the two DESIGNATED CUTS (AxSpinT2f `cutPos`), EXCLUDED from the hook, their arms premises to be
  supplied by `AxSpinT2h`:
  `ppN` at `k + 7` (row ends after the noff load; `bge` → panic):
    `KppN : LEN = k + 7 → ∀ vn pr, graphValue (i, k + 6) = some vn →
       ⊢ ann4O … (k + 6) rlN -∗ wpdM … ⟨pr, k + 7⟩ Ψ` (PO5's `wpdPpHeadP` arm);
  `ppI` at `k + 9`, arm `c = false` (row ends after the intena load; `beqz` falls → `intr_on`,
  the regime exit):
    `KppI : c = false → LEN = k + 9 → ∀ vn vi pr, graphValue (i, k + 6) = some vn →
       graphValue (i, k + 8) = some vi →
       ⊢ ann4O … (k + 6) rlN -∗ ann4O … (k + 8) rlI -∗ wpdM … ⟨pr, k + 9⟩ Ψ`
  (BOTH annotations: refuting `ppI` needs the noff readback too — `c = false` ⇒ image noff 0 ⇒
  push_off took `b = true` and stored intena 0, `AxSpinT2g.noffArmZero` / `intenaZero`).
`wpdPpMidP` takes the `ppI` arm for a FRAME `R` (the caller's continuation and the noff
annotation ride through it: `⊢ R -∗ (… -∗ R -∗ ann -∗ WPd) -∗ WPd`, `KppI : … ⊢ R -∗ ann -∗
WPd`); its window `[u, u + 1]` excludes `u + 1`, and its continuation learns `u + 1 < LEN` (so
`wpdPopOffP`'s tail starts past the `ppI` cut).  `wpdPpTailP` has no cut (window `[t, t + 2]`).

THE SWAP: the noff (PO5) and intena (`+ 0x20`, here) loads run the OPTIONAL reload leaf
`AxSpinPO5.XxLd4O` (`rlN` / `rlI`; `some (kw, vw, cls)` = `AxSpinLd4P.XxLd4R` against
push_off's own `sw noff` / `sw intena`, premises `AxSpinPO5.rlOk4 … (k + 6) rlN` and
`c = false → AxSpinPO5.rlOk4 … (k + 8) rlI` — the store's row label, data, `kw < load`, and
`nowr` up to the load, as push_off's post exposes them (AxSpinPO4)).  Both annotations
(`AxSpinPO5.ann4O`, `rlFact4` for `some`, `True` for `none`) are CARRIED to the continuation
(the intena one at `if c then none else rlI`).  The old lemmas keep their exact names and
statements and are COROLLARIES (`rlN = rlI = none`, `RowSh ⇒ RowShP`, hook / arms vacuous under
the old length premise, pins unguarded).  The spill-slot `nowr` facts come from
`AxSpinPO6.rowShPNowr` (the prefix `rowShNowr`).

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20', AxSpinPOr,
   AxSpinPOx (XxPin Option V), AxSpinPO4 / PO5 entries):
   * `pp_sh c pra ps0 pmra pms0 pn pint a0c a1a a20 a28 pret nret` (42 / 45 items) ↦
     `ppSh c pra ps0 pmra pms0 pn pint` (10 / 11 items; no fetch items, so the fetch
     parameters `a0c a1a a20 a28 pret nret` and the premises `nret = 2 ∨ nret = 4` are
     DROPPED; in `wpdPpMid` `a20 a28` and in `wpdPpTail` `a28 pret nret` likewise).
   * POSITIONS (a fetch consumes no row item): head as `wpdPpHead` (spills `k / k+1`, Rocq
     `k+2/4`; noff load `k + 6`, Rocq `k + 29`; noff store `k + 7`, Rocq `k + 33`); the mid at
     `u = k + 8` (Rocq `k + 35`): intena load at `u` (Rocq `u + 1`), beqz and continuation at
     `u + 1` (Rocq `u + 3`); `tk = k + 8 (+ 1)` (Rocq `k + 35 (+ 3)`); the tail at `t`: reloads
     at `t / t + 1` (Rocq `t + 1 / t + 3`, graph values and annotations), `c.addi`, `c.ret` and
     the continuation at `t + 2` (Rocq `t + 6`).
   * `wpdPpMid`: Rocq's premise "row item `u + 3` is the pinned fetch of `+ 0x28`" is REPLACED
     by the length premise `u + 1 < row.length` and the value pin `Hvz : ∀ vi, graphValue GD0
     (i, u) = some vi → (ldRes false 4 vi == zero_reg) = true` (the beqz is taken; Rocq: the
     other arm is row-stuck); the `fpin` premise is DROPPED.
   * `wpdPpTail`: NEW length premise `t + 2 < row.length` (the boundary after the c.ret needs
     a next row item, `AxSpinE6.XxRet`'s `k < LEN`; Rocq got it from the return-fetch item);
     `fpin T stv ret pret` ↦ the value pin `graphValue GD0 (i, t) = some (stBytes 8 ret)` +
     `jalrTgt 0#12 ret = ret` (as AxSpinE8 / AxSpinPO3).  The spills' "no write between"
     premises keep Rocq's form `nowr row kra (t + 1) …`.
   * `wpdPopOff`: the five `fpin` premises are DROPPED; NEW value pins (the callees'):
     `graphValue GD0 (i, k + 4) = some (stBytes 8 (ppp 0x0c))` (PO5's mycpu return), PO5's
     `Hvge` / `Hvc` at `(i, k + 6)` (arm `c`), `c = false → ∀ vi, graphValue GD0 (i, k + 8) =
     some vi → (ldRes false 4 vi == zero_reg) = true` (the mid's `Hvz`; Rocq's `if c then True
     else fpin …`), `graphValue GD0 (i, tk) = some (stBytes 8 ret)` + `jalrTgt 0#12 ret = ret`
     (the tail's return).  NEW length premise `tk + 2 < row.length` (PO5's `k + 8 <` and the
     mid's `u + 1 <` are discharged from it).
   * the section context `stv` and the Sail premise `va_first_read` are DROPPED (as PO1–PO5).
   * `ppp24_28` (Rocq's arm-exclusion fact) has no use in the Lean proof (the beqz arm is
     pinned by `Hvz`); it is ported as stated.
2. TYPES / SPELLING (as AxSpinPO4 deviation 2): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `eq_vec a b` ↦ `a == b`;
   `neq_vec a b` ↦ `a != b`; `(i,k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; `l !! k` ↦ `l[k]?`;
   `WeakAxiomatic.LStore` ↦ `Lbl.LStore`; the `let`s are inlined (`sp0` ↦
   `gprVal rs0 AxSpinE8.r2`, `spb` ↦ `AxSpinE8.sp1Of …` (in `wpdPpTail`: `gprVal rs0
   AxSpinE8.r2`), `tp` ↦ `gprVal rs0 AxSpinE8.r4`, `tk` ↦ `k + 8 + (if c then 0 else 1)`,
   `va_ra`/`va_s0` ↦ `… + sign_extend (m := 64) AxSpinE8.immRa/immS0`); `Interface.Ret tt` ↦
   `.pure ()`; Rocq's right-nested `a ++ b ++ c` is written `a ++ (b ++ c)`.
3. INSTANCES / SECTION (as AxSpinPO4 deviation 3): `[InvGS_gen hlc GF]` (any `hlc`); the
   local instances `qw_pol`/`qw_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`;
   section variables are explicit arguments in AxSpinE6's order (+ `Htxm Htxq`).
4. PROOF SHAPE: Rocq's `iAssert … with "[C]" as "TL"` (the tail, once for both arms) is a Lean
   `have` generic in the continuation proposition (`Cp`), instantiated at the goal's (as
   AxSpinPO4).  The trailing `Print Assumptions` is not ported.

**Rocq → Lean name map.**  `pp_sh` `ppSh`, `ppp_24_28` `ppp24_28`, `wpd_pp_mid` `wpdPpMid`,
`wpd_pp_tail` `wpdPpTail`, `wpd_pop_off` `wpdPopOff`.  The local instances `qw_pol`, `qw_G`
are inlined (deviation 3).  Lean-only (file-qualified): `AxSpinPO6.ppShNowr` (Rocq's inline `nowr_tac` calls at the two
spills, stated in a small context — in `wpdPopOff`'s context the macro hits the recursion
limit), `AxSpinPO6.rowShPNowr` (stage 2); P-form (unqualified, grepped unique) `wpdPpMidP`,
`wpdPpTailP`, `wpdPopOffP` (+ 1 local macro).  Reused (stage 2): `RowShP`/`rowShPOfSh`/
`rowShPAppL`/`rowShPAppR`/`rowShPAt` (AxSpinRowP), `wpdPpHeadP`/`AxSpinPO5.XxLd4O`/`rlOk4`/
`ann4O` (AxSpinPO5).

**Dropped:** nothing (Rocq 5 definitions/lemmas + 2 local instances; Lean 5 + 4 stage-2).
-/
import Weak.AxSpinPO4
import Weak.AxSpinPO5
import Weak.AxSpinPOt6

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `pp_sh` (deviation 1: no fetch items / parameters). -/
def ppSh (c : Bool) (pra ps0 pmra pms0 pn pint : Int) : List Ritem :=
  ppHead pra ps0 pmra pms0 pn ++ ((if c then [] else ppMid pint) ++ ppTail pra ps0)

/-- Rocq `ppp_24_28` (deviation 1: no use under Option V). -/
theorem ppp24_28 : ppp 0x24 ≠ ppp 0x28 := by decide

/-- (Lean-only, Rocq's `nowr_tac` at the two spills) the `rowShNowr` side goals of `ppSh`. -/
theorem AxSpinPO6.ppShNowr (c : Bool) (pra ps0 pmra pms0 pn pint : Int) :
    dj pra 8 ps0 8 → dj pra 8 pmra 8 → dj pra 8 pms0 8 → dj pra 8 pn 4 →
    dj ps0 8 pmra 8 → dj ps0 8 pms0 8 → dj ps0 8 pn 4 →
    (∀ it ∈ ((ppSh c pra ps0 pmra pms0 pn pint).take (9 + (if c then 0 else 1))).drop (0 + 1),
      itDisj pra 8 it) ∧
    (∀ it ∈ ((ppSh c pra ps0 pmra pms0 pn pint).take (9 + (if c then 0 else 1))).drop (1 + 1),
      itDisj ps0 8 it) := by
  intro D_ra_s0 D_ra_mra D_ra_ms0 D_ra_n D_s0_mra D_s0_ms0 D_s0_n
  constructor <;>
  cases c <;> simp only [ppSh, ↓reduceIte, Bool.false_eq_true, List.nil_append,
    Nat.reduceAdd] <;> ax_spin_por_nowr

/-- (Lean-only, stage 2) `rowShNowr` on a PREFIX row: only present items can write, and every
present item of the window is matched, so no length premise beyond `jr ≤ sh.length`. -/
theorem AxSpinPO6.rowShPNowr (k : Nat) (row : List Lbl) (sh : List Ritem) (jw jr : Nat)
    (pa : Int) (w : Nat) :
    RowShP k row sh → jr ≤ sh.length →
    (∀ it ∈ (sh.take jr).drop (jw + 1), itDisj pa w it) →
    nowr row (k + jw) (k + jr) pa w := by
  intro H Hle HF k' lb rl b m Hk Hlb Hid
  have Hk' : k' < row.length := (List.getElem?_eq_some_iff.1 Hlb).1
  obtain ⟨it, Hit⟩ : ∃ it, sh[k' - k]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨lb', Hlb', Hs⟩ := H (k' - k) it Hit (by omega)
  rw [show k + (k' - k) = k' by omega, Hlb] at Hlb'
  cases Hlb'
  have Hj : ((sh.take jr).drop (jw + 1))[k' - k - (jw + 1)]? = some it := by
    rw [List.getElem?_drop, List.getElem?_take]
    rw [if_pos (by omega), show jw + 1 + (k' - k - (jw + 1)) = k' - k by omega]
    exact Hit
  have Hd : itDisj pa w it := HF it (List.mem_of_getElem? Hj)
  cases it with
  | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hid; cases Hid
  | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid
  | RS pb n =>
    obtain ⟨vw, cls, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    rw [Hl]
    exact Hd
  | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_po6_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

section popoff
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxm : mycpuText σi T) (Htxq : popOffText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

/-! # 1. + 0x20 / 0x22: the intena load and the beqz to + 0x28 -/

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxq HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdPpMid` on a PREFIX row (the pin `Hvz` GUARDED by
`u + 1 < LEN`): `by_cases` at `u` (the WINDOWED hook; its window `[u, u + 1]` EXCLUDES the
designated cut `ppI` at `u + 1`) and at `u + 1` (the cut arm, premise `KppI`, which receives the
intena load's graph value, the frame `R` and the intena annotation).  The intena load runs the
optional reload leaf `AxSpinPO5.XxLd4O rlI`.  `R` is a frame handed back to the continuation
(and to `KppI`); the continuation also learns `u + 1 < LEN`. -/
theorem wpdPpMidP (u : Nat) (rs0 : RegFile) (ib0 : Ibch) (Pi : BitVec 64)
    (rlI : Option (Nat × List (BitVec 8) × WmClass)) (R : IProp GF) :
    RowShP u (AxOpsem.grow (gtAdGd GT) i) (ppMid (paZ Pi)) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0x20 → hitW rs0 (ppp 0) →
    fld4 σi T L i rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) i124) Pi →
    (u + 1 < (AxOpsem.grow (gtAdGd GT) i).length →
      ∀ vi, graphValue (gtAdGd GT) (i, u) = some vi → (ldRes false 4 vi == zero_reg) = true) →
    AxSpinPO5.rlOk4 (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) u rlI →
    (∀ k' : Nat, u ≤ k' → k' ≤ u + 1 → k' ≠ u + 1 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ((AxOpsem.grow (gtAdGd GT) i).length = u + 1 →
      ∀ (vi : List (BitVec 8)) (pr : Pexv6), graphValue (gtAdGd GT) (i, u) = some vi →
        ⊢ R -∗ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pi) u rlI -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, u + 1⟩ Ψ) →
    ⊢ R -∗ (∀ (vi : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ppp 0x28 ∧ rs' .tlb = rs0 .tlb ∧
          (∀ r : BitVec 5, r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphValue (gtAdGd GT) (i, u) = some vi ∧ (ldRes false 4 vi == zero_reg) = true⌝ -∗
        ⌜u + 1 < (AxOpsem.grow (gtAdGd GT) i).length⌝ -∗
        R -∗ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pi) u rlI -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', u + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, u⟩ Ψ := by
  intro _HR Hnr Hc0 HPC0 Hhit0 ⟨_, HdaL_i, Hh_i, Hpr_i, Hnt_i⟩ Hvz HrlI HΨend KppI
  iintro HRr C
  -- row end at u
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ u
  · iclear C
    iclear HRr
    iapply (HΨend _ (by omega) (by omega) (by omega) (by omega) _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, T20, T22, -⟩ := Htxq
  have XL4 := AxSpinPO5.XxLd4O L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XP := XxPin L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  -- ---- + 0x20: lw a5,124(a0) — intena (u), the optional RELOAD leaf ----
  iapply (XL4 _ rs0 u (ppp 0x20) true i124 10#5 15#5
    (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) i124) Pi
    (retxRefl cpu rs0 u ib0) Hc0 HPC0
    (hitWSvpn rs0 (ppp 0x20) (ppp 0) (by decide) Hhit0)
    (tw5d7c σi T satp0 _ T20) (by decide) rfl HdaL_i Hh_i Hnt_i Hnr (by omega) Hpr_i rlI HrlI)
  iintro %vi %rs1 %ib1 %_Hlvi %HG1 %Hgv0 HaI
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = ppp 0x22 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- row end at u + 1: THE DESIGNATED CUT ppI (the arm is the premise `KppI`)
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ u + 1
  · iclear C
    iapply (KppI (by omega) vi _ Hgv0) $$ HRr HaI
  -- ---- + 0x22: beqz a5,+0x28 — the gate (guarded pin `Hvz`) (u+1) ----
  have Hz : (ldRes false 4 vi == zero_reg) = true := Hvz (by omega) vi Hgv0
  have Hcb := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs1
    (ppp 0x22) true (sign_extend (m := 13) (3#8 +++ 0b0#1)) 0#5 15#5 .BEQ (by decide)
  have Htgt : tgtOf (brOt .BEQ 15#5 0#5 rs1
      (ppp 0x22 + sign_extend (m := 64) (sign_extend (m := 13) (3#8 +++ 0b0#1))))
      (ppp 0x22) true = ppp 0x28 := by
    have Ea5 : gval 15#5 rs1 = ldRes false 4 vi := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs1 15#5 = _
      rw [HF1]
      ax_spin_po6_zsimp
    have Ez : gval 0#5 rs1 = zero_reg := by
      unfold gval
      rw [if_pos (by decide)]
    unfold tgtOf brOt AxSymCtl2.bcond
    rw [Ea5, Ez, Hz]
    simp only [↓reduceIte]
    decide
  iapply (XP _ rs1 (u + 1) (ppp 0x22) true p22 _ none (ppp 0x28)
    (retxRefl cpu rs1 (u + 1) ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (ppp 0x22) (ppp 0) (by decide) (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (twC399 σi T satp0 _ T22) trivial (rfFBtype _ _ _ _) Hcb (by omega) Htgt)
  iintro %rs' %ib' %HGP
  obtain ⟨HGr, Htg⟩ := HGP
  have HFr := stepRegs0 T satp0 _ rs1 _ _ _ rs' HF1 HGr
  have Hlt : u + 1 < (AxOpsem.grow (gtAdGd GT) i).length := by omega
  iapply C $$ %vi %rs' %ib' [] %Hlt HRr HaI
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl1, ?_,
    Hgv0, Hz⟩
  · -- PC = + 0x28
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    exact Htg
  · -- every GPR but a5 kept
    intro r Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]

include HL Hcons hmode hasid hppn Hfix Htxq HΨmid in
/-- Rocq `wpd_pp_mid` (deviation 1: Stage C positions; the pinned-fetch row premise becomes
`u + 1 < row.length` + the value pin `Hvz`; no `fpin`).  Stage 2: the full-row corollary of
`wpdPpMidP` (`rlI = none`, frame `True`; hook and cut arm vacuous under `u + 1 < LEN`). -/
theorem wpdPpMid (u : Nat) (rs0 : RegFile) (ib0 : Ibch) (Pi : BitVec 64) :
    RowSh u (AxOpsem.grow (gtAdGd GT) i) (ppMid (paZ Pi)) →
    u + 1 < (AxOpsem.grow (gtAdGd GT) i).length →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0x20 → hitW rs0 (ppp 0) →
    fld4 σi T L i rs0 (gprVal rs0 AxSpinE8.r10 + sign_extend (m := 64) i124) Pi →
    (∀ vi, graphValue (gtAdGd GT) (i, u) = some vi → (ldRes false 4 vi == zero_reg) = true) →
    ⊢ (∀ (vi : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ppp 0x28 ∧ rs' .tlb = rs0 .tlb ∧
          (∀ r : BitVec 5, r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphValue (gtAdGd GT) (i, u) = some vi ∧ (ldRes false 4 vi == zero_reg) = true⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', u + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, u⟩ Ψ := by
  intro HR Hlen Hnr Hc0 HPC0 Hhit0 Bi Hvz
  iintro C
  iapply (wpdPpMidP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxq Ψ HΨmid
    u rs0 ib0 Pi none iprop(True) (rowShPOfSh HR) Hnr Hc0 HPC0 Hhit0 Bi (fun _ => Hvz) trivial
    (fun _ _ h2 h3 h4 => absurd h4 (by omega)) (fun h => absurd h (by omega))) $$ [] [C]
  · ipureintro
    trivial
  · iintro %vi %rs' %ib' %H %_ - -
    iapply C $$ %vi %rs' %ib' %H

/-! # 2. + 0x28 … c.ret: the two reloads and the return -/

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxq HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdPpTail` on a PREFIX row (the return pin GUARDED by
`t < LEN`, no length premise): `by_cases` at `t`, `t + 1`, `t + 2`; the row-end case is the
WINDOWED hook on `[t, t + 2]` (no designated cut in the tail). -/
theorem wpdPpTailP (t : Nat) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 : BitVec 64) (kra ks0 : Nat) (vra vs0 : List (BitVec 8)) (cra cs0 : WmClass) :
    RowShP t (AxOpsem.grow (gtAdGd GT) i) (ppTail (paZ Pra) (paZ Ps0)) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    (AxOpsem.grow (gtAdGd GT) i)[kra]? = some (.LStore false (paZ Pra) vra cra) →
    vra.length = 8 → kra < t → nowr (AxOpsem.grow (gtAdGd GT) i) kra (t + 1) (paZ Pra) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks0]? = some (.LStore false (paZ Ps0) vs0 cs0) →
    vs0.length = 8 → ks0 < t → nowr (AxOpsem.grow (gtAdGd GT) i) ks0 (t + 1) (paZ Ps0) 8 →
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0x28 → hitW rs0 (ppp 0) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immRa) 8
      Pra → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immS0) 8
      Ps0 → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (t < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, t) = some (stBytes 8 ret)) → jalrTgt 0#12 ret = ret →
    (∀ k' : Nat, t ≤ k' → k' ≤ t + 2 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vra' vs0' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 =
            gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) (sign_extend (m := 12) (16#6)) ∧
          vra'.length = 8 ∧ vs0'.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → gprVal rs' r = gprVal rs0 r) ∧
          graphValue (gtAdGd GT) (i, t) = some vra' ∧
          graphValue (gtAdGd GT) (i, t + 1) = some vs0'⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, t) iprop(⌜RLfact GT i (paZ Pra) t vra⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 1) iprop(⌜RLfact GT i (paZ Ps0) (t + 1) vs0⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', t + 2⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, t⟩ Ψ := by
  intro _HR Hnr_ra Hnr_s0 Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0
    Hc0 HPC0 Hhit0 HdaL_ra Hh_ra HdaL_s0 Hh_s0 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hval Hret HΨend
  iintro C
  -- row end at t
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, T28, T2a, T2c, T2e⟩ := Htxq
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL := XxLd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XT := XxRet L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  -- ---- + 0x28: ld ra,8(sp) — reload (t) ----
  iapply (XL _ rs0 t (ppp 0x28) true AxSpinE8.immRa 2#5 1#5
    (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immRa) Pra kra vra cra
    (retxRefl cpu rs0 t ib0) Hc0 HPC0
    (hitWSvpn rs0 (ppp 0x28) (ppp 0) (by decide) Hhit0)
    (tw60a2 σi T satp0 _ T28) (by decide) rfl HdaL_ra Hh_ra Hpr_ra Hnt_ra Hnr_ra Hkra Hlra
    Hlt_ra ?_ (by omega))
  · intro k' lb' rl b m Hk Hl Hid
    have := Hbw_ra k' lb' rl b m ⟨Hk.1, Nat.lt_succ_of_lt Hk.2⟩ Hl Hid
    unfold dj at this
    omega
  iintro %vra' %rs1 %ib1 %Hlvra %HG1 %Hgv0 H0
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = ppp 0x2a := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- row end at t + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 1
  · iclear C
    iclear H0
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x2a: ld s0,0(sp) — reload (t+1) ----
  iapply (XL _ rs1 (t + 1) (ppp 0x2a) true AxSpinE8.immS0 2#5 8#5
    (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immS0) Ps0 ks0 vs0 cs0
    (retxRefl cpu rs1 (t + 1) ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (ppp 0x2a) (ppp 0) (by decide) (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (tw6402 σi T satp0 _ T2a) (by decide) (by rw [HF1]; ax_spin_po6_zsimp)
    HdaL_s0 (hitWAgree rs0 rs1 _ Htl1 Hh_s0) Hpr_s0 Hnt_s0 Hnr_s0 Hks0 Hls0 (by omega)
    ?_ (by omega))
  · intro k' lb' rl b m Hk Hl Hid
    have := Hbw_s0 k' lb' rl b m Hk Hl Hid
    unfold dj at this
    omega
  iintro %vs0' %rs2 %ib2 %Hlvs0 %HG2 %Hgv1 H1
  have HF2 := stepRegs T satp0 _ rs1 _ _ _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = ppp 0x2c := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  -- row end at t + 2
  by_cases E2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 2
  · iclear C
    iclear H0
    iclear H1
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x2c: c.addi sp,16 (t+2) ----
  have Hc3 := certAddi (ctrlOkSW T satp0) rs2 (ppp 0x2c) true 2#5 2#5
    (sign_extend (m := 12) (16#6)) (by decide)
  simp only [HF2] at Hc3
  ax_spin_po6_zsimp at Hc3
  iapply (XR _ rs2 (t + 2) (ppp 0x2c) true ins1c _ _
    (retxRefl cpu rs2 (t + 2) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (ppp 0x2c) (ppp 0) (by decide) (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (tw0141 σi T satp0 _ T2c) (AxSpinE8.owOkSome 2#5 _ (by decide)) rfFIns1c Hc3 (by omega))
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = ppp 0x2e := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- ---- + 0x2e: c.ret (t+2; Q20': no stuck branch, the target is the reloaded ra) ----
  iapply (XT _ rs3 (t + 2) (ppp 0x2e)
    (retxRefl cpu rs3 (t + 2) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (ppp 0x2e) (ppp 0) (by decide) (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (tw8082 σi T satp0 _ T2e) rfFIns1e (by omega))
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs3 _ _ _ rs' HF3 HGr
  have Hvra : vra' = stBytes 8 ret := Option.some.inj (Hgv0.symm.trans (Hval (by omega)))
  have Hgpr1 : gprVal rs3 1#5 = ldRes false 8 vra' := by
    rw [HF3]
    ax_spin_po6_zsimp
  iapply C $$ %vra' %vs0' %rs' %ib' [] H0 H1
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl3, ?_,
    Hlvra, Hlvs0, ?_, ?_, ?_, Hgv0, Hgv1⟩
  · -- PC = ret: the c.ret target is the reloaded ra, pinned by `Hval`
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    show jalrTgt 0#12 (gprVal rs3 1#5) = ret
    rw [Hgpr1, Hvra, AxSpinE8.ldResStBytes8, Hret]
  · -- sp + 16
    rw [HFr]
    ax_spin_po6_zsimp
  · rw [HFr]
    ax_spin_po6_zsimp
  · rw [HFr]
    ax_spin_po6_zsimp
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]

include HL Hcons hmode hasid hppn Hfix Htxq HΨmid in
/-- Rocq `wpd_pp_tail` (deviation 1: Stage C positions; the value pin + `Hret` replace
`fpin T stv ret pret`; new length premise `t + 2 < row.length`).  Stage 2: the full-row
corollary of `wpdPpTailP` (the hook is vacuous under `t + 2 < LEN`). -/
theorem wpdPpTail (t : Nat) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 : BitVec 64) (kra ks0 : Nat) (vra vs0 : List (BitVec 8)) (cra cs0 : WmClass) :
    RowSh t (AxOpsem.grow (gtAdGd GT) i) (ppTail (paZ Pra) (paZ Ps0)) →
    t + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    (AxOpsem.grow (gtAdGd GT) i)[kra]? = some (.LStore false (paZ Pra) vra cra) →
    vra.length = 8 → kra < t → nowr (AxOpsem.grow (gtAdGd GT) i) kra (t + 1) (paZ Pra) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks0]? = some (.LStore false (paZ Ps0) vs0 cs0) →
    vs0.length = 8 → ks0 < t → nowr (AxOpsem.grow (gtAdGd GT) i) ks0 (t + 1) (paZ Ps0) 8 →
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0x28 → hitW rs0 (ppp 0) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immRa) 8
      Pra → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immRa) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immS0) 8
      Ps0 → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinE8.immS0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    graphValue (gtAdGd GT) (i, t) = some (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    ⊢ (∀ (vra' vs0' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 =
            gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) (sign_extend (m := 12) (16#6)) ∧
          vra'.length = 8 ∧ vs0'.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → gprVal rs' r = gprVal rs0 r) ∧
          graphValue (gtAdGd GT) (i, t) = some vra' ∧
          graphValue (gtAdGd GT) (i, t + 1) = some vs0'⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, t) iprop(⌜RLfact GT i (paZ Pra) t vra⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 1) iprop(⌜RLfact GT i (paZ Ps0) (t + 1) vs0⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', t + 2⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, t⟩ Ψ := by
  intro HR Hlen Hnr_ra Hnr_s0 Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0
    Hc0 HPC0 Hhit0 HdaL_ra Hh_ra HdaL_s0 Hh_s0 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hval Hret
  exact wpdPpTailP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxq Ψ HΨmid
    t rs0 ib0 ret Pra Ps0 kra ks0 vra vs0 cra cs0 (rowShPOfSh HR) Hnr_ra Hnr_s0 Hkra Hlra Hlt_ra
    Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hc0 HPC0 Hhit0 HdaL_ra Hh_ra HdaL_s0 Hh_s0 Hpr_ra Hnt_ra
    Hpr_s0 Hnt_s0 (fun _ => Hval) Hret (fun _ _ h2 h3 => absurd h3 (by omega))

/-! # 3. THE CERTIFICATE -/

set_option maxHeartbeats 6400000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxq HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdPopOff` on a PREFIX row (`RowShP` of `ppSh c`; every
value pin GUARDED by the position after it; no length premise).  The row-end cases: the
WINDOWED hook `HΨend` on `[k, tk + 2]` EXCEPT the two designated cuts — `ppN` at `k + 7` (arm
`KppN`: the noff load's graph value + annotation) and, on the arm `c = false`, `ppI` at `k + 9`
(arm `KppI`: both loads' graph values + both annotations).  The noff / intena loads run the
optional reload leaf `AxSpinPO5.XxLd4O rlN` / `rlI` (`rlI` only used on `c = false`); both
annotations are CARRIED to the continuation (the intena one is `True` on `c = true`). -/
theorem wpdPopOffP (k : Nat) (c : Bool) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 Pmra Pms0 Pn Pi : BitVec 64) (rlN rlI : Option (Nat × List (BitVec 8) × WmClass)) :
    -- the row (prefix)
    RowShP k (AxOpsem.grow (gtAdGd GT) i)
      (ppSh c (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn) (paZ Pi)) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0 → hitW rs0 (ppp 0) → hitW rs0 (pcm 0) →
    -- the slots and the cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    alldj [(paZ Pra, 8), (paZ Ps0, 8), (paZ Pmra, 8), (paZ Pms0, 8), (paZ Pn, 4)] →
    -- the value pins (guarded by position)
    (k + 4 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 4) = some (stBytes 8 (ppp 0x0c))) →
    (k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
      ∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
        zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = c) →
    (c = false → k + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
      ∀ vi, graphValue (gtAdGd GT) (i, k + 8) = some vi → (ldRes false 4 vi == zero_reg) = true) →
    (k + 8 + (if c then 0 else 1) < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 8 + (if c then 0 else 1)) = some (stBytes 8 ret)) →
    jalrTgt 0#12 ret = ret →
    -- the two (optional) field reloads
    AxSpinPO5.rlOk4 (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) (k + 6) rlN →
    (c = false → AxSpinPO5.rlOk4 (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) (k + 8) rlI) →
    -- the row-end hook (windowed; NOT at the designated cuts)
    (∀ k' : Nat, k ≤ k' → k' ≤ k + 8 + (if c then 0 else 1) + 2 → k' ≠ k + 7 →
      (c = false → k' ≠ k + 9) → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    -- the designated cut ppN (row ends right after the noff load)
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 7 →
      ∀ (vn : List (BitVec 8)) (pr : Pexv6), graphValue (gtAdGd GT) (i, k + 6) = some vn →
        ⊢ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, k + 7⟩ Ψ) →
    -- the designated cut ppI (arm c = false; row ends right after the intena load)
    (c = false → (AxOpsem.grow (gtAdGd GT) i).length = k + 9 →
      ∀ (vn vi : List (BitVec 8)) (pr : Pexv6), graphValue (gtAdGd GT) (i, k + 6) = some vn →
        graphValue (gtAdGd GT) (i, k + 8) = some vi →
        ⊢ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
          AxSpinPO5.ann4O (GF := GF) GT i (paZ Pi) (k + 8) rlI -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, k + 9⟩ Ψ) →
    ⊢ (∀ (vn vi vra' vs0' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 6) = some vn ∧
          zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false ∧
          graphData (gtAdGd GT) (i, k + 7) = some (stBytes 4 (addiwm1 (ldRes false 4 vn))) ∧
          (addiwm1 (ldRes false 4 vn) != zero_reg) = c ∧
          (c = false → graphValue (gtAdGd GT) (i, k + 8) = some vi ∧
            (ldRes false 4 vi == zero_reg) = true) ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if c then 0 else 1)) = some vra' ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if c then 0 else 1) + 1) = some vs0'⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8 + (if c then 0 else 1))
          iprop(⌜RLfact GT i (paZ Pra) (k + 8 + (if c then 0 else 1))
            (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8 + (if c then 0 else 1) + 1)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 8 + (if c then 0 else 1) + 1)
            (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
        AxSpinPO5.ann4O (GF := GF) GT i (paZ Pi) (k + 8) (if c then none else rlI) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 8 + (if c then 0 else 1) + 2⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hnr_mra Hnr_ms0 Hwle_n Hnrn Hnri Hc0 HPC0 Hhit0 HhitM
    Bra Bs0 Bmra Bms0 Bn Bi Hdj Hval0c Hvge Hvc Hvz Hvalr Hret HrlN HrlI HΨend KppN KppI
  -- ---- the five ranges, pairwise ----
  have D_ra_s0 : dj (paZ Pra) 8 (paZ Ps0) 8 := Hdj 0 1 (paZ Pra, 8) (paZ Ps0, 8) rfl rfl (by decide)
  have D_ra_mra : dj (paZ Pra) 8 (paZ Pmra) 8 :=
    Hdj 0 2 (paZ Pra, 8) (paZ Pmra, 8) rfl rfl (by decide)
  have D_ra_ms0 : dj (paZ Pra) 8 (paZ Pms0) 8 :=
    Hdj 0 3 (paZ Pra, 8) (paZ Pms0, 8) rfl rfl (by decide)
  have D_ra_n : dj (paZ Pra) 8 (paZ Pn) 4 := Hdj 0 4 (paZ Pra, 8) (paZ Pn, 4) rfl rfl (by decide)
  have D_s0_mra : dj (paZ Ps0) 8 (paZ Pmra) 8 :=
    Hdj 1 2 (paZ Ps0, 8) (paZ Pmra, 8) rfl rfl (by decide)
  have D_s0_ms0 : dj (paZ Ps0) 8 (paZ Pms0) 8 :=
    Hdj 1 3 (paZ Ps0, 8) (paZ Pms0, 8) rfl rfl (by decide)
  have D_s0_n : dj (paZ Ps0) 8 (paZ Pn) 4 := Hdj 1 4 (paZ Ps0, 8) (paZ Pn, 4) rfl rfl (by decide)
  have D_mra_ms0 : dj (paZ Pmra) 8 (paZ Pms0) 8 :=
    Hdj 2 3 (paZ Pmra, 8) (paZ Pms0, 8) rfl rfl (by decide)
  clear Hdj
  -- ---- tk arithmetic ----
  have Htk0 : (if c then 0 else 1) ≤ 1 := by split <;> omega
  have Htk9 : c = false → k + 8 + (if c then 0 else 1) = k + 9 := by intro hc; subst hc; rfl
  -- ---- the windows (prefix) ----
  have HRh : RowShP k (AxOpsem.grow (gtAdGd GT) i)
      (ppHead (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn)) :=
    rowShPAppL (s1 := ppHead (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn))
      (s2 := (if c then [] else ppMid (paZ Pi)) ++ ppTail (paZ Pra) (paZ Ps0)) HR
  have HRr : RowShP (k + 8) (AxOpsem.grow (gtAdGd GT) i)
      ((if c then [] else ppMid (paZ Pi)) ++ ppTail (paZ Pra) (paZ Ps0)) :=
    rowShPAppR (s1 := ppHead (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn))
      (s2 := (if c then [] else ppMid (paZ Pi)) ++ ppTail (paZ Pra) (paZ Ps0)) HR
  have HRt : RowShP (k + 8 + (if c then 0 else 1)) (AxOpsem.grow (gtAdGd GT) i)
      (ppTail (paZ Pra) (paZ Ps0)) := by
    have h := rowShPAppR (k := k + 8) (s1 := if c then [] else ppMid (paZ Pi))
      (s2 := ppTail (paZ Pra) (paZ Ps0)) HRr
    rwa [show (if c then [] else ppMid (paZ Pi)).length = (if c then 0 else 1) by
      cases c <;> rfl] at h
  -- ---- the head and the arm, generic in the continuation (Rocq's "TL" assertion) ----
  have HI : ∀ Cp : IProp GF,
      (∀ (vn vi : List (BitVec 8)) (rs1 : RegFile) (ib1 : Ibch),
        ctrlOkSW T satp0 rs1 ∧ rs1 .PC = ppp 0x28 ∧ rs1 .tlb = rs0 .tlb ∧
          gprVal rs1 AxSpinE8.r2 = AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) ∧
          gprVal rs1 AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs1 r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 6) = some vn ∧
          zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false ∧
          graphData (gtAdGd GT) (i, k + 7) = some (stBytes 4 (addiwm1 (ldRes false 4 vn))) ∧
          (addiwm1 (ldRes false 4 vn) != zero_reg) = c ∧
          (c = false → graphValue (gtAdGd GT) (i, k + 8) = some vi ∧
            (ldRes false 4 vi == zero_reg) = true) ∧
          (c = false → k + 9 < (AxOpsem.grow (gtAdGd GT) i).length) →
        ⊢ Cp -∗ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
          AxSpinPO5.ann4O (GF := GF) GT i (paZ Pi) (k + 8) (if c then none else rlI) -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨.PHart cpu (.pure ()) rs1 none ib1, k + 8 + (if c then 0 else 1)⟩ Ψ) →
      ⊢ Cp -∗ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
    intro Cp TL
    iintro C
    iapply (wpdPpHeadP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxq Ψ HΨmid
      k c rs0 ib0 Pra Ps0 Pmra Pms0 Pn rlN HRh Hw8 Hnr_mra Hnr_ms0 Hwle_n Hnrn Hc0 HPC0 Hhit0
      HhitM Bra Bs0 Bmra Bms0 Bn (djSym _ _ _ _ D_mra_ms0) Hval0c Hvge Hvc HrlN
      (fun k' h1 h2 h3 h4 pr => HΨend k' h1 (by omega) h3 (fun _ => by omega) h4 pr) KppN)
    iintro %vn %rs1 %ib1 %Hh HaN
    obtain ⟨Hc1, HPC1, Htl1, Ea01, Esp1, _, _, Hkeep1, Hgd0, Hgd1, Hgv6, Hge, Hgd7, Hcc⟩ := Hh
    cases c with
    | true =>
      -- noff − 1 ≠ 0: straight to the tail
      have TL' := TL vn [] rs1 ib1 ⟨Hc1, HPC1, Htl1, Esp1, Ea01, Hkeep1, Hgd0, Hgd1, Hgv6, Hge,
        Hgd7, Hcc, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
      rw [show k + 8 + (if true = true then 0 else 1) = k + 8 from rfl] at TL'
      ihave TLi := TL'
      iapply TLi $$ C HaN
      rw [if_pos rfl]
      simp only [AxSpinPO5.ann4O]
      ipureintro
      trivial
    | false =>
      -- noff − 1 = 0: the intena load (P-form; frame = the continuation and the noff annotation)
      have HRm : RowShP (k + 8) (AxOpsem.grow (gtAdGd GT) i) (ppMid (paZ Pi)) :=
        rowShPAppL (s1 := ppMid (paZ Pi)) (s2 := ppTail (paZ Pra) (paZ Ps0)) HRr
      iapply (wpdPpMidP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxq Ψ HΨmid
        (k + 8) rs1 ib1 Pi rlI iprop(Cp ∗ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN)
        HRm Hnri Hc1 (by rw [HPC1]; rfl) (hitWAgree rs0 rs1 _ Htl1 Hhit0)
        (by rw [Ea01]; exact fld4Tlb _ _ _ _ _ _ _ _ Htl1 Bi) (Hvz rfl) (HrlI rfl)
        (fun k' h1 h2 h3 h4 pr => HΨend k' (by omega) (by show k' ≤ k + 8 + 1 + 2; omega)
          (by omega) (fun _ => by omega) h4 pr)
        (fun hL vi pr hv => by
          iintro ⟨-, HaN⟩ HaI
          iapply (KppI rfl hL vn vi pr Hgv6 hv) $$ HaN HaI)) $$ [C HaN] []
      · isplitl [C]
        · iexact C
        · iexact HaN
      · iintro %vi %rs2 %ib2 %Hm %Hlt9 ⟨C, HaN⟩ HaI
        obtain ⟨Hc2, HPC2, Htl2, Hkeep2, Hgv8, Hz⟩ := Hm
        have TL' := TL vn vi rs2 ib2 ⟨Hc2, HPC2, Htl2.trans Htl1,
          by rw [Hkeep2 AxSpinE8.r2 (by decide)]; exact Esp1,
          by rw [Hkeep2 AxSpinE8.r10 (by decide)]; exact Ea01,
          fun r Hr1 Hr2 Hr8 Hr10 Hr15 => by
            rw [Hkeep2 r Hr15]; exact Hkeep1 r Hr1 Hr2 Hr8 Hr10 Hr15,
          Hgd0, Hgd1, Hgv6, Hge, Hgd7, Hcc, fun _ => ⟨Hgv8, Hz⟩, fun _ => Hlt9⟩
        rw [show k + 8 + (if false = true then 0 else 1) = k + 8 + 1 from rfl] at TL'
        ihave TLi := TL'
        iapply TLi $$ C HaN
        rw [if_neg (by decide)]
        iexact HaI
  refine HI _ (fun vn vi rs1 ib1 Hf => ?_)
  -- ---- the tail, once for both arms ----
  obtain ⟨Hc1, HPC1, Htl1, Esp1, Ea01, Hkeep1, Hgd0, Hgd1, Hgv6, Hge, Hgd7, Hcc, Hmid, Hlt9⟩ := Hf
  iintro C HaN HaI
  -- row end at tk (not the ppI cut: on c = false the mid ran past k + 9)
  by_cases Et : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 8 + (if c then 0 else 1)
  · iclear C
    iclear HaN
    iclear HaI
    iapply (HΨend _ (by omega) (by omega) (by omega)
      (fun hc => by have := Htk9 hc; have := Hlt9 hc; omega) Et _)
  obtain ⟨lb0, Hkra, vra, cra, Elb0, Hlra⟩ := rowShPAt (it := Ritem.RS (paZ Pra) 8) (j := 0)
    HR rfl (by omega)
  subst Elb0
  rw [Nat.add_zero] at Hkra
  obtain ⟨lb1, Hks0, vs0, cs0, Elb1, Hls0⟩ := rowShPAt (it := Ritem.RS (paZ Ps0) 8) (j := 1)
    HR rfl (by omega)
  subst Elb1
  have Evra : vra = stBytes 8 (gprVal rs0 AxSpinE8.r1) := by
    unfold graphData at Hgd0
    rw [AxWp.growLookup _ _ _ _ Hkra] at Hgd0
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd0
  have Evs0 : vs0 = stBytes 8 (gprVal rs0 AxSpinE8.r8) := by
    unfold graphData at Hgd1
    rw [AxWp.growLookup _ _ _ _ Hks0] at Hgd1
    simpa only [Option.bind_some, lblData, Option.some.injEq] using Hgd1
  subst Evra Evs0
  -- no write to a spill slot between its spill and the tail's start
  have NW : ∀ (jw : Nat) (pa : Int) (w : Nat),
      (∀ it ∈ ((ppSh c (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn)
        (paZ Pi)).take (9 + (if c then 0 else 1))).drop (jw + 1), itDisj pa w it) →
      nowr (AxOpsem.grow (gtAdGd GT) i) (k + jw) (k + 8 + (if c then 0 else 1) + 1) pa w := by
    intro jw pa w HF
    rw [show k + 8 + (if c then 0 else 1) + 1 = k + (9 + (if c then 0 else 1)) by
      cases c <;> rfl]
    exact AxSpinPO6.rowShPNowr k _ _ jw _ pa w HR
      (by cases c <;> exact Nat.le_of_ble_eq_true rfl) HF
  obtain ⟨_, HdaL_ra, Hh_ra, Hpr_ra, Hnt_ra⟩ := Bra
  obtain ⟨_, HdaL_s0, Hh_s0, Hpr_s0, Hnt_s0⟩ := Bs0
  have HNW := AxSpinPO6.ppShNowr c (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn) (paZ Pi)
    D_ra_s0 D_ra_mra D_ra_ms0 D_ra_n D_s0_mra D_s0_ms0 D_s0_n
  have Hktk : ∀ j, j ≤ 1 → k + j < k + 8 + (if c then 0 else 1) := by
    intro j hj; split <;> omega
  iapply (wpdPpTailP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxq Ψ HΨmid
    (k + 8 + (if c then 0 else 1)) rs1 ib1 ret Pra Ps0 k (k + 1) _ _ cra cs0 HRt
    Hnr_ra Hnr_s0
    Hkra Hlra (Hktk 0 (by omega))
    (NW 0 (paZ Pra) 8 HNW.1)
    Hks0 Hls0 (Hktk 1 (by omega))
    (NW 1 (paZ Ps0) 8 HNW.2)
    Hc1 HPC1 (hitWAgree rs0 rs1 _ Htl1 Hhit0)
    (by rw [Esp1]; exact HdaL_ra) (by rw [Esp1]; exact hitWAgree rs0 rs1 _ Htl1 Hh_ra)
    (by rw [Esp1]; exact HdaL_s0) (by rw [Esp1]; exact hitWAgree rs0 rs1 _ Htl1 Hh_s0)
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hvalr Hret
    (fun k' h1 h2 h3 pr => HΨend k' (by omega) h2 (by omega)
      (fun hc => by have := Htk9 hc; omega) h3 pr))
  iintro %vra' %vs0' %rs' %ib' %Hf H0 H1
  obtain ⟨Hcr, HPCr, Htlr, Espr, -, -, Hrar, Hs0r, Hkeepr, Hgv0, Hgv1⟩ := Hf
  iapply C $$ %vn %vi %vra' %vs0' %rs' %ib' [] H0 H1 HaN HaI
  ipureintro
  refine ⟨Hcr, HPCr, Htlr.trans Htl1, ?_, ?_, Hrar, Hs0r, ?_, Hgd0, Hgd1, Hgv6, Hge, Hgd7, Hcc,
    Hmid, Hgv0, Hgv1⟩
  · -- sp restored (Rocq `frame_cancel_16`)
    rw [Espr, Esp1]
    exact AxSpinE8.frameCancel16 _
  · -- a0 = mycpuRet tp
    rw [Hkeepr AxSpinE8.r10 (by decide) (by decide) (by decide)]
    exact Ea01
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr10 Hr15
    rw [Hkeepr r Hr1 Hr2 Hr8]
    exact Hkeep1 r Hr1 Hr2 Hr8 Hr10 Hr15

include HL Hcons hmode hasid hppn Hfix Htxm Htxq HΨmid in
/-- Rocq `wpd_pop_off` (deviation 1: Stage C positions; the callees' value pins replace the
`fpin` premises; new length premise `tk + 2 < row.length`).  Stage 2: the full-row corollary of
`wpdPopOffP` (no reload claimed, `rlN = rlI = none`; the hook and both cut arms are vacuous under
`tk + 2 < LEN`; the pins unguarded). -/
theorem wpdPopOff (k : Nat) (c : Bool) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 Pmra Pms0 Pn Pi : BitVec 64) :
    -- the row
    RowSh k (AxOpsem.grow (gtAdGd GT) i)
      (ppSh c (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn) (paZ Pi)) →
    k + 8 + (if c then 0 else 1) + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0 → hitW rs0 (ppp 0) → hitW rs0 (pcm 0) →
    -- the slots and the cpu fields
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    alldj [(paZ Pra, 8), (paZ Ps0, 8), (paZ Pmra, 8), (paZ Pms0, 8), (paZ Pn, 4)] →
    -- the value pins (Q20': the callees' returns and arms; deviation 1)
    graphValue (gtAdGd GT) (i, k + 4) = some (stBytes 8 (ppp 0x0c)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
      zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = c) →
    (c = false → ∀ vi, graphValue (gtAdGd GT) (i, k + 8) = some vi →
      (ldRes false 4 vi == zero_reg) = true) →
    graphValue (gtAdGd GT) (i, k + 8 + (if c then 0 else 1)) = some (stBytes 8 ret) →
    jalrTgt 0#12 ret = ret →
    ⊢ (∀ (vn vi vra' vs0' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 6) = some vn ∧
          zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false ∧
          graphData (gtAdGd GT) (i, k + 7) = some (stBytes 4 (addiwm1 (ldRes false 4 vn))) ∧
          (addiwm1 (ldRes false 4 vn) != zero_reg) = c ∧
          (c = false → graphValue (gtAdGd GT) (i, k + 8) = some vi ∧
            (ldRes false 4 vi == zero_reg) = true) ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if c then 0 else 1)) = some vra' ∧
          graphValue (gtAdGd GT) (i, k + 8 + (if c then 0 else 1) + 1) = some vs0'⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8 + (if c then 0 else 1))
          iprop(⌜RLfact GT i (paZ Pra) (k + 8 + (if c then 0 else 1))
            (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 8 + (if c then 0 else 1) + 1)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 8 + (if c then 0 else 1) + 1)
            (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 8 + (if c then 0 else 1) + 2⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hlen Hw8 Hnr_ra Hnr_s0 Hnr_mra Hnr_ms0 Hwle_n Hnrn Hnri Hc0 HPC0 Hhit0 HhitM
    Bra Bs0 Bmra Bms0 Bn Bi Hdj Hval0c Hvge Hvc Hvz Hvalr Hret
  have Htk0 : (if c then 0 else 1) ≤ 1 := by split <;> omega
  iintro C
  iapply (wpdPopOffP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxq Ψ HΨmid
    k c rs0 ib0 ret Pra Ps0 Pmra Pms0 Pn Pi none none (rowShPOfSh HR) Hw8 Hnr_ra Hnr_s0 Hnr_mra
    Hnr_ms0 Hwle_n Hnrn Hnri Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bmra Bms0 Bn Bi Hdj (fun _ => Hval0c)
    (fun _ => Hvge) Hvc (fun hc _ => Hvz hc) (fun _ => Hvalr) Hret trivial (fun _ => trivial)
    (fun _ _ h2 _ _ h5 => absurd h5 (by omega)) (fun h => absurd h (by omega))
    (fun _ h => absurd h (by omega)))
  iintro %vn %vi %vra' %vs0' %rs' %ib' %H H0 H1 - -
  iapply C $$ %vn %vi %vra' %vs0' %rs' %ib' %H H0 H1

end popoff

end Weak
