/-
Weak: **row 6m (W11-F B5), increment C3 — the per-site READ DATUM of the twin walk, and its named
per-site premises** (`notes/W10-6m-census.md`; `PROGRESS-W11F-6i6m.md` Task C).  Lean-only, no Rocq
twin.  Root of the `SilSite*` leaves (`SilSiteTab`: the census table; `SilSiteTaint`: the static walk).

**The datum** (`readDatum`): at a walk-invariant state of `SilOrd.hartStepRIS` (`stepCtx`), a graph
plain load either AGREES with the twin (`valAgree`: its values are readable by the hart at the twin's
current state — the twin step re-indexes it) or is a POISON-SAFE census site (`poisonOk`): its block's
instruction is a row of `tTabAll` (`blockPc`: the address of the star's last fetch), the twin reads some
readable `vs'` instead, and `vs, vs'` satisfy the site's VALUE RULE (`vRule`) — exactly what the static
walk `SilSiteTaint.siteOk` assumed (the differing bits within the site's mask; the same arm at the rule
branches; agreement after the rule kills).  `tTabAllOk` decides the walk for every such row.

**The premises** (`atSteps Q`: `Q` at every step of the walk's quantifier), one family per route:
  * ORDER (row 6l discharges): `ordQ pinRdK` — `main+0x16` (`started`) and the four
    `virtio_disk_intr` reads AGREE; `devQ` — the device program's reads agree; `silentQ` — a failed
    acquire has its silent window; `rmwQ` — a successful AMO reads the twin's latest bytes (the lock co
    transport, from `ordCoSP`);
  * VALUE (order-free STATIC part proved in `SilSiteTaint`; the rule premise named here): `valQ` — at a
    `tTabAll` site the twin has a readable `vs'` with `vRule` (or agrees).  Its discharge per site:
    by agreement (`vRuleRefl`: ANY order route discharges it), or two-sided value facts
    (`ruleOfLkCpuNe`, `ruleOfLkCpuEq`, `ruleOfLockedSet`, `ruleOfIrefPos`, `ruleOfPteAd`,
    `ruleOfPteWalk`);  `noPanicQ` — no row block lies in `panic`/`unreachable` (`walkaddr+0x1c`'s
    `stop` rule);
  * CUSTODY (Q-6M-PTE): `custQ` — `uvmcopy+0x36`, `uvmclear+0x10` agree;
  * RACE-FREE (the chain-based race-free-read theorem, census §5): `drfQ` — every other hart load.
**`readDatumOf`**: the premises give the datum at every step.

**Guards** (`guardsOk`, `decide +kernel`): every benign-race site's BAD outcome is a branch arm that
reaches `unreachable` in straight line (`acquire`'s `holding` check, `release`'s, `sched`'s,
`ilock`'s and `iunlock`'s `ref < 1` checks) — so the GRAPH side of every value rule except the PTE
ones is "the graph's row does not take a panic arm" (PROGRESS, Q-6M-GFVAL).

What is NOT here: the twin port of `CertZ13.hartStepOfSite` that consumes `readDatum` (a value-aware
`csync`, the Sail-level meaning of `siteOk`), and the discharge of any premise.

Spec: FAITHFUL (proof organisation; every premise is a per-read fact of the walk, none is a memory-model
choice).  Lean-only helpers `SilSite.*`.
-/
import Weak.SilSiteTaint
import Weak.SilOrd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow
open KernelPinsDef

namespace SilSite

/-! ## 1. The block's pc and agreement at the twin -/

/-- The address of the star's LAST fetch: the block's realizing instruction. -/
def blockPc : List Wlabel → Option Int
  | [] => none
  | l :: ls =>
      match blockPc ls with
      | some p => some p
      | none =>
          match l with
          | .LIFetch base _ => some base
          | _ => none

/-- The twin's current machine state. -/
def cur (S : SilWalk.St) : Mstate := SilCand.stAt S.c S.c.tr.length

/-- Hart `x` can read the bytes `vs` at `base` in the twin's current state (some timestamps). -/
def readsAt (S : SilWalk.St) (x : Nat) (aq : Bool) (base : Int) (vs : List (BitVec 8)) : Prop :=
  ∃ ts', rdOk (cur S).msImg (cur S).msLog ((cur S).msWs x) aq base ts' vs

/-- **READ AGREEMENT**: the graph load's values are readable by the hart at the twin. -/
def valAgree (S : SilWalk.St) (x : Nat) (lb : Lbl) : Prop :=
  ∀ aq base ts vs, lb = .LLoad aq base ts vs → readsAt S x aq base vs

/-! ## 2. The value rules -/

/-- Little-endian value of a byte list. -/
def leNat : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- A 32-bit word is positive as a signed value (`blez` NOT taken). -/
def pos32 (vs : List (BitVec 8)) : Prop := 0 < leNat vs ∧ leNat vs < 2 ^ 31

/-- The two PTEs differ at most in bits 6, 7 (A/D) of the low byte. -/
def adOnly (vs vs' : List (BitVec 8)) : Prop :=
  vs.length = vs'.length ∧
  ∀ (i : Nat) (b b' : BitVec 8), vs[i]? = some b → vs'[i]? = some b' →
    (i = 0 → b &&& 0x3F#8 = b' &&& 0x3F#8) ∧ (i ≠ 0 → b = b')

/-- An invalid PTE (V = 0 on both sides) agrees (A/D are clear on an invalid PTE). -/
def vzAgree (vs vs' : List (BitVec 8)) : Prop :=
  ∀ b b', vs[0]? = some b → vs'[0]? = some b' → b.getLsbD 0 = false → b'.getLsbD 0 = false → b = b'

/-- The rule kinds of the static walk's rows. -/
inductive Kind where
  /-- `holding+0x0`: the `bnez` arm -/
  | locked
  /-- `holding+0x12`: `seqz (v - me)` -/
  | lkCpu
  /-- `ilock+0xe`, `iunlock+0x1c`: the `blez` arm -/
  | iref
  /-- `walk+0x32`: A/D only, and an invalid PTE agrees -/
  | pteWalk
  /-- the other PTE rows: A/D only -/
  | pte
  deriving DecidableEq, Repr

/-- The value rule of a kind (`me`: the hart's own `&cpus[...]`). -/
def vRuleK (k : Kind) (me : Nat) (vs vs' : List (BitVec 8)) : Prop :=
  match k with
  | .locked => (leNat vs = 0 ↔ leNat vs' = 0)
  | .lkCpu => (leNat vs = me ↔ leNat vs' = me)
  | .iref => (pos32 vs ↔ pos32 vs')
  | .pteWalk => adOnly vs vs' ∧ vzAgree vs vs'
  | .pte => adOnly vs vs'

/-- The rows of `tTabAll` with their kinds. -/
def kindTab : List (Int × Kind) :=
  [ (sym KernelSyms.«holding» 0x0, .locked)
  , (sym KernelSyms.«holding» 0x12, .lkCpu)
  , (sym KernelSyms.«ilock» 0xe, .iref)
  , (sym KernelSyms.«iunlock» 0x1c, .iref)
  , (sym KernelSyms.«walk» 0x32, .pteWalk)
  , (sym KernelSyms.«walkaddr» 0x1c, .pte)
  , (sym KernelSyms.«mappages» 0x4a, .pte)
  , (sym KernelSyms.«uvmunmap» 0x5e, .pte)
  , (sym KernelSyms.«freewalk» 0x2a, .pte)
  , (sym KernelSyms.«ismapped» 0x10, .pte)
  , (sym KernelSyms.«copyout» 0x82, .pte) ]

theorem kindTabSites : kindTab.map Prod.fst = tTabAll.map Prod.fst := by decide +kernel

/-- The PTE rows carry the A/D mask, the others the full one (the walk's start masks). -/
theorem kindTabMask :
    (kindTab.zip tTabAll).all (fun p =>
      match p.1.2 with
      | .pteWalk | .pte => p.2.2.1 == adMask
      | _ => p.2.2.1 == FULL) = true := by
  decide +kernel

def kindOf (pc : Int) : Option Kind := (kindTab.find? (fun p => p.1 == pc)).map Prod.snd

/-- **THE VALUE RULE** of a pc (`True` off the table). -/
def vRule (pc : Int) (me : Nat) (vs vs' : List (BitVec 8)) : Prop :=
  match kindOf pc with
  | some k => vRuleK k me vs vs'
  | none => True

/-- Every rule is REFLEXIVE: an agreeing read meets it (so ANY route that makes the read agree — the
order included — discharges the site's value premise). -/
theorem vRuleRefl (pc : Int) (me : Nat) (vs : List (BitVec 8)) : vRule pc me vs vs := by
  unfold vRule
  generalize kindOf pc = o
  cases o with
  | none => trivial
  | some k =>
    cases k with
    | locked => exact Iff.rfl
    | lkCpu => exact Iff.rfl
    | iref => exact Iff.rfl
    | pteWalk =>
      show adOnly vs vs ∧ vzAgree vs vs
      refine ⟨⟨rfl, fun i b b' h h' => ?_⟩, fun b b' h h' _ _ => ?_⟩
      · rw [h] at h'; cases h'; exact ⟨fun _ => rfl, fun _ => rfl⟩
      · rw [h] at h'; cases h'; rfl
    | pte =>
      show adOnly vs vs
      refine ⟨rfl, fun i b b' h h' => ?_⟩
      rw [h] at h'; cases h'; exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem kindHold0 : kindOf (sym KernelSyms.«holding» 0x0) = some .locked := by decide +kernel
theorem kindHold12 : kindOf (sym KernelSyms.«holding» 0x12) = some .lkCpu := by decide +kernel
theorem kindIlock : kindOf (sym KernelSyms.«ilock» 0xe) = some .iref := by decide +kernel
theorem kindIunlock : kindOf (sym KernelSyms.«iunlock» 0x1c) = some .iref := by decide +kernel
theorem kindWalk : kindOf (sym KernelSyms.«walk» 0x32) = some .pteWalk := by decide +kernel

/-! ### The census value arguments discharge the rules -/

/-- `holding+0x12` from `acquire` ([OWN.64]): neither value is the hart's own `&cpus[...]`. -/
theorem ruleOfLkCpuNe (me : Nat) (vs vs' : List (BitVec 8)) :
    leNat vs ≠ me → leNat vs' ≠ me → vRule (sym KernelSyms.«holding» 0x12) me vs vs' := by
  intro h h'
  unfold vRule
  rw [kindHold12]
  show (leNat vs = me ↔ leNat vs' = me)
  exact ⟨fun e => absurd e h, fun e => absurd e h'⟩

/-- `holding+0x12` from `release`/`sched` (the holder): both values are the hart's own. -/
theorem ruleOfLkCpuEq (me : Nat) (vs vs' : List (BitVec 8)) :
    leNat vs = me → leNat vs' = me → vRule (sym KernelSyms.«holding» 0x12) me vs vs' := by
  intro h h'
  unfold vRule
  rw [kindHold12]
  show (leNat vs = me ↔ leNat vs' = me)
  exact ⟨fun _ => h', fun _ => h⟩

/-- `holding+0x0` from `release`/`sched` (the holder): both values are non-zero. -/
theorem ruleOfLockedSet (me : Nat) (vs vs' : List (BitVec 8)) :
    leNat vs ≠ 0 → leNat vs' ≠ 0 → vRule (sym KernelSyms.«holding» 0x0) me vs vs' := by
  intro h h'
  unfold vRule
  rw [kindHold0]
  show (leNat vs = 0 ↔ leNat vs' = 0)
  exact ⟨fun e => absurd e h, fun e => absurd e h'⟩

/-- `ilock+0xe` / `iunlock+0x1c` ([OWN.63]): both values are ≥ 1. -/
theorem ruleOfIrefPos (pc : Int) (me : Nat) (vs vs' : List (BitVec 8)) :
    pc = sym KernelSyms.«ilock» 0xe ∨ pc = sym KernelSyms.«iunlock» 0x1c →
    pos32 vs → pos32 vs' → vRule pc me vs vs' := by
  intro hpc h h'
  unfold vRule
  rcases hpc with rfl | rfl
  · rw [kindIlock]; show (pos32 vs ↔ pos32 vs'); exact ⟨fun _ => h', fun _ => h⟩
  · rw [kindIunlock]; show (pos32 vs ↔ pos32 vs'); exact ⟨fun _ => h', fun _ => h⟩

/-- The A/D-only PTE rows. -/
theorem ruleOfPteAd (pc : Int) (me : Nat) (vs vs' : List (BitVec 8)) :
    kindOf pc = some .pte → adOnly vs vs' → vRule pc me vs vs' := by
  intro hk h
  unfold vRule
  rw [hk]
  exact h

/-- `walk+0x32`: A/D only, and an invalid PTE agrees. -/
theorem ruleOfPteWalk (me : Nat) (vs vs' : List (BitVec 8)) :
    adOnly vs vs' → vzAgree vs vs' → vRule (sym KernelSyms.«walk» 0x32) me vs vs' := by
  intro h h'
  unfold vRule
  rw [kindWalk]
  show adOnly vs vs' ∧ vzAgree vs vs'
  exact ⟨h, h'⟩

/-! ## 3. The read datum -/

def tPcsAll : List Int := tTabAll.map Prod.fst

/-- **THE POISON-SAFE ARM**: a plain load at a `tTabAll` row, read by the twin as `vs'` within the
site's value rule. -/
def poisonOk (S : SilWalk.St) (x : Nat) (me : Nat) (lb : Lbl) (ls : List Wlabel) : Prop :=
  ∃ (pc : Int) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
    blockPc ls = some pc ∧ pc ∈ tPcsAll ∧ lb = .LLoad false base ts vs ∧
    ∃ vs', readsAt S x false base vs' ∧ vRule pc me vs vs'

/-- **THE PER-STEP READ DATUM**: a graph load agrees or is poison-safe. -/
def readDatum (S : SilWalk.St) (x : Nat) (me : Nat) (lb : Lbl) (ls : List Wlabel) : Prop :=
  (∃ aq base ts vs, lb = .LLoad aq base ts vs) → valAgree S x lb ∨ poisonOk S x me lb ls

/-! ## 4. The walk's quantifier and the named premises -/

/-- The hypotheses of `SilOrd.hartStepRIS` at one step (a walk-invariant twin state, the next event
`L[k] = (x, n)` with label `lb` and block `ls`/`l`). -/
def stepCtx (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (S : SilWalk.St) (x n : Nat) (lb : Lbl) (ws : Wstate) (ls : List Wlabel)
    (l : Wlabel) (pE pE' pC : Pexv6) (d' : Efab) (k : Nat) : Prop :=
  SilWalk.ok d0 S ∧
  (S.pst S.c.tr.length)[x]? = some pC ∧ Rel x n pE pC ∧ CertZ4.lblShape lb ∧
  ((lbFused l ∧ GraphFetchBlocks.blkOne (S.dv S.c.tr.length) d' ws lb ls l pE pE') ∨
    GraphFetchBlocks.blkPair (S.dv S.c.tr.length) d' ws lb ls l pE pE') ∧
  S.c.tr.map Estep.esAg = (L.take k).map Prod.fst ∧
  L[k]? = some (x, n) ∧
  (∀ y, y < rows.length →
    List.Forall₂ (SilWalk.relW Lb)
      ((rows.getD y []).take (((L.take k).filter (fun e => decide (e.1 = y))).length))
      (SilWalk.hartPr (SilOrd.pairs S) y)) ∧
  (rows.getD x [])[n]? = some lb

/-- `Q` at every step of the walk's quantifier. -/
def atSteps (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (Q : SilWalk.St → Nat → Lbl → List Wlabel → Prop) : Prop :=
  ∀ (S : SilWalk.St) (x n : Nat) (lb : Lbl) (ws : Wstate) (ls : List Wlabel) (l : Wlabel)
    (pE pE' pC : Pexv6) (d' : Efab) (k : Nat),
    stepCtx d0 rows Lb L Rel S x n lb ws ls l pE pE' pC d' k → Q S x lb ls

/-- The ORDER-pinned kernel reads other than `holding+0x0` (whose `acquire` context is a value-rule
premise discharged by agreement, `vRuleRefl`). -/
def pinRdK : List Int := pinRd.tail

theorem pinRdKEq :
    pinRdK = [ sym KernelSyms.«main» 0x16
             , sym KernelSyms.«virtio_disk_intr» 0x36, sym KernelSyms.«virtio_disk_intr» 0x4e
             , sym KernelSyms.«virtio_disk_intr» 0x5a, sym KernelSyms.«virtio_disk_intr» 0x82 ] :=
  rfl

/-- The NOT-taint-dischargeable rows (route N). -/
def nPcs : List Int := (kSites.filter (fun s => s.route == .noTaint)).map Site.pc

/-- Every census pc is in exactly the lists the datum splits on. -/
theorem censusSplit :
    kSites.all (fun s =>
      decide (s.pc ∈ pinRdK) || decide (s.pc ∈ tPcsAll) || decide (s.pc ∈ nPcs)) = true := by
  decide +kernel

/-- **ORDER (P)**: a hart load whose block is at a pc of `P` agrees. -/
def ordQ (P : Int → Prop) (isDev : Nat → Prop) : SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb ls => ¬ isDev x → (∃ pc, blockPc ls = some pc ∧ P pc) → valAgree S x lb

/-- **ORDER (P), the device program**: a device read agrees (census §4). -/
def devQ (isDev : Nat → Prop) : SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb _ => isDev x → valAgree S x lb

/-- **VALUE (T/O)**: at a `tTabAll` row the twin agrees, or reads a `vs'` within the value rule
(`cpuOf x`: hart `x`'s own `&cpus[...]`). -/
def valQ (cpuOf : Nat → Nat) (isDev : Nat → Prop) :
    SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb ls => ¬ isDev x → ∀ pc, blockPc ls = some pc → pc ∈ tPcsAll →
    valAgree S x lb ∨ poisonOk S x (cpuOf x) lb ls

/-- **CUSTODY (N, Q-6M-PTE)**: `uvmcopy+0x36`, `uvmclear+0x10` agree. -/
def custQ (isDev : Nat → Prop) : SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb ls => ¬ isDev x → ∀ pc, blockPc ls = some pc → pc ∈ nPcs → valAgree S x lb

/-- **RACE-FREE (census §5)**: every other hart load agrees. -/
def drfQ (isDev : Nat → Prop) : SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb ls => ¬ isDev x →
    (∀ pc, blockPc ls = some pc → pc ∉ pinRdK ∧ pc ∉ tPcsAll ∧ pc ∉ nPcs) → valAgree S x lb

/-- **NO PANIC** (`walkaddr+0x1c`'s `stop` rule): no block lies in `panic`/`unreachable`. -/
def noPanicQ : SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun _ _ _ ls => ∀ pc, blockPc ls = some pc →
    fnOf pc ≠ (KernelSyms.«panic» : Int) ∧ fnOf pc ≠ (KernelSyms.«unreachable» : Int)

/-- **ORDER (P), the failed acquire**: its silent window exists. -/
def silentQ (Lb : Int → Prop) : SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb _ => CertZ24.lblFail Lb lb →
    ∀ aq base ts rvs wvs kc, lb = .LRmw aq false base ts rvs wvs kc →
      ∃ ts' q, SilCand.silentOk (cur S) x aq base ts' rvs wvs q

/-- **LOCK CO (from `ordCoSP`)**: a successful AMO reads the twin's latest bytes. -/
def rmwQ (Lb : Int → Prop) : SilWalk.St → Nat → Lbl → List Wlabel → Prop :=
  fun S x lb _ => ¬ CertZ24.lblFail Lb lb →
    ∀ aq rl base ts rvs wvs kc, lb = .LRmw aq rl base ts rvs wvs kc →
      ∃ ts', rdOk (cur S).msImg (cur S).msLog ((cur S).msWs x) aq base ts' rvs ∧
        rmwLatest (cur S).msImg (cur S).msLog base ts'

/-! ## 5. The datum from the premises -/

/-- **`readDatumOf`** — the premises of every route give the read datum at every step. -/
theorem readDatumOf (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (cpuOf : Nat → Nat) (isDev : Nat → Prop) :
    atSteps d0 rows Lb L Rel (ordQ (fun pc => pc ∈ pinRdK) isDev) →
    atSteps d0 rows Lb L Rel (devQ isDev) →
    atSteps d0 rows Lb L Rel (valQ cpuOf isDev) →
    atSteps d0 rows Lb L Rel (custQ isDev) →
    atSteps d0 rows Lb L Rel (drfQ isDev) →
    atSteps d0 rows Lb L Rel (fun S x lb ls => readDatum S x (cpuOf x) lb ls) := by
  intro hord hdev hval hcust hdrf S x n lb ws ls l pE pE' pC d' k hctx _
  by_cases hd : isDev x
  · exact .inl (hdev S x n lb ws ls l pE pE' pC d' k hctx hd)
  · cases hb : blockPc ls with
    | none =>
      refine .inl (hdrf S x n lb ws ls l pE pE' pC d' k hctx hd (fun pc hpc => ?_))
      rw [hb] at hpc
      cases hpc
    | some pc =>
      by_cases h1 : pc ∈ pinRdK
      · exact .inl (hord S x n lb ws ls l pE pE' pC d' k hctx hd ⟨pc, hb, h1⟩)
      · by_cases h2 : pc ∈ tPcsAll
        · exact hval S x n lb ws ls l pE pE' pC d' k hctx hd pc hb h2
        · by_cases h3 : pc ∈ nPcs
          · exact .inl (hcust S x n lb ws ls l pE pE' pC d' k hctx hd pc hb h3)
          · refine .inl (hdrf S x n lb ws ls l pE pE' pC d' k hctx hd (fun pc' hpc' => ?_))
            rw [hb, Option.some.injEq] at hpc'
            subst hpc'
            exact ⟨h1, h2, h3⟩

/-- An AGREEING value premise (any route that makes the census reads agree, the order included)
discharges `valQ`. -/
theorem valQOfAgree (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (cpuOf : Nat → Nat) (isDev : Nat → Prop) :
    atSteps d0 rows Lb L Rel (fun S x lb ls =>
      ¬ isDev x → ∀ pc, blockPc ls = some pc → pc ∈ tPcsAll → valAgree S x lb) →
    atSteps d0 rows Lb L Rel (valQ cpuOf isDev) :=
  fun h S x n lb ws ls l pE pE' pC d' k hctx hd pc hb hm =>
    .inl (h S x n lb ws ls l pE pE' pC d' k hctx hd pc hb hm)

/-- The two-sided form: at a `tTabAll` row the twin reads SOME `vs'` within the rule (the value
arguments `ruleOf*`). -/
theorem valQOfRule (d0 : Efab) (rows : List (List Lbl)) (Lb : Int → Prop) (L : List Geid)
    (Rel : CertZ9.HRel) (cpuOf : Nat → Nat) (isDev : Nat → Prop) :
    atSteps d0 rows Lb L Rel (fun S x lb ls =>
      ¬ isDev x → ∀ pc, blockPc ls = some pc → pc ∈ tPcsAll →
        ∀ aq base ts vs, lb = .LLoad aq base ts vs →
          aq = false ∧ ∃ vs', readsAt S x false base vs' ∧ vRule pc (cpuOf x) vs vs') →
    atSteps d0 rows Lb L Rel (valQ cpuOf isDev) := by
  intro h S x n lb ws ls l pE pE' pC d' k hctx hd pc hb hm
  by_cases hl : ∃ aq base ts vs, lb = .LLoad aq base ts vs
  · obtain ⟨aq, base, ts, vs, rfl⟩ := hl
    obtain ⟨rfl, vs', hr, hv⟩ := h S x n _ ws ls l pE pE' pC d' k hctx hd pc hb hm aq base ts vs rfl
    exact .inr ⟨pc, base, ts, vs, hb, hm, rfl, vs', hr, hv⟩
  · exact .inl (fun aq base ts vs he => absurd ⟨aq, base, ts, vs, he⟩ hl)

/-! ## 6. The panic guards of the benign races -/

/-- A straight-line run from `pc` reaches a call of `unreachable`/`panic`. -/
def toUnreach : Nat → Int → Bool
  | 0, _ => false
  | f + 1, pc =>
      match kflowOf pc with
      | .FLnone => toUnreach f (pc + wSize (kw pc))
      | .FLjump tgt => toUnreach f tgt
      | .FLcall tgt => stopPcs.contains tgt
      | _ => false

/-- The arm of the branch at `pc` (`taken` or the fall-through). -/
def armOf (pc : Int) (taken : Bool) : Int :=
  match kflowOf pc with
  | .FLbranch tgt => if taken then tgt else pc + wSize (kw pc)
  | _ => pc

/-- The guarded branches and their BAD arm: `acquire`'s `bnez a0` (holding ⇒ panic), `release`'s and
`sched`'s `beqz a0` (not holding ⇒ panic), `ilock`'s and `iunlock`'s `blez a5` (`ref < 1` ⇒ panic). -/
def guards : List (Int × Bool) :=
  [ (sym KernelSyms.«acquire» 0x18, true), (sym KernelSyms.«release» 0x10, true)
  , (sym KernelSyms.«sched» 0x18, true), (sym KernelSyms.«ilock» 0x10, true)
  , (sym KernelSyms.«iunlock» 0x1e, true) ]

/-- **EVERY BENIGN RACE IS PANIC-GUARDED**: each guard is a branch whose bad arm reaches a call of
`unreachable` in straight line. -/
theorem guardsOk :
    guards.all (fun g =>
      (match kflowOf g.1 with
       | .FLbranch _ => true
       | _ => false) && toUnreach 8 (armOf g.1 g.2)) = true := by
  decide +kernel

end SilSite

end Weak
