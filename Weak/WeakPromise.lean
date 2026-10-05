/-
Weak: **the FULL promising machine** (M6 W1, slice 1).

Rocq: `iris/WeakPromise.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, in substance: the native restatement of the Promising-RISC-V
machine (`claude-notes/projects/weak-memory-m6.md` W1, D-M6-3/4/5): `WeakMem`'s
promise-free view machine EXTENDED with per-agent promise sets, so that the
robustness theorem (W2) can be stated inside this tree.  Correspondence to
snu-sf/promising-arm (@10291375, `Promising.v`) is BY INSPECTION per D-M6-3.
DELIBERATELY DEPENDENCY-FREE (stdpp shims only).  Agents are `Nat`s indexing a
list (harts AND the disk agent, D-M6-4); programs are an ABSTRACT per-agent LTS
over labels.  THE DELIBERATE DELTAS from PARM: no register views in the fulfil
pre-view beyond `wVcap` (a LOWER bound of PARM's, D-M6-5); the fused `LRmw`
event carries PARM's store-exclusive window as `exclOk`; byte granularity with
whole-message promises (exact fulfil match); `lat` reads read the latest
message of the whole log, promises included.  Slice 2 (the front-loading
factorization) is `Weak/WeakPromiseFact.lean`.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1 (lowerCamelCase of the Rocq
   name; types UpperCamelCase: `wlabel` ↦ `Wlabel`, `wpagent` ↦ `Wpagent`,
   `wpcfg` ↦ `Wpcfg`; fields `pa_st` ↦ `paSt`, `pc_log` ↦ `pcLog`, ...;
   constructors keep their Rocq spelling: `LSilent` … `LExStore`, and the
   machine arms `WPPromise` … `WPExStore` are `wpstep.WPPromise` …).  The record
   constructors `WPAgent st ws pr` / `WPCfg img log d ags` are the structures'
   `mk` (`⟨st, ws, pr⟩`, `⟨img, log, d, ags⟩`).  The Rocq notation `WPCfgU img
   log ags` is the abbreviation `WPCfgU`.
2. VOCABULARY: as `WeakMem` deviation 2, plus `gset nat` ↦ `GSet Nat`,
   `{[x]}` ↦ `{x}`, `∖` ↦ `\`, `<[i:=x]> l` ↦ `l.set i x`, `tvs.*1` ↦
   `tvs.map Prod.fst`, `rtc` ↦ `MachCSL.rtc`.
3. `ad_byte0`'s `Z.testbit (bv_unsigned d) (Z.of_nat i)` is
   `d.toNat.testBit i` (the same bit: `bv_unsigned` is the non-negative
   `toNat`).
4. `fulfil_vpre_d_0` is propositional (`Nat.zero_max`; `WeakMem` deviation 3).
   `read_ok_d_0`, `fulfil_ok_d_0` stay `rfl`.
5. `(1 ≤ j < n)` is `1 ≤ j ∧ j < n`.
6. Name exceptions: `wpstep` (a Prop-valued inductive) keeps its lower-case
   name.  Lean-only helpers (no Rocq twin): `lookupSetCases` (lookup in
   `l.set i x`), `cfgWfSet` (the common shape of `cfg_wf_step`'s eleven state
   arms), `promWfDiff`, and the private `memSingletonUnion`, `promAddDel` (the
   `set_solver` facts of the fused derivations, stated in a small context:
   `set_solver`'s `grind` over the whole proof context timed out there).
7. `lb_ldepfree` / `lb_fused` are written with a wildcard arm for the
   constructors Rocq lists one by one (same truth value per constructor).

**Not ported:** nothing.

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakMem

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## Labels: the event alphabet an agent's program emits -/

/-- The label carries the memory system's ANSWERS (timestamps and values read).
Multi-byte accesses are contiguous runs at `base`.  `LDev` is the fabric marker
(a silent-effect label); `LRegW`/`LCtrl`/`LInstr` are the dependency-only labels
(D2); `LExLoad`/`LExStore` the two halves of the RMW split. -/
inductive Wlabel where
  | LSilent
  | LLoad (aq lat : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc)
  | LStore (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
  | LRmw (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc)
  | LFence (pr pw sr sw : Bool)
  | LDev
  | LRegW (rd : Nat) (srcs : List Dsrc)
  | LCtrl (srcs : List Dsrc)
  | LInstr
  | LExLoad (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc)
  | LExStore (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)

open Wlabel

/-- THE DEPENDENCY-FREE FRAGMENT OF THE LABEL ALPHABET. -/
def lbDepfree (l : Wlabel) : Prop :=
  match l with
  | LSilent | LFence .. | LDev => True
  | LLoad _ _ _ _ asrc => asrc = []
  | LStore _ _ _ asrc vsrc => asrc = [] ∧ vsrc = []
  | LRmw _ _ _ _ _ asrc vsrc => asrc = [] ∧ vsrc = []
  | LRegW .. | LCtrl _ | LInstr => False
  | LExLoad _ _ _ asrc => asrc = []
  | LExStore _ _ _ asrc vsrc => asrc = [] ∧ vsrc = []

/-- D3-2: THE WEAKER PIN THE EVENT INSTANCE ACTUALLY SATISFIES (loads carry no
address operands). -/
def lbLdepfree (l : Wlabel) : Prop :=
  match l with
  | LLoad _ _ _ _ asrc => asrc = []
  | _ => True

theorem lbDepfreeLdepfree (l : Wlabel) : lbDepfree l → lbLdepfree l := by
  cases l <;> simp [lbDepfree, lbLdepfree]

/-- THE FUSED FRAGMENT OF THE LABEL ALPHABET (RMW split S2). -/
def lbFused (l : Wlabel) : Prop :=
  match l with
  | LExLoad .. | LExStore .. => False
  | _ => True

/-! ## Per-agent state and configurations -/

/-- `Wstate` plus the promise set (PARM `Local.promises`). -/
structure Wpagent (P : Type) where
  paSt : P
  paWs : Wstate
  paProm : GSet Nat

/-- A configuration: the image, the write log, the device fabric, the agents. -/
structure Wpcfg (P D : Type) where
  pcImg : Image
  pcLog : List Wmsg
  pcDev : D
  pcAgs : List (Wpagent P)

/-! ## Side conditions -/

/-- The fulfil pre-view (PARM `writable`'s `view_pre`, minus the label part). -/
def fulfilVpre (ws : Wstate) (rl : Bool) : Nat :=
  max ws.wVcap (max ws.wVwNew (if rl then max ws.wVrOld ws.wVwOld else 0))

theorem fulfilVpreBounded (ws : Wstate) (rl : Bool) (n : Nat) :
    wsBounded ws n → fulfilVpre ws rl ≤ n := by
  intro hb
  have hvc := wsBoundedVcap _ _ hb
  obtain ⟨hro, hwo, _, hwn, _⟩ := hb
  simp only [fulfilVpre]; split <;> omega

/-- The label half `vd`. -/
def fulfilVpreD (ws : Wstate) (rl : Bool) (vd : Nat) : Nat := max vd (fulfilVpre ws rl)

theorem fulfilVpreD0 (ws : Wstate) (rl : Bool) : fulfilVpreD ws rl 0 = fulfilVpre ws rl :=
  Nat.zero_max _

theorem fulfilVpreDVwNew (ws : Wstate) (rl : Bool) (vd : Nat) : ws.wVwNew ≤ fulfilVpreD ws rl vd := by
  simp only [fulfilVpreD, fulfilVpre]; omega

theorem fulfilVpreDVd (ws : Wstate) (rl : Bool) (vd : Nat) : vd ≤ fulfilVpreD ws rl vd :=
  Nat.le_max_left _ _

theorem fulfilVpreDBounded (ws : Wstate) (rl : Bool) (vd n : Nat) :
    wsBounded ws n → vd ≤ n → fulfilVpreD ws rl vd ≤ n := by
  intro hb hvd
  have := fulfilVpreBounded ws rl n hb
  simp only [fulfilVpreD]; omega

/-- `writesInBy log Q a lo hi`: `writesIn` refined by author. -/
def writesInBy (log : List Wmsg) (Q : Option Nat → Prop) (a : Int) (lo hi : Nat) : Prop :=
  ∃ t : Nat, lo < t ∧ t ≤ hi ∧
    ∃ m, log[t - 1]? = some m ∧ (msgByte m a).isSome ∧ Q m.wmTid

theorem writesInByWritesIn (log : List Wmsg) (Q : Option Nat → Prop) (a : Int) (lo hi : Nat) :
    writesInBy log Q a lo hi → writesIn log a lo hi := by
  rintro ⟨t, h1, h2, m, hm, hs, _⟩
  exact ⟨t, h1, h2, m, hm, hs⟩

/-- The read half of a load/rmw at address-dependency view `vaddr`. -/
def readOkD (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (vaddr : Nat) : Prop :=
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    logByte img log t (base + (j : Int)) = some v ∧
    readable img log ws (loadVpreD ws aq vaddr) (base + (j : Int)) t ∧
    (lat = true → ¬ writesIn log (base + (j : Int)) t log.length)

def readOk (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  readOkD img log ws aq lat base tvs 0

theorem readOkD0 (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    readOkD img log ws aq lat base tvs 0 = readOk img log ws aq lat base tvs := rfl

/-- A bigger address view only SHRINKS the admissible set. -/
theorem readOkDMono (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va va' : Nat) :
    va' ≤ va → readOkD img log ws aq lat base tvs va → readOkD img log ws aq lat base tvs va' := by
  intro hle hr j t v hj
  obtain ⟨h1, h2, h3⟩ := hr j t v hj
  refine ⟨h1, readableAntiVpre img log ws _ _ _ t ?_ h2, h3⟩
  simp only [loadVpreD]; omega

/-- The fulfil conditions at timestamp `ts` (COH per byte, EXT). -/
def fulfilOkD (ws : Wstate) (rl : Bool) (base : Int) (n ts vd : Nat) : Prop :=
  (∀ j, j < n → coh ws (base + (j : Int)) < ts) ∧ fulfilVpreD ws rl vd < ts

def fulfilOk (ws : Wstate) (rl : Bool) (base : Int) (n ts : Nat) : Prop :=
  fulfilOkD ws rl base n ts 0

theorem fulfilOkDMono (ws : Wstate) (rl : Bool) (base : Int) (n ts vd vd' : Nat) :
    vd' ≤ vd → fulfilOkD ws rl base n ts vd → fulfilOkD ws rl base n ts vd' := by
  rintro hle ⟨hcoh, hext⟩
  refine ⟨hcoh, ?_⟩
  simp only [fulfilVpreD] at hext ⊢; omega

theorem fulfilOkD0 (ws : Wstate) (rl : Bool) (base : Int) (n ts : Nat) :
    fulfilOkD ws rl base n ts 0 = fulfilOk ws rl base n ts := rfl

/-- PARM's `Memory.exclusive`. -/
def exclOk (log : List Wmsg) (i : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (ts : Nat) :
    Prop :=
  ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) →
    ¬ writesInBy log (fun tid => tid ≠ some i) (base + (j : Int)) t (ts - 1)

/-- `exclOk` over the reservation's timestamp column alone. -/
def exclOkTs (log : List Wmsg) (i : Nat) (base : Int) (rts : List Nat) (ts : Nat) : Prop :=
  ∀ (j t : Nat), rts[j]? = some t →
    ¬ writesInBy log (fun tid => tid ≠ some i) (base + (j : Int)) t (ts - 1)

theorem exclOkTsOfExclOk (log : List Wmsg) (i : Nat) (base : Int) (tvs : List (Nat × BitVec 8))
    (ts : Nat) : exclOk log i base tvs ts → exclOkTs log i base (tvs.map Prod.fst) ts := by
  intro he j t ht
  rw [List.getElem?_map] at ht
  cases hj : tvs[j]? with
  | none => rw [hj] at ht; cases ht
  | some p =>
    obtain ⟨t', v⟩ := p
    rw [hj] at ht; injection ht with ht; subst ht
    exact he j t' v hj

/-! ### The conditional write's whole side condition, and its boolean -/

def writesInByb (log : List Wmsg) (i : Nat) (a : Int) (lo hi : Nat) : Bool :=
  (List.range' 1 log.length).any (fun t =>
    decide (lo < t) && decide (t ≤ hi) &&
      match log[t - 1]? with
      | some m => msgWritesb m a && decide (m.wmTid ≠ some i)
      | none => false)

theorem writesInBybSpec (log : List Wmsg) (i : Nat) (a : Int) (lo hi : Nat) :
    writesInBy log (fun tid => tid ≠ some i) a lo hi ↔ writesInByb log i a lo hi = true := by
  unfold writesInByb writesInBy
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, hlo, hhi, m, hm, hs, hq⟩
    have hlt := lookup_lt_Some hm
    refine ⟨t, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
    rw [hm]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hlo, hhi⟩, (msgWritesbTrue m a).2 hs, hq⟩
  · rintro ⟨t, _, hb⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    revert h3
    cases hm : log[t - 1]? with
    | none => intro h3; cases h3
    | some m =>
      intro h3
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
      exact ⟨t, h1, h2, m, hm, (msgWritesbTrue m a).1 h3.1, h3.2⟩

def exclOkTsb (log : List Wmsg) (i : Nat) (base : Int) (rts : List Nat) (ts : Nat) : Bool :=
  (List.range' 0 rts.length).all (fun j =>
    match rts[j]? with
    | some t => !(writesInByb log i (base + (j : Int)) t (ts - 1))
    | none => true)

theorem exclOkTsbSpec (log : List Wmsg) (i : Nat) (base : Int) (rts : List Nat) (ts : Nat) :
    exclOkTs log i base rts ts ↔ exclOkTsb log i base rts ts = true := by
  unfold exclOkTs exclOkTsb
  rw [List.all_eq_true]
  constructor
  · intro he j _
    cases ht : rts[j]? with
    | none => rfl
    | some t =>
      simp only [Bool.not_eq_true']
      cases hb : writesInByb log i (base + (j : Int)) t (ts - 1) with
      | false => rfl
      | true => exact (he j t ht ((writesInBybSpec _ _ _ _ _).2 hb)).elim
  · intro hb j t ht hw
    have hj : j ∈ List.range' 0 rts.length :=
      List.mem_range'_1.2 ⟨Nat.zero_le _, by have := lookup_lt_Some ht; omega⟩
    have hbj := hb j hj
    simp [ht, (writesInBybSpec _ _ _ _ _).1 hw] at hbj

def exwinOk (log : List Wmsg) (i : Nat) (ws : Wstate) (base : Int) (n ts : Nat) : Prop :=
  ∃ R, ws.wRes = some R ∧ R.rvBase = base ∧ R.rvTs.length = n ∧ exclOkTs log i base R.rvTs ts

def exwinOkb (log : List Wmsg) (i : Nat) (ws : Wstate) (base : Int) (n ts : Nat) : Bool :=
  match ws.wRes with
  | some R => decide (R.rvBase = base) && decide (R.rvTs.length = n) &&
      exclOkTsb log i base R.rvTs ts
  | none => false

theorem exwinOkbSpec (log : List Wmsg) (i : Nat) (ws : Wstate) (base : Int) (n ts : Nat) :
    exwinOk log i ws base n ts ↔ exwinOkb log i ws base n ts = true := by
  unfold exwinOk exwinOkb
  constructor
  · rintro ⟨R, hR, hb, hl, he⟩
    rw [hR]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hb, hl⟩, (exclOkTsbSpec _ _ _ _ _).1 he⟩
  · cases hR : ws.wRes with
    | none => intro h; cases h
    | some R =>
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨R, rfl, h.1.1, h.1.2, (exclOkTsbSpec _ _ _ _ _).2 h.2⟩

theorem exwinOkbFalse (log : List Wmsg) (i : Nat) (ws : Wstate) (base : Int) (n ts : Nat) :
    exwinOkb log i ws base n ts = false → ¬ exwinOk log i ws base n ts := by
  intro hf hok
  rw [(exwinOkbSpec _ _ _ _ _ _).1 hok] at hf
  cases hf

/-! ## THE WALKER DISCRIMINATOR: which conditional writes are A/D updates (W2a) -/

/-- The reservation's observed byte `j`, read out of the log at the
reservation's own timestamp column. -/
def resReadByte (img : Image) (log : List Wmsg) (base : Int) (rts : List Nat) (j : Nat) :
    Option (BitVec 8) :=
  rts[j]?.bind (fun t => logByte img log t (base + (j : Int)))

/-- BYTE 0's clause: A (bit 6) set, bits 0–5 as read, bit 7 free, differs. -/
def adByte0 (r d : BitVec 8) : Prop :=
  d.toNat.testBit 6 = true ∧
  (∀ i : Nat, i < 6 → d.toNat.testBit i = r.toNat.testBit i) ∧
  d ≠ r

def adByte0b (r d : BitVec 8) : Bool :=
  d.toNat.testBit 6 &&
  (List.range' 0 6).all (fun i : Nat => decide (d.toNat.testBit i = r.toNat.testBit i)) &&
  decide (d ≠ r)

theorem adByte0bSpec (r d : BitVec 8) : adByte0 r d ↔ adByte0b r d = true := by
  unfold adByte0 adByte0b
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range'_1]
  constructor
  · rintro ⟨h6, hlo, hne⟩
    exact ⟨⟨h6, fun i hi => hlo i (by omega)⟩, hne⟩
  · rintro ⟨⟨h6, hlo⟩, hne⟩
    exact ⟨h6, fun i hi => hlo i ⟨Nat.zero_le _, by omega⟩, hne⟩

/-- THE CLASSIFIER: `data` is an A/D update of what the reservation read. -/
def adShaped (img : Image) (log : List Wmsg) (base : Int) (rts : List Nat)
    (data : List (BitVec 8)) : Prop :=
  data.length = rts.length ∧
  (∀ j : Nat, 1 ≤ j ∧ j < data.length → data[j]? = resReadByte img log base rts j) ∧
  (∃ r0 d0, data[0]? = some d0 ∧ resReadByte img log base rts 0 = some r0 ∧ adByte0 r0 d0)

def adShapedb (img : Image) (log : List Wmsg) (base : Int) (rts : List Nat)
    (data : List (BitVec 8)) : Bool :=
  decide (data.length = rts.length) &&
  (List.range' 1 (data.length - 1)).all
    (fun j : Nat => decide (data[j]? = resReadByte img log base rts j)) &&
  match data[0]?, resReadByte img log base rts 0 with
  | some d0, some r0 => adByte0b r0 d0
  | _, _ => false

theorem adShapedbSpec (img : Image) (log : List Wmsg) (base : Int) (rts : List Nat)
    (data : List (BitVec 8)) :
    adShaped img log base rts data ↔ adShapedb img log base rts data = true := by
  unfold adShaped adShapedb
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range'_1]
  constructor
  · rintro ⟨hlen, hhi, r0, d0, hd0, hr0, hb0⟩
    refine ⟨⟨hlen, fun j hj => hhi j ⟨hj.1, by omega⟩⟩, ?_⟩
    rw [hd0, hr0]
    exact (adByte0bSpec r0 d0).1 hb0
  · rintro ⟨⟨hlen, hhi⟩, h0⟩
    revert h0
    cases hd0 : data[0]? with
    | none => intro h; cases h
    | some d0 =>
      cases hr0 : resReadByte img log base rts 0 with
      | none => intro h; cases h
      | some r0 =>
        intro h0
        exact ⟨hlen, fun j hj => hhi j ⟨hj.1, by omega⟩, r0, d0, rfl, rfl,
          (adByte0bSpec r0 d0).2 h0⟩

/-- THE CLASSIFIER IS A FUNCTION OF THE RESERVATION'S OWN TIMESTAMPS, so it does
not move when the log is END-EXTENDED. -/
theorem resReadByteApp (img : Image) (log l : List Wmsg) (base : Int) (rts : List Nat) (j : Nat) :
    (∀ (j' t : Nat), rts[j']? = some t → t ≤ log.length) →
    resReadByte img (log ++ l) base rts j = resReadByte img log base rts j := by
  intro hb
  unfold resReadByte
  cases ht : rts[j]? with
  | none => rfl
  | some t => exact logByteApp img log l t _ (hb j t ht)

theorem adShapedApp (img : Image) (log l : List Wmsg) (base : Int) (rts : List Nat)
    (data : List (BitVec 8)) :
    (∀ (j t : Nat), rts[j]? = some t → t ≤ log.length) →
    (adShaped img (log ++ l) base rts data ↔ adShaped img log base rts data) := by
  intro hb
  unfold adShaped
  simp only [resReadByteApp img log l base rts _ hb]

theorem adShapedbApp (img : Image) (log l : List Wmsg) (base : Int) (rts : List Nat)
    (data : List (BitVec 8)) :
    (∀ (j t : Nat), rts[j]? = some t → t ≤ log.length) →
    adShapedb img (log ++ l) base rts data = adShapedb img log base rts data := by
  intro hb
  unfold adShapedb
  simp only [resReadByteApp img log l base rts _ hb]

/-- THE GATE'S VIEW ARGUMENT, and its collapse off the walker fragment. -/
theorem exstoreVdFalse (img : Image) (log : List Wmsg) (ws : Wstate) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (R : Wresv) :
    adShapedb img log base R.rvTs data = false →
    max (max (srcsView ws asrc) (srcsView ws vsrc))
      (max R.rvView (if adShapedb img log base R.rvTs data then max ws.wVrOld ws.wVwOld else 0))
    = max (max (srcsView ws asrc) (srcsView ws vsrc)) R.rvView := by
  intro hf; rw [hf]; simp

/-- ... and the ONE-WAY bound on the walker fragment. -/
theorem exstoreVdGe (img : Image) (log : List Wmsg) (ws : Wstate) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (R : Wresv) :
    max (max (srcsView ws asrc) (srcsView ws vsrc)) R.rvView
    ≤ max (max (srcsView ws asrc) (srcsView ws vsrc))
        (max R.rvView (if adShapedb img log base R.rvTs data then max ws.wVrOld ws.wVwOld else 0)) := by
  split <;> omega

/-- THE TOP FACT (layer2 §13, W2a's deliverable). -/
theorem wpstepExstoreAdTop (img : Image) (log : List Wmsg) (ws : Wstate) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (R : Wresv) (ts : Nat) :
    adShapedb img log base R.rvTs data = true →
    fulfilOkD ws rl base data.length ts
      (max (max (srcsView ws asrc) (srcsView ws vsrc))
        (max R.rvView
          (if adShapedb img log base R.rvTs data then max ws.wVrOld ws.wVwOld else 0))) →
    ws.wVrOld < ts ∧ ws.wVwOld < ts := by
  rintro ht ⟨_, hext⟩
  rw [ht] at hext
  simp only [fulfilVpreD, ↓reduceIte] at hext
  omega

/-! ## The side conditions under an end-extension of the log -/

theorem writesInByAppInv (log l : List Wmsg) (Q : Option Nat → Prop) (a : Int) (lo hi : Nat) :
    hi ≤ log.length → writesInBy (log ++ l) Q a lo hi → writesInBy log Q a lo hi := by
  rintro hle ⟨t, hlo, hhi, m, hm, hb, hq⟩
  rw [lookup_app_l (by omega)] at hm
  exact ⟨t, hlo, hhi, m, hm, hb, hq⟩

/-- A PLAIN (non-latest) read is stable under appending. -/
theorem readOkDApp (img : Image) (log l : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va : Nat) :
    wsBounded ws log.length → va ≤ log.length →
    readOkD img log ws aq false base tvs va → readOkD img (log ++ l) ws aq false base tvs va := by
  intro hb hva hr j t v htv
  obtain ⟨hlb, ⟨hs, hn⟩, _⟩ := hr j t v htv
  have ht : t ≤ log.length := logByteBounded img log t _ (by rw [hlb]; rfl)
  refine ⟨by rw [logByteApp img log l t _ ht]; exact hlb, ⟨by rw [logByteApp img log l t _ ht]; exact hs,
    fun hw => hn (writesInAppInv log l _ _ _ ?_ hw)⟩, fun h => by cases h⟩
  have hv := loadVpreDBounded ws aq va _ hb hva
  have := hb.2.2.2.2.2.2.1 (base + (j : Int))
  omega

theorem readOkApp (img : Image) (log l : List Wmsg) (ws : Wstate) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    wsBounded ws log.length →
    readOk img log ws aq false base tvs → readOk img (log ++ l) ws aq false base tvs :=
  fun hb => readOkDApp img log l ws aq base tvs 0 hb (Nat.zero_le _)

/-- The exclusivity window ends at `ts - 1`, at most the old log length. -/
theorem exclOkApp (log l : List Wmsg) (i : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) (ts : Nat) :
    ts - 1 ≤ log.length → exclOk log i base tvs ts → exclOk (log ++ l) i base tvs ts := by
  intro hle he j t v htv hw
  exact he j t v htv (writesInByAppInv log l _ _ _ _ hle hw)

theorem exclOkTsApp (log l : List Wmsg) (i : Nat) (base : Int) (rts : List Nat) (ts : Nat) :
    ts - 1 ≤ log.length → exclOkTs log i base rts ts → exclOkTs (log ++ l) i base rts ts := by
  intro hle he j t ht hw
  exact he j t ht (writesInByAppInv log l _ _ _ _ hle hw)

/-- A single-byte `readOk`. -/
theorem readOkSingle (img : Image) (log : List Wmsg) (ws : Wstate) (base : Int) (t : Nat)
    (v : BitVec 8) :
    logByte img log t base = some v →
    readable img log ws (loadVpre ws false) base t →
    readOk img log ws false false base [(t, v)] := by
  intro hv hr j t' v' hj
  cases j with
  | succ j => simp at hj
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    have h0 : base + ((0 : Nat) : Int) = base := by simp
    rw [h0]
    exact ⟨hv, by rw [loadVpreD0]; exact hr, fun h => by cases h⟩

/-! ## The machine -/

section machine

variable {P D : Type}

-- The abstract per-agent program: `pstep p d l p' d'` (the fabric is read and moved).
variable (pstep : P → D → Wlabel → P → D → Prop)

/-- One machine step.  `WPPromise` is PARM's `promise_step`; every other arm
is a `state_step` arm (see the Rocq comments on each arm: the RMW split's two
halves, the walker gate in `WPExStore`, D-2r's 0-floor exclusive reads). -/
inductive wpstep : Wpcfg P D → Wpcfg P D → Prop
  | WPPromise (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (base : Int) (data : List (BitVec 8))
      (k : WmClass) :
      cfg.pcAgs[i]? = some ag →
      data ≠ [] →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], cfg.pcDev,
         cfg.pcAgs.set i ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩⟩
  | WPSilent (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev LSilent st' d' →
      wpstep cfg ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩
  | WPLoad (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (aq lat : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LLoad aq lat base tvs asrc) st' d' →
      readOkD cfg.pcImg cfg.pcLog ag.paWs aq lat base tvs (srcsView ag.paWs asrc) →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base
           (tvs.map Prod.fst), ag.paProm⟩⟩
  | WPFulfil (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (ts : Nat) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LStore rl base data asrc vsrc) st' d' →
      ts ∈ ag.paProm →
      cfg.pcLog[ts - 1]? = some ⟨base, data, some i, k⟩ →
      fulfilOkD ag.paWs rl base data.length ts
        (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)) →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', storePostRunD ag.paWs rl (srcsView ag.paWs asrc)
           (srcsView ag.paWs vsrc) base data.length ts, ag.paProm \ {ts}⟩⟩
  | WPRmw (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (aq rl : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass)
      (ts : Nat) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LRmw aq rl base tvs data asrc vsrc) st' d' →
      tvs.length = data.length →
      ts ∈ ag.paProm →
      cfg.pcLog[ts - 1]? = some ⟨base, data, some i, k⟩ →
      readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs →
      exclOk cfg.pcLog i base tvs ts →
      fulfilOkD (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
        rl base data.length ts
        (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
          (ldvOf ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))) →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st',
           storePostRunD (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
             rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc) base data.length ts,
           ag.paProm \ {ts}⟩⟩
  | WPFence (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (pr pw sr sw : Bool) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LFence pr pw sr sw) st' d' →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', fencePost ag.paWs pr pw sr sw, ag.paProm⟩⟩
  | WPDev (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev LDev st' d' →
      wpstep cfg ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ag.paWs, ag.paProm⟩⟩
  | WPRegW (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (rd : Nat) (srcs : List Dsrc) (st' : P)
      (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LRegW rd srcs) st' d' →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', regwPost ag.paWs rd (srcsView ag.paWs srcs), ag.paProm⟩⟩
  | WPCtrl (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (srcs : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LCtrl srcs) st' d' →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', ctrlPost ag.paWs (srcsView ag.paWs srcs), ag.paProm⟩⟩
  | WPInstr (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev LInstr st' d' →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', instrPost ag.paWs, ag.paProm⟩⟩
  | WPExLoad (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (aq : Bool) (base : Int)
      (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LExLoad aq base tvs asrc) st' d' →
      readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base
           (tvs.map Prod.fst), ag.paProm⟩⟩
  | WPExStore (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (ts : Nat) (R : Wresv)
      (st' : P) (d' : D) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev (LExStore rl base data asrc vsrc) st' d' →
      ts ∈ ag.paProm →
      cfg.pcLog[ts - 1]? = some ⟨base, data, some i, k⟩ →
      ag.paWs.wRes = some R →
      R.rvBase = base →
      R.rvTs.length = data.length →
      exclOkTs cfg.pcLog i base R.rvTs ts →
      fulfilOkD ag.paWs rl base data.length ts
        (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
          (max R.rvView
            (if adShapedb cfg.pcImg cfg.pcLog base R.rvTs data
             then max ag.paWs.wVrOld ag.paWs.wVwOld else 0))) →
      wpstep cfg
        ⟨cfg.pcImg, cfg.pcLog, d',
         cfg.pcAgs.set i ⟨st', storePostRunD ag.paWs rl (srcsView ag.paWs asrc)
           (srcsView ag.paWs vsrc) base data.length ts, ag.paProm \ {ts}⟩⟩

/-! ### Initial configurations and behaviors -/

def wpInit (img : Image) (d0 : D) (ps : List P) : Wpcfg P D :=
  ⟨img, [], d0, ps.map (fun p => ⟨p, wsInit, ∅⟩)⟩

/-- All promises discharged (PARM `Machine.no_promise`). -/
def noPromises (cfg : Wpcfg P D) : Prop :=
  ∀ (i : Nat) (ag : Wpagent P), cfg.pcAgs[i]? = some ag → ag.paProm = ∅

/-- A BEHAVIOR (PARM `Machine.exec`): a reachable configuration whose every
promise set is empty. -/
def wpBehavior (img : Image) (d0 : D) (ps : List P) (cfg : Wpcfg P D) : Prop :=
  rtc (wpstep pstep) (wpInit img d0 ps) cfg ∧ noPromises cfg

/-! ### Well-formedness: the machine invariant -/

def promWf (log : List Wmsg) (i : Nat) (ag : Wpagent P) : Prop :=
  ∀ ts, ts ∈ ag.paProm →
    0 < ts ∧ ts ≤ log.length ∧ ∃ m, log[ts - 1]? = some m ∧ m.wmTid = some i

def cfgWf (cfg : Wpcfg P D) : Prop :=
  ∀ (i : Nat) (ag : Wpagent P), cfg.pcAgs[i]? = some ag →
    wsBounded ag.paWs cfg.pcLog.length ∧ promWf cfg.pcLog i ag

theorem cfgWfInit (img : Image) (d0 : D) (ps : List P) : cfgWf (wpInit img d0 ps) := by
  intro i ag hlk
  simp only [wpInit, List.getElem?_map] at hlk
  cases hp : ps[i]? with
  | none => rw [hp] at hlk; cases hlk
  | some p =>
    rw [hp] at hlk; injection hlk with hlk; subst hlk
    exact ⟨wsBoundedInit _, fun ts hts => by set_solver⟩

/-- Every read timestamp a `readOk` admits is a real log position. -/
theorem readOkDTsBounded (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (va : Nat) :
    readOkD img log ws aq lat base tvs va → ∀ t ∈ tvs.map Prod.fst, t ≤ log.length := by
  intro hr t ht
  obtain ⟨⟨t', v⟩, hmem, rfl⟩ := List.mem_map.1 ht
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
  have hb := (hr j t' v hj).1
  exact logByteBounded img log t' _ (by rw [hb]; rfl)

theorem readOkTsBounded (img : Image) (log : List Wmsg) (ws : Wstate) (aq lat : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) :
    readOk img log ws aq lat base tvs → ∀ t ∈ tvs.map Prod.fst, t ≤ log.length :=
  readOkDTsBounded img log ws aq lat base tvs 0

/-- The lookup in an updated agent list (Lean helper). -/
theorem lookupSetCases {α : Type _} {l : List α} {i j : Nat} {x y : α}
    (h : (l.set i x)[j]? = some y) : (j = i ∧ y = x) ∨ (j ≠ i ∧ l[j]? = some y) := by
  rw [List.getElem?_set] at h
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte] at h
    split at h
    · injection h with h; exact .inl ⟨rfl, h.symm⟩
    · cases h
  · simp only [hij, ↓reduceIte] at h
    exact .inr ⟨Ne.symm hij, h⟩

/-- The well-formedness of a state step's post-configuration (Lean helper: the
one shape every non-promise arm of `cfgWfStep` has). -/
theorem cfgWfSet (cfg : Wpcfg P D) (i : Nat) (ag ag' : Wpagent P) (img : Image) (d : D) :
    cfgWf cfg → cfg.pcAgs[i]? = some ag →
    (wsBounded ag.paWs cfg.pcLog.length → promWf cfg.pcLog i ag →
      wsBounded ag'.paWs cfg.pcLog.length ∧ promWf cfg.pcLog i ag') →
    cfgWf (⟨img, cfg.pcLog, d, cfg.pcAgs.set i ag'⟩ : Wpcfg P D) := by
  intro hwf hlk hstep i' ag'' hlk'
  rcases lookupSetCases hlk' with ⟨rfl, rfl⟩ | ⟨hne, hlk'⟩
  · obtain ⟨hb, hp⟩ := hwf i' ag hlk
    exact hstep hb hp
  · exact hwf i' ag'' hlk'

theorem promWfDiff (log : List Wmsg) (i : Nat) (ag : Wpagent P) (st' : P) (ws' : Wstate) (ts : Nat) :
    promWf log i ag → promWf log i (⟨st', ws', ag.paProm \ {ts}⟩ : Wpagent P) := by
  intro hp ts' hts'
  have : ts' ∈ ag.paProm := by simp only at hts'; set_solver
  exact hp ts' this

theorem cfgWfStep (cfg cfg' : Wpcfg P D) : cfgWf cfg → wpstep pstep cfg cfg' → cfgWf cfg' := by
  intro hwf hstep
  cases hstep with
  | WPPromise i ag base data k hlk hnn =>
    intro i' ag' hlk'
    dsimp only at hlk' ⊢
    have hl : (cfg.pcLog ++ [(⟨base, data, some i, k⟩ : Wmsg)]).length = cfg.pcLog.length + 1 := by
      simp
    rcases lookupSetCases hlk' with ⟨rfl, rfl⟩ | ⟨hne, hlk'⟩
    · obtain ⟨hb, hp⟩ := hwf i' ag hlk
      refine ⟨wsBoundedMono _ _ _ hb (by omega), fun ts hts => ?_⟩
      simp only at hts
      by_cases h : ts = cfg.pcLog.length + 1
      · subst h
        exact ⟨by omega, by omega, _, list_lookup_middle (by simp), rfl⟩
      · have hts' : ts ∈ ag.paProm := by set_solver
        obtain ⟨h1, h2, m, hm, ht⟩ := hp ts hts'
        exact ⟨h1, by omega, m, lookup_app_l_Some hm, ht⟩
    · obtain ⟨hb, hp⟩ := hwf i' ag' hlk'
      refine ⟨wsBoundedMono _ _ _ hb (by omega), fun ts hts => ?_⟩
      obtain ⟨h1, h2, m, hm, ht⟩ := hp ts hts
      exact ⟨h1, by omega, m, lookup_app_l_Some hm, ht⟩
  | WPSilent i ag st' d' hlk _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp => ⟨hb, hp⟩)
  | WPLoad i ag aq lat base tvs asrc st' d' hlk _ hr =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp =>
      ⟨loadPostRunDBounded _ _ _ _ _ _ hb (srcsViewBounded _ _ _ hb)
        (readOkDTsBounded _ _ _ _ _ _ _ _ hr), hp⟩)
  | WPFulfil i ag rl base data asrc vsrc k ts st' d' hlk _ hts _ _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp => by
      obtain ⟨_, hle, _⟩ := hp ts hts
      exact ⟨storePostRunDBounded _ _ _ _ _ _ _ _ _ hb hle (Nat.le_refl _)
        (srcsViewBounded _ _ _ hb) (srcsViewBounded _ _ _ hb), promWfDiff _ _ _ _ _ _ hp⟩)
  | WPRmw i ag aq rl base tvs data asrc vsrc k ts st' d' hlk _ _ hts _ hr _ _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp => by
      obtain ⟨_, hle, _⟩ := hp ts hts
      have hva := srcsViewBounded _ _ asrc hb
      have hvd := srcsViewBounded _ _ vsrc hb
      exact ⟨storePostRunDBounded _ _ _ _ _ _ _ _ _
        (loadPostRunDBounded _ _ _ _ _ _ hb hva (readOkDTsBounded _ _ _ _ _ _ _ _ hr))
        hle (Nat.le_refl _) hva hvd, promWfDiff _ _ _ _ _ _ hp⟩)
  | WPFence i ag pr pw sr sw st' d' hlk _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp => ⟨fencePostBounded _ _ _ _ _ _ hb, hp⟩)
  | WPDev i ag st' d' hlk _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp => ⟨hb, hp⟩)
  | WPRegW i ag rd srcs st' d' hlk _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp =>
      ⟨regwPostBounded _ _ _ _ hb (srcsViewBounded _ _ _ hb), hp⟩)
  | WPCtrl i ag srcs st' d' hlk _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp =>
      ⟨ctrlPostBounded _ _ _ hb (srcsViewBounded _ _ _ hb), hp⟩)
  | WPInstr i ag st' d' hlk _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp => ⟨instrPostBounded _ _ hb, hp⟩)
  | WPExLoad i ag aq base tvs asrc st' d' hlk _ hr =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp =>
      ⟨exloadPostRunDBounded _ _ _ _ _ _ hb (srcsViewBounded _ _ _ hb)
        (readOkDTsBounded _ _ _ _ _ _ _ _ hr), hp⟩)
  | WPExStore i ag rl base data asrc vsrc k ts R st' d' hlk _ hts _ _ _ _ _ _ =>
    exact cfgWfSet cfg i ag _ _ _ hwf hlk (fun hb hp => by
      obtain ⟨_, hle, _⟩ := hp ts hts
      exact ⟨storePostRunDBounded _ _ _ _ _ _ _ _ _ hb hle (Nat.le_refl _)
        (srcsViewBounded _ _ _ hb) (srcsViewBounded _ _ _ hb), promWfDiff _ _ _ _ _ _ hp⟩)

theorem cfgWfReach (cfg cfg' : Wpcfg P D) : cfgWf cfg → rtc (wpstep pstep) cfg cfg' → cfgWf cfg' := by
  intro h0 hr
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact cfgWfStep pstep _ _ ih hs

/-! ### The fused promise+fulfil derivations -/

/-- The promise set returns after inserting and removing a fresh timestamp. -/
private theorem memSingletonUnion (x : Nat) (pr : GSet Nat) : x ∈ ({x} ∪ pr : GSet Nat) := by
  set_solver

private theorem promAddDel (pr : GSet Nat) (ts : Nat) (h : ts ∉ pr) : ({ts} ∪ pr) \ {ts} = pr := by
  set_solver

theorem wpstepStoreNow (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (st' : P) (d' : D) :
    cfg.pcAgs[i]? = some ag →
    pstep ag.paSt cfg.pcDev (LStore rl base data asrc vsrc) st' d' →
    data ≠ [] →
    wsBounded ag.paWs cfg.pcLog.length →
    cfg.pcLog.length + 1 ∉ ag.paProm →
    rtc (wpstep pstep) cfg
      ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
       cfg.pcAgs.set i ⟨st', storePostRunD ag.paWs rl (srcsView ag.paWs asrc)
         (srcsView ag.paWs vsrc) base data.length (cfg.pcLog.length + 1), ag.paProm⟩⟩ := by
  intro hlk hp hnn hb hfresh
  have hlen := lookup_lt_Some hlk
  have h1 := wpstep.WPPromise (pstep := pstep) cfg i ag base data k hlk hnn
  refine rtc_l h1 (rtc_once ?_)
  have hmidlk : (cfg.pcAgs.set i (⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩ :
      Wpagent P))[i]? = some ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩ :=
    list_lookup_insert hlen
  have hmsg : (cfg.pcLog ++ [(⟨base, data, some i, k⟩ : Wmsg)])[cfg.pcLog.length + 1 - 1]?
      = some ⟨base, data, some i, k⟩ := list_lookup_middle (by simp)
  have hok : fulfilOkD ag.paWs rl base data.length (cfg.pcLog.length + 1)
      (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc)) := by
    refine ⟨fun j _ => ?_, ?_⟩
    · have := hb.2.2.2.2.2.2.1 (base + (j : Int)); omega
    · have h1 := srcsViewBounded _ _ asrc hb
      have h2 := srcsViewBounded _ _ vsrc hb
      have := fulfilVpreDBounded ag.paWs rl _ _ hb (Nat.max_le.2 ⟨h1, h2⟩)
      omega
  have h2 := wpstep.WPFulfil (pstep := pstep) (⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], cfg.pcDev,
    cfg.pcAgs.set i ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩⟩ : Wpcfg P D)
    i _ rl base data asrc vsrc k
    (cfg.pcLog.length + 1) st' d' hmidlk hp (memSingletonUnion _ _) hmsg hok
  simp only [List.set_set, promAddDel _ _ hfresh] at h2
  exact h2

/-- The rmw sibling of `wpstepStoreNow`. -/
theorem wpstepRmwNow (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (aq rl : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass)
    (st' : P) (d' : D) :
    cfg.pcAgs[i]? = some ag →
    pstep ag.paSt cfg.pcDev (LRmw aq rl base tvs data asrc vsrc) st' d' →
    data ≠ [] →
    tvs.length = data.length →
    wsBounded ag.paWs cfg.pcLog.length →
    cfg.pcLog.length + 1 ∉ ag.paProm →
    readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs →
    exclOk cfg.pcLog i base tvs (cfg.pcLog.length + 1) →
    rtc (wpstep pstep) cfg
      ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
       cfg.pcAgs.set i ⟨st',
         storePostRunD (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
           rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc) base data.length
           (cfg.pcLog.length + 1),
         ag.paProm⟩⟩ := by
  intro hlk hps hnn hlen hb hfresh hr he
  have hva := srcsViewBounded _ _ asrc hb
  have hvd := srcsViewBounded _ _ vsrc hb
  have hlt := lookup_lt_Some hlk
  have h1 := wpstep.WPPromise (pstep := pstep) cfg i ag base data k hlk hnn
  refine rtc_l h1 (rtc_once ?_)
  have hmidlk : (cfg.pcAgs.set i (⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩ :
      Wpagent P))[i]? = some ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩ :=
    list_lookup_insert hlt
  have hmsg : (cfg.pcLog ++ [(⟨base, data, some i, k⟩ : Wmsg)])[cfg.pcLog.length + 1 - 1]?
      = some ⟨base, data, some i, k⟩ := list_lookup_middle (by simp)
  have hr' := readOkApp cfg.pcImg cfg.pcLog [⟨base, data, some i, k⟩] ag.paWs aq base tvs hb hr
  have he' := exclOkApp cfg.pcLog [⟨base, data, some i, k⟩] i base tvs _ (by omega) he
  have hbl := loadPostRunDBounded ag.paWs aq _ base (tvs.map Prod.fst) _ hb hva
    (readOkDTsBounded _ _ _ _ _ _ _ _ hr)
  have hldv := ldvOfBounded ag.paWs aq _ base (tvs.map Prod.fst) _ hb hva
    (readOkDTsBounded _ _ _ _ _ _ _ _ hr)
  have hok : fulfilOkD (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
      rl base data.length (cfg.pcLog.length + 1)
      (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
        (ldvOf ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))) := by
    refine ⟨fun j _ => ?_, ?_⟩
    · have := hbl.2.2.2.2.2.2.1 (base + (j : Int)); omega
    · have := fulfilVpreDBounded _ rl _ _ hbl (Nat.max_le.2 ⟨Nat.max_le.2 ⟨hva, hvd⟩, hldv⟩)
      omega
  have h2 := wpstep.WPRmw (pstep := pstep) (⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], cfg.pcDev,
    cfg.pcAgs.set i ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩⟩ : Wpcfg P D)
    i _ aq rl base tvs data asrc vsrc k
    (cfg.pcLog.length + 1) st' d' hmidlk hps hlen (memSingletonUnion _ _) hmsg hr' he' hok
  simp only [List.set_set, promAddDel _ _ hfresh] at h2
  exact h2

/-- THE RMW SPLIT (S2): the conditional write's fused form. -/
theorem wpstepExstoreNow (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (rl : Bool) (base : Int)
    (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (k : WmClass) (R : Wresv) (st' : P) (d' : D) :
    cfg.pcAgs[i]? = some ag →
    pstep ag.paSt cfg.pcDev (LExStore rl base data asrc vsrc) st' d' →
    data ≠ [] →
    wsBounded ag.paWs cfg.pcLog.length →
    cfg.pcLog.length + 1 ∉ ag.paProm →
    ag.paWs.wRes = some R →
    R.rvBase = base →
    R.rvTs.length = data.length →
    exclOkTs cfg.pcLog i base R.rvTs (cfg.pcLog.length + 1) →
    rtc (wpstep pstep) cfg
      ⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], d',
       cfg.pcAgs.set i ⟨st', storePostRunD ag.paWs rl (srcsView ag.paWs asrc)
         (srcsView ag.paWs vsrc) base data.length (cfg.pcLog.length + 1), ag.paProm⟩⟩ := by
  intro hlk hps hnn hb hfresh hres hrb hrlen he
  have hva := srcsViewBounded _ _ asrc hb
  have hvd := srcsViewBounded _ _ vsrc hb
  have hrv : R.rvView ≤ cfg.pcLog.length := (wsBoundedRes _ _ hb R hres).2
  have hlt := lookup_lt_Some hlk
  have h1 := wpstep.WPPromise (pstep := pstep) cfg i ag base data k hlk hnn
  refine rtc_l h1 (rtc_once ?_)
  have hmidlk : (cfg.pcAgs.set i (⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩ :
      Wpagent P))[i]? = some ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩ :=
    list_lookup_insert hlt
  have hmsg : (cfg.pcLog ++ [(⟨base, data, some i, k⟩ : Wmsg)])[cfg.pcLog.length + 1 - 1]?
      = some ⟨base, data, some i, k⟩ := list_lookup_middle (by simp)
  have he' := exclOkTsApp cfg.pcLog [⟨base, data, some i, k⟩] i base R.rvTs _ (by omega) he
  have hvro : ag.paWs.wVrOld ≤ cfg.pcLog.length := hb.1
  have hvwo : ag.paWs.wVwOld ≤ cfg.pcLog.length := hb.2.1
  have hok : fulfilOkD ag.paWs rl base data.length (cfg.pcLog.length + 1)
      (max (max (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc))
        (max R.rvView
          (if adShapedb cfg.pcImg (cfg.pcLog ++ [⟨base, data, some i, k⟩]) base R.rvTs data
           then max ag.paWs.wVrOld ag.paWs.wVwOld else 0))) := by
    refine ⟨fun j _ => ?_, ?_⟩
    · have := hb.2.2.2.2.2.2.1 (base + (j : Int)); omega
    · have hg : (if adShapedb cfg.pcImg (cfg.pcLog ++ [⟨base, data, some i, k⟩]) base R.rvTs data
             then max ag.paWs.wVrOld ag.paWs.wVwOld else 0) ≤ cfg.pcLog.length := by
        split
        · exact Nat.max_le.2 ⟨hvro, hvwo⟩
        · exact Nat.zero_le _
      have := fulfilVpreDBounded ag.paWs rl _ _ hb
        (Nat.max_le.2 ⟨Nat.max_le.2 ⟨hva, hvd⟩, Nat.max_le.2 ⟨hrv, hg⟩⟩)
      exact Nat.lt_succ_of_le this
  have h2 := wpstep.WPExStore (pstep := pstep) (⟨cfg.pcImg, cfg.pcLog ++ [⟨base, data, some i, k⟩], cfg.pcDev,
    cfg.pcAgs.set i ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩⟩ : Wpcfg P D)
    i _ rl base data asrc vsrc k
    (cfg.pcLog.length + 1) R st' d' hmidlk hps (memSingletonUnion _ _) hmsg hres hrb hrlen he'
    (by dsimp only; exact hok)
  simp only [List.set_set, promAddDel _ _ hfresh] at h2
  exact h2

/-- A promise-free step never leaves promises behind. -/
theorem noPromisesStoreNow (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (k : WmClass) (st' : P)
    (ws' : Wstate) (d' : D) :
    noPromises cfg → cfg.pcAgs[i]? = some ag →
    noPromises (⟨cfg.pcImg, cfg.pcLog ++ [⟨0, [], some i, k⟩], d',
      cfg.pcAgs.set i ⟨st', ws', ag.paProm⟩⟩ : Wpcfg P D) := by
  intro hnp hlk i' ag' hlk'
  rcases lookupSetCases hlk' with ⟨rfl, rfl⟩ | ⟨_, hlk'⟩
  · exact hnp i' ag hlk
  · exact hnp i' ag' hlk'

end machine

/-! ## THE COMPATIBILITY SHIM: the old machine is the constant-fabric instance -/

def pstepOfPure {P D : Type} (ps : P → Wlabel → P → Prop) : P → D → Wlabel → P → D → Prop :=
  fun p d l p' d' => ps p l p' ∧ d' = d

theorem pstepOfPureDev {P D : Type} (ps : P → Wlabel → P → Prop) (p : P) (d : D) (l : Wlabel)
    (p' : P) (d' : D) : pstepOfPure ps p d l p' d' → d' = d := fun h => h.2

theorem pstepOfPureAny {P D : Type} (ps : P → Wlabel → P → Prop) (p : P) (d : D) (l : Wlabel)
    (p' : P) (d' : D) : pstepOfPure ps p d l p' d' → ∀ d0 : D, pstepOfPure ps p d0 l p' d0 :=
  fun h _ => ⟨h.1, rfl⟩

theorem pstepOfPureIntro {P D : Type} (ps : P → Wlabel → P → Prop) (p : P) (d : D) (l : Wlabel)
    (p' : P) : ps p l p' → pstepOfPure ps p d l p' d := fun h => ⟨h, rfl⟩

theorem pstepOfPureElim {P D : Type} (ps : P → Wlabel → P → Prop) (p : P) (d : D) (l : Wlabel)
    (p' : P) (d' : D) : pstepOfPure ps p d l p' d' → ps p l p' := fun h => h.1

/-- AT `D := Unit` THE FABRIC EQUATION IS AUTOMATIC. -/
def pstepUnit {P : Type} (ps : P → Wlabel → P → Prop) : P → Unit → Wlabel → P → Unit → Prop :=
  fun p _ l p' _ => ps p l p'

/-- Rocq's notation `WPCfgU img log ags`. -/
abbrev WPCfgU {P : Type} (img : Image) (log : List Wmsg) (ags : List (Wpagent P)) : Wpcfg P Unit :=
  ⟨img, log, (), ags⟩

theorem pstepUnitOfPure {P : Type} (ps : P → Wlabel → P → Prop) (p : P) (d : Unit) (l : Wlabel)
    (p' : P) (d' : Unit) : pstepUnit ps p d l p' d' ↔ pstepOfPure ps p d l p' d' :=
  ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩

/-- The fabric of a constant-fabric run never moves. -/
theorem wpstepPureDev {P D : Type} (ps : P → Wlabel → P → Prop) (c c' : Wpcfg P D) :
    wpstep (pstepOfPure ps) c c' → c'.pcDev = c.pcDev := by
  intro h
  cases h <;> simp_all [pstepOfPure]

end Weak
