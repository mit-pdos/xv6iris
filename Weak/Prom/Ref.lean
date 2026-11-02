/-
Weak/Prom: **`rvwmoRef` — the RVWMO reference memory model, execution level** (S0-P part (1), the reference
checker core; the S1 encoding draft).

Plan: `~/dev/weak-orch/promising/plan.md` rev 7, §6 ("Reference encoding", "Gaps (S1)"), §8 S0-P (1) and S1;
owner rulings (context.md): 6 "The definition is the RiscV reference", 8 [OWN.P1] faithful, 10 [OWN.P3] phase 1 =
small programs with translation OFF, 12 [OWN.P5] mixed-size completeness deferred (mixed-size is IN the reference).
Quotes: the RISC-V ISA manual `riscv/riscv-isa-manual` @ `e17d92a1` (copies in `~/dev/weak-orch/promising/spec/`):
`rvwmo.adoc` (§rvwmo, THE definition), `zalrsc.adoc`, `zaamo.adoc`, `mm-explanatory.adoc` (§expl, I/O ordering),
and the base-ISA FENCE text `unpriv_rv32.adoc` (fetched copy `s0t/fetched-S/manual-e17d92a1/unpriv_rv32.adoc`).

A NEW, SELF-CONTAINED encoding: nothing here imports or changes `Weak/AxDeps.lean`, `Weak/AxGraphCat.lean`,
`Weak/WeakRvwmoGraph.lean` (read for the pattern only).  Differences from `rvwmoCatConsistentT` (AxDeps.lean:299):
no `DTtrans`/`DTctx` edges (STRONGER there, plan §6 [R1.3]); rules 6, 7 (RCsc in full) and 8 present; LR/SC
labels, pair atomicity with mismatched address/width, the §zalrsc success conditions; aq/rl restricted to
same-class pairs (Table S F-S3: `gacqPo` orders a RAM acquire before I/O, WeakRvwmoGraph.lean:245–246, which
mm-explanatory.adoc:1149–1153 forbids); syntactic dependencies are carried by the events (computed from register
dataflow by the program semantics, `Weak/Prom/RefProg.lean`).

## The shape of an execution

* `Exec.evs h` is hart `h`'s list of EVENTS in program order of creation; an event is a memory operation (`ld`,
  `st`, `amo`, `lr`, a successful `sc`) or a non-memory instruction event that the rules mention: a FENCE (rule 4)
  or a FAILED SC (`scFail`: an SC instruction, which breaks LR/SC pairing and may carry rule 13's address
  dependency, but "does not give rise to any memory operations", rvwmo.adoc:82).
* PROGRAM ORDER is by the dynamic instruction index `Skel.ii` (rvwmo.adoc:60–63 "the order in which the
  instructions that generate each load and store are logically laid out in that hart's dynamic instruction
  stream"), so the component operations of ONE instruction are unordered by po, as rvwmo.adoc:96–98 requires for a
  decomposed misaligned access ("not ordered with respect to each other in program order").
* `Exec.gmo` is THE GLOBAL MEMORY ORDER, a list (rvwmo.adoc:46–47 "a total ordering of the memory operations
  produced by all harts").  RF IS NOT CHOSEN: it is DERIVED from gmo and po by the load value axiom (`rfSrc`), so
  "returns a value written by" (rules 2, 3, 12, atomicity) means the store the axiom selects.
* Bytes are natural numbers `< 256` stored per event (`rdat` = the bytes a load returns, `wdat` = the bytes a store
  writes); every rule is BYTE-WISE (mixed-size, rvwmo.adoc:279, :315–324).  Single-copy atomicity (rvwmo.adoc:69–70)
  is the fact that one aligned access is ONE gmo event (rvwmo.adoc:71–74).
* The initial memory `img` plays the initial value; it is not an event (the atomicity axiom quantifies over STORES
  only, read literally; §zalrsc's success conditions cover the initial-value case, see `scAx`).

## I/O (mm-explanatory.adoc:1137–1169)

`Exec.io` lists the I/O regions (PMAs: strongly ordered or not, channel).  An access is I/O when its address is in
one.  The load value and atomicity axioms do not apply to I/O ("For I/O, the load value axiom and atomicity axiom
in general do not apply", :1139–1140); rules 1–13 apply to any pair (§expl's I/O rule 1 "a precedes b in preserved
program order as defined in <<memorymodel>>"), EXCEPT that rules 5–7 only relate same-class pairs ("with the
exception that acquire and release ordering annotations apply only from one memory operation to another memory
operation and from one I/O operation to another I/O operation, but not from a memory operation to an I/O nor vice
versa", :1149–1153), and the rf-based rules 2, 3, 12 only relate RAM loads (rf is undefined for I/O).  I/O rules
(2)–(5) are `ioOrdB`.  Reading (recorded, PROGRESS-S0P1.md R-IO): the explicit aq/rl exception implies the other
rules DO relate RAM–I/O pairs.

## Extension points ([OWN.P3])

No page-walk, A/D or PA-3 events: an implicit-read event class (walk/fetch reads outside gmo) and the A/D pair
(r_ad, w_ad with w_ad a gmo store outside po) are to be added as new `Kind`s with their own `platformOrd`
predicate (plan §6), never as edges of `orderedB`.  No device agents (the §zalrsc device-write conditions are
vacuous).  No CMO events (cmo.adoc; machine v2 has them).
-/

namespace Weak.Prom.Ref

/-! ## 1. Events -/

/-- An event identifier: (hart, index in that hart's event list). -/
abbrev EvId := Nat × Nat

/-- A FENCE's predecessor and successor sets, unpriv_rv32.adoc:770–773: "Any combination of device input (I),
device output (O), memory reads (R), and memory writes (W) may be ordered with respect to any combination of the
same." -/
structure FenceSet where
  pr : Bool
  pw : Bool
  pi : Bool
  po : Bool
  sr : Bool
  sw : Bool
  si : Bool
  so : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The kind of an event.  `amo` is "a single memory operation that is both a load operation and a store operation
simultaneously" (rvwmo.adoc:73–74); `sc` is a SUCCESSFUL store-conditional's store operation; `scFail` a failed SC
("An unsuccessful sc instruction does not give rise to any memory operations", rvwmo.adoc:82), kept as a
non-memory event because it is an SC INSTRUCTION (pairing, rvwmo.adoc:114–117) with an address source register
(rule 13 says "instruction m"). -/
inductive Kind where
  | ld
  | st
  | amo
  | lr
  | sc
  | scFail
  | fence (f : FenceSet)
  deriving DecidableEq, Repr, Inhabited

/-- A memory operation (rvwmo.adoc:66–67 "A memory operation can be either a load operation, a store operation, or
both simultaneously"). -/
def Kind.isMem : Kind → Bool
  | .ld | .st | .amo | .lr | .sc => true
  | _ => false

/-- A load operation (an AMO is also one, rvwmo.adoc:73–74, :270–271 "note that AMOs are simultaneously both loads
and stores"). -/
def Kind.isLoad : Kind → Bool
  | .ld | .amo | .lr => true
  | _ => false

/-- A store operation. -/
def Kind.isStore : Kind → Bool
  | .st | .amo | .sc => true
  | _ => false

/-- Rule 3's "a is generated by an AMO or SC instruction". -/
def Kind.isRmwW : Kind → Bool
  | .amo | .sc => true
  | _ => false

/-- An LR or SC INSTRUCTION (successful or not): pairing (rvwmo.adoc:114–116) "there are no other lr or sc
instructions in between". -/
def Kind.isLrSc : Kind → Bool
  | .lr | .sc | .scFail => true
  | _ => false

/-- The instruction-level attributes of an event (value-independent): kind, dynamic instruction index (po), size in
bytes, the four ordering annotations (rvwmo.adoc:122–128: acquire-RCpc, acquire-RCsc, release-RCpc, release-RCsc),
and the syntactic dependencies as indices of this hart's events (rvwmo.adoc:232–246: address, data, control). -/
structure Skel where
  kind : Kind
  ii : Nat
  sz : Nat
  aqPc : Bool := false
  aqSc : Bool := false
  rlPc : Bool := false
  rlSc : Bool := false
  adep : List Nat := []
  ddep : List Nat := []
  cdep : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- An event: its skeleton, its physical address, the bytes returned (loads) and written (stores). -/
structure Ev where
  sk : Skel
  pa : Nat
  rdat : List Nat
  wdat : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- An I/O region (a PMA, mm-explanatory.adoc:1155–1162): `[lo, hi)`, strongly ordered or not, its channel. -/
structure IoRegion where
  lo : Nat
  hi : Nat
  strong : Bool
  chan : Nat
  deriving DecidableEq, Repr

/-- A candidate execution: the initial memory, the I/O regions, the per-hart events and the global memory order. -/
structure Exec where
  img : Nat → Nat
  io : List IoRegion
  evs : List (List Ev)
  gmo : List EvId

/-- All identifiers of a per-hart list of lists. -/
def idsOf {α : Type} (L : List (List α)) : List EvId :=
  (List.range L.length).flatMap (fun h => (List.range (L[h]?.getD []).length).map (fun i => (h, i)))

namespace Exec

/-- The event with identifier `e` (a default for an invalid identifier; only `ids` are ever quantified over). -/
def ev (X : Exec) (e : EvId) : Ev := ((X.evs[e.1]?).bind (·[e.2]?)).getD default

def sk (X : Exec) (e : EvId) : Skel := (X.ev e).sk

def ids (X : Exec) : List EvId := idsOf X.evs

end Exec

/-- The position of `e` in the list `g` (its length when absent). -/
def pos (g : List EvId) (e : EvId) : Nat :=
  match g with
  | [] => 0
  | x :: t => if x = e then 0 else pos t e + 1

/-! ## 2. Value-independent rules (4–11, 13), over identifiers `I`, skeletons `S`, I/O class `io` -/

/-- Program order: same hart, earlier dynamic instruction. -/
def poS (S : EvId → Skel) (a b : EvId) : Bool := a.1 == b.1 && decide ((S a).ii < (S b).ii)

/-- FENCE predecessor-set membership (unpriv_rv32.adoc:770–776; "memory-mapped I/O devices will typically be
accessed with uncached loads and stores that are ordered using the I and O bits rather than the R and W bits",
:799–802).  An AMO is both a read and a write. -/
def inPred (S : EvId → Skel) (io : EvId → Bool) (f : FenceSet) (e : EvId) : Bool :=
  ((S e).kind.isLoad && !io e && f.pr) || ((S e).kind.isStore && !io e && f.pw) ||
  ((S e).kind.isLoad && io e && f.pi) || ((S e).kind.isStore && io e && f.po)

/-- FENCE successor-set membership. -/
def inSucc (S : EvId → Skel) (io : EvId → Bool) (f : FenceSet) (e : EvId) : Bool :=
  ((S e).kind.isLoad && !io e && f.sr) || ((S e).kind.isStore && !io e && f.sw) ||
  ((S e).kind.isLoad && io e && f.si) || ((S e).kind.isStore && io e && f.so)

/-- Rule 4 (rvwmo.adoc:286): "There is a FENCE instruction that orders a before b"; unpriv_rv32.adoc:818–819 "A
FENCE (with fm=0000) orders all memory operations in its predecessor set before all memory operations in its
successor set".  FENCE.TSO is TWO fence events (`fence r,rw` and `fence w,w`, same instruction index): it "orders
all load operations in its predecessor set before all memory operations in its successor set, and all store
operations in its predecessor set before all store operations in its successor set" (:823–826), which is exactly
the union of the two (plan §6 [R1.s2]; equivalently `fence r,r` + `fence rw,w`). -/
def rule4 (I : List EvId) (S : EvId → Skel) (io : EvId → Bool) (a b : EvId) : Bool :=
  I.any (fun m => match (S m).kind with
    | .fence f => poS S a m && poS S m b && inPred S io f a && inSucc S io f b
    | _ => false)

/-- Same class (both RAM or both I/O): the scope of rules 5–7 (mm-explanatory.adoc:1149–1153). -/
def sameCls (io : EvId → Bool) (a b : EvId) : Bool := io a == io b

/-- Rule 5 (rvwmo.adoc:287): "a has an acquire annotation" (acquire-RCpc or acquire-RCsc, :130–131). -/
def rule5 (S : EvId → Skel) (io : EvId → Bool) (a b : EvId) : Bool :=
  sameCls io a b && ((S a).aqPc || (S a).aqSc)

/-- Rule 6 (rvwmo.adoc:288): "b has a release annotation". -/
def rule6 (S : EvId → Skel) (io : EvId → Bool) (a b : EvId) : Bool :=
  sameCls io a b && ((S b).rlPc || (S b).rlSc)

/-- Rule 7 (rvwmo.adoc:289): "a and b both have RCsc annotations". -/
def rule7 (S : EvId → Skel) (io : EvId → Bool) (a b : EvId) : Bool :=
  sameCls io a b && ((S a).aqSc || (S a).rlSc) && ((S b).aqSc || (S b).rlSc)

/-- Pairing (rvwmo.adoc:114–118): "An lr instruction and an sc instruction are said to be paired if the lr
precedes the sc in program order and if there are no other lr or sc instructions in between"; the store operation
exists only for a successful SC ("except in case of a failed sc, where no store operation is generated", :117–118).
No address or width match (rvwmo.adoc:340–345; zalrsc.adoc:99–101). -/
def pairedS (I : List EvId) (S : EvId → Skel) (a b : EvId) : Bool :=
  (S a).kind == .lr && (S b).kind == .sc && poS S a b &&
    I.all (fun m => !(poS S a m && poS S m b && (S m).kind.isLrSc))

/-- Rule 8 (rvwmo.adoc:290): "a is paired with b". -/
def rule8 (I : List EvId) (S : EvId → Skel) (a b : EvId) : Bool := pairedS I S a b

/-- Rule 9 (rvwmo.adoc:293): "b has a syntactic address dependency on a". -/
def rule9 (S : EvId → Skel) (a b : EvId) : Bool := a.1 == b.1 && (S b).adep.contains a.2

/-- Rule 10 (rvwmo.adoc:294): "b has a syntactic data dependency on a" (a data dependency needs "b is a store
operation", :237–238). -/
def rule10 (S : EvId → Skel) (a b : EvId) : Bool :=
  (S b).kind.isStore && a.1 == b.1 && (S b).ddep.contains a.2

/-- Rule 11 (rvwmo.adoc:295): "b is a store, and b has a syntactic control dependency on a". -/
def rule11 (S : EvId → Skel) (a b : EvId) : Bool :=
  (S b).kind.isStore && a.1 == b.1 && (S b).cdep.contains a.2

/-- Rule 13 (rvwmo.adoc:301–302): "b is a store, and there exists some instruction m between a and b in program
order such that m has an address dependency on a".  `m` ranges over MEMORY OPERATIONS only: a failed SC "does not
give rise to any memory operations" (rvwmo.adoc:82) and is not an `m`.  This is the memory-operation reading,
matching the manual's formal appendix (`r13 = [R];addr;[M];po;[W]`), chosen by the owner over the literal
"instruction m" reading ([OWN.P6], 2026-11-02; K1-c in PROGRESS-S0P1.md).  It admits more executions than the
literal reading, so theorems proved against it also hold under that reading. -/
def rule13 (I : List EvId) (S : EvId → Skel) (a b : EvId) : Bool :=
  (S b).kind.isStore &&
    I.any (fun m => (S m).kind.isMem && poS S a m && poS S m b && (S m).adep.contains a.2)

/-- The value-independent rules 4–11 and 13 (no addresses, no rf; the I/O class only through `io`). -/
def staticRules (I : List EvId) (S : EvId → Skel) (io : EvId → Bool) (a b : EvId) : Bool :=
  rule4 I S io a b || rule5 S io a b || rule6 S io a b || rule7 S io a b || rule8 I S a b ||
  rule9 S a b || rule10 S a b || rule11 S a b || rule13 I S a b

/-- The value-independent part of preserved program order, guarded like `ppoB`.  Used by the candidate enumerator
to prune gmo linearisations (`Weak/Prom/RefCheck.lean`); `staticOrd ⊆ ppoB` is `staticOrd_ppo`. -/
def staticOrd (I : List EvId) (S : EvId → Skel) (io : EvId → Bool) (a b : EvId) : Bool :=
  (S a).kind.isMem && (S b).kind.isMem && poS S a b && staticRules I S io a b

/-! ## 3. Bytes, rf, and the value-dependent rules (1, 2, 3, 12) -/

/-- Event `v` accesses byte `x`. -/
def touches (v : Ev) (x : Nat) : Bool := decide (v.pa ≤ x ∧ x < v.pa + v.sk.sz)

/-- Event `v` is a store operation that writes byte `x`. -/
def writesB (v : Ev) (x : Nat) : Bool := v.sk.kind.isStore && touches v x

/-- The byte `v` writes at `x`. -/
def wbyte (v : Ev) (x : Nat) : Nat := (v.wdat[x - v.pa]?).getD 0

/-- Overlapping addresses. -/
def overlapB (u v : Ev) : Bool := decide (u.pa < v.pa + v.sk.sz ∧ v.pa < u.pa + u.sk.sz)

/-- An access to an I/O region. -/
def isIo (X : Exec) (e : EvId) : Bool :=
  X.io.any (fun r => decide (r.lo ≤ (X.ev e).pa ∧ (X.ev e).pa < r.hi))

/-- Program order on an execution. -/
def poX (X : Exec) (a b : EvId) : Bool := poS X.sk a b

/-- `a` precedes `b` in the order listed by `g`. -/
def gB (g : List EvId) (a b : EvId) : Bool :=
  g.contains a && g.contains b && decide (pos g a < pos g b)

/-- "a precedes b in the global memory order". -/
def gmoBefore (X : Exec) (a b : EvId) : Bool := gB X.gmo a b

/-- THE LOAD VALUE AXIOM'S STORE (rvwmo.adoc:315–324): "Each byte of each load i returns the value written to that
byte by the store that is the latest in global memory order among the following stores: 1. Stores that write that
byte and that precede i in the global memory order 2. Stores that write that byte and that precede i in program
order".  `none` = no such store: the initial value. -/
def rfSrc (X : Exec) (r : EvId) (x : Nat) : Option EvId :=
  (X.gmo.filter (fun w => writesB (X.ev w) x && (gmoBefore X w r || poX X w r))).getLast?

/-- The value the load value axiom prescribes for byte `x` of load `r`. -/
def lvVal (X : Exec) (r : EvId) (x : Nat) : Nat :=
  match rfSrc X r x with
  | some w => wbyte (X.ev w) x
  | none => X.img x

/-- Rule 1 (rvwmo.adoc:278): "b is a store, and a and b access overlapping memory addresses". -/
def rule1 (X : Exec) (a b : EvId) : Bool := (X.sk b).kind.isStore && overlapB (X.ev a) (X.ev b)

/-- Rule 2 (rvwmo.adoc:279–281): "a and b are loads, x is a byte read by both a and b, there is no store to x
between a and b in program order, and a and b return values for x written by different memory operations"
(the initial value counts as one writer, `rfSrc = none`). RAM loads only (rf is undefined for I/O). -/
def rule2 (X : Exec) (a b : EvId) : Bool :=
  (X.sk a).kind.isLoad && (X.sk b).kind.isLoad && !isIo X a && !isIo X b &&
    (List.range (X.sk a).sz).any (fun k =>
      touches (X.ev b) ((X.ev a).pa + k) &&
      X.ids.all (fun m => !(poX X a m && poX X m b && writesB (X.ev m) ((X.ev a).pa + k))) &&
      rfSrc X a ((X.ev a).pa + k) != rfSrc X b ((X.ev a).pa + k))

/-- Rule 3 (rvwmo.adoc:282–283): "a is generated by an AMO or sc instruction, b is a load, and b returns a value
written by a". -/
def rule3 (X : Exec) (a b : EvId) : Bool :=
  (X.sk a).kind.isRmwW && (X.sk b).kind.isLoad && !isIo X b &&
    (List.range (X.sk b).sz).any (fun k => rfSrc X b ((X.ev b).pa + k) == some a)

/-- Rule 12 (rvwmo.adoc:298–300): "b is a load, and there exists some store m between a and b in program order
such that m has an address or data dependency on a, and b returns a value written by m". -/
def rule12 (X : Exec) (a b : EvId) : Bool :=
  (X.sk b).kind.isLoad && !isIo X b &&
    X.ids.any (fun m => poX X a m && poX X m b && (X.sk m).kind.isStore &&
      ((X.sk m).adep.contains a.2 || (X.sk m).ddep.contains a.2) &&
      (List.range (X.sk b).sz).any (fun k => rfSrc X b ((X.ev b).pa + k) == some m))

/-- PRESERVED PROGRAM ORDER (rvwmo.adoc:267–302): "memory operation a precedes memory operation b in preserved
program order (and hence also in the global memory order) if a precedes b in program order, a and b both access
regular main memory (rather than I/O regions), and any of the following hold" — rules 1–13; with
mm-explanatory.adoc:1146–1153 extending them to I/O accesses except aq/rl across classes. -/
def ppoB (X : Exec) (a b : EvId) : Bool :=
  (X.sk a).kind.isMem && (X.sk b).kind.isMem && poX X a b &&
    (rule1 X a b || rule2 X a b || rule3 X a b || staticRules X.ids X.sk (isIo X) a b || rule12 X a b)

/-- The I/O region of an access. -/
def regionOf (X : Exec) (e : EvId) : Option IoRegion :=
  X.io.find? (fun r => decide (r.lo ≤ (X.ev e).pa ∧ (X.ev e).pa < r.hi))

/-- I/O ORDERING rules (2)–(5) (mm-explanatory.adoc:1154–1162): "a and b are accesses to overlapping addresses in
an I/O region"; "a and b are accesses to the same strongly ordered I/O region"; "a and b are accesses to I/O
regions, and the channel associated with the I/O region accessed by either a or b is channel 1"; "a and b are
accesses to I/O regions associated with the same channel (except for channel 0)". -/
def ioOrdB (X : Exec) (a b : EvId) : Bool :=
  (X.sk a).kind.isMem && (X.sk b).kind.isMem && poX X a b &&
    match regionOf X a, regionOf X b with
    | some ra, some rb =>
        overlapB (X.ev a) (X.ev b) || (ra == rb && ra.strong) || ra.chan == 1 || rb.chan == 1 ||
          (ra.chan == rb.chan && ra.chan != 0)
    | _, _ => false

/-- Every ordering gmo must respect. -/
def orderedB (X : Exec) (a b : EvId) : Bool := ppoB X a b || ioOrdB X a b

/-! ## 4. The axioms -/

/-- gmo is a total order (a duplicate-free list) of exactly the memory operations. -/
def gmoWf (X : Exec) : Prop :=
  X.gmo.Nodup ∧ (∀ e ∈ X.gmo, e ∈ X.ids ∧ (X.sk e).kind.isMem = true) ∧
    (∀ e ∈ X.ids, (X.sk e).kind.isMem = true → e ∈ X.gmo)

/-- A load returns, and a store writes, exactly its size in bytes. -/
def evWf (X : Exec) : Prop :=
  ∀ e ∈ X.ids, ((X.sk e).kind.isLoad = true → (X.ev e).rdat.length = (X.sk e).sz) ∧
    ((X.sk e).kind.isStore = true → (X.ev e).wdat.length = (X.sk e).sz)

/-- gmo CONFORMS TO preserved program order (and the I/O orderings): rvwmo.adoc:308–311 "there exists a global
memory order conforming to preserved program order" (:307–310). -/
def ppoAx (X : Exec) : Prop :=
  ∀ a ∈ X.ids, ∀ b ∈ X.ids, orderedB X a b = true → gmoBefore X a b = true

/-- THE LOAD VALUE AXIOM (rvwmo.adoc:315–324), byte-wise, for RAM loads (I/O: mm-explanatory.adoc:1139–1140). -/
def loadValueAx (X : Exec) : Prop :=
  ∀ r ∈ X.ids, (X.sk r).kind.isLoad = true → isIo X r = false →
    ∀ k < (X.sk r).sz, (X.ev r).rdat[k]? = some (lvVal X r ((X.ev r).pa + k))

/-- Natural alignment. -/
def aligned (v : Ev) : Bool := v.pa % v.sk.sz == 0

/-- THE ATOMICITY AXIOM (rvwmo.adoc:331–337): "If r and w are paired load and store operations generated by aligned
lr and sc instructions in a hart h, s is a store to byte x, and r returns a value written by s, then s must precede
w in the global memory order, and there can be no store from a hart other than h to byte x following s and
preceding w in the global memory order."  Quantified over the LR's bytes (mismatched pairs, :340–345). -/
def atomicityAx (X : Exec) : Prop :=
  ∀ r ∈ X.ids, ∀ w ∈ X.ids, pairedS X.ids X.sk r w = true → aligned (X.ev r) = true →
    aligned (X.ev w) = true → ∀ k < (X.sk r).sz, ∀ s ∈ (rfSrc X r ((X.ev r).pa + k)).toList,
      gmoBefore X s w = true ∧
      ∀ s' ∈ X.ids, writesB (X.ev s') ((X.ev r).pa + k) = true → s'.1 ≠ r.1 →
        ¬ (gmoBefore X s s' = true ∧ gmoBefore X s' w = true)

/-- The reservation of the LR `r` admits the successful SC `w`: SOME reservation set `R` "that subsumes the bytes in
the addressed word" (zalrsc.adoc:9–10; "An implementation can register an arbitrarily large reservation set on each
lr, provided the reservation set includes all bytes of the addressed data word or doubleword", :91–93) contains
the SC's bytes ("the sc.w succeeds only if the reservation is still valid and the reservation set contains the bytes
being written", :11–13; :117–118 "must fail if the address is not within the reservation set"), and "no store from
another hart to the reservation set can be observed to have occurred between the lr and the sc" (:94–97, :118–120;
"between" read as gmo-between). -/
def resvOk (X : Exec) (r w : EvId) : Prop :=
  ∃ R : List Nat, (∀ x, touches (X.ev r) x = true → x ∈ R) ∧ (∀ x, touches (X.ev w) x = true → x ∈ R) ∧
    ∀ s ∈ X.ids, (X.sk s).kind.isStore = true → s.1 ≠ w.1 → (∃ x ∈ R, writesB (X.ev s) x = true) →
      ¬ (gmoBefore X r s = true ∧ gmoBefore X s w = true)

/-- THE §zalrsc SUCCESS CONDITIONS for every successful SC: it pairs with an LR (zalrsc.adoc:93–94 "An sc can only
pair with the most recent lr in program order", 123–125 "An sc must fail if there is another sc (to any address)
between the lr and the sc in program order", :23–24 "Regardless of success or failure, executing an sc.w
instruction invalidates any reservation held by this hart") whose reservation admits it (`resvOk`).  The device
conditions (:97–99, :120–122) are vacuous: no device agents (phase 1).  A failed SC needs nothing: "these
definitions permit an implementation to fail an sc instruction occasionally for any reason" (:245–246). -/
def scAx (X : Exec) : Prop :=
  ∀ w ∈ X.ids, (X.sk w).kind = .sc → ∃ r ∈ X.ids, pairedS X.ids X.sk r w = true ∧ resvOk X r w

/-- THE PROGRESS AXIOM (rvwmo.adoc:350–351): "No memory operation may be preceded in the global memory order by an
infinite sequence of other memory operations."  Stated literally (an injective sequence of gmo-predecessors); it
holds for every finite execution (`progressFin`). -/
def progressAx (X : Exec) : Prop :=
  ∀ e ∈ X.gmo, ¬ ∃ f : Nat → EvId, (∀ n m, f n = f m → n = m) ∧ ∀ n, gmoBefore X (f n) e = true

/-- The decidable part of the model. -/
def refCore (X : Exec) : Prop :=
  gmoWf X ∧ evWf X ∧ ppoAx X ∧ loadValueAx X ∧ atomicityAx X ∧ scAx X

/-- **`rvwmoRef`**: rvwmo.adoc:307–310 "An execution of a RISC-V program obeys the RVWMO memory consistency model
only if there exists a global memory order conforming to preserved program order and satisfying the load value
axiom, the atomicity axiom, and the progress axiom" — plus the §zalrsc success conditions of the SCs that
succeeded (zalrsc.adoc:125–126 "The precise statement of the atomicity requirements for successful lr/sc sequences
is defined by the Atomicity Axiom"; the conditions under which an SC may succeed are §zalrsc's, rvwmo.adoc:118–120).
WITHOUT `DTtrans`/`DTctx` (plan §6). -/
def rvwmoRef (X : Exec) : Prop := refCore X ∧ progressAx X

/-- The final value of byte `x`: the gmo-last store to it, else the initial value. -/
def finalByte (X : Exec) (x : Nat) : Nat :=
  match (X.gmo.filter (fun w => writesB (X.ev w) x)).getLast? with
  | some w => wbyte (X.ev w) x
  | none => X.img x

/-! ## 5. Decidability: the reservation set (minimal witness), and the reflective checker -/

/-- The bytes of an event. -/
def bytesOf (v : Ev) : List Nat := (List.range v.sk.sz).map (v.pa + ·)

theorem mem_bytesOf (v : Ev) (x : Nat) : touches v x = true → x ∈ bytesOf v := by
  intro h
  simp only [touches, decide_eq_true_eq] at h
  simp only [bytesOf, List.mem_map, List.mem_range]
  exact ⟨x - v.pa, by omega, by omega⟩

theorem touches_of_mem_bytesOf (v : Ev) (x : Nat) : x ∈ bytesOf v → touches v x = true := by
  simp only [bytesOf, List.mem_map, List.mem_range, touches, decide_eq_true_eq]
  rintro ⟨k, hk, rfl⟩
  omega

/-- The reservation check with the MINIMAL reservation set (the LR's bytes and the SC's bytes): the no-store
condition is monotone in `R`, so a reservation set exists iff this one works (`resvOkB_iff`). -/
def resvOkB (X : Exec) (r w : EvId) : Bool :=
  X.ids.all (fun s => !((X.sk s).kind.isStore && s.1 != w.1 &&
    (bytesOf (X.ev r) ++ bytesOf (X.ev w)).any (fun x => writesB (X.ev s) x) &&
    gmoBefore X r s && gmoBefore X s w))

theorem resvOkB_iff (X : Exec) (r w : EvId) : resvOkB X r w = true ↔ resvOk X r w := by
  constructor
  · intro h
    refine ⟨bytesOf (X.ev r) ++ bytesOf (X.ev w), fun x hx => List.mem_append_left _ (mem_bytesOf _ _ hx),
      fun x hx => List.mem_append_right _ (mem_bytesOf _ _ hx), ?_⟩
    intro s hs hst hne ⟨x, hx, hwx⟩ ⟨h1, h2⟩
    have := (List.all_eq_true.1 h) s hs
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at this
    have hany : (bytesOf (X.ev r) ++ bytesOf (X.ev w)).any (fun x => writesB (X.ev s) x) = true :=
      List.any_eq_true.2 ⟨x, hx, hwx⟩
    have hne' : (s.1 != w.1) = true := by simpa using hne
    rcases this with ((((h | h) | h) | h) | h) <;> simp_all
  · rintro ⟨R, hr, hw, hs⟩
    apply List.all_eq_true.2
    intro s hsm
    simp only [Bool.not_eq_true']
    cases hst : (X.sk s).kind.isStore <;> simp only [Bool.false_and, Bool.true_and]
    cases hne : (s.1 != w.1) <;> simp only [Bool.false_and, Bool.true_and]
    cases hany : (bytesOf (X.ev r) ++ bytesOf (X.ev w)).any (fun x => writesB (X.ev s) x) <;>
      simp only [Bool.false_and, Bool.true_and]
    cases h1 : gmoBefore X r s <;> simp only [Bool.false_and, Bool.true_and]
    cases h2 : gmoBefore X s w
    · rfl
    · exfalso
      obtain ⟨x, hx, hwx⟩ := List.any_eq_true.1 hany
      have hxR : x ∈ R := by
        rcases List.mem_append.1 hx with hx | hx
        · exact hr x (touches_of_mem_bytesOf _ _ hx)
        · exact hw x (touches_of_mem_bytesOf _ _ hx)
      exact hs s hsm hst (by simpa using hne) ⟨x, hxR, hwx⟩ ⟨h1, h2⟩

instance (X : Exec) (r w : EvId) : Decidable (resvOk X r w) :=
  decidable_of_iff _ (resvOkB_iff X r w)

instance (X : Exec) : Decidable (gmoWf X) := by unfold gmoWf; infer_instance
instance (X : Exec) : Decidable (evWf X) := by unfold evWf; infer_instance
instance (X : Exec) : Decidable (ppoAx X) := by unfold ppoAx; infer_instance
instance (X : Exec) : Decidable (loadValueAx X) := by unfold loadValueAx; infer_instance
instance (X : Exec) : Decidable (atomicityAx X) := by unfold atomicityAx; infer_instance
instance (X : Exec) : Decidable (scAx X) := by unfold scAx; infer_instance
instance (X : Exec) : Decidable (refCore X) := by unfold refCore; infer_instance

/-- **The reflective checker** (the `catTConsistentB` pattern, AxDeps.lean:1337): a Bool, evaluated by the kernel
(`decide +kernel`; never `native_decide`). -/
def refCoreB (X : Exec) : Bool := decide (refCore X)

/-! ## 6. Progress holds for every finite execution -/

/-- Pigeonhole: a duplicate-free list inside `L` is no longer than `L`. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (l L : List α), l.Nodup → (∀ x ∈ l, x ∈ L) → l.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, L, hn, hs => by
    have ha : a ∈ L := hs a (List.mem_cons_self ..)
    have hnt : t.Nodup := (List.nodup_cons.1 hn).2
    have hat : a ∉ t := (List.nodup_cons.1 hn).1
    have hsub : ∀ x ∈ t, x ∈ L.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hat (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).2 (hs x (List.mem_cons_of_mem _ hx))
    have := nodup_length_le t (L.erase a) hnt hsub
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < L.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem progressFin (X : Exec) : progressAx X := by
  intro e _ ⟨f, hinj, hb⟩
  have hmem : ∀ n, f n ∈ X.gmo := by
    intro n
    have := hb n
    simp only [gmoBefore, gB, Bool.and_eq_true, List.contains_iff_mem] at this
    exact this.1.1
  let l := (List.range (X.gmo.length + 1)).map f
  have hnd : l.Nodup :=
    List.pairwise_map.2 (List.nodup_range.imp (fun h1 h2 => h1 (hinj _ _ h2)))
  have hsub : ∀ x ∈ l, x ∈ X.gmo := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 hx
    exact hmem n
  have := nodup_length_le l X.gmo hnd hsub
  simp [l] at this
  omega

theorem rvwmoRef_iff (X : Exec) : rvwmoRef X ↔ refCore X :=
  ⟨fun h => h.1, fun h => ⟨h, progressFin X⟩⟩

/-- SOUNDNESS of the reflective checker. -/
theorem refCoreB_sound (X : Exec) : refCoreB X = true → rvwmoRef X :=
  fun h => (rvwmoRef_iff X).2 (of_decide_eq_true h)

/-- COMPLETENESS of the reflective checker. -/
theorem refCoreB_complete (X : Exec) : rvwmoRef X → refCoreB X = true :=
  fun h => decide_eq_true ((rvwmoRef_iff X).1 h)

/-! ## 7. Structural facts used by the enumerator -/

theorem staticOrd_ppo (X : Exec) (a b : EvId) :
    staticOrd X.ids X.sk (isIo X) a b = true → ppoB X a b = true := by
  simp only [staticOrd, ppoB, poX, Bool.and_eq_true, Bool.or_eq_true]
  rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨⟨⟨h1, h2⟩, h3⟩, Or.inl (Or.inr h4)⟩

theorem ppo_ordered (X : Exec) (a b : EvId) : ppoB X a b = true → orderedB X a b = true := by
  intro h; simp [orderedB, h]

/-- An execution without I/O regions has no I/O access. -/
theorem isIo_nil (X : Exec) (h : X.io = []) (e : EvId) : isIo X e = false := by
  simp [isIo, h]

end Weak.Prom.Ref
