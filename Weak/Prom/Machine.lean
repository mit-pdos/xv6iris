/-
Weak/Prom: **machine v2** — the Promising-RISC-V machine of the plan of record (rev 7), definitions only (S1M-def).

Plan: `~/dev/weak-orch/promising/plan.md` §1 (M0–M21) and §8 S1M; owner rulings [OWN.P1] (model every behaviour a
permissive sentence allows), [OWN.P2] (instruction fetch and FENCE.I faithful to Zifencei), [OWN.P3] (OQ-1 punted:
this increment covers programs that never enable address translation).  Quotes are from the RISC-V ISA manual
`riscv/riscv-isa-manual` @ `e17d92a1` (copies in `~/dev/weak-orch/promising/spec/`): `rvwmo.adoc` (§rvwmo),
`zalrsc.adoc`, `zaamo.adoc`, `zifencei.adoc`.

A NEW machine: nothing here changes `Weak/WeakPromise.lean` (today's machine) or `Weak/WeakMem.lean`; only the
vocabulary `Image`/`Dsrc` is shared.  Marks (plan §0): FAITHFUL = same behaviours as the reference; WEAKER = more
behaviours (sound); STRONGER = fewer (unsound for (T-cmp)); INERT = bookkeeping that orders nothing.

## Shape

* Memory is ONE append-only list of messages (Pulte et al. PLDI'19); timestamp 0 is the image, timestamp `k + 1` the
  log entry `k`.  Messages are byte runs; a promise appends a whole message, and a fulfil matches it exactly.
* Each agent has a `PState` (views, banks, the LR reservation `wRes`, the AMO slot `wRmw`, the fetch views) and a
  promise set.  The machine is UNCERTIFIED (M8; Pulte Thm 6.2/D.2): `promise` is unconditional.
* One step is `pmStep pstep cfg ev cfg'`, labelled by the event `ev : PEvt` (a promise, or a state step with its
  label and its fulfil timestamp), so a run's trace (plan §0 [R4.5]) is the list of its events.
* The memory half of a state step is `memStep`, a FUNCTION OF THE LABEL (one constructor per arm, Table C's C-A
  family); the program half is the abstract LTS `pstep` (instantiated with Sail by `Weak/Prom/Emit.lean`).

## Invariants the definitions are written to keep ([R7.s1])

* Every arm is APPEND-STABLE: a premise reads the log only inside windows `(lo, hi]` whose upper end is a view or a
  fulfilled timestamp (never the log length), so appending promised messages at the end never changes a state
  step's admissibility.  No arm has a "latest message present" floor (`LLoad` has no `lat` field, SR-31).
* Every arm is OWN-PROMISE-MONOTONE: the only premise that reads the promise set besides the fulfil membership is
  `ownDone` ("this own message is already fulfilled"), which a NEW promise (a fresh timestamp) never changes.
* `cfgWf` bounds every view, `wRes`, `wRmw` and the fetch views by the log length.

## Extension points left by [OWN.P3] (translation deferred; see PROGRESS-S1Mdef.md)

Not present, by design: walk reads (M14/M18: a label `LWalk`, a per-access walk bank consumed by the access's
pre-view and never by `ctrl`), `LSfence` and its floor `wSfv` (M18, D-S0-1), the A/D pair (M20: labels
`LAdRd`/`LAdWr`, the class `ad`, arms `WPAd`/`WPAspec`), the translation cache (M21, emission only).  The
programs this file is used with are those that never enable translation (`Emit.translationOff`).
-/
import Weak.WeakMem

namespace Weak.Prom

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)

/-! ## 1. Messages and memory -/

/-- The three cache-block management operations (cmo.adoc:116–126): an invalidate "deallocates the copy of the cache
block", a clean "performs a write transfer … if the data … have been modified", a flush "atomically performs a clean
operation followed by an invalidate operation". -/
inductive CmoKind where
  | inval
  | clean
  | flush
  deriving DecidableEq, Inhabited, Repr

/-- THE MESSAGE CLASS (plan M20 (5), N-10): bookkeeping that orders nothing (INERT), fixed at the promise and
checked at the fulfil, so the final memory says which messages are plain, release or exclusive writes.  The
A/D class `ad` of M20 (5) is added together with the A/D arm (deferred, [OWN.P3]). -/
inductive PClass where
  | plain
  | rel
  | excl
  /-- A cache-block management operation (Zicbom) on `[pa, pa + len)`: writes no byte (its message has
  `data = []`), is a gmo event that "behave[s] as stores in the PPO rules" (cmo.adoc:235), and changes load values
  (cmo.adoc:259–274, `invalRead`). -/
  | cmo (k : CmoKind) (len : Nat)
  deriving DecidableEq, Inhabited, Repr

/-- One write event: the bytes `data` at `[pa, pa + |data|)`, its author, its class. -/
structure PMsg where
  pa : Int
  data : List (BitVec 8)
  tid : Option Nat
  cls : PClass
  deriving DecidableEq, Inhabited

/-- The byte message `m` writes at address `a` (`none` outside its range). -/
def PMsg.byteAt (m : PMsg) (a : Int) : Option (BitVec 8) :=
  if m.pa ≤ a then m.data[(a - m.pa).toNat]? else none

/-- Memory at timestamp `t`: the image at `0`, log entry `t - 1` otherwise. -/
def memByte (img : Image) (log : List PMsg) (t : Nat) (a : Int) : Option (BitVec 8) :=
  match t with
  | 0 => img a
  | k + 1 => log[k]?.bind (fun m => m.byteAt a)

/-- `writesIn log a lo hi`: some timestamp in `(lo, hi]` writes byte `a`. -/
def writesIn (log : List PMsg) (a : Int) (lo hi : Nat) : Prop :=
  ∃ t : Nat, lo < t ∧ t ≤ hi ∧ ∃ m, log[t - 1]? = some m ∧ (m.byteAt a).isSome = true

/-- `writesIn` restricted to authors satisfying `Q`. -/
def writesInBy (log : List PMsg) (Q : Option Nat → Prop) (a : Int) (lo hi : Nat) : Prop :=
  ∃ t : Nat, lo < t ∧ t ≤ hi ∧ ∃ m, log[t - 1]? = some m ∧ (m.byteAt a).isSome = true ∧ Q m.tid

/-- `ownDone log i prom t`: timestamp `t` is a message of agent `i` that `i` has already fulfilled, i.e. (in the
state phase) a po-earlier store of `i`.  Used by the own-store exemption of PA-1f (`LIFetch`). -/
def ownDone (log : List PMsg) (i : Nat) (prom : GSet Nat) (t : Nat) : Bool :=
  match log[t - 1]? with
  | some m => decide (1 ≤ t) && decide (m.tid = some i) && !(decide (t ∈ prom))
  | none => false

/-- Timestamp `t` is a cache-block operation covering byte `a` whose kind satisfies `p`. -/
def cmoAt (log : List PMsg) (p : CmoKind → Bool) (t : Nat) (a : Int) : Prop :=
  ∃ m k len, log[t - 1]? = some m ∧ m.cls = .cmo k len ∧ p k = true ∧ m.pa ≤ a ∧ a < m.pa + len

/-- An invalidate-class operation (an invalidate, or a flush, which includes one). -/
def isInvalK : CmoKind → Bool
  | .inval | .flush => true
  | .clean => false

/-- A clean-class operation (a clean, or a flush, which includes one). -/
def isCleanK : CmoKind → Bool
  | .clean | .flush => true
  | .inval => false

/-- THE INVALIDATE CLAUSE OF THE LOAD VALUE AXIOM ([OWN.P1], Table S CMO-6), byte `a`, answer `t`, floor `fl`.
cmo.adoc:259–274: "If an invalidate operation i precedes a load r and operates on a byte x returned by r, and no
store to x appears between i and r in program order or in the global memory order, then r returns any of the
following values for x: 1. If no clean or flush operations on x precede i in the global memory order, either the
initial value of x or the value of any store to x that precedes i; 2. If no store to x precedes a clean or flush
operation on x in the global memory order and if the clean or flush operation on x precedes i in the global memory
order, either the initial value of x or the value of any store to x that precedes i; 3. If a store to x precedes a
clean or flush operation on x in the global memory order and if the clean or flush operation on x precedes i in the
global memory order, either the value of the latest store to x that precedes the latest clean or flush operation on
x or the value of any store to x that both precedes i and succeeds the latest clean or flush operation on x that
precedes i" (the fourth bullet, non-coherent agents, has no instance: every agent here is coherent).
Rendering: some invalidate-class `ti` covering `a` is the latest one at or below the read point `max(fl, ti)`, no
byte write to `a` lies in `(ti, fl]` (no store between `i` and `r`; an own po-intervening store raised `coh`, hence
`fl`), `t < ti`, and no byte write to `a` lies in `(t, c)` for any clean-class `c < ti` (bullets 2–3: `t` is the
latest store before the latest clean, or later; `t = 0`, the initial value, only if no store precedes it).  The
load's post-view does NOT absorb `ti` ("i precedes r" would order `r` after `i`): WEAKER, sound. -/
def invalRead (log : List PMsg) (a : Int) (t fl : Nat) : Prop :=
  ∃ ti, cmoAt log isInvalK ti a ∧ t < ti ∧
    ¬ writesIn log a ti fl ∧
    (¬ ∃ ti', ti < ti' ∧ ti' ≤ max fl ti ∧ cmoAt log isInvalK ti' a) ∧
    ∀ c, c < ti → cmoAt log isCleanK c a → ¬ writesIn log a t (c - 1)

/-! ### Byte runs -/

/-- A run of answered bytes `(t, v)` at consecutive addresses from `a`: `bytesAll P a tvs` says `P` of each. -/
def bytesAll (P : Int → Nat → BitVec 8 → Prop) : Int → List (Nat × BitVec 8) → Prop
  | _, [] => True
  | a, (t, v) :: r => P a t v ∧ bytesAll P (a + 1) r

/-- The maximum of `f a t` over a run. -/
def bytesMax (f : Int → Nat → Nat) : Int → List (Nat × BitVec 8) → Nat
  | _, [] => 0
  | a, (t, _) :: r => max (f a t) (bytesMax f (a + 1) r)

/-- "No write by another agent than `i` to byte `a + j` in `(t_j, ts)`" for every byte of the run `rts` (PARM's
`Memory.exclusive`): the atomicity axiom's window (§rvwmo, "Atomicity Axiom … there is no store from another hart
to x between r and w in global memory order"). -/
def exclOk (log : List PMsg) (i : Nat) : Int → List Nat → Nat → Prop
  | _, [], _ => True
  | a, t :: r, ts => ¬ writesInBy log (fun tid => tid ≠ some i) a t (ts - 1) ∧ exclOk log i (a + 1) r ts

/-! ## 2. The agent state -/

/-- THE LR RESERVATION (M16): the LR's base, per-byte read timestamps and its post-view (M5: rule 8's view). -/
structure PResv where
  rvBase : Int
  rvTs : List Nat
  rvView : Nat
  deriving DecidableEq, Inhabited

/-- THE AMO SLOT (M10 (1)): written by an AMO's read half, consumed by its write half; separate from `wRes`, so an
AMO never touches an LR reservation.  `rmAq` is the read half's aq bit (M10 (2): "aq comes from the read half"). -/
structure PRmw where
  rmBase : Int
  rmTs : List Nat
  rmAq : Bool
  deriving DecidableEq, Inhabited

/-- THE AGENT STATE of machine v2.  Fields (Table C family C-F):
* `wCoh` — per-byte coherence floor (PARM `coh`);
* `wVrOld`/`wVwOld` — max post-view of past loads / stores; `wVrNew`/`wVwNew` — pre-view floors for future loads /
  stores (fences, acquire); `wVRel` — the release view (rule 7 RCsc: a later acquire reads after it);
* `wFwd` — the forward bank: per byte, the timestamp of the hart's latest own store and its FORWARD VIEW (M2: the
  store's address ⊔ data view, rule 12; M1: the timestamp itself for an exclusive write, rule 3);
* `wRegv` — register views (PARM `rmap`); `wVcap` — the control/address-capture view (rules 11, 13); `wLdv` — the
  current instruction's load-result view (`DLdRes`);
* `wRes` — the LR reservation (M16; survives loads, stores, fences, AMOs and instruction boundaries);
* `wRmw` — the AMO slot (M10 (1));
* `wIfl` — the FETCH FLOOR raised by FENCE.I ([OWN.P2]); `wIfr` — the maximum source timestamp of every fetch so far
  (FENCE.I orders earlier fetches before later ones); `wIfv` — the current instruction's fetch view (PA-1f).
Dropped from today's `Wstate` (WeakMem.lean:320–334): `wPub`/`wRelp` (INERT: "no view effect reads `wPub`/`wRelp`
except to compute them", WbPrimed.lean:17) and `wTbank` (M14: the W-TV bank is STRONGER; walks are deferred). -/
structure PState where
  wCoh : GMapF Int Nat
  wVrOld : Nat
  wVwOld : Nat
  wVrNew : Nat
  wVwNew : Nat
  wVRel : Nat
  wFwd : GMapF Int (Nat × Nat)
  wRegv : GMapF Nat Nat
  wVcap : Nat
  wLdv : Nat
  wRes : Option PResv
  wRmw : Option PRmw
  wIfl : Nat
  wIfr : Nat
  wIfv : Nat

/-- The initial agent state: every view `0`, no reservation, no AMO in flight. -/
def psInit : PState where
  wCoh := ∅
  wVrOld := 0
  wVwOld := 0
  wVrNew := 0
  wVwNew := 0
  wVRel := 0
  wFwd := ∅
  wRegv := ∅
  wVcap := 0
  wLdv := 0
  wRes := none
  wRmw := none
  wIfl := 0
  wIfr := 0
  wIfv := 0

/-- Coherence lookup with default 0. -/
def coh (ws : PState) (a : Int) : Nat := (get? ws.wCoh a).getD 0

/-- Register-view lookup with default 0. -/
def regv (ws : PState) (r : Nat) : Nat := (get? ws.wRegv r).getD 0

/-- The view of a dependency source (PARM `sem_expr`). -/
def dsrcView (ws : PState) : Dsrc → Nat
  | .DReg r => regv ws r
  | .DLdRes => ws.wLdv

/-- The view of a syntactic source list: the max of its members' views (`0` for `[]`). -/
def srcsView (ws : PState) (srcs : List Dsrc) : Nat :=
  srcs.foldr (fun s v => max (dsrcView ws s) v) 0

/-! ## 3. Pre-views -/

/-- THE LOAD PRE-VIEW (PARM `read`'s `view_pre`): the address view `va` (rule 9, M3), the current instruction's
fetch view (PA-1f, zifencei.adoc:107–108 "An instruction fetch is always ordered before any explicit memory accesses
that instruction gives rise to"), the load floor `vrNew` (fences, acquire; rules 4, 5), and, for an acquire, the
release view (rule 7 RCsc: "a and b both have RCsc annotations"). -/
def ldPre (ws : PState) (aq : Bool) (va : Nat) : Nat :=
  max va (max ws.wIfv (max ws.wVrNew (if aq then ws.wVRel else 0)))

/-- THE STORE PRE-VIEW (PARM `writable`'s `view_pre`): address and data views `va`, `vd` (rules 9, 10), the fetch
view (PA-1f), the capture view `vcap` (rules 11, 13), the store floor `vwNew` (fences, acquire), and for a release
`vrOld ⊔ vwOld` (rule 6: "b has a release annotation"). -/
def stPre (ws : PState) (rl : Bool) (va vd : Nat) : Nat :=
  max va (max vd (max ws.wIfv (max ws.wVcap (max ws.wVwNew (if rl then max ws.wVrOld ws.wVwOld else 0)))))

/-! ## 4. Reads -/

/-- Is the answer `t` at byte `a` the hart's own latest store to `a` (store-buffer forwarding)? -/
def fwdHit (ws : PState) (a : Int) (t : Nat) : Bool :=
  match get? ws.wFwd a with
  | some (tf, _) => t == tf
  | none => false

/-- THE FORWARDED VIEW of an answer (PARM `FwdItem.read_view`): a forwarded byte gets the store's forward view
(M2, rule 12; M1, rule 3 for an exclusive write, whose forward view is its own timestamp); an acquire, or a
non-forwarded byte, gets the timestamp itself. -/
def fwdView (ws : PState) (aq : Bool) (a : Int) (t : Nat) : Nat :=
  if aq then t
  else match get? ws.wFwd a with
    | some (tf, vf) => if t = tf then vf else t
    | none => t

/-- The common read point's closed form (M9, [R2.s1]): the max of the non-forwarded answers. -/
def nonFwdMax (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) : Nat :=
  bytesMax (fun a t => if fwdHit ws a t then 0 else t) base tvs

/-- THE READ ADMISSIBILITY of an explicit load-like access (plain load, LR, AMO read), at pre-view `vpre`.
Each byte returns the byte some write (or the image) holds at its timestamp, and no write to that byte lies between
its timestamp and the floor.  M9 (single-copy atomicity, §rvwmo "All memory operations are single-copy atomic: they
can never be observed in a partially complete state"): the floor of every NON-forwarded byte is raised to the
common read point `p₀ = max(vpre, max t_k)`; a byte FORWARDED from the hart's own latest store keeps the floor
`vpre ⊔ coh` (the load value axiom's po clause, "Stores that write that byte and that precede i in program order").
The exemption is the WEAKER-or-FAITHFUL side (S3c decides it, plan M9).  Alternatively a byte may return a value
the invalidate clause allows (`invalRead`; such a byte is exempt from the common point, WEAKER-or-FAITHFUL). -/
def loadOk (img : Image) (log : List PMsg) (ws : PState) (vpre : Nat) (base : Int)
    (tvs : List (Nat × BitVec 8)) : Prop :=
  bytesAll (fun a t v =>
      memByte img log t a = some v ∧
      (¬ writesIn log a t
          (max (if fwdHit ws a t then vpre else max vpre (nonFwdMax ws base tvs)) (coh ws a)) ∨
        invalRead log a t (max vpre (coh ws a))))
    base tvs

/-- The per-byte read update (today's `loadPostAt`, WeakMem.lean:618, minus the reservation clear (M16) and the
translation bank (M14)): coherence takes the raw timestamp and the forwarded post-view; `vrOld` and the load-result
view `wLdv` take the post-view; an acquire raises both new-floors (rule 5). -/
def loadByte (ws : PState) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) : PState :=
  let vpost := max vpre (fwdView ws aq a t)
  { ws with
    wCoh := insert ws.wCoh a (max (coh ws a) (max vpost t))
    wVrOld := max ws.wVrOld vpost
    wVrNew := if aq then max ws.wVrNew vpost else ws.wVrNew
    wVwNew := if aq then max ws.wVwNew vpost else ws.wVwNew
    wLdv := max ws.wLdv vpost }

/-- The run-level byte fold, at the pre-view computed once (a read leaves the forward bank alone, so every byte
reads the entry state's bank). -/
def loadBytes (aq : Bool) (vpre : Nat) : PState → Int → List (Nat × BitVec 8) → PState
  | ws, _, [] => ws
  | ws, a, (t, _) :: r => loadBytes aq vpre (loadByte ws aq vpre a t) (a + 1) r

/-- THE RUN-LEVEL READ: the byte fold, then `vcap ⊔= va` (PARM `vcap ⊔= view(addr)`, rule 13's address
capture).  `va` is the address view only; no walk or fetch view reaches `vcap` (M14). -/
def loadRun (ws : PState) (aq : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : PState :=
  let ws1 := loadBytes aq (ldPre ws aq va) ws base tvs
  { ws1 with wVcap := max va ws1.wVcap }

/-- The read's post-view (the max per-byte post-view): an LR's rule-8 view (M5). -/
def readView (ws : PState) (aq : Bool) (va : Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : Nat :=
  max (ldPre ws aq va) (bytesMax (fun a t => fwdView ws aq a t) base tvs)

/-! ## 5. Writes -/

/-- COH (PARM `writable`'s coherence conjunct): every written byte's coherence floor is below `ts`. -/
def cohBelow (ws : PState) : Int → Nat → Nat → Prop
  | _, 0, _ => True
  | a, n + 1, ts => coh ws a < ts ∧ cohBelow ws (a + 1) n ts

/-- Raise the coherence floor of `len` bytes from `a` to `ts`. -/
def cohRaise : PState → Int → Nat → Nat → PState
  | ws, _, 0, _ => ws
  | ws, a, n + 1, ts => cohRaise { ws with wCoh := insert ws.wCoh a (max (coh ws a) ts) } (a + 1) n ts

/-- The per-byte write update: coherence takes `ts`, the forward bank records `(ts, fv)`. -/
def storeBytes : PState → Int → Nat → Nat → Nat → PState
  | ws, _, 0, _, _ => ws
  | ws, a, n + 1, ts, fv =>
      storeBytes { ws with wCoh := insert ws.wCoh a (max (coh ws a) ts), wFwd := insert ws.wFwd a (ts, fv) }
        (a + 1) n ts fv

/-- THE RUN-LEVEL WRITE: the byte fold with forward view `fv`, `vwOld ⊔= ts`, a release raises `vRel` (rule 7),
and `vcap ⊔= va` (rule 13).  No reservation clear (M16). -/
def storeRun (ws : PState) (rl : Bool) (va : Nat) (fv : Nat) (base : Int) (n ts : Nat) : PState :=
  let ws1 := storeBytes ws base n ts fv
  { ws1 with
    wVwOld := max ws1.wVwOld ts
    wVRel := if rl then max ws1.wVRel ts else ws1.wVRel
    wVcap := max va ws1.wVcap }

/-- THE AMO's SINGLE-OP POST (M0 (i), (iv), (v)): the AMO is one memory operation at its write timestamp `ts`
(§rvwmo "An aligned AMO gives rise to a single memory operation that is both a load operation and a store
operation simultaneously"), so `vrOld ⊔= ts` (a later `fence r,·` covers it, §expl Example 2), the result register's
view `wLdv ⊔= ts`, and an acquire raises both new-floors to `ts` (rule 5). -/
def amoPost (ws : PState) (aq : Bool) (ts : Nat) : PState :=
  { ws with
    wVrOld := max ws.wVrOld ts
    wLdv := max ws.wLdv ts
    wVrNew := if aq then max ws.wVrNew ts else ws.wVrNew
    wVwNew := if aq then max ws.wVwNew ts else ws.wVwNew }

/-- THE CACHE-BLOCK OPERATION's post: the block's coherence floors take `ts` (it behaves as a store in the PPO rules:
rule 1 orders later stores to the block after it, and cmo.adoc:229–233 "a is an invalidate, clean, or flush, b is a
load, and a and b access overlapping memory addresses" orders later loads after it), `vwOld ⊔= ts` (it is "classified
as W … for the purposes of predecessor and successor sets in FENCE instructions", cmo.adoc:241–244), `vcap ⊔= va`.
No forward-bank entry (it writes no value). -/
def cmoPost (ws : PState) (va : Nat) (base : Int) (len ts : Nat) : PState :=
  let ws1 := cohRaise ws base len ts
  { ws1 with wVwOld := max ws1.wVwOld ts, wVcap := max va ws1.wVcap }

/-- The class a fulfil must find on its message (INERT bookkeeping, N-10). -/
def stClass (rl : Bool) : PClass := if rl then .rel else .plain

/-! ## 6. Fences and fetches -/

/-- FENCE pred,succ (PARM): `pr`/`pw` select `vrOld`/`vwOld`, `sr`/`sw` the floors they raise (rule 4).  No
reservation clear (M16).  FENCE.TSO is the union of its two halves (M6), applied by the emission as two labels. -/
def fencePost (ws : PState) (pr pw sr sw : Bool) : PState :=
  let v := max (if pr then ws.wVrOld else 0) (if pw then ws.wVwOld else 0)
  { ws with
    wVrNew := if sr then max ws.wVrNew v else ws.wVrNew
    wVwNew := if sw then max ws.wVwNew v else ws.wVwNew }

/-- THE FETCH ADMISSIBILITY of one byte ([OWN.P2]): the byte returns what some write (or the image) holds there
(PA-0: zifencei.adoc:70 "will see any previous data stores already visible", which presupposes fetched values are
values the location held), and no write to that byte lies in `(t, wIfl]` — the floor FENCE.I raised.  Nothing else:
a fetch may be STALE ("RISC-V does not guarantee that stores to instruction memory will be made visible to
instruction fetches on a RISC-V hart until that hart executes a FENCE.I instruction", zifencei.adoc:67–69), bytes
of one fetch need no common point, and a fetch moves no coherence or load view.  FAITHFUL under the reading of
`wIfl` given at `fenceIPost`. -/
def fetchByteOk (img : Image) (log : List PMsg) (ws : PState) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  memByte img log t a = some v ∧ ¬ writesIn log a t ws.wIfl

/-- The fetch's contribution to the current instruction's fetch view (PA-1f, zifencei.adoc:107–108): every source
timestamp, except an own already-fulfilled store (a po-earlier store of the hart), which contributes nothing — the
analogue of PA-1's own-store exemption (plan M14/M18).  The exemption is the WEAKER-or-FAITHFUL side of a reading
the text does not settle (fetch forwarding from the store buffer); PROGRESS-S1Mdef.md records it. -/
def fetchView (log : List PMsg) (i : Nat) (prom : GSet Nat) (base : Int) (tvs : List (Nat × BitVec 8)) : Nat :=
  bytesMax (fun _ t => if ownDone log i prom t then 0 else t) base tvs

/-- FENCE.I ([OWN.P2]).  zifencei.adoc:69–71: "A FENCE.I instruction ensures that a subsequent instruction fetch on
a RISC-V hart will see any previous data stores already visible to the same RISC-V hart."  zifencei.adoc:77–80: "A
FENCE.I instruction orders all explicit memory accesses and instruction fetches that precede the FENCE.I in program
order before all instruction fetches that follow the FENCE.I in program order."
Rendering: the fetch floor rises to `vrOld ⊔ vwOld ⊔ wIfr`.
* "already visible to the same hart" is read as PA-3's execution-level definition (plan M18, Table S §14): a
  po-earlier store of the hart, or a write gmo-before some memory operation of the hart that is po-before the fence
  (the multi-copy-atomic reading, mm-explanatory.adoc:189–195).  Every timestamp below `vwOld` is gmo-before (or
  is) a po-earlier own store; every timestamp below `vrOld` is gmo-before a po-earlier load (or below a view built
  from such timestamps).  So every write the floor excludes is co-before an already-visible store: the machine floor
  is at or below the reference floor (machine ⊇ reference).  `coh a ≤ vrOld ⊔ vwOld` on v2 (loads raise `coh` by
  at most their post-view or an own forwarded timestamp), so a per-byte term would add nothing.
* "orders … instruction fetches that precede the FENCE.I … before all instruction fetches that follow": an earlier
  fetch that returned a write `w` is ordered after `w`, so a later fetch may not return a write co-before `w`;
  `wIfr` (every earlier fetch's source timestamp) is that bound.
* Nothing is drained and nothing else is ordered: FENCE.I is not a data fence (EX-FENCEI-1, [OWN.143]), and
  "FENCE.I does not ensure that other RISC-V harts' instruction fetches will observe the local hart's stores"
  (zifencei.adoc:71–73) — the floor is the fencing hart's own.
Mark: FAITHFUL under the multi-copy-atomic reading of "visible" (as PA-3); quoted; formal form pending S0. -/
def fenceIPost (ws : PState) : PState :=
  { ws with wIfl := max ws.wIfl (max ws.wVrOld (max ws.wVwOld ws.wIfr)) }

/-! ## 7. Labels -/

/-- THE v2 LABEL ALPHABET.  A label carries the memory system's ANSWERS (per-byte timestamp and value); multi-byte
accesses are contiguous runs at `base`; `asrc`/`vsrc`/`srcs` are SYNTACTIC dependency sources (M19).
Changes from today's `Wlabel` (WeakPromise.lean:79–110): `LLoad` has no `lat` field (SR-31, [R6.1(a)]); the AMO
halves are their own labels `LAmoLd`/`LAmoSt` (M10 (1): they use `wRmw`, never `wRes`); `LExFail` (M16);
`LFenceI` ([OWN.P2]). -/
inductive PLabel where
  /-- No memory or view effect. -/
  | LSilent
  /-- A plain or acquire load (no `lat`, SR-31). -/
  | LLoad (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc)
  /-- A plain or release store. -/
  | LStore (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
  /-- A FUSED AMO, one label (for abstract-`pstep` litmus programs; Sail emits the split pair). -/
  | LRmw (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc)
  /-- The read half of a split AMO (M10). -/
  | LAmoLd (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc)
  /-- The write half of a split AMO (M10). -/
  | LAmoSt (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
  /-- FENCE pred,succ over {r, w} (the i/o bits are dropped by Sail at decode, SAIL-GAP-1). -/
  | LFence (pr pw sr sw : Bool)
  /-- FENCE.I ([OWN.P2]). -/
  | LFenceI
  /-- A device (MMIO / fabric) event: no view effect (M12, WEAKER; NA-7). -/
  | LDev (kind : Weak.IoKind) (base : Int) (vs : List (BitVec 8)) (asrc vsrc : List Dsrc)
  /-- A register write with its syntactic sources (PARM `step_assign`; M19: EVERY register write). -/
  | LRegW (rd : Nat) (srcs : List Dsrc)
  /-- A control dependency (PARM `Local.control`, rule 11). -/
  | LCtrl (srcs : List Dsrc)
  /-- The instruction boundary: resets the per-instruction banks. -/
  | LInstr
  /-- LR (load-reserved). -/
  | LExLoad (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc)
  /-- A SUCCESSFUL SC. -/
  | LExStore (rl : Bool) (base : Int) (data : List (BitVec 8)) (asrc vsrc : List Dsrc)
  /-- A retired SC that did not write (memory-level failure, or the end of any SC): clears the reservation (M16). -/
  | LExFail
  /-- An instruction fetch of the bytes `tvs` at `base` ([OWN.P2]). -/
  | LIFetch (base : Int) (tvs : List (Nat × BitVec 8))
  /-- A cache-block management operation on `[base, base + len)` ([OWN.P1], Zicbom). -/
  | LCmo (k : CmoKind) (base : Int) (len : Nat) (asrc : List Dsrc)

open PLabel

/-! ## 8. The memory half of a state step (the C-A arms) -/

section memstep

variable (img : Image) (log : List PMsg) (i : Nat)

/-- `memStep img log i prom ws l ots ws' prom'`: agent `i`, with promises `prom` and state `ws`, performs label `l`,
fulfilling timestamp `ots` (`some ts` for the five write arms, `none` otherwise).  One constructor per arm. -/
inductive memStep : GSet Nat → PState → PLabel → Option Nat → PState → GSet Nat → Prop
  /-- `LSilent`. -/
  | silent (prom : GSet Nat) (ws : PState) :
      memStep prom ws LSilent none ws prom
  /-- PLAIN/ACQUIRE LOAD: admissible at `ldPre` (rules 4, 5, 7, 9; PA-1f), single read point (M9). -/
  | load (prom : GSet Nat) (ws : PState) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
      (asrc : List Dsrc) :
      loadOk img log ws (ldPre ws aq (srcsView ws asrc)) base tvs →
      memStep prom ws (LLoad aq base tvs asrc) none (loadRun ws aq (srcsView ws asrc) base tvs) prom
  /-- PLAIN/RELEASE STORE: fulfils its promise `ts` (COH + EXT); forward view = address ⊔ data view (M2). -/
  | store (prom : GSet Nat) (ws : PState) (rl : Bool) (base : Int) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc) (ts : Nat) :
      ts ∈ prom →
      log[ts - 1]? = some ⟨base, data, some i, stClass rl⟩ →
      cohBelow ws base data.length ts →
      stPre ws rl (srcsView ws asrc) (srcsView ws vsrc) < ts →
      memStep prom ws (LStore rl base data asrc vsrc) (some ts)
        (storeRun ws rl (srcsView ws asrc) (max (srcsView ws asrc) (srcsView ws vsrc)) base data.length ts)
        (prom \ {ts})
  /-- FUSED AMO (M0): the read at `ldPre` with the address view (rule 9 on the single op), the atomicity window
  (`exclOk`), the write at the post-read state's `stPre`; post: exclusive forward view `ts` (M1), `amoPost`. -/
  | rmw (prom : GSet Nat) (ws : PState) (aq rl : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (ts : Nat) :
      tvs.length = data.length →
      ts ∈ prom →
      log[ts - 1]? = some ⟨base, data, some i, .excl⟩ →
      loadOk img log ws (ldPre ws aq (srcsView ws asrc)) base tvs →
      exclOk log i base (tvs.map Prod.fst) ts →
      cohBelow (loadRun ws aq (srcsView ws asrc) base tvs) base data.length ts →
      stPre (loadRun ws aq (srcsView ws asrc) base tvs) rl (srcsView ws asrc) (srcsView ws vsrc) < ts →
      memStep prom ws (LRmw aq rl base tvs data asrc vsrc) (some ts)
        (amoPost (storeRun (loadRun ws aq (srcsView ws asrc) base tvs) rl (srcsView ws asrc) ts base
          data.length ts) aq ts)
        (prom \ {ts})
  /-- SPLIT AMO, read half (M10): a load-like read; records the AMO slot (never `wRes`). -/
  | amoLd (prom : GSet Nat) (ws : PState) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
      (asrc : List Dsrc) :
      loadOk img log ws (ldPre ws aq (srcsView ws asrc)) base tvs →
      memStep prom ws (LAmoLd aq base tvs asrc) none
        { loadRun ws aq (srcsView ws asrc) base tvs with wRmw := some ⟨base, tvs.map Prod.fst, aq⟩ }
        prom
  /-- SPLIT AMO, write half (M10 (2), (3)): needs the slot at the same base and width, the atomicity window, COH
  and EXT; post as the fused AMO with the READ half's aq; the slot is consumed. -/
  | amoSt (prom : GSet Nat) (ws : PState) (rl : Bool) (base : Int) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc) (ts : Nat) (R : PRmw) :
      ws.wRmw = some R →
      R.rmBase = base →
      R.rmTs.length = data.length →
      ts ∈ prom →
      log[ts - 1]? = some ⟨base, data, some i, .excl⟩ →
      exclOk log i base R.rmTs ts →
      cohBelow ws base data.length ts →
      stPre ws rl (srcsView ws asrc) (srcsView ws vsrc) < ts →
      memStep prom ws (LAmoSt rl base data asrc vsrc) (some ts)
        { amoPost (storeRun ws rl (srcsView ws asrc) ts base data.length ts) R.rmAq ts with wRmw := none }
        (prom \ {ts})
  /-- FENCE. -/
  | fence (prom : GSet Nat) (ws : PState) (pr pw sr sw : Bool) :
      memStep prom ws (LFence pr pw sr sw) none (fencePost ws pr pw sr sw) prom
  /-- FENCE.I ([OWN.P2]). -/
  | fenceI (prom : GSet Nat) (ws : PState) :
      memStep prom ws LFenceI none (fenceIPost ws) prom
  /-- DEVICE EVENT: no view effect (M12, WEAKER). -/
  | dev (prom : GSet Nat) (ws : PState) (kd : Weak.IoKind) (ba : Int) (bs : List (BitVec 8))
      (sa sv : List Dsrc) :
      memStep prom ws (LDev kd ba bs sa sv) none ws prom
  /-- REGISTER WRITE: an assignment of the sources' view (PARM `step_assign`). -/
  | regW (prom : GSet Nat) (ws : PState) (rd : Nat) (srcs : List Dsrc) :
      memStep prom ws (LRegW rd srcs) none { ws with wRegv := insert ws.wRegv rd (srcsView ws srcs) } prom
  /-- CONTROL: `vcap ⊔= view(srcs)` (rule 11). -/
  | ctrl (prom : GSet Nat) (ws : PState) (srcs : List Dsrc) :
      memStep prom ws (LCtrl srcs) none { ws with wVcap := max (srcsView ws srcs) ws.wVcap } prom
  /-- INSTRUCTION BOUNDARY: resets `wLdv`, the AMO slot and the fetch view; NOT the reservation (M16 [R3.s5]). -/
  | instr (prom : GSet Nat) (ws : PState) :
      memStep prom ws LInstr none { ws with wLdv := 0, wRmw := none, wIfv := 0 } prom
  /-- LR (M3: the address view is in the pre-view; M16: the reservation records the LR's own bytes and its
  post-view, M5). -/
  | lr (prom : GSet Nat) (ws : PState) (aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
      (asrc : List Dsrc) :
      loadOk img log ws (ldPre ws aq (srcsView ws asrc)) base tvs →
      memStep prom ws (LExLoad aq base tvs asrc) none
        { loadRun ws aq (srcsView ws asrc) base tvs with
          wRes := some ⟨base, tvs.map Prod.fst, readView ws aq (srcsView ws asrc) base tvs⟩ }
        prom
  /-- SUCCESSFUL SC (M16): needs a reservation; the SC's base and width are FREE (§rvwmo: "The Atomicity Axiom
  theoretically supports LR/SC pairs of different widths and to mismatched addresses"; the reservation set is the
  model's free choice, zalrsc.adoc "an arbitrarily large reservation set"); atomicity on the LR's bytes
  (`exclOk`); rule 8 through the reservation's view (M5); COH and EXT on the SC's bytes.  Post: exclusive forward
  view `ts` (M1), the success register's view `wLdv ⊔= ts` (M4), the reservation cleared ("Regardless of success or
  failure, executing an SC.W instruction invalidates any reservation held by this hart", zalrsc.adoc:23–24).
  WEAKER, optional refinement not taken (M16): another hart's store to SC bytes outside the LR's bytes is not
  checked. -/
  | sc (prom : GSet Nat) (ws : PState) (rl : Bool) (base : Int) (data : List (BitVec 8))
      (asrc vsrc : List Dsrc) (ts : Nat) (R : PResv) :
      ws.wRes = some R →
      ts ∈ prom →
      log[ts - 1]? = some ⟨base, data, some i, .excl⟩ →
      exclOk log i R.rvBase R.rvTs ts →
      cohBelow ws base data.length ts →
      max (stPre ws rl (srcsView ws asrc) (srcsView ws vsrc)) R.rvView < ts →
      memStep prom ws (LExStore rl base data asrc vsrc) (some ts)
        { storeRun ws rl (srcsView ws asrc) ts base data.length ts with
          wLdv := max (storeRun ws rl (srcsView ws asrc) ts base data.length ts).wLdv ts
          wRes := none }
        (prom \ {ts})
  /-- SC FAILURE / END OF SC (M16 (c1), (c2)): clears the reservation, nothing else. -/
  | scFail (prom : GSet Nat) (ws : PState) :
      memStep prom ws LExFail none { ws with wRes := none } prom
  /-- INSTRUCTION FETCH ([OWN.P2]): every byte admissible above the fetch floor; post: `wIfr` takes every source,
  `wIfv` the non-own-done ones (PA-1f). -/
  | fetch (prom : GSet Nat) (ws : PState) (base : Int) (tvs : List (Nat × BitVec 8)) :
      bytesAll (fetchByteOk img log ws) base tvs →
      memStep prom ws (LIFetch base tvs) none
        { ws with
          wIfr := max ws.wIfr (bytesMax (fun _ t => t) base tvs)
          wIfv := max ws.wIfv (fetchView log i prom base tvs) }
        prom

  /-- CACHE-BLOCK OPERATION (Zicbom; [OWN.P1]): fulfils its (byte-free) message like a plain store (COH on the
  block, EXT at the plain store pre-view: it behaves as a store in the PPO rules, cmo.adoc:228). -/
  | cmo (prom : GSet Nat) (ws : PState) (k : CmoKind) (base : Int) (len : Nat) (asrc : List Dsrc) (ts : Nat) :
      ts ∈ prom →
      log[ts - 1]? = some ⟨base, [], some i, .cmo k len⟩ →
      cohBelow ws base len ts →
      stPre ws false (srcsView ws asrc) 0 < ts →
      memStep prom ws (LCmo k base len asrc) (some ts) (cmoPost ws (srcsView ws asrc) base len ts) (prom \ {ts})

end memstep

/-! ## 9. Configurations, events, runs -/

/-- An agent: its program state, its `PState`, its promise set (PARM `Local.promises`). -/
structure PAgent (P : Type) where
  paSt : P
  paWs : PState
  paProm : GSet Nat

/-- A configuration: the image, the log, the device fabric, the agents (the hart domain is the list index,
[R7.s3]: agent `i` runs `ps[i]`). -/
structure PCfg (P D : Type) where
  pcImg : Image
  pcLog : List PMsg
  pcDev : D
  pcAgs : List (PAgent P)

/-- A machine EVENT: a promise of message `m` by agent `i`, or a state step of agent `i` with its label and its
fulfil timestamp.  A run's trace (plan §0 [R4.5]) is its event list; `run.trace h` keeps `h`'s state events. -/
inductive PEvt where
  | prom (i : Nat) (m : PMsg)
  | st (i : Nat) (l : PLabel) (ts : Option Nat)
  deriving Inhabited

section machine

variable {P D : Type} (pstep : P → D → PLabel → P → D → Prop)

/-- ONE MACHINE STEP.  `promise` is PARM's `promise_step` (unconditional: the machine is uncertified, M8); the
message's author is the promising agent and the message writes at least one byte (or is a cache-block operation
on a non-empty block).  `state` composes the program half `pstep`
(which may read and move the fabric) with the memory half `memStep`. -/
inductive pmStep : PCfg P D → PEvt → PCfg P D → Prop
  | promise (cfg : PCfg P D) (i : Nat) (ag : PAgent P) (m : PMsg) :
      cfg.pcAgs[i]? = some ag →
      (m.data ≠ [] ∨ ∃ k len, m.cls = .cmo k len ∧ 0 < len) →
      m.tid = some i →
      pmStep cfg (.prom i m)
        ⟨cfg.pcImg, cfg.pcLog ++ [m], cfg.pcDev,
         cfg.pcAgs.set i ⟨ag.paSt, ag.paWs, {cfg.pcLog.length + 1} ∪ ag.paProm⟩⟩
  | state (cfg : PCfg P D) (i : Nat) (ag : PAgent P) (l : PLabel) (ots : Option Nat) (st' : P) (d' : D)
      (ws' : PState) (prom' : GSet Nat) :
      cfg.pcAgs[i]? = some ag →
      pstep ag.paSt cfg.pcDev l st' d' →
      memStep cfg.pcImg cfg.pcLog i ag.paProm ag.paWs l ots ws' prom' →
      pmStep cfg (.st i l ots) ⟨cfg.pcImg, cfg.pcLog, d', cfg.pcAgs.set i ⟨st', ws', prom'⟩⟩

/-- Runs: the reflexive-transitive closure, with the event list (oldest first). -/
inductive pmSteps : PCfg P D → List PEvt → PCfg P D → Prop
  | refl (cfg : PCfg P D) : pmSteps cfg [] cfg
  | step (c0 c1 c2 : PCfg P D) (e : PEvt) (es : List PEvt) :
      pmStep pstep c0 e c1 → pmSteps c1 es c2 → pmSteps c0 (e :: es) c2

/-- The initial configuration: every agent at `psInit` with no promises. -/
def pmInit (img : Image) (d0 : D) (ps : List P) : PCfg P D :=
  ⟨img, [], d0, ps.map (fun p => ⟨p, psInit, ∅⟩)⟩

/-- All promises discharged (PARM `Machine.no_promise`). -/
def noPromises (cfg : PCfg P D) : Prop :=
  ∀ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag → ag.paProm = ∅

/-- A VALID RUN (plan §0 `PF.validRun`): a finite run from the initial configuration that ends with no outstanding
promises; its final memory `M` is the final log. -/
def validRun (img : Image) (d0 : D) (ps : List P) (evs : List PEvt) (cfg : PCfg P D) : Prop :=
  pmSteps pstep (pmInit img d0 ps) evs cfg ∧ noPromises cfg

/-- A behaviour (the final configuration of a valid run). -/
def pmBehavior (img : Image) (d0 : D) (ps : List P) (cfg : PCfg P D) : Prop :=
  ∃ evs, validRun pstep img d0 ps evs cfg

end machine

/-- The trace of agent `h`: its state events, label and fulfil timestamp, in order (plan §0 `run.trace h`). -/
def traceOf (h : Nat) : List PEvt → List (PLabel × Option Nat)
  | [] => []
  | .prom _ _ :: es => traceOf h es
  | .st i l ots :: es => if i = h then (l, ots) :: traceOf h es else traceOf h es

/-- The timestamps agent `h` fulfilled, in order (plan §0 `run.fulfils h`). -/
def fulfilsOf (h : Nat) (es : List PEvt) : List Nat :=
  (traceOf h es).filterMap (fun e => e.2)

/-- The read answers a label carries (load-like entries: `LLoad`, `LExLoad`, `LRmw`, `LAmoLd`; and `LIFetch`),
with their base. -/
def labelReads : PLabel → Option (Int × List (Nat × BitVec 8))
  | LLoad _ base tvs _ => some (base, tvs)
  | LExLoad _ base tvs _ => some (base, tvs)
  | LRmw _ _ base tvs _ _ _ => some (base, tvs)
  | LAmoLd _ base tvs _ => some (base, tvs)
  | LIFetch base tvs => some (base, tvs)
  | _ => none

/-- The write a label performs (`LStore`, `LExStore`, `LRmw`, `LAmoSt`; `LCmo`, with no bytes), with its base. -/
def labelWrite : PLabel → Option (Int × List (BitVec 8))
  | LStore _ base data _ _ => some (base, data)
  | LExStore _ base data _ _ => some (base, data)
  | LRmw _ _ base _ data _ _ => some (base, data)
  | LAmoSt _ base data _ _ => some (base, data)
  | LCmo _ base _ _ => some (base, [])
  | _ => none

/-- TRACE WELL-FORMEDNESS against the final memory `M` (plan §0 (v); [R7.s4]: it covers the LR's (`LExLoad`) read
bytes as well as every other load-like entry and fetches): every answered byte is the byte `M` (or the image)
holds at its timestamp; every write entry has a fulfil timestamp whose message is `h`'s, with the label's base and
data; a non-write entry has none. -/
def traceWf (img : Image) (M : List PMsg) (h : Nat) (tr : List (PLabel × Option Nat)) : Prop :=
  ∀ e ∈ tr,
    (∀ base tvs, labelReads e.1 = some (base, tvs) →
      bytesAll (fun a t v => memByte img M t a = some v) base tvs) ∧
    (match labelWrite e.1, e.2 with
     | some (base, data), some ts => ∃ m, M[ts - 1]? = some m ∧ m.pa = base ∧ m.data = data ∧ m.tid = some h
     | none, none => True
     | _, _ => False)

/-! ## 10. Well-formedness (the bounds `cfgWf` keeps, [R7.s1]) -/

/-- Every timestamp in a list is at most `n`. -/
def tsBounded (l : List Nat) (n : Nat) : Prop := ∀ t ∈ l, t ≤ n

/-- Every view, bank, reservation and slot timestamp of `ws` is at most `n` (the log length). -/
def psBounded (ws : PState) (n : Nat) : Prop :=
  (∀ a, coh ws a ≤ n) ∧ ws.wVrOld ≤ n ∧ ws.wVwOld ≤ n ∧ ws.wVrNew ≤ n ∧ ws.wVwNew ≤ n ∧ ws.wVRel ≤ n ∧
  (∀ a tf vf, get? ws.wFwd a = some (tf, vf) → tf ≤ n ∧ vf ≤ n) ∧ (∀ r, regv ws r ≤ n) ∧
  ws.wVcap ≤ n ∧ ws.wLdv ≤ n ∧
  (∀ R, ws.wRes = some R → tsBounded R.rvTs n ∧ R.rvView ≤ n) ∧
  (∀ R, ws.wRmw = some R → tsBounded R.rmTs n) ∧
  ws.wIfl ≤ n ∧ ws.wIfr ≤ n ∧ ws.wIfv ≤ n

/-- Every promise of agent `i` is a real message of `i`. -/
def promWf (log : List PMsg) (i : Nat) (prom : GSet Nat) : Prop :=
  ∀ ts, ts ∈ prom → 0 < ts ∧ ts ≤ log.length ∧ ∃ m, log[ts - 1]? = some m ∧ m.tid = some i

/-- THE MACHINE INVARIANT (S1M-proof derives it from `pmInit`, plan [R2.s10]). -/
def cfgWf {P D : Type} (cfg : PCfg P D) : Prop :=
  ∀ (i : Nat) (ag : PAgent P), cfg.pcAgs[i]? = some ag →
    psBounded ag.paWs cfg.pcLog.length ∧ promWf cfg.pcLog i ag.paProm

end Weak.Prom
