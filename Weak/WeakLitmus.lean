/-
Weak: **executable litmus programs over the M0 view machine**.

Rocq: `iris/WeakLitmus.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, verbatim in substance: a tiny hart-program language (NOT
Sail) on top of `WeakMem`'s promise-free view machine, plus the litmus suite
the design doc makes a standing obligation (`claude-notes/design/weak-memory.md`,
"Validation"): SB, MP with and without fences, MP with an acquire load, CoRR,
LB, IRIW.  Verdicts are stated against riscv.cat/herd expectations, and the
two places where this machine is deliberately STRONGER than RVWMO are called
out in comments as gap witnesses (see `lbForbidden` and
`mpReaderFenceOnlyForbidden`).  Like `WeakMem` this file imports only the
stdpp shims.

**Deviations from Rocq.**

1. NAMES: as `Weak/WeakMem.lean` deviation 1.  Rocq → Lean map: types
   `instr` ↦ `Instr`, `hart` ↦ `Hart` (fields `h_prog`/`h_regs`/`h_ws` ↦
   `hProg`/`hRegs`/`hWs`, constructor `Hart p r w` ↦ `⟨p, r, w⟩`), `config` ↦
   `Config` (`c_img`/`c_log`/`c_harts` ↦ `cImg`/`cLog`/`cHarts`, `Cfg` ↦
   `⟨img, log, harts⟩`); constructors `ILoad`/`IStore`/`IFence`/`IAmoSwapAq`
   keep their spelling.  Lemmas: lowerCamelCase (`b0_ne_b1` ↦ `b0NeB1`,
   `img0_x` ↦ `img0X`, `msg_byte_single` ↦ `msgByteSingle`, `log_byte_1` ↦
   `logByte1`, `amo_latest_unique` ↦ `amoLatestUnique`, `step_load` ↦
   `stepLoad`, `inv_reach` ↦ `invReach`, `sb_00_reachable` ↦ `sb00Reachable`,
   `mp_read_y_1` ↦ `mpReadY1`, `mpf_W` ↦ `mpfW`, `mpf_R_app` ↦ `mpfRApp`,
   `mb_MX_x` ↦ `mbMXX`, `mb_CX1` ↦ `mbCX1`, `LX_ne_LY` ↦ `lXNeLY`,
   `lb_H0` ↦ `lbH0`, `iriw_R` ↦ `iriwR`, `fwd_bank_after_store` ↦
   `fwdBankAfterStore`, ...).  `Notation reach := rtc lstep` is the
   abbreviation `reach`.  The Rocq `Local Notation`s (`ax`, `ay`, `rg1`,
   `rg2`, the fence spellings, the litmus programs `MPF_W0` …, the messages
   `MX` …, `FWD_WS`) are `local notation`s with the same spellings.
2. VOCABULARY: as `WeakMem` deviation 2; `gmap nat (bv 8)` ↦
   `GMapF Nat (BitVec 8)` (`regs !! r` ↦ `get? regs r`, `<[r := v]> regs` ↦
   `insert regs r v`), `<[i := h]> harts` ↦ `harts.set i h`,
   `Z_to_bv 8 n` ↦ `n#8`, `m ∈ log` ↦ list membership.
3. CLOSED CHECKS.  The Rocq `vm_compute` side conditions (`solve_is_Some`,
   `solve_nw`, the concrete `log_byte` values, the `writes_in_compute` /
   `not_writes_in_compute` reflections, the `fwd_selfread_*` views) are
   `decide` on the same closed Boolean checkers (`writesInb`, `readableb` via
   `readablebSpec`, `Option` equality); every one is a few-message log and
   checks in well under a second, so no restructuring was needed.  The two
   Ltacs `solve_is_Some` / `solve_nw` are therefore not introduced.
4. `msg_byte_single`'s `if bool_decide (a' = a)` is `if a' = a` (the same
   decision).
5. The invariant-preservation proofs (`mpfStep` …) case-split the acting
   hart by matching on its index and destructure the step's `match` directly;
   the case structure and every appeal to a `WeakMem` lemma follow Rocq.

**Not ported:** nothing (the two Ltacs of deviation 3 are tactics, not
declarations).

**Statements checked** (by hand, against Rocq): all of them.
-/
import Weak.WeakMem

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Iris.Std.PartialMap

/-! ## Bytes, addresses, registers -/

def b0 : BitVec 8 := 0#8
def b1 : BitVec 8 := 1#8
def b2 : BitVec 8 := 2#8

theorem b0NeB1 : b0 ≠ b1 := by decide
theorem b0NeB2 : b0 ≠ b2 := by decide
theorem b1NeB2 : b1 ≠ b2 := by decide

/-- The two litmus addresses and the litmus registers. -/
local notation "ax" => (0 : Int)
local notation "ay" => (8 : Int)
local notation "rg1" => (1 : Nat)
local notation "rg2" => (2 : Nat)

/-- The era-initial image: both litmus bytes read as 0 at timestamp 0 (the
alternative — seeding explicit init messages — would shift every timestamp). -/
def img0m : GMapF Int (BitVec 8) := insert {[ay := b0]} ax b0

/-- `Image` is a partial FUNCTION on `Int`; the litmus image is still built as a
two-entry map. -/
def img0 : Image := fun a => get? img0m a

theorem img0X : img0 ax = some b0 := by
  show get? (insert _ ax b0) ax = some b0
  exact lookupInsert

theorem img0Y : img0 ay = some b0 := by
  show get? (insert {[ay := b0]} ax b0) ay = some b0
  rw [lookupInsertNe (by decide)]
  exact lookupSingleton

/-! ## Single-byte messages -/

theorem WeakLitmus.msgByteSingle (a : Int) (v : BitVec 8) (tid : Option Nat) (k : WmClass) (a' : Int) :
    msgByte ⟨a, [v], tid, k⟩ a' = if a' = a then some v else none := by
  unfold msgByte
  by_cases h : a' = a
  · subst h; simp
  · simp only [h, if_false]
    split
    · obtain ⟨n, hn⟩ : ∃ n, (a' - a).toNat = n + 1 := ⟨(a' - a).toNat - 1, by omega⟩
      simp only [hn, List.getElem?_cons_succ, List.getElem?_nil]
    · rfl

/-- Reading a concrete log at a concrete timestamp. -/
theorem logByte1 (img : Image) (m : Wmsg) (rest : List Wmsg) (a : Int) :
    logByte img (m :: rest) 1 a = msgByte m a := rfl

theorem logByte2 (img : Image) (m0 m1 : Wmsg) (rest : List Wmsg) (a : Int) :
    logByte img (m0 :: m1 :: rest) 2 a = msgByte m1 a := rfl

/-! ## The hart-program language -/

inductive Instr where
  | ILoad (reg : Nat) (a : Int) (aq : Bool)
  | IStore (a : Int) (v : BitVec 8)
  | IFence (pr pw sr sw : Bool)
  /-- `amoswap.aq`: an acquire load of the per-byte globally-LATEST value plus a
  store, atomically in one step. -/
  | IAmoSwapAq (reg : Nat) (a : Int) (v : BitVec 8)
  deriving DecidableEq, Inhabited

open Instr

/-- A hart: the remaining program IS the pc. -/
structure Hart where
  hProg : List Instr
  hRegs : GMapF Nat (BitVec 8)
  hWs : Wstate

structure Config where
  cImg : Image
  cLog : List Wmsg
  cHarts : List Hart

/-- One small step: pick a hart, execute its next instruction.  Loads
∃-quantify an admissible timestamp (`readable`); stores append at the log's
fresh top; the AMO does both in one step under the atomicity constraint.

THE MESSAGE CLASS in the litmus miniature (M6, inert): the AMO stamps `WCexcl`;
a plain `IStore` stamps `WCplain` UNCONDITIONALLY (the real machine's
`WeakInterp.wm_class_of` would raise it to `WCrel` under `wRelp`; that arm is
deliberately not modelled — every litmus invariant here characterizes a run by
(remaining program, log) alone, and the class is inert). -/
def lstep (c c' : Config) : Prop :=
  ∃ (i : Nat) (h : Hart),
    c.cHarts[i]? = some h ∧ c'.cImg = c.cImg ∧
    match h.hProg with
    | [] => False
    | ILoad r a aq :: rest => ∃ (t : Nat) (v : BitVec 8),
        logByte c.cImg c.cLog t a = some v ∧
        readable c.cImg c.cLog h.hWs (loadVpre h.hWs aq) a t ∧
        c'.cLog = c.cLog ∧
        c'.cHarts = c.cHarts.set i ⟨rest, insert h.hRegs r v, loadPost h.hWs aq a t⟩
    | IStore a v :: rest =>
        c'.cLog = c.cLog ++ [⟨a, [v], some i, .WCplain⟩] ∧
        c'.cHarts = c.cHarts.set i
          ⟨rest, h.hRegs, storePost h.hWs false a (c.cLog.length + 1)⟩
    | IFence pr pw sr sw :: rest =>
        c'.cLog = c.cLog ∧
        c'.cHarts = c.cHarts.set i ⟨rest, h.hRegs, fencePost h.hWs pr pw sr sw⟩
    | IAmoSwapAq r a v :: rest => ∃ (t : Nat) (vv : BitVec 8),
        logByte c.cImg c.cLog t a = some vv ∧
        -- atomicity: the read half takes the globally-latest write to `a`
        ¬ writesIn c.cLog a t c.cLog.length ∧
        readable c.cImg c.cLog h.hWs (loadVpre h.hWs true) a t ∧
        c'.cLog = c.cLog ++ [⟨a, [v], some i, .WCexcl⟩] ∧
        c'.cHarts = c.cHarts.set i
          ⟨rest, insert h.hRegs r vv,
           storePost (loadPost h.hWs true a t) false a (c.cLog.length + 1)⟩

/-- The AMO's atomicity constraint really does pin the read. -/
theorem amoLatestUnique (img : Image) (log : List Wmsg) (a : Int) (t t' : Nat) :
    (logByte img log t a).isSome → ¬ writesIn log a t log.length →
    (logByte img log t' a).isSome → ¬ writesIn log a t' log.length →
    t = t' := fun ht hnt ht' hnt' =>
  latestUnique img log a t t' ⟨ht, hnt⟩ ⟨ht', hnt'⟩

/-! ## Step constructors (used to exhibit interleavings) -/

theorem stepLoad (c : Config) (i r : Nat) (a : Int) (aq : Bool) (rest : List Instr)
    (regs : GMapF Nat (BitVec 8)) (ws : Wstate) (t : Nat) (v : BitVec 8) :
    c.cHarts[i]? = some ⟨ILoad r a aq :: rest, regs, ws⟩ →
    logByte c.cImg c.cLog t a = some v →
    readable c.cImg c.cLog ws (loadVpre ws aq) a t →
    lstep c ⟨c.cImg, c.cLog, c.cHarts.set i ⟨rest, insert regs r v, loadPost ws aq a t⟩⟩ :=
  fun hlk hv hr => ⟨i, _, hlk, rfl, t, v, hv, hr, rfl, rfl⟩

theorem stepStore (c : Config) (i : Nat) (a : Int) (v : BitVec 8) (rest : List Instr)
    (regs : GMapF Nat (BitVec 8)) (ws : Wstate) :
    c.cHarts[i]? = some ⟨IStore a v :: rest, regs, ws⟩ →
    lstep c ⟨c.cImg, c.cLog ++ [⟨a, [v], some i, .WCplain⟩],
      c.cHarts.set i ⟨rest, regs, storePost ws false a (c.cLog.length + 1)⟩⟩ :=
  fun hlk => ⟨i, _, hlk, rfl, rfl, rfl⟩

theorem stepFence (c : Config) (i : Nat) (pr pw sr sw : Bool) (rest : List Instr)
    (regs : GMapF Nat (BitVec 8)) (ws : Wstate) :
    c.cHarts[i]? = some ⟨IFence pr pw sr sw :: rest, regs, ws⟩ →
    lstep c ⟨c.cImg, c.cLog, c.cHarts.set i ⟨rest, regs, fencePost ws pr pw sr sw⟩⟩ :=
  fun hlk => ⟨i, _, hlk, rfl, rfl, rfl⟩

/-- Reachability (Rocq `Notation reach := (rtc lstep)`). -/
abbrev reach : Config → Config → Prop := rtc lstep

theorem invReach (I : Config → Prop) (c0 c : Config) :
    I c0 → (∀ a b, I a → lstep a b → I b) → reach c0 c → I c := by
  intro h0 hpres h
  exact rtc_ind_r (R := lstep) I c0 h0 (fun y z _ hyz ihy => hpres y z ihy hyz) c h

/-! ## Litmus programs -/

/-- `fence rw,w` — the release-side writer fence. -/
local notation "FENCE_RW_W" => Instr.IFence true true false true
/-- `fence r,rw` — the acquire-side reader fence. -/
local notation "FENCE_R_RW" => Instr.IFence true false true true
/-- `fence rw,rw`. -/
local notation "FENCE_RW_RW" => Instr.IFence true true true true

/-! ### SB — store buffering.  Both loads reading 0 is ALLOWED (herd: allowed) -/

def sbProg0 : List Instr := [IStore ax b1, ILoad rg1 ay false]
def sbProg1 : List Instr := [IStore ay b1, ILoad rg2 ax false]
def sbC0 : Config := ⟨img0, [], [⟨sbProg0, ∅, wsInit⟩, ⟨sbProg1, ∅, wsInit⟩]⟩

theorem sb00Reachable :
    ∃ c, reach sbC0 c ∧
      (∃ regs ws, c.cHarts[0]? = some ⟨[], regs, ws⟩ ∧ get? regs rg1 = some b0) ∧
      (∃ regs ws, c.cHarts[1]? = some ⟨[], regs, ws⟩ ∧ get? regs rg2 = some b0) := by
  refine ⟨?c, ?run, ?rest⟩
  case run =>
    refine rtc_l (stepStore _ 0 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepStore _ 1 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepLoad _ 0 rg1 ay false _ _ _ 0 b0 rfl img0Y
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    refine rtc_l (stepLoad _ 1 rg2 ax false _ _ _ 0 b0 rfl img0X
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    exact rtc_refl _
  case rest => exact ⟨⟨_, _, rfl, lookupInsert⟩, ⟨_, _, rfl, lookupInsert⟩⟩

/-! ### MP with no fences — the weak outcome is ALLOWED (herd: allowed) -/

def mpWNofence : List Instr := [IStore ax b1, IStore ay b1]
def mpRNofence : List Instr := [ILoad rg1 ay false, ILoad rg2 ax false]
def mpNofenceC0 : Config := ⟨img0, [], [⟨mpWNofence, ∅, wsInit⟩, ⟨mpRNofence, ∅, wsInit⟩]⟩

theorem mpNofenceWeakReachable :
    ∃ c, reach mpNofenceC0 c ∧
      ∃ regs ws, c.cHarts[1]? = some ⟨[], regs, ws⟩ ∧
        get? regs rg1 = some b1 ∧ get? regs rg2 = some b0 := by
  refine ⟨?c, ?run, ?rest⟩
  case run =>
    refine rtc_l (stepStore _ 0 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepStore _ 0 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepLoad _ 1 rg1 ay false _ _ _ 2 b1 rfl
      ((logByte2 _ _ _ _ _).trans (by rw [WeakLitmus.msgByteSingle]; decide))
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    refine rtc_l (stepLoad _ 1 rg2 ax false _ _ _ 0 b0 rfl img0X
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    exact rtc_refl _
  case rest =>
    refine ⟨_, _, rfl, ?_, lookupInsert⟩
    rw [lookupInsertNe (by decide)]; exact lookupInsert

/-! ### MP with a WRITER fence only — still ALLOWED (herd: allowed).

In this promise-free machine the writer fence is inert (stores are never
early), so it cannot forbid anything on its own; RVWMO agrees. -/

def mpWFenced : List Instr := [IStore ax b1, FENCE_RW_W, IStore ay b1]
def mpWfenceC0 : Config := ⟨img0, [], [⟨mpWFenced, ∅, wsInit⟩, ⟨mpRNofence, ∅, wsInit⟩]⟩

theorem mpWfenceWeakReachable :
    ∃ c, reach mpWfenceC0 c ∧
      ∃ regs ws, c.cHarts[1]? = some ⟨[], regs, ws⟩ ∧
        get? regs rg1 = some b1 ∧ get? regs rg2 = some b0 := by
  refine ⟨?c, ?run, ?rest⟩
  case run =>
    refine rtc_l (stepStore _ 0 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepFence _ 0 _ _ _ _ _ _ _ rfl) ?_
    refine rtc_l (stepStore _ 0 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepLoad _ 1 rg1 ay false _ _ _ 2 b1 rfl
      ((logByte2 _ _ _ _ _).trans (by rw [WeakLitmus.msgByteSingle]; decide))
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    refine rtc_l (stepLoad _ 1 rg2 ax false _ _ _ 0 b0 rfl img0X
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    exact rtc_refl _
  case rest =>
    refine ⟨_, _, rfl, ?_, lookupInsert⟩
    rw [lookupInsertNe (by decide)]; exact lookupInsert

/-! ### SB with both harts fenced — the ONE-SIDED outcome is reachable.

(0,0) is forbidden with both fences; (0,1) is not, and the machine really does
produce it: the hart whose store lost the race to the log is forced to see the
winner's store. -/

def sbfProg0 : List Instr := [IStore ax b1, FENCE_RW_RW, ILoad rg1 ay false]
def sbfProg1 : List Instr := [IStore ay b1, FENCE_RW_RW, ILoad rg2 ax false]
def sbfC0 : Config := ⟨img0, [], [⟨sbfProg0, ∅, wsInit⟩, ⟨sbfProg1, ∅, wsInit⟩]⟩

theorem sbFenced01Reachable :
    ∃ c, reach sbfC0 c ∧
      (∃ regs ws, c.cHarts[0]? = some ⟨[], regs, ws⟩ ∧ get? regs rg1 = some b0) ∧
      (∃ regs ws, c.cHarts[1]? = some ⟨[], regs, ws⟩ ∧ get? regs rg2 = some b1) := by
  refine ⟨?c, ?run, ?rest⟩
  case run =>
    refine rtc_l (stepStore _ 0 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepFence _ 0 _ _ _ _ _ _ _ rfl) ?_
    refine rtc_l (stepLoad _ 0 rg1 ay false _ _ _ 0 b0 rfl img0Y
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    refine rtc_l (stepStore _ 1 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepFence _ 1 _ _ _ _ _ _ _ rfl) ?_
    refine rtc_l (stepLoad _ 1 rg2 ax false _ _ _ 1 b1 rfl
      ((logByte1 _ _ _ _).trans (by rw [WeakLitmus.msgByteSingle]; decide))
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    exact rtc_refl _
  case rest => exact ⟨⟨_, _, rfl, lookupInsert⟩, ⟨_, _, rfl, lookupInsert⟩⟩

/-! ## FORBIDDEN outcomes

These are the real work: unreachability over ALL interleavings.  Each proof is
an induction over `reach` with a hand-built global invariant.  Two structural
facts do the heavy lifting and hold BY CONSTRUCTION of `lstep`: the log is
append-only (so `writesIn` is monotone), and each hart's stores enter the log
in program order. -/

/-- Reading a concrete log at an arbitrary timestamp. -/
theorem logByteCases0 (img : Image) (a : Int) (t : Nat) (v : BitVec 8) :
    logByte img [] t a = some v → t = 0 ∧ img a = some v := by
  cases t with
  | zero => intro h; exact ⟨rfl, h⟩
  | succ i => intro h; simp [logByte] at h

theorem logByteCases1 (img : Image) (m : Wmsg) (a : Int) (t : Nat) (v : BitVec 8) :
    logByte img [m] t a = some v →
    (t = 0 ∧ img a = some v) ∨ (t = 1 ∧ msgByte m a = some v) := by
  match t with
  | 0 => intro h; exact .inl ⟨rfl, h⟩
  | 1 => intro h; exact .inr ⟨rfl, h⟩
  | i + 2 => intro h; simp [logByte] at h

theorem logByteCases2 (img : Image) (m0 m1 : Wmsg) (a : Int) (t : Nat) (v : BitVec 8) :
    logByte img [m0, m1] t a = some v →
    (t = 0 ∧ img a = some v) ∨ (t = 1 ∧ msgByte m0 a = some v) ∨
      (t = 2 ∧ msgByte m1 a = some v) := by
  match t with
  | 0 => intro h; exact .inl ⟨rfl, h⟩
  | 1 => intro h; exact .inr (.inl ⟨rfl, h⟩)
  | 2 => intro h; exact .inr (.inr ⟨rfl, h⟩)
  | i + 3 => intro h; simp [logByte] at h

theorem img0XNb1 : img0 ax ≠ some b1 := by
  rw [img0X]; intro h; exact b0NeB1 (Option.some.inj h)

theorem img0YNb1 : img0 ay ≠ some b1 := by
  rw [img0Y]; intro h; exact b0NeB1 (Option.some.inj h)

/-! ### The MP family: shared message facts and read analyses -/

local notation "MX" => Wmsg.mk ax [b1] (some 0) WmClass.WCplain
local notation "MY" => Wmsg.mk ay [b1] (some 0) WmClass.WCplain

theorem mbMXX : msgByte MX ax = some b1 := by rw [WeakLitmus.msgByteSingle]; decide
theorem mbMXY : msgByte MX ay = none := by rw [WeakLitmus.msgByteSingle]; decide
theorem mbMYX : msgByte MY ax = none := by rw [WeakLitmus.msgByteSingle]; decide
theorem mbMYY : msgByte MY ay = some b1 := by rw [WeakLitmus.msgByteSingle]; decide

/-- The only logs any MP-family run can produce: the writer stores x then y. -/
def mpLogs (log : List Wmsg) : Prop :=
  log = [] ∨ log = [MX] ∨ log = [MX, MY]

/-- Reading y = 1 pins the timestamp to the y-message, and the x-message is
strictly below it in the global order. -/
theorem mpReadY1 (log : List Wmsg) (t : Nat) :
    mpLogs log → logByte img0 log t ay = some b1 → t = 2 ∧ writesIn log ax 0 2 := by
  rintro (rfl | rfl | rfl) hlb
  · obtain ⟨_, hi⟩ := logByteCases0 _ _ _ _ hlb
    exact (img0YNb1 hi).elim
  · rcases logByteCases1 _ _ _ _ _ hlb with ⟨_, hi⟩ | ⟨_, hm⟩
    · exact (img0YNb1 hi).elim
    · rw [mbMXY] at hm; cases hm
  · rcases logByteCases2 _ _ _ _ _ _ hlb with ⟨_, hi⟩ | ⟨_, hm⟩ | ⟨ht, _⟩
    · exact (img0YNb1 hi).elim
    · rw [mbMXY] at hm; cases hm
    · exact ⟨ht, writesInCompute _ _ _ _ (by decide)⟩

/-- Any non-initial read of x returns 1: the x-message is the only write. -/
theorem mpReadX (log : List Wmsg) (t : Nat) (v : BitVec 8) :
    mpLogs log → logByte img0 log t ax = some v → t ≠ 0 → v = b1 := by
  rintro (rfl | rfl | rfl) hlb hne
  · exact (hne (logByteCases0 _ _ _ _ hlb).1).elim
  · rcases logByteCases1 _ _ _ _ _ hlb with ⟨ht, _⟩ | ⟨_, hm⟩
    · exact (hne ht).elim
    · rw [mbMXX] at hm; exact (Option.some.inj hm).symm
  · rcases logByteCases2 _ _ _ _ _ _ hlb with ⟨ht, _⟩ | ⟨_, hm⟩ | ⟨_, hm⟩
    · exact (hne ht).elim
    · rw [mbMXX] at hm; exact (Option.some.inj hm).symm
    · rw [mbMYX] at hm; cases hm

/-! ### MP with writer `fence rw,w` AND reader `fence r,rw`: the weak outcome is
FORBIDDEN (herd: forbidden). -/

local notation "MPF_W0" => [IStore ax b1, FENCE_RW_W, IStore ay b1]
local notation "MPF_W1" => [FENCE_RW_W, IStore ay b1]
local notation "MPF_W2" => [IStore ay b1]
local notation "MPF_R0" => [ILoad rg1 ay false, FENCE_R_RW, ILoad rg2 ax false]
local notation "MPF_R1" => [FENCE_R_RW, ILoad rg2 ax false]
local notation "MPF_R2" => [ILoad rg2 ax false]

def mpfC0 : Config := ⟨img0, [], [⟨MPF_W0, ∅, wsInit⟩, ⟨MPF_R0, ∅, wsInit⟩]⟩

/-- The writer's phase determines the log exactly (it is the only writer). -/
def mpfW (p : List Instr) (log : List Wmsg) : Prop :=
  (p = MPF_W0 ∧ log = []) ∨ (p = MPF_W1 ∧ log = [MX]) ∨
  (p = MPF_W2 ∧ log = [MX]) ∨ (p = [] ∧ log = [MX, MY])

/-- The reader's phase carries the ordering it has accumulated: once it has
seen y = 1, the x-message is below its read floor.

THE FORWARD-BANK CONJUNCT.  Since M1 wires `wFwd` into the load view
(`WeakMem.fwdView`), "the load's post-view covers the timestamp it read" only
holds for a NON-forwarded read.  A reader that never stores has an empty bank,
and neither `loadPost` nor `fencePost` populates one, so the conjunct is
trivially inductive — and it is the honest statement of what the ordering
argument needs.  (The MP+acquire reader needs no such conjunct: forwarding is
disabled for acquire loads.) -/
def mpfR (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate) (log : List Wmsg) : Prop :=
  ws.wFwd = ∅ ∧
  ((p = MPF_R0) ∨
   (p = MPF_R1 ∧ (get? regs rg1 = some b1 → writesIn log ax 0 ws.wVrOld)) ∨
   (p = MPF_R2 ∧ (get? regs rg1 = some b1 → writesIn log ax 0 ws.wVrNew)) ∨
   (p = [] ∧ (get? regs rg1 = some b1 → get? regs rg2 = some b1)))

def mpfInv (c : Config) : Prop :=
  c.cImg = img0 ∧
  ∃ h0 h1, c.cHarts = [h0, h1] ∧
    mpfW h0.hProg c.cLog ∧
    mpfR h1.hProg h1.hRegs h1.hWs c.cLog

theorem mpfWLogs (p : List Instr) (log : List Wmsg) : mpfW p log → mpLogs log := by
  rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem mpfRApp (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate)
    (log l : List Wmsg) : mpfR p regs ws log → mpfR p regs ws (log ++ l) := by
  rintro ⟨hf, hR⟩
  refine ⟨hf, ?_⟩
  rcases hR with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨rfl, fun hv => writesInApp _ _ _ _ _ (h hv)⟩)
  · exact .inr (.inr (.inl ⟨rfl, fun hv => writesInApp _ _ _ _ _ (h hv)⟩))
  · exact .inr (.inr (.inr ⟨rfl, h⟩))

theorem mpfStep (c c' : Config) : mpfInv c → lstep c c' → mpfInv c' := by
  obtain ⟨img, log, harts⟩ := c
  obtain ⟨img', log', harts'⟩ := c'
  rintro ⟨himg, ⟨p0, regs0, ws0⟩, ⟨p1, regs1, ws1⟩, hh, hW, hR⟩ ⟨i, h, hlk, himg', hst⟩
  dsimp only at himg hh hW hR hlk himg' hst
  subst himg himg' hh
  have hlogs := mpfWLogs _ _ hW
  match i, hlk with
  | 0, hlk =>
    -- ---- the writer steps ----
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk; subst hlk
    rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inl ⟨rfl, rfl⟩), mpfRApp _ _ _ _ _ hR⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inr (.inl ⟨rfl, rfl⟩)), hR⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inr (.inr ⟨rfl, rfl⟩)), mpfRApp _ _ _ _ _ hR⟩
    · exact (hst : False).elim
  | 1, hlk =>
    -- ---- the reader steps ----
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    obtain ⟨hfwd, hR⟩ := hR
    rcases hR with rfl | ⟨rfl, hRc⟩ | ⟨rfl, hRc⟩ | ⟨rfl, hRc⟩
    · -- load r1 <- y
      obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, (loadPostFwd _ _ _ _).trans hfwd, .inr (.inl ⟨rfl, ?_⟩)⟩
      intro hv
      rw [lookupInsert] at hv
      cases hv
      obtain ⟨rfl, hw⟩ := mpReadY1 _ _ hlogs hlb
      exact writesInMonoHi _ _ _ _ _ (loadPostVrOldNofwd _ _ _ _ hfwd) hw
    · -- fence r,rw
      obtain ⟨rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, (fencePostFwd _ _ _ _ _).trans hfwd,
        .inr (.inr (.inl ⟨rfl, ?_⟩))⟩
      intro hv
      exact writesInMonoHi _ _ _ _ _ (fencePostVrNewR _ _ _) (hRc hv)
    · -- load r2 <- x
      obtain ⟨t, v, hlb, hrd, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, (loadPostFwd _ _ _ _).trans hfwd,
        .inr (.inr (.inr ⟨rfl, ?_⟩))⟩
      rw [lookupInsertNe (by decide), lookupInsert]
      intro hv
      have hpre := writesInMonoHi _ _ _ _ _ (loadVpreVrNew _ false) (hRc hv)
      have hne : t ≠ 0 := readableNotInit _ _ _ _ _ _ hrd hpre
      rw [mpReadX _ _ _ hlogs hlb hne]
    · exact (hst : False).elim
  | i + 2, hlk => simp at hlk

theorem mpfInv0 : mpfInv mpfC0 :=
  ⟨rfl, _, _, rfl, .inl ⟨rfl, rfl⟩, rfl, .inl rfl⟩

/-- MP + writer `fence rw,w` + reader `fence r,rw`: r1 = 1 ∧ r2 = 0 is
UNREACHABLE.  Agrees with RVWMO. -/
theorem mpFencedForbidden (c : Config) (h0 : Hart) (regs1 : GMapF Nat (BitVec 8)) (ws1 : Wstate) :
    reach mpfC0 c →
    c.cHarts = [h0, ⟨[], regs1, ws1⟩] →
    get? regs1 rg1 = some b1 →
    get? regs1 rg2 ≠ some b0 := by
  intro hre hh h1 h2
  have hinv : mpfInv c := invReach _ _ _ mpfInv0 (fun a b ha hs => mpfStep a b ha hs) hre
  obtain ⟨_, g0, g1, hh', _, _, hR⟩ := hinv
  rw [hh] at hh'
  simp only [List.cons.injEq, and_true] at hh'
  obtain ⟨rfl, rfl⟩ := hh'
  rcases hR with hc | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, himp⟩
  · cases hc
  · cases hc
  · cases hc
  · have h3 := himp h1
    rw [h2] at h3
    exact b0NeB1 (Option.some.inj h3)

/-! ### MP with writer `fence rw,w` and an ACQUIRE reader load: the weak outcome
is FORBIDDEN (herd: forbidden).

The reader's first access is `ld.aq` on y — the read half of `amoswap.w.aq`,
which is how the kernel's `acquire` is spelled.  No reader fence: the
acquire's own `vrNew` update does the ordering. -/

local notation "MPA_R0" => [ILoad rg1 ay true, ILoad rg2 ax false]
local notation "MPA_R1" => [ILoad rg2 ax false]

def mpaC0 : Config := ⟨img0, [], [⟨MPF_W0, ∅, wsInit⟩, ⟨MPA_R0, ∅, wsInit⟩]⟩

def mpaR (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate) (log : List Wmsg) : Prop :=
  (p = MPA_R0) ∨
  (p = MPA_R1 ∧ (get? regs rg1 = some b1 → writesIn log ax 0 ws.wVrNew)) ∨
  (p = [] ∧ (get? regs rg1 = some b1 → get? regs rg2 = some b1))

def mpaInv (c : Config) : Prop :=
  c.cImg = img0 ∧
  ∃ h0 h1, c.cHarts = [h0, h1] ∧
    mpfW h0.hProg c.cLog ∧
    mpaR h1.hProg h1.hRegs h1.hWs c.cLog

theorem mpaRApp (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate)
    (log l : List Wmsg) : mpaR p regs ws log → mpaR p regs ws (log ++ l) := by
  rintro (rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩)
  · exact .inl rfl
  · exact .inr (.inl ⟨rfl, fun hv => writesInApp _ _ _ _ _ (h hv)⟩)
  · exact .inr (.inr ⟨rfl, h⟩)

theorem mpaStep (c c' : Config) : mpaInv c → lstep c c' → mpaInv c' := by
  obtain ⟨img, log, harts⟩ := c
  obtain ⟨img', log', harts'⟩ := c'
  rintro ⟨himg, ⟨p0, regs0, ws0⟩, ⟨p1, regs1, ws1⟩, hh, hW, hR⟩ ⟨i, h, hlk, himg', hst⟩
  dsimp only at himg hh hW hR hlk himg' hst
  subst himg himg' hh
  have hlogs := mpfWLogs _ _ hW
  match i, hlk with
  | 0, hlk =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk; subst hlk
    rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inl ⟨rfl, rfl⟩), mpaRApp _ _ _ _ _ hR⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inr (.inl ⟨rfl, rfl⟩)), hR⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inr (.inr ⟨rfl, rfl⟩)), mpaRApp _ _ _ _ _ hR⟩
    · exact (hst : False).elim
  | 1, hlk =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    rcases hR with rfl | ⟨rfl, hRc⟩ | ⟨rfl, hRc⟩
    · -- ld.aq r1 <- y
      obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, .inr (.inl ⟨rfl, ?_⟩)⟩
      intro hv
      rw [lookupInsert] at hv
      cases hv
      obtain ⟨rfl, hw⟩ := mpReadY1 _ _ hlogs hlb
      exact writesInMonoHi _ _ _ _ _ (loadPostVrNewAq _ _ _) hw
    · -- load r2 <- x
      obtain ⟨t, v, hlb, hrd, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, .inr (.inr ⟨rfl, ?_⟩)⟩
      rw [lookupInsertNe (by decide), lookupInsert]
      intro hv
      have hpre := writesInMonoHi _ _ _ _ _ (loadVpreVrNew _ false) (hRc hv)
      have hne : t ≠ 0 := readableNotInit _ _ _ _ _ _ hrd hpre
      rw [mpReadX _ _ _ hlogs hlb hne]
    · exact (hst : False).elim
  | i + 2, hlk => simp at hlk

theorem mpAcquireForbidden (c : Config) (h0 : Hart) (regs1 : GMapF Nat (BitVec 8)) (ws1 : Wstate) :
    reach mpaC0 c →
    c.cHarts = [h0, ⟨[], regs1, ws1⟩] →
    get? regs1 rg1 = some b1 →
    get? regs1 rg2 ≠ some b0 := by
  intro hre hh h1 h2
  have hinv : mpaInv c :=
    invReach _ _ _ ⟨rfl, _, _, rfl, .inl ⟨rfl, rfl⟩, .inl rfl⟩
      (fun a b ha hs => mpaStep a b ha hs) hre
  obtain ⟨_, g0, g1, hh', _, hR⟩ := hinv
  rw [hh] at hh'
  simp only [List.cons.injEq, and_true] at hh'
  obtain ⟨rfl, rfl⟩ := hh'
  rcases hR with hc | ⟨hc, _⟩ | ⟨_, himp⟩
  · cases hc
  · cases hc
  · have h3 := himp h1
    rw [h2] at h3
    exact b0NeB1 (Option.some.inj h3)

/-! ### GAP WITNESS #2 — MP with NO writer fence but a reader `fence r,rw`.

RVWMO ALLOWS the weak outcome here (nothing orders the writer's two stores, so
W→W may be reordered), but this machine FORBIDS it: the promise-free
single-append log hardwires every hart's stores into the global order in
program order, which is exactly the machinery a promise would defeat.  This is
the second documented way in which the M0 machine is STRONGER than RVWMO (the
first is the absence of load buffering — see `lbForbidden`).  Both gaps are in
the sound direction for the kernel proofs, and both are retired by the M6
robustness theorem. -/

local notation "MPG_W0" => [IStore ax b1, IStore ay b1]
local notation "MPG_W1" => [IStore ay b1]

def mpgC0 : Config := ⟨img0, [], [⟨MPG_W0, ∅, wsInit⟩, ⟨MPF_R0, ∅, wsInit⟩]⟩

def mpgW (p : List Instr) (log : List Wmsg) : Prop :=
  (p = MPG_W0 ∧ log = []) ∨ (p = MPG_W1 ∧ log = [MX]) ∨ (p = [] ∧ log = [MX, MY])

def mpgInv (c : Config) : Prop :=
  c.cImg = img0 ∧
  ∃ h0 h1, c.cHarts = [h0, h1] ∧
    mpgW h0.hProg c.cLog ∧
    mpfR h1.hProg h1.hRegs h1.hWs c.cLog

theorem mpgWLogs (p : List Instr) (log : List Wmsg) : mpgW p log → mpLogs log := by
  rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem mpgStep (c c' : Config) : mpgInv c → lstep c c' → mpgInv c' := by
  obtain ⟨img, log, harts⟩ := c
  obtain ⟨img', log', harts'⟩ := c'
  rintro ⟨himg, ⟨p0, regs0, ws0⟩, ⟨p1, regs1, ws1⟩, hh, hW, hR⟩ ⟨i, h, hlk, himg', hst⟩
  dsimp only at himg hh hW hR hlk himg' hst
  subst himg himg' hh
  have hlogs := mpgWLogs _ _ hW
  match i, hlk with
  | 0, hlk =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk; subst hlk
    rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inl ⟨rfl, rfl⟩), mpfRApp _ _ _ _ _ hR⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inr ⟨rfl, rfl⟩), mpfRApp _ _ _ _ _ hR⟩
    · exact (hst : False).elim
  | 1, hlk =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    obtain ⟨hfwd, hR⟩ := hR
    rcases hR with rfl | ⟨rfl, hRc⟩ | ⟨rfl, hRc⟩ | ⟨rfl, hRc⟩
    · obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, (loadPostFwd _ _ _ _).trans hfwd, .inr (.inl ⟨rfl, ?_⟩)⟩
      intro hv
      rw [lookupInsert] at hv
      cases hv
      obtain ⟨rfl, hw⟩ := mpReadY1 _ _ hlogs hlb
      exact writesInMonoHi _ _ _ _ _ (loadPostVrOldNofwd _ _ _ _ hfwd) hw
    · obtain ⟨rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, (fencePostFwd _ _ _ _ _).trans hfwd,
        .inr (.inr (.inl ⟨rfl, ?_⟩))⟩
      intro hv
      exact writesInMonoHi _ _ _ _ _ (fencePostVrNewR _ _ _) (hRc hv)
    · obtain ⟨t, v, hlb, hrd, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, (loadPostFwd _ _ _ _).trans hfwd,
        .inr (.inr (.inr ⟨rfl, ?_⟩))⟩
      rw [lookupInsertNe (by decide), lookupInsert]
      intro hv
      have hpre := writesInMonoHi _ _ _ _ _ (loadVpreVrNew _ false) (hRc hv)
      have hne : t ≠ 0 := readableNotInit _ _ _ _ _ _ hrd hpre
      rw [mpReadX _ _ _ hlogs hlb hne]
    · exact (hst : False).elim
  | i + 2, hlk => simp at hlk

theorem mpReaderFenceOnlyForbidden (c : Config) (h0 : Hart) (regs1 : GMapF Nat (BitVec 8))
    (ws1 : Wstate) :
    reach mpgC0 c →
    c.cHarts = [h0, ⟨[], regs1, ws1⟩] →
    get? regs1 rg1 = some b1 →
    get? regs1 rg2 ≠ some b0 := by
  intro hre hh h1 h2
  have hinv : mpgInv c :=
    invReach _ _ _ ⟨rfl, _, _, rfl, .inl ⟨rfl, rfl⟩, rfl, .inl rfl⟩
      (fun a b ha hs => mpgStep a b ha hs) hre
  obtain ⟨_, g0, g1, hh', _, _, hR⟩ := hinv
  rw [hh] at hh'
  simp only [List.cons.injEq, and_true] at hh'
  obtain ⟨rfl, rfl⟩ := hh'
  rcases hR with hc | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, himp⟩
  · cases hc
  · cases hc
  · cases hc
  · have h3 := himp h1
    rw [h2] at h3
    exact b0NeB1 (Option.some.inj h3)

/-! ### CoRR — read-read coherence.  Seeing x = 2 then x = 1 is FORBIDDEN
(herd: forbidden; this is RVWMO's load-value/coherence axiom). -/

local notation "CX1" => Wmsg.mk ax [b1] (some 0) WmClass.WCplain
local notation "CX2" => Wmsg.mk ax [b2] (some 0) WmClass.WCplain
local notation "CORR_W0" => [IStore ax b1, IStore ax b2]
local notation "CORR_W1" => [IStore ax b2]
local notation "CORR_R0" => [ILoad rg1 ax false, ILoad rg2 ax false]
local notation "CORR_R1" => [ILoad rg2 ax false]

def corrC0 : Config := ⟨img0, [], [⟨CORR_W0, ∅, wsInit⟩, ⟨CORR_R0, ∅, wsInit⟩]⟩

theorem mbCX1 : msgByte CX1 ax = some b1 := by rw [WeakLitmus.msgByteSingle]; decide
theorem mbCX2 : msgByte CX2 ax = some b2 := by rw [WeakLitmus.msgByteSingle]; decide

def corrLogs (log : List Wmsg) : Prop :=
  log = [] ∨ log = [CX1] ∨ log = [CX1, CX2]

/-- x = 2 can only come from the SECOND store, at timestamp 2 — and the first
store then sits strictly below it, which is what pins coherence. -/
theorem corrReadB2 (log : List Wmsg) (t : Nat) :
    corrLogs log → logByte img0 log t ax = some b2 → t = 2 ∧ writesIn log ax 1 2 := by
  rintro (rfl | rfl | rfl) hlb
  · obtain ⟨_, hi⟩ := logByteCases0 _ _ _ _ hlb
    rw [img0X] at hi; exact (b0NeB2 (Option.some.inj hi)).elim
  · rcases logByteCases1 _ _ _ _ _ hlb with ⟨_, hi⟩ | ⟨_, hm⟩
    · rw [img0X] at hi; exact (b0NeB2 (Option.some.inj hi)).elim
    · rw [mbCX1] at hm; exact (b1NeB2 (Option.some.inj hm)).elim
  · rcases logByteCases2 _ _ _ _ _ _ hlb with ⟨_, hi⟩ | ⟨_, hm⟩ | ⟨ht, _⟩
    · rw [img0X] at hi; exact (b0NeB2 (Option.some.inj hi)).elim
    · rw [mbCX1] at hm; exact (b1NeB2 (Option.some.inj hm)).elim
    · exact ⟨ht, writesInCompute _ _ _ _ (by decide)⟩

/-- x = 1 can only come from the FIRST store, at timestamp 1. -/
theorem corrReadB1 (log : List Wmsg) (t : Nat) :
    corrLogs log → logByte img0 log t ax = some b1 → t = 1 := by
  rintro (rfl | rfl | rfl) hlb
  · obtain ⟨_, hi⟩ := logByteCases0 _ _ _ _ hlb
    exact (img0XNb1 hi).elim
  · rcases logByteCases1 _ _ _ _ _ hlb with ⟨_, hi⟩ | ⟨ht, _⟩
    · exact (img0XNb1 hi).elim
    · exact ht
  · rcases logByteCases2 _ _ _ _ _ _ hlb with ⟨_, hi⟩ | ⟨ht, _⟩ | ⟨_, hm⟩
    · exact (img0XNb1 hi).elim
    · exact ht
    · rw [mbCX2] at hm; exact (b1NeB2 (Option.some.inj hm).symm).elim

def corrW (p : List Instr) (log : List Wmsg) : Prop :=
  (p = CORR_W0 ∧ log = []) ∨ (p = CORR_W1 ∧ log = [CX1]) ∨ (p = [] ∧ log = [CX1, CX2])

def corrR (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate) (log : List Wmsg) : Prop :=
  (p = CORR_R0) ∨
  (p = CORR_R1 ∧ (get? regs rg1 = some b2 → writesIn log ax 1 (coh ws ax))) ∨
  (p = [] ∧ (get? regs rg1 = some b2 → get? regs rg2 ≠ some b1))

def corrInv (c : Config) : Prop :=
  c.cImg = img0 ∧
  ∃ h0 h1, c.cHarts = [h0, h1] ∧
    corrW h0.hProg c.cLog ∧
    corrR h1.hProg h1.hRegs h1.hWs c.cLog

theorem corrWLogs (p : List Instr) (log : List Wmsg) : corrW p log → corrLogs log := by
  rintro (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem corrRApp (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate)
    (log l : List Wmsg) : corrR p regs ws log → corrR p regs ws (log ++ l) := by
  rintro (rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩)
  · exact .inl rfl
  · exact .inr (.inl ⟨rfl, fun hv => writesInApp _ _ _ _ _ (h hv)⟩)
  · exact .inr (.inr ⟨rfl, h⟩)

theorem corrStep (c c' : Config) : corrInv c → lstep c c' → corrInv c' := by
  obtain ⟨img, log, harts⟩ := c
  obtain ⟨img', log', harts'⟩ := c'
  rintro ⟨himg, ⟨p0, regs0, ws0⟩, ⟨p1, regs1, ws1⟩, hh, hW, hR⟩ ⟨i, h, hlk, himg', hst⟩
  dsimp only at himg hh hW hR hlk himg' hst
  subst himg himg' hh
  have hlogs := corrWLogs _ _ hW
  match i, hlk with
  | 0, hlk =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk; subst hlk
    rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inl ⟨rfl, rfl⟩), corrRApp _ _ _ _ _ hR⟩
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, rfl, .inr (.inr ⟨rfl, rfl⟩), corrRApp _ _ _ _ _ hR⟩
    · exact (hst : False).elim
  | 1, hlk =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    rcases hR with rfl | ⟨rfl, hRc⟩ | ⟨rfl, hRc⟩
    · -- first load
      obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, .inr (.inl ⟨rfl, ?_⟩)⟩
      intro hv
      rw [lookupInsert] at hv
      cases hv
      obtain ⟨rfl, hw⟩ := corrReadB2 _ _ hlogs hlb
      exact writesInMonoHi _ _ _ _ _ (loadPostCoh _ _ _ _) hw
    · -- second load: coherence forbids going back to timestamp 1
      obtain ⟨t, v, hlb, hrd, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hW, .inr (.inr ⟨rfl, ?_⟩)⟩
      rw [lookupInsertNe (by decide), lookupInsert]
      intro h1 h2
      cases h2
      obtain rfl := corrReadB1 _ _ hlogs hlb
      exact hrd.2 (writesInMonoHi _ _ _ _ _ (Nat.le_max_right _ _) (hRc h1))
    · exact (hst : False).elim
  | i + 2, hlk => simp at hlk

theorem corrForbidden (c : Config) (h0 : Hart) (regs1 : GMapF Nat (BitVec 8)) (ws1 : Wstate) :
    reach corrC0 c →
    c.cHarts = [h0, ⟨[], regs1, ws1⟩] →
    get? regs1 rg1 = some b2 →
    get? regs1 rg2 ≠ some b1 := by
  intro hre hh h1
  have hinv : corrInv c :=
    invReach _ _ _ ⟨rfl, _, _, rfl, .inl ⟨rfl, rfl⟩, .inl rfl⟩
      (fun a b ha hs => corrStep a b ha hs) hre
  obtain ⟨_, g0, g1, hh', _, hR⟩ := hinv
  rw [hh] at hh'
  simp only [List.cons.injEq, and_true] at hh'
  obtain ⟨rfl, rfl⟩ := hh'
  rcases hR with hc | ⟨hc, _⟩ | ⟨_, himp⟩
  · cases hc
  · cases hc
  · exact himp h1

/-! ## Generic list/read helpers used by LB and IRIW -/

theorem lookupAppLast (l : List Wmsg) (m : Wmsg) (j : Nat) (m' : Wmsg) :
    (l ++ [m])[j]? = some m' →
    (j < l.length ∧ l[j]? = some m') ∨ (j = l.length ∧ m' = m) := by
  intro hlk
  by_cases hlt : j < l.length
  · exact .inl ⟨hlt, by rw [← hlk, lookup_app_l hlt]⟩
  · right
    have hj := lookup_lt_Some hlk
    simp only [List.length_append, List.length_singleton] at hj
    have hjl : j = l.length := by omega
    subst hjl
    rw [list_lookup_middle rfl] at hlk
    exact ⟨rfl, (Option.some.inj hlk).symm⟩

/-- A read that is not the era-initial image is a read of some logged write. -/
theorem writesInRead (img : Image) (log : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8) :
    logByte img log t a = some v → t ≠ 0 → writesIn log a 0 log.length := by
  intro hlb hne
  refine (writesInLogByte img log a 0 log.length).2 ⟨t, by omega, ?_, by rw [hlb]; rfl⟩
  exact logByteBounded img log t a (by rw [hlb]; rfl)

theorem readXB1Ne0 (log : List Wmsg) (t : Nat) : logByte img0 log t ax = some b1 → t ≠ 0 := by
  rintro hlb rfl
  rw [logByte0] at hlb
  exact img0XNb1 hlb

theorem readYB1Ne0 (log : List Wmsg) (t : Nat) : logByte img0 log t ay = some b1 → t ≠ 0 := by
  rintro hlb rfl
  rw [logByte0] at hlb
  exact img0YNb1 hlb

/-! ### LB — load buffering.  Both loads returning 1 is FORBIDDEN here.

RVWMO **ALLOWS** this outcome (it is exactly the `po ∪ rf` cycle a promising
machine produces by certifying a store early).  This machine is promise-free,
so a store cannot enter the log before the po-earlier load resolves, and the
outcome is unreachable.  GAP WITNESS #1: the documented LB gap of
`design/weak-memory.md` Decision 1, retired by the M6 robustness theorem.  The
proof below is the honest statement of that gap. -/

/-- hart 0 stores y -/
local notation "LY" => Wmsg.mk ay [b1] (some 0) WmClass.WCplain
/-- hart 1 stores x -/
local notation "LX" => Wmsg.mk ax [b1] (some 1) WmClass.WCplain
local notation "LB_P0" => [ILoad rg1 ax false, IStore ay b1]
local notation "LB_P1" => [IStore ay b1]
local notation "LB_Q0" => [ILoad rg2 ay false, IStore ax b1]
local notation "LB_Q1" => [IStore ax b1]

def lbC0 : Config := ⟨img0, [], [⟨LB_P0, ∅, wsInit⟩, ⟨LB_Q0, ∅, wsInit⟩]⟩

theorem mbLXX : msgByte LX ax = some b1 := by rw [WeakLitmus.msgByteSingle]; decide
theorem mbLXY : msgByte LX ay = none := by rw [WeakLitmus.msgByteSingle]; decide
theorem mbLYX : msgByte LY ax = none := by rw [WeakLitmus.msgByteSingle]; decide
theorem mbLYY : msgByte LY ay = some b1 := by rw [WeakLitmus.msgByteSingle]; decide
theorem lXNeLY : LX ≠ LY := by decide

def lbContent (log : List Wmsg) : Prop :=
  ∀ m, m ∈ log → m = LX ∨ m = LY

def lbH0 (p : List Instr) (regs : GMapF Nat (BitVec 8)) (log : List Wmsg) : Prop :=
  (p = LB_P0 ∧ LY ∉ log) ∨
  (p = LB_P1 ∧ LY ∉ log ∧ (get? regs rg1 = some b1 → writesIn log ax 0 log.length)) ∨
  (p = [] ∧ (get? regs rg1 = some b1 → writesIn log ax 0 log.length))

def lbH1 (p : List Instr) (regs : GMapF Nat (BitVec 8)) (log : List Wmsg) : Prop :=
  (p = LB_Q0 ∧ LX ∉ log) ∨
  (p = LB_Q1 ∧ LX ∉ log ∧ (get? regs rg2 = some b1 → writesIn log ay 0 log.length)) ∨
  (p = [] ∧ (get? regs rg2 = some b1 → writesIn log ay 0 log.length))

def lbInv (c : Config) : Prop :=
  c.cImg = img0 ∧
  ∃ h0 h1, c.cHarts = [h0, h1] ∧
    lbContent c.cLog ∧
    lbH0 h0.hProg h0.hRegs c.cLog ∧
    lbH1 h1.hProg h1.hRegs c.cLog ∧
    (∀ j, c.cLog[j]? = some LY → get? h0.hRegs rg1 = some b1 → writesIn c.cLog ax 0 j) ∧
    (∀ j, c.cLog[j]? = some LX → get? h1.hRegs rg2 = some b1 → writesIn c.cLog ay 0 j)

theorem lbContentApp (log : List Wmsg) (m : Wmsg) :
    lbContent log → (m = LX ∨ m = LY) → lbContent (log ++ [m]) := by
  intro hc hm m' hin
  rcases List.mem_append.1 hin with hin | hin
  · exact hc m' hin
  · rw [List.mem_singleton] at hin; subst hin; exact hm

theorem notinApp (P m : Wmsg) (log : List Wmsg) : P ∉ log → P ≠ m → P ∉ log ++ [m] := by
  intro hn hne hin
  rcases List.mem_append.1 hin with hin | hin
  · exact hn hin
  · exact hne (List.mem_singleton.1 hin)

theorem lbH0App (p : List Instr) (regs : GMapF Nat (BitVec 8)) (log : List Wmsg) (m : Wmsg) :
    LY ≠ m → lbH0 p regs log → lbH0 p regs (log ++ [m]) := by
  rintro hne (⟨rfl, hn⟩ | ⟨rfl, hn, h⟩ | ⟨rfl, h⟩)
  · exact .inl ⟨rfl, notinApp _ _ _ hn hne⟩
  · refine .inr (.inl ⟨rfl, notinApp _ _ _ hn hne, fun hr => ?_⟩)
    exact writesInMonoHi _ _ _ _ _ (by simp) (writesInApp _ _ _ _ _ (h hr))
  · refine .inr (.inr ⟨rfl, fun hr => ?_⟩)
    exact writesInMonoHi _ _ _ _ _ (by simp) (writesInApp _ _ _ _ _ (h hr))

theorem lbH1App (p : List Instr) (regs : GMapF Nat (BitVec 8)) (log : List Wmsg) (m : Wmsg) :
    LX ≠ m → lbH1 p regs log → lbH1 p regs (log ++ [m]) := by
  rintro hne (⟨rfl, hn⟩ | ⟨rfl, hn, h⟩ | ⟨rfl, h⟩)
  · exact .inl ⟨rfl, notinApp _ _ _ hn hne⟩
  · refine .inr (.inl ⟨rfl, notinApp _ _ _ hn hne, fun hr => ?_⟩)
    exact writesInMonoHi _ _ _ _ _ (by simp) (writesInApp _ _ _ _ _ (h hr))
  · refine .inr (.inr ⟨rfl, fun hr => ?_⟩)
    exact writesInMonoHi _ _ _ _ _ (by simp) (writesInApp _ _ _ _ _ (h hr))

/-- The descent that closes LB: an x-message must be preceded by a y-message,
which must be preceded by an x-message, ... — impossible in a finite log that
grows only at its end. -/
theorem lbDescend (log : List Wmsg) :
    lbContent log →
    (∀ j : Nat, log[j]? = some LY → writesIn log ax 0 j) →
    (∀ j : Nat, log[j]? = some LX → writesIn log ay 0 j) →
    ∀ j : Nat, log[j]? = some LX → False := by
  intro hcont hY hX
  have H : ∀ n j : Nat, j ≤ n → log[j]? = some LX → False := by
    intro n
    induction n with
    | zero =>
      intro j hj hlk
      obtain ⟨t, ht0, htj, _⟩ := hX j hlk
      omega
    | succ n ih =>
      intro j hj hlk
      obtain ⟨t, ht0, htj, m, hm, hs⟩ := hX j hlk
      have hmY : m = LY := by
        rcases hcont m (elem_of_list_lookup_2 hm) with rfl | rfl
        · rw [mbLXY] at hs; cases hs
        · rfl
      subst hmY
      obtain ⟨t', ht'0, ht'j, m', hm', hs'⟩ := hY (t - 1) hm
      have hmX : m' = LX := by
        rcases hcont m' (elem_of_list_lookup_2 hm') with rfl | rfl
        · rfl
        · rw [mbLYX] at hs'; cases hs'
      subst hmX
      exact ih (t' - 1) (by omega) hm'
  intro j
  exact H j j (Nat.le_refl _)

theorem lbStep (c c' : Config) : lbInv c → lstep c c' → lbInv c' := by
  obtain ⟨img, log, harts⟩ := c
  obtain ⟨img', log', harts'⟩ := c'
  rintro ⟨himg, ⟨p0, regs0, ws0⟩, ⟨p1, regs1, ws1⟩, hh, hcont, H0, H1, J0, J1⟩
    ⟨i, h, hlk, himg', hst⟩
  dsimp only at himg hh hcont H0 H1 J0 J1 hlk himg' hst
  subst himg himg' hh
  match i, hlk with
  | 0, hlk =>
    -- ---- hart 0 ----
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk; subst hlk
    rcases H0 with ⟨rfl, hn⟩ | ⟨rfl, hn, hw⟩ | ⟨rfl, hw⟩
    · -- load rg1 <- x
      obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hcont, .inr (.inl ⟨rfl, hn, ?_⟩), H1, ?_, J1⟩
      · intro hv
        rw [lookupInsert] at hv
        cases hv
        exact writesInRead _ _ _ _ _ hlb (readXB1Ne0 _ _ hlb)
      · intro j hj _
        exact (hn (elem_of_list_lookup_2 hj)).elim
    · -- store y
      obtain ⟨rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, lbContentApp _ _ hcont (.inr rfl), .inr (.inr ⟨rfl, fun hr => ?_⟩),
        lbH1App _ _ _ _ lXNeLY H1, ?_, ?_⟩
      · exact writesInMonoHi _ _ _ _ _ (by simp) (writesInApp _ _ _ _ _ (hw hr))
      · intro j hj hr
        rcases lookupAppLast _ _ _ _ hj with ⟨_, hj⟩ | ⟨rfl, _⟩
        · exact (hn (elem_of_list_lookup_2 hj)).elim
        · exact writesInApp _ _ _ _ _ (hw hr)
      · intro j hj hr
        rcases lookupAppLast _ _ _ _ hj with ⟨_, hj⟩ | ⟨_, hc⟩
        · exact writesInApp _ _ _ _ _ (J1 j hj hr)
        · exact (lXNeLY hc).elim
    · exact (hst : False).elim
  | 1, hlk =>
    -- ---- hart 1 ----
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    rcases H1 with ⟨rfl, hn⟩ | ⟨rfl, hn, hw⟩ | ⟨rfl, hw⟩
    · -- load rg2 <- y
      obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, hcont, H0, .inr (.inl ⟨rfl, hn, ?_⟩), J0, ?_⟩
      · intro hv
        rw [lookupInsert] at hv
        cases hv
        exact writesInRead _ _ _ _ _ hlb (readYB1Ne0 _ _ hlb)
      · intro j hj _
        exact (hn (elem_of_list_lookup_2 hj)).elim
    · -- store x
      obtain ⟨rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, rfl, lbContentApp _ _ hcont (.inl rfl),
        lbH0App _ _ _ _ (fun hc => lXNeLY hc.symm) H0, .inr (.inr ⟨rfl, fun hr => ?_⟩), ?_, ?_⟩
      · exact writesInMonoHi _ _ _ _ _ (by simp) (writesInApp _ _ _ _ _ (hw hr))
      · intro j hj hr
        rcases lookupAppLast _ _ _ _ hj with ⟨_, hj⟩ | ⟨_, hc⟩
        · exact writesInApp _ _ _ _ _ (J0 j hj hr)
        · exact (lXNeLY hc.symm).elim
      · intro j hj hr
        rcases lookupAppLast _ _ _ _ hj with ⟨_, hj⟩ | ⟨rfl, _⟩
        · exact (hn (elem_of_list_lookup_2 hj)).elim
        · exact writesInApp _ _ _ _ _ (hw hr)
    · exact (hst : False).elim
  | i + 2, hlk => simp at hlk

theorem lbForbidden (c : Config) (regs0 : GMapF Nat (BitVec 8)) (ws0 : Wstate)
    (regs1 : GMapF Nat (BitVec 8)) (ws1 : Wstate) :
    reach lbC0 c →
    c.cHarts = [⟨[], regs0, ws0⟩, ⟨[], regs1, ws1⟩] →
    get? regs0 rg1 = some b1 →
    get? regs1 rg2 ≠ some b1 := by
  intro hre hh hr0 hr1
  have hinv : lbInv c := by
    refine invReach _ _ _ ?_ (fun a b ha hs => lbStep a b ha hs) hre
    refine ⟨rfl, _, _, rfl, ?_, .inl ⟨rfl, List.not_mem_nil⟩, .inl ⟨rfl, List.not_mem_nil⟩, ?_, ?_⟩
    · intro m hm; cases hm
    · intro j hj; simp [lbC0] at hj
    · intro j hj; simp [lbC0] at hj
  obtain ⟨_, g0, g1, hh', hcont, H0, _, J0, J1⟩ := hinv
  rw [hh] at hh'
  simp only [List.cons.injEq, and_true] at hh'
  obtain ⟨rfl, rfl⟩ := hh'
  rcases H0 with ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, hw⟩
  · cases hc
  · cases hc
  obtain ⟨t, _, _, m, hm, hs⟩ := hw hr0
  have hmX : m = LX := by
    rcases hcont m (elem_of_list_lookup_2 hm) with rfl | rfl
    · rfl
    · rw [mbLYX] at hs; cases hs
  subst hmX
  exact lbDescend c.cLog hcont (fun j hj => J0 j hj hr0) (fun j hj => J1 j hj hr1) _ hm

/-! ### IRIW with both readers fenced — FORBIDDEN (herd: forbidden).

RVWMO is multi-copy atomic, so two readers cannot observe the two independent
stores in opposite orders once each pair of loads is separated by
`fence rw,rw`.  Here that falls out of the single global log: "x entered the
log before y" and "y entered before x" cannot both hold. -/

local notation "IX" => Wmsg.mk ax [b1] (some 0) WmClass.WCplain
local notation "IY" => Wmsg.mk ay [b1] (some 1) WmClass.WCplain

def iriwC0 : Config :=
  ⟨img0, [],
   [⟨[IStore ax b1], ∅, wsInit⟩,
    ⟨[IStore ay b1], ∅, wsInit⟩,
    ⟨[ILoad rg1 ax false, FENCE_RW_RW, ILoad rg2 ay false], ∅, wsInit⟩,
    ⟨[ILoad rg1 ay false, FENCE_RW_RW, ILoad rg2 ax false], ∅, wsInit⟩]⟩

/-- "`a` was written into the global order strictly before `b` was" — stated as
a view `v` that already covers a write to `a` and no write to `b`.  The
`v ≤ length log` clause is what makes it stable under later appends. -/
def wfirst (log : List Wmsg) (a b : Int) : Prop :=
  ∃ v, v ≤ log.length ∧ writesIn log a 0 v ∧ ¬ writesIn log b 0 v

theorem wfirstApp (log l : List Wmsg) (a b : Int) : wfirst log a b → wfirst (log ++ l) a b := by
  rintro ⟨v, hv, hw, hn⟩
  refine ⟨v, by simp; omega, writesInApp _ _ _ _ _ hw, fun hc => hn ?_⟩
  exact writesInAppInv log l b 0 v hv hc

theorem wfirstAbsurd (log : List Wmsg) (a b : Int) : wfirst log a b → wfirst log b a → False := by
  rintro ⟨v, _, ⟨t, ht0, htv, mt, hmt, hst⟩, hnb⟩ ⟨w, _, ⟨u, hu0, huw, mu, hmu, hsu⟩, hna⟩
  have h1 : v < u := by
    by_cases hle : u ≤ v
    · exact (hnb ⟨u, hu0, hle, mu, hmu, hsu⟩).elim
    · omega
  have h2 : w < t := by
    by_cases hle : t ≤ w
    · exact (hna ⟨t, ht0, hle, mt, hmt, hst⟩).elim
    · omega
  omega

theorem msgNeB0 (m : Wmsg) (a : Int) : (m = IX ∨ m = IY) → msgByte m a ≠ some b0 := by
  intro hm h
  have hc : msgByte m a = none ∨ msgByte m a = some b1 := by
    rcases hm with rfl | rfl <;> rw [WeakLitmus.msgByteSingle] <;> split <;> simp
  rcases hc with hc | hc <;> rw [hc] at h
  · cases h
  · exact b0NeB1 (Option.some.inj h).symm

def iriwContent (log : List Wmsg) : Prop :=
  ∀ m, m ∈ log → m = IX ∨ m = IY

/-- Reading 0 means reading the era-initial image: nothing ever writes 0. -/
theorem iriwReadB0 (log : List Wmsg) (t : Nat) (a : Int) :
    iriwContent log → logByte img0 log t a = some b0 → t = 0 := by
  intro hc hlb
  cases t with
  | zero => rfl
  | succ i =>
    exfalso
    rw [logByteS] at hlb
    cases hm : log[i]? with
    | none => rw [hm] at hlb; cases hlb
    | some m =>
      rw [hm] at hlb
      exact msgNeB0 m a (hc m (elem_of_list_lookup_2 hm)) hlb

theorem writesInReadAt (img : Image) (log : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8) :
    logByte img log t a = some v → t ≠ 0 → writesIn log a 0 t := by
  intro hlb hne
  exact (writesInLogByte img log a 0 t).2 ⟨t, by omega, Nat.le_refl _, by rw [hlb]; rfl⟩

/-- One reader: loads `a`, fences rw,rw, loads `b`.  The `wFwd` conjunct is the
forward-bank one — see `mpfR`. -/
def iriwR (a b : Int) (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate)
    (log : List Wmsg) : Prop :=
  ws.wFwd = ∅ ∧
  ((p = [ILoad rg1 a false, FENCE_RW_RW, ILoad rg2 b false]) ∨
   (p = [FENCE_RW_RW, ILoad rg2 b false] ∧
      (get? regs rg1 = some b1 → writesIn log a 0 ws.wVrOld)) ∨
   (p = [ILoad rg2 b false] ∧
      (get? regs rg1 = some b1 → writesIn log a 0 ws.wVrNew)) ∨
   (p = [] ∧ (get? regs rg1 = some b1 → get? regs rg2 = some b0 → wfirst log a b)))

theorem iriwRApp (a b : Int) (p : List Instr) (regs : GMapF Nat (BitVec 8)) (ws : Wstate)
    (log l : List Wmsg) : iriwR a b p regs ws log → iriwR a b p regs ws (log ++ l) := by
  rintro ⟨hf, hR⟩
  refine ⟨hf, ?_⟩
  rcases hR with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨rfl, fun hv => writesInApp _ _ _ _ _ (h hv)⟩)
  · exact .inr (.inr (.inl ⟨rfl, fun hv => writesInApp _ _ _ _ _ (h hv)⟩))
  · exact .inr (.inr (.inr ⟨rfl, fun h1 h2 => wfirstApp _ _ _ _ (h h1 h2)⟩))

def iriwInv (c : Config) : Prop :=
  c.cImg = img0 ∧
  ∃ h0 h1 h2 h3, c.cHarts = [h0, h1, h2, h3] ∧
    iriwContent c.cLog ∧
    (h0.hProg = [IStore ax b1] ∨ h0.hProg = []) ∧
    (h1.hProg = [IStore ay b1] ∨ h1.hProg = []) ∧
    iriwR ax ay h2.hProg h2.hRegs h2.hWs c.cLog ∧
    iriwR ay ax h3.hProg h3.hRegs h3.hWs c.cLog

theorem iriwContentApp (log : List Wmsg) (m : Wmsg) :
    iriwContent log → (m = IX ∨ m = IY) → iriwContent (log ++ [m]) := by
  intro hc hm m' hin
  rcases List.mem_append.1 hin with hin | hin
  · exact hc m' hin
  · rw [List.mem_singleton] at hin; subst hin; exact hm

theorem iriwStep (c c' : Config) : iriwInv c → lstep c c' → iriwInv c' := by
  obtain ⟨img, log, harts⟩ := c
  obtain ⟨img', log', harts'⟩ := c'
  rintro ⟨himg, ⟨q0, g0, v0⟩, ⟨q1, g1, v1⟩, ⟨q2, g2, v2⟩, ⟨q3, g3, v3⟩, hh, hcont,
    H0, H1, H2, H3⟩ ⟨i, h, hlk, himg', hst⟩
  dsimp only at himg hh hcont H0 H1 H2 H3 hlk himg' hst
  subst himg himg' hh
  match i, hlk with
  | 0, hlk =>
    -- hart 0: store x
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk; subst hlk
    rcases H0 with rfl | rfl
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, _, _, rfl, iriwContentApp _ _ hcont (.inl rfl), .inr rfl, H1,
        iriwRApp _ _ _ _ _ _ _ H2, iriwRApp _ _ _ _ _ _ _ H3⟩
    · exact (hst : False).elim
  | 1, hlk =>
    -- hart 1: store y
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    rcases H1 with rfl | rfl
    · obtain ⟨rfl, rfl⟩ := hst
      exact ⟨rfl, _, _, _, _, rfl, iriwContentApp _ _ hcont (.inr rfl), H0, .inr rfl,
        iriwRApp _ _ _ _ _ _ _ H2, iriwRApp _ _ _ _ _ _ _ H3⟩
    · exact (hst : False).elim
  | 2, hlk =>
    -- hart 2: loads x then y
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    obtain ⟨hfwd, H2⟩ := H2
    rcases H2 with rfl | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, _, _, rfl, hcont, H0, H1, ⟨(loadPostFwd _ _ _ _).trans hfwd,
        .inr (.inl ⟨rfl, ?_⟩)⟩, H3⟩
      intro hv
      rw [lookupInsert] at hv
      cases hv
      exact writesInMonoHi _ _ _ _ _ (loadPostVrOldNofwd _ _ _ _ hfwd)
        (writesInReadAt _ _ _ _ _ hlb (readXB1Ne0 _ _ hlb))
    · obtain ⟨rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, _, _, rfl, hcont, H0, H1, ⟨(fencePostFwd _ _ _ _ _).trans hfwd,
        .inr (.inr (.inl ⟨rfl, fun hv => ?_⟩))⟩, H3⟩
      exact writesInMonoHi _ _ _ _ _ (fencePostVrNewR _ _ _) (hc hv)
    · obtain ⟨t, v, hlb, hrd, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, _, _, rfl, hcont, H0, H1, ⟨(loadPostFwd _ _ _ _).trans hfwd,
        .inr (.inr (.inr ⟨rfl, ?_⟩))⟩, H3⟩
      rw [lookupInsertNe (by decide), lookupInsert]
      intro hv1 hv2
      cases hv2
      obtain rfl := iriwReadB0 _ _ _ hcont hlb
      refine ⟨min (loadVpre v2 false) _, Nat.min_le_right _ _, ?_, fun hw => ?_⟩
      · exact writesInClip _ _ _ _
          (writesInMonoHi _ _ _ _ _ (loadVpreVrNew _ _) (hc hv1))
      · exact hrd.2 (writesInMonoHi _ _ _ _ _
          (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)) hw)
    · exact (hst : False).elim
  | 3, hlk =>
    -- hart 3: loads y then x
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hlk
    subst hlk
    obtain ⟨hfwd, H3⟩ := H3
    rcases H3 with rfl | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · obtain ⟨t, v, hlb, _, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, _, _, rfl, hcont, H0, H1, H2, ⟨(loadPostFwd _ _ _ _).trans hfwd,
        .inr (.inl ⟨rfl, ?_⟩)⟩⟩
      intro hv
      rw [lookupInsert] at hv
      cases hv
      exact writesInMonoHi _ _ _ _ _ (loadPostVrOldNofwd _ _ _ _ hfwd)
        (writesInReadAt _ _ _ _ _ hlb (readYB1Ne0 _ _ hlb))
    · obtain ⟨rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, _, _, rfl, hcont, H0, H1, H2, ⟨(fencePostFwd _ _ _ _ _).trans hfwd,
        .inr (.inr (.inl ⟨rfl, fun hv => ?_⟩))⟩⟩
      exact writesInMonoHi _ _ _ _ _ (fencePostVrNewR _ _ _) (hc hv)
    · obtain ⟨t, v, hlb, hrd, rfl, rfl⟩ := hst
      refine ⟨rfl, _, _, _, _, rfl, hcont, H0, H1, H2, ⟨(loadPostFwd _ _ _ _).trans hfwd,
        .inr (.inr (.inr ⟨rfl, ?_⟩))⟩⟩
      rw [lookupInsertNe (by decide), lookupInsert]
      intro hv1 hv2
      cases hv2
      obtain rfl := iriwReadB0 _ _ _ hcont hlb
      refine ⟨min (loadVpre v3 false) _, Nat.min_le_right _ _, ?_, fun hw => ?_⟩
      · exact writesInClip _ _ _ _
          (writesInMonoHi _ _ _ _ _ (loadVpreVrNew _ _) (hc hv1))
      · exact hrd.2 (writesInMonoHi _ _ _ _ _
          (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_max_left _ _)) hw)
    · exact (hst : False).elim
  | i + 4, hlk => simp at hlk

theorem iriwForbidden (c : Config) (h0 h1 : Hart) (regs2 : GMapF Nat (BitVec 8)) (ws2 : Wstate)
    (regs3 : GMapF Nat (BitVec 8)) (ws3 : Wstate) :
    reach iriwC0 c →
    c.cHarts = [h0, h1, ⟨[], regs2, ws2⟩, ⟨[], regs3, ws3⟩] →
    get? regs2 rg1 = some b1 → get? regs2 rg2 = some b0 →
    get? regs3 rg1 = some b1 → get? regs3 rg2 ≠ some b0 := by
  intro hre hh ha1 ha2 hb1 hb2
  have hinv : iriwInv c := by
    refine invReach _ _ _ ?_ (fun a b ha hs => iriwStep a b ha hs) hre
    refine ⟨rfl, _, _, _, _, rfl, ?_, .inl rfl, .inl rfl, ⟨rfl, .inl rfl⟩, ⟨rfl, .inl rfl⟩⟩
    intro m hm; cases hm
  obtain ⟨_, g0, g1, g2, g3, hh', _, _, _, H2, H3⟩ := hinv
  rw [hh] at hh'
  simp only [List.cons.injEq, and_true] at hh'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hh'
  obtain ⟨_, H2⟩ := H2
  obtain ⟨_, H3⟩ := H3
  rcases H2 with hc | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, himp2⟩
  · cases hc
  · cases hc
  · cases hc
  rcases H3 with hc | ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, himp3⟩
  · cases hc
  · cases hc
  · cases hc
  exact wfirstAbsurd _ _ _ (himp2 ha1 ha2) (himp3 hb1 hb2)

/-! ### amoswap.w.aq — the read half is forced to the globally-latest write.

This exercises the `IAmoSwapAq` arm of `lstep`.  `amoLatestUnique` says the
atomicity constraint pins the timestamp; `amoNotStale` is the concrete
consequence the kernel's `acquire` depends on — once another hart's store to
the lock word is in the log, the AMO cannot read the era-initial value. -/

theorem stepAmo (c : Config) (i r : Nat) (a : Int) (v : BitVec 8) (rest : List Instr)
    (regs : GMapF Nat (BitVec 8)) (ws : Wstate) (t : Nat) (vv : BitVec 8) :
    c.cHarts[i]? = some ⟨IAmoSwapAq r a v :: rest, regs, ws⟩ →
    logByte c.cImg c.cLog t a = some vv →
    ¬ writesIn c.cLog a t c.cLog.length →
    readable c.cImg c.cLog ws (loadVpre ws true) a t →
    lstep c ⟨c.cImg, c.cLog ++ [⟨a, [v], some i, .WCexcl⟩],
      c.cHarts.set i ⟨rest, insert regs r vv,
        storePost (loadPost ws true a t) false a (c.cLog.length + 1)⟩⟩ :=
  fun hlk hv hat hr => ⟨i, _, hlk, rfl, t, vv, hv, hat, hr, rfl, rfl⟩

theorem amoNotStale (m : Wmsg) (t : Nat) :
    (msgByte m ax).isSome → ¬ writesIn [m] ax t 1 → t ≠ 0 := by
  rintro hm hn rfl
  exact hn ⟨1, by omega, Nat.le_refl _, m, rfl, hm⟩

def amoC0 : Config :=
  ⟨img0, [], [⟨[IStore ax b1], ∅, wsInit⟩, ⟨[IAmoSwapAq rg1 ax b2], ∅, wsInit⟩]⟩

theorem amoSwapReachable :
    ∃ c, reach amoC0 c ∧
      ∃ regs ws, c.cHarts[1]? = some ⟨[], regs, ws⟩ ∧ get? regs rg1 = some b1 := by
  refine ⟨?c, ?run, ?rest⟩
  case run =>
    refine rtc_l (stepStore _ 0 _ _ _ _ _ rfl) ?_
    refine rtc_l (stepAmo _ 1 rg1 ax b2 _ _ _ 1 b1 rfl
      ((logByte1 _ _ _ _).trans (by rw [WeakLitmus.msgByteSingle]; decide))
      (notWritesInCompute _ _ _ _ (by decide))
      ((readablebSpec _ _ _ _ _ _).1 (by decide))) ?_
    exact rtc_refl _
  case rest => exact ⟨_, _, rfl, lookupInsert⟩

/-! ### The FORWARD BANK, in action.

No litmus program above reads back its own store, so the M1 wire-in of `wFwd`
into the load view (`WeakMem.fwdView`, design doc Decision 3) is invisible to
every verdict — which is exactly why it needs its own witness here, or the
wire-in could be vacuous and nobody would notice.

A hart that stores x = 1 and then loads x back reads its OWN message
(timestamp 1, which coherence pins), but its read view rises only to the view
the store banked — PARM's `FwdItem` view, i.e. the store's address/data
dependency views, which is 0 in this dependency-free machine (D-7, 2026-08-17;
M1 banked `wVwNew` here, which was LARGER than PARM's and therefore removed
hardware behaviours).  Coherence still records the real timestamp.  No verdict
below depends on which of the two is banked: every hart in this file reaches
its store with `wVwNew = 0`. -/

local notation "FWD_WS" => storePost wsInit false ax 1

theorem fwdBankAfterStore : get? (FWD_WS).wFwd ax = some (1, 0) := lookupInsert

/-- The forwarded (relaxed) load: post-view 0, NOT the timestamp 1. -/
theorem fwdSelfreadRelaxed : (loadPost (FWD_WS) false ax 1).wVrOld = 0 := by decide

/-- Coherence is unaffected — the read still cannot go back before its own store
(this is what keeps CoRR-style verdicts intact). -/
theorem fwdSelfreadCoh : 1 ≤ coh (loadPost (FWD_WS) false ax 1) ax := loadPostCoh _ _ _ _

/-- An ACQUIRE load is never forwarded (Promising-ARM's `read_view` side
condition): its post-view is the timestamp, so the kernel's `amoswap.w.aq`
keeps its full ordering force even on its own lock word. -/
theorem fwdSelfreadAcquire : 1 ≤ (loadPost (FWD_WS) true ax 1).wVrOld := by decide

end Weak
