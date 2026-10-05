/-
Weak: **the promise-free view machine** (the M0 model spike of the RVWMO model).

Rocq: `iris/WeakMem.v` @ xxvzwolszwmp (1cc222280).

The Rocq header, verbatim in substance: the Promising-RISC-V machine shape with
the promise machinery deliberately omitted (every store appends at the end of
the global log), with syntactic dependency tracking (ppo 9–13) dropped.
DELIBERATELY DEPENDENCY-FREE: this file imports only the stdpp shims, no Iris
proof mode, no Sail.  The machine types are abstracted for the spike —
addresses are `Int` (Rocq `Z`; the real machine instantiates at `Arch.pa`),
bytes are `BitVec 8` (Rocq `bv 8`), agents and register names are `Nat`.
Nothing below inspects an agent identifier, and addresses are used only as
map keys and under `≤`/`-`.  The design records of the Rocq file (the forward
bank's D-7r note, the W-TV translation bank, the RMW split S2, D-2r, the M6
inert components, the D2 dependency components) are the comments on the
corresponding Lean definitions below; they are kept because the notes cite
them.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention.  Every Rocq definition/lemma
   `foo_bar_baz` is the lowerCamelCase `fooBarBaz` (a segment already in
   camelCase keeps it with its first letter raised: `ctrl_post_vrOld` ↦
   `ctrlPostVrOld`, `load_post_fold_vrOld'` ↦ `loadPostFoldVrOld'`, `log_byte_0`
   ↦ `logByte0`); types are UpperCamelCase (`wmsg` ↦ `Wmsg`, `wstate` ↦
   `Wstate`, `wresv` ↦ `Wresv`, `dsrc` ↦ `Dsrc`, `wm_class` ↦ `WmClass`,
   `image` ↦ `Image`); record fields likewise (`w_coh` ↦ `wCoh`, `wm_pa` ↦
   `wmPa`, `rv_ts` ↦ `rvTs`, ...); inductive constructors keep their Rocq
   spelling (`DReg`, `DLdRes`, `WCplain`, `WCrel`, `WCexcl`).  Record
   constructors are the structures' `mk` (`WMsg b d t k` ↦ `⟨b, d, t, k⟩`,
   `WResv b ts v` ↦ `⟨b, ts, v⟩`).  Exceptions: the Rocq `Reflexive` /
   `Transitive` instances `ws_le_refl`/`ws_le_trans` (and the `_nc`,
   `ws_depmove`, `ws_ctrl_up` ones) are theorems `wsLeRefl`/`wsLeTrans`/...
   plus a `Trans` instance.
2. VOCABULARY (stdpp ↦ Lean, as in `MachCSL/StdppList.lean`, `StdppMap.lean`):
   `gmap K V` ↦ `GMapF K V` with `get?`/`insert`; `l !! i` ↦ `l[i]?`;
   `l !!! i` ↦ `l[i]!`; `seq` ↦ `List.range'`; `zip_with` ↦ `List.zipWith`;
   `existsb`/`forallb` ↦ `List.any`/`List.all`; `bool_decide` ↦ `decide`;
   `is_Some o` ↦ `o.isSome`; `Forall P l` ↦ `∀ x ∈ l, P x`; `Nat.max` ↦ `max`;
   `S n` ↦ `n + 1`; `Z.of_nat j` ↦ `(j : Int)`; `Z.to_nat` ↦ `Int.toNat`;
   `default 0 o` ↦ `o.getD 0`.
3. CONVERSION FACTS THAT BECOME PROPOSITIONAL.  Rocq's `Nat.max 0 x`
   reduces to `x` by iota; Lean's `max 0 x` does not (it is an `if` on
   `0 ≤ x`).  So the `_0` collapse lemmas whose Rocq proof is `done` because
   of that reduction (`load_vpre_d_0`, `load_post_bytes_d_0`,
   `load_post_run_d_0`, `store_post_run_d_0`, `exload_post_run_d_0`,
   `ctrl_post_0`) are proved by `simp [Nat.zero_max]` here; their statements
   are unchanged.  Downstream files that relied on the CONVERSION (writing
   the `_d` function where the plain one is expected) must rewrite with these
   lemmas.  `srcs_view_nil` and every field-transparency lemma stay `rfl`.
4. `rev_ind` (snoc induction) is the local `snocInd` below.
5. `Local Lemma`s of the Rocq file are ordinary theorems here (no
   `private`), so later files may use them.
6. The Rocq `Add Printing Constructor` / `Global Instance ... EqDecision`
   lines (`dsrc_eq_dec`, `wm_class_eq_dec`, `wmsg_eq_dec`, `wresv_eq_dec`) are
   `deriving DecidableEq` clauses.  The Rocq notations `agent := nat` and
   `wreg := nat` are not introduced: `Nat` is written directly (a Lean `Agent`
   would clash with `MachCSL.Agent`).  `image` ↦ `Image` (an `abbrev`).
7. Name exception to the rule of 1: `Forall_zip_seq` ↦ `forallZipSeq`.
   Lean-only helpers (no Rocq twin): `snocInd`,
   `memLoadRunAts`, `memStoreRunAs` (the zipped/mapped byte runs contain byte
   `j`, used where Rocq inlines `elem_of_list_lookup_2` + `lookup_zip_with`),
   and the private `latestTsAccFstGen`, `cohInsertLe`, `intAddNatZero`,
   `loadPostFoldRelp`.
8. Statement spellings: `coh_upd_ne`'s right side `default 0 (m !! a')` is
   `(get? m a').getD 0`; `ts !!! j` is `ts[j]!`; `wresv_bounded`'s inner
   binders are annotated `(j t : Nat)`.  No premise or quantifier changed.

**Not ported:** nothing — every Rocq definition and lemma has a Lean twin.

**Statements checked** (diffed against Rocq by hand): all of them.
-/
import MachCSL.SetSolver
import MachCSL.StdppList
import MachCSL.Rel

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-! ## Dependency sources, the image, messages -/

/-- THE DEPENDENCY SOURCE VOCABULARY (deps design §2.2).  `DReg r`: a general-
purpose register (PARM's `rmap` entry); `DLdRes`: this instruction's load result
(PARM's `res`, banked in `wLdv` and reset by `LInstr`).  Register names (Rocq
`wreg`) and agents (Rocq `agent`) are `Nat`. -/
inductive Dsrc where
  | DReg (r : Nat)
  | DLdRes
  deriving DecidableEq, Inhabited

/-- The era-initial image: a partial function on addresses (see the Rocq note:
the interpreter converts at the seam, so this is a function, not a map). -/
abbrev Image : Type := Int → Option (BitVec 8)

/-- THE MESSAGE CLASS (M6 D-M6-6): an inert syntactic tag recording how a write
was issued.  `WCexcl` — the write half of an exclusive access; `WCrel` — a
release-class publication; `WCplain` — everything else. -/
inductive WmClass where
  | WCplain
  | WCrel
  | WCexcl
  deriving DecidableEq, Inhabited

/-- One write event, covering `[wmPa, wmPa + |wmData|)`; `wmTid` names the
appending agent; `wmAk` is the inert class field. -/
structure Wmsg where
  wmPa : Int
  wmData : List (BitVec 8)
  wmTid : Option Nat
  wmAk : WmClass
  deriving DecidableEq, Inhabited

/-- The byte message `m` writes at address `a` (`none` outside its range). -/
def msgByte (m : Wmsg) (a : Int) : Option (BitVec 8) :=
  if m.wmPa ≤ a then m.wmData[(a - m.wmPa).toNat]? else none

/-! ## The two tid-space notions both towers share -/

/-- `tidHart nh t`: `t` is one of the first `nh` agents, i.e. a hart. -/
def tidHart (nh : Nat) (t : Option Nat) : Prop :=
  ∃ i : Nat, t = some i ∧ i < nh

theorem tidHartNeDisk (nh : Nat) (t : Option Nat) : tidHart nh t → t ≠ some nh := by
  rintro ⟨i, rfl, hlt⟩ h
  injection h with h
  omega

theorem tidHartNone (nh : Nat) : ¬ tidHart nh none := by
  rintro ⟨i, h, _⟩
  cases h

/-- PUBLICATION, PURELY OVER THE LOG (φ-upgrade §1b): a later message of the
same agent is release-class. -/
def wpublished (log : List Wmsg) (tid : Option Nat) (p : Nat) : Prop :=
  ∃ (q : Nat) (mq : Wmsg), p ≤ q ∧ log[q]? = some mq ∧ mq.wmTid = tid ∧ mq.wmAk = .WCrel

theorem wpublishedApp (log ms : List Wmsg) (tid : Option Nat) (p : Nat) :
    wpublished log tid p → wpublished (log ++ ms) tid p := by
  rintro ⟨q, mq, hle, hq, ht, hk⟩
  exact ⟨q, mq, hle, lookup_app_l_Some hq, ht, hk⟩

/-- Memory: the era-initial image plus an append-only log.  Timestamp 0 is the
image; timestamp `i+1` is log entry `i`. -/
def logByte (img : Image) (log : List Wmsg) (t : Nat) (a : Int) : Option (BitVec 8) :=
  match t with
  | 0 => img a
  | i + 1 => log[i]?.bind (fun m => msgByte m a)

theorem logByte0 (img : Image) (log : List Wmsg) (a : Int) : logByte img log 0 a = img a := rfl

theorem logByteS (img : Image) (log : List Wmsg) (i : Nat) (a : Int) :
    logByte img log (i + 1) a = log[i]?.bind (fun m => msgByte m a) := rfl

/-- A timestamp that writes anything is within the log. -/
theorem logByteBounded (img : Image) (log : List Wmsg) (t : Nat) (a : Int) :
    (logByte img log t a).isSome → t ≤ log.length := by
  intro h
  cases t with
  | zero => omega
  | succ i =>
    rw [logByteS] at h
    cases hm : log[i]? with
    | none => rw [hm] at h; simp at h
    | some m => have := lookup_lt_Some hm; omega

/-- The log is append-only, so old timestamps keep their values. -/
theorem logByteApp (img : Image) (log l : List Wmsg) (t : Nat) (a : Int) :
    t ≤ log.length → logByte img (log ++ l) t a = logByte img log t a := by
  intro h
  cases t with
  | zero => rfl
  | succ i => rw [logByteS, logByteS, lookup_app_l (by omega)]

/-! ## `writesIn`: some timestamp in a half-open view window writes a byte -/

/-- `writesIn log a lo hi`: some timestamp `t` with `lo < t ≤ hi` writes `a`. -/
def writesIn (log : List Wmsg) (a : Int) (lo hi : Nat) : Prop :=
  ∃ t : Nat, lo < t ∧ t ≤ hi ∧ ∃ m, log[t - 1]? = some m ∧ (msgByte m a).isSome

/-- The bridge to `logByte` at any image. -/
theorem writesInLogByte (img : Image) (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesIn log a lo hi ↔ ∃ t : Nat, lo < t ∧ t ≤ hi ∧ (logByte img log t a).isSome := by
  constructor
  · rintro ⟨t, hlo, hhi, m, hm, hs⟩
    refine ⟨t, hlo, hhi, ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hm
    rw [logByteS, hm]; exact hs
  · rintro ⟨t, hlo, hhi, hs⟩
    refine ⟨t, hlo, hhi, ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    rw [logByteS] at hs
    simp only [Nat.add_sub_cancel]
    cases hm : log[i]? with
    | none => rw [hm] at hs; simp at hs
    | some m => rw [hm] at hs; exact ⟨m, rfl, hs⟩

theorem writesInMono (log : List Wmsg) (a : Int) (lo hi lo' hi' : Nat) :
    lo' ≤ lo → hi ≤ hi' → writesIn log a lo hi → writesIn log a lo' hi' := by
  rintro h1 h2 ⟨t, h3, h4, rest⟩
  exact ⟨t, by omega, by omega, rest⟩

theorem writesInMonoHi (log : List Wmsg) (a : Int) (lo hi hi' : Nat) :
    hi ≤ hi' → writesIn log a lo hi → writesIn log a lo hi' :=
  fun h => writesInMono log a lo hi lo hi' (Nat.le_refl _) h

theorem writesInApp (log l : List Wmsg) (a : Int) (lo hi : Nat) :
    writesIn log a lo hi → writesIn (log ++ l) a lo hi := by
  rintro ⟨t, h1, h2, m, hm, hs⟩
  exact ⟨t, h1, h2, m, lookup_app_l_Some hm, hs⟩

/-- A write in a window that predates the extension was already there. -/
theorem writesInAppInv (log l : List Wmsg) (a : Int) (lo hi : Nat) :
    hi ≤ log.length → writesIn (log ++ l) a lo hi → writesIn log a lo hi := by
  rintro hle ⟨t, h1, h2, m, hm, hs⟩
  rw [lookup_app_l (by omega)] at hm
  exact ⟨t, h1, h2, m, hm, hs⟩

/-- Any witness is inside the log, so the window may be clipped to it. -/
theorem writesInClip (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesIn log a lo hi → writesIn log a lo (min hi log.length) := by
  rintro ⟨t, h1, h2, m, hm, hs⟩
  have := lookup_lt_Some hm
  exact ⟨t, h1, by omega, m, hm, hs⟩

theorem notWritesInClip (log : List Wmsg) (a : Int) (lo hi : Nat) :
    ¬ writesIn log a lo (min hi log.length) → ¬ writesIn log a lo hi :=
  fun hn hw => hn (writesInClip log a lo hi hw)

/-! ## Deciding `writesIn` by reflection -/

def msgWritesb (m : Wmsg) (a : Int) : Bool :=
  match msgByte m a with
  | some _ => true
  | none => false

theorem msgWritesbTrue (m : Wmsg) (a : Int) : msgWritesb m a = true ↔ (msgByte m a).isSome := by
  unfold msgWritesb; split <;> simp_all

theorem msgWritesbFalse (m : Wmsg) (a : Int) : msgWritesb m a = false ↔ msgByte m a = none := by
  unfold msgWritesb; split <;> simp_all

def writesInb (log : List Wmsg) (a : Int) (lo hi : Nat) : Bool :=
  (List.range' 1 log.length).any (fun t =>
    decide (lo < t) && decide (t ≤ hi) &&
      match log[t - 1]? with
      | some m => msgWritesb m a
      | none => false)

theorem writesInbSpec (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesIn log a lo hi ↔ writesInb log a lo hi = true := by
  unfold writesInb writesIn
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, hlo, hhi, m, hm, hs⟩
    have hlt := lookup_lt_Some hm
    refine ⟨t, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
    rw [hm]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hlo, hhi⟩, (msgWritesbTrue m a).2 hs⟩
  · rintro ⟨t, _, hb⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    revert h3
    cases hm : log[t - 1]? with
    | none => intro h3; cases h3
    | some m => intro h3; exact ⟨t, h1, h2, m, hm, (msgWritesbTrue m a).1 h3⟩

theorem notWritesInCompute (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesInb log a lo hi = false → ¬ writesIn log a lo hi := by
  intro hb hw
  rw [(writesInbSpec log a lo hi).1 hw] at hb
  cases hb

theorem writesInCompute (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesInb log a lo hi = true → writesIn log a lo hi :=
  (writesInbSpec log a lo hi).2

theorem notWritesInb (log : List Wmsg) (a : Int) (lo hi : Nat) :
    writesInb log a lo hi = false ↔ ¬ writesIn log a lo hi := by
  refine ⟨notWritesInCompute log a lo hi, fun hn => ?_⟩
  cases hb : writesInb log a lo hi with
  | false => rfl
  | true => exact (hn (writesInCompute log a lo hi hb)).elim

/-! ## The per-agent weak state -/

/-- THE AGENT-LOCAL RESERVATION of the RMW split (design weak-memory-rmw-split.md
§3): what an `LExLoad` banks and the matching `LExStore`'s fulfil consumes.
`rvTs` holds the read half's per-byte timestamps positionally from `rvBase`;
`rvView` is the read half's banked post-view. -/
structure Wresv where
  rvBase : Int
  rvTs : List Nat
  rvView : Nat
  deriving DecidableEq, Inhabited

/-- The Promising-RISC-V thread state minus promises.  See the Rocq field
comments (reproduced in substance): `wCoh` per-byte coherence floor (default 0);
`wVrOld`/`wVwOld` max post-view of past loads/stores; `wVrNew`/`wVwNew` pre-view
floors for future loads/stores; `wVRel` release view; `wFwd` the forward bank
(timestamp + forwarded view); `wPub`/`wRelp` the two M6 inert components (the
publication watermark and the pending-release flag); `wRegv`/`wVcap`/`wLdv` the
three D2 dependency components (register views, the control/address-capture
view, the current instruction's load-result view); `wRes`/`wTbank` the two
RMW-split components (the agent-local reservation and the W-TV translation
bank). -/
structure Wstate where
  wCoh : GMapF Int Nat
  wVrOld : Nat
  wVwOld : Nat
  wVrNew : Nat
  wVwNew : Nat
  wVRel : Nat
  wFwd : GMapF Int (Nat × Nat)
  wPub : Nat
  wRelp : Bool
  wRegv : GMapF Nat Nat
  wVcap : Nat
  wLdv : Nat
  wRes : Option Wresv
  wTbank : Nat

/-- Coherence lookup with default 0. -/
def coh (ws : Wstate) (a : Int) : Nat := (get? ws.wCoh a).getD 0

/-- Register-view lookup with default 0. -/
def regv (ws : Wstate) (r : Nat) : Nat := (get? ws.wRegv r).getD 0

/-- THE VIEW OF A DEPENDENCY SOURCE (PARM's `sem_expr`). -/
def dsrcView (ws : Wstate) (s : Dsrc) : Nat :=
  match s with
  | .DReg r => regv ws r
  | .DLdRes => ws.wLdv

def srcsView (ws : Wstate) (srcs : List Dsrc) : Nat :=
  srcs.foldr (fun s v => max (dsrcView ws s) v) 0

/-- THE INSTANCE FACT: a label with no operands has view `0`, by conversion. -/
theorem srcsViewNil (ws : Wstate) : srcsView ws [] = 0 := rfl

theorem srcsViewCons (ws : Wstate) (s : Dsrc) (l : List Dsrc) :
    srcsView ws (s :: l) = max (dsrcView ws s) (srcsView ws l) := rfl

def wsInit : Wstate where
  wCoh := ∅
  wVrOld := 0
  wVwOld := 0
  wVrNew := 0
  wVwNew := 0
  wVRel := 0
  wFwd := ∅
  wPub := 0
  wRelp := false
  wRegv := ∅
  wVcap := 0
  wLdv := 0
  wRes := none
  wTbank := 0

theorem regvInit (r : Nat) : regv wsInit r = 0 := rfl

theorem srcsViewInit (l : List Dsrc) : srcsView wsInit l = 0 := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [srcsViewCons, ih, Nat.max_zero]
    cases s with
    | DReg r => exact regvInit r
    | DLdRes => rfl

theorem cohInit (a : Int) : coh wsInit a = 0 := rfl

theorem cohUpdEq (m : GMapF Int Nat) (vrO vwO vrN vwN vR : Nat) (fwd : GMapF Int (Nat × Nat))
    (pb : Nat) (rp : Bool) (rg : GMapF Nat Nat) (vc ld : Nat) (rs : Option Wresv) (tb : Nat)
    (a : Int) (n : Nat) :
    coh { wCoh := insert m a n, wVrOld := vrO, wVwOld := vwO, wVrNew := vrN, wVwNew := vwN,
          wVRel := vR, wFwd := fwd, wPub := pb, wRelp := rp, wRegv := rg, wVcap := vc,
          wLdv := ld, wRes := rs, wTbank := tb } a = n := by
  simp [coh, lookupInsert]

theorem cohUpdNe (m : GMapF Int Nat) (vrO vwO vrN vwN vR : Nat) (fwd : GMapF Int (Nat × Nat))
    (pb : Nat) (rp : Bool) (rg : GMapF Nat Nat) (vc ld : Nat) (rs : Option Wresv) (tb : Nat)
    (a a' : Int) (n : Nat) :
    a' ≠ a →
    coh { wCoh := insert m a n, wVrOld := vrO, wVwOld := vwO, wVrNew := vrN, wVwNew := vwN,
          wVRel := vR, wFwd := fwd, wPub := pb, wRelp := rp, wRegv := rg, wVcap := vc,
          wLdv := ld, wRes := rs, wTbank := tb } a'
    = (get? m a').getD 0 := by
  intro h
  simp [coh, lookupInsertNe (Ne.symm h)]

/-! ## Readability -/

/-- `readable img log ws vpre a t`: the agent may read timestamp `t` for byte
`a` at load pre-view `vpre`: `t` writes `a`, and no timestamp strictly between
`t` and the floor `vpre ⊔ coh(a)` writes `a`. -/
def readable (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int) (t : Nat) :
    Prop :=
  (logByte img log t a).isSome ∧ ¬ writesIn log a t (max vpre (coh ws a))

/-- The decision procedure the interpreter checks a read with. -/
def readableb (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int) (t : Nat) :
    Bool :=
  match logByte img log t a with
  | some _ => !(writesInb log a t (max vpre (coh ws a)))
  | none => false

theorem readablebSpec (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int)
    (t : Nat) : readableb img log ws vpre a t = true ↔ readable img log ws vpre a t := by
  unfold readableb readable
  cases hv : logByte img log t a with
  | some v =>
    simp only [Bool.not_eq_true', Option.isSome_some, true_and]
    exact notWritesInb log a t _
  | none => simp

/-- Readability is ANTI-monotone in the pre-view. -/
theorem readableAntiVpre (img : Image) (log : List Wmsg) (ws : Wstate) (vpre vpre' : Nat)
    (a : Int) (t : Nat) :
    vpre' ≤ vpre → readable img log ws vpre a t → readable img log ws vpre' a t := by
  rintro hle ⟨hs, hn⟩
  exact ⟨hs, fun hw => hn (writesInMonoHi log a t _ _ (by omega) hw)⟩

/-- THE WORKHORSE of the litmus proofs: once the pre-view covers a write to
`a`, the era-initial image is no longer readable. -/
theorem readableNotInit (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int)
    (t : Nat) : readable img log ws vpre a t → writesIn log a 0 vpre → t ≠ 0 := by
  rintro ⟨_, hn⟩ hw rfl
  exact hn (writesInMonoHi log a 0 _ _ (by omega) hw)

/-! ## Coherent (latest) reads -/

def latest (img : Image) (log : List Wmsg) (a : Int) (t : Nat) : Prop :=
  (logByte img log t a).isSome ∧ ¬ writesIn log a t log.length

theorem latestUnique (img : Image) (log : List Wmsg) (a : Int) (t t' : Nat) :
    latest img log a t → latest img log a t' → t = t' := by
  rintro ⟨ht, hnt⟩ ⟨ht', hnt'⟩
  by_cases hlt : t < t'
  · exact (hnt ((writesInLogByte img log a t _).2
      ⟨t', hlt, logByteBounded img log t' a ht', ht'⟩)).elim
  by_cases hlt' : t' < t
  · exact (hnt' ((writesInLogByte img log a t' _).2
      ⟨t, hlt', logByteBounded img log t a ht, ht⟩)).elim
  omega

/-- A latest timestamp is readable at any pre-view. -/
theorem latestReadable (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int)
    (t : Nat) :
    max vpre (coh ws a) ≤ log.length → latest img log a t → readable img log ws vpre a t := by
  rintro hle ⟨hs, hn⟩
  exact ⟨hs, fun hw => hn (writesInMonoHi log a t _ _ hle hw)⟩

/-- The COMPUTED latest timestamp: the index (+1) of the last message writing
`a`, or 0 if none does. -/
def latestTsAcc (log : List Wmsg) (a : Int) : Nat × Nat :=
  log.foldl (fun p m => (p.1 + 1, if msgWritesb m a then p.1 + 1 else p.2)) (0, 0)

def latestTs (log : List Wmsg) (a : Int) : Nat := (latestTsAcc log a).2

/-- Snoc induction (Rocq's `rev_ind`). -/
theorem snocInd {α : Type _} {P : List α → Prop} (h0 : P [])
    (hs : ∀ l x, P l → P (l ++ [x])) (l : List α) : P l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons x l ih => rw [List.reverse_cons]; exact hs _ _ ih

private theorem latestTsAccFstGen (a : Int) (log : List Wmsg) (p : Nat × Nat) :
    (log.foldl (fun p m => (p.1 + 1, if msgWritesb m a then p.1 + 1 else p.2)) p).1
      = p.1 + log.length := by
  induction log generalizing p with
  | nil => simp
  | cons m l ih => simp only [List.foldl_cons, ih, List.length_cons]; omega

theorem latestTsAccFst (log : List Wmsg) (a : Int) : (latestTsAcc log a).1 = log.length := by
  unfold latestTsAcc; rw [latestTsAccFstGen]; simp

theorem latestTsNil (a : Int) : latestTs [] a = 0 := rfl

theorem latestTsApp (log : List Wmsg) (m : Wmsg) (a : Int) :
    latestTs (log ++ [m]) a = (if msgWritesb m a then log.length + 1 else latestTs log a) := by
  have h := latestTsAccFst log a
  unfold latestTs latestTsAcc at *
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [h]

theorem latestTsLe (log : List Wmsg) (a : Int) : latestTs log a ≤ log.length := by
  induction log using snocInd with
  | h0 => exact Nat.le_refl _
  | hs l m ih =>
    rw [latestTsApp, List.length_append]
    split <;> simp <;> omega

/-- Nothing above `latestTs` writes `a`. -/
theorem latestTsTop (log : List Wmsg) (a : Int) : ¬ writesIn log a (latestTs log a) log.length := by
  induction log using snocInd with
  | h0 => rintro ⟨t, h1, h2, _⟩; simp [latestTsNil] at h1 h2; omega
  | hs l m ih =>
    rw [latestTsApp, List.length_append]
    cases hm : msgWritesb m a with
    | true => rintro ⟨t, h1, h2, _⟩; simp at h1 h2; omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_singleton]
      rintro ⟨t, hlo, hhi, mm, hmm, hs⟩
      by_cases hle : t ≤ l.length
      · exact ih ⟨t, hlo, hle, mm, by rwa [lookup_app_l (by omega)] at hmm, hs⟩
      · have ht : t - 1 = l.length := by omega
        rw [ht, list_lookup_middle rfl] at hmm
        injection hmm with hmm
        subst hmm
        rw [(msgWritesbFalse _ a).1 hm] at hs
        cases hs

theorem latestTsLatest (img : Image) (log : List Wmsg) (a : Int) :
    (logByte img log (latestTs log a) a).isSome → latest img log a (latestTs log a) :=
  fun h => ⟨h, latestTsTop log a⟩

/-- `latestTs` is either 0 or the index of a message that writes `a`. -/
theorem latestTsWrites (log : List Wmsg) (a : Int) :
    latestTs log a = 0 ∨
    ∃ i m, latestTs log a = i + 1 ∧ log[i]? = some m ∧ (msgByte m a).isSome := by
  induction log using snocInd with
  | h0 => exact .inl rfl
  | hs l m ih =>
    rw [latestTsApp]
    cases hm : msgWritesb m a with
    | true =>
      refine .inr ⟨l.length, m, rfl, list_lookup_middle rfl, (msgWritesbTrue m a).1 hm⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases ih with hz | ⟨i, m', hr, hlk, hs⟩
      · exact .inl hz
      · exact .inr ⟨i, m', hr, lookup_app_l_Some hlk, hs⟩

/-- If ANY timestamp holds a value for `a`, so does `latestTs`. -/
theorem latestTsSome (img : Image) (log : List Wmsg) (a : Int) (t : Nat) :
    (logByte img log t a).isSome → (logByte img log (latestTs log a) a).isSome := by
  intro ht
  rcases latestTsWrites log a with hz | ⟨i, m, hr, hlk, hs⟩
  · rw [hz, logByte0]
    cases t with
    | zero => exact ht
    | succ i =>
      exfalso
      apply latestTsTop log a
      rw [hz]
      exact (writesInLogByte img log a 0 _).2
        ⟨i + 1, by omega, logByteBounded img log (i + 1) a ht, ht⟩
  · rw [hr, logByteS, hlk]; exact hs

/-- Hence `latestTs` IS the latest timestamp whenever one exists. -/
theorem latestTsEq (img : Image) (log : List Wmsg) (a : Int) (t : Nat) :
    latest img log a t → latestTs log a = t := fun hl =>
  latestUnique img log a _ _ ⟨latestTsSome img log a t hl.1, latestTsTop log a⟩ hl

/-- SC DEGENERACY: a floor covering the whole log collapses readability to
`latest`. -/
theorem readableAllSeen (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int)
    (t : Nat) : log.length ≤ vpre → readable img log ws vpre a t → latest img log a t := by
  rintro hall ⟨hs, hn⟩
  exact ⟨hs, fun hw => hn (writesInMonoHi log a t _ _ (by omega) hw)⟩

/-! ## The step functions -/

/-- Loads: pre-view `vrNew ⊔ (aq ? vRel)`. -/
def loadVpre (ws : Wstate) (aq : Bool) : Nat :=
  max ws.wVrNew (if aq then ws.wVRel else 0)

/-- PARM's full read `view_pre`: the address-dependency view first. -/
def loadVpreD (ws : Wstate) (aq : Bool) (vaddr : Nat) : Nat :=
  max vaddr (loadVpre ws aq)

theorem loadVpreD0 (ws : Wstate) (aq : Bool) : loadVpreD ws aq 0 = loadVpre ws aq :=
  Nat.zero_max _

theorem loadVpreLoadVpreD (ws : Wstate) (aq : Bool) (vaddr : Nat) :
    loadVpre ws aq ≤ loadVpreD ws aq vaddr := Nat.le_max_right _ _

/-- THE FORWARD BANK, wired into the read view (design doc, Decision 3; the
D-5 audit's correction is recorded in the Rocq header of this definition). -/
def fwdView (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) : Nat :=
  if aq then t
  else match get? ws.wFwd a with
    | some (tf, vf) => if t = tf then vf else t
    | none => t

theorem fwdViewAq (ws : Wstate) (a : Int) (t : Nat) : fwdView ws true a t = t := rfl

theorem fwdViewMiss (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    get? ws.wFwd a = none → fwdView ws aq a t = t := by
  intro h; cases aq <;> simp [fwdView, h]

theorem fwdViewEmpty (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    ws.wFwd = ∅ → fwdView ws aq a t = t := by
  intro h; apply fwdViewMiss; rw [h]; rfl

theorem fwdViewHit (ws : Wstate) (a : Int) (t tf vf : Nat) :
    get? ws.wFwd a = some (tf, vf) → t = tf → fwdView ws false a t = vf := by
  rintro hf rfl; simp [fwdView, hf]

/-- THE PER-BYTE READ UPDATE at an explicit pre-view.  `vpost` is the
FORWARDED view; the coherence floor takes the raw timestamp.  A plain load
CLEARS the reservation (A2-s3) and BANKS its forwarded timestamp (W-TV). -/
def loadPostAt (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) : Wstate :=
  let vpost := max vpre (fwdView ws aq a t)
  { wCoh := insert ws.wCoh a (max (coh ws a) (max vpost t))
    wVrOld := max ws.wVrOld vpost
    wVwOld := ws.wVwOld
    wVrNew := if aq then max ws.wVrNew vpost else ws.wVrNew
    wVwNew := if aq then max ws.wVwNew vpost else ws.wVwNew
    wVRel := ws.wVRel
    wFwd := ws.wFwd
    wPub := ws.wPub
    wRelp := ws.wRelp
    wRegv := ws.wRegv
    wVcap := ws.wVcap
    wLdv := max ws.wLdv vpost
    wRes := none
    wTbank := max ws.wTbank (fwdView ws aq a t) }

def loadPost (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) : Wstate :=
  loadPostAt ws aq (loadVpre ws aq) a t

/-- THE PER-BYTE WRITE UPDATE, dependency-carrying.  `vf` is DEAD since D-7r:
the forward bank's view column is `0` (PARM's dependency-free `FwdItem`); see
the Rocq comment for the re-upgrade coupling.  A store clears the reservation
(clear-on-own-store); a `wRelp`/`rl` store publishes. -/
def storePostD (ws : Wstate) (rl : Bool) (vf : Nat) (a : Int) (t : Nat) : Wstate :=
  { wCoh := insert ws.wCoh a (max (coh ws a) t)
    wVrOld := ws.wVrOld
    wVwOld := max ws.wVwOld t
    wVrNew := ws.wVrNew
    wVwNew := ws.wVwNew
    wVRel := if rl then max ws.wVRel t else ws.wVRel
    wFwd := insert ws.wFwd a (t, 0)
    wPub := if (ws.wRelp || rl) then max ws.wPub t else ws.wPub
    wRelp := false
    wRegv := ws.wRegv
    wVcap := ws.wVcap
    wLdv := ws.wLdv
    wRes := none
    wTbank := ws.wTbank }

def storePost (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) : Wstate :=
  { wCoh := insert ws.wCoh a (max (coh ws a) t)
    wVrOld := ws.wVrOld
    wVwOld := max ws.wVwOld t
    wVrNew := ws.wVrNew
    wVwNew := ws.wVwNew
    wVRel := if rl then max ws.wVRel t else ws.wVRel
    wFwd := insert ws.wFwd a (t, 0)
    wPub := if (ws.wRelp || rl) then max ws.wPub t else ws.wPub
    wRelp := false
    wRegv := ws.wRegv
    wVcap := ws.wVcap
    wLdv := ws.wLdv
    wRes := none
    wTbank := ws.wTbank }

/-- THE D-7r COLLAPSE: `vf` feeds nothing. -/
theorem storePostDVf (ws : Wstate) (rl : Bool) (vf : Nat) (a : Int) (t : Nat) :
    storePostD ws rl vf a t = storePost ws rl a t := rfl

theorem storePostD0 (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    storePostD ws rl 0 a t = storePost ws rl a t := storePostDVf ws rl 0 a t

/-- FENCE pred,succ (`pr`/`pw` ∈ pred, `sr`/`sw` ∈ succ).  A `pw ∧ sw` fence
arms `wRelp`; a non-trivial fence clears the reservation; the all-false fence
is the identity (`fence.i`'s inert rendering). -/
def fencePost (ws : Wstate) (pr pw sr sw : Bool) : Wstate :=
  let v1 := max (if pr then ws.wVrOld else 0) (if pw then ws.wVwOld else 0)
  { wCoh := ws.wCoh
    wVrOld := ws.wVrOld
    wVwOld := ws.wVwOld
    wVrNew := if sr then max ws.wVrNew v1 else ws.wVrNew
    wVwNew := if sw then max ws.wVwNew v1 else ws.wVwNew
    wVRel := ws.wVRel
    wFwd := ws.wFwd
    wPub := ws.wPub
    wRelp := if (pw && sw) then true else ws.wRelp
    wRegv := ws.wRegv
    wVcap := ws.wVcap
    wLdv := ws.wLdv
    wRes := if (pr || pw || sr || sw) then none else ws.wRes
    wTbank := ws.wTbank }

theorem fencePostId (ws : Wstate) : fencePost ws false false false false = ws := by
  cases ws; rfl

/-! ## The three DEPENDENCY-ONLY label effects -/

/-- `LRegW rd srcs`: PARM's `step_assign` — an ASSIGNMENT, not a join. -/
def regwPost (ws : Wstate) (rd : Nat) (v : Nat) : Wstate :=
  { ws with wRegv := insert ws.wRegv rd v }

/-- `LCtrl srcs`: PARM's `Local.control` — `vcap ⊔= ctrl`. -/
def ctrlPost (ws : Wstate) (v : Nat) : Wstate :=
  { ws with wVcap := max v ws.wVcap }

theorem ctrlPostCoh (ws : Wstate) (v : Nat) (a : Int) : coh (ctrlPost ws v) a = coh ws a := rfl
theorem ctrlPostVrOld (ws : Wstate) (v : Nat) : (ctrlPost ws v).wVrOld = ws.wVrOld := rfl
theorem ctrlPostVwOld (ws : Wstate) (v : Nat) : (ctrlPost ws v).wVwOld = ws.wVwOld := rfl
theorem ctrlPostVrNew (ws : Wstate) (v : Nat) : (ctrlPost ws v).wVrNew = ws.wVrNew := rfl
theorem ctrlPostVwNew (ws : Wstate) (v : Nat) : (ctrlPost ws v).wVwNew = ws.wVwNew := rfl
theorem ctrlPostVRel (ws : Wstate) (v : Nat) : (ctrlPost ws v).wVRel = ws.wVRel := rfl
theorem ctrlPostFwd (ws : Wstate) (v : Nat) : (ctrlPost ws v).wFwd = ws.wFwd := rfl
theorem ctrlPostPub (ws : Wstate) (v : Nat) : (ctrlPost ws v).wPub = ws.wPub := rfl
theorem ctrlPostRelp (ws : Wstate) (v : Nat) : (ctrlPost ws v).wRelp = ws.wRelp := rfl
theorem ctrlPostRegv (ws : Wstate) (v : Nat) (r : Nat) : regv (ctrlPost ws v) r = regv ws r := rfl
theorem ctrlPostLdv (ws : Wstate) (v : Nat) : (ctrlPost ws v).wLdv = ws.wLdv := rfl
theorem ctrlPostRes (ws : Wstate) (v : Nat) : (ctrlPost ws v).wRes = ws.wRes := rfl
theorem ctrlPostTbank (ws : Wstate) (v : Nat) : (ctrlPost ws v).wTbank = ws.wTbank := rfl
theorem ctrlPostVcap (ws : Wstate) (v : Nat) : (ctrlPost ws v).wVcap = max v ws.wVcap := rfl

/-- `LInstr`: instruction start — resets the load-result bank, the reservation
(its GC point) and the translation bank. -/
def instrPost (ws : Wstate) : Wstate :=
  { ws with wLdv := 0, wRes := none, wTbank := 0 }

theorem regvRegwPostEq (ws : Wstate) (rd v : Nat) : regv (regwPost ws rd v) rd = v := by
  simp [regv, regwPost, lookupInsert]

theorem regvRegwPostNe (ws : Wstate) (rd v r : Nat) :
    r ≠ rd → regv (regwPost ws rd v) r = regv ws r := by
  intro h; simp [regv, regwPost, lookupInsertNe (Ne.symm h)]

/-- Multi-byte accesses are per-byte folds, at the pre-view computed ONCE. -/
def loadPostBytesD (ws : Wstate) (aq : Bool) (vaddr : Nat) (ats : List (Int × Nat)) : Wstate :=
  ats.foldl (fun w at_ => loadPostAt w aq (loadVpreD ws aq vaddr) at_.1 at_.2) ws

def loadPostBytes (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) : Wstate :=
  ats.foldl (fun w at_ => loadPostAt w aq (loadVpre ws aq) at_.1 at_.2) ws

theorem loadPostBytesD0 (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    loadPostBytesD ws aq 0 ats = loadPostBytes ws aq ats := by
  simp only [loadPostBytesD, loadPostBytes, loadVpreD0]

def storePostBytesD (ws : Wstate) (rl : Bool) (vf : Nat) (as_ : List Int) (t : Nat) : Wstate :=
  as_.foldl (fun w a => storePostD w rl vf a t) ws

def storePostBytes (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) : Wstate :=
  as_.foldl (fun w a => storePost w rl a t) ws

theorem storePostBytesDVf (ws : Wstate) (rl : Bool) (vf : Nat) (as_ : List Int) (t : Nat) :
    storePostBytesD ws rl vf as_ t = storePostBytes ws rl as_ t := rfl

theorem storePostBytesD0 (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) :
    storePostBytesD ws rl 0 as_ t = storePostBytes ws rl as_ t := storePostBytesDVf ws rl 0 as_ t

/-- The contiguous instances: byte `j` of an access based at `base` lives at
`base + j`. -/
def loadRunAts (base : Int) (ts : List Nat) : List (Int × Nat) :=
  List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts

/-- THE RUN-LEVEL READ: one `ctrlPost` per access (PARM's `vcap ⊔= view(addr)`),
joined with the W-TV translation bank of the ENTRY state. -/
def loadPostRunD (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    Wstate :=
  ctrlPost (loadPostBytesD ws aq vaddr (loadRunAts base ts)) (max vaddr ws.wTbank)

def loadPostRun (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) : Wstate :=
  ctrlPost
    (loadPostBytes ws aq
      (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts))
    ws.wTbank

def storeRunAs (base : Int) (n : Nat) : List Int :=
  (List.range' 0 n).map (fun j : Nat => base + (j : Int))

def storePostRunD (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat) :
    Wstate :=
  ctrlPost (storePostBytesD ws rl (max vaddr vdata) (storeRunAs base n) t) (max vaddr ws.wTbank)

def storePostRun (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) : Wstate :=
  ctrlPost (storePostBytes ws rl ((List.range' 0 n).map (fun j : Nat => base + (j : Int))) t)
    ws.wTbank

theorem ctrlPost0 (ws : Wstate) : ctrlPost ws 0 = ws := by
  cases ws; simp [ctrlPost]

theorem loadPostRunD0 (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    loadPostRunD ws aq 0 base ts = loadPostRun ws aq base ts := by
  simp only [loadPostRunD, loadPostRun, loadPostBytesD0, Nat.zero_max, loadRunAts]

theorem storePostRunD0 (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    storePostRunD ws rl 0 0 base n t = storePostRun ws rl base n t := by
  simp only [storePostRunD, storePostRun, storePostBytesDVf, Nat.zero_max, storeRunAs]

/-- The bank equations: the consumed bank is below the produced control view. -/
theorem loadPostRunDTbankVcap (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int)
    (ts : List Nat) : ws.wTbank ≤ (loadPostRunD ws aq vaddr base ts).wVcap := by
  simp only [loadPostRunD, ctrlPostVcap]; omega

theorem storePostRunDTbankVcap (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int)
    (n t : Nat) : ws.wTbank ≤ (storePostRunD ws rl vaddr vdata base n t).wVcap := by
  simp only [storePostRunD, ctrlPostVcap]; omega

/-- THE EXCLUSIVE-BANK VIEW (PARM's `Exbank.view`, deviation D-2), computed from
a zeroed `wLdv`. -/
def wsLdv0 (ws : Wstate) : Wstate := instrPost ws

def ldvOf (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) : Nat :=
  (loadPostRunD (wsLdv0 ws) aq vaddr base ts).wLdv

/-! ## The exclusive read's post-state (RMW split S2) -/

/-- The reservation update (supersedes). -/
def wsResSet (ws : Wstate) (r : Option Wresv) : Wstate := { ws with wRes := r }

theorem wsResSetCoh (ws : Wstate) (r : Option Wresv) (a : Int) : coh (wsResSet ws r) a = coh ws a := rfl
theorem wsResSetVrOld (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wVrOld = ws.wVrOld := rfl
theorem wsResSetVwOld (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wVwOld = ws.wVwOld := rfl
theorem wsResSetVrNew (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wVrNew = ws.wVrNew := rfl
theorem wsResSetVwNew (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wVwNew = ws.wVwNew := rfl
theorem wsResSetVRel (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wVRel = ws.wVRel := rfl
theorem wsResSetFwd (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wFwd = ws.wFwd := rfl
theorem wsResSetPub (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wPub = ws.wPub := rfl
theorem wsResSetRelp (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wRelp = ws.wRelp := rfl
theorem wsResSetRegv (ws : Wstate) (r : Option Wresv) (x : Nat) : regv (wsResSet ws r) x = regv ws x := rfl
theorem wsResSetVcap (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wVcap = ws.wVcap := rfl
theorem wsResSetLdv (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wLdv = ws.wLdv := rfl
theorem wsResSetTbank (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wTbank = ws.wTbank := rfl
theorem wsResSetRes (ws : Wstate) (r : Option Wresv) : (wsResSet ws r).wRes = r := rfl

theorem wsResSetNone (ws : Wstate) : wsResSet ws ws.wRes = ws := rfl

/-- THE EXCLUSIVE READ, at the run level (D-2r: the byte fold runs at the PLAIN
pre-view; `vaddr` survives only in the control view; see the Rocq comment for
the re-upgrade coupling). -/
def exloadPostRunD (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    Wstate :=
  wsResSet
    (ctrlPost
      (loadPostBytes ws aq
        (List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts))
      (max vaddr ws.wTbank))
    (some ⟨base, ts, ldvOf ws aq 0 base ts⟩)

/-- THE D-2r COLLAPSE. -/
theorem exloadPostRunDCtrl (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    exloadPostRunD ws aq vaddr base ts = ctrlPost (exloadPostRunD ws aq 0 base ts) vaddr := by
  simp only [exloadPostRunD, wsResSet, ctrlPost]
  congr 1
  omega

theorem exloadPostRunD0 (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    exloadPostRunD ws aq 0 base ts
    = wsResSet (loadPostRun ws aq base ts) (some ⟨base, ts, ldvOf ws aq 0 base ts⟩) := by
  simp only [exloadPostRunD, loadPostRun, Nat.zero_max]

theorem exloadPostRunDRes (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    (exloadPostRunD ws aq vaddr base ts).wRes = some ⟨base, ts, ldvOf ws aq 0 base ts⟩ := rfl

/-! ### What each access does to `wRes`, as an equation -/

theorem wsInitRes : wsInit.wRes = none := rfl

theorem loadPostBytesDRes (ws : Wstate) (aq : Bool) (vaddr : Nat) (ats : List (Int × Nat)) :
    ats ≠ [] → (loadPostBytesD ws aq vaddr ats).wRes = none := by
  induction ats using snocInd with
  | h0 => intro h; exact (h rfl).elim
  | hs l x _ => intro _; simp only [loadPostBytesD, List.foldl_append, List.foldl_cons,
      List.foldl_nil]; rfl

theorem storePostBytesDRes (ws : Wstate) (rl : Bool) (vf : Nat) (as_ : List Int) (t : Nat) :
    as_ ≠ [] → (storePostBytesD ws rl vf as_ t).wRes = none := by
  induction as_ using snocInd with
  | h0 => intro h; exact (h rfl).elim
  | hs l x _ => intro _; simp only [storePostBytesD, List.foldl_append, List.foldl_cons,
      List.foldl_nil]; rfl

theorem loadPostRunDRes (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    (loadPostRunD ws aq vaddr base ts).wRes
    = match ts with | [] => ws.wRes | _ :: _ => none := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [loadPostRunD, ctrlPostRes]
    apply loadPostBytesDRes
    simp [loadRunAts, List.range'_succ]

theorem storePostRunDRes (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat) :
    (storePostRunD ws rl vaddr vdata base n t).wRes
    = match n with | 0 => ws.wRes | _ + 1 => none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [storePostRunD, ctrlPostRes]
    apply storePostBytesDRes
    simp [storeRunAs, List.range'_succ]

theorem fencePostRes (ws : Wstate) (pr pw sr sw : Bool) :
    (fencePost ws pr pw sr sw).wRes = if (pr || pw || sr || sw) then none else ws.wRes := rfl

/-- THE RESERVATION'S BANKED VIEW as a total function of the state. -/
def resView (ws : Wstate) : Nat :=
  match ws.wRes with
  | some R => R.rvView
  | none => 0

theorem resViewSome (ws : Wstate) (R : Wresv) : ws.wRes = some R → resView ws = R.rvView := by
  intro h; simp [resView, h]

/-! ## Monotonicity: every step function only raises views -/

/-- `wsLe`: the monotone components (`wRelp`, `wLdv`, `wRegv`, `wRes`,
`wTbank` are NOT monotone, see the Rocq D2 FINDING note). -/
def wsLe (w1 w2 : Wstate) : Prop :=
  (∀ a, coh w1 a ≤ coh w2 a) ∧
  w1.wVrOld ≤ w2.wVrOld ∧ w1.wVwOld ≤ w2.wVwOld ∧
  w1.wVrNew ≤ w2.wVrNew ∧ w1.wVwNew ≤ w2.wVwNew ∧
  w1.wVRel ≤ w2.wVRel ∧ w1.wPub ≤ w2.wPub ∧
  w1.wVcap ≤ w2.wVcap

theorem wsLeRefl (w : Wstate) : wsLe w w :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
   Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem wsLeTrans {w1 w2 w3 : Wstate} : wsLe w1 w2 → wsLe w2 w3 → wsLe w1 w3 := by
  rintro ⟨c1, h1, h2, h3, h4, h5, h6, h7⟩ ⟨c2, g1, g2, g3, g4, g5, g6, g7⟩
  exact ⟨fun a => Nat.le_trans (c1 a) (c2 a), by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩

instance : Trans wsLe wsLe wsLe := ⟨wsLeTrans⟩

theorem wsLeCoh (w1 w2 : Wstate) (a : Int) : wsLe w1 w2 → coh w1 a ≤ coh w2 a := fun h => h.1 a
theorem wsLeVrOld (w1 w2 : Wstate) : wsLe w1 w2 → w1.wVrOld ≤ w2.wVrOld := fun h => h.2.1
theorem wsLeVwOld (w1 w2 : Wstate) : wsLe w1 w2 → w1.wVwOld ≤ w2.wVwOld := fun h => h.2.2.1
theorem wsLeVrNew (w1 w2 : Wstate) : wsLe w1 w2 → w1.wVrNew ≤ w2.wVrNew := fun h => h.2.2.2.1
theorem wsLeVwNew (w1 w2 : Wstate) : wsLe w1 w2 → w1.wVwNew ≤ w2.wVwNew :=
  fun h => h.2.2.2.2.1
theorem wsLeVRel (w1 w2 : Wstate) : wsLe w1 w2 → w1.wVRel ≤ w2.wVRel := fun h => h.2.2.2.2.2.1
theorem wsLeVcap (w1 w2 : Wstate) : wsLe w1 w2 → w1.wVcap ≤ w2.wVcap :=
  fun h => h.2.2.2.2.2.2.2
theorem wsLePub (w1 w2 : Wstate) : wsLe w1 w2 → w1.wPub ≤ w2.wPub := fun h => h.2.2.2.2.2.2.1

/-- `ctrlPost` only raises the control view. -/
theorem ctrlPostLe (ws : Wstate) (v : Nat) : wsLe ws (ctrlPost ws v) :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
   Nat.le_refl _, Nat.le_refl _, Nat.le_max_right _ _⟩

/-- `wsLeNc`: `wsLe` minus the `wVcap` conjunct (the erasure's relation). -/
def wsLeNc (w1 w2 : Wstate) : Prop :=
  (∀ a, coh w1 a ≤ coh w2 a) ∧
  w1.wVrOld ≤ w2.wVrOld ∧ w1.wVwOld ≤ w2.wVwOld ∧
  w1.wVrNew ≤ w2.wVrNew ∧ w1.wVwNew ≤ w2.wVwNew ∧
  w1.wVRel ≤ w2.wVRel ∧ w1.wPub ≤ w2.wPub

theorem wsLeNcRefl (w : Wstate) : wsLeNc w w :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
   Nat.le_refl _, Nat.le_refl _⟩

theorem wsLeNcTrans {w1 w2 w3 : Wstate} : wsLeNc w1 w2 → wsLeNc w2 w3 → wsLeNc w1 w3 := by
  rintro ⟨c1, h1, h2, h3, h4, h5, h6⟩ ⟨c2, g1, g2, g3, g4, g5, g6⟩
  exact ⟨fun a => Nat.le_trans (c1 a) (c2 a), by omega, by omega, by omega, by omega, by omega,
    by omega⟩

instance : Trans wsLeNc wsLeNc wsLeNc := ⟨wsLeNcTrans⟩

theorem wsLeWsLeNc (w1 w2 : Wstate) : wsLe w1 w2 → wsLeNc w1 w2 := by
  rintro ⟨c, h1, h2, h3, h4, h5, h6, _⟩; exact ⟨c, h1, h2, h3, h4, h5, h6⟩

theorem wsLeNcCoh (w1 w2 : Wstate) (a : Int) : wsLeNc w1 w2 → coh w1 a ≤ coh w2 a :=
  fun h => h.1 a
theorem wsLeNcVrOld (w1 w2 : Wstate) : wsLeNc w1 w2 → w1.wVrOld ≤ w2.wVrOld := fun h => h.2.1
theorem wsLeNcVwOld (w1 w2 : Wstate) : wsLeNc w1 w2 → w1.wVwOld ≤ w2.wVwOld := fun h => h.2.2.1
theorem wsLeNcVrNew (w1 w2 : Wstate) : wsLeNc w1 w2 → w1.wVrNew ≤ w2.wVrNew :=
  fun h => h.2.2.2.1
theorem wsLeNcVwNew (w1 w2 : Wstate) : wsLeNc w1 w2 → w1.wVwNew ≤ w2.wVwNew :=
  fun h => h.2.2.2.2.1
theorem wsLeNcVRel (w1 w2 : Wstate) : wsLeNc w1 w2 → w1.wVRel ≤ w2.wVRel :=
  fun h => h.2.2.2.2.2.1
theorem wsLeNcPub (w1 w2 : Wstate) : wsLeNc w1 w2 → w1.wPub ≤ w2.wPub :=
  fun h => h.2.2.2.2.2.2

theorem ctrlPostMono (w1 w2 : Wstate) (v1 v2 : Nat) :
    wsLe w1 w2 → v1 ≤ v2 → wsLe (ctrlPost w1 v1) (ctrlPost w2 v2) := by
  rintro ⟨c, h1, h2, h3, h4, h5, h6, h7⟩ hv
  exact ⟨c, h1, h2, h3, h4, h5, h6, by simp only [ctrlPostVcap]; omega⟩

/-- The coherence floor of a state whose `wCoh` is an insert. -/
private theorem cohInsertLe (w w' : Wstate) (a : Int) (n : Nat)
    (hw : w'.wCoh = insert w.wCoh a n) (hn : coh w a ≤ n) : ∀ a', coh w a' ≤ coh w' a' := by
  intro a'
  simp only [coh, hw]
  by_cases h : a = a'
  · subst h; rw [lookupInsert]; exact hn
  · rw [lookupInsertNe h]; exact Nat.le_refl _

theorem loadPostAtLe (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    wsLe ws (loadPostAt ws aq vpre a t) := by
  refine ⟨cohInsertLe _ _ a _ rfl (Nat.le_max_left _ _), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [loadPostAt] <;> (try split) <;> omega

theorem loadPostLe (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) : wsLe ws (loadPost ws aq a t) :=
  loadPostAtLe _ _ _ _ _

theorem storePostLe (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    wsLe ws (storePost ws rl a t) := by
  refine ⟨cohInsertLe _ _ a _ rfl (Nat.le_max_left _ _), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [storePost] <;> (try split) <;> omega

theorem fencePostLe (ws : Wstate) (pr pw sr sw : Bool) : wsLe ws (fencePost ws pr pw sr sw) := by
  refine ⟨fun _ => Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [fencePost] <;> (try split) <;> omega

/-- ... and so do the multi-byte folds. -/
theorem loadPostFoldLe (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    wsLe ws (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) := by
  induction ats generalizing ws with
  | nil => exact wsLeRefl _
  | cons p l ih => exact wsLeTrans (loadPostAtLe _ _ _ _ _) (ih _)

theorem loadPostBytesLe (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    wsLe ws (loadPostBytes ws aq ats) := loadPostFoldLe _ _ _ _

theorem loadPostRunLe (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    wsLe ws (loadPostRun ws aq base ts) :=
  wsLeTrans (loadPostBytesLe _ _ _) (ctrlPostLe _ _)

theorem storePostFoldLe (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    wsLe ws (as_.foldl (fun w a => storePost w rl a t) ws) := by
  induction as_ generalizing ws with
  | nil => exact wsLeRefl _
  | cons a l ih => exact wsLeTrans (storePostLe _ _ _ _) (ih _)

theorem storePostBytesLe (ws : Wstate) (rl : Bool) (as_ : List Int) (t : Nat) :
    wsLe ws (storePostBytes ws rl as_ t) := storePostFoldLe _ _ _ _

theorem storePostRunLe (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    wsLe ws (storePostRun ws rl base n t) :=
  wsLeTrans (storePostBytesLe _ _ _ _) (ctrlPostLe _ _)

/-! ## The individual view facts the litmus proofs consume -/

theorem loadVpreVrNew (ws : Wstate) (aq : Bool) : ws.wVrNew ≤ loadVpre ws aq :=
  Nat.le_max_left _ _

theorem loadPostAtVrOld (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    fwdView ws aq a t ≤ (loadPostAt ws aq vpre a t).wVrOld := by
  simp only [loadPostAt]; omega

theorem loadPostVrOld (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    fwdView ws aq a t ≤ (loadPost ws aq a t).wVrOld := loadPostAtVrOld _ _ _ _ _

theorem loadPostAtVrOldNofwd (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    ws.wFwd = ∅ → t ≤ (loadPostAt ws aq vpre a t).wVrOld := by
  intro h
  have := loadPostAtVrOld ws aq vpre a t
  rwa [fwdViewEmpty ws aq a t h] at this

theorem loadPostVrOldNofwd (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    ws.wFwd = ∅ → t ≤ (loadPost ws aq a t).wVrOld := loadPostAtVrOldNofwd _ _ _ _ _

/-- No step function but `storePost` changes the bank. -/
theorem loadPostAtFwd (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    (loadPostAt ws aq vpre a t).wFwd = ws.wFwd := rfl

theorem loadPostFwd (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) :
    (loadPost ws aq a t).wFwd = ws.wFwd := rfl

theorem fencePostFwd (ws : Wstate) (pr pw sr sw : Bool) :
    (fencePost ws pr pw sr sw).wFwd = ws.wFwd := rfl

theorem loadPostFoldFwd (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wFwd = ws.wFwd := by
  induction ats generalizing ws with
  | nil => rfl
  | cons p l ih => exact (ih _).trans (loadPostAtFwd _ _ _ _ _)

theorem loadPostBytesFwd (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) :
    (loadPostBytes ws aq ats).wFwd = ws.wFwd := loadPostFoldFwd _ _ _ _

theorem loadPostRunFwd (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) :
    (loadPostRun ws aq base ts).wFwd = ws.wFwd := loadPostBytesFwd _ _ _

/-- THE MULTI-BYTE READ GAIN. -/
theorem loadPostFoldVrOld (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate)
    (a : Int) (t : Nat) :
    (a, t) ∈ ats → get? ws.wFwd a = none →
    t ≤ (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrOld := by
  induction ats generalizing ws with
  | nil => intro h; cases h
  | cons p l ih =>
    intro hin hfwd
    rcases List.mem_cons.1 hin with rfl | hin
    · refine Nat.le_trans ?_ (wsLeVrOld _ _ (loadPostFoldLe aq vpre l (loadPostAt ws aq vpre a t)))
      simp only [loadPostAt, fwdViewMiss ws aq a t hfwd]; omega
    · exact ih _ hin (by rw [loadPostAtFwd]; exact hfwd)

theorem loadPostBytesVrOld (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) (a : Int) (t : Nat) :
    (a, t) ∈ ats → get? ws.wFwd a = none → t ≤ (loadPostBytes ws aq ats).wVrOld :=
  loadPostFoldVrOld _ _ _ _ _ _

/-- The zipped byte run contains byte `j` of the access. -/
theorem memLoadRunAts (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t →
    (base + (j : Int), t) ∈
      List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' 0 ts.length) ts := by
  intro ht
  apply elem_of_list_lookup_2 (i := j)
  rw [lookup_zip_with, lookup_seq_lt (lookup_lt_Some ht), ht]
  simp

theorem loadPostRunVrOld (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (j : Nat) :
    j < ts.length → get? ws.wFwd (base + (j : Int)) = none →
    ts[j]! ≤ (loadPostRun ws aq base ts).wVrOld := by
  intro hj hfwd
  obtain ⟨t, ht⟩ : ∃ t, ts[j]? = some t := ⟨ts[j], List.getElem?_eq_getElem hj⟩
  rw [list_lookup_total_correct ht]
  exact loadPostBytesVrOld ws aq _ (base + (j : Int)) t (memLoadRunAts base ts j t ht) hfwd

theorem loadPostAtCoh (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    t ≤ coh (loadPostAt ws aq vpre a t) a := by
  simp only [loadPostAt, coh, lookupInsert, Option.getD_some]; omega

theorem loadPostCoh (ws : Wstate) (aq : Bool) (a : Int) (t : Nat) : t ≤ coh (loadPost ws aq a t) a :=
  loadPostAtCoh _ _ _ _ _

/-- An ACQUIRE load raises the read AND write pre-view floors. -/
theorem loadPostAtVrNewAq (ws : Wstate) (vpre : Nat) (a : Int) (t : Nat) :
    t ≤ (loadPostAt ws true vpre a t).wVrNew := by
  simp only [loadPostAt, fwdViewAq, ↓reduceIte]; omega

theorem loadPostVrNewAq (ws : Wstate) (a : Int) (t : Nat) : t ≤ (loadPost ws true a t).wVrNew :=
  loadPostAtVrNewAq _ _ _ _

theorem loadPostAtVwNewAq (ws : Wstate) (vpre : Nat) (a : Int) (t : Nat) :
    t ≤ (loadPostAt ws true vpre a t).wVwNew := by
  simp only [loadPostAt, fwdViewAq, ↓reduceIte]; omega

theorem storePostCoh (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) : t ≤ coh (storePost ws rl a t) a := by
  simp only [storePost, coh, lookupInsert, Option.getD_some]; omega

theorem storePostVwOld (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    t ≤ (storePost ws rl a t).wVwOld := by
  simp only [storePost]; omega

theorem storePostVRelRl (ws : Wstate) (a : Int) (t : Nat) : t ≤ (storePost ws true a t).wVRel := by
  simp only [storePost, ↓reduceIte]; omega

/-- A succ-R fence with pred-R delivers the past loads' floor to future loads. -/
theorem fencePostVrNewR (ws : Wstate) (pw sw : Bool) :
    ws.wVrOld ≤ (fencePost ws true pw true sw).wVrNew := by
  simp only [fencePost, ↓reduceIte]; omega

theorem fencePostVrNewW (ws : Wstate) (pr sw : Bool) :
    ws.wVwOld ≤ (fencePost ws pr true true sw).wVrNew := by
  simp only [fencePost, ↓reduceIte]; omega

theorem fencePostVwNewR (ws : Wstate) (pw sr : Bool) :
    ws.wVrOld ≤ (fencePost ws true pw sr true).wVwNew := by
  simp only [fencePost, ↓reduceIte]; omega

theorem fencePostVwNewW (ws : Wstate) (pr sr : Bool) :
    ws.wVwOld ≤ (fencePost ws pr true sr true).wVwNew := by
  simp only [fencePost, ↓reduceIte]; omega

/-! ## Own-write read-back -/

/-- THE COLLAPSE LEMMA — the pure heart of the M2 load rule. -/
theorem readableLatestPin (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int)
    (t t' : Nat) :
    latest img log a t → t ≤ max vpre (coh ws a) → readable img log ws vpre a t' → t' = t := by
  rintro ⟨ht, htop⟩ hfloor ⟨ht', hn'⟩
  by_cases hne : t' = t
  · exact hne
  exfalso
  by_cases hlt : t' < t
  · exact hn' ((writesInLogByte img log a _ _).2 ⟨t, hlt, hfloor, ht⟩)
  · exact htop ((writesInLogByte img log a _ _).2
      ⟨t', by omega, logByteBounded img log t' a ht', ht'⟩)

/-- The `vpre = 0` instance of `readableLatestPin`. -/
theorem readableTopUnique (img : Image) (log : List Wmsg) (ws : Wstate) (vpre : Nat) (a : Int)
    (t t' : Nat) :
    (logByte img log t a).isSome → t ≤ coh ws a → ¬ writesIn log a t log.length →
    readable img log ws vpre a t' → t' = t := by
  intro ht hcoh htop hr
  exact readableLatestPin img log ws vpre a t t' ⟨ht, htop⟩ (by omega) hr

/-- Right after a store, the storer can only read back its own message. -/
theorem storeFreshTopUnique (img : Image) (log : List Wmsg) (ws : Wstate) (rl : Bool) (m : Wmsg)
    (a : Int) (vpre t' : Nat) :
    (msgByte m a).isSome →
    readable img (log ++ [m]) (storePost ws rl a (log.length + 1)) vpre a t' →
    t' = log.length + 1 := by
  intro hm hr
  refine readableTopUnique img (log ++ [m]) _ vpre a _ t' ?_ (storePostCoh _ _ _ _) ?_ hr
  · rw [logByteS, list_lookup_middle rfl]; exact hm
  · rw [List.length_append]; rintro ⟨t, h1, h2, _⟩; simp at h2; omega

/-! ## `wsBounded`: every view a hart holds is a real timestamp -/

/-- The reservation's own boundedness. -/
def wresvBounded (o : Option Wresv) (n : Nat) : Prop :=
  ∀ R, o = some R → (∀ (j t : Nat), R.rvTs[j]? = some t → t ≤ n) ∧ R.rvView ≤ n

theorem wresvBoundedNone (n : Nat) : wresvBounded none n := by
  intro R h; cases h

theorem wresvBoundedMono (o : Option Wresv) (n n' : Nat) :
    wresvBounded o n → n ≤ n' → wresvBounded o n' := by
  intro ho hle R hR
  obtain ⟨hts, hv⟩ := ho R hR
  exact ⟨fun j t ht => Nat.le_trans (hts j t ht) hle, by omega⟩

def wsBounded (ws : Wstate) (n : Nat) : Prop :=
  ws.wVrOld ≤ n ∧ ws.wVwOld ≤ n ∧
  ws.wVrNew ≤ n ∧ ws.wVwNew ≤ n ∧ ws.wVRel ≤ n ∧
  ws.wPub ≤ n ∧
  (∀ a, coh ws a ≤ n) ∧
  (∀ a tv, get? ws.wFwd a = some tv → tv.1 ≤ n ∧ tv.2 ≤ n) ∧
  (∀ r, regv ws r ≤ n) ∧ ws.wVcap ≤ n ∧ ws.wLdv ≤ n ∧
  wresvBounded ws.wRes n ∧ ws.wTbank ≤ n

theorem wsBoundedVcap (ws : Wstate) (n : Nat) : wsBounded ws n → ws.wVcap ≤ n :=
  fun h => h.2.2.2.2.2.2.2.2.2.1
theorem wsBoundedLdv (ws : Wstate) (n : Nat) : wsBounded ws n → ws.wLdv ≤ n :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.1
theorem wsBoundedRes (ws : Wstate) (n : Nat) : wsBounded ws n → wresvBounded ws.wRes n :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.1
theorem wsBoundedTbank (ws : Wstate) (n : Nat) : wsBounded ws n → ws.wTbank ≤ n :=
  fun h => h.2.2.2.2.2.2.2.2.2.2.2.2
theorem wsBoundedRegv (ws : Wstate) (n : Nat) (r : Nat) : wsBounded ws n → regv ws r ≤ n :=
  fun h => h.2.2.2.2.2.2.2.2.1 r

/-- A source list's view is bounded by any bound on the state. -/
theorem srcsViewBounded (ws : Wstate) (n : Nat) (l : List Dsrc) :
    wsBounded ws n → srcsView ws l ≤ n := by
  intro hb
  induction l with
  | nil => exact Nat.zero_le _
  | cons x l ih =>
    rw [srcsViewCons]
    cases x with
    | DReg r => have := wsBoundedRegv ws n r hb; simp only [dsrcView]; omega
    | DLdRes => have := wsBoundedLdv ws n hb; simp only [dsrcView]; omega

/-! ## D3: THE DEPENDENCY-ONLY MOVE -/

def wsDepmove (w1 w2 : Wstate) : Prop :=
  w2.wCoh = w1.wCoh ∧
  w2.wVrOld = w1.wVrOld ∧ w2.wVwOld = w1.wVwOld ∧
  w2.wVrNew = w1.wVrNew ∧ w2.wVwNew = w1.wVwNew ∧
  w2.wVRel = w1.wVRel ∧ w2.wFwd = w1.wFwd ∧
  w2.wPub = w1.wPub ∧ w2.wRelp = w1.wRelp ∧
  w1.wVcap ≤ w2.wVcap

theorem wsDepmoveRefl (w : Wstate) : wsDepmove w w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem wsDepmoveTrans {w1 w2 w3 : Wstate} : wsDepmove w1 w2 → wsDepmove w2 w3 → wsDepmove w1 w3 := by
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, Nat.le_trans a10 b10⟩

instance : Trans wsDepmove wsDepmove wsDepmove := ⟨wsDepmoveTrans⟩

theorem wsDepmoveCoh (w1 w2 : Wstate) (a : Int) : wsDepmove w1 w2 → coh w2 a = coh w1 a := by
  intro h; simp only [coh, h.1]

theorem wsDepmoveRelp (w1 w2 : Wstate) : wsDepmove w1 w2 → w2.wRelp = w1.wRelp :=
  fun h => h.2.2.2.2.2.2.2.2.1

theorem wsDepmoveLe (w1 w2 : Wstate) : wsDepmove w1 w2 → wsLe w1 w2 := by
  rintro ⟨hc, h1, h2, h3, h4, h5, _, h7, _, h9⟩
  exact ⟨fun a => by simp only [coh, hc]; exact Nat.le_refl _, by omega, by omega, by omega,
    by omega, by omega, by omega, h9⟩

theorem regwPostDepmove (ws : Wstate) (rd v : Nat) : wsDepmove ws (regwPost ws rd v) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem ctrlPostDepmove (ws : Wstate) (v : Nat) : wsDepmove ws (ctrlPost ws v) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_max_right _ _⟩

theorem instrPostDepmove (ws : Wstate) : wsDepmove ws (instrPost ws) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem wsBoundedInit (n : Nat) : wsBounded wsInit n := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, fun a => by rw [cohInit]; exact Nat.zero_le _, ?_,
    fun r => by rw [regvInit]; exact Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    wresvBoundedNone n, Nat.zero_le _⟩
  intro a tv h
  exact absurd h (by simp [wsInit, lookupEmpty])

theorem wsBoundedMono (ws : Wstate) (n n' : Nat) :
    wsBounded ws n → n ≤ n' → wsBounded ws n' := by
  rintro ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hres, htb⟩ hle
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    fun a => Nat.le_trans (hcoh a) hle, fun a tv h => ?_, fun r => Nat.le_trans (hrg r) hle,
    by omega, by omega, wresvBoundedMono _ _ _ hres hle, by omega⟩
  have := hfwd a tv h; omega

/-- The `coh` half of every preservation proof below. -/
theorem cohUpdBounded (ws : Wstate) (vrO vwO vrN vwN vR : Nat) (fwd : GMapF Int (Nat × Nat))
    (pb : Nat) (rp : Bool) (rg : GMapF Nat Nat) (vc ld : Nat) (rs : Option Wresv) (tb : Nat)
    (a : Int) (v n : Nat) :
    (∀ a', coh ws a' ≤ n) → v ≤ n →
    ∀ a', coh { wCoh := insert ws.wCoh a v, wVrOld := vrO, wVwOld := vwO, wVrNew := vrN,
                wVwNew := vwN, wVRel := vR, wFwd := fwd, wPub := pb, wRelp := rp, wRegv := rg,
                wVcap := vc, wLdv := ld, wRes := rs, wTbank := tb } a' ≤ n := by
  intro hm hv a'
  by_cases h : a' = a
  · subst h; rw [cohUpdEq]; exact hv
  · rw [cohUpdNe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h]; exact hm a'

theorem loadVpreBounded (ws : Wstate) (aq : Bool) (n : Nat) :
    wsBounded ws n → loadVpre ws aq ≤ n := by
  rintro ⟨_, _, hrn, _, hrel, _⟩
  simp only [loadVpre]; split <;> omega

theorem loadVpreDBounded (ws : Wstate) (aq : Bool) (vaddr n : Nat) :
    wsBounded ws n → vaddr ≤ n → loadVpreD ws aq vaddr ≤ n := by
  intro hb hv
  have := loadVpreBounded ws aq n hb
  simp only [loadVpreD]; omega

theorem fwdViewBounded (ws : Wstate) (aq : Bool) (a : Int) (t n : Nat) :
    wsBounded ws n → t ≤ n → fwdView ws aq a t ≤ n := by
  intro hb ht
  have hfwd := hb.2.2.2.2.2.2.2.1
  unfold fwdView
  cases aq with
  | true => exact ht
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hf : get? ws.wFwd a with
    | none => exact ht
    | some p =>
      obtain ⟨tf, vf⟩ := p
      simp only
      split
      · exact (hfwd a (tf, vf) hf).2
      · exact ht

theorem loadPostAtBounded (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t n : Nat) :
    wsBounded ws n → vpre ≤ n → t ≤ n → wsBounded (loadPostAt ws aq vpre a t) n := by
  intro hb hvp ht
  have hfv := fwdViewBounded ws aq a t n hb ht
  obtain ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hres, htb⟩ := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, cohUpdBounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcoh
    (by have := hcoh a; omega), hfwd, hrg, hvc, ?_, wresvBoundedNone n, ?_⟩ <;>
    simp only [loadPostAt] <;> (try split) <;> omega

theorem storePostDBounded (ws : Wstate) (rl : Bool) (vf : Nat) (a : Int) (t n n' : Nat) :
    wsBounded ws n → t ≤ n' → n ≤ n' → vf ≤ n' → wsBounded (storePostD ws rl vf a t) n' := by
  rintro ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hres, htb⟩ ht hle hvf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    cohUpdBounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a' => Nat.le_trans (hcoh a') hle)
      (by have := hcoh a; omega), ?_, fun r => Nat.le_trans (hrg r) hle, ?_, ?_,
    wresvBoundedNone n', ?_⟩
  all_goals simp only [storePostD]
  all_goals try (split <;> omega)
  all_goals try omega
  intro a' tv
  by_cases h : a = a'
  · subst h; rw [lookupInsert]; intro he; injection he with he; subst he; simp; omega
  · rw [lookupInsertNe h]; intro ha; have := hfwd a' tv ha; omega

theorem storePostBounded (ws : Wstate) (rl : Bool) (a : Int) (t n n' : Nat) :
    wsBounded ws n → t ≤ n' → n ≤ n' → wsBounded (storePost ws rl a t) n' := by
  intro hb ht hle
  rw [← storePostD0]
  exact storePostDBounded ws rl 0 a t n n' hb ht hle (Nat.zero_le _)

theorem fencePostBounded (ws : Wstate) (pr pw sr sw : Bool) (n : Nat) :
    wsBounded ws n → wsBounded (fencePost ws pr pw sr sw) n := by
  rintro ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hres, htb⟩
  refine ⟨hro, hwo, ?_, ?_, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, ?_, htb⟩
  · simp only [fencePost]; (repeat' split) <;> omega
  · simp only [fencePost]; (repeat' split) <;> omega
  · simp only [fencePost]; split
    · exact wresvBoundedNone n
    · exact hres

/-- The three dependency-only effects preserve both orders. -/
theorem regwPostLe (ws : Wstate) (rd v : Nat) : wsLe ws (regwPost ws rd v) :=
  wsDepmoveLe _ _ (regwPostDepmove ws rd v)

theorem instrPostLe (ws : Wstate) : wsLe ws (instrPost ws) :=
  wsDepmoveLe _ _ (instrPostDepmove ws)

theorem regwPostBounded (ws : Wstate) (rd v n : Nat) :
    wsBounded ws n → v ≤ n → wsBounded (regwPost ws rd v) n := by
  rintro ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hres, htb⟩ hv
  refine ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, fun r => ?_, hvc, hld, hres, htb⟩
  by_cases h : r = rd
  · subst h; rw [regvRegwPostEq]; exact hv
  · rw [regvRegwPostNe _ _ _ _ h]; exact hrg r

theorem ctrlPostBounded (ws : Wstate) (v n : Nat) :
    wsBounded ws n → v ≤ n → wsBounded (ctrlPost ws v) n := by
  rintro ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hres, htb⟩ hv
  exact ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, by simp only [ctrlPostVcap]; omega,
    hld, hres, htb⟩

theorem instrPostBounded (ws : Wstate) (n : Nat) : wsBounded ws n → wsBounded (instrPost ws) n := by
  rintro ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hres, htb⟩
  exact ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, Nat.zero_le _,
    wresvBoundedNone n, Nat.zero_le _⟩

/-- ... and the multi-byte folds. -/
theorem loadPostFoldBounded (aq : Bool) (vpre n : Nat) (ats : List (Int × Nat)) :
    vpre ≤ n → ∀ ws, wsBounded ws n → (∀ p ∈ ats, p.2 ≤ n) →
      wsBounded (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) n := by
  intro hvp
  induction ats with
  | nil => intro ws hb _; exact hb
  | cons p l ih =>
    intro ws hb hall
    exact ih _ (loadPostAtBounded _ _ _ _ _ _ hb hvp (hall p List.mem_cons_self))
      (fun q hq => hall q (List.mem_cons_of_mem _ hq))

theorem loadPostBytesBounded (ws : Wstate) (aq : Bool) (ats : List (Int × Nat)) (n : Nat) :
    wsBounded ws n → (∀ p ∈ ats, p.2 ≤ n) → wsBounded (loadPostBytes ws aq ats) n :=
  fun hb hall => loadPostFoldBounded aq _ n ats (loadVpreBounded ws aq n hb) ws hb hall

theorem storePostFoldBounded (rl : Bool) (t n' : Nat) (as_ : List Int) :
    t ≤ n' → ∀ ws, wsBounded ws n' → wsBounded (as_.foldl (fun w a => storePost w rl a t) ws) n' := by
  intro ht
  induction as_ with
  | nil => intro ws hb; exact hb
  | cons a l ih => intro ws hb; exact ih _ (storePostBounded ws rl a t n' n' hb ht (Nat.le_refl _))

theorem storePostBytesBounded (ws : Wstate) (rl : Bool) (as_ : List Int) (t n n' : Nat) :
    wsBounded ws n → t ≤ n' → n ≤ n' → wsBounded (storePostBytes ws rl as_ t) n' :=
  fun hb ht hle => storePostFoldBounded rl t n' as_ ht ws (wsBoundedMono ws n n' hb hle)

/-- The contiguous-run transport. -/
theorem forallZipSeq (base : Int) (n : Nat) (ts : List Nat) :
    (∀ t ∈ ts, t ≤ n) →
    ∀ k, ∀ p ∈ List.zipWith (fun (j : Nat) t => (base + (j : Int), t)) (List.range' k ts.length) ts,
      p.2 ≤ n := by
  induction ts with
  | nil => intro _ k p hp; simp at hp
  | cons t l ih =>
    intro hall k p hp
    rw [List.length_cons, List.range'_succ, List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hall t List.mem_cons_self
    · exact ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (k + 1) p hp

theorem loadPostRunBounded (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (n : Nat) :
    wsBounded ws n → (∀ t ∈ ts, t ≤ n) → wsBounded (loadPostRun ws aq base ts) n := by
  intro hb hall
  exact ctrlPostBounded _ _ _ (loadPostBytesBounded _ _ _ _ hb (forallZipSeq base n ts hall 0))
    (wsBoundedTbank _ _ hb)

theorem storePostRunBounded (ws : Wstate) (rl : Bool) (base : Int) (cnt t n n' : Nat) :
    wsBounded ws n → t ≤ n' → n ≤ n' → wsBounded (storePostRun ws rl base cnt t) n' := by
  intro hb ht hle
  exact ctrlPostBounded _ _ _ (storePostBytesBounded ws rl _ t n n' hb ht hle)
    (Nat.le_trans (wsBoundedTbank _ _ hb) hle)

/-- THE PAYOFF: the hart's own index into the log is a real timestamp. -/
theorem wsBoundedScl (ws : Wstate) (n : Nat) :
    wsBounded ws n → ∀ a, max ws.wVrNew (coh ws a) ≤ n := by
  intro hb a
  have := hb.2.2.2.2.2.2.1 a
  have := hb.2.2.1
  omega


/-! ## THE W4 LIFT BATCH — fold facts the consumers used to prove locally

Three kinds of fact about the step functions live in this file: MONOTONE
(`wsLe`), BOUNDED (`wsBounded`), and DOMINATED (upper bounds in terms of the
step's inputs). -/

/-! ### Singleton collapses of the run-shaped post-states -/

private theorem intAddNatZero (base : Int) : base + ((0 : Nat) : Int) = base := by simp

theorem loadPostRunSingle (ws : Wstate) (aq : Bool) (base : Int) (t : Nat) :
    loadPostRun ws aq base [t] = ctrlPost (loadPost ws aq base t) ws.wTbank := by
  show ctrlPost (loadPostAt ws aq (loadVpre ws aq) (base + ((0 : Nat) : Int)) t) ws.wTbank = _
  rw [intAddNatZero]; rfl

theorem storePostRunSingle (ws : Wstate) (rl : Bool) (base : Int) (v : BitVec 8) (t : Nat) :
    storePostRun ws rl base [v].length t = ctrlPost (storePost ws rl base t) ws.wTbank := by
  show ctrlPost (storePost ws rl (base + ((0 : Nat) : Int)) t) ws.wTbank = _
  rw [intAddNatZero]

/-! ### A message writes only inside its own byte range -/

theorem msgByteRange (m : Wmsg) (a : Int) :
    (msgByte m a).isSome → ∃ j : Nat, j < m.wmData.length ∧ a = m.wmPa + (j : Int) := by
  unfold msgByte
  split
  · intro hs
    refine ⟨(a - m.wmPa).toNat, lookup_lt_is_Some_1 hs, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; omega
  · intro h; simp at h

/-! ### The missing `coh` / `wVwOld` / forwarded-`wVrOld` fold instances -/

theorem loadPostFoldCoh (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) (a : Int)
    (t : Nat) :
    (a, t) ∈ ats → t ≤ coh (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) a := by
  induction ats generalizing ws with
  | nil => intro h; cases h
  | cons p l ih =>
    intro hin
    rcases List.mem_cons.1 hin with rfl | hin
    · exact Nat.le_trans (loadPostAtCoh ws aq vpre a t)
        (wsLeCoh _ _ a (loadPostFoldLe aq vpre l (loadPostAt ws aq vpre a t)))
    · exact ih _ hin

theorem loadPostRunCoh (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t → t ≤ coh (loadPostRun ws aq base ts) (base + (j : Int)) := fun ht =>
  loadPostFoldCoh aq _ _ ws _ t (memLoadRunAts base ts j t ht)

theorem storePostFoldCoh (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) (a : Int) :
    a ∈ as_ → t ≤ coh (as_.foldl (fun w a => storePost w rl a t) ws) a := by
  induction as_ generalizing ws with
  | nil => intro h; cases h
  | cons b l ih =>
    intro hin
    rcases List.mem_cons.1 hin with rfl | hin
    · exact Nat.le_trans (storePostCoh ws rl a t)
        (wsLeCoh _ _ a (storePostFoldLe rl t l (storePost ws rl a t)))
    · exact ih _ hin

/-- The store run's byte list contains byte `j < n`. -/
theorem memStoreRunAs (base : Int) (n j : Nat) :
    j < n → base + (j : Int) ∈ (List.range' 0 n).map (fun j : Nat => base + (j : Int)) := by
  intro hj
  exact List.mem_map.2 ⟨j, List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩, rfl⟩

theorem storePostRunCoh (ws : Wstate) (rl : Bool) (base : Int) (n t j : Nat) :
    j < n → t ≤ coh (storePostRun ws rl base n t) (base + (j : Int)) := fun hj =>
  storePostFoldCoh rl t _ ws _ (memStoreRunAs base n j hj)

theorem storePostFoldVwOld (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    as_ ≠ [] → t ≤ (as_.foldl (fun w a => storePost w rl a t) ws).wVwOld := by
  cases as_ with
  | nil => intro h; exact (h rfl).elim
  | cons a l =>
    intro _
    exact Nat.le_trans (storePostVwOld ws rl a t)
      (wsLeVwOld _ _ (storePostFoldLe rl t l (storePost ws rl a t)))

theorem storePostRunVwOld (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) :
    0 < n → t ≤ (storePostRun ws rl base n t).wVwOld := by
  intro hn
  apply storePostFoldVwOld
  cases n with
  | zero => omega
  | succ n => simp [List.range'_succ]

/-- The generalized `loadPostRunVrOld`: the side condition is "this byte's read
was not forwarded". -/
theorem loadPostFoldVrOld' (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate)
    (a : Int) (t : Nat) :
    (a, t) ∈ ats → fwdView ws aq a t = t →
    t ≤ (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrOld := by
  induction ats generalizing ws with
  | nil => intro h; cases h
  | cons p l ih =>
    intro hin hfv
    rcases List.mem_cons.1 hin with rfl | hin
    · refine Nat.le_trans ?_ (wsLeVrOld _ _ (loadPostFoldLe aq vpre l (loadPostAt ws aq vpre a t)))
      simp only [loadPostAt, hfv]; omega
    · exact ih _ hin hfv

theorem loadPostRunVrOld' (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t → fwdView ws aq (base + (j : Int)) t = t →
    t ≤ (loadPostRun ws aq base ts).wVrOld := fun ht hfv =>
  loadPostFoldVrOld' aq _ _ ws _ t (memLoadRunAts base ts j t ht) hfv

/-! ### The acquire-load fold instances -/

theorem loadPostFoldVrNewAq (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) (a : Int) (t : Nat) :
    (a, t) ∈ ats → t ≤ (ats.foldl (fun w at_ => loadPostAt w true vpre at_.1 at_.2) ws).wVrNew := by
  induction ats generalizing ws with
  | nil => intro h; cases h
  | cons p l ih =>
    intro hin
    rcases List.mem_cons.1 hin with rfl | hin
    · exact Nat.le_trans (loadPostAtVrNewAq ws vpre a t)
        (wsLeVrNew _ _ (loadPostFoldLe true vpre l (loadPostAt ws true vpre a t)))
    · exact ih _ hin

theorem loadPostRunVrNewAq (ws : Wstate) (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t → t ≤ (loadPostRun ws true base ts).wVrNew := fun ht =>
  loadPostFoldVrNewAq _ _ ws _ t (memLoadRunAts base ts j t ht)

theorem loadPostFoldVwNewAq (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) (a : Int) (t : Nat) :
    (a, t) ∈ ats → t ≤ (ats.foldl (fun w at_ => loadPostAt w true vpre at_.1 at_.2) ws).wVwNew := by
  induction ats generalizing ws with
  | nil => intro h; cases h
  | cons p l ih =>
    intro hin
    rcases List.mem_cons.1 hin with rfl | hin
    · exact Nat.le_trans (loadPostAtVwNewAq ws vpre a t)
        (wsLeVwNew _ _ (loadPostFoldLe true vpre l (loadPostAt ws true vpre a t)))
    · exact ih _ hin

theorem loadPostRunVwNewAq (ws : Wstate) (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t → t ≤ (loadPostRun ws true base ts).wVwNew := fun ht =>
  loadPostFoldVwNewAq _ _ ws _ t (memLoadRunAts base ts j t ht)

/-- An ACQUIRE load's own PRE-VIEW lands under its post-`wVrNew`. -/
theorem loadPostFoldVrNewAqVpre (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate)
    (p : Int × Nat) :
    p ∈ ats → vpre ≤ (ats.foldl (fun w at_ => loadPostAt w true vpre at_.1 at_.2) ws).wVrNew := by
  induction ats generalizing ws with
  | nil => intro h; cases h
  | cons q l ih =>
    intro hin
    rcases List.mem_cons.1 hin with rfl | hin
    · refine Nat.le_trans ?_ (wsLeVrNew _ _ (loadPostFoldLe true vpre l (loadPostAt ws true vpre p.1 p.2)))
      simp only [loadPostAt, ↓reduceIte]; omega
    · exact ih _ hin

theorem loadPostRunVrNewAqVpre (ws : Wstate) (base : Int) (ts : List Nat) (j t : Nat) :
    ts[j]? = some t → loadVpre ws true ≤ (loadPostRun ws true base ts).wVrNew := fun ht =>
  loadPostFoldVrNewAqVpre _ _ ws _ (memLoadRunAts base ts j t ht)

/-! ### The forward-bank inversion for a store fold -/

theorem storePostFoldFwd (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) (a : Int) (tf vf : Nat) :
    get? (as_.foldl (fun w a => storePost w rl a t) ws).wFwd a = some (tf, vf) →
    tf = t ∨ get? ws.wFwd a = some (tf, vf) := by
  induction as_ generalizing ws with
  | nil => intro h; exact .inr h
  | cons b l ih =>
    intro hlk
    rcases ih _ hlk with h | hlk'
    · exact .inl h
    · simp only [storePost] at hlk'
      by_cases h : b = a
      · subst h; rw [lookupInsert] at hlk'; injection hlk' with hlk'; injection hlk' with h1 _
        exact .inl h1.symm
      · rw [lookupInsertNe h] at hlk'; exact .inr hlk'

theorem storePostRunFwdInv (ws : Wstate) (rl : Bool) (base : Int) (n t : Nat) (a : Int) (tf vf : Nat) :
    get? (storePostRun ws rl base n t).wFwd a = some (tf, vf) →
    tf = t ∨ get? ws.wFwd a = some (tf, vf) :=
  storePostFoldFwd rl t _ ws a tf vf

/-! ## DOMINATION: upper bounds for the step functions -/

def maxcl (P : Nat → Prop) : Prop := P 0 ∧ ∀ n1 n2, P n1 → P n2 → P (max n1 n2)

theorem maxcl0 (P : Nat → Prop) : maxcl P → P 0 := fun h => h.1

theorem maxclMax (P : Nat → Prop) (n1 n2 : Nat) : maxcl P → P n1 → P n2 → P (max n1 n2) :=
  fun h => h.2 n1 n2

/-! ### Pointwise shapes of the two per-byte updates -/

theorem cohLoadPostAtEq (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) :
    coh (loadPostAt ws aq vpre a t) a = max (coh ws a) (max (max vpre (fwdView ws aq a t)) t) := by
  simp only [loadPostAt, coh, lookupInsert, Option.getD_some]

theorem cohLoadPostAtNe (ws : Wstate) (aq : Bool) (vpre : Nat) (a : Int) (t : Nat) (a' : Int) :
    a' ≠ a → coh (loadPostAt ws aq vpre a t) a' = coh ws a' := by
  intro h; simp only [loadPostAt, coh, lookupInsertNe (Ne.symm h)]

theorem cohStorePostEq (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) :
    coh (storePost ws rl a t) a = max (coh ws a) t := by
  simp only [storePost, coh, lookupInsert, Option.getD_some]

theorem cohStorePostNe (ws : Wstate) (rl : Bool) (a : Int) (t : Nat) (a' : Int) :
    a' ≠ a → coh (storePost ws rl a t) a' = coh ws a' := by
  intro h; simp only [storePost, coh, lookupInsertNe (Ne.symm h)]

/-! ### The load fold: the components it does not touch -/

theorem loadFoldVwOld (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVwOld = ws.wVwOld := by
  induction ats generalizing ws with
  | nil => rfl
  | cons p l ih => exact ih _

theorem loadFoldVRel (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVRel = ws.wVRel := by
  induction ats generalizing ws with
  | nil => rfl
  | cons p l ih => exact ih _

theorem loadFoldVrNewPlain (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w false vpre at_.1 at_.2) ws).wVrNew = ws.wVrNew := by
  induction ats generalizing ws with
  | nil => rfl
  | cons p l ih => exact ih _

/-! ### The load fold: upper bounds, under "no byte of this load is forwarded" -/

theorem loadFoldCoh (P : Nat → Prop) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws : Wstate) (a : Int) :
    maxcl P → (∀ p ∈ ats, fwdView ws aq p.1 p.2 = p.2) →
    P (coh ws a) → P vpre → (∀ p ∈ ats, p.1 = a → P p.2) →
    P (coh (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) a) := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _ _; exact hc
  | cons p l ih =>
    intro hfv hc hv hts
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fun q hq => hfv q (List.mem_cons_of_mem _ hq)) _ hv
      (fun q hq hqa => hts q (List.mem_cons_of_mem _ hq) hqa)
    by_cases heq : a = p.1
    · have hpa : P p.2 := hts p List.mem_cons_self heq.symm
      rw [heq, cohLoadPostAtEq, hfv p List.mem_cons_self]
      rw [← heq]
      exact maxclMax P _ _ hcl hc (maxclMax P _ _ hcl (maxclMax P _ _ hcl hv hpa) hpa)
    · rw [cohLoadPostAtNe _ _ _ _ _ _ heq]; exact hc

theorem loadFoldVrOld (P : Nat → Prop) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws : Wstate) :
    maxcl P → (∀ p ∈ ats, fwdView ws aq p.1 p.2 = p.2) →
    P ws.wVrOld → P vpre → (∀ p ∈ ats, P p.2) →
    P (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrOld := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _ _; exact hc
  | cons p l ih =>
    intro hfv hc hv hts
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fun q hq => hfv q (List.mem_cons_of_mem _ hq)) _ hv
      (fun q hq => hts q (List.mem_cons_of_mem _ hq))
    simp only [loadPostAt, hfv p List.mem_cons_self]
    exact maxclMax P _ _ hcl hc (maxclMax P _ _ hcl hv (hts p List.mem_cons_self))

theorem loadFoldVrNew (P : Nat → Prop) (aq : Bool) (vpre : Nat) (ats : List (Int × Nat))
    (ws : Wstate) :
    maxcl P → (∀ p ∈ ats, fwdView ws aq p.1 p.2 = p.2) →
    P ws.wVrNew → P vpre → (∀ p ∈ ats, P p.2) →
    P (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wVrNew := by
  intro hcl
  induction ats generalizing ws with
  | nil => intro _ hc _ _; exact hc
  | cons p l ih =>
    intro hfv hc hv hts
    apply ih (loadPostAt ws aq vpre p.1 p.2) (fun q hq => hfv q (List.mem_cons_of_mem _ hq)) _ hv
      (fun q hq => hts q (List.mem_cons_of_mem _ hq))
    simp only [loadPostAt, hfv p List.mem_cons_self]
    cases aq with
    | false => exact hc
    | true => exact maxclMax P _ _ hcl hc (maxclMax P _ _ hcl hv (hts p List.mem_cons_self))

/-! ### The store fold -/

theorem storeFoldVrOld (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    (as_.foldl (fun w a => storePost w rl a t) ws).wVrOld = ws.wVrOld := by
  induction as_ generalizing ws with
  | nil => rfl
  | cons a l ih => exact ih _

theorem storeFoldVrNew (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    (as_.foldl (fun w a => storePost w rl a t) ws).wVrNew = ws.wVrNew := by
  induction as_ generalizing ws with
  | nil => rfl
  | cons a l ih => exact ih _

theorem storeFoldVRelNorl (t : Nat) (as_ : List Int) (ws : Wstate) :
    (as_.foldl (fun w a => storePost w false a t) ws).wVRel = ws.wVRel := by
  induction as_ generalizing ws with
  | nil => rfl
  | cons a l ih => exact ih _

theorem storeFoldVwOld (P : Nat → Prop) (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) :
    maxcl P → P ws.wVwOld → P t → P (as_.foldl (fun w a => storePost w rl a t) ws).wVwOld := by
  intro hcl
  induction as_ generalizing ws with
  | nil => intro hc _; exact hc
  | cons a l ih => intro hc ht; exact ih _ (maxclMax P _ _ hcl hc ht) ht

theorem storeFoldCoh (P : Nat → Prop) (rl : Bool) (t : Nat) (as_ : List Int) (ws : Wstate) (a : Int) :
    maxcl P → P (coh ws a) → (a ∈ as_ → P t) →
    P (coh (as_.foldl (fun w a => storePost w rl a t) ws) a) := by
  intro hcl
  induction as_ generalizing ws with
  | nil => intro hc _; exact hc
  | cons b l ih =>
    intro hc ht
    apply ih _ _ (fun hin => ht (List.mem_cons_of_mem _ hin))
    by_cases h : a = b
    · subst h; rw [cohStorePostEq]; exact maxclMax P _ _ hcl hc (ht List.mem_cons_self)
    · rw [cohStorePostNe _ _ _ _ _ h]; exact hc

/-! ### The fence -/

theorem fencePostVrNewPred (P : Nat → Prop) (ws : Wstate) (pr pw sr sw : Bool) :
    maxcl P → P ws.wVrNew →
    (pr = true → sr = true → P ws.wVrOld) →
    (pw = true → sr = true → P ws.wVwOld) →
    P (fencePost ws pr pw sr sw).wVrNew := by
  intro hcl hn hro hwo
  cases sr with
  | false => exact hn
  | true =>
    simp only [fencePost, ↓reduceIte]
    refine maxclMax P _ _ hcl hn (maxclMax P _ _ hcl ?_ ?_)
    · cases pr with
      | true => exact hro rfl rfl
      | false => exact maxcl0 P hcl
    · cases pw with
      | true => exact hwo rfl rfl
      | false => exact maxcl0 P hcl

/-! ## THE DEPENDENCY-CARRYING RUN FACTS (D2) -/

/-! ### The load run -/

theorem loadPostBytesDLe (ws : Wstate) (aq : Bool) (vaddr : Nat) (ats : List (Int × Nat)) :
    wsLe ws (loadPostBytesD ws aq vaddr ats) := loadPostFoldLe _ _ _ _

theorem loadPostRunDLe (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    wsLe ws (loadPostRunD ws aq vaddr base ts) :=
  wsLeTrans (loadPostBytesDLe _ _ _ _) (ctrlPostLe _ _)

theorem loadPostBytesDBounded (ws : Wstate) (aq : Bool) (vaddr : Nat) (ats : List (Int × Nat))
    (n : Nat) :
    wsBounded ws n → vaddr ≤ n → (∀ p ∈ ats, p.2 ≤ n) →
    wsBounded (loadPostBytesD ws aq vaddr ats) n := fun hb hva hall =>
  loadPostFoldBounded aq _ n ats (loadVpreDBounded ws aq vaddr n hb hva) ws hb hall

theorem loadPostRunDBounded (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat)
    (n : Nat) :
    wsBounded ws n → vaddr ≤ n → (∀ t ∈ ts, t ≤ n) →
    wsBounded (loadPostRunD ws aq vaddr base ts) n := by
  intro hb hva hall
  refine ctrlPostBounded _ _ _ (loadPostBytesDBounded _ _ _ _ _ hb hva
    (forallZipSeq base n ts hall 0)) ?_
  have := wsBoundedTbank _ _ hb
  omega

theorem loadPostRunDFwd (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    (loadPostRunD ws aq vaddr base ts).wFwd = ws.wFwd := loadPostFoldFwd _ _ _ _

private theorem loadPostFoldRelp (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (ws : Wstate) :
    (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws).wRelp = ws.wRelp := by
  induction ats generalizing ws with
  | nil => rfl
  | cons p l ih => exact ih _

theorem loadPostRunDRelp (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    (loadPostRunD ws aq vaddr base ts).wRelp = ws.wRelp := loadPostFoldRelp _ _ _ _

theorem loadPostRunDCoh (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat)
    (j t : Nat) :
    ts[j]? = some t → t ≤ coh (loadPostRunD ws aq vaddr base ts) (base + (j : Int)) := fun ht =>
  loadPostFoldCoh aq _ _ ws _ t (memLoadRunAts base ts j t ht)

theorem loadPostRunDVcap (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    vaddr ≤ (loadPostRunD ws aq vaddr base ts).wVcap := by
  simp only [loadPostRunD, ctrlPostVcap]; omega

/-- The RMW's exclusive-bank view is bounded like every other view. -/
theorem wsLdv0Bounded (ws : Wstate) (n : Nat) : wsBounded ws n → wsBounded (wsLdv0 ws) n :=
  instrPostBounded ws n

theorem ldvOfBounded (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) (n : Nat) :
    wsBounded ws n → vaddr ≤ n → (∀ t ∈ ts, t ≤ n) → ldvOf ws aq vaddr base ts ≤ n := fun hb hva hall =>
  wsBoundedLdv _ _ (loadPostRunDBounded _ aq vaddr base ts n (wsLdv0Bounded ws n hb) hva hall)

/-! ### The EXCLUSIVE load run (RMW split S2) -/

theorem wsResSetLe (ws1 ws2 : Wstate) (r : Option Wresv) : wsLe ws1 ws2 → wsLe ws1 (wsResSet ws2 r) :=
  id

theorem wsResSetBounded (ws : Wstate) (r : Option Wresv) (n : Nat) :
    wsBounded ws n → wresvBounded r n → wsBounded (wsResSet ws r) n := by
  rintro ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, _, htb⟩ hr
  exact ⟨hro, hwo, hrn, hwn, hrel, hpub, hcoh, hfwd, hrg, hvc, hld, hr, htb⟩

theorem resViewBounded (ws : Wstate) (n : Nat) : wsBounded ws n → resView ws ≤ n := by
  intro hb
  unfold resView
  cases hR : ws.wRes with
  | none => exact Nat.zero_le _
  | some R => exact (wsBoundedRes _ _ hb R hR).2

theorem exloadPostRunDLe (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    wsLe ws (exloadPostRunD ws aq vaddr base ts) :=
  wsResSetLe _ _ _ (wsLeTrans (loadPostBytesLe _ _ _) (ctrlPostLe _ _))

theorem exloadPostRunDBounded (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat)
    (n : Nat) :
    wsBounded ws n → vaddr ≤ n → (∀ t ∈ ts, t ≤ n) →
    wsBounded (exloadPostRunD ws aq vaddr base ts) n := by
  intro hb hva hall
  apply wsResSetBounded
  · refine ctrlPostBounded _ _ _ (loadPostBytesBounded _ _ _ _ hb (forallZipSeq base n ts hall 0)) ?_
    have := wsBoundedTbank _ _ hb
    omega
  · intro R hR
    injection hR with hR
    subst hR
    refine ⟨fun j t ht => hall t (elem_of_list_lookup_2 ht), ?_⟩
    exact ldvOfBounded ws aq 0 base ts n hb (Nat.zero_le _) hall

theorem exloadPostRunDFwd (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    (exloadPostRunD ws aq vaddr base ts).wFwd = ws.wFwd := loadPostFoldFwd _ _ _ _

theorem exloadPostRunDRelp (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    (exloadPostRunD ws aq vaddr base ts).wRelp = ws.wRelp := loadPostFoldRelp _ _ _ _

theorem exloadPostRunDCoh (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat)
    (j t : Nat) :
    ts[j]? = some t → t ≤ coh (exloadPostRunD ws aq vaddr base ts) (base + (j : Int)) := fun ht =>
  loadPostFoldCoh aq _ _ ws _ t (memLoadRunAts base ts j t ht)

theorem exloadPostRunDVcap (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    vaddr ≤ (exloadPostRunD ws aq vaddr base ts).wVcap := by
  simp only [exloadPostRunD, wsResSetVcap, ctrlPostVcap]; omega

/-! ### The store run -/

theorem storePostDLe (ws : Wstate) (rl : Bool) (vf : Nat) (a : Int) (t : Nat) :
    wsLe ws (storePostD ws rl vf a t) := storePostLe ws rl a t

theorem storePostFoldDLe (rl : Bool) (vf t : Nat) (as_ : List Int) (ws : Wstate) :
    wsLe ws (as_.foldl (fun w a => storePostD w rl vf a t) ws) := storePostFoldLe rl t as_ ws

theorem storePostBytesDLe (ws : Wstate) (rl : Bool) (vf : Nat) (as_ : List Int) (t : Nat) :
    wsLe ws (storePostBytesD ws rl vf as_ t) := storePostFoldDLe _ _ _ _ _

theorem storePostRunDLe (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat) :
    wsLe ws (storePostRunD ws rl vaddr vdata base n t) :=
  wsLeTrans (storePostBytesDLe _ _ _ _ _) (ctrlPostLe _ _)

theorem storePostFoldDBounded (rl : Bool) (vf t : Nat) (as_ : List Int) (n' : Nat) :
    vf ≤ n' → t ≤ n' → ∀ ws, wsBounded ws n' →
      wsBounded (as_.foldl (fun w a => storePostD w rl vf a t) ws) n' := by
  intro hvf ht
  induction as_ with
  | nil => intro ws hb; exact hb
  | cons a l ih =>
    intro ws hb
    exact ih _ (storePostDBounded ws rl vf a t n' n' hb ht (Nat.le_refl _) hvf)

theorem storePostBytesDBounded (ws : Wstate) (rl : Bool) (vf : Nat) (as_ : List Int) (t n n' : Nat) :
    wsBounded ws n → t ≤ n' → n ≤ n' → vf ≤ n' → wsBounded (storePostBytesD ws rl vf as_ t) n' :=
  fun hb ht hle hvf => storePostFoldDBounded rl vf t as_ n' hvf ht ws (wsBoundedMono ws n n' hb hle)

theorem storePostRunDBounded (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int)
    (cnt t n n' : Nat) :
    wsBounded ws n → t ≤ n' → n ≤ n' → vaddr ≤ n' → vdata ≤ n' →
    wsBounded (storePostRunD ws rl vaddr vdata base cnt t) n' := by
  intro hb ht hle hva hvd
  refine ctrlPostBounded _ _ _ (storePostBytesDBounded _ _ _ _ _ n n' hb ht hle (by omega)) ?_
  have := wsBoundedTbank _ _ hb
  omega

theorem storePostFoldDCoh (rl : Bool) (vf t : Nat) (as_ : List Int) (ws : Wstate) (a : Int) :
    a ∈ as_ → t ≤ coh (as_.foldl (fun w a => storePostD w rl vf a t) ws) a :=
  storePostFoldCoh rl t as_ ws a

theorem storePostRunDCoh (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t j : Nat) :
    j < n → t ≤ coh (storePostRunD ws rl vaddr vdata base n t) (base + (j : Int)) := fun hj =>
  storePostFoldCoh rl t _ ws _ (memStoreRunAs base n j hj)

theorem storePostFoldDVwOld (rl : Bool) (vf t : Nat) (as_ : List Int) (ws : Wstate) :
    as_ ≠ [] → t ≤ (as_.foldl (fun w a => storePostD w rl vf a t) ws).wVwOld :=
  storePostFoldVwOld rl t as_ ws

theorem storePostRunDVwOld (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat) :
    0 < n → t ≤ (storePostRunD ws rl vaddr vdata base n t).wVwOld :=
  storePostRunVwOld ws rl base n t

theorem storePostFoldDRelp (rl : Bool) (vf t : Nat) (as_ : List Int) (ws : Wstate) :
    as_ ≠ [] → (as_.foldl (fun w a => storePostD w rl vf a t) ws).wRelp = false := by
  induction as_ generalizing ws with
  | nil => intro h; exact (h rfl).elim
  | cons a l ih =>
    intro _
    cases l with
    | nil => rfl
    | cons b l' => exact ih _ (List.cons_ne_nil _ _)

theorem storePostRunDRelp (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat) :
    0 < n → (storePostRunD ws rl vaddr vdata base n t).wRelp = false := by
  intro hn
  apply storePostFoldDRelp
  cases n with
  | zero => omega
  | succ n => simp [storeRunAs, List.range'_succ]

/-- D-7r: the banked view column is `0`, not `vf`. -/
theorem storePostFoldDFwd (rl : Bool) (vf t : Nat) (as_ : List Int) (ws : Wstate) (a : Int)
    (tf vfd : Nat) :
    get? (as_.foldl (fun w a => storePostD w rl vf a t) ws).wFwd a = some (tf, vfd) →
    (tf = t ∧ vfd = 0) ∨ get? ws.wFwd a = some (tf, vfd) := by
  induction as_ generalizing ws with
  | nil => intro h; exact .inr h
  | cons b l ih =>
    intro hlk
    rcases ih _ hlk with h | hlk'
    · exact .inl h
    · simp only [storePostD] at hlk'
      by_cases h : b = a
      · subst h; rw [lookupInsert] at hlk'; injection hlk' with hlk'; injection hlk' with h1 h2
        exact .inl ⟨h1.symm, h2.symm⟩
      · rw [lookupInsertNe h] at hlk'; exact .inr hlk'

theorem storePostRunDFwdInv (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat)
    (a : Int) (tf vfd : Nat) :
    get? (storePostRunD ws rl vaddr vdata base n t).wFwd a = some (tf, vfd) →
    (tf = t ∧ vfd = 0) ∨ get? ws.wFwd a = some (tf, vfd) :=
  storePostFoldDFwd rl _ t _ ws a tf vfd

theorem storePostRunDVcap (ws : Wstate) (rl : Bool) (vaddr vdata : Nat) (base : Int) (n t : Nat) :
    vaddr ≤ (storePostRunD ws rl vaddr vdata base n t).wVcap := by
  simp only [storePostRunD, ctrlPostVcap]; omega

/-! ### THE DEPENDENCY-FREE RUN IS BELOW THE DEPENDENCY-CARRYING ONE -/

theorem loadPostAtMono (ws1 ws2 : Wstate) (aq : Bool) (vpre1 vpre2 : Nat) (a : Int) (t : Nat) :
    wsLe ws1 ws2 → ws1.wFwd = ws2.wFwd → vpre1 ≤ vpre2 →
    wsLe (loadPostAt ws1 aq vpre1 a t) (loadPostAt ws2 aq vpre2 a t) := by
  intro hle hfw hvp
  have hfv : fwdView ws1 aq a t = fwdView ws2 aq a t := by simp only [fwdView, hfw]
  obtain ⟨hcoh, hrO, hwO, hrN, hwN, hR, hpub, hvc⟩ := hle
  refine ⟨fun a' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : a' = a
    · subst h; rw [cohLoadPostAtEq, cohLoadPostAtEq, hfv]; have := hcoh a'; omega
    · rw [cohLoadPostAtNe _ _ _ _ _ _ h, cohLoadPostAtNe _ _ _ _ _ _ h]; exact hcoh a'
  all_goals simp only [loadPostAt, hfv]
  all_goals (try split) <;> omega

theorem loadPostFoldMono (aq : Bool) (vpre1 vpre2 : Nat) (ats : List (Int × Nat)) :
    vpre1 ≤ vpre2 → ∀ w1 w2, wsLe w1 w2 → w1.wFwd = w2.wFwd →
      wsLe (ats.foldl (fun w at_ => loadPostAt w aq vpre1 at_.1 at_.2) w1)
           (ats.foldl (fun w at_ => loadPostAt w aq vpre2 at_.1 at_.2) w2) := by
  intro hvp
  induction ats with
  | nil => intro w1 w2 hle _; exact hle
  | cons x l ih =>
    intro w1 w2 hle hfw
    exact ih _ _ (loadPostAtMono _ _ _ _ _ _ _ hle hfw hvp) hfw

/-- The BYTE-fold form. -/
theorem loadPostBytesDMono (ws : Wstate) (aq : Bool) (vaddr : Nat) (ats : List (Int × Nat)) :
    wsLe (loadPostBytes ws aq ats) (loadPostBytesD ws aq vaddr ats) :=
  loadPostFoldMono aq _ _ ats (loadVpreLoadVpreD ws aq vaddr) ws ws (wsLeRefl _) rfl

theorem loadPostRunDMono (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) :
    wsLe (loadPostRun ws aq base ts) (loadPostRunD ws aq vaddr base ts) :=
  ctrlPostMono _ _ _ _ (loadPostBytesDMono _ _ _ _) (Nat.le_max_right _ _)

/-! ## A RAISED CONTROL VIEW, AND NOTHING ELSE (`wsCtrlUp`) -/

def wsCtrlUp (w1 w2 : Wstate) : Prop := ∃ v, w2 = ctrlPost w1 v

theorem wsCtrlUpRefl (w : Wstate) : wsCtrlUp w w := ⟨0, (ctrlPost0 w).symm⟩

theorem wsCtrlUpLe (w1 w2 : Wstate) : wsCtrlUp w1 w2 → wsLe w1 w2 := by
  rintro ⟨v, rfl⟩; exact ctrlPostLe _ _

/-- Two control raises are one. -/
theorem ctrlPostCtrl (ws : Wstate) (v1 v2 : Nat) :
    ctrlPost (ctrlPost ws v1) v2 = ctrlPost ws (max v1 v2) := by
  simp only [ctrlPost]
  congr 1
  omega

theorem wsCtrlUpTrans {w1 w2 w3 : Wstate} : wsCtrlUp w1 w2 → wsCtrlUp w2 w3 → wsCtrlUp w1 w3 := by
  rintro ⟨v1, rfl⟩ ⟨v2, rfl⟩
  exact ⟨max v1 v2, ctrlPostCtrl _ _ _⟩

instance : Trans wsCtrlUp wsCtrlUp wsCtrlUp := ⟨wsCtrlUpTrans⟩

/-- The per-byte step functions COMMUTE with a control raise. -/
theorem loadPostAtCtrl (ws : Wstate) (aq : Bool) (v vpre : Nat) (a : Int) (t : Nat) :
    loadPostAt (ctrlPost ws v) aq vpre a t = ctrlPost (loadPostAt ws aq vpre a t) v := rfl

theorem loadPostCtrl (ws : Wstate) (aq : Bool) (v : Nat) (a : Int) (t : Nat) :
    loadPost (ctrlPost ws v) aq a t = ctrlPost (loadPost ws aq a t) v := rfl

theorem storePostCtrl (ws : Wstate) (rl : Bool) (v : Nat) (a : Int) (t : Nat) :
    storePost (ctrlPost ws v) rl a t = ctrlPost (storePost ws rl a t) v := rfl

theorem fencePostCtrl (ws : Wstate) (v : Nat) (pr pw sr sw : Bool) :
    fencePost (ctrlPost ws v) pr pw sr sw = ctrlPost (fencePost ws pr pw sr sw) v := rfl

theorem loadPostFoldCtrl (aq : Bool) (vpre : Nat) (ats : List (Int × Nat)) (v : Nat) :
    ∀ ws, ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) (ctrlPost ws v)
      = ctrlPost (ats.foldl (fun w at_ => loadPostAt w aq vpre at_.1 at_.2) ws) v := by
  induction ats with
  | nil => intro ws; rfl
  | cons x l ih => intro ws; simp only [List.foldl_cons]; rw [loadPostAtCtrl, ih]

theorem loadPostBytesDCtrl (ws : Wstate) (aq : Bool) (vaddr : Nat) (ats : List (Int × Nat)) (v : Nat) :
    loadPostBytesD (ctrlPost ws v) aq vaddr ats = ctrlPost (loadPostBytesD ws aq vaddr ats) v :=
  loadPostFoldCtrl aq _ ats v ws

theorem loadPostRunDCtrl (ws : Wstate) (aq : Bool) (vaddr : Nat) (base : Int) (ts : List Nat) (v : Nat) :
    loadPostRunD (ctrlPost ws v) aq vaddr base ts = ctrlPost (loadPostRunD ws aq vaddr base ts) v := by
  simp only [loadPostRunD]
  rw [loadPostBytesDCtrl, ctrlPostTbank, ctrlPostCtrl, ctrlPostCtrl]
  congr 1
  omega

/-- ... hence the SINGLE-BYTE run-level arms preserve the relation. -/
theorem wsCtrlUpLoad (ws1 ws2 : Wstate) (aq : Bool) (base : Int) (t : Nat) :
    wsCtrlUp ws1 ws2 → wsCtrlUp (loadPost ws1 aq base t) (loadPostRun ws2 aq base [t]) := by
  rintro ⟨v, rfl⟩
  refine ⟨max v ws1.wTbank, ?_⟩
  rw [loadPostRunSingle, loadPostCtrl, ctrlPostTbank, ctrlPostCtrl]

theorem wsCtrlUpStore (ws1 ws2 : Wstate) (rl : Bool) (base : Int) (t : Nat) :
    wsCtrlUp ws1 ws2 → wsCtrlUp (storePost ws1 rl base t) (storePostRun ws2 rl base 1 t) := by
  rintro ⟨v, rfl⟩
  refine ⟨max v ws1.wTbank, ?_⟩
  have h1 := storePostRunSingle (ctrlPost ws1 v) rl base (0 : BitVec 8) t
  simp only [List.length_singleton] at h1
  rw [h1, storePostCtrl, ctrlPostTbank, ctrlPostCtrl]

theorem wsCtrlUpFence (ws1 ws2 : Wstate) (pr pw sr sw : Bool) :
    wsCtrlUp ws1 ws2 → wsCtrlUp (fencePost ws1 pr pw sr sw) (fencePost ws2 pr pw sr sw) := by
  rintro ⟨v, rfl⟩
  exact ⟨v, fencePostCtrl _ _ _ _ _ _⟩

end Weak
