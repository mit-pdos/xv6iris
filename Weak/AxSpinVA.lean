/-
Weak: **the spinlock plan, PHASE 5 item (4), part 1** — the GENERIC first-label / label-CHAIN
certificate for a hart thread at an arbitrary Sail node, its soundness w.r.t. the first-label
property at every node the diverted run reaches through image-answered reads, and an evaluator.

Rocq: `iris/AxSpinVA.v` @ xxvzwolszwmp.

## What this file proves

* §1 `ekey`, `lkey` (a label's identity), `FOf K` (the label set of a key predicate),
  `keyFits` / `keyFitsb`, `rowRejectsKeys` / `rowRejectsKey1`: `rowRejects row k (FOf K)` from a
  key-level check.
* §2 `FEC img QE Q Ks m t`: an all-paths predicate on Sail trees (`EvA`'s shape: pin reads
  DEMONIC, no pin writes) whose memory nodes either END the chain (`fcMrdEnd` / `fcMwr` /
  `fcBar` / `fcSf`: the node's key is the LAST element) or, for a plain RAM read whose bytes are
  in the image, CONTINUE with the image value (`fcMrdGo`); `.pure` hands the remaining chain to
  `Q`; failure nodes are covered by `QE`.  `BFEC n Ks t`: from the boundary at `t`, for BOTH
  ticks, `riscvStep` is an `FEC` with the remaining chain continued at the next boundary.
* §3 SOUNDNESS.  `ireach img p i p'`: `p'` is reached from `p` by (image-pinned) administrative
  program steps, PLIC wires and exactly `i` RAM reads answered with IMAGE bytes.  `chainFirst`:
  if `hthr img Ks p`, then at every such `p'` with `Ks[i]? = some e`, the next
  non-administrative label from `⟨p', k⟩` along PINNED administrative steps has key `e`
  (`AxSpinVA.firstEvPin`).  `hthrBoundary`: `BFEC n Ks t` at a register file agreeing with `t`
  off the pins gives `hthr Ks` at the boundary node `.pure ()`.
* §4 THE EVALUATOR `fstep fuel len t` and `fstepSound`: `fstep fuel len t = some Ks →
  BFEC fuel Ks t`; `fstepChain` packages it with `chainFirst`.

## Deviations from Rocq

1. O2 STAGE C (fetch = pinned admin step `LIFetch`, no row item, no key).  Rocq's
   `fc_mrd_end` / `fc_mrd_go` covered every RAM read, fetches included (a Rocq fetch was a graph
   `LLoad`).  In Lean they take `akIfetch = false`, and a fetch node is the Lean-only
   constructor `FEC.fcIf`: it CONTINUES the chain (no key consumed) with the IMAGE bytes.  This is
   sound only along runs whose fetches are pinned to `img` (`WeakAxRealize.fetchPin img l`, the
   graph tier's fetch oracle, cf. `AxCjrWpd.pinnedBytes`).  Hence:
   - `hinvCStep`'s administrative half and `hthrAdmin` take `WeakAxRealize.fetchPin img l`;
   - `ireach`'s `irAdmin` constructor carries the pin;
   - `hthrFirst` / `chainFirst` / `fstepChain` conclude the Lean-only PINNED first-label property
     `AxSpinVA.firstEvPin img F s` (`AxSpinRow.firstEv` with administrative steps restricted to
     `fetchPin img`, `AxSpinVA.kstep0Pin`), NOT `AxSpinRow.firstEv` (whose administrative
     steps fetch ARBITRARY bytes: past a fetch no chain can be certified for it).
   - **`row_stuck_of_chain` is NOT PORTED** (open question): it would feed
     `AxSpinRow.rowStuckOfFirst`, whose `firstEv` / `rowStuckR` / `wpdMStuck` are unpinned.  A
     pinned `rowStuckR` + a pinned `wpdOfClosedRunGM` (the WPd step clause IS pinned, Q8) are
     needed first — an orchestrator decision outside this file.
2. Q7 (sfence marker): `fcIa` takes `sfAnnB n w = false` (an announce is `LInstr`, admin); the
   Lean-only constructor `FEC.fcSf` ENDS the chain at an SFENCE.VMA announce with the marker's
   key `EFn (false, false, false, false)`.  The evaluator does the same.
3. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` (`sig_seip` or
   `sig_meip`); `fch` answers a pin read with both pins `0#1`, then both `1#1` (as
   `AxSymEngine2.evb`), and requires both branches to agree.
4. LEAN-SAIL OUTCOMES: Rocq's stuck nodes `fc_gf` (GenericFail), `fc_dis` (Discard) and `fc_ext`
   (ExtraOutcome, covered by `QE`) ↦ ONE constructor `fcExt` at lean-sail's failure node
   `.impure (.error e)` (covered by `QE`; `QT` is `True`).  `choose`, `readRam`, `writeRam` are not
   covered (as Rocq's `Choose`).  `fcGcc` answers `(0 : Nat)`.
5. TYPES: `Z → option (bv 8)` ↦ `Image`; `mstate` ↦ `ExecSt` (`sregs` ↦ `regs`); `set_reg` ↦
   `ExecSt.setReg`; `register_lookup r rs` ↦ `rs r`; `N.to_nat n` ↦ `n : Nat`; `inl (w, None)` ↦
   `.Ok (w, none)`; `Interface.Ret tt` ↦ `.pure ()`; `default rs ors` ↦ `ors.getD rs`;
   `Ks !! i` ↦ `Ks[i]?`; the label-identity triple `(aq, base, n)` is right-nested
   (`x.1.2` ↦ `x.2.1`, `x.2` ↦ `x.2.2`); `F_of (eq e)` ↦ `FOf (Eq e)`; `bool_decide` ↦ `decide`.
   `pnode_step` carries `obar` (`hinvCStep` takes it).  `fstep` is `noncomputable` (`riscvStep`
   is); kernel evaluation (`decide +kernel`) is unaffected.
6. Lean-only helpers (file-qualified): `AxSpinVA.kstep0Pin`, `AxSpinVA.firstEvPin`,
   `AxSpinVA.erwLabelAdmin` (Rocq `erw_label_admin`, a duplicated name; = `AxCjrWpd`'s),
   `AxSpinVA.annAdmin`.

**Rocq → Lean name map.**  `ekey` `ekey` (`ERd`/`EWr`/`EFn`), `lkey` `lkey`, `lkey_rd` `lkeyRd`,
`lkey_fence` `lkeyFence`, `F_of` `FOf`, `key_fits` `keyFits`, `key_fitsb` `keyFitsb`,
`key_fitsb_spec` `keyFitsbSpec`, `fits_key` `fitsKey`, `row_rejects_keys` `rowRejectsKeys`,
`row_rejects_key1` `rowRejectsKey1`, `FEC` `FEC` (constructors `fc_ret` `fcRet`, `fc_rd` `fcRd`,
`fc_wr` `fcWr`, `fc_mrd_end` `fcMrdEnd`, `fc_mrd_go` `fcMrdGo`, `fc_mwr` `fcMwr`, `fc_bar`
`fcBar`, `fc_ia` `fcIa`, `fc_ba` `fcBa`, `fc_co` `fcCo`, `fc_tl` `fcTl`, `fc_te` `fcTe`, `fc_rx`
`fcRx`, `fc_ts` `fcTs`, `fc_tx` `fcTx`, `fc_cc` `fcCc`, `fc_msg` `fcMsg`, `fc_gcc` `fcGcc`,
`fc_gf`/`fc_dis`/`fc_ext` `fcExt`; Lean-only `fcIf`, `fcSf`), `QT` `QT`, `BFEC` `BFEC`, `hinvC`
`hinvC`, `erw_label_admin` `AxSpinVA.erwLabelAdmin`, `ebar_label_not_admin` `ebarLabelNotAdmin`,
`hinvC_step` `hinvCStep`, `hthr` `hthr`, `hthr_admin` `hthrAdmin`, `hthr_wire` `hthrWire`,
`hthr_first` `hthrFirst`, `ireach` `ireach` (`ir_refl` `irRefl`, `ir_admin` `irAdmin`,
`ir_wire` `irWire`, `ir_read` `irRead`), `chain_first` `chainFirst`, `hthr_boundary`
`hthrBoundary`, `fch` `fch`, `fch_sound` `fchSound`, `fstep` `fstep`, `fstep_sound`
`fstepSound`, `fstep_chain` `fstepChain`.

**Dropped / not ported:** `row_stuck_of_chain` (deviation 1; open question) and the `nadm`
tactic (inlined); the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxSymEngine2
import Weak.AxSpinRow
import Weak.AxCjrWpd

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-! # 1. Label identities -/

inductive ekey where
  | ERd (x : Bool × Int × Nat)
  | EWr (x : Bool × Int × Nat)
  | EFn (x : Bool × Bool × Bool × Bool)
  deriving DecidableEq

def lkey (l : Wlabel) : Option ekey :=
  match l with
  | LLoad aq _ base tvs _ => some (.ERd (aq, base, tvs.length))
  | LExLoad aq base tvs _ => some (.ERd (aq, base, tvs.length))
  | LStore rl base data _ _ => some (.EWr (rl, base, data.length))
  | LExStore rl base data _ _ => some (.EWr (rl, base, data.length))
  | LFence pr pw sr sw => some (.EFn (pr, pw, sr, sw))
  | _ => none

theorem lkeyRd (l : Wlabel) (x : Bool × Int × Nat) : wlRd l = some x → lkey l = some (.ERd x) := by
  cases l <;> simp [wlRd, lkey] <;> intro h <;> subst h <;> rfl

theorem lkeyFence (l : Wlabel) (x : Bool × Bool × Bool × Bool) :
    wlFence l = some x → lkey l = some (.EFn x) := by
  cases l <;> simp [wlFence, lkey] <;> intro h <;> subst h <;> rfl

/-- The label set of a key predicate. -/
def FOf (K : ekey → Prop) (l : Wlabel) : Prop := ∃ e, lkey l = some e ∧ K e

/-- A key FITS a row item: the identity half `fits` compares. -/
def keyFits (e : ekey) (lb : Lbl) : Prop :=
  match e with
  | .ERd x => aidentRd (aident lb) = some x
  | .EWr x => aidentWr (aident lb) = some x
  | .EFn x => aidentFence (aident lb) = some x

def keyFitsb (e : ekey) (lb : Lbl) : Bool :=
  match e with
  | .ERd x => decide (aidentRd (aident lb) = some x)
  | .EWr x => decide (aidentWr (aident lb) = some x)
  | .EFn x => decide (aidentFence (aident lb) = some x)

theorem keyFitsbSpec (e : ekey) (lb : Lbl) : keyFitsb e lb = true ↔ keyFits e lb := by
  cases e <;> simp [keyFitsb, keyFits]

theorem fitsKey (l : Wlabel) (lb : Lbl) (e : ekey) : lkey l = some e → fits l lb → keyFits e lb := by
  intro Hk Hf
  cases l <;> simp only [lkey, reduceCtorEq, Option.some.injEq] at Hk <;> subst Hk <;>
    rcases Hf with ⟨Hs, H⟩ | ⟨Hs, H⟩ | ⟨Hs, H⟩ <;>
    simp_all [wlRd, wlWr, wlFence, keyFits]

/-- The ROW half of `rowStuckOfFirst`, at the key level. -/
theorem rowRejectsKeys (row : List Lbl) (k : Nat) (K : ekey → Prop) :
    (∀ lb, row[k]? = some lb → ∀ e, K e → ¬ keyFits e lb) → rowRejects row k (FOf K) := by
  rintro H lb Hlb l ⟨e, He, HK⟩ Hf
  exact H lb Hlb e HK (fitsKey l lb e He Hf)

theorem rowRejectsKey1 (row : List Lbl) (k : Nat) (e : ekey) (lb : Lbl) :
    row[k]? = some lb → keyFitsb e lb = false → rowRejects row k (FOf (Eq e)) := by
  intro Hlb Hb
  apply rowRejectsKeys
  intro lb' Hlb' e' He' Hf
  subst He'
  rw [Hlb] at Hlb'
  cases Hlb'
  rw [← keyFitsbSpec] at Hf
  rw [Hf] at Hb
  cases Hb

/-! # 2. The chain certificate -/

section fec
variable (img : Image)

/-- THE CHAIN CERTIFICATE (see the header). -/
inductive FEC {X : Type} (QE : List ekey → Sail.Error exception → ExecSt → Prop)
    (Q : List ekey → X → ExecSt → Prop) : List ekey → SailM X → ExecSt → Prop where
  | fcRet (Ks : List ekey) (x : X) (t : ExecSt) : Q Ks x t → FEC QE Q Ks (.pure x) t
  | fcRd (Ks : List ekey) (r : Register) (k : RegisterType r → SailM X) (t : ExecSt) :
      (AxRunClose.pinReg r → ∀ v, FEC QE Q Ks (k v) t) →
      (¬ AxRunClose.pinReg r → FEC QE Q Ks (k (t.regs r)) t) →
      FEC QE Q Ks (.impure (.ok (.regRead r)) k) t
  | fcWr (Ks : List ekey) (r : Register) (v : RegisterType r) (k : PUnit → SailM X)
      (t : ExecSt) :
      ¬ AxRunClose.pinReg r → FEC QE Q Ks (k PUnit.unit) (t.setReg r v) →
      FEC QE Q Ks (.impure (.ok (.regWrite r v)) k) t
  /-- a RAM data read that ENDS the chain (any bytes, any non-fetch kind) -/
  | fcMrdEnd (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
      FEC QE Q [.ERd ((classify req.access_kind).akSync, paZ req.pa, n)]
        (.impure (.ok (.memRead n va req)) k) t
  /-- a plain RAM read in the IMAGE that CONTINUES the chain with the image bytes -/
  | fcMrdGo (e : ekey) (Ks : List ekey) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      Ks ≠ [] → devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
      (classify req.access_kind).akLatest = false →
      e = .ERd ((classify req.access_kind).akSync, paZ req.pa, n) →
      imgBytes img (paZ req.pa) n = some vs →
      FEC QE Q Ks (k (.Ok (wordOfBytes n vs, none))) t →
      FEC QE Q (e :: Ks) (.impure (.ok (.memRead n va req)) k) t
  /-- (Lean-only, Stage C) a FETCH: administrative, continues with the IMAGE bytes -/
  | fcIf (Ks : List ekey) (n va : Nat)
      (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = some vs →
      FEC QE Q Ks (k (.Ok (wordOfBytes n vs, none))) t →
      FEC QE Q Ks (.impure (.ok (.memRead n va req)) k) t
  | fcMwr (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false →
      FEC QE Q [.EWr ((classify req.access_kind).akSync, paZ req.pa, n)]
        (.impure (.ok (.memWrite n va req)) k) t
  | fcBar (b : barrier_kind) (k : Unit → SailM X) (t : ExecSt) (x : Bool × Bool × Bool × Bool) :
      wlFence (ebarLabel b) = some x → FEC QE Q [.EFn x] (.impure (.ok (.barrier b)) k) t
  | fcIa (Ks : List ekey) (n : Nat) (w : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = false → FEC QE Q Ks (k ()) t →
      FEC QE Q Ks (.impure (.ok (.instrAnnounce n w)) k) t
  /-- (Lean-only, Q7) the SFENCE.VMA marker ENDS the chain -/
  | fcSf (n : Nat) (w : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      sfAnnB n w = true →
      FEC QE Q [.EFn (false, false, false, false)] (.impure (.ok (.instrAnnounce n w)) k) t
  | fcBa (Ks : List ekey) (n : Nat) (a : BitVec n) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.branchAnnounce n a)) k) t
  | fcCo (Ks : List ekey) (c : Arch.cache_op) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.cacheOp c)) k) t
  | fcTl (Ks : List ekey) (c : Arch.tlb_op) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.tlbi c)) k) t
  | fcTe (Ks : List ekey) (f : Arch.fault) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.takeException f)) k) t
  | fcRx (Ks : List ekey) (a : Arch.pa) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.returnException a)) k) t
  | fcTs (Ks : List ekey) (a : Arch.trans_start) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.translationStart a)) k) t
  | fcTx (Ks : List ekey) (a : Arch.trans_end) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.translationEnd a)) k) t
  | fcCc (Ks : List ekey) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok .cycleCount) k) t
  | fcMsg (Ks : List ekey) (a : String) (k : Unit → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k ()) t → FEC QE Q Ks (.impure (.ok (.message a)) k) t
  | fcGcc (Ks : List ekey) (k : Nat → SailM X) (t : ExecSt) :
      FEC QE Q Ks (k (0 : Nat)) t → FEC QE Q Ks (.impure (.ok .getCycleCount) k) t
  /-- failure nodes: no step at all (Rocq `fc_gf` / `fc_dis` / `fc_ext`) -/
  | fcExt (Ks : List ekey) (e : Sail.Error exception) (k : Empty → SailM X) (t : ExecSt) :
      QE Ks e t → FEC QE Q Ks (.impure (.error e) k) t

def QT : List ekey → Sail.Error exception → ExecSt → Prop := fun _ _ _ => True

/-- From the boundary at `t`: both ticks, at most `n` boundaries. -/
def BFEC : Nat → List ekey → ExecSt → Prop
  | 0, _, _ => False
  | n + 1, Ks, t => ∀ tick, FEC img QT (fun Ks' _ t' => BFEC n Ks' t') Ks (riscvStep tick) t

/-! # 3. Soundness -/

def hinvC (Ks : List ekey) (m : SailM Unit) (rs : RegFile) : Prop :=
  ∃ n t, regsAgree AxRunClose.pinReg rs t.regs ∧
    FEC img QT (fun Ks' _ t' => BFEC img n Ks' t') Ks m t

theorem AxSpinVA.erwLabelAdmin (k : ErwKind) : lbAdmin true (erwLabel k) :=
  AxCjrWpd.erwLabelAdmin k

theorem ebarLabelNotAdmin (b : barrier_kind) : ¬ lbAdmin true (ebarLabel b) := by
  unfold ebarLabel
  rcases ebarNow b with _ | ⟨_, _, _, _⟩ <;> simp [lbAdmin]

/-- (Lean-only) A non-sfence announce is administrative. -/
theorem AxSpinVA.annAdmin (n : Nat) (w : BitVec n) (h : sfAnnB n w = false) :
    lbAdmin true (annLabel n w) := by
  simp [annLabel, h, lbAdmin]

theorem hinvCStep (Ks : List ekey) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    hinvC img Ks m rs → pnodeStep m rs ib d l m' ors fn' d' oib obar →
    (lbAdmin true l → WeakAxRealize.fetchPin img l → fn' = none ∧ hinvC img Ks m' (ors.getD rs)) ∧
    (¬ lbAdmin true l → ∃ e Ks', Ks = e :: Ks' ∧ lkey l = some e ∧
      (Ks' ≠ [] → ∀ x, wlRd l = some x → imgBytes img x.2.1 x.2.2 = some (wlRvals l) →
        fn' = none ∧ ors = none ∧ hinvC img Ks' m' rs)) := by
  rintro ⟨n, t0, Hag, H⟩ Hps
  -- the silent-node pattern: an admin step to the continuation, same chain, same state
  have silent : ∀ (k' : SailM Unit), FEC img QT (fun Ks' _ t' => BFEC img n Ks' t') Ks k' t0 →
      (l = LSilent ∧ m' = k' ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none) →
      (lbAdmin true l → WeakAxRealize.fetchPin img l →
          fn' = none ∧ hinvC img Ks m' (ors.getD rs)) ∧
      (¬ lbAdmin true l → ∃ e Ks', Ks = e :: Ks' ∧ lkey l = some e ∧
        (Ks' ≠ [] → ∀ x, wlRd l = some x → imgBytes img x.2.1 x.2.2 = some (wlRvals l) →
          fn' = none ∧ ors = none ∧ hinvC img Ks' m' rs)) := by
    rintro k' Hk ⟨rfl, rfl, rfl, rfl, -, -, -⟩
    exact ⟨fun _ _ => ⟨rfl, n, t0, Hag, Hk⟩, fun Hna => absurd trivial Hna⟩
  cases H with
  | fcRet Ks x t HQ =>
    obtain ⟨tick, rfl, rfl, rfl, rfl, -, -, -⟩ := Hps
    refine ⟨fun _ _ => ⟨rfl, ?_⟩, fun Hna => absurd rfl Hna⟩
    cases n with
    | zero => exact HQ.elim
    | succ n => exact ⟨n, t0, Hag, HQ tick⟩
  | fcRd Ks r k t H1 H2 =>
    obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := Hps
    refine ⟨fun _ _ => ⟨rfl, n, t0, Hag, ?_⟩, fun Hna => absurd trivial Hna⟩
    by_cases hp : AxRunClose.pinReg r
    · exact H1 hp _
    · rw [Hag r hp]; exact H2 hp
  | fcWr Ks r v k t Hs Hk =>
    obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := Hps
    refine ⟨fun _ _ => ⟨rfl, n, t0.setReg r v, ?_, Hk⟩,
      fun Hna => absurd (AxSpinVA.erwLabelAdmin _) Hna⟩
    exact regsAgreeSet _ _ _ r v Hag
  | fcMrdEnd n0 va req k t Hdev Hif =>
    simp only [pnodeStep, Hdev, Bool.false_eq_true, ↓reduceIte] at Hps
    rcases Hps with ⟨Hif', -⟩ | ⟨-, Hps⟩
    · rw [Hif] at Hif'; cases Hif'
    rcases Hps with ⟨-, w, tvs, Hlen, -, rfl, -⟩ | ⟨-, w, tvs, Hlen, -, rfl, -⟩
    · refine ⟨fun Ha => Ha.elim, fun _ => ⟨_, [], rfl, by simp [lkey, Hlen], ?_⟩⟩
      intro Hne; exact absurd rfl Hne
    · refine ⟨fun Ha => Ha.elim, fun _ => ⟨_, [], rfl, by simp [lkey, Hlen], ?_⟩⟩
      intro Hne; exact absurd rfl Hne
  | fcMrdGo e Ks n0 va req k t vs HKs Hdev Hif Hlat He Himg Hk =>
    simp only [pnodeStep, Hdev, Bool.false_eq_true, ↓reduceIte] at Hps
    rcases Hps with ⟨Hif', -⟩ | ⟨-, Hps⟩
    · rw [Hif] at Hif'; cases Hif'
    rcases Hps with ⟨-, w, tvs, Hlen, Hby, rfl, rfl, rfl, rfl, -, -, -⟩ | ⟨Hlat', -⟩
    · refine ⟨fun Ha => Ha.elim, fun _ => ⟨_, Ks, rfl, by simp [lkey, Hlen, He], ?_⟩⟩
      intro _ x Hx Hx'
      simp only [wlRd, Option.some.injEq] at Hx
      subst Hx
      simp only [wlRvals, Hlen, Himg, Option.some.injEq] at Hx'
      refine ⟨rfl, rfl, n, t0, Hag, ?_⟩
      have Hw : w = wordOfBytes n0 vs := by
        rw [Hx']; exact bytesWordEq n0 w tvs Hlen Hby
      rw [Hw]; exact Hk
    · rw [Hlat] at Hlat'; cases Hlat'
  | fcIf Ks n0 va req k t vs Hdev Hif Himg Hk =>
    simp only [pnodeStep, Hdev, Bool.false_eq_true, ↓reduceIte] at Hps
    rcases Hps with ⟨-, w, tvs, Hlen, Hby, rfl, rfl, rfl, rfl, -, -, -⟩ | ⟨Hif', -⟩
    · refine ⟨fun _ Hpin => ⟨rfl, n, t0, Hag, ?_⟩, fun Hna => absurd rfl Hna⟩
      obtain ⟨Hvl, Hvs⟩ := imgBytesSpec img _ _ vs Himg
      have Hsnd := AxCjrWpd.pinnedBytes img (paZ req.pa) tvs vs (by omega)
        (fun j hj => Hvs j (by omega)) Hpin
      have Hw : w = wordOfBytes n0 vs := by
        rw [← Hsnd]; exact bytesWordEq n0 w tvs Hlen Hby
      rw [Hw]; exact Hk
    · rw [Hif] at Hif'; cases Hif'
  | fcMwr n0 va req k t Hdev =>
    simp only [pnodeStep, Hdev, Bool.false_eq_true, ↓reduceIte] at Hps
    cases hv : req.value with
    | none => rw [hv] at Hps; exact Hps.elim
    | some v =>
      rw [hv] at Hps
      obtain ⟨-, Hps⟩ := Hps
      rcases Hps with ⟨-, rfl, -⟩ | ⟨-, ⟨rfl, -⟩ | ⟨rfl, rfl, rfl, rfl, -, -, -⟩⟩
      · refine ⟨fun Ha => Ha.elim, fun _ => ⟨_, [], rfl, by simp [lkey, wbytesLength], ?_⟩⟩
        intro Hne; exact absurd rfl Hne
      · refine ⟨fun Ha => Ha.elim, fun _ => ⟨_, [], rfl, by simp [lkey, wbytesLength], ?_⟩⟩
        intro Hne; exact absurd rfl Hne
      · exact ⟨fun _ _ => ⟨rfl, n, t0, Hag, .fcMwr n0 va req k t0 Hdev⟩,
          fun Hna => absurd trivial Hna⟩
  | fcBar b k t x Hx =>
    obtain ⟨rfl, -, -, -, -, -, -⟩ := Hps
    refine ⟨fun Ha => absurd Ha (ebarLabelNotAdmin b), fun _ => ⟨_, [], rfl, lkeyFence _ _ Hx, ?_⟩⟩
    intro Hne; exact absurd rfl Hne
  | fcIa Ks n0 w k t Hs Hk =>
    obtain ⟨rfl, rfl, rfl, rfl, -, -, -⟩ := Hps
    exact ⟨fun _ _ => ⟨rfl, n, t0, Hag, Hk⟩, fun Hna => absurd (AxSpinVA.annAdmin n0 w Hs) Hna⟩
  | fcSf n0 w k t Hs =>
    obtain ⟨rfl, -, -, -, -, -, -⟩ := Hps
    have Hl : annLabel n0 w = LFence false false false false := by simp [annLabel, Hs]
    rw [Hl]
    refine ⟨fun Ha => Ha.elim, fun _ => ⟨_, [], rfl, rfl, ?_⟩⟩
    intro Hne; exact absurd rfl Hne
  | fcBa Ks n0 a k t Hk => exact silent _ Hk Hps
  | fcCo Ks c k t Hk => exact silent _ Hk Hps
  | fcTl Ks c k t Hk => exact silent _ Hk Hps
  | fcTe Ks f k t Hk => exact silent _ Hk Hps
  | fcRx Ks a k t Hk => exact silent _ Hk Hps
  | fcTs Ks a k t Hk => exact silent _ Hk Hps
  | fcTx Ks a k t Hk => exact silent _ Hk Hps
  | fcCc Ks k t Hk => exact silent _ Hk Hps
  | fcMsg Ks a k t Hk => exact silent _ Hk Hps
  | fcGcc Ks k t Hk => exact silent _ Hk Hps
  | fcExt Ks e k t _ => exact Hps.elim

/-- The hart-thread invariant. -/
def hthr (Ks : List ekey) (p : Pexv6) : Prop :=
  ∃ cpu m rs ib, p = .PHart cpu m rs none ib ∧ hinvC img Ks m rs

theorem hthrAdmin (Ks : List ekey) (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    hthr img Ks p → pstepProg p d l p' d' → lbAdmin true l → WeakAxRealize.fetchPin img l →
    hthr img Ks p' := by
  rintro ⟨cpu, m, rs, ib, rfl, H⟩ Hps Hadm Hpin
  cases p' with
  | PDisk _ => exact Hps.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, Hn, -⟩ := Hps
    obtain ⟨rfl, H'⟩ := (hinvCStep img _ _ _ _ _ _ _ _ _ _ _ _ H Hn).1 Hadm Hpin
    exact ⟨_, m', ors.getD rs, oib.getD ib, rfl, H'⟩

theorem hthrWire (Ks : List ekey) (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    hthr img Ks p → pstepWire p d l p' d' → hthr img Ks p' := by
  rintro ⟨cpu, m, rs, ib, rfl, n, t, Hag, H⟩ Hw
  obtain ⟨-, cpu', m', rs', fn', ib', mm, b, k, Hp, -, -, rfl⟩ := pstepWireInv _ _ _ _ _ Hw
  injection Hp with h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  refine ⟨cpu, m, pinSet rs mm b, ib, rfl, n, t, ?_, H⟩
  intro r hr
  rw [← AxRunClose.pinSetAgree rs mm b r hr]
  exact Hag r hr

/-- (Lean-only, deviation 1) An administrative step whose fetch (if any) is pinned to `img`, or
a wire (both keep the position). -/
def AxSpinVA.kstep0Pin (a b : Athread) : Prop :=
  (b.atK = a.atK ∧ ∃ d l d', lbAdmin true l ∧ WeakAxRealize.fetchPin img l ∧
    pstepProg a.atP d l b.atP d') ∨
  awire a b

/-- (Lean-only, deviation 1) `firstEv` along PINNED administrative steps. -/
def AxSpinVA.firstEvPin (F : Wlabel → Prop) (s : Athread) : Prop :=
  ∀ s2, rtc (AxSpinVA.kstep0Pin img) s s2 →
    ∀ d l p' d', pstepProg s2.atP d l p' d' → ¬ lbAdmin true l → F l

theorem hthrFirst (e : ekey) (Ks : List ekey) (p : Pexv6) (k : Nat) :
    hthr img (e :: Ks) p → AxSpinVA.firstEvPin img (FOf (Eq e)) ⟨p, k⟩ := by
  intro H0 s2 Hr
  have Hinv : hthr img (e :: Ks) s2.atP := by
    induction Hr with
    | refl => exact H0
    | tail _ Hyz IH =>
      rcases Hyz with ⟨-, d, l, d', Hadm, Hpin, Hps⟩ | ⟨-, d, d', Hw⟩
      · exact hthrAdmin img _ _ _ _ _ _ IH Hps Hadm Hpin
      · exact hthrWire img _ _ _ _ _ _ IH Hw
  intro d l p' d' Hps Hna
  obtain ⟨cpu, m, rs, ib, Hp, H⟩ := Hinv
  rw [Hp] at Hps
  cases p' with
  | PDisk _ => exact Hps.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨-, ors, oib, obar, -, -, Hn, -⟩ := Hps
    obtain ⟨e', Ks', He, Hk, -⟩ := (hinvCStep img _ _ _ _ _ _ _ _ _ _ _ _ H Hn).2 Hna
    injection He with He1 _
    subst He1
    exact ⟨e, Hk, rfl⟩

/-- Reachability through (pinned) administrative steps, wires and IMAGE-answered reads. -/
inductive ireach : Pexv6 → Nat → Pexv6 → Prop where
  | irRefl (p : Pexv6) : ireach p 0 p
  | irAdmin (p p' : Pexv6) (i : Nat) (p'' : Pexv6) :
      (∃ d l d', lbAdmin true l ∧ WeakAxRealize.fetchPin img l ∧ pstepProg p d l p' d') →
      ireach p' i p'' → ireach p i p''
  | irWire (p p' : Pexv6) (i : Nat) (p'' : Pexv6) :
      (∃ d l d', pstepWire p d l p' d') → ireach p' i p'' → ireach p i p''
  | irRead (p p' : Pexv6) (i : Nat) (p'' : Pexv6) :
      (∃ d l d' x, pstepProg p d l p' d' ∧ wlRd l = some x ∧
        imgBytes img x.2.1 x.2.2 = some (wlRvals l)) →
      ireach p' i p'' → ireach p (i + 1) p''

/-- THE CHAIN THEOREM. -/
theorem chainFirst (Ks : List ekey) (p : Pexv6) (i : Nat) (p' : Pexv6) (e : ekey) (k : Nat) :
    hthr img Ks p → ireach img p i p' → Ks[i]? = some e →
    AxSpinVA.firstEvPin img (FOf (Eq e)) ⟨p', k⟩ := by
  intro H Hr
  induction Hr generalizing Ks with
  | irRefl p =>
    intro He
    cases Ks with
    | nil => simp at He
    | cons e0 Ks =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at He
      subst He
      exact hthrFirst img _ _ _ _ H
  | irAdmin p p' i p'' Hs _ IH =>
    obtain ⟨d, l, d', Hadm, Hpin, Hps⟩ := Hs
    exact IH Ks (hthrAdmin img _ _ _ _ _ _ H Hps Hadm Hpin)
  | irWire p p' i p'' Hs _ IH =>
    obtain ⟨d, l, d', Hw⟩ := Hs
    exact IH Ks (hthrWire img _ _ _ _ _ _ H Hw)
  | irRead p p' i p'' Hs _ IH =>
    intro He
    obtain ⟨d, l, d', x, Hps, Hx, Himg⟩ := Hs
    obtain ⟨cpu, m, rs, ib, rfl, H⟩ := H
    cases p' with
    | PDisk _ => exact Hps.elim
    | PHart cpu' m' rs' fn' ib' =>
      obtain ⟨rfl, ors, oib, obar, rfl, rfl, Hn, -⟩ := Hps
      have Hna : ¬ lbAdmin true l := rdNotAdmin l x Hx
      obtain ⟨e0, Ks', rfl, -, Hc⟩ := (hinvCStep img _ _ _ _ _ _ _ _ _ _ _ _ H Hn).2 Hna
      simp only [List.getElem?_cons_succ] at He
      have HKs' : Ks' ≠ [] := by rintro rfl; simp at He
      obtain ⟨rfl, rfl, H'⟩ := Hc HKs' x Hx Himg
      exact IH Ks' ⟨cpu', m', rs, oib.getD ib, rfl, H'⟩ He

/-- The boundary node. -/
theorem hthrBoundary (n : Nat) (Ks : List ekey) (t : ExecSt) (cpu : CPU) (rs : RegFile)
    (ib : Ibch) :
    BFEC img n Ks t → regsAgree AxRunClose.pinReg rs t.regs →
    hthr img Ks (.PHart cpu (.pure ()) rs none ib) :=
  fun HB Hag => ⟨cpu, .pure (), rs, ib, rfl, n, t, Hag, .fcRet Ks () t HB⟩

/-! # 4. The evaluator -/

def fch {X : Type} (c : Nat → X → ExecSt → Option (List ekey)) :
    Nat → SailM X → ExecSt → Option (List ekey)
  | len, .pure x, t => c len x t
  | _, .impure (.error _) _, _ => some []
  | len, .impure (.ok o) k, t =>
    match o, k with
    | .regRead r, k =>
      if r = .sig_seip ∨ r = .sig_meip then
        let a := fch c len (k (((t.regs.set .sig_seip 0#1).set .sig_meip 0#1) r)) t
        let b := fch c len (k (((t.regs.set .sig_seip 1#1).set .sig_meip 1#1) r)) t
        if a = b then a else none
      else fch c len (k (t.regs r)) t
    | .regWrite r v, k =>
      if r = .sig_seip ∨ r = .sig_meip then none else fch c len (k PUnit.unit) (t.setReg r v)
    | .memRead n _ req, k =>
      if devAddr req.pa then none
      else if (classify req.access_kind).akIfetch then
        match imgBytes img (paZ req.pa) n with
        | some vs => fch c len (k (.Ok (wordOfBytes n vs, none))) t
        | none => none
      else
        match len with
        | 0 => none
        | 1 => some [.ERd ((classify req.access_kind).akSync, paZ req.pa, n)]
        | len' + 2 =>
          if (classify req.access_kind).akLatest then
            some [.ERd ((classify req.access_kind).akSync, paZ req.pa, n)]
          else
            match imgBytes img (paZ req.pa) n with
            | some vs =>
              match fch c (len' + 1) (k (.Ok (wordOfBytes n vs, none))) t with
              | some (e' :: Ks) =>
                some (.ERd ((classify req.access_kind).akSync, paZ req.pa, n) :: e' :: Ks)
              | _ => some [.ERd ((classify req.access_kind).akSync, paZ req.pa, n)]
            | none => some [.ERd ((classify req.access_kind).akSync, paZ req.pa, n)]
    | .memWrite n _ req, _ =>
      if devAddr req.pa then none
      else
        match len with
        | 0 => none
        | _ + 1 => some [.EWr ((classify req.access_kind).akSync, paZ req.pa, n)]
    | .barrier b, _ =>
      match len, wlFence (ebarLabel b) with
      | _ + 1, some x => some [.EFn x]
      | _, _ => none
    | .instrAnnounce n w, k =>
      if sfAnnB n w then
        match len with
        | 0 => none
        | _ + 1 => some [.EFn (false, false, false, false)]
      else fch c len (k ()) t
    | .branchAnnounce _ _, k => fch c len (k ()) t
    | .cacheOp _, k => fch c len (k ()) t
    | .tlbi _, k => fch c len (k ()) t
    | .takeException _, k => fch c len (k ()) t
    | .returnException _, k => fch c len (k ()) t
    | .translationStart _, k => fch c len (k ()) t
    | .translationEnd _, k => fch c len (k ()) t
    | .cycleCount, k => fch c len (k ()) t
    | .message _, k => fch c len (k ()) t
    | .getCycleCount, k => fch c len (k (0 : Nat)) t
    | _, _ => none

theorem fchSound {X : Type} (c : Nat → X → ExecSt → Option (List ekey))
    (Q : List ekey → X → ExecSt → Prop)
    (Hc : ∀ len x t Ks, c len x t = some Ks → Q Ks x t) (m : SailM X) :
    ∀ len t Ks, fch img c len m t = some Ks → FEC img (fun _ _ _ => True) Q Ks m t := by
  induction m with
  | pure y => intro len t Ks Hf; exact .fcRet Ks y t (Hc _ _ _ _ Hf)
  | impure call k ih =>
    intro len t Ks Hf
    cases call with
    | error e => exact .fcExt Ks e k t trivial
    | ok o =>
      cases o
      case regRead r =>
        simp only [fch] at Hf
        refine .fcRd Ks r k t ?_ ?_
        · intro hp v
          have hp' : r = .sig_seip ∨ r = .sig_meip := hp
          rw [if_pos hp'] at Hf
          by_cases hab : fch img c len (k (((t.regs.set .sig_seip 0#1).set .sig_meip 0#1) r)) t =
              fch img c len (k (((t.regs.set .sig_seip 1#1).set .sig_meip 1#1) r)) t
          · rw [if_pos hab] at Hf
            have Hf2 := hab ▸ Hf
            rcases hp with rfl | rfl <;> rcases bv1_cases v with rfl | rfl
            · exact ih _ _ _ _ (by simpa [RegFile.set_same, RegFile.set_other] using Hf)
            · exact ih _ _ _ _ (by simpa [RegFile.set_same, RegFile.set_other] using Hf2)
            · exact ih _ _ _ _ (by simpa [RegFile.set_same] using Hf)
            · exact ih _ _ _ _ (by simpa [RegFile.set_same] using Hf2)
          · rw [if_neg hab] at Hf; cases Hf
        · intro hp
          have hp' : ¬ (r = .sig_seip ∨ r = .sig_meip) := hp
          rw [if_neg hp'] at Hf
          exact ih _ _ _ _ Hf
      case regWrite r v =>
        simp only [fch] at Hf
        by_cases hp : r = .sig_seip ∨ r = .sig_meip
        · rw [if_pos hp] at Hf; cases Hf
        · rw [if_neg hp] at Hf
          exact .fcWr Ks r v k t hp (ih _ _ _ _ Hf)
      case memRead n va req =>
        cases hd : devAddr req.pa
        · cases hif : (classify req.access_kind).akIfetch
          · rw [fch.eq_def] at Hf
            simp only [hd, hif, Bool.false_eq_true, ↓reduceIte] at Hf
            rcases len with _ | _ | len'
            · cases Hf
            · cases Hf; exact .fcMrdEnd n va req k t hd hif
            · cases hl : (classify req.access_kind).akLatest
              · simp only [hl, Bool.false_eq_true, ↓reduceIte] at Hf
                cases hv : imgBytes img (paZ req.pa) n with
                | none => rw [hv] at Hf; cases Hf; exact .fcMrdEnd n va req k t hd hif
                | some vs =>
                  simp only [hv] at Hf
                  cases hk : fch img c (len' + 1) (k (.Ok (wordOfBytes n vs, none))) t with
                  | none => rw [hk] at Hf; cases Hf; exact .fcMrdEnd n va req k t hd hif
                  | some Ks' =>
                    rw [hk] at Hf
                    cases Ks' with
                    | nil => cases Hf; exact .fcMrdEnd n va req k t hd hif
                    | cons e' Ks'' =>
                      cases Hf
                      exact .fcMrdGo _ _ n va req k t vs (by simp) hd hif hl rfl hv
                        (ih _ _ _ _ hk)
              · simp only [hl, ↓reduceIte] at Hf
                cases Hf; exact .fcMrdEnd n va req k t hd hif
          · rw [fch.eq_def] at Hf
            simp only [hd, hif, Bool.false_eq_true, ↓reduceIte] at Hf
            cases hv : imgBytes img (paZ req.pa) n with
            | none => rw [hv] at Hf; cases Hf
            | some vs =>
              rw [hv] at Hf
              exact .fcIf Ks n va req k t vs hd hif hv (ih _ _ _ _ Hf)
        · rw [fch.eq_def] at Hf
          simp [hd] at Hf
      case memWrite n va req =>
        simp only [fch] at Hf
        cases hd : devAddr req.pa
        · simp only [hd, Bool.false_eq_true, ↓reduceIte] at Hf
          rcases len with _ | len'
          · cases Hf
          · cases Hf; exact .fcMwr n va req k t hd
        · simp [hd] at Hf
      case barrier b =>
        simp only [fch] at Hf
        rcases len with _ | len'
        · cases Hf
        · cases hx : wlFence (ebarLabel b) with
          | none => rw [hx] at Hf; cases Hf
          | some x => rw [hx] at Hf; cases Hf; exact .fcBar b k t x hx
      case instrAnnounce n w =>
        simp only [fch] at Hf
        cases hs : sfAnnB n w
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] at Hf
          exact .fcIa Ks n w k t hs (ih _ _ _ _ Hf)
        · simp only [hs, ↓reduceIte] at Hf
          rcases len with _ | len'
          · cases Hf
          · cases Hf; exact .fcSf n w k t hs
      case branchAnnounce n a => exact .fcBa Ks n a k t (ih _ _ _ _ Hf)
      case cacheOp c' => exact .fcCo Ks c' k t (ih _ _ _ _ Hf)
      case tlbi c' => exact .fcTl Ks c' k t (ih _ _ _ _ Hf)
      case takeException c' => exact .fcTe Ks c' k t (ih _ _ _ _ Hf)
      case returnException c' => exact .fcRx Ks c' k t (ih _ _ _ _ Hf)
      case translationStart c' => exact .fcTs Ks c' k t (ih _ _ _ _ Hf)
      case translationEnd c' => exact .fcTx Ks c' k t (ih _ _ _ _ Hf)
      case cycleCount => exact .fcCc Ks k t (ih _ _ _ _ Hf)
      case message c' => exact .fcMsg Ks c' k t (ih _ _ _ _ Hf)
      case getCycleCount => exact .fcGcc Ks k t (ih _ _ _ _ Hf)
      all_goals simp [fch] at Hf

/-- The boundary evaluator: both ticks must agree. -/
noncomputable def fstep : Nat → Nat → ExecSt → Option (List ekey)
  | 0, _, _ => none
  | f + 1, len, t =>
    let a := fch img (fun len' _ t' => fstep f len' t') len (riscvStep false) t
    let b := fch img (fun len' _ t' => fstep f len' t') len (riscvStep true) t
    if a = b then a else none

theorem fstepSound (fuel : Nat) : ∀ len t Ks, fstep img fuel len t = some Ks → BFEC img fuel Ks t := by
  induction fuel with
  | zero => intro len t Ks Hf; cases Hf
  | succ f IH =>
    intro len t Ks Hf
    simp only [fstep] at Hf
    split at Hf
    · rename_i Hab
      have Hc : ∀ len' (x : Unit) t' Ks', fstep img f len' t' = some Ks' → BFEC img f Ks' t' :=
        fun len' _ t' Ks' H => IH len' t' Ks' H
      intro tick
      cases tick
      · exact fchSound img _ (fun Ks' _ t' => BFEC img f Ks' t') Hc _ len t Ks Hf
      · exact fchSound img _ (fun Ks' _ t' => BFEC img f Ks' t') Hc _ len t Ks (Hab ▸ Hf)
    · cases Hf

/-- Packaged: the evaluator's chain at the boundary. -/
theorem fstepChain (fuel len : Nat) (t : ExecSt) (Ks : List ekey) (cpu : CPU) (rs : RegFile)
    (ib : Ibch) (p' : Pexv6) (i : Nat) (e : ekey) (k : Nat) :
    fstep img fuel len t = some Ks → regsAgree AxRunClose.pinReg rs t.regs →
    ireach img (.PHart cpu (.pure ()) rs none ib) i p' → Ks[i]? = some e →
    AxSpinVA.firstEvPin img (FOf (Eq e)) ⟨p', k⟩ := by
  intro Hf Hag Hr He
  exact chainFirst img _ _ _ _ _ _ (hthrBoundary img _ _ _ _ _ _ (fstepSound img _ _ _ _ Hf) Hag)
    Hr He

end fec

end Weak
