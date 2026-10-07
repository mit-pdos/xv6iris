/-
Weak: **the PATH interpreter `execA`** — an SC-style functional certificate whose success IS an
`AxSymEngine` `EvA` certificate.

Rocq: `iris/AxSpineOk.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`EvA` is an all-paths predicate that forbids, ON THE PATH TAKEN: device reads, `ak_latest`
reads, memory writes, barriers and any access to the PLIC pins other than a demonic read.  An
SC fact `exec m s = some _` cannot witness any of these (`exec` reads devices silently,
reads/writes the pins like any register and ignores access kinds), and a syntactic all-branches
footprint cannot be proved for any function whose code merely CONTAINS such a branch (the MMIO
arm of `checked_mem_read`, the reserved-read arm of `update_and_write_pte`, a page-table walk
whose later PTE addresses are computed from read values).  So the memory-touching spine of the
S-mode fetch is REPLAYED at `execA` (`exec` with those arms made stuck, the RAM arm unchanged,
reading `s.mem`), while every REGISTER-ONLY callee is transferred from its UNCHANGED SC `exec`
lemma by the fail-tolerant syntactic footprint `rfF` (`execAOfRfF`: failure outcomes are
allowed, since `exec` is stuck there anyway).

§1 `execA`/`execAR` (base / early-return monad) and their bind kit.
§2 THE BRIDGE `execAEvA`: `execA m s = some (x, s')` ⇒ `EvA (imgOf s) … m t` at every `t` with
   `s`'s registers — the image is the memory `s` reads, as an `Int`-indexed map (`imgOf`); the
   RAM arm's no-wrap guard makes the two byte spellings agree.
§3 `rfF` and `execAOfRfF` / `execAROfRfF`; the tactic `rff_solve`.

## Deviations from Rocq

1. O2 STAGE C (as `AxSymEngine` deviation 1): `ramOk` DROPS Rocq's `negb (ak_coh …)` conjunct.
   In Rocq the model's instruction fetch is a plain (`ak_coh = false`) read; in Lean it is an
   `AK_ifetch` read (`akIfetch = true`, Rocq `ak_coh` renamed), and `EvA.evMrd` covers both.
   Keeping the conjunct would make every Lean fetch stuck at `execA` (AxSpineOk3's fetch leaves).
2. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` (`sig_seip` or
   `sig_meip`) in `execA`/`execAR`/`rfF` (decided by the Lean-only instance
   `AxSpineOk.pinRegDec`).
3. Q7 (sfence marker): an SFENCE.VMA announce (`sfAnnB n w = true`) is a graph event, not a
   silent node (`EvA.evIa` takes `sfAnnB n w = false`): `execA` is stuck there and `rfF`'s
   announce arm demands `sfAnnB n w = false`.
4. LEAN-SAIL OUTCOMES / MONADS (as `Exec` deviation 5, `AxSymEngine` deviation 4): `execAR` is
   not a second interpreter — `SailME R X` is `ExceptT (Error ⊕ R) SailM X`, so `execAR m s` is
   `execA` of `ExceptT.run m` with `.error (.inr r)` ↦ `.inl r` (early return), `.ok x` ↦ `.inr x`
   and `.error (.inl _)` (Rocq's stuck `ExtraOutcome (inr _)`) ↦ `none`.  A failure node
   `.impure (.error _)` is stuck for `execA` (Rocq `ExtraOutcome` in the base monad).
   `rfF` is stated on `SailM X` (Rocq: any `Defs.monad E X`); for the early-return monad it is
   applied to `ExceptT.run m` (`rfFLiftR`, `execAROfRfF`).  `liftR` ↦ `liftM`,
   `catch_early_return` ↦ `SailME.run`, `returnm`/`returnM`/`returnR` ↦ `pure`, `bind0 m n` ↦
   `m >>= fun _ => n`.  Lean-sail's `choose`, `readRam`/`writeRam` are stuck for `execA`
   (Rocq `Choose`) and allowed by `rfF` (Rocq `_ => True`).
5. Rocq `untilMT` with measure 1 ↦ lean-sail `untilFuelM 1` (`execARUntilFuelM1`, as
   `ExecSC5.execRUntilFuelM1`).
6. TYPES: `mstate` ↦ `ExecSt`, `read_bytes` ↦ `bmRead` (recursive, little-endian; Rocq a
   `mapM`), `pa_add pa j` ↦ `pa + BitVec.ofNat 64 j`, `z_pa z` ↦ `BitVec.ofInt 64 z`, `Z` ↦
   `Int`, `N` ↦ `Nat`, `inl (w, None)` ↦ `.Ok (w, none)`, `register_lookup r s.(sregs)` ↦
   `s.regs r`.  `readBytesImg` produces `vs := WeakInterpProj.wbytes n w`.
7. `execAEvA`: Rocq states it in a section with an unused `QE`; the statement's failure
   predicate is `fun _ _ => False` in both.

**Rocq → Lean name map.**  `ram_ok` `ramOk`, `execA` `execA`, `execAR` `execAR`, `execA_bind`
`execABind`, `execA_bind_Some` `execABindSome`, `execA_bind0_Some` `execABind0Some`,
`execA_returnm` `execAReturnm`, `execA_returnM` `execAReturnM`, `execA_read_reg` `execAReadReg`,
`execA_write_reg` `execAWriteReg`, `execAR_bind` `execARBind`, `execAR_bind_Some`
`execARBindSome`, `execAR_bind0_Some` `execARBind0Some`, `execAR_returnR_fwd` `execARReturnRFwd`,
`execAR_liftR` `execARLiftR`, `execAR_liftR_seq` `execARLiftRSeq`, `execA_catch_early_return`
`execACatchEarlyReturn`, `execAR_untilMT_1` `execARUntilFuelM1`, `execA_exec` `execAExec`,
`img_of` `imgOf`, `pa_add_z` `paAddZ`, `mapM_ext_in'` `mapMExtIn'`, `read_bytes_img`
`readBytesImg`, `execA_EvA` `execAEvA`, `rfF` `rfF`, `rfF_bind` `rfFBind`, `rfF_bind0`
`rfFBind0`, `rfF_liftR` `rfFLiftR`, `execA_of_rfF` `execAOfRfF`, `execAR_of_rfF` `execAROfRfF`;
tactics `rfF_step`/`rfF_solve` ↦ `rff_solve`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxSpineOk.pinRegDec`, `AxSpineOk.mapMMap`, `AxSpineOk.ramOkSpec`.

**Dropped:** `execA_and_boolM_Some`, `execA_or_boolM_Some` (Lean's model has no
`and_boolM`/`or_boolM`; no weak file uses them — as `Exec`'s `exec_and_boolM_Some`).
**Not ported:** the `Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSymEngine

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The path interpreter -/

/-- (Lean-only, deviation 2) The pins are decidable. -/
instance AxSpineOk.pinRegDec : DecidablePred AxRunClose.pinReg := fun r =>
  inferInstanceAs (Decidable (r = .sig_seip ∨ r = .sig_meip))

/-- A RAM read the path may take (deviation 1: no `ak_coh` conjunct). -/
def ramOk (pa : PAddr) (ak : AK) (n : Nat) : Bool :=
  !devAddr pa && !(classify ak).akLatest && decide (paZ pa + n ≤ 2 ^ 64)

theorem AxSpineOk.ramOkSpec (pa : PAddr) (ak : AK) (n : Nat) (h : ramOk pa ak n = true) :
    devAddr pa = false ∧ (classify ak).akLatest = false ∧ paZ pa + n ≤ 2 ^ 64 := by
  unfold ramOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The path interpreter** (Rocq `execA`). -/
def execA {X : Type} : SailM X → ExecSt → Option (X × ExecSt)
  | .pure x, s => some (x, s)
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => if AxRunClose.pinReg r then none else execA (k (s.regs r)) s
    | .regWrite r v, k =>
      if AxRunClose.pinReg r then none else execA (k PUnit.unit) (s.setReg r v)
    | .memRead n _ req, k =>
      if ramOk req.pa req.access_kind n then
        match bmRead s.mem req.pa n with
        | some w => execA (k (.Ok (w, none))) s
        | none => none
      else none
    | .memWrite .., _ => none
    | .barrier _, _ => none
    | .cacheOp _, k => execA (k ()) s
    | .tlbi _, k => execA (k ()) s
    | .translationStart _, k => execA (k ()) s
    | .translationEnd _, k => execA (k ()) s
    | .takeException _, k => execA (k ()) s
    | .returnException _, k => execA (k ()) s
    | .cycleCount, k => execA (k ()) s
    | .getCycleCount, k => execA (k (0 : Nat)) s
    | .message _, k => execA (k ()) s
    | .instrAnnounce n w, k => if sfAnnB n w then none else execA (k ()) s
    | .branchAnnounce _ _, k => execA (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-- Rocq `execAR` (deviation 4): `execA` of the `ExceptT` run. -/
def execAR {R X : Type} (m : SailME R X) (s : ExecSt) : Option ((R ⊕ X) × ExecSt) :=
  match execA (ExceptT.run m) s with
  | some (.ok x, s') => some (.inr x, s')
  | some (.error (.inr r), s') => some (.inl r, s')
  | some (.error (.inl _), _) => none
  | none => none

section bind
variable {X Y : Type}

theorem execABind (m : SailM X) (f : X → SailM Y) :
    ∀ s, execA (m >>= f) s =
      match execA m s with
      | some (x, s1) => execA (f x) s1
      | none => none := by
  induction m with
  | pure x => intro s; rfl
  | impure call k ih =>
    intro s
    cases call with
    | error e => rfl
    | ok o =>
      show execA (FreeM.impure (.ok o) (fun v => k v >>= f)) s = _
      cases o
      case regRead r =>
        by_cases hr : AxRunClose.pinReg r
        · simp only [execA, hr, ↓reduceIte]
        · simp only [execA, hr, ↓reduceIte]; exact ih _ _
      case regWrite r v =>
        by_cases hr : AxRunClose.pinReg r
        · simp only [execA, hr, ↓reduceIte]
        · simp only [execA, hr, ↓reduceIte]; exact ih _ _
      case memRead n va req =>
        cases hm : ramOk req.pa req.access_kind n
        · simp only [execA, hm, Bool.false_eq_true, ↓reduceIte]
        · simp only [execA, hm, ↓reduceIte]
          cases bmRead s.mem req.pa n <;> first | rfl | simp only [ih]
      case instrAnnounce n w =>
        cases hs : sfAnnB n w
        · simp only [execA, hs, Bool.false_eq_true, ↓reduceIte]; exact ih _ _
        · simp only [execA, hs, ↓reduceIte]
      all_goals first | rfl | exact ih _ _ | (simp only [execA]; exact ih _ _)

theorem execABindSome (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X) (st : ExecSt)
    (h : execA m s = some (v, st)) : execA (m >>= f) s = execA (f v) st := by
  rw [execABind, h]

theorem execABind0Some (m : SailM Unit) (n : SailM Y) (s : ExecSt) (u : Unit) (st : ExecSt)
    (h : execA m s = some (u, st)) : execA (m >>= fun _ => n) s = execA n st := by
  rw [execABind, h]

theorem execAReturnm (x : X) (s : ExecSt) : execA (pure x : SailM X) s = some (x, s) := rfl
theorem execAReturnM (x : X) (s : ExecSt) : execA (pure x : SailM X) s = some (x, s) := rfl

theorem execAReadReg (r : Register) (s : ExecSt) (hr : ¬ AxRunClose.pinReg r) :
    execA (readReg r) s = some (s.regs r, s) := by
  simp only [readReg, PreSail.readReg, PreSail.emit, execA, hr, ↓reduceIte]

theorem execAWriteReg (r : Register) (v : RegisterType r) (s : ExecSt)
    (hr : ¬ AxRunClose.pinReg r) :
    execA (writeReg r v) s = some (PUnit.unit, s.setReg r v) := by
  simp only [writeReg, PreSail.writeReg, PreSail.emit, execA, hr, ↓reduceIte]

end bind

section execAR
variable {R X Y : Type}

theorem execARBind (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) :
    execAR (m >>= f) s =
      match execAR m s with
      | some (.inl r, s') => some (.inl r, s')
      | some (.inr a, s') => execAR (f a) s'
      | none => none := by
  unfold execAR
  rw [ExceptT.run_bind, execABind]
  rcases h : execA (ExceptT.run m) s with _ | ⟨e | a, s'⟩
  · rfl
  · rcases e with e | r <;> rfl
  · rfl

theorem execARBindSome (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y) (s' : ExecSt)
    (h : execAR m s = some (.inr a, s')) : execAR (m >>= f) s = execAR (f a) s' := by
  rw [execARBind, h]

theorem execARBind0Some (m : SailME R Unit) (n : SailME R X) (s s' : ExecSt)
    (h : execAR m s = some (.inr (), s')) : execAR (m >>= fun _ => n) s = execAR n s' := by
  rw [execARBind, h]

theorem execARReturnRFwd (x : X) (s : ExecSt) : execAR (pure x : SailME R X) s = some (.inr x, s) :=
  rfl

theorem execARLiftR (m : SailM X) (s : ExecSt) :
    execAR (liftM m : SailME R X) s =
      match execA m s with
      | some (x, s') => some (.inr x, s')
      | none => none := by
  unfold execAR
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e, execABind]
  rcases execA m s with _ | ⟨x, s'⟩ <;> rfl

theorem execARLiftRSeq (m : SailM Y) (f : Y → SailME R X) (s s' : ExecSt) (x : Y)
    (h : execA m s = some (x, s')) : execAR (liftM m >>= f) s = execAR (f x) s' := by
  rw [execARBind, execARLiftR, h]

theorem execACatchEarlyReturn (body : SailME X X) (s : ExecSt) :
    execA (SailME.run body) s =
      match execAR body s with
      | some (.inl r, s') => some (r, s')
      | some (.inr r, s') => some (r, s')
      | none => none := by
  unfold execAR
  show execA (ExceptT.run body >>= _) s = _
  rw [execABind]
  rcases execA (ExceptT.run body) s with _ | ⟨e | a, s'⟩
  · rfl
  · rcases e with e | r <;> rfl
  · rfl

/-- Rocq `execAR_untilMT_1` (deviation 5). -/
theorem execARUntilFuelM1 {Vars : Type} (vars vars' : Vars) (cond : Vars → SailME R Bool)
    (body : Vars → SailME R Vars) (s s' : ExecSt)
    (hb : execAR (body vars) s = some (.inr vars', s'))
    (hc : execAR (cond vars') s' = some (.inr true, s')) :
    execAR (untilFuelM 1 cond vars body) s = some (.inr vars', s') := by
  unfold untilFuelM untilFuelM.go
  rw [execARBind, hb]
  simp only []
  rw [execARBind, hc]
  rfl

end execAR

/-- `execA` only ever runs the RAM arm: it is a restriction of `exec`. -/
theorem execAExec {X : Type} (m : SailM X) :
    ∀ s r, execA m s = some r → exec m s = some r := by
  induction m with
  | pure x => intro s r h; exact h
  | impure call k ih =>
    intro s r h
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r' =>
        simp only [execA] at h
        split at h
        · cases h
        · exact ih _ _ _ h
      case regWrite r' v =>
        simp only [execA] at h
        split at h
        · cases h
        · exact ih _ _ _ h
      case memRead n va req =>
        simp only [execA] at h
        split at h
        · rename_i hok
          have hd := (AxSpineOk.ramOkSpec _ _ _ hok).1
          have hm : mmioAcc req.pa n = false := by simp [mmioAcc, hd]
          rw [execMemRead n va req k s hm]
          split at h
          · rename_i w hw; rw [hw]; exact ih _ _ _ h
          · cases h
        · cases h
      case instrAnnounce n w =>
        simp only [execA] at h
        split at h
        · cases h
        · exact ih _ _ _ h
      all_goals first | cases h | exact ih _ _ _ h

/-! # 2. THE BRIDGE: `execA` ⇒ `EvA` -/

/-- The image a heap denotes, `Int`-indexed as `EvA`'s. -/
def imgOf (s : ExecSt) : Image := fun z =>
  if 0 ≤ z ∧ z < 2 ^ 64 then s.mem (BitVec.ofInt 64 z) else none

theorem paAddZ (pa : PAddr) (j : Nat) :
    paZ pa + j < 2 ^ 64 → pa + BitVec.ofNat 64 j = BitVec.ofInt 64 (paZ pa + j) := by
  intro h
  unfold paZ at h ⊢
  rw [show ((pa.toNat : Int) + (j : Int)) = ((pa.toNat + j : Nat) : Int) by omega,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mapMExtIn' {α β : Type} (f g : α → Option β) :
    ∀ (l : List α), (∀ x, x ∈ l → f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, H => by
    rw [List.mapM_cons, List.mapM_cons, H x (List.mem_cons_self ..),
      mapMExtIn' f g l (fun y hy => H y (List.mem_cons_of_mem _ hy))]

/-- (Lean-only) A pointwise-`some` `mapM` is the `map`. -/
theorem AxSpineOk.mapMMap {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x, x ∈ l → f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, H => by
    rw [List.mapM_cons, H x (List.mem_cons_self ..),
      AxSpineOk.mapMMap f g l (fun y hy => H y (List.mem_cons_of_mem _ hy))]
    rfl

theorem readBytesImg (s : ExecSt) (pa : PAddr) (n : Nat) (w : BitVec (8 * n)) :
    paZ pa + n ≤ 2 ^ 64 → bmRead s.mem pa n = some w →
    ∃ vs, imgBytes (imgOf s) (paZ pa) n = some vs ∧ wordOfBytes n vs = w := by
  intro hwf hrb
  refine ⟨WeakInterpProj.wbytes n w, ?_, wordOfBytesWbytes n w⟩
  unfold imgBytes WeakInterpProj.wbytes
  rw [List.range_eq_range']
  apply AxSpineOk.mapMMap
  intro j hj
  rw [List.mem_range'_1] at hj
  have hz : paZ pa + j < 2 ^ 64 := by omega
  have h0 : 0 ≤ paZ pa := by unfold paZ; omega
  unfold imgOf
  rw [if_pos ⟨by omega, hz⟩, ← paAddZ pa j hz]
  exact bmRead_spec s.mem pa n w hrb j (by omega)

theorem execAEvA {X : Type} (m : SailM X) :
    ∀ s x s', execA m s = some (x, s') →
    ∀ t : ExecSt, t.regs = s.regs →
    EvA (imgOf s) (fun (_ : Sail.Error exception) _ => False)
      (fun x' t' => x' = x ∧ t'.regs = s'.regs ∧ t'.mem = t.mem ∧ t'.dev = t.dev) m t := by
  induction m with
  | pure y =>
    intro s x s' h t ht
    simp only [execA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .evRet _ _ ⟨rfl, ht, rfl, rfl⟩
  | impure call k ih =>
    intro s x s' h t ht
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          refine .evRd r k t (fun hp => absurd hp hr) (fun _ => ?_)
          rw [ht]
          exact ih _ s x s' h t ht
      case regWrite r v =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          refine .evWr r v k t hr ?_
          have HI := ih PUnit.unit (s.setReg r v) x s' h (t.setReg r v) (by simp [ht])
          exact EvAMono (imgOf s) _ _ _ _ _ _ (fun _ _ h => h)
            (fun x' t' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩) HI
      case memRead n va req =>
        simp only [execA] at h
        split at h
        · rename_i hok
          obtain ⟨hd, hl, hwf⟩ := AxSpineOk.ramOkSpec _ _ _ hok
          split at h
          · rename_i w hrb
            obtain ⟨vs, hvs, hw⟩ := readBytesImg s req.pa n w hwf hrb
            refine .evMrd n va req k t vs hd hl hvs ?_
            rw [hw]
            exact ih _ s x s' h t ht
          · cases h
        · cases h
      case instrAnnounce n w =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hs
          exact .evIa n w k t (by simpa using hs) (ih _ s x s' h t ht)
      case barrier => cases h
      case memWrite => cases h
      case choose => cases h
      case readRam => cases h
      case writeRam => cases h
      case branchAnnounce => exact .evBa _ _ k t (ih _ s x s' h t ht)
      case cacheOp => exact .evCo _ k t (ih _ s x s' h t ht)
      case tlbi => exact .evTl _ k t (ih _ s x s' h t ht)
      case takeException => exact .evTe _ k t (ih _ s x s' h t ht)
      case returnException => exact .evRx _ k t (ih _ s x s' h t ht)
      case translationStart => exact .evTs _ k t (ih _ s x s' h t ht)
      case translationEnd => exact .evTx _ k t (ih _ s x s' h t ht)
      case cycleCount => exact .evCc k t (ih _ s x s' h t ht)
      case message => exact .evMsg _ k t (ih _ s x s' h t ht)
      case getCycleCount => exact .evGcc k t (ih _ s x s' h t ht)

/-! # 3. The fail-tolerant register-only footprint -/

/-- Rocq `rfF` (deviations 2–4). -/
def rfF {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => ¬ AxRunClose.pinReg r ∧ ∀ v, rfF (k v)
    | .regWrite r _, k => ¬ AxRunClose.pinReg r ∧ rfF (k PUnit.unit)
    | .memRead .., _ => False
    | .memWrite .., _ => False
    | .barrier _, _ => False
    | .cacheOp _, k => rfF (k ())
    | .tlbi _, k => rfF (k ())
    | .translationStart _, k => rfF (k ())
    | .translationEnd _, k => rfF (k ())
    | .takeException _, k => rfF (k ())
    | .returnException _, k => rfF (k ())
    | .cycleCount, k => rfF (k ())
    | .getCycleCount, k => rfF (k (0 : Nat))
    | .message _, k => rfF (k ())
    | .instrAnnounce n w, k => sfAnnB n w = false ∧ rfF (k ())
    | .branchAnnounce _ _, k => rfF (k ())
    | .choose _, _ => True
    | .readRam .., _ => True
    | .writeRam .., _ => True

theorem rfFBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    rfF m → (∀ x, rfF (f x)) → rfF (m >>= f) := by
  induction m with
  | pure y => intro _ hf; exact hf y
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show rfF (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case regRead r => exact ⟨hm.1, fun v => ih v (hm.2 v) hf⟩
      case regWrite r v => exact ⟨hm.1, ih _ hm.2 hf⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2 hf⟩
      all_goals first | exact hm | trivial | exact ih _ hm hf

theorem rfFBind0 {Y : Type} (m : SailM Unit) (n : SailM Y) :
    rfF m → rfF n → rfF (m >>= fun _ => n) :=
  fun hm hn => rfFBind m (fun _ => n) hm (fun _ => hn)

theorem rfFLiftR {R X : Type} (m : SailM X) : rfF m → rfF (ExceptT.run (liftM m : SailME R X)) := by
  intro h
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  exact rfFBind _ _ h (fun _ => trivial)

theorem execAOfRfF {X : Type} (m : SailM X) :
    rfF m → ∀ s r, exec m s = some r → execA m s = some r := by
  induction m with
  | pure y => intro _ s r h; exact h
  | impure call k ih =>
    intro hrf s r h
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r' =>
        simp only [execA, hrf.1, ↓reduceIte]
        exact ih _ (hrf.2 _) _ _ h
      case regWrite r' v =>
        simp only [execA, hrf.1, ↓reduceIte]
        exact ih _ hrf.2 _ _ h
      case instrAnnounce n w =>
        simp only [execA, hrf.1, Bool.false_eq_true, ↓reduceIte]
        exact ih _ hrf.2 _ _ h
      case memRead => exact hrf.elim
      case memWrite => exact hrf.elim
      case barrier => exact hrf.elim
      all_goals first | cases h | exact ih _ hrf _ _ h

theorem execAROfRfF {R X : Type} (m : SailME R X) :
    rfF (ExceptT.run m) → ∀ s r, execR m s = some r → execAR m s = some r := by
  intro hrf s r h
  unfold execR at h
  unfold execAR
  rcases he : exec (ExceptT.run m) s with _ | p
  · rw [he] at h; cases h
  · rw [he] at h
    rw [execAOfRfF _ hrf s p he]
    exact h

/-- Rocq `rfF_step`/`rfF_solve`: close a `rfF` goal over a register-only tree. -/
syntax "rff_solve" : tactic
macro_rules
  | `(tactic| rff_solve) => `(tactic| repeat (first
      | exact True.intro
      | (apply rfFBind <;> try intro _)
      | apply rfFLiftR
      | (split)
      | (refine ⟨?_, ?_⟩)
      | (intro h; rcases h with h | h <;> cases h)
      | (intro _)
      | rfl
      | (simp only [rfF, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit])))

end Weak

namespace Weak
open MachCSL Sail LeanRV64D LeanRV64D.Functions
example : rfF (do let v ← readReg .PC; writeReg .nextPC v; pure () : SailM Unit) := by rff_solve
example (b : Bool) : rfF (do let v ← readReg .PC; if b then writeReg .nextPC v else pure () : SailM Unit) := by rff_solve
end Weak
