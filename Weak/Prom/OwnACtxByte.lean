/-
Weak/Prom: **criterion (iii) on track (a): a ctxByte-SHAPED POINTS-TO with FRACTIONAL SHARING** (stage S4a part 4;
plan rev 7 §4 G4 criterion (iii) "a ctxByte-shaped points-to expressible (MachCSL/Ctx.lean:1242)"; §7 "`ctxByte ξ a
dq v` … becomes the track's points-to at context ξ's view").

MachCSL's `ctxByte ξ a dq v := ∃ e H, a ↦ₕ{dq} (e :: H) ∗ ⌜e.v = v ∧ …⌝ ∗ keyAt era ξ e.t` (a fraction of byte `a`'s
history whose latest entry `e` holds `v`, and the context ξ's view has passed `e.t`).  Track (a)'s analogue
`ctxByteA g img M vw a dq v`: the latest write `lw` to `a` holds `v` (pure, M-indexed: all of M is present), a
FRACTION `dq` of the `pend` of every later message touching `a` (`pendq`), and `lw ≤ vw` — the analogue of
`keyAt ξ e.t`, a hart-local view bound (track (a)'s views are the hart's exact state, carried as pure facts, not
resources).
* `ctxByteA_split` — FRACTIONAL SHARING: `dq₁ + dq₂` splits (the bag of fractional `pend`s splits);
* `ctxByteA_read` — THE SHARED READ: any fraction suffices to read `v` when the answer lies below the reader's
  frontier (a later message touching `a` would be fulfilled — `shot` — contradicting the held fraction), or free
  mode; the R-a1 case (an answer above the frontier) needs the full fraction (doom; the existing `cld_cases` /
  `h1_cld` pattern);
* `ctxByteA_write` — THE OWNER'S WRITE (`dq = 1`): the store's `pend` comes out of the bag; the points-to moves to it.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipe

namespace Weak.Prom.OA.P

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- Message `m` touches byte `a` (writes it, or a cache-block operation covering it). -/
def touchB (m : PMsg) (a : Int) : Bool :=
  (m.byteAt a).isSome || (match m.cls with
    | .cmo _ len => decide (m.pa ≤ a ∧ a < m.pa + len)
    | _ => false)

/-- Byte `a`'s BAG above `lw`: the later messages touching it. -/
def byteBag (M : List PMsg) (a : Int) (lw : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lw < t) && (match msgAt M t with
    | some m => touchB m a
    | none => false))

section cb

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- A FRACTION `q` of message `t`'s one-shot (`pendq g t 1` is `pend g t`). -/
def pendq (g : AGN) (t : Nat) (q : Qp) : IProp GF := ghost_var (g.mn.getD (t - 1) 0) (.own q) false

theorem pendq_one (g : AGN) (t : Nat) : pendq (GF := GF) g t 1 ⊣⊢ pend g t := .rfl

theorem pendq_shot (g : AGN) (t : Nat) (q : Qp) : pendq (GF := GF) g t q ∗ shot g t ⊢ False := by
  unfold pendq shot
  iintro ⟨H1, H2⟩
  ihave %h := ghost_var_valid_2 $$ H1 H2
  exact absurd h.2 (by decide)

theorem pendq_split (g : AGN) (t : Nat) (q1 q2 : Qp) :
    pendq (GF := GF) g t (q1 + q2) ⊢ pendq g t q1 ∗ pendq g t q2 := by
  unfold pendq
  iintro H
  iapply ghost_var_split $$ H

theorem bag_split (g : AGN) (q1 q2 : Qp) : ∀ (l : List Nat),
    ([∗list] t ∈ l, pendq (GF := GF) g t (q1 + q2)) ⊢ ([∗list] t ∈ l, pendq g t q1) ∗ [∗list] t ∈ l, pendq g t q2
  | [] => by iintro _; isplitl <;> exact BigSepL.bigSepL_nil.2
  | a :: l => by
    have ih := bag_split g q1 q2 l
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, H⟩
    icases pendq_split g a q1 q2 $$ Ha with ⟨Ha1, Ha2⟩
    icases ih $$ H with ⟨H1, H2⟩
    isplitl [Ha1 H1]
    · iapply (BigSepL.bigSepL_cons).2; iframe Ha1 H1
    · iapply (BigSepL.bigSepL_cons).2; iframe Ha2 H2

/-- **THE ctxByte-SHAPED POINTS-TO** (see the header). -/
def ctxByteA (g : AGN) (img : Image) (M : List PMsg) (vw : Nat) (a : Int) (q : Qp) (v : BitVec 8) : IProp GF :=
  iprop(∃ lw, ⌜memByte img M lw a = some v ∧ lw ≤ vw ∧
      (lw = 0 ∨ ∃ m, msgAt M lw = some m ∧ notCmo m.cls = true ∧ (m.byteAt a).isSome = true)⌝ ∗
    [∗list] t ∈ byteBag M a lw, pendq g t q)

/-- **FRACTIONAL SHARING**. -/
theorem ctxByteA_split (g : AGN) (img : Image) (M : List PMsg) (vw : Nat) (a : Int) (q1 q2 : Qp) (v : BitVec 8) :
    ctxByteA (GF := GF) g img M vw a (q1 + q2) v ⊢ ctxByteA g img M vw a q1 v ∗ ctxByteA g img M vw a q2 v := by
  unfold ctxByteA
  iintro ⟨%lw, %h, Hb⟩
  icases bag_split g q1 q2 _ $$ Hb with ⟨H1, H2⟩
  isplitl [H1]
  · iexists lw; iframe H1; ipureintro; exact h
  · iexists lw; iframe H2; ipureintro; exact h

/-- A larger view keeps the points-to. -/
theorem ctxByteA_view (g : AGN) (img : Image) (M : List PMsg) {vw vw' : Nat} (hv : vw ≤ vw') (a : Int) (q : Qp)
    (v : BitVec 8) : ctxByteA (GF := GF) g img M vw a q v ⊢ ctxByteA g img M vw' a q v := by
  unfold ctxByteA
  iintro ⟨%lw, %h, Hb⟩
  iexists lw; iframe Hb; ipureintro; exact ⟨h.1, by omega, h.2.2⟩

/-- The answer `t` of a read of `a` with a floor `fl ≥ lw` and no write of `a` in `(t, fl]` is `lw` or a later
message writing `a`. -/
theorem src_lw {img : Image} {M : List PMsg} {a : Int} {t lw fl : Nat} {v : BitVec 8}
    (hlw : lw = 0 ∨ ∃ m, msgAt M lw = some m ∧ notCmo m.cls = true ∧ (m.byteAt a).isSome = true)
    (hfl : lw ≤ fl) (hb : memByte img M t a = some v) (hr : ¬ writesIn M a t fl) :
    t = lw ∨ (lw < t ∧ ∃ m, msgAt M t = some m ∧ (m.byteAt a).isSome = true) := by
  by_cases h : t < lw
  · rcases hlw with rfl | ⟨m, hm, _, hba⟩
    · omega
    · obtain ⟨k, rfl⟩ : ∃ k, lw = k + 1 := ⟨lw - 1, by omega⟩
      exact absurd ⟨k + 1, h, hfl, m, by simpa [msgAt] using hm, hba⟩ hr
  · by_cases he : t = lw
    · exact .inl he
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
      obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
      exact .inr ⟨by omega, m, by simpa [msgAt] using hm, by rw [hba]; rfl⟩

/-- **THE SHARED READ** (see the header): any fraction, an answer below the frontier. -/
theorem ctxByteA_read (g : AGN) {π : Proto} {img : Image} (M : List PMsg) {ws1 : PState} {vw fl t : Nat}
    {a : Int} {q : Qp} {v v' : BitVec 8} (hfl : vw ≤ fl) (hb : memByte img M t a = some v')
    (hr : ¬ writesIn M a t fl) (ht : t ≤ wfr ws1) :
    doomInv (GF := GF) g M ∗ frontA g π img M ws1 ∗ ctxByteA g img M vw a q v ⊢
      |={⊤}=> (⌜v' = v⌝ ∗ ctxByteA g img M vw a q v) ∨ (dfree g ∗ dshot g) := by
  iintro ⟨#Hdoom, #Hfr, Hc⟩
  unfold ctxByteA
  icases Hc with ⟨%lw, %hlw, Hb⟩
  obtain ⟨hv, hlv, hlm⟩ := hlw
  rcases src_lw hlm (by omega) hb hr with rfl | ⟨hlt, m, hm, hba⟩
  · imodintro; ileft
    isplitr
    · ipureintro; rw [hv] at hb; exact (Option.some.inj hb).symm
    · iexists t; iframe Hb; ipureintro; exact ⟨hv, hlv, hlm⟩
  · have htM := msgAt_le hm
    ihave #Hft := frontA_get t $$ Hfr %⟨htM.1, htM.2, ht⟩
    unfold byteBag
    icases bsl_filter_take (fun t => pendq g t q) (fun t => decide (lw < t) && (match msgAt M t with
        | some m => touchB m a
        | none => false)) (fun _ => false) t (by simp [hlt, hm, touchB, hba]) (fun _ h => by cases h) (rng M)
      (mem_rng.2 htM) (nodup_rng M) $$ Hb with ⟨Hp, -⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · iexfalso; iapply pendq_shot; iframe Hp Hsh
    · imod dfree_dshot (E := ⊤) CoPset.subseteq_top g M $$ [] with #Hd
      · iframe Hdoom Hf
      imodintro; iright; iframe Hf Hd

/-- **THE OWNER'S WRITE** (`dq = 1`): a store at `ts` above the view (`vw < ts`) writing `v'` to `a` takes its
`pend` out of the bag; the points-to moves to `ts`. -/
theorem ctxByteA_write (g : AGN) (img : Image) (M : List PMsg) {vw ts : Nat} {a : Int} {v v' : BitVec 8}
    {m : PMsg} (hvt : vw < ts) (hm : msgAt M ts = some m) (hnc : notCmo m.cls = true) (hba : m.byteAt a = some v') :
    ctxByteA (GF := GF) g img M vw a 1 v ⊢ |={⊤}=> (shot g ts ∗ ctxByteA g img M ts a 1 v') := by
  unfold ctxByteA
  iintro ⟨%lw, %hlw, Hb⟩
  have htM := msgAt_le hm
  unfold byteBag
  icases bsl_filter_take (fun t => pendq g t 1) (fun t => decide (lw < t) && (match msgAt M t with
      | some m => touchB m a
      | none => false))
    (fun t => decide (ts < t) && (match msgAt M t with
      | some m => touchB m a
      | none => false)) ts (by simp [show lw < ts by omega, hm, touchB, hba])
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
  ihave Hp := (pendq_one g ts).1 $$ Hp
  imod shoot $$ Hp with #Hsh
  imodintro
  iframe Hsh
  iexists ts; iframe Hb; ipureintro
  refine ⟨?_, Nat.le_refl _, .inr ⟨m, hm, hnc, by rw [hba]; rfl⟩⟩
  obtain ⟨k, rfl⟩ : ∃ k, ts = k + 1 := ⟨ts - 1, by omega⟩
  simp only [memByte]
  rw [show M[k]? = some m by simpa [msgAt] using hm, Option.bind_some, hba]

end cb

/-! ## Criterion (ii): the `isLock γ lk s R` binder shape -/

/-- The ambient pre-allocated families (in S5: an instance, as MachCSL's `MachGS` ghost names). -/
class PipeEnv where
  M : List PMsg
  sv : SV

/-- **`isLockN γ lk s R`** — MachCSL `isLock γ lk s R`'s binders (Lock.lean:3325): γ the lock's ghost name (here
allocated at runtime by `initlock`), `lk` the lock word, `s` the name, `R` the protected resource (an `IProp`, not
`CtxId → IProp`: track (a)'s views are hart-local pure facts).  Persistent. -/
def isLockN {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]
    [PipeEnv] (γ : GName) (lk : Int) (_s : String) (R : IProp GF) : IProp GF :=
  isLockA PipeEnv.M PipeEnv.sv γ lk R

instance {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]
    [PipeEnv] (γ : GName) (lk : Int) (s : String) (R : IProp GF) : Persistent (isLockN γ lk s R) := by
  unfold isLockN; infer_instance

end Weak.Prom.OA.P
