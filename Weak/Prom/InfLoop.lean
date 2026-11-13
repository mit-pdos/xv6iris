/-
Weak/Prom: **MP FOREVER, END TO END — the infinite-execution theorem for `tLoop`** (owner request 2026-11-13,
verbatim: "write the end-to-end infinite-execution theorem for tLoop").

`inf_mpLoop`: for EVERY execution `E` of `tLoop` (CoreLitLoop.lean's MP loop: hart 0 stores data then flag with
`fence w,w`, hart 1 loads flag then data with `fence r,r`, both forever) that the RVWMO reference allows —
`infExec tLoop E` (PfxDefs.lean: the harts run the program, the path conditions hold, `rvwmoRefInf`: the manual's
axioms over a possibly INFINITE set of events, progress axiom included) — if a hart's memory operation `(h, i)` is
a load of the flag that returned 1 and the hart's NEXT memory operation `(h, j)` is a load of the data, then that
data load returned 1.  The statement mentions no machine, no unrolling and no observed set: every one of them is
chosen inside the proof.

The proof (`inf_mpLoop_core`):
1. scope: `progS3aB tLoop` (decide) and NA-6 `singleSizeI E` (InfLoopRef.lean `singleSizeI_loop`, from the program);
2. `h = 1` (hart 0 has no loads, `noLoad0`);
3. path-exposing completeness with `O = [(1, j)]` (InfLoopCmp.lean `rvwmo_inf_completeP`): an unrolling `T'` that
   follows `E`'s path and a valid `litStep` run of `T'` whose hart-1 load row extends `E`'s up to `j`;
4. `T'` follows the loop's path (`pc_pat`: `pc = j % 4` before halting), so the BRIDGE (InfLoopBridge.lean) turns
   the run into a valid `xStep xsLoop` run of `tLoop` with the same event list;
5. `lit_mpLoop` (the program logic, CoreLitLoop.lean) gives `qLoop` of hart 1's trace; hart 1's memory entries
   alternate flag / data on the machine (InfLoopMach.lean `alt_run`) and in `E` (`par1`), so `E`'s flag load is
   the machine's memory entry `m` (`m` = number of earlier loads, even) and the data load is entry `m + 1`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.InfLoopMach

noncomputable section

namespace Weak.Prom.InfLoop

open Classical
open MachCSL MachCSL.Stdpp Iris.Std
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref
open Weak.Prom.Pfx
open Weak.Prom.Cmp (machRow)
open Weak.Prom.PF.Loop (tLoop xsLoop qLoop ldRet lit_mpLoop)
open Weak.Prom.Ref.Lit (X Y)
open PLabel

/-! ## 1. Rows -/

theorem filt_succ {α : Type} (f : Nat → α) (p : α → Bool) (n : Nat) :
    ((List.range (n + 1)).map f).filter p = ((List.range n).map f).filter p ++ (if p (f n) then [f n] else []) := by
  rw [List.range_succ, List.map_append, List.filter_append]
  cases hp : p (f n) <;> simp [hp]

theorem filt_mid {α : Type} (f : Nat → α) (p : α → Bool) (i : Nat) :
    ∀ n, (∀ k, i < k → k < i + 1 + n → p (f k) = false) →
      ((List.range (i + 1 + n)).map f).filter p = ((List.range (i + 1)).map f).filter p
  | 0, _ => rfl
  | n + 1, h => by
    rw [show i + 1 + (n + 1) = (i + 1 + n) + 1 by omega, filt_succ, h (i + 1 + n) (by omega) (by omega),
      filt_mid f p i n (fun k hk1 hk2 => h k hk1 (by omega))]
    simp

/-- The filtered row through `j`, when `i < j` are the only two kept indices from `i` on. -/
theorem filt_two {α : Type} (f : Nat → α) (p : α → Bool) {i j : Nat} (hij : i < j) (hi : p (f i) = true)
    (hj : p (f j) = true) (hmid : ∀ k, i < k → k < j → p (f k) = false) :
    ((List.range (j + 1)).map f).filter p = ((List.range i).map f).filter p ++ [f i, f j] := by
  have hm : ((List.range j).map f).filter p = ((List.range (i + 1)).map f).filter p := by
    have := filt_mid f p i (j - i - 1) (fun k h1 h2 => hmid k h1 (by omega))
    rwa [show i + 1 + (j - i - 1) = j by omega] at this
  rw [filt_succ, if_pos hj, hm, filt_succ, if_pos hi]
  simp

theorem get_mid {β : Type} (A : List β) (x y : β) (t : List β) :
    (A ++ [x, y] ++ t)[A.length]? = some x ∧ (A ++ [x, y] ++ t)[A.length + 1]? = some y := by
  constructor <;> simp [List.append_assoc]

theorem bytes_one {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (h : bytesVal [a, b, c, d] = 1) : [a, b, c, d] = [1, 0, 0, 0] := by
  simp only [bytesVal, List.foldr_cons, List.foldr_nil] at h
  have h1 : a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
  rfl

/-- Four answered bytes whose value is 1 are `[1, 0, 0, 0]`. -/
theorem obs_one {tvs : List (Nat × BitVec 8)} (hl : tvs.length = 4) (h : obsOf tvs = 1) :
    tvs.map (fun tv => tv.2.toNat) = [1, 0, 0, 0] := by
  rw [Cmp.obsOf_eq] at h
  match tvs, hl with
  | [t0, t1, t2, t3], _ =>
    exact bytes_one (by have := t0.2.isLt; simpa using this) (by have := t1.2.isLt; simpa using this)
      (by have := t2.2.isLt; simpa using this) (by have := t3.2.isLt; simpa using this) h

/-! ## 2. THE THEOREM -/

/-- **The end-to-end theorem, value form of the flag premise** (`bytesVal` of the flag load's bytes is 1; the
data load's bytes are then exactly `[1, 0, 0, 0]`). -/
theorem inf_mpLoop_core {E : IExec} (hE : infExec tLoop E) (h i j : Nat)
    (hi : E.isMem (h, i)) (hj : E.isMem (h, j)) (hij : i < j)
    (hnext : ∀ k, i < k → k < j → ¬ E.isMem (h, k))
    (hfl : (E.sk (h, i)).kind.isLoad = true) (hfa : (E.ev (h, i)).pa = Y) (hfv : bytesVal (E.ev (h, i)).rdat = 1)
    (hdl : (E.sk (h, j)).kind.isLoad = true) (_hda : (E.ev (h, j)).pa = X) :
    (E.ev (h, j)).rdat = [1, 0, 0, 0] := by
  -- the hart is hart 1
  have hh : h < 2 := has_lt hE hi.1
  have h1 : h = 1 := by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · rw [noLoad0 hE hi.1] at hfl; cases hfl
    · rfl
  subst h1
  -- path-exposing completeness, `O = [(1, j)]`
  obtain ⟨T', K, _, _, _, _, hunr, hpath, _, _, _, _, run, hv, _, _, hrow⟩ :=
    rvwmo_inf_completeP tLoop_S3a hE (singleSizeI_loop hE) [(1, j)]
      (by intro e he; simp only [List.mem_singleton] at he; subst he; exact hj)
  -- the unrolling follows the loop's path
  have hU : ∀ h' < 2, UOk h' (T'.prog h') := by
    intro h' hh' jj ins hget
    obtain ⟨hp, hnh⟩ := hpath h' (by rw [tLoop_len]; exact hh')
    have hl4 : (tLoop.prog h').length = 4 := by rcases (by omega : h' = 0 ∨ h' = 1) with rfl | rfl <;> rfl
    rw [hp] at hget
    simp only [unrP, List.getElem?_map] at hget
    have hjj : jj < K h' := by
      by_cases hc : jj < K h'
      · exact hc
      · rw [List.getElem?_eq_none (by simp; omega)] at hget; cases hget
    rw [List.getElem?_range hjj, Option.map_some, Option.some.injEq] at hget
    have hpc : (E.st h' jj).pc = jj % 4 := by
      rcases pc_pat hE hh' jj (fun j' hj' => by have := hnh j' (by omega); rwa [hl4] at this) with h1 | ⟨h1, _⟩
      · exact h1
      · exact absurd h1 (by have := hnh jj hjj; rwa [hl4] at this)
    have hlt : jj % 4 < (tLoop.prog h').length := by rw [hl4]; exact Nat.mod_lt _ (by decide)
    refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
    rw [← hget]
    unfold iAt
    rw [hE.1, hpc, List.getElem?_eq_getElem hlt]
    rfl
  -- the bridge, the logic, the alternation
  obtain ⟨hreg, himg, _, hlen, _⟩ := hunr
  obtain ⟨cfg, hv'⟩ := bridge (by rw [hlen, tLoop_len]) hreg himg hU hv
  have hq : qLoop (traceOf 1 run.evs) := lit_mpLoop _ _ hv' 1
  have halt : AltT (traceOf 1 run.evs) := alt_run (run := ⟨run.evs, cfg⟩) hv'
  have hpre : (((List.range (j + 1)).map (fun i => E.ev (1, i))).filter (fun v => v.sk.kind.isLoad)).map Ev.rdat <+:
      machRow (traceOf 1 run.evs) := hrow (1, j) (by simp)
  -- `E`'s row through `j`: the loads before `i`, then `i`, then `j`
  have hmid : ∀ k, i < k → k < j → (E.ev (1, k)).sk.kind.isLoad = false := by
    intro k k1 k2
    cases hk : (E.ev (1, k)).sk.kind.isLoad
    · rfl
    · exfalso
      apply hnext k k1 k2
      obtain ⟨hh1, k0, hk0⟩ := hj.1
      exact ⟨⟨hh1, k0, Nat.lt_trans k2 hk0⟩, Kind.isMem_of_isLoad _ hk⟩
  have hrowEq := filt_two (fun i => E.ev (1, i)) (fun v => v.sk.kind.isLoad) hij hfl hdl hmid
  obtain ⟨m, hmdef⟩ : ∃ m, m = (((List.range i).map (fun i => E.ev (1, i))).filter (fun v => v.sk.kind.isLoad)).length :=
    ⟨_, rfl⟩
  have hm : m % 2 = 0 := by
    rw [hmdef, List.filter_map, List.length_map]
    exact (par1 hE hi.1 hfl).1 hfa
  obtain ⟨t, ht⟩ := hpre
  rw [hrowEq, List.map_append] at ht
  have hgm := get_mid ((((List.range i).map (fun i => E.ev (1, i))).filter (fun v => v.sk.kind.isLoad)).map Ev.rdat)
    (E.ev (1, i)).rdat (E.ev (1, j)).rdat t
  rw [List.length_map, ← hmdef] at hgm
  have hR0 : (machRow (traceOf 1 run.evs))[m]? = some (E.ev (1, i)).rdat := by rw [← ht]; exact hgm.1
  have hR1 : (machRow (traceOf 1 run.evs))[m + 1]? = some (E.ev (1, j)).rdat := by rw [← ht]; exact hgm.2
  -- the machine's memory entries `m`, `m + 1`
  obtain ⟨tvs0, src0, he0, _, hv0⟩ := machRow_at halt hR0
  obtain ⟨tvs1, src1, he1, hl1, hv1⟩ := machRow_at halt hR1
  rw [if_pos hm] at he0
  rw [if_neg (by omega)] at he1
  have hobs0 : obsOf tvs0 = 1 := by rw [Cmp.obsOf_eq, hv0]; exact hfv
  have hobs1 : obsOf tvs1 = 1 := hq m _ _ he0 he1 (by simp [ldRet, hobs0]) (obsOf tvs1) (by simp [ldRet])
  rw [← hv1]
  exact obs_one hl1 hobs1

/-- **MP FOREVER, END TO END** (owner request 2026-11-13).  In every execution of `tLoop` — finite or infinite —
that the RVWMO reference allows, a data load that is the next memory operation after a flag load that returned 1
returns 1. -/
theorem inf_mpLoop {E : IExec} (hE : infExec tLoop E) (h i j : Nat)
    (hi : E.isMem (h, i)) (hj : E.isMem (h, j)) (hij : i < j)
    (hnext : ∀ k, i < k → k < j → ¬ E.isMem (h, k))
    (hfl : (E.sk (h, i)).kind.isLoad = true) (hfa : (E.ev (h, i)).pa = Y) (hfv : (E.ev (h, i)).rdat = [1, 0, 0, 0])
    (hdl : (E.sk (h, j)).kind.isLoad = true) (hda : (E.ev (h, j)).pa = X) :
    (E.ev (h, j)).rdat = [1, 0, 0, 0] :=
  inf_mpLoop_core hE h i j hi hj hij hnext hfl hfa (by rw [hfv]; rfl) hdl hda

/-- **The value form**: the little-endian VALUE of the data load is 1 whenever the flag load's value is 1. -/
theorem inf_mpLoop_val {E : IExec} (hE : infExec tLoop E) (h i j : Nat)
    (hi : E.isMem (h, i)) (hj : E.isMem (h, j)) (hij : i < j)
    (hnext : ∀ k, i < k → k < j → ¬ E.isMem (h, k))
    (hfl : (E.sk (h, i)).kind.isLoad = true) (hfa : (E.ev (h, i)).pa = Y) (hfv : bytesVal (E.ev (h, i)).rdat = 1)
    (hdl : (E.sk (h, j)).kind.isLoad = true) (hda : (E.ev (h, j)).pa = X) :
    bytesVal (E.ev (h, j)).rdat = 1 := by
  rw [inf_mpLoop_core hE h i j hi hj hij hnext hfl hfa hfv hdl hda]; rfl

end Weak.Prom.InfLoop

end

#print axioms Weak.Prom.InfLoop.inf_mpLoop
#print axioms Weak.Prom.InfLoop.inf_mpLoop_val
