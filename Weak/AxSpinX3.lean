/-
Weak: **Phase 1c, part 3 of the spinlock plan -- n-BYTE HAND NODES** (the multi-byte step lemmas
Phase 1a/1b did not build): `memRead n` / `memWrite n` `Pexv6` nodes at any width (4 =
lw/sw/amoswap.w, 8 = ld/sd), their program-step facts (unique plain write, exclusive write +
retry loop, read at every byte string), the row-pinned RUNS (`nrunRead`/`nrunWrite`/
`nrunRmwRead`/`nrunRmwWrite`), the WPd SHELLS at any `axGA2` instance (`nshRead` -- demonic read
at the graph value, any continuation; `nshWrite` via `shPos`; `nshRmwRead`/`nshRmwWrite` -- the
RMW halves; `nshFence`), and the n-byte label facts (`gwbStoren`, `grbLoadn`, `gwbRmwn`,
`storenNoRead`).  Hand nodes = no fetch/decode, `ibNone`.

Rocq: `iris/AxSpinX3.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. O2 STAGE C (as `AxSpinProt2` deviation 1): no text oracle -- Rocq's `Tf`/`T`/`img` arguments
   are gone (`nrdAstepVacuous`, `nwriteInv`, `nxwriteInv`, the shells' instance `shG`,
   `tierAWpd`).  `nrdAstepVacuous` takes `(classify ak).akIfetch = false` (a fetch is an admin
   step in Lean); its `Hn : n ≠ 0` premise (Rocq: used to refute the deleted fetch arm) is kept
   for faithfulness but unused (`_Hn`), likewise `nshRead`'s / `nshRmwRead`'s `_Hn`.
2. `nreadStep`'s premise `ak_coh (classify ak) = false` ↦ `(classify ak).akIfetch = false`, and
   its label is `rdLabel false …` (the Lean read label carries the fetch flag; as
   `l3pReadStep`).
3. lean-sail shapes (as `AxLock3Prog` deviation 3): widths are `Nat` (Rocq `N`); the requests
   `rreqn`/`wreqn` are `Mem_read_request n 64 …`/`Mem_write_request n 64 …` records with
   `size := n`, `va := none`, `value := some v`; read answers `.Ok (w, none)` (Rocq
   `inl (w, None)`), RAM write answers `.Ok (some true)` (Rocq `inl None`); `dev0_state` ↦
   `OpaxWit.wtD0`; `S k` ↦ `k + 1`; `l !! k` ↦ `l[k]?`; wand chains `A -∗ B` ↦ `⊢ A -∗ B`.
4. CONTEXTS (as `AxSpinProt2` deviation 2): section variables are explicit leading arguments
   (`cpu` in §1/§2; `GD N obSt0 obi nm cpu` in §3); §2's unused `axirisG Σ` is dropped;
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`; the policy binder is `[pol : Axpol]`; Rocq's
   local instance `nshG` is `AxSpinWit`'s `shG` (the same `axGA2` record).
5. `tvsWbytes` is proved by `AxOpsem.sndEqWbytes`; `rdLblExclFence` by `l3pRdExclFence`.

**Rocq → Lean name map.**  `rreqn` `rreqn`, `wreqn` `wreqn`, `tvs_wbytes` `tvsWbytes`,
`nread_step` `nreadStep`, `nwrite_plain_step` `nwritePlainStep`, `nwrite_plain_det`
`nwritePlainDet`, `nwrite_excl_step` `nwriteExclStep`, `nwrite_excl_det` `nwriteExclDet`,
`nread_inv_any` `nreadInvAny`, `rd_lbl_excl_fence` `rdLblExclFence`, `nrd_astep_vacuous`
`nrdAstepVacuous`, `nwrite_inv` `nwriteInv`, `no_read_at_nwrite` `noReadAtNwrite`, `nxwrite_inv`
`nxwriteInv`, `no_read_at_nxwrite` `noReadAtNxwrite`, `nrun_read` `nrunRead`, `nrun_write`
`nrunWrite`, `nrun_rmw_read` `nrunRmwRead`, `nrun_rmw_write` `nrunRmwWrite`, `nsh_read`
`nshRead`, `nsh_rmw_read` `nshRmwRead`, `nsh_rmw_write` `nshRmwWrite`, `nsh_write` `nshWrite`,
`nsh_fence` `nshFence`, `gwb_storen` `gwbStoren`, `grb_loadn` `grbLoadn`, `gwb_rmwn` `gwbRmwn`,
`storen_no_read` `storenNoRead`.  No duplicated Rocq names; no Lean-only helpers.

**Dropped:** none (`nshG` local instance inlined as `shG`, deviation 4).
-/
import Weak.AxSpinProt2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

def rreqn (n : Nat) (ak : AK) (pa : PAddr) :
    Mem_read_request n 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := ak, va := none, pa := pa, translation := (), size := n, tag := false }

def wreqn (n : Nat) (ak : AK) (pa : PAddr) (v : BitVec (8 * n)) :
    Mem_write_request n 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := ak, va := none, pa := pa, translation := (), size := n, value := some v,
    tag := none }

/-- The bytes a read node hands back ARE the word's bytes. -/
theorem tvsWbytes (n : Nat) (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) :
    tvs.length = n → (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    tvs.map Prod.snd = WeakInterpProj.wbytes n w :=
  AxOpsem.sndEqWbytes n w tvs

/-! # 1. Program-step facts -/

section nsteps
variable (cpu : CPU)

theorem nreadStep (n : Nat) (ak : AK) (pa : PAddr) :
    devAddr pa = false → (classify ak).akIfetch = false →
    ∀ (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
      (ib : Ibch) (d : Efab) (vs : List (BitVec 8)),
    vs.length = n →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n 64 (rreqn n ak pa))) KK) rs none ib) d
      (rdLabel false (classify ak).akLatest (classify ak).akSync (paZ pa) (tagVals vs)
        (rdAsrc (classify ak).akLatest ib))
      (.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib) d := by
  intro hdev hfe KK rs ib d vs hlen
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have h := pnodeStepReadAny n 64 (rreqn n ak pa) KK rs ib d.efDev vs hdev hlen
  have hfe' : (classify (rreqn n ak pa).access_kind).akIfetch = false := hfe
  rw [hfe'] at h
  exact h

theorem nwritePlainStep (n : Nat) (Hn : n ≠ 0) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa val))) KK) rs none ib)
      d
      (LStore false (paZ pa) (WeakInterpProj.wbytes n val)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (.PHart cpu (KK (.Ok (some true))) rs none ib) d := by
  intro KK rs ib d
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have hpa : devAddr (wreqn n l3pAkP pa val).pa = false := Hdev
  have hval : (wreqn n l3pAkP pa val).value = some val := rfl
  simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hn, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> first | rfl | trivial

theorem nwritePlainDet (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
      (l : Wlabel) (p' : Pexv6) (d' : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa val))) KK) rs none ib)
      d l p' d' →
    l = LStore false (paZ pa) (WeakInterpProj.wbytes n val)
          (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
    p' = .PHart cpu (KK (.Ok (some true))) rs none ib ∧ d' = d := by
  intro KK rs ib d l p' d' h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    have hpa : devAddr (wreqn n l3pAkP pa val).pa = false := Hdev
    have hval : (wreqn n l3pAkP pa val).value = some val := rfl
    simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨_, ⟨_, rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩ | ⟨hlat, _⟩⟩
    · refine ⟨rfl, rfl, ?_⟩
      rw [hd, hdd]
    · exact absurd hlat Bool.false_ne_true

theorem nwriteExclStep (n : Nat) (Hn : n ≠ 0) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) KK) rs none ib)
      d
      (LExStore false (paZ pa) (WeakInterpProj.wbytes n val)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (.PHart cpu (KK (.Ok (some true))) rs none ib) d := by
  intro KK rs ib d
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have hpa : devAddr (wreqn n l3pAkXpl pa val).pa = false := Hdev
  have hval : (wreqn n l3pAkXpl pa val).value = some val := rfl
  simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hn, Or.inr ⟨rfl, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩ <;> first | rfl | trivial

theorem nwriteExclDet (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
      (l : Wlabel) (p' : Pexv6) (d' : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) KK) rs none ib)
      d l p' d' →
    (l = LExStore false (paZ pa) (WeakInterpProj.wbytes n val)
          (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
      p' = .PHart cpu (KK (.Ok (some true))) rs none ib ∧ d' = d) ∨
    (l = LSilent ∧
      p' = .PHart cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) KK) rs none ib ∧
      d' = d) := by
  intro KK rs ib d l p' d' h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    have hpa : devAddr (wreqn n l3pAkXpl pa val).pa = false := Hdev
    have hval : (wreqn n l3pAkXpl pa val).value = some val := rfl
    simp only [pstepNode, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨_, ⟨hlat, _⟩ | ⟨_, ⟨rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, hdd, rfl, rfl⟩⟩⟩
    · exact absurd hlat.symm Bool.false_ne_true
    · exact .inl ⟨rfl, rfl, by rw [hd, hdd]⟩
    · exact .inr ⟨rfl, rfl, by rw [hd, hdd]⟩

/-- The READ inversion at an n-byte RAM `memRead` node, any access kind. -/
theorem nreadInvAny (row : List Lbl) (n : Nat) (ak : AK) (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (id : AidentT) (K : List (BitVec 8) → Athread) (v : List (BitVec 8)) :
    areadStep row ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n ak pa))) KK) rs, k⟩ id K →
    v.length = aidentN id →
    ∃ lb, row[k]? = some lb ∧ aident lb = id ∧
      K v = ⟨hp cpu (KK (.Ok (wordOfBytes n v, none))) rs, k + aidentAdvRd id⟩ := by
  rintro ⟨lb, Hlk, Hid, Hsome, Hvs⟩ Hlen
  obtain ⟨l, d, d', Hrd, Hrv, Hst, Hk⟩ := Hvs v Hlen
  rcases HKv : K v with ⟨p', k'⟩
  rw [HKv] at Hst Hk
  simp only at Hst Hk
  cases p' with
  | PDisk _ => exact Hst.elim
  | PHart cpu' m'' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, Hrs, Hib, Hn, -⟩ := Hst
    have hpa : devAddr (rreqn n ak pa).pa = false := Hdev
    simp only [pstepNode, pnodeStep, hpa, Bool.false_eq_true, ↓reduceIte] at Hn
    rcases Hn with ⟨-, w, tvs, -, -, rfl, -⟩ |
      ⟨-, ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩ |
        ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩⟩
    · rw [← Hrd] at Hsome
      simp [wlRd] at Hsome
    · simp only [Option.getD_none] at Hrs Hib
      subst Hrs Hib Hk
      simp only [wlRvals] at Hrv
      have hw : wordOfBytes n v = w := by
        rw [← Hrv, tvsWbytes n w tvs hlen hby, wordOfBytesWbytes]
      rw [hw]
      exact ⟨lb, Hlk, Hid, rfl⟩
    · simp only [Option.getD_none] at Hrs Hib
      subst Hrs Hib Hk
      simp only [wlRvals] at Hrv
      have hw : wordOfBytes n v = w := by
        rw [← Hrv, tvsWbytes n w tvs hlen hby, wordOfBytesWbytes]
      rw [hw]
      exact ⟨lb, Hlk, Hid, rfl⟩

theorem rdLblExclFence (l : Wlabel) :
    (wlRd l).isSome = true → (wlFence l).isSome = true → False :=
  l3pRdExclFence l

/-- No program step at an n-byte RAM read node (Stage C: not an i-fetch access kind). -/
theorem nrdAstepVacuous (row : List Lbl) (n : Nat) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hfe : (classify ak).akIfetch = false) (_Hn : n ≠ 0)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n ak pa))) KK) rs, k⟩ l s' →
    False := by
  intro Hst
  obtain ⟨d, d', hps⟩ := astepProgPstep _ _ l s' Hst
  obtain ⟨hrd, _⟩ := pstepProgMemreadLbl cpu n 64 (rreqn n ak pa) KK rs ibNone d l s'.atP d' Hdev
    Hfe hps
  rcases l3pAstepProgShape _ _ l s' Hst with hadm | hwr | hfn
  · exact l3pRdExclAdmin l hrd hadm
  · exact l3pRdExclWr l hrd hwr
  · exact rdLblExclFence l hrd hfn

/-- A plain n-byte write node steps only by its store. -/
theorem nwriteInv (row : List Lbl) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat) (l : Wlabel)
    (s' : Athread) :
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa val))) (fun _ => m')) rs, k⟩ l s' →
    wlWdata l = some (WeakInterpProj.wbytes n val) ∧ s' = ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hst
  generalize hs : (Athread.AThread
    (hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa val))) (fun _ => m')) rs) k) = s
    at Hst
  cases Hst with
  | AStepAdmin p k0 d l0 p' d' Hadm Hps =>
    cases hs
    obtain ⟨rfl, -, -⟩ := nwritePlainDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hps
    simp [lbAdmin] at Hadm
  | AStepWrite p k0 d l0 lb p' d' _ _ _ _ Hps =>
    cases hs
    obtain ⟨rfl, rfl, -⟩ := nwritePlainDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hps
    exact ⟨rfl, rfl⟩
  | AStepFence p k0 d l0 lb p' d' _ Hfe _ Hps =>
    cases hs
    obtain ⟨rfl, -, -⟩ := nwritePlainDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hps
    simp [wlFence] at Hfe

theorem noReadAtNwrite (row : List Lbl) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat) (id : AidentT)
    (K : List (BitVec 8) → Athread) :
    ¬ areadStep row
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa val))) (fun _ => m')) rs, k⟩
      id K := by
  rintro ⟨lb, -, -, Hsome, Hvs⟩
  obtain ⟨l, d, d', Hrd, -, Hst, -⟩ := Hvs (List.replicate (aidentN id) b0) List.length_replicate
  obtain ⟨rfl, -⟩ := nwritePlainDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hst
  rw [← Hrd] at Hsome
  simp [wlRd] at Hsome

theorem nxwriteInv (row : List Lbl) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat) (l : Wlabel)
    (s' : Athread) :
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) (fun _ => m')) rs, k⟩
      l s' →
    (wlWdata l = some (WeakInterpProj.wbytes n val) ∧ s' = ⟨hp cpu m' rs, k + 1⟩) ∨
    (l = .LSilent ∧
      s' = ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) (fun _ => m')) rs,
        k⟩) := by
  intro Hst
  generalize hs : (Athread.AThread
    (hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) (fun _ => m')) rs) k) = s
    at Hst
  cases Hst with
  | AStepAdmin p k0 d l0 p' d' Hadm Hps =>
    cases hs
    rcases nwriteExclDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hps with
      ⟨rfl, -, -⟩ | ⟨rfl, rfl, -⟩
    · simp [lbAdmin] at Hadm
    · exact .inr ⟨rfl, rfl⟩
  | AStepWrite p k0 d l0 lb p' d' Hlk Hwr Heqwr Hwdat Hps =>
    cases hs
    rcases nwriteExclDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hps with
      ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩
    · exact .inl ⟨by simp [wlWdata], rfl⟩
    · simp [wlWr] at Hwr
  | AStepFence p k0 d l0 lb p' d' _ Hfe _ Hps =>
    cases hs
    rcases nwriteExclDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hps with
      ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [wlFence] at Hfe

theorem noReadAtNxwrite (row : List Lbl) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat) (id : AidentT)
    (K : List (BitVec 8) → Athread) :
    ¬ areadStep row
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) (fun _ => m')) rs, k⟩
      id K := by
  rintro ⟨lb, -, -, Hsome, Hvs⟩
  obtain ⟨l, d, d', Hrd, -, Hst, -⟩ := Hvs (List.replicate (aidentN id) b0) List.length_replicate
  rcases nwriteExclDet cpu n pa Hdev val _ rs ibNone d _ _ _ Hst with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · rw [← Hrd] at Hsome
    simp [wlRd] at Hsome

end nsteps

/-! # 2. Row-pinned runs -/

section nruns
variable (cpu : CPU)

theorem nrunRead (GD : Gdexec) (i : Agent) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (ts : List Nat) (vs : List (BitVec 8))
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat) :
    (AxOpsem.grow GD i)[k]? = some (.LLoad false (paZ pa) ts vs) → vs.length = n →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkP pa))) KK) rs, k⟩
      ⟨hp cpu (KK (.Ok (wordOfBytes n vs, none))) rs, k + 1⟩ := by
  intro Hl Hlen
  have Hrd : areadStep (AxOpsem.grow GD i)
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkP pa))) KK) rs, k⟩
      (.IRead false (paZ pa) vs.length)
      (fun vs' => ⟨hp cpu (KK (.Ok (wordOfBytes n vs', none))) rs, k + 1⟩) := by
    refine ⟨_, Hl, rfl, rfl, ?_⟩
    intro vs' hvs'
    have hvs'' : vs'.length = n := by simp only [aidentN] at hvs'; omega
    refine ⟨rdLabel false (classify l3pAkP).akLatest (classify l3pAkP).akSync (paZ pa)
        (tagVals vs') (rdAsrc (classify l3pAkP).akLatest ibNone), OpaxWit.wtD0, OpaxWit.wtD0,
      ?_, ?_, nreadStep cpu n l3pAkP pa Hdev rfl KK rs ibNone OpaxWit.wtD0 vs' hvs'', rfl⟩
    · have hl : (classify l3pAkP).akLatest = false := rfl
      have hs : (classify l3pAkP).akSync = false := rfl
      rw [hl, hs]
      simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
      rw [hvs']
      rfl
    · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]
  have Hgv : graphValue GD (i, k) = some vs := by
    unfold graphValue
    rw [gxLblGrow, Hl]
    rfl
  exact .ANFGVRead _ _ _ vs Hrd Hgv rfl

theorem nrunWrite (GD : Gdexec) (i : Agent) (n : Nat) (Hn : n ≠ 0) (pa : PAddr)
    (Hdev : devAddr pa = false) (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat)
    (cls : WmClass) :
    (AxOpsem.grow GD i)[k]? = some (.LStore false (paZ pa) (WeakInterpProj.wbytes n val) cls) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa val))) (fun _ => m')) rs, k⟩
      ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hl
  refine .ANFGVProg _ _ ⟨.LStore false (paZ pa) (WeakInterpProj.wbytes n val) [] [], ?_, trivial⟩
  exact .AStepWrite _ k OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 Hl rfl rfl rfl
    (nwritePlainStep cpu n Hn pa Hdev val (fun _ => m') rs ibNone OpaxWit.wtD0)

theorem nrunRmwRead (GD : Gdexec) (i : Agent) (k : Nat) (n : Nat) (pa : PAddr)
    (Hdev : devAddr pa = false) (ts : List Nat) (old new : List (BitVec 8)) (cls : WmClass)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) :
    (AxOpsem.grow GD i)[k]? = some (.LRmw true false (paZ pa) ts old new cls) →
    old.length = n → new.length = n →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkXaq pa))) KK) rs, k⟩
      ⟨hp cpu (KK (.Ok (wordOfBytes n old, none))) rs, k⟩ := by
  intro Hl Hlo Hln
  have Hrd : areadStep (AxOpsem.grow GD i)
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkXaq pa))) KK) rs, k⟩
      (.IRmw true false (paZ pa) new.length)
      (fun vs => ⟨hp cpu (KK (.Ok (wordOfBytes n vs, none))) rs, k⟩) := by
    refine ⟨_, Hl, rfl, rfl, ?_⟩
    intro vs hvs
    have hvs' : vs.length = n := by simp only [aidentN] at hvs; omega
    refine ⟨rdLabel false true (classify l3pAkXaq).akSync (paZ pa) (tagVals vs)
        (rdAsrc true ibNone), OpaxWit.wtD0, OpaxWit.wtD0, ?_, ?_,
      nreadStep cpu n l3pAkXaq pa Hdev rfl KK rs ibNone OpaxWit.wtD0 vs hvs', ?_⟩
    · simp only [rdLabel, wlRd, aidentRd, tagValsLength, Bool.false_eq_true, ↓reduceIte]
      rw [hvs]; rfl
    · rw [rdLabelRvals _ _ _ _ _ _ rfl, tagValsSnd]
    · rfl
  have Hgv : graphValue GD (i, k) = some old := by
    unfold graphValue
    rw [gxLblGrow, Hl]
    rfl
  exact .ANFGVRead _ _ _ old Hrd Hgv (by simp only [aidentN]; omega)

theorem nrunRmwWrite (GD : Gdexec) (i : Agent) (k : Nat) (n : Nat) (Hn : n ≠ 0) (pa : PAddr)
    (Hdev : devAddr pa = false) (ts : List Nat) (old : List (BitVec 8)) (val : BitVec (8 * n))
    (cls : WmClass) (m' : SailM Unit) (rs : RegFile) :
    (AxOpsem.grow GD i)[k]? =
      some (.LRmw true false (paZ pa) ts old (WeakInterpProj.wbytes n val) cls) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) (fun _ => m')) rs, k⟩
      ⟨hp cpu m' rs, k + 1⟩ := by
  intro Hl
  refine .ANFGVProg _ _
    ⟨.LExStore false (paZ pa) (WeakInterpProj.wbytes n val) [] [], ?_, trivial⟩
  exact .AStepWrite _ k OpaxWit.wtD0 _ _ _ OpaxWit.wtD0 Hl rfl rfl rfl
    (nwriteExclStep cpu n Hn pa Hdev val (fun _ => m') rs ibNone OpaxWit.wtD0)

end nruns

/-! # 3. WPd shells at any `axGA2` instance -/

section nshells
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [pol : Axpol]

/-- A plain n-byte read node strictly inside the row, ANY continuation: the event's step is taken
at the PINNED graph value `v`. -/
theorem nshRead (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N) (cpu : CPU) (i : Agent) (Φ : Athread → IProp GF) (n : Nat) (_Hn : n ≠ 0)
    (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (k : Nat)
    (Hne : k ≠ (AxOpsem.grow GD i).length)
    (Hrow : ∀ lb, (AxOpsem.grow GD i)[k]? = some lb → aidentAdvRd (aident lb) = 1)
    (P : IProp GF)
    (Hcont : ∀ (v : List (BitVec 8)) (rs : RegFile), graphValue GD (i, k) = some v →
      ⊢ P -∗ @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphValue GD (i, k) = some v) (fun _ => k + 1)
        (fun _ => tierAWpd (hlc := hlc) GD N obSt0 obi nm
          ⟨hp cpu (KK (.Ok (wordOfBytes n v, none))) rs, k + 1⟩ .MaybeStuck i Φ)) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  have H : ⊢ ∀ rs : RegFile, P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
    iloeb as IH
    iintro %rs HP
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i Φ).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      have Hst' := Hst
      obtain ⟨lb, Hlk, Hidlb, _, -⟩ := Hst
      have Hadv1 : aidentAdvRd id = 1 := by rw [← Hidlb]; exact Hrow lb Hlk
      rw [if_pos Hadv1]
      iintro %v %Hgv %Hlen
      obtain ⟨lb', -, -, HK⟩ := nreadInvAny cpu _ n l3pAkP pa Hdev KK rs k id K v Hst' Hlen
      rw [HK, Hadv1]
      iapply (Hcont v rs Hgv) $$ HP
    isplit
    · iintro %l %s' %Hst %_
      exact (nrdAstepVacuous cpu _ n l3pAkP pa Hdev rfl _Hn KK rs k l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu _ rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

/-- The RMW's READ half (n bytes): pinned to the row's read value. -/
theorem nshRmwRead (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent)
    (Φ : Athread → IProp GF) (n : Nat) (_Hn : n ≠ 0) (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (k : Nat)
    (ts : List Nat) (old new : List (BitVec 8)) (cls : WmClass)
    (Hne : k ≠ (AxOpsem.grow GD i).length)
    (Hrow : (AxOpsem.grow GD i)[k]? = some (.LRmw true false (paZ pa) ts old new cls))
    (P : IProp GF)
    (Hcont : ∀ rs : RegFile, ⊢ P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (KK (.Ok (wordOfBytes n old, none))) rs, k⟩ .MaybeStuck i Φ) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkXaq pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
  have H : ⊢ ∀ rs : RegFile, P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memRead n 64 (rreqn n l3pAkXaq pa))) KK) rs, k⟩ .MaybeStuck i Φ := by
    iloeb as IH
    iintro %rs HP
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i Φ).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      have Hst' := Hst
      obtain ⟨lb, Hlk, Hidlb, _, -⟩ := Hst
      have Hlk' : (AxOpsem.grow GD i)[k]? = some lb := Hlk
      rw [Hrow] at Hlk'
      cases Hlk'
      have Hadv0 : aidentAdvRd id = 0 := by rw [← Hidlb]; rfl
      rw [if_neg (by rw [Hadv0]; decide)]
      iintro %v %Hgv %Hlen
      obtain ⟨lb', -, -, HK⟩ := nreadInvAny cpu _ n l3pAkXaq pa Hdev KK rs k id K v Hst' Hlen
      have Hb : v = old := by
        have Hgv' : graphValue GD (i, k) = some v := Hgv
        unfold graphValue at Hgv'
        rw [gxLblGrow, Hrow] at Hgv'
        simp only [Option.bind_some, lblValue, Option.some.injEq] at Hgv'
        exact Hgv'.symm
      rw [HK, Hadv0, Nat.add_zero, Hb]
      iapply shSkip
      inext
      iapply (Hcont rs) $$ HP
    isplit
    · iintro %l %s' %Hst %_
      exact (nrdAstepVacuous cpu _ n l3pAkXaq pa Hdev rfl _Hn KK rs k l s' Hst).elim
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu _ rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

/-- The RMW's WRITE half (n bytes, with the store-conditional retry). -/
theorem nshRmwWrite (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent)
    (Φ : Athread → IProp GF) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (k : Nat) (Hne : k ≠ (AxOpsem.grow GD i).length)
    (P : IProp GF)
    (Hb : ∀ rs : RegFile, ⊢ P -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphData GD (i, k) = some (WeakInterpProj.wbytes n val)) (fun _ => k + 1)
        (fun _ => tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ)) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) (fun _ => m')) rs, k⟩
      .MaybeStuck i Φ := by
  have H : ⊢ ∀ rs : RegFile, P -∗ tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkXpl pa val))) (fun _ => m')) rs, k⟩
      .MaybeStuck i Φ := by
    iloeb as IH
    iintro %rs HP
    iapply (AxSpinWit.twUnfold (hlc := hlc) GD N obSt0 obi nm _ i Φ).2
    isplit
    · simp only [progressObl]
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, Hloc⟩
    ihave Hok := AxSpinWit.gconstEq GD N obSt0 obi nm GD' $$ Hg
    icases Hok with %HGD
    subst GD'
    isplit
    · iintro %id %K %Hst
      exact (noReadAtNxwrite cpu _ n pa Hdev val m' rs k id K Hst).elim
    isplit
    · iintro %l %s' %Hst %_
      rcases nxwriteInv cpu _ n pa Hdev val m' rs k l s' Hst with ⟨Hwd, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Hwd]
        dsimp only
        iapply (Hb rs) $$ HP
      · dsimp only [wlWdata]
        iapply shSkip
        inext
        iapply IH $$ %rs HP
    isplit
    · iintro %s' %Hw
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu _ rs k s' Hw
      iapply shSkip
      inext
      iapply IH $$ %rs' HP
    · iintro %Heq
      exact (Hne Heq).elim
  iintro HP %rs
  iapply H $$ %rs HP

/-- A plain n-byte write node strictly inside the row. -/
theorem nshWrite (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent)
    (Φ : Athread → IProp GF) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (k : Nat) (Hne : k ≠ (AxOpsem.grow GD i).length)
    (P : IProp GF)
    (Hb : ∀ rs : RegFile, ⊢ P -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphData GD (i, k) = some (WeakInterpProj.wbytes n val)) (fun _ => k + 1)
        (fun _ => tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ)) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (wreqn n l3pAkP pa val))) (fun _ => m')) rs, k⟩
      .MaybeStuck i Φ := by
  refine shPos GD N obSt0 obi nm cpu i Φ P k _ Hne
    (fun rs' id K => noReadAtNwrite cpu _ n pa Hdev val m' rs' k id K) ?_
  intro rs' l s' Hst
  obtain ⟨Hwd, rfl⟩ := nwriteInv cpu _ n pa Hdev val m' rs' k l s' Hst
  rw [Hwd]
  exact Hb rs'

/-- A fence node strictly inside the row. -/
theorem nshFence (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent)
    (Φ : Athread → IProp GF) (m' : SailM Unit) (k : Nat) (Hne : k ≠ (AxOpsem.grow GD i).length)
    (P : IProp GF)
    (Hb : ∀ rs : RegFile, ⊢ P -∗
      ▷ tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs, k⟩
      .MaybeStuck i Φ := by
  refine shPos GD N obSt0 obi nm cpu i Φ P k _ Hne
    (fun rs' id K => noReadAtFence cpu _ m' rs' k id K) ?_
  intro rs' l s' Hst
  obtain ⟨rfl, rfl, -⟩ := fenceInv2 cpu _ m' rs' k l s' Hst
  iintro HP
  dsimp only [wlWdata]
  iapply shSkip
  iapply (Hb rs') $$ HP

end nshells

/-! # 4. n-byte label facts -/

theorem gwbStoren (G : Gexec) (e : Geid) (base : Int) (vs : List (BitVec 8)) (cls : WmClass) :
    gxLbl G e = some (.LStore false base vs cls) →
    (∀ (j : Nat) v, vs[j]? = some v → gwritesByte G e (base + (j : Int)) v) ∧
    (∀ a v, gwritesByte G e a v → ∃ j : Nat, vs[j]? = some v ∧ a = base + (j : Int)) := by
  intro Hl
  refine ⟨fun j v Hj => ⟨_, base, vs, j, Hl, rfl, Hj, rfl⟩, ?_⟩
  rintro a v ⟨l, base', vs', j, Hl', Hwr, Hv, Ha⟩
  rw [Hl] at Hl'
  cases Hl'
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
  obtain ⟨rfl, rfl⟩ := Hwr
  exact ⟨j, Hv, Ha.symm⟩

theorem grbLoadn (G : Gexec) (e : Geid) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl G e = some (.LLoad false base ts vs) →
    (∀ (j : Nat) t v, ts[j]? = some t → vs[j]? = some v → greadsByte G e (base + (j : Int)) t v) ∧
    (∀ a t v, greadsByte G e a t v →
      ∃ j : Nat, ts[j]? = some t ∧ vs[j]? = some v ∧ a = base + (j : Int)) := by
  intro Hl
  refine ⟨fun j t v Ht Hv => ⟨_, base, ts, vs, j, Hl, rfl, Ht, Hv, rfl⟩, ?_⟩
  rintro a t v ⟨l, base', ts', vs', j, Hl', Hrd, Ht, Hv, Ha⟩
  rw [Hl] at Hl'
  cases Hl'
  simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at Hrd
  obtain ⟨rfl, rfl, rfl⟩ := Hrd
  exact ⟨j, Ht, Hv, Ha.symm⟩

theorem gwbRmwn (G : Gexec) (e : Geid) (base : Int) (ts : List Nat) (old new : List (BitVec 8))
    (cls : WmClass) :
    gxLbl G e = some (.LRmw true false base ts old new cls) →
    (∀ (j : Nat) t v, ts[j]? = some t → old[j]? = some v → greadsByte G e (base + (j : Int)) t v) ∧
    (∀ (j : Nat) v, new[j]? = some v → gwritesByte G e (base + (j : Int)) v) ∧
    (∀ a v, gwritesByte G e a v → ∃ j : Nat, new[j]? = some v ∧ a = base + (j : Int)) ∧
    (∀ a t v, greadsByte G e a t v →
      ∃ j : Nat, ts[j]? = some t ∧ old[j]? = some v ∧ a = base + (j : Int)) := by
  intro Hl
  refine ⟨fun j t v Ht Hv => ⟨_, base, ts, old, j, Hl, rfl, Ht, Hv, rfl⟩,
    fun j v Hj => ⟨_, base, new, j, Hl, rfl, Hj, rfl⟩, ?_, ?_⟩
  · rintro a v ⟨l, base', vs', j, Hl', Hwr, Hv, Ha⟩
    rw [Hl] at Hl'
    cases Hl'
    simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hwr
    obtain ⟨rfl, rfl⟩ := Hwr
    exact ⟨j, Hv, Ha.symm⟩
  · rintro a t v ⟨l, base', ts', vs', j, Hl', Hrd, Ht, Hv, Ha⟩
    rw [Hl] at Hl'
    cases Hl'
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at Hrd
    obtain ⟨rfl, rfl, rfl⟩ := Hrd
    exact ⟨j, Ht, Hv, Ha.symm⟩

theorem storenNoRead (G : Gexec) (e : Geid) (base : Int) (vs : List (BitVec 8)) (cls : WmClass)
    (a : Int) (t : Nat) (v : BitVec 8) :
    gxLbl G e = some (.LStore false base vs cls) → ¬ greadsByte G e a t v := by
  rintro Hl ⟨l, base', ts, vs', j, Hl', Hrd, -⟩
  rw [Hl] at Hl'
  cases Hl'
  simp [lbRd] at Hrd

end Weak
