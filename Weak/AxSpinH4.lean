/-
Weak: **Phase 2b, part 1 of the spinlock plan -- n-BYTE nodes, the FRACTIONAL value-tracking
owned WORD, and the instance `spinOb6`** (lock byte + an owned WORD `xs` + lk->cpu `Cl`) with its
flow equations.  (Phase-2b files: this one; `AxSpinH5` handle leaves/contracts; `AxSpinH6`
certificate 1 `[lw x; lw x; addiw; sw x]`; `AxSpinH7` certificate 2, CS never touches the word.)

Rocq: `iris/AxSpinH4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 n-BYTE HAND NODES (`h4rreq`/`h4wreq`, `memRead n`/`memWrite n`, plain access only):
   program-step facts, the row-pinned runs `h4runRead`/`h4runWrite`, the WPd shells
   `h4shRead`/`h4shWrite`, the n-byte label facts.  In Rocq a SELF-CONTAINED COPY of the plain
   read/write part of `AxSpinX3` (renamed); here a thin layer over the ported `AxSpinX3`
   (deviation 4).
§2 `RbF γ GD q a e mv`: FRACTION `q` of byte `a`'s history auth, tied at `e`, last value `mv`;
   `RbN q xs e vs` = the bytes `xs` (value of byte `k` = `vs[k]?`; `vs = []` = unknown).
   `RL xs e ⊣⊢ RbN 1 xs e []`.  PROVED: `RbFSplit`/`RbNSplit` (a fraction splits at one anchor),
   `RbFJoin`/`RbNJoin` (TWO fractions at DIFFERENT anchors recombine at the first anchor; their
   values AGREE -- one history, `hvalDet`), `RbFRead`/`RbNRead` (the owned read needs only a
   FRACTION: `ownedReadRule` at `{[e := q]}`), `RbFStep`/`RbNWrite` (the n-byte owned write:
   every byte's history appended, ONE `ownInv` insertion); `nbSingleSource` (aligned n-byte
   reads: every byte of the range is read at the same write index -- `clSingleSource` at
   `clRange a n` via `clAlignedOfSd`).
§3 `spinOb6 lk xs Cl cv` = `spinOb5` with the single owned byte replaced by the byte list `xs`;
   `spinR6 = RL xs ∗ RL Cl`; `spinHobAlloc6`; flow equations `fe6Claim`, `fe6Release'`,
   `fe6LkreadHeld` (copies of the 1b ones), and the WORD rules `fe6RdN` (fractional owned read),
   `fe6WrN` (owned write, the old handle produced by any wand from `flowIn` -- recombination goes
   through it), `fe6PlainN` (plain read drawing nothing: forwarding).

## Deviations from Rocq

1. VOCABULARY (as `AxSpinProt5`/`AxSpinH`): `Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`, `N` widths ↦
   `Nat`, `gd_g GD` ↦ `GD.gdG`, `list_to_set` ↦ `LawfulSet.ofList`, `l !! k` ↦ `l[k]?`, `S k` ↦
   `k + 1`, `base.NoDup` ↦ `List.Nodup`, `Forall P Rs` ↦ `∀ Rj, Rj ∈ Rs → P Rj`, `dev0_state` ↦
   `OpaxWit.wtD0`; the Rocq notations `OWN`/`LK`/`R6`/`WN` are unfolded (`WN q ys e vs` ↦
   `RbN nm.1 GD q ys e vs`).
2. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's section mechanism includes them (§1 `cpu`; §1 shells `GD N obSt0 obi nm [pol] cpu`;
   §2 `γ GD`; §3 `lk xs Cl cv` / `lk xs Cl cv GT nm`, then `Hcons`/`HlkX` where `Proof using`
   names them; unused ones `_`-named).  O2 STAGE C (as `AxSpinProt2` deviation 1): Rocq's
   `Tf`/`T`/`img` arguments are gone (`h4RdAstepVacuous`, `h4WriteInv`, the shells).
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`; §1 runs' unused `axirisG Σ` dropped.  The
   local instances: `h4shG` ↦ `AxSpinWit`'s `shG` (the same `axGA2` record), `s6_pol` ↦
   `splPol GT` (passed explicitly), `s6_G` ↦ the reducible def `s6G lk xs Cl cv GT nm` (passed
   explicitly, as `AxSpinProt6.s5G`).
3. STAGE C at §1 (as `AxSpinX3` deviations 1–3): `h4ReadStep`'s `ak_coh (classify ak) = false`
   ↦ `(classify ak).akIfetch = false` and its label is `rdLabel false …`; `h4RdAstepVacuous`
   takes `(classify ak).akIfetch = false` (a fetch is an admin step; Rocq refuted the fetch arm
   with `Hn`, kept as `_Hn`); RAM write answers `.Ok (some true)` (Rocq `inl None`), read answers
   `.Ok (w, none)`.
4. §1 is NOT re-proved: `h4rreq`/`h4wreq` are `abbrev`s of `AxSpinX3.rreqn`/`wreqn` (Rocq: copies
   of the same records), and each §1 lemma is proved by its `AxSpinX3` twin (`nreadStep`, …,
   `nshWrite`), so `AxSpinX3`/`AxSpinH4` statements interoperate.
5. STATEMENT SHAPES (as `AxSpinH` deviation 3): §2 `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`, `P -∗ Q ==∗ R`
   ↦ `P ∗ Q ⊢ |==> R`; §3 wand chains ↦ `⊢ A -∗ B -∗ …`; pure premises stay `→`.
6. PROOF ROUTE (not statements): `RbFRead` case-splits on `H.getLast?` (as `AxSpinH.RboRead`);
   the `big_sepL_impl`/`big_sepL_bupd` steps of `RbNRead`/`RbNWrite` go through `bigSepL_impl`/
   `bigSepL_mono` + `bigSepL_bupd`.

**Rocq → Lean name map.**  `h4rreq` `h4rreq`, `h4wreq` `h4wreq`, `h4_tvs_wbytes` `h4TvsWbytes`,
`h4_read_step` `h4ReadStep`, `h4_write_step` `h4WriteStep`, `h4_write_det` `h4WriteDet`,
`h4_read_inv` `h4ReadInv`, `h4_rd_astep_vacuous` `h4RdAstepVacuous`, `h4_write_inv`
`h4WriteInv`, `h4_no_read_at_write` `h4NoReadAtWrite`, `h4run_read` `h4runRead`, `h4run_write`
`h4runWrite`, `h4sh_read` `h4shRead`, `h4sh_write` `h4shWrite`, `cl_range_length`
`clRangeLength`, `cl_range_lookup` `AxSpinH4.clRangeLookup` (duplicated name, AxSpinX4),
`loadN_bytes` `loadNBytes`, `storeN_bytes` `storeNBytes`, `nb_single_source` `nbSingleSource`,
`hval_det` `hvalDet`, `RbF` `RbF`, `RbF_Rbo` `RbFRbo`, `RbF_Rb` `RbFRb`, `RbF_forget`
`RbFForget`, `RbF_split` `RbFSplit`, `RbF_join` `RbFJoin`, `RbF_read` `RbFRead`, `RbF_step`
`RbFStep`, `RbN` `RbN`, `RL_RbN` `RLRbN`, `RbN_RL` `RbNRL`, `RbN_split` `RbNSplit`, `RbN_join`
`RbNJoin`, `RbN_read` `RbNRead`, `RbN_write` `RbNWrite`, `X6` `X6`, `spin_ob6` `spinOb6`,
`spin_R6` `spinR6`, `spin_init6` `spinInit6`, `spin_R6_transportable` `spinR6Transportable`,
`spin_Hob_alloc6` `spinHobAlloc6`, `s6_G` `s6G`, `fe6_build` `fe6Build`, `lkw6_nX` `lkw6NX`,
`lkw6_cpu` `lkw6Cpu`, `nw6_nX` `nw6NX`, `nw6_cpu` `nw6Cpu`, `fe6_claim` `fe6Claim`,
`fe6_release'` `fe6Release'`, `fe6_lkread_held` `fe6LkreadHeld`, `ldN_facts` `ldNFacts`,
`fe6_rdN` `fe6RdN`, `fe6_plainN` `fe6PlainN`, `fe6_wrN` `fe6WrN`.
Lean-only (file-qualified): `AxSpinH4.tokTieSingletonQ` (`AxSpinProt.tokTieSingleton` at any
fraction), `AxSpinH4.histInOfCovQ` (`AxSpinH.histInOfCov` at any fraction).

**Dropped:** none (56 Rocq decls = 53 + the local instances `h4shG`/`s6_pol` (inlined) and
`s6_G`; 56 Lean = 53 + `s6G` + 2 Lean-only).
-/
import Weak.AxSpinH
import Weak.AxSpinX3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. n-byte hand nodes (over `AxSpinX3`) -/

abbrev h4rreq (n : Nat) (ak : AK) (pa : PAddr) :
    Mem_read_request n 64 Arch.pa Arch.translation Arch.arch_ak :=
  rreqn n ak pa

abbrev h4wreq (n : Nat) (ak : AK) (pa : PAddr) (v : BitVec (8 * n)) :
    Mem_write_request n 64 Arch.pa Arch.translation Arch.arch_ak :=
  wreqn n ak pa v

theorem h4TvsWbytes (n : Nat) (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) :
    tvs.length = n → (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    tvs.map Prod.snd = WeakInterpProj.wbytes n w :=
  tvsWbytes n w tvs

section h4steps
variable (cpu : CPU)

theorem h4ReadStep (n : Nat) (ak : AK) (pa : PAddr) :
    devAddr pa = false → (classify ak).akIfetch = false →
    ∀ (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
      (ib : Ibch) (d : Efab) (vs : List (BitVec 8)),
    vs.length = n →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n 64 (h4rreq n ak pa))) KK) rs none ib) d
      (rdLabel false (classify ak).akLatest (classify ak).akSync (paZ pa) (tagVals vs)
        (rdAsrc (classify ak).akLatest ib))
      (.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib) d :=
  nreadStep cpu n ak pa

theorem h4WriteStep (n : Nat) (Hn : n ≠ 0) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) KK) rs none ib)
      d
      (.LStore false (paZ pa) (WeakInterpProj.wbytes n val)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (.PHart cpu (KK (.Ok (some true))) rs none ib) d :=
  nwritePlainStep cpu n Hn pa Hdev val

theorem h4WriteDet (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false) (val : BitVec (8 * n)) :
    ∀ (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
      (l : Wlabel) (p' : Pexv6) (d' : Efab),
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) KK) rs none ib)
      d l p' d' →
    l = .LStore false (paZ pa) (WeakInterpProj.wbytes n val)
          (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)) ∧
    p' = .PHart cpu (KK (.Ok (some true))) rs none ib ∧ d' = d :=
  nwritePlainDet cpu n pa Hdev val

theorem h4ReadInv (row : List Lbl) (n : Nat) (ak : AK) (pa : PAddr) (Hdev : devAddr pa = false)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (id : AidentT) (K : List (BitVec 8) → Athread) (v : List (BitVec 8)) :
    areadStep row ⟨hp cpu (.impure (.ok (.memRead n 64 (h4rreq n ak pa))) KK) rs, k⟩ id K →
    v.length = aidentN id →
    ∃ lb, row[k]? = some lb ∧ aident lb = id ∧
      K v = ⟨hp cpu (KK (.Ok (wordOfBytes n v, none))) rs, k + aidentAdvRd id⟩ :=
  nreadInvAny cpu row n ak pa Hdev KK rs k id K v

theorem h4RdAstepVacuous (row : List Lbl) (n : Nat) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hfe : (classify ak).akIfetch = false) (_Hn : n ≠ 0)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row ⟨hp cpu (.impure (.ok (.memRead n 64 (h4rreq n ak pa))) KK) rs, k⟩
      l s' → False :=
  nrdAstepVacuous cpu row n ak pa Hdev Hfe _Hn KK rs k l s'

theorem h4WriteInv (row : List Lbl) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat) (l : Wlabel)
    (s' : Athread) :
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) (fun _ => m')) rs, k⟩
      l s' →
    wlWdata l = some (WeakInterpProj.wbytes n val) ∧ s' = ⟨hp cpu m' rs, k + 1⟩ :=
  nwriteInv cpu row n pa Hdev val m' rs k l s'

theorem h4NoReadAtWrite (row : List Lbl) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat) (id : AidentT)
    (K : List (BitVec 8) → Athread) :
    ¬ areadStep row
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) (fun _ => m')) rs, k⟩
      id K :=
  noReadAtNwrite cpu row n pa Hdev val m' rs k id K

end h4steps

section h4runs
variable (cpu : CPU)

theorem h4runRead (GD : Gdexec) (i : Agent) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (ts : List Nat) (vs : List (BitVec 8))
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat) :
    (AxOpsem.grow GD i)[k]? = some (.LLoad false (paZ pa) ts vs) → vs.length = n →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memRead n 64 (h4rreq n l3pAkP pa))) KK) rs, k⟩
      ⟨hp cpu (KK (.Ok (wordOfBytes n vs, none))) rs, k + 1⟩ :=
  nrunRead cpu GD i n pa Hdev ts vs KK rs k

theorem h4runWrite (GD : Gdexec) (i : Agent) (n : Nat) (Hn : n ≠ 0) (pa : PAddr)
    (Hdev : devAddr pa = false) (val : BitVec (8 * n)) (m' : SailM Unit) (rs : RegFile) (k : Nat)
    (cls : WmClass) :
    (AxOpsem.grow GD i)[k]? = some (.LStore false (paZ pa) (WeakInterpProj.wbytes n val) cls) →
    astepAnyNfGv GD i
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) (fun _ => m')) rs, k⟩
      ⟨hp cpu m' rs, k + 1⟩ :=
  nrunWrite cpu GD i n Hn pa Hdev val m' rs k cls

end h4runs

section h4shells
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [pol : Axpol]

theorem h4shRead (GD : Gdexec) (N obSt0 : Type) (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF)
    (nm : N) (cpu : CPU) (i : Agent) (Φ : Athread → IProp GF) (n : Nat) (Hn : n ≠ 0)
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
      ⟨hp cpu (.impure (.ok (.memRead n 64 (h4rreq n l3pAkP pa))) KK) rs, k⟩ .MaybeStuck i Φ :=
  nshRead GD N obSt0 obi nm cpu i Φ n Hn pa Hdev KK k Hne Hrow P Hcont

theorem h4shWrite (GD : Gdexec) (N obSt0 : Type)
    (obi : N → Gdexec → obSt0 → GSet Geid → IProp GF) (nm : N) (cpu : CPU) (i : Agent)
    (Φ : Athread → IProp GF) (n : Nat) (pa : PAddr) (Hdev : devAddr pa = false)
    (val : BitVec (8 * n)) (m' : SailM Unit) (k : Nat) (Hne : k ≠ (AxOpsem.grow GD i).length)
    (P : IProp GF)
    (Hb : ∀ rs : RegFile, ⊢ P -∗
      @wpEvStep hlc GF _ (shG GD N obSt0 obi nm) pol Unit GD i k (fun _ => True)
        (fun _ => graphData GD (i, k) = some (WeakInterpProj.wbytes n val)) (fun _ => k + 1)
        (fun _ => tierAWpd (hlc := hlc) GD N obSt0 obi nm ⟨hp cpu m' rs, k + 1⟩ .MaybeStuck i Φ)) :
    ⊢ P -∗ ∀ rs : RegFile, tierAWpd (hlc := hlc) GD N obSt0 obi nm
      ⟨hp cpu (.impure (.ok (.memWrite n 64 (h4wreq n l3pAkP pa val))) (fun _ => m')) rs, k⟩
      .MaybeStuck i Φ :=
  nshWrite GD N obSt0 obi nm cpu i Φ n pa Hdev val m' k Hne P Hb

end h4shells

/-! ## n-byte label facts over `clRange` -/

theorem clRangeLength (a : Int) (n : Nat) : (clRange a n).length = n := by
  simp [clRange]

theorem AxSpinH4.clRangeLookup (a : Int) (n k : Nat) (b : Int) :
    (clRange a n)[k]? = some b ↔ k < n ∧ b = a + (k : Int) := by
  unfold clRange
  rw [List.getElem?_map]
  by_cases hk : k < n
  · rw [List.getElem?_range hk]
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun h => ⟨hk, h.symm⟩, fun h => h.2.symm⟩
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [Option.map_none, reduceCtorEq, false_iff]
    exact fun h => hk h.1

theorem loadNBytes (G : Gexec) (r : Geid) (a : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl G r = some (.LLoad false a ts vs) → ts.length = vs.length →
    (∀ (k : Nat) b, (clRange a vs.length)[k]? = some b →
      ∃ t v, ts[k]? = some t ∧ vs[k]? = some v ∧ greadsByte G r b t v) ∧
    (∀ b t v, greadsByte G r b t v → b ∈ clRange a vs.length) := by
  intro Hl Hlen
  obtain ⟨Hrd, Honly⟩ := grbLoadn G r a ts vs Hl
  refine ⟨fun k b Hk => ?_, fun b t v Hr => ?_⟩
  · obtain ⟨Hk', rfl⟩ := (AxSpinH4.clRangeLookup a vs.length k b).1 Hk
    have Ht : ts[k]? = some ts[k] := List.getElem?_eq_getElem (by omega)
    have Hv : vs[k]? = some vs[k] := List.getElem?_eq_getElem Hk'
    exact ⟨_, _, Ht, Hv, Hrd k _ _ Ht Hv⟩
  · obtain ⟨j, -, Hv, rfl⟩ := Honly b t v Hr
    exact List.mem_of_getElem? ((AxSpinH4.clRangeLookup a vs.length j _).2
      ⟨(List.getElem?_eq_some_iff.1 Hv).1, rfl⟩)

theorem storeNBytes (G : Gexec) (w : Geid) (a : Int) (bs : List (BitVec 8)) (cls : WmClass) :
    gxLbl G w = some (.LStore false a bs cls) →
    (∀ (k : Nat) b, (clRange a bs.length)[k]? = some b →
      ∃ v, bs[k]? = some v ∧ gwritesByte G w b v) ∧
    (∀ b v, gwritesByte G w b v → b ∈ clRange a bs.length) := by
  intro Hl
  obtain ⟨Hwr, Honly⟩ := gwbStoren G w a bs cls Hl
  refine ⟨fun k b Hk => ?_, fun b v Hw => ?_⟩
  · obtain ⟨Hk', rfl⟩ := (AxSpinH4.clRangeLookup a bs.length k b).1 Hk
    have Hv : bs[k]? = some bs[k] := List.getElem?_eq_getElem Hk'
    exact ⟨_, Hv, Hwr k _ Hv⟩
  · obtain ⟨j, Hv, rfl⟩ := Honly b v Hw
    exact List.mem_of_getElem? ((AxSpinH4.clRangeLookup a bs.length j _).2
      ⟨(List.getElem?_eq_some_iff.1 Hv).1, rfl⟩)

/-- THE n-BYTE SINGLE-SOURCE LEMMA for an ALIGNED word: if every write touching `[a, a+n)` is a
full-width write based at `a`, every byte of the range a read touches is read at the SAME write
index. -/
theorem nbSingleSource (G : Gexec) (a : Int) (n : Nat) (r : Geid) (b b' : Int) (t t' : Nat)
    (v v' : BitVec 8) :
    gwf G → gloadValue G →
    (∀ w b0 v0, b0 ∈ clRange a n → gwritesByte G w b0 v0 →
      ∃ l vs, gxLbl G w = some l ∧ lbWr l = some (a, vs) ∧ vs.length = n) →
    b ∈ clRange a n → b' ∈ clRange a n →
    greadsByte G r b t v → greadsByte G r b' t' v' → t = t' := by
  intro Hwf Hlv Hsd Hb Hb' Hr Hr'
  exact clSingleSource (clRange a n) G r b b' t t' v v' Hwf Hlv (clAlignedOfSd G a n Hsd) Hb Hb'
    Hr Hr'

/-! # 2. THE FRACTIONAL VALUE-TRACKING WORD -/

theorem hvalDet (G : Gexec) (a : Int) (H : List Hent) (v1 v2 : BitVec 8) :
    hval G a H v1 → hval G a H v2 → v1 = v2 := by
  rintro (⟨Hn1, H1⟩ | ⟨w1, H1⟩) (⟨Hn2, H2⟩ | ⟨w2, H2⟩)
  · rw [H1] at H2
    exact Option.some.inj H2
  · subst Hn1
    simp at H2
  · subst Hn2
    simp at H1
  · rw [H1] at H2
    simp only [Option.some.injEq, Prod.mk.injEq] at H2
    exact H2.2

section rbf
variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- FRACTION `q` of byte `a`'s history auth, tied at `e`, last value `mv`. -/
def RbF (γ : GName) (GD : Gdexec) (q : Qp) (a : Int) (e : Geid) (mv : Option (BitVec 8)) :
    IProp GF :=
  iprop(∃ H, histAuth γ a q H ∗
    ⌜(H = [] ∨ tieBase GD.gdG (H.map Prod.fst) e) ∧ hwfa GD a H ∧
      ∀ v, mv = some v → hval GD.gdG a H v⌝)

theorem RbFRbo (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) (mv : Option (BitVec 8)) :
    RbF (GF := GF) γ GD 1 a e mv ⊣⊢ Rbo γ GD a e mv := by
  unfold RbF Rbo
  exact BiEntails.of_eq rfl

theorem RbFRb (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) :
    RbF (GF := GF) γ GD 1 a e none ⊣⊢ Rb γ GD a e :=
  (RbFRbo γ GD a e none).trans ⟨RboRb γ GD a e none, RboOfRb γ GD a e⟩

theorem RbFForget (γ : GName) (GD : Gdexec) (q : Qp) (a : Int) (e : Geid)
    (mv : Option (BitVec 8)) :
    RbF (GF := GF) γ GD q a e mv ⊢ RbF γ GD q a e none := by
  unfold RbF
  iintro ⟨%H, Ha, %hp⟩
  iexists H
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    exact ⟨hp.1, hp.2.1, fun _ h => by cases h⟩

theorem RbFSplit (γ : GName) (GD : Gdexec) (q1 q2 : Qp) (a : Int) (e : Geid)
    (mv : Option (BitVec 8)) :
    RbF (GF := GF) γ GD (q1 + q2) a e mv ⊢ RbF γ GD q1 a e mv ∗ RbF γ GD q2 a e mv := by
  unfold RbF
  iintro ⟨%H, Ha, %hp⟩
  icases histSplit γ a q1 q2 H $$ Ha with ⟨H1, H2⟩
  isplitl [H1]
  · iexists H
    isplitl [H1]
    · iexact H1
    · ipureintro
      exact hp
  · iexists H
    isplitl [H2]
    · iexact H2
    · ipureintro
      exact hp

/-- RECOMBINATION: two fractions (any anchors) are fractions of ONE history, so they join
(re-tied at the first anchor) and their recorded last values AGREE. -/
theorem RbFJoin (γ : GName) (GD : Gdexec) (q1 q2 : Qp) (a : Int) (e1 e2 : Geid)
    (mv1 mv2 : Option (BitVec 8)) :
    RbF (GF := GF) γ GD q1 a e1 mv1 ∗ RbF γ GD q2 a e2 mv2 ⊢
      RbF γ GD (q1 + q2) a e1 mv1 ∗ ⌜∀ v1 v2, mv1 = some v1 → mv2 = some v2 → v1 = v2⌝ := by
  unfold RbF
  iintro ⟨⟨%H1, Ha1, %hp1⟩, ⟨%H2, Ha2, %hp2⟩⟩
  icases (persistent_entails_left (histAgree (GF := GF) γ a q1 q2 H1 H2)) $$ [$Ha1 $Ha2]
    with ⟨⟨Ha1, Ha2⟩, %hag⟩
  obtain ⟨rfl, -⟩ := hag
  ihave Ha := histJoin γ a q1 q2 H1 $$ [$Ha1 $Ha2]
  isplitl [Ha]
  · iexists H1
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      exact hp1
  · ipureintro
    intro v1 v2 E1 E2
    exact hvalDet _ _ _ _ _ (hp1.2.2 v1 E1) (hp2.2.2 v2 E2)

/-- (Lean-only) `AxSpinProt.tokTieSingleton` at any fraction `q`. -/
theorem AxSpinH4.tokTieSingletonQ (GD : Gdexec) (γ : GName) (x : Int) (H : List Hent) (e : Geid)
    (q : Qp) (ht : tieBase GD.gdG (H.map Prod.fst) e) :
    histAuth (GF := GF) γ x q H ⊣⊢ tokTie GD γ x H {[e := q]} := by
  constructor
  · unfold tokTie
    iintro Ha
    isplitl [Ha]
    · iapply (tokSingleton γ x H e q).2
      iexact Ha
    · ipureintro
      intro e' he'
      rw [domSingleton, elemOfSingleton] at he'
      subst he'
      exact ht
  · iintro HT
    iapply (tokSingleton γ x H e q).1
    iapply tokTieTok GD γ x H
    iexact HT

/-- (Lean-only) `AxSpinH.histInOfCov` at any fraction `q`. -/
theorem AxSpinH4.histInOfCovQ (γ : GName) (GD : Gdexec) (a : Int) (r : Geid) (q : Qp)
    (H : List Hent) :
    histAuth (GF := GF) γ a q H ∗
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') ⊢
      ⌜∀ w v', gwritesByte GD.gdG w a v' → gmoLt GD.gdG w r → w ∈ H.map Prod.fst⌝ := by
  refine (BI.forall_intro fun w => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun v => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun hw => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun hlt => ?_).trans BI.pure_forall.2
  iintro ⟨Ha, Hcov⟩
  icases Hcov $$ %w %v %hw %hlt with ⟨%H', %hw', Hs⟩
  iapply histSnapIn γ a q H H' w hw'
  isplitl [Ha]
  · iexact Ha
  · iexact Hs

/-- THE OWNED READ WITH A FRACTION (`RboRead` at any `q`). -/
theorem RbFRead (γ : GName) (GD : Gdexec) (X : GSet Int) (q : Qp) (a : Int) (s : GSet Geid)
    (e r : Geid) (t : Nat) (v : BitVec 8) (mv : Option (BitVec 8)) :
    rvwmoCatConsistent GD → a ∈ X → greadsByte GD.gdG r a t v → gmoLt GD.gdG e r →
    WPh GD.gdG s r →
    (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
    ownInv (GF := GF) X γ GD s ∗ RbF γ GD q a e mv ⊢
      RbF γ GD q a r (some v) ∗ ⌜∀ v0, mv = some v0 → v = v0⌝ := by
  intro hcons haX hrd her hwp hfw
  unfold RbF
  iintro ⟨#Hinv, %H, Ha, %hp⟩
  obtain ⟨ht, ⟨hwr, hch⟩, hmv⟩ := hp
  ihave #Hcov := AxSpinProt5.covMoX γ X a GD s r haX hwp $$ Hinv
  icases (persistent_entails_left (AxSpinH4.histInOfCovQ (GF := GF) γ GD a r q H))
    $$ [$Ha $Hcov] with ⟨⟨Ha, -⟩, %hin⟩
  cases hlast : H.getLast? with
  | none =>
    have hnil : H = [] := List.getLast?_eq_none_iff.1 hlast
    subst hnil
    have himg : GD.gdG.gxImg a = some v := by
      cases t with
      | zero => exact (hcons.2.2.1 r a 0 v hrd).1
      | succ j =>
        obtain ⟨w, -, hw', hvis⟩ := (hcons.2.2.1 r a (j + 1) v hrd).1
        have hlt : gmoLt GD.gdG w r := hvis.elim id (hfw w v hw')
        have := hin w v hw' hlt
        simp at this
    isplitl [Ha]
    · iexists ([] : List Hent)
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        refine ⟨Or.inl rfl, hwfaNil GD a, fun v' hv' => ?_⟩
        cases hv'
        exact Or.inl ⟨rfl, himg⟩
    · ipureintro
      intro v0 hv0
      rcases hmv v0 hv0 with ⟨-, hi⟩ | ⟨w, hw⟩
      · rw [himg] at hi
        exact Option.some.inj hi
      · simp at hw
  | some p =>
    obtain ⟨wl, vl⟩ := p
    have hne : H ≠ [] := by
      intro h
      subst h
      simp at hlast
    have ht' : tieBase GD.gdG (H.map Prod.fst) e := ht.resolve_left hne
    have hown : ∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
        w ∈ H.map Prod.fst := fun w v' hw' hp => hin w v' hw' (hfw w v' hw' hp)
    ihave HT := (AxSpinH4.tokTieSingletonQ GD γ a H e q ht').1 $$ Ha
    icases (persistent_entails_left (ownedReadRule (GF := GF) GD a r γ H {[e := q]} wl vl
        hcons hwr hch hown hlast ⟨t, v, hrd⟩
        (Or.inl ⟨e, by rw [domSingleton, elemOfSingleton], her⟩)))
      $$ [$HT $Hcov] with ⟨⟨HT, -⟩, %hv⟩
    have hvl : v = vl := hv.2 t v hrd
    subst vl
    ihave Ha := (AxSpinH4.tokTieSingletonQ GD γ a H e q ht').2 $$ HT
    isplitl [Ha]
    · iexists H
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        refine ⟨Or.inr (tieLob _ _ e r ht' her), ⟨hwr, hch⟩, fun v' hv' => ?_⟩
        cases hv'
        exact Or.inr ⟨wl, hlast⟩
    · ipureintro
      intro v0 hv0
      rcases hmv v0 hv0 with ⟨h, -⟩ | ⟨w, hw⟩
      · exact absurd h hne
      · rw [hlast] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        exact hw.2

/-- ONE BYTE OF AN OWNED WRITE (full fraction): append, re-tie at `w`, hand out the snapshot for
the event's `ownInv` deposit. -/
theorem RbFStep (γ : GName) (GD : Gdexec) (a : Int) (e w : Geid) (b : BitVec 8)
    (mv : Option (BitVec 8)) :
    gmoLt GD.gdG e w → gwritesByte GD.gdG w a b →
    RbF (GF := GF) γ GD 1 a e mv ⊢ |==> (RbF γ GD 1 a w (some b) ∗
      ∃ H, histSnap γ a H ∗ ⌜H.getLast? = some (w, b)⌝) := by
  intro hew hw
  unfold RbF
  iintro ⟨%H, Ha, %hp⟩
  obtain ⟨ht, ⟨hwr, hch⟩, -⟩ := hp
  imod histAppend γ a H (w, b) $$ Ha with Ha
  ihave #Hsn := histSnapGet γ a 1 (H ++ [(w, b)]) $$ Ha
  imodintro
  isplitl [Ha]
  · iexists (H ++ [(w, b)])
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      refine ⟨Or.inr (tieWrite GD.gdG H w b), ⟨?_, ?_⟩, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with h | h
        · exact hwr p h
        · simp only [List.mem_singleton] at h
          subst h
          exact hw
      · rw [List.map_append]
        refine AxSpinProt.chainWithSnoc' _ _ w hch ?_
        intro wl hl
        rcases ht with rfl | ht | ⟨wl', ht, hlt⟩
        · simp at hl
        · rw [ht] at hl
          cases hl
          exact hew
        · rw [ht] at hl
          cases hl
          exact gmoLtTrans _ _ _ _ hlt hew
      · intro v hv
        cases hv
        unfold hval
        exact Or.inr ⟨w, by simp⟩
  · iexists (H ++ [(w, b)])
    isplitl []
    · iexact Hsn
    · ipureintro
      simp

/-- THE WORD: bytes `xs`, byte `k`'s value `vs[k]?` (`vs = []`: unknown). -/
def RbN (γ : GName) (GD : Gdexec) (q : Qp) (xs : List Int) (e : Geid) (vs : List (BitVec 8)) :
    IProp GF :=
  iprop([∗list] k ↦ a ∈ xs, RbF γ GD q a e vs[k]?)

theorem RLRbN (γ : GName) (GD : Gdexec) (xs : List Int) (e : Geid) :
    RL (GF := GF) γ GD xs e ⊣⊢ RbN γ GD 1 xs e [] := by
  unfold RL RbN
  constructor
  · exact BigSepL.bigSepL_mono fun {k a} _ => by
      rw [List.getElem?_nil]
      exact (RbFRb γ GD a e).2
  · exact BigSepL.bigSepL_mono fun {k a} _ => by
      rw [List.getElem?_nil]
      exact (RbFRb γ GD a e).1

theorem RbNRL (γ : GName) (GD : Gdexec) (xs : List Int) (e : Geid) (vs : List (BitVec 8)) :
    RbN (GF := GF) γ GD 1 xs e vs ⊢ RL γ GD xs e := by
  unfold RL RbN
  exact BigSepL.bigSepL_mono fun {k a} _ =>
    (RbFForget γ GD 1 a e _).trans (RbFRb γ GD a e).1

theorem RbNSplit (γ : GName) (GD : Gdexec) (q1 q2 : Qp) (xs : List Int) (e : Geid)
    (vs : List (BitVec 8)) :
    RbN (GF := GF) γ GD (q1 + q2) xs e vs ⊢ RbN γ GD q1 xs e vs ∗ RbN γ GD q2 xs e vs := by
  unfold RbN
  exact (BigSepL.bigSepL_mono fun {k a} _ => RbFSplit γ GD q1 q2 a e _).trans
    BigSepL.bigSepL_sep_eqv.1

theorem RbNJoin (γ : GName) (GD : Gdexec) (q1 q2 : Qp) (xs : List Int) (e1 e2 : Geid)
    (vs1 vs2 : List (BitVec 8)) :
    RbN (GF := GF) γ GD q1 xs e1 vs1 ∗ RbN γ GD q2 xs e2 vs2 ⊢
      RbN γ GD (q1 + q2) xs e1 vs1 ∗
      ⌜∀ (k : Nat) a v1 v2, xs[k]? = some a → vs1[k]? = some v1 → vs2[k]? = some v2 →
        v1 = v2⌝ := by
  unfold RbN
  refine (BigSepL.bigSepL_sep_eqv
    (Φ := fun k a => RbF (GF := GF) γ GD q1 a e1 vs1[k]?)
    (Ψ := fun k a => RbF (GF := GF) γ GD q2 a e2 vs2[k]?) (l := xs)).2.trans ?_
  refine (BigSepL.bigSepL_mono
    (Ψ := fun k a => iprop(RbF (GF := GF) γ GD (q1 + q2) a e1 vs1[k]? ∗
      ⌜∀ v1 v2, vs1[k]? = some v1 → vs2[k]? = some v2 → v1 = v2⌝))
    fun {k a} _ => RbFJoin γ GD q1 q2 a e1 e2 _ _).trans ?_
  refine (BigSepL.bigSepL_sep_eqv
    (Φ := fun k a => RbF (GF := GF) γ GD (q1 + q2) a e1 vs1[k]?)
    (Ψ := fun k _ => iprop(⌜∀ v1 v2, vs1[k]? = some v1 → vs2[k]? = some v2 → v1 = v2⌝ :
      IProp GF)) (l := xs)).1.trans ?_
  iintro ⟨HR, HP⟩
  ihave %hP := (BigSepL.bigSepL_pure_intro
    (φ := fun k (_ : Int) => ∀ v1 v2, vs1[k]? = some v1 → vs2[k]? = some v2 → v1 = v2)
    (l := xs) (PROP := IProp GF)) $$ HP
  isplitl [HR]
  · iexact HR
  · ipureintro
    intro k a v1 v2 ha E1 E2
    exact hP k a ha v1 v2 E1 E2

/-- THE OWNED WORD READ (fraction `q`): every byte re-tied at `r` with the read value; the old
values (if known) agree with the read ones. -/
theorem RbNRead (γ : GName) (GD : Gdexec) (X : GSet Int) (q : Qp) (xs : List Int)
    (s : GSet Geid) (e r : Geid) (ts : List Nat) (vs mv : List (BitVec 8)) :
    rvwmoCatConsistent GD → (∀ a, a ∈ xs → a ∈ X) →
    (∀ (k : Nat) a, xs[k]? = some a →
      ∃ t v, ts[k]? = some t ∧ vs[k]? = some v ∧ greadsByte GD.gdG r a t v) →
    gmoLt GD.gdG e r → WPh GD.gdG s r →
    (∀ a w v', a ∈ xs → gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
      gmoLt GD.gdG w r) →
    ownInv (GF := GF) X γ GD s ∗ RbN γ GD q xs e mv ⊢
      RbN γ GD q xs r vs ∗
      ⌜∀ (k : Nat) a v0 v, xs[k]? = some a → mv[k]? = some v0 → vs[k]? = some v → v = v0⌝ := by
  intro hcons hX hrd her hwp hfw
  unfold RbN
  iintro ⟨#Hinv, HR⟩
  ihave HR := (BigSepL.bigSepL_impl
    (Φ := fun k a => RbF (GF := GF) γ GD q a e mv[k]?)
    (Ψ := fun k a => iprop(RbF (GF := GF) γ GD q a r vs[k]? ∗
      ⌜∀ v0 v, mv[k]? = some v0 → vs[k]? = some v → v = v0⌝)) (l := xs)) $$ HR
  ihave HR := HR $$ []
  · imodintro
    iintro %k %a %hk Ha
    obtain ⟨t, v, -, hv, hr⟩ := hrd k a hk
    have hax : a ∈ xs := List.mem_of_getElem? hk
    icases (RbFRead γ GD X q a s e r t v mv[k]? hcons (hX a hax) hr her hwp
      (fun w v' hw hpo => hfw a w v' hax hw hpo)) $$ [$Hinv $Ha] with ⟨Ha, %hf⟩
    rw [hv]
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      intro v0 v' E0 Ev
      cases Ev
      exact hf v0 E0
  icases (BigSepL.bigSepL_sep_eqv
    (Φ := fun k a => RbF (GF := GF) γ GD q a r vs[k]?)
    (Ψ := fun k _ => iprop(⌜∀ v0 v, mv[k]? = some v0 → vs[k]? = some v → v = v0⌝ : IProp GF))
    (l := xs)).1 $$ HR with ⟨HR, HP⟩
  ihave %hP := (BigSepL.bigSepL_pure_intro
    (φ := fun k (_ : Int) => ∀ v0 v, mv[k]? = some v0 → vs[k]? = some v → v = v0)
    (l := xs) (PROP := IProp GF)) $$ HP
  isplitl [HR]
  · iexact HR
  · ipureintro
    intro k a v0 v ha E0 Ev
    exact hP k a ha v0 v E0 Ev

/-- THE OWNED WORD WRITE (full fraction): every byte appended and re-tied at `w`; `w`'s `ownInv`
deposit made ONCE. -/
theorem RbNWrite (γ : GName) (GD : Gdexec) (X : GSet Int) (xs : List Int) (s : GSet Geid)
    (e w : Geid) (mv bs : List (BitVec 8)) :
    w ∉ s → gmoLt GD.gdG e w →
    (∀ (k : Nat) a, xs[k]? = some a → ∃ b, bs[k]? = some b ∧ gwritesByte GD.gdG w a b) →
    (∀ a v, gwritesByte GD.gdG w a v → a ∈ xs) →
    ownInv (GF := GF) X γ GD s ∗ RbN γ GD 1 xs e mv ⊢
      |==> (ownInv X γ GD (({w} : GSet Geid) ∪ s) ∗ RbN γ GD 1 xs w bs) := by
  intro hn hew hall honly
  have hstep : iprop([∗list] k ↦ a ∈ xs, RbF (GF := GF) γ GD 1 a e mv[k]?) ⊢
      iprop(|==> [∗list] k ↦ a ∈ xs, RbF (GF := GF) γ GD 1 a w bs[k]? ∗
        ∃ v H, ⌜gwritesByte GD.gdG w a v⌝ ∗ histSnap (GF := GF) γ a H ∗
          ⌜H.getLast? = some (w, v)⌝) := by
    refine (BigSepL.bigSepL_mono fun {k a} hk => ?_).trans (BigSepL.bigSepL_bupd _ _)
    obtain ⟨b, hb, hw⟩ := hall k a hk
    rw [hb]
    refine (RbFStep γ GD a e w b _ hew hw).trans ?_
    iintro H
    imod H with ⟨Ha, %H, #Hs, %hl⟩
    imodintro
    isplitl [Ha]
    · iexact Ha
    · iexists b
      iexists H
      isplitl []
      · ipureintro
        exact hw
      isplitl []
      · iexact Hs
      · ipureintro
        exact hl
  unfold RbN ownInv
  iintro ⟨#Hinv, HR⟩
  ihave HR := hstep $$ HR
  imod HR
  icases (BigSepL.bigSepL_sep_eqv
    (Φ := fun k a => RbF (GF := GF) γ GD 1 a w bs[k]?)
    (Ψ := fun _ a => iprop(∃ v H, ⌜gwritesByte GD.gdG w a v⌝ ∗ histSnap (GF := GF) γ a H ∗
      ⌜H.getLast? = some (w, v)⌝)) (l := xs)).1 $$ HR with ⟨HR, Hsn⟩
  icases Hsn with #Hsn
  imodintro
  isplitr [HR]
  · iapply (AxSpinProt.bigSepSUnionSingleton hn).2
    isplitl []
    · unfold Φx
      iintro %a %v %_ %hw
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 (honly a v hw)
      ihave H2 := BigSepL.bigSepL_lookup
        (Φ := fun (_ : Nat) (a : Int) => iprop(∃ v H, ⌜gwritesByte GD.gdG w a v⌝ ∗
          histSnap (GF := GF) γ a H ∗ ⌜H.getLast? = some (w, v)⌝)) hk $$ Hsn
      icases H2 with ⟨%v', %H, %hv', Hs, %hl⟩
      obtain rfl := gwritesByteDet _ _ _ _ _ hw hv'
      iexists H
      isplitl []
      · iexact Hs
      · ipureintro
        exact hl
    · iexact Hinv
  · iexact HR

end rbf

/-! # 3. THE INSTANCE `spinOb6`: lock word + owned WORD `xs` + lk->cpu `Cl` -/

def X6 (xs Cl : List Int) : GSet Int := LawfulSet.ofList xs ∪ LawfulSet.ofList Cl

section inst6
variable {GF : BundledGFunctors} [AxlogG GF Hent] [SpinlockG GF]

def spinOb6 (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (nm : spinN)
    (GD : Gdexec) (_ : Unit) (s : GSet Geid) : IProp GF :=
  iprop(⌜WC GD.gdG s ∧ CPUOK Cl cv GD.gdG s⌝ ∗ ownInv (X6 xs Cl) nm.1 GD s ∗ lkInv nm.2 lk GD s)

def spinR6 (xs Cl : List Int) (nm : spinN) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(RL nm.1 GD xs e ∗ RL nm.1 GD Cl e)

def spinInit6 (lk : Int) (xs Cl : List Int) (GD : Gdexec) (nm : spinN) (i : Agent) : IProp GF :=
  iprop(isLock nm.2 lk (spinR6 xs Cl nm GD) ∗ notheld nm.2 lk i)

theorem spinR6Transportable (xs Cl : List Int) (nm : spinN) (GD : Gdexec) :
    rvwmoCatConsistent GD → lkTransportable GD (spinR6 (GF := GF) xs Cl nm GD) := by
  intro Hcons e e' Hob
  unfold spinR6
  iintro ⟨H1, H2⟩
  isplitl [H1]
  · iapply (RLTransportable nm.1 GD xs Hcons e e' Hob) $$ H1
  · iapply (RLTransportable nm.1 GD Cl Hcons e e' Hob) $$ H2

/-- GENESIS: all histories empty, `R6` parked in σ0's genesis box. -/
theorem spinHobAlloc6 (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8))
    (GD : Gdexec) (harts : List Agent) :
    harts.Nodup → xs.Nodup → Cl.Nodup → (∀ a, a ∈ xs → a ∉ Cl) →
    ⊢ iprop(|==> ∃ (nm : spinN) (σ0 : Unit), spinOb6 (GF := GF) lk xs Cl cv nm GD σ0 ∅ ∗
      [∗list] i ∈ harts, spinInit6 lk xs Cl GD nm i) := by
  intro Hnd Hndx HndC Hdisj
  have Hd : (LawfulSet.ofList xs : GSet Int) ## LawfulSet.ofList Cl :=
    elemOfDisjoint.2 fun a ha hb =>
      Hdisj a (LawfulSet.mem_ofList.2 ha) (LawfulSet.mem_ofList.2 hb)
  imod histAlloc (GF := GF) (X6 xs Cl) ([] : List Hent) with ⟨%γx, H⟩
  unfold X6
  icases (BigSepS.bigSepS_union Hd).1 $$ H with ⟨Hx, HC⟩
  ihave Hx := (BigSepS.bigSepS_of_list Hndx).1 $$ Hx
  ihave HC := (BigSepS.bigSepS_of_list HndC).1 $$ HC
  ihave HRx := RLGenesis γx GD xs $$ Hx
  ihave HRC := RLGenesis γx GD Cl $$ HC
  imod (lkInvAlloc lk GD harts (fun e => iprop(RL γx GD xs e ∗ RL γx GD Cl e)) Hnd)
    $$ [HRx HRC] with ⟨%reg, Hinv, #Hil, Hnh⟩
  · iintro %e
    isplitl [HRx]
    · iapply HRx
    · iapply HRC
  imodintro
  iexists ((γx, reg) : spinN), ()
  isplitl [Hinv]
  · unfold spinOb6
    isplitr
    · ipureintro
      exact ⟨fun e w He => absurd He notElemOfEmpty, fun w Hw => absurd Hw notElemOfEmpty⟩
    isplitr [Hinv]
    · unfold ownInv
      iapply BigSepS.bigSepS_empty.2
      iempintro
    · iexact Hinv
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ i => notheld (GF := GF) reg lk i)
      (Ψ := fun _ i => spinInit6 (GF := GF) lk xs Cl GD (γx, reg) i)) $$ Hnh
    imodintro
    iintro %k %i %_ Hi
    unfold spinInit6 spinR6
    isplitl []
    · iexact Hil
    · iexact Hi

end inst6

/-- Rocq `#[local] Instance s6_G` (a named reducible def). -/
@[reducible] def s6G {GF : BundledGFunctors.{0,0,0}} [AxannotGS GF] [AxlogG GF Hent]
    [SpinlockG GF] (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) : AxirisG GF :=
  shG (gtAdGd GT) spinN Unit (spinOb6 lk xs Cl cv) nm

section rules6
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxlogG GF Hent] [SpinlockG GF]

/-- THE BUILDER: re-establishes `WC` and `CPUOK`, demanding Φ_cpu of the event. -/
theorem fe6Build (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (e : Geid) (flowIn : Mea GF) (R : IProp GF) :
    ⊢ (∀ s : GSet Geid, ⌜e ∉ s⌝ -∗ ⌜WC (gtAdGd GT).gdG s⌝ -∗ ⌜WPh (gtAdGd GT).gdG s e⌝ -∗
        ⌜spSpol GT (gtAdGd GT) e ⊆ s⌝ -∗ ⌜CPUOK Cl cv (gtAdGd GT).gdG s⌝ -∗
        ownInv (X6 xs Cl) nm.1 (gtAdGd GT) s -∗ lkInv nm.2 lk (gtAdGd GT) s -∗
        ([∗map] Rin ∈ flowIn, Rin) ==∗
        ▷ |==> (⌜cpuOk Cl cv (gtAdGd GT).gdG e⌝ ∗
          ownInv (X6 xs Cl) nm.1 (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗
          lkInv nm.2 lk (gtAdGd GT) (({e} : GSet Geid) ∪ s) ∗ R)) -∗
      @flowEqDyn hlc GF _ (s6G lk xs Cl cv GT nm) (gtAdGd GT) e
        (@Axpol.sPol (splPol GT) (gtAdGd GT) e) flowIn R := by
  iintro H
  unfold flowEqDyn
  iintro %σ %s %Hsub %Hnin Hob Hfi
  have Hwp := spolWP GT (gtAdGd GT) e s Hsub
  ihave Hob := (show @AxirisG.obStInterp GF (s6G lk xs Cl cv GT nm) (gtAdGd GT) σ s ⊢
    spinOb6 lk xs Cl cv nm (gtAdGd GT) σ s from .rfl) $$ Hob
  unfold spinOb6
  icases Hob with ⟨%Hp, Ho, Hl⟩
  obtain ⟨Hwc, Hok⟩ := Hp
  imod H $$ %s %Hnin %Hwc %Hwp %Hsub %Hok Ho Hl Hfi with H
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imod H with ⟨%He, Ho, Hl, HR⟩
  imodintro
  iexists σ
  isplitl [Ho Hl]
  · iapply (show spinOb6 lk xs Cl cv nm (gtAdGd GT) σ (({e} : GSet Geid) ∪ s) ⊢
      @AxirisG.obStInterp GF (s6G lk xs Cl cv GT nm) (gtAdGd GT) σ (({e} : GSet Geid) ∪ s)
      from .rfl)
    unfold spinOb6
    isplitr
    · ipureintro
      exact ⟨WCInsert _ s e Hwc Hwp, CPUOKInsert Cl cv _ s e Hok He⟩
    isplitl [Ho]
    · iexact Ho
    · iexact Hl
  · iexact HR

theorem lkw6NX (lk : Int) (xs Cl : List Int) (GT : GdexecT) (HlkX : lk ∉ X6 xs Cl) (e : Geid) :
    (∀ a v, gwritesByte (gtAdGd GT).gdG e a v → a = lk) →
    ∀ a v, a ∈ X6 xs Cl → ¬ gwritesByte (gtAdGd GT).gdG e a v := by
  intro Hsg a v Ha Hw
  rw [Hsg a v Hw] at Ha
  exact HlkX Ha

theorem lkw6Cpu (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (HlkX : lk ∉ X6 xs Cl) (e : Geid) :
    (∀ a v, gwritesByte (gtAdGd GT).gdG e a v → a = lk) → cpuOk Cl cv (gtAdGd GT).gdG e := by
  intro Hsg
  apply cpuOkNw
  intro a v Ha Hw
  apply HlkX
  rw [← Hsg a v Hw]
  exact elemOfUnionR (LawfulSet.mem_ofList.1 Ha)

theorem nw6NX (xs Cl : List Int) (GT : GdexecT) (e : Geid) :
    gisW (gtAdGd GT).gdG e = false → ∀ a v, a ∈ X6 xs Cl → ¬ gwritesByte (gtAdGd GT).gdG e a v :=
  fun Hnw a v _ => AxSpinProt6.nwb _ e Hnw a v

theorem nw6Cpu (Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT) (e : Geid) :
    gisW (gtAdGd GT).gdG e = false → cpuOk Cl cv (gtAdGd GT).gdG e :=
  fun Hnw => cpuOkNw Cl cv _ e (fun a v _ => AxSpinProt6.nwb _ e Hnw a v)

/-- ACQUIRE-SUCCESS, `notheld` in hand. -/
theorem fe6Claim (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X6 xs Cl) (c : Geid)
    (oz : Option Geid) :
    lkClaim lk (gtAdGd GT).gdG c oz → (∀ a v', gwritesByte (gtAdGd GT).gdG c a v' → a = lk) →
    ⊢ notheld nm.2 lk c.1 -∗ isLock nm.2 lk (spinR6 xs Cl nm (gtAdGd GT)) -∗
      @flowEqDyn hlc GF _ (s6G lk xs Cl cv GT nm) (gtAdGd GT) c
        (@Axpol.sPol (splPol GT) (gtAdGd GT) c) (∅ : Mea GF)
        iprop(locked nm.2 lk c.1 c ∗ spinR6 xs Cl nm (gtAdGd GT) c) := by
  intro Hcl Hsg
  iintro Hnh #Hil
  iapply fe6Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl _
  imod (lkInvClaim nm.2 lk (gtAdGd GT) s c oz (spinR6 xs Cl nm (gtAdGd GT)) Hcons Hwc Hwp Hn Hcl
    (spinR6Transportable xs Cl nm (gtAdGd GT) Hcons)) $$ [$Hl $Hnh $Hil] with H
  imodintro
  inext
  icases H with ⟨Hl, Hlk, HR⟩
  imodintro
  isplitr
  · ipureintro
    exact lkw6Cpu lk xs Cl cv GT HlkX c Hsg
  isplitl [Ho]
  · iapply (ownInvOther (X6 xs Cl) nm.1 (gtAdGd GT) s c Hn (lkw6NX lk xs Cl GT HlkX c Hsg)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  isplitl [Hlk]
  · iexact Hlk
  · iexact HR

/-- RELEASE, each component of `R` from `flowIn` at its own anchor. -/
theorem fe6Release' (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X6 xs Cl) (w : Geid)
    (i : Nat) (c : Geid) (R : Geid → IProp GF) (Rs : List (Geid → IProp GF)) (flowIn : Mea GF) :
    zw lk (gtAdGd GT).gdG w → (∀ t v, ¬ greadsByte (gtAdGd GT).gdG w lk t v) →
    (∀ a v', gwritesByte (gtAdGd GT).gdG w a v' → a = lk) →
    (∀ Rj, Rj ∈ Rs → lkTransportable (gtAdGd GT) Rj) → (([∗list] Rj ∈ Rs, Rj w) ⊢ R w) →
    ⊢ isLock nm.2 lk R -∗
      (([∗map] Rin ∈ flowIn, Rin) -∗
        locked nm.2 lk i c ∗ [∗list] Rj ∈ Rs, ∃ a, ⌜gobCat (gtAdGd GT) a w⌝ ∗ Rj a) -∗
      @flowEqDyn hlc GF _ (s6G lk xs Cl cv GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn iprop(notheld nm.2 lk i) := by
  intro Hzw Hnr Hsg Htr HRs
  iintro #Hil Hfi
  iapply fe6Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl Hin
  ihave ⟨Hlk, HRc⟩ := Hfi $$ Hin
  ihave HRc := (transportComps (gtAdGd GT) Rs w Htr) $$ HRc
  ihave HR := HRs $$ HRc
  ihave H := (lkInvRelease nm.2 lk (gtAdGd GT) s w i c R Hcons Hwc Hn Hzw Hnr)
    $$ [$Hl $Hlk $Hil $HR]
  imodintro
  inext
  imod H with ⟨Hl, Hnh, -⟩
  imodintro
  isplitr
  · ipureintro
    exact lkw6Cpu lk xs Cl cv GT HlkX w Hsg
  isplitl [Ho]
  · iapply (ownInvOther (X6 xs Cl) nm.1 (gtAdGd GT) s w Hn (lkw6NX lk xs Cl GT HlkX w Hsg)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  · iexact Hnh

/-- The HOLDER's plain read of the lock byte (`locked` via `flowIn`). -/
theorem fe6LkreadHeld (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8))
    (GT : GdexecT) (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (_HlkX : lk ∉ X6 xs Cl)
    (r : Geid) (i : Nat) (c : Geid) (Q : IProp GF) (flowIn : Mea GF) :
    gisW (gtAdGd GT).gdG r = false → WeakRvwmoGraph.gpo (gtAdGd GT).gdG c r →
    nolk lk (gtAdGd GT).gdG c r →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ locked nm.2 lk i c ∗ Q) -∗
      @flowEqDyn hlc GF _ (s6G lk xs Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) flowIn
        iprop((locked nm.2 lk i c ∗ Q) ∗
          ⌜∀ t v, greadsByte (gtAdGd GT).gdG r lk t v → v ≠ b0⌝) := by
  intro Hnw Hpo Hnl
  iintro Hfi
  iapply fe6Build
  iintro %s %Hn %Hwc %Hwp %_ %_ Ho Hl Hin
  ihave ⟨Hlk, HQ⟩ := Hfi $$ Hin
  icases (lkInvReadHeld nm.2 lk (gtAdGd GT) s r i c Hcons Hwp Hn Hnw Hpo Hnl) $$ [$Hl $Hlk]
    with ⟨Hl, Hlk, %Hf⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact nw6Cpu Cl cv GT r Hnw
  isplitl [Ho]
  · iapply (ownInvOther (X6 xs Cl) nm.1 (gtAdGd GT) s r Hn (nw6NX xs Cl GT r Hnw)) $$ Ho
  isplitl [Hl]
  · iexact Hl
  · isplitl [Hlk HQ]
    · isplitl [Hlk]
      · iexact Hlk
      · iexact HQ
    · ipureintro
      exact Hf

/-- A word load `r` of `[a, a+n)` (`n = vs.length`) touching only owned bytes is not a lock-word
read and writes nothing. -/
theorem ldNFacts (lk : Int) (xs Cl : List Int) (GT : GdexecT) (HlkX : lk ∉ X6 xs Cl) (r : Geid)
    (a : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG r = some (.LLoad false a ts vs) → ts.length = vs.length →
    (∀ b, b ∈ clRange a vs.length → b ∈ X6 xs Cl) →
    gisW (gtAdGd GT).gdG r = false ∧ ¬ lkread lk (gtAdGd GT).gdG r := by
  intro Hl Hlen HX
  have Hnw : gisW (gtAdGd GT).gdG r = false := by unfold gisW; rw [Hl]; rfl
  refine ⟨Hnw, ?_⟩
  rintro ⟨⟨t, v, Hrd⟩, -⟩
  exact HlkX (HX lk ((loadNBytes _ r a ts vs Hl Hlen).2 lk t v Hrd))

/-- THE OWNED WORD READ (fraction `q`). -/
theorem fe6RdN (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X6 xs Cl) (r e : Geid)
    (q : Qp) (a : Int) (ts : List Nat) (vs mv : List (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG r = some (.LLoad false a ts vs) → ts.length = vs.length →
    (∀ b, b ∈ clRange a vs.length → b ∈ X6 xs Cl) → gmoLt (gtAdGd GT).gdG e r →
    (∀ b w v', b ∈ clRange a vs.length → gwritesByte (gtAdGd GT).gdG w b v' →
      WeakRvwmoGraph.gpo (gtAdGd GT).gdG w r → gmoLt (gtAdGd GT).gdG w r) →
    ⊢ @flowEqDyn hlc GF _ (s6G lk xs Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r)
        ({[e := RbN nm.1 (gtAdGd GT) q (clRange a vs.length) e mv]} : Mea GF)
        iprop(RbN nm.1 (gtAdGd GT) q (clRange a vs.length) r vs ∗
          ⌜∀ (k : Nat) v0 v, mv[k]? = some v0 → vs[k]? = some v → v = v0⌝) := by
  intro Hl Hlen HX Her Hfw
  obtain ⟨Hnw, Hnr⟩ := ldNFacts lk xs Cl GT HlkX r a ts vs Hl Hlen HX
  iapply fe6Build
  iintro %s %Hn %_ %Hwp %_ %_ #Ho Hl Hin
  ihave Hin := (BigSepM.bigSepM_singleton (M := GMapF Geid)).1 $$ Hin
  ihave ⟨HR, %Hf⟩ := (RbNRead nm.1 (gtAdGd GT) (X6 xs Cl) q (clRange a vs.length) s e r ts vs
    mv Hcons HX (loadNBytes _ r a ts vs Hl Hlen).1 Her Hwp Hfw) $$ [$Ho $Hin]
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact nw6Cpu Cl cv GT r Hnw
  isplitl []
  · iapply (ownInvOther (X6 xs Cl) nm.1 (gtAdGd GT) s r Hn (nw6NX xs Cl GT r Hnw)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn
      (fun v' => AxSpinProt6.nwb _ r Hnw lk v') Hnr) $$ Hl
  · isplitl [HR]
    · iexact HR
    · ipureintro
      intro k v0 v E0 Ev
      have Hk : k < vs.length := (List.getElem?_eq_some_iff.1 Ev).1
      exact Hf k (a + (k : Int)) v0 v
        ((AxSpinH4.clRangeLookup a vs.length k _).2 ⟨Hk, rfl⟩) E0 Ev

/-- A PLAIN word read drawing nothing (the forwarded reload). -/
theorem fe6PlainN (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X6 xs Cl) (r : Geid)
    (a : Int) (ts : List Nat) (vs : List (BitVec 8)) :
    gxLbl (gtAdGd GT).gdG r = some (.LLoad false a ts vs) → ts.length = vs.length →
    (∀ b, b ∈ clRange a vs.length → b ∈ X6 xs Cl) →
    ⊢ @flowEqDyn hlc GF _ (s6G lk xs Cl cv GT nm) (gtAdGd GT) r
        (@Axpol.sPol (splPol GT) (gtAdGd GT) r) (∅ : Mea GF) iprop(True) := by
  intro Hl Hlen HX
  obtain ⟨Hnw, Hnr⟩ := ldNFacts lk xs Cl GT HlkX r a ts vs Hl Hlen HX
  iapply fe6Build
  iintro %s %Hn %_ %_ %_ %_ #Ho Hl _
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact nw6Cpu Cl cv GT r Hnw
  isplitl []
  · iapply (ownInvOther (X6 xs Cl) nm.1 (gtAdGd GT) s r Hn (nw6NX xs Cl GT r Hnw)) $$ Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s r Hn
      (fun v' => AxSpinProt6.nwb _ r Hnw lk v') Hnr) $$ Hl
  · itrivial

/-- THE OWNED WORD WRITE: the old FULL handle is produced by any wand from `flowIn` (one handle,
or two recombined fractions), `Q` framed; the written bytes must be owned and outside lk->cpu
(Φ_cpu holds trivially). -/
theorem fe6WrN (lk : Int) (xs Cl : List Int) (cv : Agent → List (BitVec 8)) (GT : GdexecT)
    (nm : spinN) (_Hcons : rvwmoCatConsistent (gtAdGd GT)) (HlkX : lk ∉ X6 xs Cl) (w e : Geid)
    (a : Int) (bs mv : List (BitVec 8)) (cls : WmClass) (Q : IProp GF) (flowIn : Mea GF) :
    gxLbl (gtAdGd GT).gdG w = some (.LStore false a bs cls) →
    (∀ b, b ∈ clRange a bs.length → b ∈ X6 xs Cl ∧ b ∉ Cl) → gmoLt (gtAdGd GT).gdG e w →
    ⊢ (([∗map] Rin ∈ flowIn, Rin) -∗ Q ∗ RbN nm.1 (gtAdGd GT) 1 (clRange a bs.length) e mv) -∗
      @flowEqDyn hlc GF _ (s6G lk xs Cl cv GT nm) (gtAdGd GT) w
        (@Axpol.sPol (splPol GT) (gtAdGd GT) w) flowIn
        iprop(Q ∗ RbN nm.1 (gtAdGd GT) 1 (clRange a bs.length) w bs) := by
  intro Hl HX Hew
  obtain ⟨Hall, Honly⟩ := storeNBytes _ w a bs cls Hl
  iintro Hfi
  iapply fe6Build
  iintro %s %Hn %_ %_ %_ %_ Ho Hl Hin
  ihave ⟨HQ, HR⟩ := Hfi $$ Hin
  imod (RbNWrite nm.1 (gtAdGd GT) (X6 xs Cl) (clRange a bs.length) s e w mv bs Hn Hew Hall
    Honly) $$ [$Ho $HR] with ⟨Ho, HR⟩
  imodintro
  inext
  imodintro
  isplitr
  · ipureintro
    exact cpuOkNw Cl cv _ w (fun b v HbC Hw => (HX b (Honly b v Hw)).2 HbC)
  isplitl [Ho]
  · iexact Ho
  isplitl [Hl]
  · iapply (lkInvOther nm.2 lk (gtAdGd GT) s w Hn
      (fun v Hv => HlkX (HX lk (Honly lk v Hv)).1)
      (fun ⟨_, Hnw⟩ => by simp [gisW, Hl, lbIsW] at Hnw)) $$ Hl
  · isplitl [HQ]
    · iexact HQ
    · iexact HR

end rules6

end Weak
