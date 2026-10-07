/-
Weak: **Phase 1c, part 1 of the spinlock plan -- THE JOINT INSTANCE `protXv6` (Ixv6).**
(Files: this one (layout, the real lk->cpu value table `cvx`, the last-value owned bytes
`Rv`/`RVL`, the instance, `RPid`, `xv6Init`, `xv6HobAlloc`, the policy and its `Hok`);
`AxSpinX2` (rule lemmas as flow equations); `AxSpinX3` (n-byte hand nodes); `AxSpinX4`
(certificate layout, hand programs); `AxSpinX5`/`AxSpinX6` (WPds); `AxSpinX8` (certificate
graphs); `AxSpinX7` (capstone).)

Rocq: `iris/AxSpinX.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE INSTANCE (parametrised ONLY by the layout `L : Xlay`):
  `protXv6 L nm GD σ s := ⌜WC ∧ CPUOK (clb L) cvx ∧ WOK L⌝ ∗ ownInv (XO L) ∗ lkInv lk`.
CLASSES (by address): the LOCK WORD `lwb L` = lk..lk+3 (the Phase-1a lock component, keyed on
the low byte; upper bytes written only by lock arms, never owned); lk->cpu `clb L` =
lk+16..lk+23 (OWNED bytes whose auths travel inside the lock's `R`, with Φ_cpu for the REAL
value table `cvx i` = the bytes of `&cpus[cpuOf i]`); nextpid `npb L` (OWNED bytes inside
`RPid`, exact value via the `RVL` last-value handle, plus Theorem 2's ghosts ●mono and the
issued set); PRIVATE stack / struct-cpu bytes of each hart (σ's WOK writer = owner arm, no
history ghost -- FINDING 1); READ-ONLY bytes (not writable by anyone); BLOCKED (everything
else: no write admissible).  `RPid` = `(∃ vs, RVL (clb L) e vs) ∗ ∃ v, ⌜0 ≤ v < 2³²⌝ ∗
RVL (npb L) e (bytes of v) ∗ ●mono v ∗ issuedAuth S ∗ ⌜S ⊆ [0,v)⌝`.  `xv6Init nm i` =
kernelText ∗ cpuOwn i ∗ stackOwn i ∗ isLock pid_lock RPid ∗ notheld i (the first three are PURE
layout facts).  POLICY: `AxSpinProt2.splPol GT`; `xv6Hok` = `splHok`.  `xv6HobAlloc` allocates
from the LAYOUT (`xlayOk`) and IMAGE (lk->cpu = 0, nextpid = n0 < 2³²) premises.
FINDINGS 1-4 and the extension points: see the Rocq header (unchanged by the port).

## Deviations from Rocq

1. VOCABULARY (as `AxSpinProt5`/`AxSpinProt6` deviation 1): `Z` ↦ `Int`, `agent` ↦ `Agent`
   (= `Nat`), `bv 8` ↦ `BitVec 8`, `gset` ↦ `GSet`, `list_to_set` ↦ `LawfulSet.ofList`,
   `gd_g GD` ↦ `GD.gdG`, `gx_img G a` ↦ `G.gxImg a`, `l !! j` ↦ `l[j]?`, `last l` ↦
   `l.getLast?`, `H.*1` ↦ `H.map Prod.fst`, `B0` ↦ `b0`, `NoDup` ↦ `List.Nodup`,
   `wbytes n (Z_to_bv 32 v)` ↦ `WeakInterpProj.wbytes n (BitVec.ofInt 32 v)`,
   `0 ≤ v < 2^32` ↦ `0 ≤ v ∧ v < 2 ^ 32`; record fields `xl_lk` … ↦ `Xlay.xlLk` …, `xn_h` … ↦
   `Xv6N.xnH` ….
2. THE lk->cpu VALUE TABLE: Rocq `cpus_ptr i = mycpu_ret (cid_word_of i)` (ProcGeom; the
   `mycpu` code form, equal to `KernelSyms.cpus + 128 * i` by `mycpu_ret_unsigned`) ↦ Lean
   `MachCSL.cpuAddr i` at `Xv6.Geom`'s `KernelGeom` instance (`cpusBase = KA.cpus`, the same
   address); `cvxNz` uses `cpuAddr_ne_zero`, `cvxInj` uses `cpuAddr_inj` (Rocq
   `mycpu_ret_unsigned`/`cpus_ptr_inj`).  `cpu_of` uses `if h : i < NCPU` (Rocq `lt_dec`).
3. GHOST CLASS: Rocq `xv6G Σ` ↦ `AxSpinX.Xv6G GF` (file-qualified: `Xv6.Xv6G` exists) with
   instance fields `AxlogG GF Hent`, `SpinlockG GF`, `MonoNatG GF` and the issued-set camera
   `ElemG GF (constOF (Auth (DisjointLeibnizSet (GSet Int))))` (Rocq `authR (gset_disjUR Z)`).
   Adequacy files using `protXv6`/`RPid` take `[AxSpinX.Xv6G GF]` and must ALLOCATE it.
   `mono_nat_auth_own γ 1 n` ↦ `MonoNat.auth_own γ (DFrac.own 1) (.ofNat n)`.
4. CONTEXTS: Rocq section variables are explicit leading arguments in Rocq's order, only where
   Rocq's section mechanism includes them (§1 `L [HL]`; §3 `γ GD`; §4 `L`).  `hwfx` takes only
   `GD` (it does not mention `γ`).
5. STATEMENT SHAPES (as `AxSpinProt5` deviation 3): `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`,
   `P -∗ Q ==∗ R` ↦ `P ∗ Q ⊢ |==> R`; pure premises stay `→`.
6. `kernel_text`/`cpu_own`/`stack_own` are file-qualified `AxSpinX.kernelText`/`cpuOwn`/
   `stackOwn` (MachCSL/Xv6 have unrelated `kernelText`/`cpuOwn`/`stackOwn`, and Weak files
   `open MachCSL`).
7. The trailing `Print Assumptions` commands are not ported.

**Rocq → Lean name map.**  `xlay` `Xlay` (fields `xlLk xlNp xlHarts xlStk xlCpuf xlRo xlText`),
`lwb` `lwb`, `clb` `clb`, `npb` `npb`, `XO` `XO`, `priv` `priv`, `wok` `wok`, `xlay_ok`
`xlayOk`, `lk_in_lwb` `lkInLwb`, `lwb_notin_XO` `lwbNotinXO`, `lk_notin_XO` `lkNotinXO`,
`NoDup_clb` `NoDupClb`, `NoDup_npb` `NoDupNpb`, `clb_npb_disj` `clbNpbDisj`, `clb_XO` `clbXO`,
`npb_XO` `npbXO`, `lk_notin_clb` `lkNotinClb`, `ncpu_pos` `ncpuPos`, `cpu_of` `cpuOf`,
`cpu_of_nat` `cpuOfNat`, `cvx` `cvx`, `cvx_length` `cvxLength`, `wbytes8_inj` `wbytes8Inj`,
`cvx_nz` `cvxNz`, `cvx_inj` `cvxInj`, `WOK` `WOK`, `WOK_insert` `WOKInsert`, `hwfx` `hwfx`,
`Rv` `Rv`, `RVL` `RVL`, `hwfx_nil` `hwfxNil`, `Rv_transport` `RvTransport`, `RVL_transport`
`RVLTransport`, `RVL_genesis` `RVLGenesis`, `Rv_step` `RvStep`, `RVL_write` `RVLWrite`,
`Rv_read` `RvRead`, `RVL_read` `RVLRead`, `RVL_any` `RVLAny`, `xv6G` `AxSpinX.Xv6G` (fields
`xv6LogG xv6LockG xv6MonoG xv6IssG`), `xv6_N` `Xv6N` (fields `xnH xnReg xnM xnI`),
`issued_auth` `issuedAuth`, `issued_frag` `issuedFrag`, `prot_xv6` `protXv6`, `R_np` `RNp`,
`R_cpu` `RCpu`, `R_pid` `RPid`, `R_cpu_transportable` `RCpuTransportable`,
`R_np_transportable` `RNpTransportable`, `R_pid_transportable` `RPidTransportable`,
`kernel_text` `AxSpinX.kernelText`, `cpu_own` `AxSpinX.cpuOwn`, `stack_own`
`AxSpinX.stackOwn`, `xv6_init` `xv6Init`, `xv6_Hob_alloc` `xv6HobAlloc`, `xv6_pol` `xv6Pol`,
`xv6_axpol_wf` `xv6AxpolWf`, `xv6_Hok` `xv6Hok`.
Lean-only (file-qualified): `AxSpinX.rvlSnaps` (`RVL_write`'s inner `big_sepL_bupd` step, by
list induction), `AxSpinX.histInOfCov` (`Rv_read`'s inner `iAssert`: every covered write is in
the auth's history).

**Dropped:** none (58 Rocq decls; 60 Lean = 58 + 2 Lean-only).
-/
import Weak.AxSpinProt6
import MachCSL.Lock
import Xv6.Geom
import Iris.BI.Lib.MonoNat

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE LAYOUT (the only parameters of the instance) -/

structure Xlay where
  /-- `&pid_lock` (lock word; lk->cpu at +16) -/
  xlLk : Int
  /-- `&nextpid` -/
  xlNp : Int
  /-- the harts -/
  xlHarts : List Agent
  /-- hart i's stack bytes -/
  xlStk : Agent → GSet Int
  /-- hart i's struct-cpu field bytes (noff, intena) -/
  xlCpuf : Agent → GSet Int
  /-- read-only bytes: kernel text, PTE pages -/
  xlRo : Int → Prop
  /-- the fetch region (`ax_text`); ⊆ ro in xv6 -/
  xlText : Int → Prop

def lwb (L : Xlay) : List Int := clRange L.xlLk 4
def clb (L : Xlay) : List Int := clRange (L.xlLk + 16) 8
def npb (L : Xlay) : List Int := clRange L.xlNp 4
def XO (L : Xlay) : GSet Int := LawfulSet.ofList (clb L) ∪ LawfulSet.ofList (npb L)

/-- `a` is a PRIVATE byte of hart `j` (stack or struct-cpu field). -/
def priv (L : Xlay) (a : Int) (j : Agent) : Prop :=
  j ∈ L.xlHarts ∧ (a ∈ L.xlStk j ∨ a ∈ L.xlCpuf j)

/-- Hart `j` may write byte `a`: lock word, owned (lock-protected), or its own private bytes.
Everything else (read-only, unknown) is BLOCKED. -/
def wok (L : Xlay) (a : Int) (j : Agent) : Prop :=
  a ∈ lwb L ∨ a ∈ XO L ∨ priv L a j

/-- Hlayout (the part the instance needs). -/
def xlayOk (L : Xlay) : Prop :=
  (lwb L ++ (clb L ++ npb L)).Nodup ∧
  (∀ a j, priv L a j → a ∉ lwb L ∧ a ∉ XO L) ∧
  (∀ a j1 j2, priv L a j1 → priv L a j2 → j1 = j2) ∧
  (∀ a j, L.xlRo a → ¬ wok L a j) ∧
  L.xlHarts.Nodup ∧
  (∀ i, i ∈ L.xlHarts → i < NCPU)

section layoutFacts
variable (L : Xlay)

theorem lkInLwb : L.xlLk ∈ lwb L := by
  unfold lwb clRange
  exact List.mem_map.2 ⟨0, List.mem_range.2 (by decide), by simp⟩

theorem lwbNotinXO (HL : xlayOk L) (a : Int) : a ∈ lwb L → a ∉ XO L := by
  intro Ha Hx
  obtain ⟨-, -, Hdis⟩ := List.nodup_append.1 HL.1
  unfold XO at Hx
  rcases elemOfUnion.1 Hx with h | h
  · exact Hdis a Ha a (List.mem_append_left _ (LawfulSet.mem_ofList.2 h)) rfl
  · exact Hdis a Ha a (List.mem_append_right _ (LawfulSet.mem_ofList.2 h)) rfl

theorem lkNotinXO (HL : xlayOk L) : L.xlLk ∉ XO L := lwbNotinXO L HL _ (lkInLwb L)

theorem NoDupClb (HL : xlayOk L) : (clb L).Nodup :=
  (List.nodup_append.1 (List.nodup_append.1 HL.1).2.1).1

theorem NoDupNpb (HL : xlayOk L) : (npb L).Nodup :=
  (List.nodup_append.1 (List.nodup_append.1 HL.1).2.1).2.1

theorem clbNpbDisj (HL : xlayOk L) (a : Int) : a ∈ clb L → a ∉ npb L := fun Ha Hb =>
  (List.nodup_append.1 (List.nodup_append.1 HL.1).2.1).2.2 a Ha a Hb rfl

theorem clbXO (a : Int) : a ∈ clb L → a ∈ XO L := fun Ha =>
  elemOfUnion.2 (Or.inl (LawfulSet.mem_ofList.1 Ha))

theorem npbXO (a : Int) : a ∈ npb L → a ∈ XO L := fun Ha =>
  elemOfUnion.2 (Or.inr (LawfulSet.mem_ofList.1 Ha))

theorem lkNotinClb (HL : xlayOk L) : L.xlLk ∉ clb L := fun H =>
  lkNotinXO L HL (clbXO L _ H)

end layoutFacts

/-! # 2. The REAL lk->cpu value table: `cvx i` = the 8 little-endian bytes of `&cpus[cpuOf i]`
(Rocq `cpus_ptr (cpu_of i) = mycpu_ret (cid_word_of (cpu_of i))`; deviation 2). -/

theorem ncpuPos : 0 < NCPU := by decide

def cpuOf (i : Agent) : CPU := if h : i < NCPU then ⟨i, h⟩ else ⟨0, ncpuPos⟩

theorem cpuOfNat (i : Agent) : i < NCPU → (cpuOf i).val = i := by
  intro H
  unfold cpuOf
  rw [dif_pos H]

def cvx (i : Agent) : List (BitVec 8) := WeakInterpProj.wbytes 8 (cpuAddr (cpuOf i))

theorem cvxLength (i : Agent) : (cvx i).length = 8 := wbytesLength 8 _

theorem wbytes8Inj (a b : BitVec 64) :
    WeakInterpProj.wbytes 8 a = WeakInterpProj.wbytes 8 b → a = b := by
  intro H
  have ha := wordOfBytesWbytes 8 a
  have hb := wordOfBytesWbytes 8 b
  rw [H] at ha
  exact ha.symm.trans hb

theorem cvxNz (i : Agent) : cvx i ≠ List.replicate 8 b0 := by
  intro H
  have H0 : List.replicate 8 b0 = WeakInterpProj.wbytes 8 (0#64) := by decide
  rw [H0] at H
  exact cpuAddr_ne_zero (cpuOf i) (wbytes8Inj _ _ H)

theorem cvxInj (i j : Agent) : i < NCPU → j < NCPU → cvx i = cvx j → i = j := by
  intro Hi Hj H
  have h := cpuAddr_inj (wbytes8Inj _ _ H)
  rw [← cpuOfNat i Hi, ← cpuOfNat j Hj, h]

/-! # 3. σ's pure conjunct WOK, and the LAST-VALUE owned bytes `Rv`/`RVL` (the exact-value
handle: genesis arm = the image, else the history's last value, tied at `e`) -/

/-- WOK: every processed write writes only bytes its writer may write. -/
def WOK (L : Xlay) (G : Gexec) (s : GSet Geid) : Prop :=
  ∀ e a v, e ∈ s → gwritesByte G e a v → wok L a e.1

theorem WOKInsert (L : Xlay) (G : Gexec) (s : GSet Geid) (e : Geid) :
    WOK L G s → (∀ a v, gwritesByte G e a v → wok L a e.1) →
    WOK L G (({e} : GSet Geid) ∪ s) := by
  intro H He e' a v Hin Hw
  rcases elemOfUnion.1 Hin with h | h
  · rw [elemOfSingleton.1 h] at Hw ⊢
    exact He a v Hw
  · exact H e' a v h Hw

def hwfx (GD : Gdexec) (a : Int) (H : List Hent) : Prop :=
  (∀ p, p ∈ H → gwritesByte GD.gdG p.1 a p.2) ∧ chainWith (gmoLt GD.gdG) (H.map Prod.fst)

theorem hwfxNil (GD : Gdexec) (a : Int) : hwfx GD a [] :=
  ⟨fun _ hp => absurd hp List.not_mem_nil, fun _ _ _ hk => by simp at hk⟩

section rv
variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- One owned byte with its CURRENT value `vl`: the full history auth; either still the genesis
(image = `vl`) or the last entry has value `vl`, the history tied at `e`. -/
def Rv (γ : GName) (GD : Gdexec) (a : Int) (e : Geid) (vl : BitVec 8) : IProp GF :=
  iprop(∃ H, histAuth γ a 1 H ∗
    ⌜hwfx GD a H ∧ ((H = [] ∧ GD.gdG.gxImg a = some vl) ∨
      ((∃ wl, H.getLast? = some (wl, vl)) ∧ tieBase GD.gdG (H.map Prod.fst) e))⌝)

/-- A list of them (`Cl` bytes, values `vs` index-wise). -/
def RVL (γ : GName) (GD : Gdexec) (Cl : List Int) (e : Geid) (vs : List (BitVec 8)) :
    IProp GF :=
  iprop(⌜vs.length = Cl.length⌝ ∗
    [∗list] j ↦ a ∈ Cl, ∃ v, ⌜vs[j]? = some v⌝ ∗ Rv γ GD a e v)

theorem RvTransport (γ : GName) (GD : Gdexec) (a : Int) (e e' : Geid) (vl : BitVec 8) :
    rvwmoCatConsistent GD → gobCat GD e e' → Rv (GF := GF) γ GD a e vl ⊢ Rv γ GD a e' vl := by
  intro hcons hob
  unfold Rv
  iintro ⟨%H, Ha, %hp⟩
  obtain ⟨hw, hc⟩ := hp
  iexists H
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    refine ⟨hw, ?_⟩
    rcases hc with h | ⟨hl, ht⟩
    · exact Or.inl h
    · exact Or.inr ⟨hl, tieLob _ _ e e' ht (obCatSubGmo GD e e' hcons hob)⟩

theorem RVLTransport (γ : GName) (GD : Gdexec) (Cl : List Int) (e e' : Geid)
    (vs : List (BitVec 8)) :
    rvwmoCatConsistent GD → gobCat GD e e' →
    RVL (GF := GF) γ GD Cl e vs ⊢ RVL γ GD Cl e' vs := by
  intro hcons hob
  unfold RVL
  iintro ⟨%hlen, H⟩
  isplitr
  · ipureintro
    exact hlen
  · iapply (BigSepL.bigSepL_mono_of_forall fun {k a} => ?_) $$ H
    iintro ⟨%v, %hv, Ha⟩
    iexists v
    isplitr
    · ipureintro
      exact hv
    · iapply (RvTransport γ GD a e e' v hcons hob) $$ Ha

theorem RVLGenesis (γ : GName) (GD : Gdexec) (Cl : List Int) (vs : List (BitVec 8)) :
    vs.length = Cl.length →
    (∀ (j : Nat) a v, Cl[j]? = some a → vs[j]? = some v → GD.gdG.gxImg a = some v) →
    ([∗list] a ∈ Cl, histAuth (GF := GF) γ a 1 []) ⊢ ∀ e, RVL γ GD Cl e vs := by
  intro hlen himg
  have h : ∀ e, ([∗list] a ∈ Cl, histAuth (GF := GF) γ a 1 []) ⊢ RVL γ GD Cl e vs := by
    intro e
    unfold RVL
    iintro H
    isplitr
    · ipureintro
      exact hlen
    · iapply (BigSepL.bigSepL_mono fun {k a} hk => ?_) $$ H
      have hkl : k < vs.length := by
        rw [hlen]
        exact (List.getElem?_eq_some_iff.1 hk).1
      have hv : vs[k]? = some vs[k] := List.getElem?_eq_getElem hkl
      unfold Rv
      iintro Ha
      iexists vs[k]
      isplitr
      · ipureintro
        exact hv
      · iexists ([] : List Hent)
        isplitl [Ha]
        · iexact Ha
        · ipureintro
          exact ⟨hwfxNil GD a, Or.inl ⟨rfl, himg k a _ hk hv⟩⟩
  iintro H %e
  iapply h e
  iexact H

theorem RvStep (γ : GName) (GD : Gdexec) (a : Int) (e w : Geid) (vold v : BitVec 8) :
    gmoLt GD.gdG e w → gwritesByte GD.gdG w a v →
    Rv (GF := GF) γ GD a e vold ⊢ |==> (Rv γ GD a w v ∗
      ∃ H, histSnap γ a H ∗ ⌜H.getLast? = some (w, v)⌝) := by
  intro hew hw
  unfold Rv
  iintro ⟨%H, Ha, %hp⟩
  obtain ⟨⟨hwr, hch⟩, hc⟩ := hp
  imod histAppend γ a H (w, v) $$ Ha with Ha
  ihave #Hsn := histSnapGet γ a 1 (H ++ [(w, v)]) $$ Ha
  imodintro
  isplitl [Ha]
  · iexists (H ++ [(w, v)])
    isplitl [Ha]
    · iexact Ha
    · ipureintro
      refine ⟨⟨?_, ?_⟩, Or.inr ⟨⟨w, by simp⟩, tieWrite GD.gdG H w v⟩⟩
      · intro p hp
        rcases List.mem_append.1 hp with h | h
        · exact hwr p h
        · simp only [List.mem_singleton] at h
          subst h
          exact hw
      · rw [List.map_append]
        refine AxSpinProt.chainWithSnoc' _ _ w hch ?_
        intro wl hl
        rcases hc with ⟨rfl, -⟩ | ⟨-, ht | ⟨wl', ht, hlt⟩⟩
        · simp at hl
        · rw [ht] at hl
          cases hl
          exact hew
        · rw [ht] at hl
          cases hl
          exact gmoLtTrans _ _ _ _ hlt hew
  · iexists (H ++ [(w, v)])
    isplitl []
    · iexact Hsn
    · ipureintro
      simp

/-- (Lean-only) `RVL_write`'s inner step: every byte of `Cl` steps to `w` with its new value,
with one deposit snapshot per written byte. -/
theorem AxSpinX.rvlSnaps (γ : GName) (GD : Gdexec) (Cl : List Int) (vs : List (BitVec 8))
    (e w : Geid) :
    gmoLt GD.gdG e w → vs.length = Cl.length →
    (∀ (j : Nat) a v, Cl[j]? = some a → vs[j]? = some v → gwritesByte GD.gdG w a v) →
    ([∗list] a ∈ Cl, ∃ vo, Rv (GF := GF) γ GD a e vo) ⊢
      |==> (([∗list] j ↦ a ∈ Cl, ∃ v, ⌜vs[j]? = some v⌝ ∗ Rv γ GD a w v) ∗
        ∀ a v, ⌜a ∈ Cl⌝ → ⌜gwritesByte GD.gdG w a v⌝ →
          ∃ H, histSnap γ a H ∗ ⌜H.getLast? = some (w, v)⌝) := by
  induction Cl generalizing vs with
  | nil =>
    intro _ _ _
    iintro -
    imodintro
    isplitl []
    · iapply BigSepL.bigSepL_nil.2
      iempintro
    · iintro %a %v %ha
      simp at ha
  | cons a Cl ih =>
    intro hew hlen hall
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hv : gwritesByte GD.gdG w a v := hall 0 a v rfl rfl
      iintro H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%vo, Ha⟩, HL⟩
      imod RvStep γ GD a e w vo v hew hv $$ Ha with ⟨Ha, %H, #Hs, %hl⟩
      imod ih vs hew (by simpa using hlen) (fun j a' v' h1 h2 => hall (j + 1) a' v' h1 h2)
        $$ HL with ⟨HL, #HS⟩
      imodintro
      isplitl [Ha HL]
      · iapply BigSepL.bigSepL_cons.2
        isplitl [Ha]
        · iexists v
          isplitr
          · ipureintro
            rfl
          · iexact Ha
        · iapply (BigSepL.bigSepL_mono_of_forall
            (Φ := fun k y => iprop(∃ v', ⌜vs[k]? = some v'⌝ ∗ Rv (GF := GF) γ GD y w v'))
            (Ψ := fun k y => iprop(∃ v', ⌜(v :: vs)[k + 1]? = some v'⌝ ∗ Rv (GF := GF) γ GD y w v'))
            (l := Cl) fun {k y} => by simp only [List.getElem?_cons_succ]; exact .rfl) $$ HL
      · iintro %a' %v' %ha' %hw'
        rcases List.mem_cons.1 ha' with rfl | h
        · obtain rfl := gwritesByteDet _ _ _ _ _ hw' hv
          iexists H
          isplitl []
          · iexact Hs
          · ipureintro
            exact hl
        · ihave H2 := HS $$ %a' %v' %h %hw'
          iexact H2

/-- THE n-BYTE OWNED WRITE of a last-value list: every byte's history appended with its new
value, `w`'s Own deposit enters `ownInv X`. -/
theorem RVLWrite (γ : GName) (GD : Gdexec) (X : GSet Int) (Cl : List Int) (s : GSet Geid)
    (e w : Geid) (vold vs : List (BitVec 8)) :
    w ∉ s → gmoLt GD.gdG e w → vs.length = Cl.length →
    (∀ (j : Nat) a v, Cl[j]? = some a → vs[j]? = some v → gwritesByte GD.gdG w a v) →
    (∀ a v, gwritesByte GD.gdG w a v → a ∈ Cl) →
    ownInv (GF := GF) X γ GD s ∗ RVL γ GD Cl e vold ⊢ |==> (
      ownInv X γ GD (({w} : GSet Geid) ∪ s) ∗ RVL γ GD Cl w vs) := by
  intro hn hew hlen hall honly
  unfold RVL ownInv
  iintro ⟨#Hinv, -, HR⟩
  ihave HR := (BigSepL.bigSepL_mono_of_forall
    (Φ := fun j a => iprop(∃ v, ⌜vold[j]? = some v⌝ ∗ Rv (GF := GF) γ GD a e v))
    (Ψ := fun _ a => iprop(∃ vo, Rv (GF := GF) γ GD a e vo)) (l := Cl) fun {k a} => by
      iintro ⟨%v, -, Ha⟩
      iexists v
      iexact Ha) $$ HR
  imod AxSpinX.rvlSnaps γ GD Cl vs e w hew hlen hall $$ HR with ⟨HR, #HS⟩
  imodintro
  isplitr [HR]
  · iapply (AxSpinProt.bigSepSUnionSingleton hn).2
    isplitl []
    · unfold Φx
      iintro %a %v %_ %hw
      ihave H2 := HS $$ %a %v %(honly a v hw) %hw
      iexact H2
    · iexact Hinv
  · isplitr
    · ipureintro
      exact hlen
    · iexact HR

/-- (Lean-only) `Rv_read`'s inner `iAssert`: every write covered (gmo-before `r`) is in the
auth's history. -/
theorem AxSpinX.histInOfCov (γ : GName) (GD : Gdexec) (a : Int) (r : Geid) (H : List Hent) :
    histAuth (GF := GF) γ a 1 H ∗
      (∀ w v, ⌜gwritesByte GD.gdG w a v⌝ -∗ ⌜gmoLt GD.gdG w r⌝ -∗
        ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ a H') ⊢
      ⌜∀ w v', gwritesByte GD.gdG w a v' → gmoLt GD.gdG w r → w ∈ H.map Prod.fst⌝ := by
  refine (BI.forall_intro fun w => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun v => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun hw => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun hlt => ?_).trans BI.pure_forall.2
  iintro ⟨Ha, Hcov⟩
  icases Hcov $$ %w %v %hw %hlt with ⟨%H', %hw', Hs⟩
  iapply histSnapIn γ a 1 H H' w hw'
  isplitl [Ha]
  · iexact Ha
  · iexact Hs

/-- THE OWNED READ with VALUE of byte `a` under `Rv a e vl` (`e` gmo-before `r`; every
po-earlier write of `a` by `r`'s hart is gmo-before `r`): `r` reads `vl`.  Genesis arm (empty
history): no visible write, `r` reads the image.  The handle is kept. -/
theorem RvRead (γ : GName) (GD : Gdexec) (X : GSet Int) (s : GSet Geid) (a : Int) (e r : Geid)
    (vl : BitVec 8) :
    rvwmoCatConsistent GD → a ∈ X → gmoLt GD.gdG e r → WPh GD.gdG s r →
    (∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r → gmoLt GD.gdG w r) →
    ownInv (GF := GF) X γ GD s ∗ Rv γ GD a e vl ⊢
      Rv γ GD a e vl ∗ ⌜∀ t v, greadsByte GD.gdG r a t v → v = vl⌝ := by
  intro hcons haX her hwp hpo
  unfold Rv
  iintro ⟨#Hinv, %H, Ha, %hp⟩
  obtain ⟨⟨hwr, hch⟩, hc⟩ := hp
  ihave #Hcov := AxSpinProt5.covMoX γ X a GD s r haX hwp $$ Hinv
  icases (persistent_entails_left (AxSpinX.histInOfCov (GF := GF) γ GD a r H))
    $$ [$Ha $Hcov] with ⟨⟨Ha, -⟩, %hin⟩
  rcases hc with ⟨rfl, himg⟩ | ⟨⟨wl, hlast⟩, ht⟩
  · isplitl [Ha]
    · iexists ([] : List Hent)
      isplitl [Ha]
      · iexact Ha
      · ipureintro
        exact ⟨⟨hwr, hch⟩, Or.inl ⟨rfl, himg⟩⟩
    · ipureintro
      intro t v hrd
      cases t with
      | zero =>
        have h0 : GD.gdG.gxImg a = some v := (hcons.2.2.1 r a 0 v hrd).1
        rw [himg] at h0
        exact (Option.some.inj h0).symm
      | succ j =>
        obtain ⟨w, -, hw', hvis⟩ := (hcons.2.2.1 r a (j + 1) v hrd).1
        have hlt : gmoLt GD.gdG w r := hvis.elim id (hpo w v hw')
        have := hin w v hw' hlt
        simp at this
  · rcases Classical.em (∃ t v, greadsByte GD.gdG r a t v) with hex | hex
    · have hown : ∀ w v', gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
          w ∈ H.map Prod.fst := fun w v' hw' hp => hin w v' hw' (hpo w v' hw' hp)
      ihave HT := (AxSpinProt.tokTieSingleton GD γ a H e ht).1 $$ Ha
      icases (persistent_entails_left (ownedReadRule (GF := GF) GD a r γ H {[e := (1 : Qp)]} wl vl
          hcons hwr hch hown hlast hex
          (Or.inl ⟨e, by rw [domSingleton, elemOfSingleton], her⟩)))
        $$ [$HT $Hcov] with ⟨⟨HT, -⟩, %hv⟩
      ihave Ha := (AxSpinProt.tokTieSingleton GD γ a H e ht).2 $$ HT
      isplitl [Ha]
      · iexists H
        isplitl [Ha]
        · iexact Ha
        · ipureintro
          exact ⟨⟨hwr, hch⟩, Or.inr ⟨⟨wl, hlast⟩, ht⟩⟩
      · ipureintro
        exact hv.2
    · isplitl [Ha]
      · iexists H
        isplitl [Ha]
        · iexact Ha
        · ipureintro
          exact ⟨⟨hwr, hch⟩, Or.inr ⟨⟨wl, hlast⟩, ht⟩⟩
      · ipureintro
        exact fun t v h => absurd ⟨t, v, h⟩ hex

/-- The list version: the read value of every byte of `Cl`. -/
theorem RVLRead (γ : GName) (GD : Gdexec) (X : GSet Int) (s : GSet Geid) (Cl : List Int)
    (e r : Geid) (vs : List (BitVec 8)) :
    rvwmoCatConsistent GD → (∀ a, a ∈ Cl → a ∈ X) → gmoLt GD.gdG e r → WPh GD.gdG s r →
    (∀ w a v', a ∈ Cl → gwritesByte GD.gdG w a v' → WeakRvwmoGraph.gpo GD.gdG w r →
      gmoLt GD.gdG w r) →
    ownInv (GF := GF) X γ GD s ∗ RVL γ GD Cl e vs ⊢
      RVL γ GD Cl e vs ∗
        ⌜∀ (j : Nat) a t v, Cl[j]? = some a → greadsByte GD.gdG r a t v → vs[j]? = some v⌝ := by
  intro hcons hX her hwp hpo
  unfold RVL
  iintro ⟨#Hinv, %hlen, HR⟩
  ihave HR := (BigSepL.bigSepL_impl
    (Φ := fun j a => iprop(∃ v, ⌜vs[j]? = some v⌝ ∗ Rv (GF := GF) γ GD a e v))
    (Ψ := fun j a => iprop((∃ v, ⌜vs[j]? = some v⌝ ∗ Rv (GF := GF) γ GD a e v) ∗
      ⌜∀ t v, greadsByte GD.gdG r a t v → vs[j]? = some v⌝)) (l := Cl)) $$ HR
  ihave HR := HR $$ []
  · imodintro
    iintro %k %a %hk ⟨%v, %hv, Ha⟩
    have ha : a ∈ Cl := List.mem_of_getElem? hk
    icases (RvRead γ GD X s a e r v hcons (hX a ha) her hwp (fun w v' => hpo w a v' ha))
      $$ [$Hinv $Ha] with ⟨Ha, %hf⟩
    isplitl [Ha]
    · iexists v
      isplitr
      · ipureintro
        exact hv
      · iexact Ha
    · ipureintro
      intro t v' hr
      rw [hv, hf t v' hr]
  icases (BigSepL.bigSepL_sep_eqv
    (Φ := fun j a => iprop(∃ v, ⌜vs[j]? = some v⌝ ∗ Rv (GF := GF) γ GD a e v))
    (Ψ := fun j a => iprop(⌜∀ t v, greadsByte GD.gdG r a t v → vs[j]? = some v⌝ : IProp GF))
    (l := Cl)).1 $$ HR with ⟨HR, HP⟩
  ihave %hP := (BigSepL.bigSepL_pure_intro
    (φ := fun j a => ∀ t v, greadsByte GD.gdG r a t v → vs[j]? = some v) (l := Cl)
    (PROP := IProp GF)) $$ HP
  isplitl [HR]
  · isplitr
    · ipureintro
      exact hlen
    · iexact HR
  · ipureintro
    intro j a t v hj hr
    exact hP j a hj t v hr

/-- Forgetting the value. -/
theorem RVLAny (γ : GName) (GD : Gdexec) (Cl : List Int) (e : Geid) (vs : List (BitVec 8)) :
    RVL (GF := GF) γ GD Cl e vs ⊢ ∃ vs', RVL γ GD Cl e vs' := by
  iintro H
  iexists vs
  iexact H

end rv

/-! # 4. THE INSTANCE, `RPid`, `xv6Init`, the allocation -/

class AxSpinX.Xv6G (GF : BundledGFunctors) where
  [xv6LogG : AxlogG GF Hent]
  [xv6LockG : SpinlockG GF]
  [xv6MonoG : MonoNatG GF]
  xv6IssG : ElemG GF (constOF (Auth (DisjointLeibnizSet (GSet Int))))

attribute [reducible, instance] AxSpinX.Xv6G.xv6LogG AxSpinX.Xv6G.xv6LockG
  AxSpinX.Xv6G.xv6MonoG AxSpinX.Xv6G.xv6IssG

/-- The ghost names: per-byte histories, the lock registry, Theorem 2's ●mono and issued-set. -/
structure Xv6N where
  xnH : GName
  xnReg : GName
  xnM : GName
  xnI : GName

section inst
variable {GF : BundledGFunctors} [AxSpinX.Xv6G GF]

def issuedAuth (γ : GName) (S : GSet Int) : IProp GF :=
  iOwn (E := AxSpinX.Xv6G.xv6IssG) γ (● (DisjointLeibnizSet.valid S))

def issuedFrag (γ : GName) (x : Int) : IProp GF :=
  iOwn (E := AxSpinX.Xv6G.xv6IssG) γ (◯ (DisjointLeibnizSet.valid ({x} : GSet Int)))

variable (L : Xlay)

def protXv6 (nm : Xv6N) (GD : Gdexec) (_ : Unit) (s : GSet Geid) : IProp GF :=
  iprop(⌜WC GD.gdG s ∧ CPUOK (clb L) cvx GD.gdG s ∧ WOK L GD.gdG s⌝ ∗
    ownInv (XO L) nm.xnH GD s ∗ lkInv nm.xnReg L.xlLk GD s)

/-- nextpid's component: exact value `v` (0 ≤ v < 2³²), ●mono, the issued set below `v`.
Names: `γh` histories, `γm` mono, `γi` issued. -/
def RNp (γh γm γi : GName) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(∃ v : Int, ⌜0 ≤ v ∧ v < 2 ^ 32⌝ ∗
    RVL γh GD (npb L) e (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 v)) ∗
    MonoNat.auth_own γm (DFrac.own 1) (.ofNat v.toNat) ∗
    ∃ S, issuedAuth γi S ∗ ⌜∀ x, x ∈ S → 0 ≤ x ∧ x < v⌝)

/-- lk->cpu's component (value-generic; exact after the holder's write). -/
def RCpu (γh : GName) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(∃ vs, RVL γh GD (clb L) e vs)

def RPid (γh γm γi : GName) (GD : Gdexec) (e : Geid) : IProp GF :=
  iprop(RCpu L γh GD e ∗ RNp L γh γm γi GD e)

theorem RCpuTransportable (γh : GName) (GD : Gdexec) :
    rvwmoCatConsistent GD → lkTransportable GD (RCpu (GF := GF) L γh GD) := by
  intro hcons e e' hob
  unfold RCpu
  iintro ⟨%vs, H⟩
  iexists vs
  iapply (RVLTransport γh GD (clb L) e e' vs hcons hob) $$ H

theorem RNpTransportable (γh γm γi : GName) (GD : Gdexec) :
    rvwmoCatConsistent GD → lkTransportable GD (RNp (GF := GF) L γh γm γi GD) := by
  intro hcons e e' hob
  unfold RNp
  iintro ⟨%v, %hv, H, Hm, HS⟩
  iexists v
  isplitr
  · ipureintro
    exact hv
  isplitl [H]
  · iapply (RVLTransport γh GD (npb L) e e' _ hcons hob) $$ H
  isplitl [Hm]
  · iexact Hm
  · iexact HS

theorem RPidTransportable (γh γm γi : GName) (GD : Gdexec) :
    rvwmoCatConsistent GD → lkTransportable GD (RPid (GF := GF) L γh γm γi GD) := by
  intro hcons e e' hob
  unfold RPid
  iintro ⟨H1, H2⟩
  isplitl [H1]
  · iapply (RCpuTransportable L γh GD hcons e e' hob) $$ H1
  · iapply (RNpTransportable L γh γm γi GD hcons e e' hob) $$ H2

/-- The per-hart init resource.  `kernelText`, `cpuOwn`, `stackOwn` are PURE layout facts at
this instance: the read-only and private classes are enforced by σ's WOK (FINDING 1). -/
def AxSpinX.kernelText : IProp GF := iprop(⌜∀ a j, L.xlRo a → ¬ wok L a j⌝)
def AxSpinX.cpuOwn (i : Agent) : IProp GF :=
  iprop(⌜i ∈ L.xlHarts ∧ ∀ a, a ∈ L.xlCpuf i → priv L a i⌝)
def AxSpinX.stackOwn (i : Agent) : IProp GF :=
  iprop(⌜i ∈ L.xlHarts ∧ ∀ a, a ∈ L.xlStk i → priv L a i⌝)

def xv6Init (GD : Gdexec) (nm : Xv6N) (i : Agent) : IProp GF :=
  iprop(AxSpinX.kernelText L ∗ AxSpinX.cpuOwn L i ∗ AxSpinX.stackOwn L i ∗
    isLock nm.xnReg L.xlLk (RPid L nm.xnH nm.xnM nm.xnI GD) ∗ notheld nm.xnReg L.xlLk i)

/-- THE ALLOCATION (Hob_alloc).  Image premises: lk->cpu = 0 (initlock), nextpid = n0 (the
genesis R lives in σ0's genesis box: initlock's unheld state has no protocol arm). -/
theorem xv6HobAlloc (GD : Gdexec) (n0 : Int) :
    xlayOk L →
    (∀ a, a ∈ clb L → GD.gdG.gxImg a = some b0) →
    0 ≤ n0 ∧ n0 < 2 ^ 32 →
    (∀ (j : Nat) a v, (npb L)[j]? = some a →
      (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))[j]? = some v → GD.gdG.gxImg a = some v) →
    ⊢ iprop(|==> ∃ (nm : Xv6N) (σ0 : Unit), protXv6 (GF := GF) L nm GD σ0 ∅ ∗
      [∗list] i ∈ L.xlHarts, xv6Init L GD nm i) := by
  intro HL Hcl Hn0 Hnp
  obtain ⟨-, -, -, Hro, Hnd, -⟩ := id HL
  have Hdisj : LawfulSet.ofList (clb L) ## (LawfulSet.ofList (npb L) : GSet Int) := by
    rw [elemOfDisjoint]
    intro y hy hy'
    exact clbNpbDisj L HL y (LawfulSet.mem_ofList.2 hy) (LawfulSet.mem_ofList.2 hy')
  have HlenC : (List.replicate 8 b0).length = (clb L).length := by
    simp [clb, clRange]
  have HimgC : ∀ (j : Nat) a v, (clb L)[j]? = some a → (List.replicate 8 b0)[j]? = some v →
      GD.gdG.gxImg a = some v := by
    intro j a v Hj Hv
    obtain rfl := List.eq_of_mem_replicate (List.mem_of_getElem? Hv)
    exact Hcl a (List.mem_of_getElem? Hj)
  have HlenN : (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0)).length = (npb L).length := by
    rw [wbytesLength]
    simp [npb, clRange]
  imod histAlloc (GF := GF) (XO L) ([] : List Hent) with ⟨%γh, H⟩
  unfold XO
  icases (BigSepS.bigSepS_union (Φ := fun a => histAuth (GF := GF) γh a 1 ([] : List Hent))
    Hdisj).1 $$ H with ⟨HC, HN⟩
  ihave HC := (BigSepS.bigSepS_of_list (NoDupClb L HL)).1 $$ HC
  ihave HN := (BigSepS.bigSepS_of_list (NoDupNpb L HL)).1 $$ HN
  ihave HRC := RVLGenesis γh GD (clb L) (List.replicate 8 b0) HlenC HimgC $$ HC
  ihave HRN := RVLGenesis γh GD (npb L) (WeakInterpProj.wbytes 4 (BitVec.ofInt 32 n0))
    HlenN Hnp $$ HN
  imod MonoNat.own_alloc (GF := GF) (.ofNat n0.toNat) with ⟨%γm, Hm, -⟩
  imod iOwn_alloc (E := AxSpinX.Xv6G.xv6IssG (GF := GF))
      (● (DisjointLeibnizSet.valid (∅ : GSet Int)) : Auth (DisjointLeibnizSet (GSet Int)))
      (Auth.auth_valid.mpr DisjointLeibnizSet.valid_set) with ⟨%γi, Hi⟩
  imod (lkInvAlloc L.xlLk GD L.xlHarts (RPid (GF := GF) L γh γm γi GD) Hnd)
    $$ [HRC HRN Hm Hi] with ⟨%reg, Hinv, #Hil, Hnh⟩
  · iintro %e
    unfold RPid RCpu RNp
    isplitl [HRC]
    · iexists (List.replicate 8 b0)
      iapply HRC
    · iexists n0
      isplitr
      · ipureintro
        exact Hn0
      isplitl [HRN]
      · iapply HRN
      isplitl [Hm]
      · iexact Hm
      · iexists (∅ : GSet Int)
        isplitl [Hi]
        · unfold issuedAuth
          iexact Hi
        · ipureintro
          exact fun x hx => absurd hx notElemOfEmpty
  imodintro
  iexists (⟨γh, reg, γm, γi⟩ : Xv6N), ()
  isplitl [Hinv]
  · unfold protXv6
    isplitr
    · ipureintro
      exact ⟨fun e w He => absurd He notElemOfEmpty, fun w Hw => absurd Hw notElemOfEmpty,
        fun e a v He => absurd He notElemOfEmpty⟩
    isplitr [Hinv]
    · unfold ownInv
      iapply BigSepS.bigSepS_empty.2
      iempintro
    · iexact Hinv
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ i => notheld (GF := GF) reg L.xlLk i)
      (Ψ := fun _ i => xv6Init (GF := GF) L GD (⟨γh, reg, γm, γi⟩ : Xv6N) i)) $$ Hnh
    imodintro
    iintro %k %i %hk Hi
    have Hik : i ∈ L.xlHarts := List.mem_of_getElem? hk
    unfold xv6Init AxSpinX.kernelText AxSpinX.cpuOwn AxSpinX.stackOwn
    isplitr
    · ipureintro
      exact fun a j Ha => Hro a j Ha
    isplitr
    · ipureintro
      exact ⟨Hik, fun a Ha => ⟨Hik, Or.inr Ha⟩⟩
    isplitr
    · ipureintro
      exact ⟨Hik, fun a Ha => ⟨Hik, Or.inl Ha⟩⟩
    isplitl []
    · iexact Hil
    · iexact Hi

end inst

/-! # 5. THE POLICY and its `Hok` (generic: every class, every event) -/

@[reducible] def xv6Pol (GT : GdexecT) : Axpol := splPol GT

theorem xv6AxpolWf (GT : GdexecT) : @axpolWf (xv6Pol GT) := splAxpolWf GT

/-- `Hok` of `AxSpinGate.tierAAdequacyAnnGateT`: CLASS-INDEPENDENT (no handout depends on the
address). -/
theorem xv6Hok (GT : GdexecT) (HconsT : rvwmoCatConsistentT GT) (Hcl : ctrlClosed GT) :
    ∀ e e', e' ∈ @Axpol.sPol (xv6Pol GT) (gtAdGd GT) e ∪ @Axpol.lobp (xv6Pol GT) (gtAdGd GT) e →
      polDS GT.gtG (gsrcT GT) e' e ∨ e' ∈ gsrcT GT e :=
  splHok GT HconsT Hcl

end Weak
