/-
**kexec's image algebra** (Rocq `KexecBuilt.v`), RE-BASED onto the Lean user
memory (wave 7b, decision D18; plan: notes/briefs/kexec_image_plan.md).

STATUS: PARTIAL.  §0 (the view and the laws that move it) is written; the push
geometry, the ELF image algebra, the loadseg window, the size chain, the phdr
walk, the permission rows and `kexecBuilt` itself follow once K-A's `KexecDefs`
/ `ElfFile` / `ElfBridge` (and, for S6/S7, D17's `UserPerm` subset) land.

THE RE-BASE (D18, a recorded deviation).  Rocq's image is `M : gmap Z (bv 8)`
keyed by byte address; under `proc_pt P M` its domain is exactly the bytes of
the mapped pages.  The Lean pair `(P, M)` stores the same thing per page
(`umPages`: `(M k).length = 4096 ∗ byteBuf (pte2pa w) (M k)` at every mapped
`k`), so Rocq's `M !! a` is the FUNCTION `umemView P M a` below.  Every Rocq
predicate over the image is kept verbatim over an abstract
`Mv : Int → Option (BitVec 8)` (instantiated at `umemView P M`); what is
re-based is only the laws that MOVE the view, now stated over the landed Lean
operations instead of the gmap algebra:

  * uvmalloc (`uvmallocOk`) in place of `umem_grow` (§0.2).  Lean's uvmalloc
    zero-fills only its run, where `umem_grow` zero-fills every live unmapped
    byte; the two agree on a covered space, which every kexec state is.  The
    "old byte survives" law needs uvmalloc's own premise `hfree` (the run was
    unmapped), which `umem_grow`'s left-biased union did not;
  * a page write (`umemWrite`, P unchanged) in place of `umem_write` (§0.3);
  * copyout's post (`P.extSz psz P'`, `umemWrite (viewFaulted P P' M)`) in
    place of `umem_wr`: on a covered space (`lazyFree`, Rocq's `um_covered`)
    copyout gains no leaf and faults nothing (`kxCopyout_covered`, §0.4), so
    its image IS `umemWrite M dst bs`.  This replaces Rocq's
    `proc_pt ⊣⊢ proc_ptm` crossing (KexecPtImage §6) by a pure fact, and
    Rocq's `umem_wr_write`/`kx_wr_linear` no-wrap rows are not needed (the
    Lean write is Nat-keyed);
  * uvmclear (`UPtd.clearU`) keeps the view (§0.4, `umemView_clearU`);
  * Rocq's `proc_pt_fresh_above(_z)` (an entailment reading `dom M`) is the
    PURE `umemGet_none_above`: the view is defined from `P`.

The view is the MAPPED one; Rocq's `us_M` is the lazy view (`proc_ptm`).  They
agree under `lazyFree` (`kexec_built`'s S8), which is where kexec hands its
image over.

A lemma file: it imports definitional and Spec files only.
-/
import Xv6.UMem
import Xv6.UMemLemmas
import Xv6.UPtAllocLemmas
import Xv6.SpecUvmalloc
import Xv6.SpecUvmclear

namespace Xv6

open MachCSL
open Iris.Std (get?)

/-! ## §0.1 The view -/

/-- **Byte `n` of an address space** (Rocq's `M !! n` under `proc_pt P M`):
defined exactly on the mapped pages. -/
def umemGet (P : UPtd) (M : Nat → List (BitVec 8)) (n : Nat) : Option (BitVec 8) :=
  if (get? P.um (n / 4096)).isSome then (M (n / 4096))[n % 4096]? else none

/-- **The image at Rocq's `Z` keys** (nothing below `0`): the abstract byte map
the kexec predicates are stated over. -/
def umemView (P : UPtd) (M : Nat → List (BitVec 8)) : Int → Option (BitVec 8) :=
  fun a => if 0 ≤ a then umemGet P M a.toNat else none

/-- Every mapped page is a full page (what `umPages` pins, Rocq's
`dom M = uva_dom P`). -/
def umPageLen (P : UPtd) (M : Nat → List (BitVec 8)) : Prop :=
  ∀ k w, get? P.um k = some w → (M k).length = 4096

namespace KexecBuilt

theorem umemView_ofNat (P : UPtd) (M : Nat → List (BitVec 8)) (n : Nat) :
    umemView P M (n : Int) = umemGet P M n := by
  simp [umemView]

theorem umemView_neg (P : UPtd) (M : Nat → List (BitVec 8)) (a : Int) (h : a < 0) :
    umemView P M a = none := by
  simp only [umemView]; rw [if_neg (by omega)]

/-- A defined byte is on a mapped page. -/
theorem umemGet_mapped {P : UPtd} {M : Nat → List (BitVec 8)} {n : Nat} {b : BitVec 8}
    (h : umemGet P M n = some b) : (get? P.um (n / 4096)).isSome := by
  unfold umemGet at h
  split at h
  · assumption
  · cases h

/-- Every byte of a mapped (full) page is defined (Rocq `proc_pt_page_bytes`). -/
theorem umemGet_some_of_mapped {P : UPtd} {M : Nat → List (BitVec 8)} (hlen : umPageLen P M)
    {n : Nat} (hm : (get? P.um (n / 4096)).isSome) : umemGet P M n = some (umemByte M n) := by
  unfold umemGet umemByte
  rw [if_pos hm]
  cases hk : get? P.um (n / 4096) with
  | none => rw [hk] at hm; cases hm
  | some w =>
    have hl := hlen _ w hk
    rw [List.getElem?_eq_getElem (by rw [hl]; omega)]
    simp

/-- The view depends on the table only through its domain. -/
theorem umemGet_congr {P P' : UPtd} (M : Nat → List (BitVec 8))
    (h : ∀ k, (get? P.um k).isSome = (get? P'.um k).isSome) : umemGet P M = umemGet P' M := by
  funext n; unfold umemGet; rw [h]

theorem umemView_congr {P P' : UPtd} (M : Nat → List (BitVec 8))
    (h : ∀ k, (get? P.um k).isSome = (get? P'.um k).isSome) : umemView P M = umemView P' M := by
  funext a; unfold umemView; rw [umemGet_congr M h]

/-- **Nothing above the break** (Rocq `proc_pt_fresh_above(_z)`, now pure):
under `umBelow sz`, no byte at or above a page-aligned bound past `sz` is
defined. -/
theorem umemGet_none_above {P : UPtd} (M : Nat → List (BitVec 8)) {sz : BitVec 64}
    (hb : umBelow sz P) {bnd : Nat} (halign : bnd % 4096 = 0) (hge : sz.toNat ≤ bnd)
    {n : Nat} (hn : bnd ≤ n) : umemGet P M n = none := by
  unfold umemGet
  rw [if_neg]
  intro hm
  cases hk : get? P.um (n / 4096) with
  | none => rw [hk] at hm; cases hm
  | some w =>
    have hlt := hb _ w hk
    have hpg : pgRoundUpN sz.toNat ≤ bnd := by
      have := UPtAlloc.pgRoundUpN_le hge
      have hb' : pgRoundUpN bnd = bnd := by unfold pgRoundUpN; omega
      omega
    have : bnd ≤ n / 4096 * 4096 := by omega
    omega

theorem umemView_none_above {P : UPtd} (M : Nat → List (BitVec 8)) {sz : BitVec 64}
    (hb : umBelow sz P) {bnd : Nat} (halign : bnd % 4096 = 0) (hge : sz.toNat ≤ bnd)
    {a : Int} (ha : (bnd : Int) ≤ a) : umemView P M a = none := by
  unfold umemView
  rw [if_pos (by omega)]
  exact umemGet_none_above M hb halign hge (by omega)

/-! ## §0.2 uvmalloc (Rocq `umem_grow`) -/

/-- The page of byte `n` is in uvmalloc's run. -/
def uvmaInRun (o nw : BitVec 64) (n : Nat) : Prop :=
  uvmaVpn0 o ≤ n / 4096 ∧ n / 4096 < uvmaVpn0 o + uvmaNp o nw

/-- A byte outside the run is untouched (the frame half of `umem_grow`). -/
theorem umemGet_uvmalloc_out {P P' : UPtd} {M M' : Nat → List (BitVec 8)} {o nw x : BitVec 64}
    (hok : uvmallocOk P P' M M' o nw x) {n : Nat} (hn : ¬ uvmaInRun o nw n) :
    umemGet P' M' n = umemGet P M n := by
  obtain ⟨hg, hm⟩ := hok.2.1 (n / 4096) hn
  unfold umemGet; rw [hg, hm]

/-- **An old byte survives** (Rocq `umem_grow_lookup_old`), given uvmalloc's
own premise that its run was unmapped. -/
theorem umemGet_uvmalloc_old {P P' : UPtd} {M M' : Nat → List (BitVec 8)} {o nw x : BitVec 64}
    (hok : uvmallocOk P P' M M' o nw x)
    (hfree : ∀ i, i < uvmaNp o nw → get? P.um (uvmaVpn0 o + i) = none)
    {n : Nat} {b : BitVec 8} (h : umemGet P M n = some b) : umemGet P' M' n = some b := by
  have hm := umemGet_mapped h
  rw [umemGet_uvmalloc_out hok ?_, h]
  rintro ⟨h1, h2⟩
  have := hfree (n / 4096 - uvmaVpn0 o) (by omega)
  rw [show uvmaVpn0 o + (n / 4096 - uvmaVpn0 o) = n / 4096 by omega] at this
  rw [this] at hm; cases hm

/-- **A run byte reads zero** (Rocq `umem_grow_lookup_zero`). -/
theorem umemGet_uvmalloc_zero {P P' : UPtd} {M M' : Nat → List (BitVec 8)} {o nw x : BitVec 64}
    (hok : uvmallocOk P P' M M' o nw x) {n : Nat} (hn : uvmaInRun o nw n) :
    umemGet P' M' n = some 0#8 := by
  obtain ⟨⟨r, -, hr⟩, hz⟩ := hok.2.2 (n / 4096 - uvmaVpn0 o) (by unfold uvmaInRun at hn; omega)
  rw [show uvmaVpn0 o + (n / 4096 - uvmaVpn0 o) = n / 4096 by unfold uvmaInRun at hn; omega]
    at hr hz
  unfold umemGet
  rw [hr, hz]
  simp only [Option.isSome_some, if_true]
  rw [List.getElem?_replicate]
  rw [if_pos (by omega)]

/-- uvmalloc keeps every mapped page full (`umPages`' length fact, carried). -/
theorem umPageLen_uvmalloc {P P' : UPtd} {M M' : Nat → List (BitVec 8)} {o nw x : BitVec 64}
    (hok : uvmallocOk P P' M M' o nw x) (hlen : umPageLen P M) : umPageLen P' M' := by
  intro k w hk
  by_cases hr : uvmaVpn0 o ≤ k ∧ k < uvmaVpn0 o + uvmaNp o nw
  · obtain ⟨-, hz⟩ := hok.2.2 (k - uvmaVpn0 o) (by omega)
    rw [show uvmaVpn0 o + (k - uvmaVpn0 o) = k by omega] at hz
    rw [hz, List.length_replicate]
  · obtain ⟨hg, hm⟩ := hok.2.1 k hr
    rw [hm]; rw [hg] at hk; exact hlen k w hk

/-! ## §0.3 A page write (Rocq `umem_write`), the table unchanged -/

/-- **A byte the write misses** (Rocq `umem_write_lookup_out`). -/
theorem umemGet_write_out (P : UPtd) (M : Nat → List (BitVec 8)) (va : Nat) (bs : List (BitVec 8))
    {n : Nat} (hn : ¬ (va ≤ n ∧ n < va + bs.length)) :
    umemGet P (umemWrite M va bs) n = umemGet P M n := by
  unfold umemGet
  split
  · rw [UMemL.umemWrite_getElem?]
    cases (M (n / 4096))[n % 4096]? with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [if_neg (by rw [Nat.div_add_mod' n 4096]; exact hn)]
  · rfl

/-- **A byte the write hits** (Rocq `umem_write_lookup_in`), where the view
was defined (Rocq's `umem_write_dom` premise). -/
theorem umemGet_write_in (P : UPtd) (M : Nat → List (BitVec 8)) (va : Nat) (bs : List (BitVec 8))
    {j : Nat} (hj : j < bs.length) (hdef : (umemGet P M (va + j)).isSome) :
    umemGet P (umemWrite M va bs) (va + j) = bs[j]? := by
  unfold umemGet at hdef ⊢
  split at hdef
  · rw [if_pos (by assumption), UMemL.umemWrite_getElem?]
    cases hb : (M ((va + j) / 4096))[(va + j) % 4096]? with
    | none => rw [hb] at hdef; cases hdef
    | some b =>
      simp only [Option.map_some]
      rw [Nat.div_add_mod' (va + j) 4096, if_pos ⟨by omega, by omega⟩,
        show va + j - va = j by omega, List.getElem?_eq_getElem hj]
      rfl
  · cases hdef

/-- A write keeps every page full. -/
theorem umPageLen_write {P : UPtd} {M : Nat → List (BitVec 8)} (va : Nat) (bs : List (BitVec 8))
    (hlen : umPageLen P M) : umPageLen P (umemWrite M va bs) := by
  intro k w hk
  rw [UMemL.umemWrite_length]; exact hlen k w hk

theorem umemView_write_out (P : UPtd) (M : Nat → List (BitVec 8)) (va : Nat) (bs : List (BitVec 8))
    {a : Int} (ha : ¬ ((va : Int) ≤ a ∧ a < va + bs.length)) :
    umemView P (umemWrite M va bs) a = umemView P M a := by
  unfold umemView
  split
  · exact umemGet_write_out P M va bs (by omega)
  · rfl

theorem umemView_write_in (P : UPtd) (M : Nat → List (BitVec 8)) (va : Nat) (bs : List (BitVec 8))
    {j : Nat} (hj : j < bs.length) (hdef : (umemView P M ((va : Int) + j)).isSome) :
    umemView P (umemWrite M va bs) ((va : Int) + j) = bs[j]? := by
  have hc : ((va : Int) + j) = ((va + j : Nat) : Int) := by omega
  rw [hc, umemView_ofNat] at hdef ⊢
  exact umemGet_write_in P M va bs hj hdef

/-! ## §0.4 copyout and uvmclear on a covered space -/

/-- **copyout on a covered space** (replaces Rocq's `proc_pt ⊣⊢ proc_ptm`
crossing, KexecPtImage §6): with every page below the break mapped, the
extension copyout reports gains no leaf, so nothing was faulted and its image
is a plain `umemWrite M`. -/
theorem kxCopyout_covered {P P' : UPtd} (M : Nat → List (BitVec 8)) {psz : BitVec 64}
    (hcov : lazyFree P.um psz) (hext : P.extSz psz P') :
    (∀ k, get? P'.um k = get? P.um k) ∧ viewFaulted P P' M = M := by
  have hsame : ∀ k, get? P'.um k = get? P.um k := by
    intro k
    cases hk : get? P.um k with
    | some w => exact hext.1.2.2 k w hk
    | none =>
      cases hk' : get? P'.um k with
      | none => rfl
      | some w' =>
        have hlt := hext.2.1 k w' hk hk'
        have := hcov k (Nat.lt_of_lt_of_le hlt (UPtAlloc.pgRoundUpN_ge _))
        rw [hk] at this; cases this
  refine ⟨hsame, ?_⟩
  funext k
  unfold viewFaulted
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [hsame k] at h2
  rw [Option.isNone_iff_eq_none] at h1
  rw [h1] at h2; cases h2

/-- The covered copyout keeps the view's domain. -/
theorem kxCopyout_dom {P P' : UPtd} {psz : BitVec 64} (M : Nat → List (BitVec 8))
    (hcov : lazyFree P.um psz) (hext : P.extSz psz P') :
    ∀ k, (get? P'.um k).isSome = (get? P.um k).isSome := by
  intro k; rw [(kxCopyout_covered M hcov hext).1 k]

/-- **uvmclear keeps every byte** (its leaf stays mapped). -/
theorem umemGet_clearU {P : UPtd} (M : Nat → List (BitVec 8)) {v : Nat} {w : BitVec 64}
    (hv : get? P.um v = some w) : umemGet (P.clearU v w) M = umemGet P M := by
  refine umemGet_congr M fun k => ?_
  simp only [UPtd.clearU]
  by_cases hk : v = k
  · subst hk; rw [Iris.Std.LawfulPartialMap.get?_insert_eq rfl, hv]; rfl
  · rw [Iris.Std.LawfulPartialMap.get?_insert_ne hk]

theorem umemView_clearU {P : UPtd} (M : Nat → List (BitVec 8)) {v : Nat} {w : BitVec 64}
    (hv : get? P.um v = some w) : umemView (P.clearU v w) M = umemView P M := by
  funext a; unfold umemView; rw [umemGet_clearU M hv]

end KexecBuilt

end Xv6
