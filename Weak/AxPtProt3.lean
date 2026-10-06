/-
Weak: **constraint A — THE PAGE-TABLE-WORD TOKEN** under the AxSL ownership machinery
(`AxGhost`'s per-byte history logs), the OWNED walker RMW, and the extraction of the
discipline from the token (AxSL tier).

Rocq: `iris/AxPtProt3.v` @ xxvzwolszwmp.

The Rocq header, in substance.  Over `AxPtProt` (the PTW model, H5') and `AxGhost`
(`histAuth`/`histSnap`).

THE PROTOCOL (statement; the WPd threading is the engine's, see `AxPtProt`'s header):
- PRIVATE (table reachable from no satp): the kernel hart holds the 8 full byte auths of
  each PTE word, `[∗list] j ∈ seq 0 8, histAuth γ (pa+j) 1 (Hs j)` — exactly the
  precondition of `AxProtBytes.wp_write_owned_tokn` (n = 8).  A PTE store is an ordinary
  owned 8-byte write.
- ACTIVE (reachable from some satp): the same auths PLUS the pure class invariant `clsHist`,
  the token `pteTok γ GP pa P Hs ks`: from position `ks j` (the install) on, every history
  entry is a `P`-byte.  The token RIDES THE CO CHAIN: deposited in the annotation of the
  co-latest window write; the walker of whichever hart walks the word PULLS it at its A/D
  RMW (it is LENT the token for exactly one RMW and returns it in the RMW's own deposit),
  appends ONE entry per byte and re-deposits.  `pteTokRmw` is the OWNED-RMW rule: the read
  half is pinned to the token's last entries (under the PTW model — NOT riscv.cat, cf.
  `AxGhost.ownedReadGhost`, which needs the full cat model); the write must stay in the class
  (A/D only: `rmwClassOkUpdate`).
- PLAIN walker reads pull nothing: their value is pinned by the DISCIPLINE `ptDisc`
  (+ H5'.2 for the at-or-after-the-install floor), and the discipline is EXTRACTED from the
  token's final history (`ptDiscOfHist`).
- PUBLISH (PRIVATE→ACTIVE): `pteTokPublish`; RECLAIM (ACTIVE→PRIVATE): `pteTokReclaim`
  (H5'.5 makes the reclaim sound).

PURE: §1.  IRIS: §2.  NON-VACUITY on `AxPtProt2.GPad`: §3 (`gadTokenRoute`).

O2 / D1: graph-level; no access kinds, no fetch events.  Nothing moves.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase (map below).  The duplicated Rocq name `chain_with_snoc'`
   (`notes/weak-port-dupnames.json`: AxPtProt3, AxSpinProt) is FILE-QUALIFIED:
   `AxPtProt3.chainWithSnoc'`.  `Hs_ad0`/`Hs_ad1` keep their capital (`HsAd0`/`HsAd1`, as
   `AxGhost`'s `Hdemo`).
2. VOCABULARY (`AxGhost` deviation 2): `last l` ↦ `l.getLast?`; `l !! i` ↦ `l[i]?`; `H.*1` ↦
   `H.map Prod.fst`; `seq 0 8` ↦ `List.range' 0 8` (as `AxPtProt2`); `default u o` ↦
   `o.getD u`; `mword 64` ↦ `BitVec 64`; `nth_byte x j` ↦ `nthByte (n := 8) x j`;
   `bool_decide` ↦ `decide`; `forallb` ↦ `List.all`; `w0` ↦ `AxPtProt2.w0`;
   `WeakVariant.update_PTE_Bits_variant` ↦ `updatePTEBitsVariant`.
3. CAMERAS: `axlogG Σ hent` ↦ `[AxlogG GF Hent]` (`AxGhost` deviation 3).
4. STATEMENT SHAPES (`AxGhost` deviation 4): `P -∗ Q` is `P ⊢ Q`; `P -∗ Q -∗ R` (with `Q`
   the boxed coverage) is `P ∗ Q ⊢ R`; `P ==∗ Q` is `P ⊢ |==> Q`; pure premises stay `→`.
5. Lean-only helper (file-qualified): `AxPtProt3.histSnapInKeep` — `histSnapIn` that returns
   the auth (Rocq's `iDestruct (hist_snap_in with "Hj0 Hsn") as %_` keeps `Hj0`; iris-lean's
   `icases` consumes spatial hypotheses).
6. PROOFS (not statements): the per-byte `vmr` case splits of `gad_token_route` (`do 8
   (destruct j …)`) are one `decide +kernel` over `(List.range 8).all …`; every `vmr` is
   `decide +kernel` on the boolean twins (`grbBSpec`, `gmoLtBSpec`, `gwritesWordBSound`).
7. The `Print Assumptions` lines have no Lean twin (the lint's axiom check covers them).

**Rocq → Lean name map.**  `cls_hist` ↦ `clsHist`; `chain_with_snoc'` ↦
`AxPtProt3.chainWithSnoc'`; `cls_hist_last_ok` ↦ `clsHistLastOk`; `cls_hist_snoc` ↦
`clsHistSnoc`; `gwix_pos_elem'` ↦ `gwixPosElem'`; `rmw_src` ↦ `rmwSrc`; `rmw_read_last` ↦
`rmwReadLast`; `pte_rmw_pure` ↦ `pteRmwPure`; `pt_disc_of_hist` ↦ `ptDiscOfHist`;
`pte_auths` ↦ `pteAuths`; `pte_tok` ↦ `pteTok`; `pte_tok_publish` ↦ `pteTokPublish`;
`pte_tok_reclaim` ↦ `pteTokReclaim`; `auths_in` ↦ `authsIn`; `auths_append` ↦
`authsAppend`; `pte_tok_rmw` ↦ `pteTokRmw`; `hist_covers_b` ↦ `histCoversB`;
`hist_covers_b_sound` ↦ `histCoversBSound`; `Hs_ad0`/`Hs_ad1` ↦ `HsAd0`/`HsAd1`;
`gad_token_route` ↦ `gadTokenRoute`.

**Dropped:** nothing (every Rocq definition and lemma of `AxPtProt3.v` is ported).
-/
import Weak.AxPtProt2
import Weak.AxGhost

namespace Weak

open Iris Iris.BI Iris.Std MachCSL MachCSL.Stdpp

/-! ## 1. Pure: class histories, the owned-RMW read, the extraction -/

/-- `H` is byte `a`'s (= window byte `j`'s) history: its entries write `a`, it is
gmo-chained, it reaches the install position `k`, and from `k` on every entry is a
`P`-byte. -/
def clsHist (G : Gexec) (a : Int) (j : Nat) (P : BitVec 64 → Prop) (k : Nat)
    (H : List Hent) : Prop :=
  (∀ p, p ∈ H → gwritesByte G p.1 a p.2) ∧
  chainWith (gmoLt G) (H.map Prod.fst) ∧
  k < H.length ∧
  (∀ n p, k ≤ n → H[n]? = some p → AxPtProt.byteOk P j p.2)

theorem AxPtProt3.chainWithSnoc' (R : Geid → Geid → Prop) (l : List Geid) (x : Geid) :
    chainWith R l → (∀ y, l.getLast? = some y → R y x) → chainWith R (l ++ [x]) := by
  intro hc hl i w1 w2 h1 h2
  by_cases hlt : i + 1 < l.length
  · rw [List.getElem?_append_left (by omega)] at h1
    rw [List.getElem?_append_left hlt] at h2
    exact hc i w1 w2 h1 h2
  · have hlen := lookup_lt_Some h2
    simp only [List.length_append, List.length_singleton] at hlen
    have hi : i + 1 = l.length := by omega
    rw [List.getElem?_append_right (by omega), hi, Nat.sub_self] at h2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
    subst h2
    rw [List.getElem?_append_left (by omega)] at h1
    apply hl
    rw [List.getLast?_eq_getElem?]
    have he : l.length - 1 = i := by omega
    rw [he]
    exact h1

theorem clsHistLastOk (G : Gexec) (a : Int) (j : Nat) (P : BitVec 64 → Prop) (k : Nat)
    (H : List Hent) (wl : Geid) (vl : BitVec 8) :
    clsHist G a j P k H → H.getLast? = some (wl, vl) → AxPtProt.byteOk P j vl := by
  rintro ⟨_, _, hk, ht⟩ hl
  rw [List.getLast?_eq_getElem?] at hl
  exact ht (H.length - 1) _ (by omega) hl

theorem clsHistSnoc (G : Gexec) (a : Int) (j : Nat) (P : BitVec 64 → Prop) (k : Nat)
    (H : List Hent) (u : Geid) (b : BitVec 8) :
    clsHist G a j P k H → gwritesByte G u a b → AxPtProt.byteOk P j b →
    (∀ p, H.getLast? = some p → gmoLt G p.1 u) →
    clsHist G a j P k (H ++ [(u, b)]) := by
  rintro ⟨hm, hch, hk, ht⟩ hw hb hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hm p hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact hw
  · simp only [List.map_append, List.map_cons, List.map_nil]
    apply AxPtProt3.chainWithSnoc' _ _ _ hch
    intro y hy
    rw [List.getLast?_map] at hy
    cases e : H.getLast? with
    | none => rw [e] at hy; cases hy
    | some p =>
      rw [e, Option.map_some, Option.some.injEq] at hy
      subst hy
      exact hl p e
  · simp only [List.length_append, List.length_singleton]
    omega
  · intro n p hn hp
    by_cases hlt : n < H.length
    · rw [List.getElem?_append_left hlt] at hp
      exact ht n p hn hp
    · rw [List.getElem?_append_right (by omega)] at hp
      cases e : n - H.length with
      | zero =>
        rw [e, List.getElem?_cons_zero, Option.some.injEq] at hp
        subst hp
        exact hb
      | succ m =>
        rw [e] at hp
        simp at hp

theorem gwixPosElem' (G : Gexec) (e : Geid) : 0 < gwix G e → e ∈ gwrites G := by
  unfold gwix
  cases hf : listFind (fun e' => decide (e' = e)) (gwrites G) with
  | none => intro h; exact absurd h (Nat.lt_irrefl 0)
  | some q =>
    intro _
    obtain ⟨i, x⟩ := q
    obtain ⟨hi, hx, _⟩ := list_find_Some.1 hf
    have : x = e := of_decide_eq_true hx
    subst this
    exact List.mem_of_getElem? hi

/-- The source of an atomic walker RMW's read half is gmo-before it. -/
theorem rmwSrc (GP : Gptw) (a : Int) (u : Geid) (t : Nat) (v : BitVec 8) :
    gwf (gpG GP) → h5WalkValue GP → h5AdAtomic GP →
    gwalk GP u → glblIs (gpG GP) u lbIsW → greadsByte (gpG GP) u a t v →
    ∀ s, gwriteAt (gpG GP) t = some s →
      gmoLt (gpG GP) s u ∧ gwritesByte (gpG GP) s a v ∧ gwix (gpG GP) s = t := by
  intro hwf hwv hada hu hwu hr s hs
  obtain ⟨hsw, hsix⟩ := gwriteAtInv _ _ _ hwf.1 hs
  have hlt := hada u a t v hu hwu hr
  have hsrc := hwv u a t v hu hr
  cases t with
  | zero => simp [gwriteAt] at hs
  | succ k =>
    obtain ⟨s', hs', hsb, _⟩ := hsrc
    rw [hs, Option.some.injEq] at hs'
    subst hs'
    refine ⟨?_, hsb, hsix⟩
    exact gwixLtGmo _ _ _ hwf hsw (gwixPosElem' _ _ (by omega)) (by omega)

/-- THE OWNED-RMW READ under the PTW model: the read half of a walker RMW reads the LAST
entry of a history that covers its source. -/
theorem rmwReadLast (GP : Gptw) (a : Int) (H : List Hent) (u : Geid) (t : Nat) (v : BitVec 8)
    (wl : Geid) (vl : BitVec 8) :
    gwf (gpG GP) → gatomicity (gpG GP) → h5WalkValue GP → h5AdAtomic GP →
    gwalk GP u → glblIs (gpG GP) u lbIsW →
    (∀ p, p ∈ H → gwritesByte (gpG GP) p.1 a p.2) →
    chainWith (gmoLt (gpG GP)) (H.map Prod.fst) →
    H.getLast? = some (wl, vl) → gmoLt (gpG GP) wl u →
    greadsByte (gpG GP) u a t v →
    (∀ s, gwriteAt (gpG GP) t = some s → s ∈ H.map Prod.fst) →
    gwriteAt (gpG GP) t = some wl ∧ v = vl := by
  intro hwf hat hwv hada hu hwu hm hch hl hlu hr hcov
  have hlin : (wl, vl) ∈ H := List.mem_of_getLast? hl
  have hwlb : gwritesByte (gpG GP) wl a vl := hm _ hlin
  have hwlw := gwritesByteInGwrites _ _ _ _ hwf hwlb
  have huw : u ∈ gwrites (gpG GP) :=
    gwixPosElem' _ _ (by have := hada u a t v hu hwu hr; omega)
  have hwlu := gmoGwixLt _ _ _ hwf hwlw huw hlu
  have hna := hat u a t v hr hwu wl vl hwlb
  cases t with
  | zero => exact absurd ⟨WeakRvwmoGraph.gwixPos _ _ hwlw, hwlu⟩ hna
  | succ k =>
    have hsrc := hwv u a (k + 1) v hu hr
    obtain ⟨s, hs, hsb, _⟩ := hsrc
    have hsin := hcov s hs
    obtain ⟨hsw, hsix⟩ := gwriteAtInv _ _ _ hwf.1 hs
    by_cases hne : s = wl
    · subst hne
      exact ⟨hs, gwritesByteDet _ _ _ _ _ hsb hwlb⟩
    · exfalso
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hsin
      have hlast : (H.map Prod.fst)[(H.map Prod.fst).length - 1]? = some wl := by
        rw [← List.getLast?_eq_getElem?, List.getLast?_map, hl]
        rfl
      have hilt : i < (H.map Prod.fst).length - 1 := by
        have := lookup_lt_Some hi
        by_cases heq : i = (H.map Prod.fst).length - 1
        · rw [heq, hlast, Option.some.injEq] at hi
          exact absurd hi.symm hne
        · omega
      have hsl := chainWithGmo _ (gmoLt (gpG GP)) _ _ _ _ _ (fun _ _ h => h) hch hi hlast hilt
      have hsl' := gmoGwixLt _ _ _ hwf hsw hwlw hsl
      exact hna ⟨by omega, by omega⟩

/-- THE OWNED-RMW THEOREM (pure core): with every byte history covering the RMW's sources,
the read word is the class's (last entries), the written word stays in the class, and the
histories extended by the RMW's bytes are class histories again. -/
theorem pteRmwPure (GP : Gptw) (pa : Int) (P : BitVec 64 → Prop) (Hs : Nat → List Hent)
    (ks ts : Nat → Nat) (u : Geid) (x x' : BitVec 64) :
    gwf (gpG GP) → gatomicity (gpG GP) → h5WalkValue GP → h5AdAtomic GP →
    mixClosed P → gwalk GP u →
    (∀ j, j < 8 → greadsByte (gpG GP) u (accAddr pa j) (ts j) (nthByte (n := 8) x j)) →
    gwritesWord (gpG GP) u pa x' → (P x → P x') →
    (∀ j, j < 8 →
      clsHist (gpG GP) (accAddr pa j) j P (ks j) (Hs j) ∧
      (∀ p, (Hs j).getLast? = some p → gmoLt (gpG GP) p.1 u) ∧
      (∀ s, gwriteAt (gpG GP) (ts j) = some s → s ∈ (Hs j).map Prod.fst)) →
    P x ∧ P x' ∧
    ∀ j, j < 8 → clsHist (gpG GP) (accAddr pa j) j P (ks j)
      (Hs j ++ [(u, nthByte (n := 8) x' j)]) := by
  intro hwf hat hwv hada hmix hu hrx hwx' hcls hall
  have hwu : glblIs (gpG GP) u lbIsW := gwritesByteGlblW _ _ _ _ (hwx' 0 (by omega))
  have hPx : P x := by
    apply hmix
    intro j hj
    obtain ⟨hc, hlast, hcov⟩ := hall j hj
    have ⟨hm, hch, hk, _⟩ := hc
    cases el : (Hs j).getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at el
      rw [el] at hk
      simp at hk
    | some q =>
      obtain ⟨wl, vl⟩ := q
      obtain ⟨_, hv⟩ := rmwReadLast GP _ (Hs j) u (ts j) _ wl vl hwf hat hwv hada hu hwu hm hch
        el (hlast _ el) (hrx j hj) hcov
      rw [hv]
      exact clsHistLastOk _ _ _ _ _ _ _ _ hc el
  have hPx' := hcls hPx
  refine ⟨hPx, hPx', fun j hj => ?_⟩
  obtain ⟨hc, hlast, _⟩ := hall j hj
  exact clsHistSnoc _ _ _ _ _ _ _ _ hc (hwx' j hj) ⟨x', hPx', rfl⟩ hlast

/-- THE EXTRACTION: a history per byte that is a class history from the install on and
COVERS every window write at-or-after the install (what an exclusive token's final history
does: every write needs the full auth) yields the discipline `ptDisc` the plain-read rule
uses. -/
theorem ptDiscOfHist (G : Gexec) (pa : Int) (P : BitVec 64 → Prop) (i : Geid) (w0 : BitVec 64)
    (Hs : Nat → List Hent) (ks : Nat → Nat) :
    gwf G → gwritesWord G i pa w0 →
    (∀ j, j < 8 →
      clsHist G (accAddr pa j) j P (ks j) (Hs j) ∧
      (Hs j)[ks j]? = some (i, nthByte (n := 8) w0 j) ∧
      (∀ w v, gwritesByte G w (accAddr pa j) v → gwix G i ≤ gwix G w →
        w ∈ (Hs j).map Prod.fst)) →
    ptDisc G pa P (gwix G i) := by
  intro hwf hi hall
  have hiw : i ∈ gwrites G := gwritesByteInGwrites G i _ _ hwf (hi 0 (by omega))
  have hipos := WeakRvwmoGraph.gwixPos G i hiw
  refine ⟨?_, fun hz => absurd hz (by omega)⟩
  intro w j v hj hw hle
  obtain ⟨⟨hm, hch, _, ht⟩, hik, hcov⟩ := hall j hj
  have hin := hcov w v hw hle
  obtain ⟨⟨w', b⟩, hp, heq⟩ := List.mem_map.1 hin
  dsimp only at heq
  subst heq
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hp
  have hb : v = b := gwritesByteDet G w' _ v b hw (hm (w', b) (List.mem_of_getElem? hn))
  subst hb
  by_cases hkn : ks j ≤ n
  · exact ht n _ hkn hn
  · exfalso
    have h1 : ((Hs j).map Prod.fst)[n]? = some w' := by rw [List.getElem?_map, hn]; rfl
    have h2 : ((Hs j).map Prod.fst)[ks j]? = some i := by rw [List.getElem?_map, hik]; rfl
    have hwi := chainWithGmo G (gmoLt G) _ n (ks j) w' i (fun _ _ h => h) hch h1 h2 (by omega)
    have := gmoGwixLt G w' i hwf (gwritesByteInGwrites G w' _ _ hwf hw) hiw hwi
    omega

/-! ## 2. The token (Iris) -/

section ptok

variable {GF : BundledGFunctors} [AxlogG GF Hent]

def pteAuths (γ : GName) (pa : Int) (Hs : Nat → List Hent) : IProp GF :=
  [∗list] j ∈ List.range' 0 8, histAuth γ (accAddr pa j) 1 (Hs j)

/-- THE PAGE-TABLE-WORD TOKEN (ACTIVE state). -/
def pteTok (γ : GName) (GP : Gptw) (pa : Int) (P : BitVec 64 → Prop)
    (Hs : Nat → List Hent) (ks : Nat → Nat) : IProp GF :=
  iprop(pteAuths γ pa Hs ∗
    ⌜∀ j, j < 8 → clsHist (gpG GP) (accAddr pa j) j P (ks j) (Hs j)⌝)

/-- PUBLISH (a state change of the protocol). -/
theorem pteTokPublish (γ : GName) (GP : Gptw) (pa : Int) (P : BitVec 64 → Prop)
    (Hs : Nat → List Hent) (ks : Nat → Nat) :
    (∀ j, j < 8 → clsHist (gpG GP) (accAddr pa j) j P (ks j) (Hs j)) →
    pteAuths (GF := GF) γ pa Hs ⊢ pteTok γ GP pa P Hs ks := by
  intro hc
  unfold pteTok
  iintro Ha
  isplitl [Ha]
  · iexact Ha
  · ipureintro
    exact hc

/-- RECLAIM (a state change of the protocol). -/
theorem pteTokReclaim (γ : GName) (GP : Gptw) (pa : Int) (P : BitVec 64 → Prop)
    (Hs : Nat → List Hent) (ks : Nat → Nat) :
    pteTok (GF := GF) γ GP pa P Hs ks ⊢ pteAuths γ pa Hs := by
  unfold pteTok
  iintro ⟨Ha, _⟩
  iexact Ha

/-- `histSnapIn`, keeping the auth (deviation 5). -/
theorem AxPtProt3.histSnapInKeep (γ : GName) (a : Int) (q : Qp) (H H' : List Hent) (w : Geid)
    (hw : w ∈ H'.map Prod.fst) :
    histAuth (GF := GF) γ a q H ∗ histSnap γ a H' ⊢
      ⌜w ∈ H.map Prod.fst⌝ ∗ histAuth γ a q H := by
  refine BI.pure_elim _ (histSnapIn γ a q H H' w hw) (fun hin => ?_)
  iintro ⟨Ha, _⟩
  isplitr [Ha]
  · ipureintro
    exact hin
  · iexact Ha

/-- Coverage snapshots + the auths ⇒ the sources are in the histories. -/
theorem authsIn (γ : GName) (pa : Int) (Hs : Nat → List Hent) (src : Nat → Geid)
    (l : List Nat) :
    ([∗list] j ∈ l, histAuth (GF := GF) γ (accAddr pa j) 1 (Hs j)) ∗
      □ (∀ j, ⌜j ∈ l⌝ -∗ ∃ H', ⌜src j ∈ H'.map Prod.fst⌝ ∗ histSnap γ (accAddr pa j) H') ⊢
    ⌜∀ j, j ∈ l → src j ∈ (Hs j).map Prod.fst⌝ ∗
      [∗list] j ∈ l, histAuth γ (accAddr pa j) 1 (Hs j) := by
  induction l with
  | nil =>
    iintro ⟨Ha, _⟩
    isplitr [Ha]
    · ipureintro
      intro j hj
      cases hj
    · iexact Ha
  | cons j0 l ih =>
    iintro ⟨Ha, #Hc⟩
    icases BigSepL.bigSepL_cons.1 $$ Ha with ⟨Hj0, Ha⟩
    have h0 : j0 ∈ j0 :: l := List.mem_cons_self
    ihave ⟨%H', %hin, #Hsn⟩ := Hc $$ %j0 %h0
    icases AxPtProt3.histSnapInKeep γ (accAddr pa j0) 1 (Hs j0) H' (src j0) hin $$ [Hj0 Hsn]
      with ⟨%hin0, Hj0⟩
    · isplitl [Hj0]
      · iexact Hj0
      · iexact Hsn
    icases ih $$ [Ha] with ⟨%hl, Ha⟩
    · isplitl [Ha]
      · iexact Ha
      · imodintro
        iintro %j %hj
        iapply Hc
        ipureintro
        exact List.mem_cons_of_mem _ hj
    isplitr [Ha Hj0]
    · ipureintro
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hin0
      · exact hl j hj
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hj0]
      · iexact Hj0
      · iexact Ha

theorem authsAppend (γ : GName) (pa : Int) (Hs : Nat → List Hent) (f : Nat → Hent)
    (l : List Nat) :
    ([∗list] j ∈ l, histAuth (GF := GF) γ (accAddr pa j) 1 (Hs j)) ⊢ |==>
      (([∗list] j ∈ l, histAuth γ (accAddr pa j) 1 (Hs j ++ [f j])) ∗
        ([∗list] j ∈ l, histSnap γ (accAddr pa j) (Hs j ++ [f j]))) := by
  induction l with
  | nil =>
    iintro _
    imodintro
    isplitl []
    · iapply BigSepL.bigSepL_nil_intro (P := (emp : IProp GF))
      iempintro
    · iapply BigSepL.bigSepL_nil_intro (P := (emp : IProp GF))
      iempintro
  | cons j0 l ih =>
    iintro Ha
    icases BigSepL.bigSepL_cons.1 $$ Ha with ⟨Hj0, Ha⟩
    imod histAppend γ (accAddr pa j0) (Hs j0) (f j0) $$ Hj0 with Hj0
    ihave #Hs0 := histSnapGet γ (accAddr pa j0) 1 (Hs j0 ++ [f j0]) $$ Hj0
    imod ih $$ Ha with ⟨Ha, Hsn⟩
    imodintro
    isplitl [Hj0 Ha]
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hj0]
      · iexact Hj0
      · iexact Ha
    · iapply BigSepL.bigSepL_cons.2
      isplitr [Hsn]
      · iexact Hs0
      · iexact Hsn

/-- THE OWNED WALKER RMW RULE.  The walker of the hart holding (being lent) the token
performs the Svadu write-back `u`: given the protocol's coverage (a snapshot for every
gmo-earlier window write), its read half is the token's last word — a CLASS word — its
write stays in the class, the token is re-established at the extended histories (to be
re-deposited in `u`'s annotation), and persistent snapshots of the extension are
returned. -/
theorem pteTokRmw (γ : GName) (GP : Gptw) (pa : Int) (P : BitVec 64 → Prop)
    (Hs : Nat → List Hent) (ks ts : Nat → Nat) (u : Geid) (x x' : BitVec 64) :
    gwf (gpG GP) → gatomicity (gpG GP) → h5WalkValue GP → h5AdAtomic GP →
    mixClosed P → gwalk GP u →
    (∀ j, j < 8 → greadsByte (gpG GP) u (accAddr pa j) (ts j) (nthByte (n := 8) x j)) →
    gwritesWord (gpG GP) u pa x' → (P x → P x') →
    (∀ j, j < 8 → ∀ p, (Hs j).getLast? = some p → gmoLt (gpG GP) p.1 u) →
    pteTok (GF := GF) γ GP pa P Hs ks ∗
      □ (∀ j w v', ⌜j < 8⌝ -∗ ⌜gwritesByte (gpG GP) w (accAddr pa j) v'⌝ -∗
          ⌜gmoLt (gpG GP) w u⌝ -∗ ∃ H', ⌜w ∈ H'.map Prod.fst⌝ ∗ histSnap γ (accAddr pa j) H') ⊢
    |==> (⌜P x ∧ P x'⌝ ∗
      pteTok γ GP pa P (fun j => Hs j ++ [(u, nthByte (n := 8) x' j)]) ks ∗
      ([∗list] j ∈ List.range' 0 8,
        histSnap γ (accAddr pa j) (Hs j ++ [(u, nthByte (n := 8) x' j)]))) := by
  intro hwf hat hwv hada hmix hu hrx hwx' hcls hlast
  unfold pteTok pteAuths
  iintro ⟨⟨Ha, %hcl⟩, #Hcov⟩
  have hwu : glblIs (gpG GP) u lbIsW := gwritesByteGlblW _ _ _ _ (hwx' 0 (by omega))
  have hex : ∀ j, j < 8 → ∃ s, gwriteAt (gpG GP) (ts j) = some s := by
    intro j hj
    obtain ⟨hm, _, hk, _⟩ := hcl j hj
    cases el : (Hs j).getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at el
      rw [el] at hk
      simp at hk
    | some q =>
      obtain ⟨wl, vl⟩ := q
      have hwlb : gwritesByte (gpG GP) wl (accAddr pa j) vl := hm _ (List.mem_of_getLast? el)
      have hlu : gmoLt (gpG GP) wl u := hlast j hj _ el
      have hna := hat u _ _ _ (hrx j hj) hwu wl vl hwlb
      have hsrc := hwv u _ _ _ hu (hrx j hj)
      have hwlw := gwritesByteInGwrites _ _ _ _ hwf hwlb
      have huw := gwritesByteInGwrites _ _ _ _ hwf (hwx' 0 (by omega))
      have h1 := gmoGwixLt _ _ _ hwf hwlw huw hlu
      have h2 := WeakRvwmoGraph.gwixPos _ _ hwlw
      revert hna hsrc
      cases ts j with
      | zero => intro hna _; exact absurd ⟨h2, h1⟩ hna
      | succ k =>
        intro _ hsrc
        obtain ⟨s, hs, _⟩ := hsrc
        exact ⟨s, hs⟩
  icases authsIn γ pa Hs (fun j => (gwriteAt (gpG GP) (ts j)).getD u) (List.range' 0 8)
      $$ [Ha] with ⟨%hin, Ha⟩
  · isplitl [Ha]
    · iexact Ha
    · imodintro
      iintro %j %hj
      have hj8 : j < 8 := by
        simp only [List.mem_range'_1] at hj
        omega
      obtain ⟨s, hs⟩ := hex j hj8
      obtain ⟨hsu, hsb, _⟩ := rmwSrc GP _ u (ts j) _ hwf hwv hada hu hwu (hrx j hj8) s hs
      ihave ⟨%H', %hw', #Hsn⟩ := Hcov $$ %j %s %(nthByte (n := 8) x j) %hj8 %hsb %hsu
      iexists H'
      isplitr
      · ipureintro
        simp only [hs, Option.getD_some]
        exact hw'
      · iexact Hsn
  have hall : ∀ j, j < 8 →
      clsHist (gpG GP) (accAddr pa j) j P (ks j) (Hs j) ∧
      (∀ p, (Hs j).getLast? = some p → gmoLt (gpG GP) p.1 u) ∧
      (∀ s, gwriteAt (gpG GP) (ts j) = some s → s ∈ (Hs j).map Prod.fst) := by
    intro j hj
    refine ⟨hcl j hj, hlast j hj, fun s hs => ?_⟩
    have h := hin j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    simp only [hs, Option.getD_some] at h
    exact h
  obtain ⟨hPx, hPx', hnew⟩ :=
    pteRmwPure GP pa P Hs ks ts u x x' hwf hat hwv hada hmix hu hrx hwx' hcls hall
  imod authsAppend γ pa Hs (fun j => (u, nthByte (n := 8) x' j)) (List.range' 0 8) $$ Ha
    with ⟨Ha, Hsn⟩
  imodintro
  isplitr [Ha Hsn]
  · ipureintro
    exact ⟨hPx, hPx'⟩
  isplitl [Ha]
  · isplitl [Ha]
    · iexact Ha
    · ipureintro
      exact hnew
  · iexact Hsn

end ptok

/-! ## 3. NON-VACUITY: the token route on AxPtProt2's `GPad`

Before the write-back each byte's history is the install's entry; the owned-RMW theorem's
premises all hold on the concrete graph, its conclusion extends the histories by the RMW's
bytes, and the EXTRACTION re-derives the discipline `gAdSound` got by the absorption
theorem. -/

def histCoversB (G : Gexec) (a : Int) (l : List Geid) : Bool :=
  (gevents G).all (fun w => !(gwaB G w a) || decide (w ∈ l))

theorem histCoversBSound (G : Gexec) (a : Int) (l : List Geid) :
    histCoversB G a l = true → ∀ w v, gwritesByte G w a v → w ∈ l := by
  intro h w v hw
  unfold histCoversB at h
  have hb := (forallbForallTrue _ _).1 h w (gwritesByteGevents _ _ _ _ hw)
  rw [(gwaBSpec G w a).2 ⟨v, hw⟩] at hb
  simpa using hb

def HsAd0 (j : Nat) : List Hent := [((0, 0), nthByte (n := 8) AxPtProt2.w0 j)]
def HsAd1 (j : Nat) : List Hent := HsAd0 j ++ [((0, 3), nthByte (n := 8) w1 j)]

theorem gadTokenRoute :
    pteVar AxPtProt2.w0 AxPtProt2.w0 ∧ pteVar AxPtProt2.w0 w1 ∧
    (∀ j, j < 8 → clsHist (gpG GPad) (accAddr 0 j) j (pteVar AxPtProt2.w0) 0 (HsAd1 j)) ∧
    ptDisc (gpG GPad) 0 (pteVar AxPtProt2.w0) 1 := by
  obtain ⟨_, ⟨hwf, _, _, hat, _, _⟩, ⟨hwv, _, hada, _, _⟩⟩ := gadModel
  have hi : gwritesWord (gpG GPad) (0, 0) 0 AxPtProt2.w0 :=
    gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hw1 : gwritesWord (gpG GPad) (0, 3) 0 w1 := gwritesWordBSound _ _ _ _ (by decide +kernel)
  have hrx : ∀ j, j < 8 →
      greadsByte (gpG GPad) (0, 3) (accAddr 0 j) 1 (nthByte (n := 8) AxPtProt2.w0 j) := by
    have hb : (List.range 8).all (fun j =>
        grbB (gpG GPad) (0, 3) (accAddr 0 j) 1 (nthByte (n := 8) AxPtProt2.w0 j)) = true := by
      decide +kernel
    intro j hj
    exact (grbBSpec _ _ _ _ _).1 (List.all_eq_true.1 hb j (List.mem_range.2 hj))
  have hw1v : pteVar AxPtProt2.w0 w1 :=
    updatePTEBitsVariant AxPtProt2.w0 AxPtProt2.w0 w1 (.Load .Data) (pteVarRefl AxPtProt2.w0)
      w1Update
  have hpre : ∀ j, j < 8 →
      clsHist (gpG GPad) (accAddr 0 j) j (pteVar AxPtProt2.w0) 0 (HsAd0 j) ∧
      (∀ p, (HsAd0 j).getLast? = some p → gmoLt (gpG GPad) p.1 (0, 3)) ∧
      (∀ s, gwriteAt (gpG GPad) 1 = some s → s ∈ (HsAd0 j).map Prod.fst) := by
    intro j hj
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro p hp
      simp only [HsAd0, List.mem_singleton] at hp
      subst hp
      exact hi j hj
    · intro n w1' w2' _ h2
      simp [HsAd0] at h2
    · simp [HsAd0]
    · intro n p _ hp
      cases n with
      | zero =>
        simp only [HsAd0, List.getElem?_cons_zero, Option.some.injEq] at hp
        subst hp
        exact ⟨AxPtProt2.w0, pteVarRefl _, rfl⟩
      | succ n => simp [HsAd0] at hp
    · intro p hp
      simp only [HsAd0, List.getLast?_singleton, Option.some.injEq] at hp
      subst hp
      have h03 : gmoLt (gpG GPad) (0, 0) (0, 3) := (gmoLtBSpec _ _ _).1 (by decide +kernel)
      exact h03
    · intro s hs
      have hg : gwriteAt (gpG GPad) 1 = some (0, 0) := by decide +kernel
      rw [hg, Option.some.injEq] at hs
      subst hs
      simp [HsAd0]
  obtain ⟨_, _, hcls⟩ := pteRmwPure GPad 0 (pteVar AxPtProt2.w0) HsAd0 (fun _ => 0)
    (fun _ => 1) (0, 3) AxPtProt2.w0 w1 hwf hat hwv hada (mixClosedVar AxPtProt2.w0)
    (by unfold gwalk; decide +kernel) hrx hw1 (fun _ => hw1v) hpre
  refine ⟨pteVarRefl _, hw1v, hcls, ?_⟩
  have hix : gwix (gpG GPad) (0, 0) = 1 := by decide +kernel
  rw [← hix]
  apply ptDiscOfHist _ 0 (pteVar AxPtProt2.w0) (0, 0) AxPtProt2.w0 HsAd1 (fun _ => 0) hwf hi
  intro j hj
  refine ⟨hcls j hj, ?_, ?_⟩
  · simp [HsAd1, HsAd0]
  · intro w v hw _
    have hb : (List.range 8).all (fun j =>
        histCoversB (gpG GPad) (accAddr 0 j) [(0, 0), (0, 3)]) = true := by
      decide +kernel
    have hcov := List.all_eq_true.1 hb j (List.mem_range.2 hj)
    have hin := histCoversBSound _ _ _ hcov w v hw
    simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hin
    rcases hin with rfl | rfl <;> simp [HsAd1, HsAd0]

end Weak
