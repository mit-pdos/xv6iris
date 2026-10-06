/-
Weak: **constraint A, PROTOCOL SIDE — LIVE page tables under RVWMO** (AxSL tier, the
page-table-word protocol).

Rocq: `iris/AxPtProt.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).  PURE (graph level; no Iris).  The RVWMO
twin of the SC tier's `PtTreeAdue` / `KptTree` §5–6 / `KptShare` `tlb_res_pt`; it replaces
the engine's D3 "immutable image, A/D preset".  Companions: `AxPtProt2` (computable
checkers + witnesses), `AxPtProt3` (the Iris token over `AxGhost`).

(P) THE PAGE-TABLE-WORD PROTOCOL.  A PTE word is the 8 bytes at `pa`.  PRIVATE (reachable
from no satp): the kernel hart owns the 8 byte auths and stores to the word as an ordinary
owned write.  ACTIVE (reachable from a satp): the auths + the CLASS invariant form the token
`AxPtProt3.pte_tok` — every history entry from the install on is a `P`-byte, `P = pteVar w0`
(A/D variants of the canonical leaf) for leaves, `Eq p` for pointers.  The walker is lent
the token for one Svadu write-back (an owned RMW whose write is `update_PTE_Bits` of the
read word: `rmwClassOkUpdate`).  Plain walker reads are DEMONIC reads pinned by the
DISCIPLINE `ptDisc` (§4 `walkReadClass`); the discipline is an invariant of walker
write-backs (§5 `ptDiscOfWriters`, the absorption theorem).  Per-byte weak reads mixing
messages still return a class word (`mixClosedVar`, = `WeakVariant.pteVariantMix`).
PUBLISH at kvminithart / userret (csrw satp; sfence.vma); RECLAIM after the switch-away +
sfence.vma (H5'.5).  xv6 never stores to an ACTIVE table, so the kernel premise of
`ptDiscOfWriters` is vacuous on xv6.

(I) TLB-AGREES-WITH-PT.  `tlbAgrees asid T tlbvec := tlbOkPt asid T tlbvec`: every
resident entry is the walk entry of a vpn the current canonical tree maps, stale in A/D at
most.  Established by the sfence flush (`tlbAgreesFlush`), preserved by a fill whose three
demonic walker reads are pinned by the discipline (`tlbAgreesWalkFill`), by the write-back
(`tlbAgreesSetLeaf`) and by canon-preserving changes of `T` (`tlbAgreesCanon`).  Graph
shadow: `agreesAt GP pa r e` (§8), established by `agreesAtOfDisc`.

(H5') THE NEW HARDWARE CLAUSE (riscv.cat has no page-table-walker accesses).
`ptwModel GP := ptwWf ∧ ptwExplicitConsistent ∧ ptwHw`; `ptwExplicitConsistent` is
riscv.cat with every ppo / load-value obligation touching a walker event removed; `ptwHw`
is H5'.1 `h5WalkValue` (walker reads return the image or a VISIBLE write's byte, no
co-maximality), H5'.2 `h5Sfence` (a walk po-after an sfence reads co-at-or-after every
store the fence covers, `sfCovers`), H5'.3 `h5AdAtomic` (the Svadu write-back is one atomic
RMW reading strictly co-before its write), H5'.4 `h5AdBefore` (the write-back is
gmo-before its access), H5'.5 `h5SfenceAd` (walker writes po-before an sfence are
gmo-before the hart's later explicit stores; least spec-grounded, RECLAIM only).  The
§INTERFACE and §CONCERNS paragraphs of the Rocq header (what the certificate must express;
the residuals (1)–(6)) stand unchanged.

O2 (`notes/weak-port-o2-design.md` §1.6): walker reads are `AK_ttw`, a PLAIN read under
O2 (`classify (.AK_ttw ()) = ⟨false,false,false⟩`); this file is graph-level and never
mentions an access kind, so nothing moves.  Fetches (D1) are not graph events of this
file either.

**Deviations from Rocq.**

1. NAMES: lowerCamelCase (map below).  The duplicated Rocq names `src_ok`, `byte_ok`
   (`notes/weak-port-dupnames.json`) are FILE-QUALIFIED: `AxPtProt.srcOk`,
   `AxPtProt.byteOk`.  The record `gptw`/`GPtw` ↦ `structure Gptw` (fields `gpGd`,
   `gpFor`, `gpSf`); `gp_g GP` ↦ `gpG GP` (`= GP.gpGd.gdG`).
2. VOCABULARY: as `Weak/AxGraph.lean` deviation 2 (`Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`,
   `mword 64` ↦ `BitVec 64`, `is_Some o` ↦ `o.isSome = true`, `relation geid` ↦
   `Geid → Geid → Prop`, `eq p` ↦ `Eq p`); `nth_byte x j` ↦ `nthByte (n := 8) x j`;
   `acc_addr` ↦ `accAddr` (`WeakAxiomatic`); `bv_unsigned a` (a 64-bit PTE address) ↦
   `(a.toNat : Int)`; `pte_set_ad` ↦ `MachCSL.pteSetAD`; `pte_canon` ↦
   `PtAdBits.pteCanon` (WeakVariant); `vec (option TLB_Entry) (2 ^ 6)` ↦
   `Vector (Option TLB_Entry) (2 ^ 6)`; `vec_access_dec v (tlb_hash (__id 39) x)` ↦
   `v[tlb_hash 39 x]!`; `vec_update_dec` ↦ `vectorUpdate`; `option_map` ↦ `Option.map`.
3. THE `PtTree.v` / `PtAdBits.v` PIECES §7 needs are not in the Lean tree
   (`MachCSL/PtTree.lean` is an analog with a recursive walk; it has the node type
   `MachCSL.PTree`, which IS Rocq's `ptree`, but not the shallow 3-level `ptree_maps`,
   `ptree_set_leaf`, `ptree_canon`, `tlb_ok_pt`).  They are ported HERE, file-qualified
   `AxPtProt.*`, over `MachCSL.PTree` and `Weak/ExecSC9.lean`'s `CommonWalk`/`PtTree` §1
   vocabulary (`uPteAddr`, `uNextBase`, `pteValid`, `ptePtr`, `pteLeaf`, `ptePbmt0`,
   `uWalkEntry`): `vpn_idx`, `pt_addr2/1/0`, `pte_no_napot`, `ptree_maps`,
   `ptree_maps_det`, `pt_upd_ent`, `pt_upd_kid`, `ptree_set_leaf`, `vpn_idx_inj`,
   `ptree_set_leaf_maps_self/other`, `tlb_cache_of`, `tlb_ok_pt`, `tlb_ok_pt_empty`,
   `tlb_ok_pt_fill`, `tlb_cache_of_set_leaf`, `tlb_ok_pt_set_leaf`, `pte_set_ad_leaf`,
   `pte_set_ad_ptr`, `pte_set_ad_valid_leaf`, `pte_set_ad_no_napot`, `pte_set_ad_pbmt0`,
   `pt_canon_l0/l1`, `ptree_canon`, `ptree_maps_canon(_inv)`, `ptree_canon_set_leaf`,
   `tlb_ok_pt_canon`; from `PtAdBits.v`: `pte_set_ad_refl` (= `MachCSL.pteAD_refl`, used
   directly), `pte_canon_inv`, and the four flag laws as `AxPtProt.pteSetAdFlagV/R/W/X`.
   Rocq's `pt_sub27_*` arithmetic and the `pt_upd_*` projection laws are not needed
   (`bv_decide` / `simp` close them).  Later ports needing them (AxWalk3's
   `tlb_ok_pt_fill`, AxSfence2's `tlb_agrees`) should use these names.
4. Lean-only helpers (file-qualified): `AxPtProt.kidsNode`, `AxPtProt.entsNode` (node
   projections as rewrite rules), `AxPtProt.vecUpdSame`, `AxPtProt.vecUpdNe` (the
   `vec64_access_update` case split, at `2 ^ 6`), `AxPtProt.tlbHashLt`,
   `AxPtProt.pteIsInvalidLeafEq` (the monadic validity check is A/D-blind on a leaf:
   Rocq's in-proof `pte_is_invalid` unfolding, once).
5. `pte_valid` validity stability is proved by rewriting the `SailM` term (`exec`-free),
   which is stronger than Rocq's statement and implies it.
6. The final `Print Assumptions` block has no Lean twin (the lint's axiom check covers it).

**Rocq → Lean name map.**  `gwrites_word` ↦ `gwritesWord`; `greads_word` ↦ `greadsWord`;
`gptw`/`GPtw` ↦ `Gptw`/`Gptw.mk`; `gp_gd`/`gp_for`/`gp_sf` ↦ `Gptw.gpGd`/`gpFor`/`gpSf`;
`gp_g` ↦ `gpG`; `gwalk`; `gsfence`; `src_ok` ↦ `AxPtProt.srcOk`; `lv_at` ↦ `lvAt`;
`gload_value_lv_at` ↦ `gloadValueLvAt`; `ptw_explicit_consistent` ↦
`ptwExplicitConsistent`; `ptw_wf` ↦ `ptwWf`; `h5_walk_value` ↦ `h5WalkValue`; `gob_expl`
↦ `gobExpl`; `gob_expl_cat` ↦ `gobExplCat`; `sf_covers` ↦ `sfCovers`; `h5_sfence` ↦
`h5Sfence`; `h5_ad_atomic` ↦ `h5AdAtomic`; `h5_ad_before` ↦ `h5AdBefore`;
`h5_sfence_ad` ↦ `h5SfenceAd`; `ptw_hw` ↦ `ptwHw`; `ptw_model` ↦ `ptwModel`;
`ptw_explicit_of_cat` ↦ `ptwExplicitOfCat`; `h5_walk_value_of_cat` ↦ `h5WalkValueOfCat`;
`byte_ok` ↦ `AxPtProt.byteOk`; `mix_closed` ↦ `mixClosed`; `pte_var` ↦ `pteVar`;
`pte_var_refl` ↦ `pteVarRefl`; `mix_closed_var` ↦ `mixClosedVar`; `mix_closed_eq` ↦
`mixClosedEq`; `pt_disc` ↦ `ptDisc`; `walk_read_class` ↦ `walkReadClass`;
`walk_after_sfence` ↦ `walkAfterSfence`; `rmw_class_ok` ↦ `rmwClassOk`;
`pt_disc_of_writers` ↦ `ptDiscOfWriters`; `rmw_class_ok_update` ↦ `rmwClassOkUpdate`;
`pte_var_ppn` ↦ `pteVarPpn`; `pte_var_canon` ↦ `pteVarCanon`; `walk_det` ↦ `walkDet`;
`tlb_agrees` ↦ `tlbAgrees`; `tlb_agrees_flush` ↦ `tlbAgreesFlush`; `tlb_agrees_canon` ↦
`tlbAgreesCanon`; `tlb_agrees_set_leaf` ↦ `tlbAgreesSetLeaf`; `tlb_agrees_walk_fill` ↦
`tlbAgreesWalkFill`; `reads_after` ↦ `readsAfter`; `agrees_at` ↦ `agreesAt`;
`reads_after_of_sfence` ↦ `readsAfterOfSfence`; `agrees_at_of_disc` ↦ `agreesAtOfDisc`.
`PtTree.v`/`PtAdBits.v` (deviation 3): `vpn_idx` ↦ `AxPtProt.vpnIdx`; `pt_addr2/1/0` ↦
`AxPtProt.ptAddr2/1/0`; `pte_no_napot` ↦ `AxPtProt.pteNoNapot`; `ptree_maps` ↦
`AxPtProt.ptreeMaps`; `ptree_maps_det` ↦ `AxPtProt.ptreeMapsDet`; `pt_upd_ent`/`pt_upd_kid`
↦ `AxPtProt.ptUpdEnt`/`ptUpdKid`; `ptree_set_leaf` ↦ `AxPtProt.ptreeSetLeaf`;
`vpn_idx_inj` ↦ `AxPtProt.vpnIdxInj`; `ptree_set_leaf_maps_self/other` ↦
`AxPtProt.ptreeSetLeafMapsSelf/Other`; `tlb_cache_of` ↦ `AxPtProt.tlbCacheOf`;
`tlb_ok_pt` ↦ `AxPtProt.tlbOkPt`; `tlb_ok_pt_empty/fill/set_leaf/canon` ↦
`AxPtProt.tlbOkPtEmpty/Fill/SetLeaf/Canon`; `tlb_cache_of_set_leaf` ↦
`AxPtProt.tlbCacheOfSetLeaf`; `pte_set_ad_leaf/ptr/valid_leaf/no_napot/pbmt0` ↦
`AxPtProt.pteSetAdLeaf/Ptr/ValidLeaf/NoNapot/Pbmt0`; `pt_canon_l0/l1` ↦
`AxPtProt.ptCanonL0/L1`; `ptree_canon` ↦ `AxPtProt.ptreeCanon`; `ptree_maps_canon(_inv)` ↦
`AxPtProt.ptreeMapsCanon(Inv)`; `ptree_canon_set_leaf` ↦ `AxPtProt.ptreeCanonSetLeaf`;
`pte_canon_inv` ↦ `AxPtProt.pteCanonInv`; `pte_set_ad_flag_V/R/W/X` ↦
`AxPtProt.pteSetAdFlagV/R/W/X`.

**Dropped:** nothing (every Rocq definition and lemma of `AxPtProt.v` is ported).
-/
import Weak.AxGraphCat
import Weak.WeakVariant
import Weak.ExecSC9
import MachCSL.PteClass

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. PTE words in a graph (8 little-endian bytes at `accAddr pa j`) -/

def gwritesWord (G : Gexec) (e : Geid) (pa : Int) (x : BitVec 64) : Prop :=
  ∀ j : Nat, j < 8 → gwritesByte G e (accAddr pa j) (nthByte (n := 8) x j)

def greadsWord (G : Gexec) (e : Geid) (pa : Int) (x : BitVec 64) : Prop :=
  ∀ j : Nat, j < 8 → ∃ t, greadsByte G e (accAddr pa j) t (nthByte (n := 8) x j)

/-! ## 2. The PTW-extended graph and its model (H5')

`gpFor u = some e`: `u` is an IMPLICIT page-table-walker access (a PTE read, or the Svadu
A/D write-back RMW) performed on behalf of the explicit access (or fetch) `e`.
`gpSf f = true`: `f` is an `sfence.vma` marker — a no-op fence event
`LFence false false false false`. -/

structure Gptw where
  gpGd : Gdexec
  gpFor : Geid → Option Geid
  gpSf : Geid → Bool

def gpG (GP : Gptw) : Gexec := GP.gpGd.gdG
def gwalk (GP : Gptw) (e : Geid) : Prop := (GP.gpFor e).isSome = true
def gsfence (GP : Gptw) (f : Geid) : Prop :=
  GP.gpSf f = true ∧ gxLbl (gpG GP) f = some (LFence false false false false)

/-- The source half of load-value (no co-maximality). -/
def AxPtProt.srcOk (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  match t with
  | 0 => G.gxImg a = some v
  | _ + 1 => ∃ w, gwriteAt G t = some w ∧ gwritesByte G w a v ∧ gvisible G w e

/-- The full per-read load-value clause of `gloadValue`. -/
def lvAt (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  AxPtProt.srcOk G e a t v ∧
  (∀ w' v', gwritesByte G w' a v' → gvisible G w' e → gwix G w' ≤ t)

theorem gloadValueLvAt (G : Gexec) (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    gloadValue G → greadsByte G e a t v → lvAt G e a t v := by
  intro H Hr
  obtain ⟨h1, h2⟩ := H e a t v Hr
  refine ⟨?_, h2⟩
  cases t with
  | zero => exact h1
  | succ k => exact h1

/-- RVWMO for EXPLICIT accesses: riscv.cat with every ppo edge and every load-value
obligation that touches an implicit walker access removed. -/
def ptwExplicitConsistent (GP : Gptw) : Prop :=
  gwf (gpG GP) ∧
  (∀ e1 e2, gppoCat GP.gpGd e1 e2 → GP.gpFor e1 = none →
            GP.gpFor e2 = none → gmoLt (gpG GP) e1 e2) ∧
  (∀ e a t v, GP.gpFor e = none → greadsByte (gpG GP) e a t v →
              lvAt (gpG GP) e a t v) ∧
  gatomicity (gpG GP) ∧
  gdepsWf (gpG GP) GP.gpGd.gdDeps ∧
  gdepsGmo (gpG GP) GP.gpGd.gdDeps

/-- Row shape (certificate obligations). -/
def ptwWf (GP : Gptw) : Prop :=
  (∀ u e, GP.gpFor u = some e → WeakRvwmoGraph.gpo (gpG GP) u e ∧ GP.gpFor e = none) ∧
  (∀ u, gwalk GP u → glblIs (gpG GP) u lbIsW → glblIs (gpG GP) u lbIsR) ∧
  (∀ f, GP.gpSf f = true → gxLbl (gpG GP) f = some (LFence false false false false))

/-- H5'.1 WALK VALUE — a walker read returns, per byte, the image or the byte of SOME
visible write; NO coherence/co-maximality obligation. -/
def h5WalkValue (GP : Gptw) : Prop :=
  ∀ e a t v, gwalk GP e → greadsByte (gpG GP) e a t v → AxPtProt.srcOk (gpG GP) e a t v

/-- riscv.cat's `ob` restricted to EXPLICIT events. -/
def gobExpl (GP : Gptw) : Geid → Geid → Prop :=
  tc (fun x y => gobrCat GP.gpGd x y ∧ GP.gpFor x = none ∧ GP.gpFor y = none)

theorem gobExplCat (GP : Gptw) (x y : Geid) : gobExpl GP x y → gobCat GP.gpGd x y := by
  intro h
  induction h with
  | single h => exact tc_once h.1
  | tail _ h ih => exact tc_r ih h.1

/-- A store `s` is ALREADY VISIBLE to the hart at the fence `f`. -/
def sfCovers (GP : Gptw) (s f : Geid) : Prop :=
  WeakRvwmoGraph.gpo (gpG GP) s f ∨ ∃ e, WeakRvwmoGraph.gpo (gpG GP) e f ∧ gobExpl GP s e

/-- H5'.2 SFENCE.VMA: every walker read po-after an sfence reads, at each byte, a write
co-at-or-after every store the sfence covers. -/
def h5Sfence (GP : Gptw) : Prop :=
  ∀ f r a t v s v', gsfence GP f → gwalk GP r → WeakRvwmoGraph.gpo (gpG GP) f r →
    greadsByte (gpG GP) r a t v → gwritesByte (gpG GP) s a v' →
    sfCovers GP s f → gwix (gpG GP) s ≤ t

/-- H5'.3 A/D ATOMICITY: the write-back's read half reads strictly co-before its write. -/
def h5AdAtomic (GP : Gptw) : Prop :=
  ∀ u a t v, gwalk GP u → glblIs (gpG GP) u lbIsW →
    greadsByte (gpG GP) u a t v → t < gwix (gpG GP) u

/-- H5'.4 A/D BEFORE THE ACCESS. -/
def h5AdBefore (GP : Gptw) : Prop :=
  ∀ u e, GP.gpFor u = some e → glblIs (gpG GP) u lbIsW → gmoLt (gpG GP) u e

/-- H5'.5 SFENCE ORDERS PRIOR WALKER WRITES before the hart's later explicit stores. -/
def h5SfenceAd (GP : Gptw) : Prop :=
  ∀ u f s, gsfence GP f → gwalk GP u → glblIs (gpG GP) u lbIsW →
    WeakRvwmoGraph.gpo (gpG GP) u f → WeakRvwmoGraph.gpo (gpG GP) f s → GP.gpFor s = none →
    glblIs (gpG GP) s lbIsW → gmoLt (gpG GP) u s

def ptwHw (GP : Gptw) : Prop :=
  h5WalkValue GP ∧ h5Sfence GP ∧ h5AdAtomic GP ∧ h5AdBefore GP ∧ h5SfenceAd GP

def ptwModel (GP : Gptw) : Prop :=
  ptwWf GP ∧ ptwExplicitConsistent GP ∧ ptwHw GP

/-- The full cat model implies the explicit part ... -/
theorem ptwExplicitOfCat (GP : Gptw) :
    rvwmoCatConsistent GP.gpGd → ptwExplicitConsistent GP := by
  rintro ⟨hwf, hppo, hlv, hat, hdw, hdg⟩
  exact ⟨hwf, fun e1 e2 hp _ _ => hppo e1 e2 hp,
    fun e a t v _ hr => gloadValueLvAt _ e a t v hlv hr, hat, hdw, hdg⟩

/-- ... and H5'.1. -/
theorem h5WalkValueOfCat (GP : Gptw) : rvwmoCatConsistent GP.gpGd → h5WalkValue GP := by
  rintro ⟨_, _, hlv, _⟩
  intro e a t v _ hr
  exact (gloadValueLvAt _ e a t v hlv hr).1

/-! ## 3. Word classes, byte mixing -/

def AxPtProt.byteOk (P : BitVec 64 → Prop) (j : Nat) (b : BitVec 8) : Prop :=
  ∃ x, P x ∧ nthByte (n := 8) x j = b

/-- A class is MIX-CLOSED when a word assembled byte-by-byte from members is a member. -/
def mixClosed (P : BitVec 64 → Prop) : Prop :=
  ∀ w : BitVec 64, (∀ j, j < 8 → AxPtProt.byteOk P j (nthByte (n := 8) w j)) → P w

/-- The LEAF class: the A/D variants of the canonical word. -/
def pteVar (w0 x : BitVec 64) : Prop := ∃ a d : BitVec 1, x = pteSetAD w0 a d

theorem pteVarRefl (w0 : BitVec 64) : pteVar w0 w0 := pteAD_refl w0

theorem mixClosedVar (w0 : BitVec 64) : mixClosed (pteVar w0) := by
  intro w hb
  apply pteVariantMix w0 w
  intro j hj
  obtain ⟨x, ⟨a, d, rfl⟩, hx⟩ := hb j hj
  exact ⟨a, d, hx.symm⟩

/-- The POINTER class: exactly one word. -/
theorem mixClosedEq (p : BitVec 64) : mixClosed (Eq p) := by
  intro w hb
  apply bv_eq_of_bytes (n := 8)
  intro j hj
  obtain ⟨x, rfl, hx⟩ := hb j hj
  exact hx

/-! ## 4. THE PAGE-TABLE-WORD DISCIPLINE and the WALK-READ PINNING LEMMA -/

def ptDisc (G : Gexec) (pa : Int) (P : BitVec 64 → Prop) (T0 : Nat) : Prop :=
  (∀ w j v, j < 8 → gwritesByte G w (accAddr pa j) v →
            T0 ≤ gwix G w → AxPtProt.byteOk P j v) ∧
  (T0 = 0 → ∀ j v, j < 8 → G.gxImg (accAddr pa j) = some v →
            AxPtProt.byteOk P j v)

/-- THE PINNING LEMMA: a walker read whose every byte reads at-or-after the install
returns a `P`-word. -/
theorem walkReadClass (GP : Gptw) (pa : Int) (P : BitVec 64 → Prop) (T0 : Nat) (r : Geid)
    (x : BitVec 64) :
    gwf (gpG GP) → h5WalkValue GP → ptDisc (gpG GP) pa P T0 → mixClosed P →
    gwalk GP r →
    (∀ j, j < 8 → ∃ t, greadsByte (gpG GP) r (accAddr pa j) t (nthByte (n := 8) x j) ∧
                         T0 ≤ t) →
    P x := by
  rintro hwf hwv ⟨hd, himg⟩ hmix hr hrd
  apply hmix
  intro j hj
  obtain ⟨t, hrb, ht⟩ := hrd j hj
  have hsrc := hwv _ _ _ _ hr hrb
  cases t with
  | zero =>
    simp only [AxPtProt.srcOk] at hsrc
    exact himg (by omega) j _ hj hsrc
  | succ k =>
    simp only [AxPtProt.srcOk] at hsrc
    obtain ⟨w, hw, hwb, _⟩ := hsrc
    obtain ⟨_, hix⟩ := gwriteAtInv _ _ _ hwf.1 hw
    exact hd w j _ hj hwb (by omega)

/-- ... and H5'.2 supplies the "at-or-after the install" premise for every walk po-after
an sfence that covers the install. -/
theorem walkAfterSfence (GP : Gptw) (f r i : Geid) (pa : Int) (w0 : BitVec 64)
    (P : BitVec 64 → Prop) (x : BitVec 64) :
    gwf (gpG GP) → h5WalkValue GP → h5Sfence GP →
    gsfence GP f → gwalk GP r → WeakRvwmoGraph.gpo (gpG GP) f r →
    gwritesWord (gpG GP) i pa w0 → sfCovers GP i f →
    ptDisc (gpG GP) pa P (gwix (gpG GP) i) → mixClosed P →
    greadsWord (gpG GP) r pa x → P x := by
  intro hwf hwv hsf hf hr hfr hi hcov hd hmix hx
  refine walkReadClass GP pa P (gwix (gpG GP) i) r x hwf hwv hd hmix hr ?_
  intro j hj
  obtain ⟨t, ht⟩ := hx j hj
  exact ⟨t, ht, hsf f r _ t _ i _ hf hr hfr ht (hi j hj) hcov⟩

/-! ## 5. THE ABSORPTION THEOREM: the discipline is an INVARIANT of walker A/D
write-backs -/

def rmwClassOk (G : Gexec) (u : Geid) (pa : Int) (P : BitVec 64 → Prop) : Prop :=
  ∃ x x' : BitVec 64, greadsWord G u pa x ∧ gwritesWord G u pa x' ∧ (P x → P x')

theorem ptDiscOfWriters (GP : Gptw) (pa : Int) (P : BitVec 64 → Prop) (i : Geid)
    (w0 : BitVec 64) :
    gwf (gpG GP) → h5WalkValue GP → gatomicity (gpG GP) → h5AdAtomic GP →
    mixClosed P →
    gwritesWord (gpG GP) i pa w0 → P w0 →
    (∀ w j v, j < 8 → GP.gpFor w = none →
       gwritesByte (gpG GP) w (accAddr pa j) v →
       gwix (gpG GP) i < gwix (gpG GP) w → AxPtProt.byteOk P j v) →
    (∀ u j v, j < 8 → gwalk GP u → gwritesByte (gpG GP) u (accAddr pa j) v →
       rmwClassOk (gpG GP) u pa P) →
    ptDisc (gpG GP) pa P (gwix (gpG GP) i) := by
  intro hwf hwv hat hada hmix hi hP0 hker hrmw
  have hnd := hwf.1
  have hiw : i ∈ gwrites (gpG GP) := gwritesByteInGwrites _ i _ _ hwf (hi 0 (by omega))
  have hipos := WeakRvwmoGraph.gwixPos _ i hiw
  refine ⟨?_, fun hz => absurd hz (by omega)⟩
  have hind : ∀ n w j v, gwix (gpG GP) w = n → j < 8 →
      gwritesByte (gpG GP) w (accAddr pa j) v → gwix (gpG GP) i ≤ n →
      AxPtProt.byteOk P j v := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
    intro w j v hn hj hwb hle
    have hww := gwritesByteInGwrites _ w _ _ hwf hwb
    by_cases hne : w = i
    · rw [hne] at hwb
      have := gwritesByteDet _ i _ _ _ hwb (hi j hj)
      rw [this]
      exact ⟨w0, hP0, rfl⟩
    have hlt : gwix (gpG GP) i < gwix (gpG GP) w := by
      rcases Nat.lt_or_ge (gwix (gpG GP) i) (gwix (gpG GP) w) with h | h
      · exact h
      · exfalso
        have heq : gwix (gpG GP) i = gwix (gpG GP) w := by omega
        exact hne (gwixInj _ i w hnd hiw hww heq).symm
    cases hfor : GP.gpFor w with
    | none => exact hker w j v hj hfor hwb hlt
    | some e =>
      have hwk : gwalk GP w := by simp [gwalk, hfor]
      obtain ⟨x, x', hrx, hwx', hcls⟩ := hrmw w j v hj hwk hwb
      have hPx : P x := by
        apply hmix
        intro j' hj'
        obtain ⟨t, hrt⟩ := hrx j' hj'
        have hisw := gwritesByteGlblW _ w _ _ hwb
        have htw := hada w _ t _ hwk hisw hrt
        have hna := hat w _ t _ hrt hisw i _ (hi j' hj')
        have hti : gwix (gpG GP) i ≤ t := by
          rcases Nat.lt_or_ge t (gwix (gpG GP) i) with h | h
          · exact absurd ⟨h, hlt⟩ hna
          · exact h
        have hsrc := hwv w _ t _ hwk hrt
        cases t with
        | zero => omega
        | succ k =>
          simp only [AxPtProt.srcOk] at hsrc
          obtain ⟨s, hs, hsb, _⟩ := hsrc
          obtain ⟨_, hsix⟩ := gwriteAtInv _ _ s hnd hs
          exact ih (k + 1) (by omega) s j' _ hsix hj' hsb hti
      have := gwritesByteDet _ w _ _ _ hwb (hwx' j hj)
      rw [this]
      exact ⟨x', hcls hPx, rfl⟩
  intro w j v hj hwb hle
  exact hind _ w j v rfl hj hwb hle

/-- The Svadu write-back is class-preserving for the LEAF class. -/
theorem rmwClassOkUpdate (G : Gexec) (u : Geid) (pa : Int) (w0 x x' : BitVec 64)
    (acc : MemoryAccessType mem_payload) :
    greadsWord G u pa x → gwritesWord G u pa x' →
    update_PTE_Bits x acc = some x' →
    rmwClassOk G u pa (pteVar w0) :=
  fun hr hw hup => ⟨x, x', hr, hw, fun hx => updatePTEBitsVariant w0 x x' acc hx hup⟩

/-! ## 6. Translation invariance and WALK DETERMINISM -/

theorem pteVarPpn (w0 x : BitVec 64) : pteVar w0 x → PPN_of_PTE x = PPN_of_PTE w0 := by
  rintro ⟨a, d, rfl⟩
  exact ppn_of_pteSetAD w0 a d

theorem pteVarCanon (w0 x : BitVec 64) :
    pteVar w0 x → PtAdBits.pteCanon x = PtAdBits.pteCanon w0 := by
  rintro ⟨a, d, rfl⟩
  exact PtAdBits.pteCanonSetAd w0 a d

/-- WALK DETERMINISM under the invariant. -/
theorem walkDet (GP : Gptw) (pa : Int) (w0 : BitVec 64) (T0 : Nat) (r1 r2 : Geid)
    (x1 x2 : BitVec 64) :
    gwf (gpG GP) → h5WalkValue GP → ptDisc (gpG GP) pa (pteVar w0) T0 →
    gwalk GP r1 → gwalk GP r2 →
    (∀ j, j < 8 → ∃ t, greadsByte (gpG GP) r1 (accAddr pa j) t (nthByte (n := 8) x1 j) ∧
      T0 ≤ t) →
    (∀ j, j < 8 → ∃ t, greadsByte (gpG GP) r2 (accAddr pa j) t (nthByte (n := 8) x2 j) ∧
      T0 ≤ t) →
    PtAdBits.pteCanon x1 = PtAdBits.pteCanon x2 ∧ PPN_of_PTE x1 = PPN_of_PTE x2 := by
  intro hwf hwv hd h1 h2 hr1 hr2
  have v1 := walkReadClass GP pa _ T0 r1 x1 hwf hwv hd (mixClosedVar w0) h1 hr1
  have v2 := walkReadClass GP pa _ T0 r2 x2 hwf hwv hd (mixClosedVar w0) h2 hr2
  exact ⟨by rw [pteVarCanon _ _ v1, pteVarCanon _ _ v2],
    by rw [pteVarPpn _ _ v1, pteVarPpn _ _ v2]⟩

/-! ## 7a. The `PtTree.v` / `PtAdBits.v` pieces (deviation 3) -/

/-- Rocq `PtTree.vpn_idx`. -/
def AxPtProt.vpnIdx (lvl : Nat) (vpn : BitVec 27) : BitVec 9 :=
  match lvl with
  | 2 => Sail.BitVec.extractLsb vpn 26 18
  | 1 => Sail.BitVec.extractLsb vpn 17 9
  | _ => Sail.BitVec.extractLsb vpn 8 0

/-- Rocq `PtTree.pt_addr2/1/0`: the three slot addresses a walk of `vpn` reads. -/
def AxPtProt.ptAddr2 (t : PTree) (vpn : BitVec 27) : BitVec 64 :=
  uPteAddr t.base (AxPtProt.vpnIdx 2 vpn)
def AxPtProt.ptAddr1 (p2 : BitVec 64) (vpn : BitVec 27) : BitVec 64 :=
  uPteAddr (uNextBase p2) (AxPtProt.vpnIdx 1 vpn)
def AxPtProt.ptAddr0 (p1 : BitVec 64) (vpn : BitVec 27) : BitVec 64 :=
  uPteAddr (uNextBase p1) (AxPtProt.vpnIdx 0 vpn)

/-- Rocq `PtTree.pte_no_napot`. -/
def AxPtProt.pteNoNapot (w : BitVec 64) : Prop :=
  (_get_PTE_Ext_N (ext_bits_of_PTE w) == 1#1) = false

/-- Rocq `PtTree.ptree_maps`: `t` 4K-maps `vpn` through pointer words `p2`, `p1` to the
leaf word `p0` (shallow 3-level path). -/
def AxPtProt.ptreeMaps (t : PTree) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64) : Prop :=
  ∃ c1 c0,
    t.kids (AxPtProt.vpnIdx 2 vpn) = some c1 ∧
    c1.kids (AxPtProt.vpnIdx 1 vpn) = some c0 ∧
    t.ents (AxPtProt.vpnIdx 2 vpn) = p2 ∧
    c1.ents (AxPtProt.vpnIdx 1 vpn) = p1 ∧
    c0.ents (AxPtProt.vpnIdx 0 vpn) = p0 ∧
    uNextBase p2 = c1.base ∧
    uNextBase p1 = c0.base ∧
    pteValid p2 ∧ ptePtr p2 ∧
    pteValid p1 ∧ ptePtr p1 ∧
    pteValid p0 ∧ pteLeaf p0 ∧ AxPtProt.pteNoNapot p0 ∧ ptePbmt0 p0

theorem AxPtProt.ptreeMapsDet (t : PTree) (vpn : BitVec 27) (p2 p1 p0 q2 q1 q0 : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 → AxPtProt.ptreeMaps t vpn q2 q1 q0 →
    p2 = q2 ∧ p1 = q1 ∧ p0 = q0 := by
  rintro ⟨c1, c0, hk2, hk1, he2, he1, he0, -⟩ ⟨d1, d0, hk2', hk1', he2', he1', he0', -⟩
  rw [hk2] at hk2'
  have hc1 : c1 = d1 := Option.some.inj hk2'
  rw [← hc1] at hk1' he1'
  rw [hk1] at hk1'
  have hc0 : c0 = d0 := Option.some.inj hk1'
  rw [← hc0] at he0'
  exact ⟨he2.symm.trans he2', he1.symm.trans he1', he0.symm.trans he0'⟩

/-- Lean-only (deviation 4): the node projections, as rewrite rules. -/
theorem AxPtProt.kidsNode (b : BitVec 44) (e : BitVec 9 → BitVec 64) 
    (k : BitVec 9 → Option PTree) : (PTree.node b e k).kids = k := rfl
theorem AxPtProt.entsNode (b : BitVec 44) (e : BitVec 9 → BitVec 64) 
    (k : BitVec 9 → Option PTree) : (PTree.node b e k).ents = e := rfl

/-- Rocq `PtTree.pt_upd_ent` / `pt_upd_kid`. -/
def AxPtProt.ptUpdEnt (t : PTree) (i : BitVec 9) (w : BitVec 64) : PTree :=
  .node t.base (fun j => if j = i then w else t.ents j) t.kids
def AxPtProt.ptUpdKid (t : PTree) (i : BitVec 9) (c : Option PTree) : PTree :=
  .node t.base t.ents (fun j => if j = i then c else t.kids j)

/-- Rocq `PtTree.ptree_set_leaf`: replace the LEAF word on `vpn`'s path. -/
def AxPtProt.ptreeSetLeaf (t : PTree) (vpn : BitVec 27) (w : BitVec 64) : PTree :=
  match t.kids (AxPtProt.vpnIdx 2 vpn) with
  | some c1 =>
      match c1.kids (AxPtProt.vpnIdx 1 vpn) with
      | some c0 =>
          AxPtProt.ptUpdKid t (AxPtProt.vpnIdx 2 vpn)
            (some (AxPtProt.ptUpdKid c1 (AxPtProt.vpnIdx 1 vpn)
                     (some (AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w))))
      | none => t
  | none => t

/-- The three 9-bit indices determine the vpn. -/
theorem AxPtProt.vpnIdxInj (x y : BitVec 27) :
    AxPtProt.vpnIdx 2 x = AxPtProt.vpnIdx 2 y → AxPtProt.vpnIdx 1 x = AxPtProt.vpnIdx 1 y →
    AxPtProt.vpnIdx 0 x = AxPtProt.vpnIdx 0 y → x = y := by
  intro h2 h1 h0
  simp only [AxPtProt.vpnIdx, Sail.BitVec.extractLsb] at h2 h1 h0
  bv_decide

theorem AxPtProt.ptreeSetLeafMapsSelf (t : PTree) (vpn : BitVec 27) (p2 p1 p0 w : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    pteValid w → pteLeaf w → AxPtProt.pteNoNapot w → ptePbmt0 w →
    AxPtProt.ptreeMaps (AxPtProt.ptreeSetLeaf t vpn w) vpn p2 p1 w := by
  rintro ⟨c1, c0, hk2, hk1, he2, he1, -, hb1, hb0, hv2, hn2, hv1, hn1, -⟩ hv hl hnap hpb
  simp only [AxPtProt.ptreeSetLeaf, hk2, hk1]
  unfold AxPtProt.ptreeMaps
  refine ⟨AxPtProt.ptUpdKid c1 (AxPtProt.vpnIdx 1 vpn)
      (some (AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w)),
    AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w, ?_, ?_, he2, he1, ?_, hb1, hb0,
    hv2, hn2, hv1, hn1, hv, hl, hnap, hpb⟩ <;>
    simp [AxPtProt.ptUpdKid, AxPtProt.ptUpdEnt]

theorem AxPtProt.ptreeSetLeafMapsOther (t : PTree) (vpn vpn' : BitVec 27)
    (q2 q1 q0 w : BitVec 64) :
    vpn' ≠ vpn →
    AxPtProt.ptreeMaps t vpn' q2 q1 q0 →
    AxPtProt.ptreeMaps (AxPtProt.ptreeSetLeaf t vpn w) vpn' q2 q1 q0 := by
  rintro hne ⟨d1, d0, hk2, hk1, he2, he1, he0, hb1, hb0, hrest⟩
  cases hc2 : t.kids (AxPtProt.vpnIdx 2 vpn) with
  | none =>
    simp only [AxPtProt.ptreeSetLeaf, hc2]
    exact ⟨d1, d0, hk2, hk1, he2, he1, he0, hb1, hb0, hrest⟩
  | some c1 =>
    cases hc1 : c1.kids (AxPtProt.vpnIdx 1 vpn) with
    | none =>
      simp only [AxPtProt.ptreeSetLeaf, hc2, hc1]
      exact ⟨d1, d0, hk2, hk1, he2, he1, he0, hb1, hb0, hrest⟩
    | some c0 =>
      simp only [AxPtProt.ptreeSetLeaf, hc2, hc1]
      unfold AxPtProt.ptreeMaps
      by_cases ei2 : AxPtProt.vpnIdx 2 vpn' = AxPtProt.vpnIdx 2 vpn
      · -- same root slot: vpn' routes through the rebuilt c1
        have hd1 : d1 = c1 := by
          rw [ei2, hc2] at hk2
          exact (Option.some.inj hk2).symm
        rw [hd1] at hk1 hb1 he1
        by_cases ei1 : AxPtProt.vpnIdx 1 vpn' = AxPtProt.vpnIdx 1 vpn
        · -- same root and mid slot: the leaf index must differ
          have hd0 : d0 = c0 := by
            rw [ei1, hc1] at hk1
            exact (Option.some.inj hk1).symm
          rw [hd0] at he0 hb0
          have ei0 : AxPtProt.vpnIdx 0 vpn' ≠ AxPtProt.vpnIdx 0 vpn :=
            fun h => hne (AxPtProt.vpnIdxInj _ _ ei2 ei1 h)
          refine ⟨AxPtProt.ptUpdKid c1 (AxPtProt.vpnIdx 1 vpn)
              (some (AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w)),
            AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w, ?_, ?_, he2, he1, ?_, hb1, hb0,
            hrest⟩
          · simp [AxPtProt.ptUpdKid, ei2]
          · simp [AxPtProt.ptUpdKid, ei1]
          · simp [AxPtProt.ptUpdEnt, ei0, he0]
        · refine ⟨AxPtProt.ptUpdKid c1 (AxPtProt.vpnIdx 1 vpn)
              (some (AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w)), d0, ?_, ?_, he2, he1,
            he0, hb1, hb0, hrest⟩
          · simp [AxPtProt.ptUpdKid, ei2]
          · simp [AxPtProt.ptUpdKid, ei1, hk1]
      · -- different root slot: everything below is the old subtree
        refine ⟨d1, d0, ?_, hk1, he2, he1, he0, hb1, hb0, hrest⟩
        simp [AxPtProt.ptUpdKid, ei2, hk2]

/-- Lean-only (deviation 4): the hash is in range. -/
theorem AxPtProt.tlbHashLt (vpn : BitVec 27) : tlb_hash 39 vpn < 2 ^ 6 := by
  rw [tlbHash_eq]; exact tlbHash_lt vpn

/-- Lean-only (deviation 4): `vectorUpdate` at the updated slot ... -/
theorem AxPtProt.vecUpdSame {α : Type} [Inhabited α] (v : Vector α (2 ^ 6)) (n : Nat) (a : α)
    (h : n < 2 ^ 6) : (vectorUpdate v n a)[n]! = a := by
  simp [vectorUpdate, getElem!_pos, h]

/-- ... and elsewhere. -/
theorem AxPtProt.vecUpdNe {α : Type} [Inhabited α] (v : Vector α (2 ^ 6)) (n j : Nat) (a : α)
    (h : j ≠ n) : (vectorUpdate v n a)[j]! = v[j]! := by
  by_cases hj : j < 2 ^ 6
  · simp [vectorUpdate, getElem!_pos, hj]
    grind
  · simp [vectorUpdate, getElem!_neg, hj]

/-- Rocq `PtTree.tlb_cache_of`: `ent` is a legal resident of slot `tlb_hash vpn'` w.r.t.
`t`, modulo A/D staleness of the leaf. -/
def AxPtProt.tlbCacheOf (asid : BitVec 16) (t : PTree) (vpn' : BitVec 27) (ent : TLB_Entry) :
    Prop :=
  ∃ (vpn : BitVec 27) (p2 p1 p0 : BitVec 64) (a d : BitVec 1),
    AxPtProt.ptreeMaps t vpn p2 p1 p0 ∧
    tlb_hash 39 vpn = tlb_hash 39 vpn' ∧
    ent = uWalkEntry vpn p2 p1 (pteSetAD p0 a d) asid

/-- Rocq `PtTree.tlb_ok_pt`. -/
def AxPtProt.tlbOkPt (asid : BitVec 16) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) : Prop :=
  ∀ (vpn' : BitVec 27) (ent : TLB_Entry),
    tlbvec[tlb_hash 39 vpn']! = some ent → AxPtProt.tlbCacheOf asid t vpn' ent

theorem AxPtProt.tlbOkPtEmpty (asid : BitVec 16) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) :
    (∀ vpn', tlbvec[tlb_hash 39 vpn']! = none) → AxPtProt.tlbOkPt asid t tlbvec := by
  intro hnone vpn' ent hget
  rw [hnone] at hget
  cases hget

theorem AxPtProt.tlbOkPtFill (asid : BitVec 16) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) (p2 p1 p0 q0 : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    (∃ a d : BitVec 1, q0 = pteSetAD p0 a d) →
    AxPtProt.tlbOkPt asid t tlbvec →
    AxPtProt.tlbOkPt asid t (vectorUpdate tlbvec (tlb_hash 39 vpn)
                      (some (uWalkEntry vpn p2 p1 q0 asid))) := by
  rintro hmaps ⟨a, d, hq⟩ hok vpn' ent hget
  by_cases hh : tlb_hash 39 vpn' = tlb_hash 39 vpn
  · rw [hh, AxPtProt.vecUpdSame _ _ _ (AxPtProt.tlbHashLt vpn)] at hget
    have hent := Option.some.inj hget
    exact ⟨vpn, p2, p1, p0, a, d, hmaps, hh.symm, by rw [← hent, hq]⟩
  · rw [AxPtProt.vecUpdNe _ _ _ _ hh] at hget
    exact hok vpn' ent hget

/-- Rocq `PtAdBits.pte_set_ad_flag_V/R/W/X`: the walk's classifier bits are A/D-blind. -/
theorem AxPtProt.pteSetAdFlagV (w : BitVec 64) (a d : BitVec 1) :
    _get_PTE_Flags_V (Mk_PTE_Flags (Sail.BitVec.extractLsb (pteSetAD w a d) 7 0)) =
      _get_PTE_Flags_V (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) := by
  simp only [pteSetAD, Mk_PTE_Flags, _get_PTE_Flags_V, Sail.BitVec.extractLsb,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.extractLsb,
    _update_PTE_Flags_A, _update_PTE_Flags_D]
  bv_decide

theorem AxPtProt.pteSetAdFlagR (w : BitVec 64) (a d : BitVec 1) :
    _get_PTE_Flags_R (Mk_PTE_Flags (Sail.BitVec.extractLsb (pteSetAD w a d) 7 0)) =
      _get_PTE_Flags_R (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) := by
  simp only [pteSetAD, Mk_PTE_Flags, _get_PTE_Flags_R, Sail.BitVec.extractLsb,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.extractLsb,
    _update_PTE_Flags_A, _update_PTE_Flags_D]
  bv_decide

theorem AxPtProt.pteSetAdFlagW (w : BitVec 64) (a d : BitVec 1) :
    _get_PTE_Flags_W (Mk_PTE_Flags (Sail.BitVec.extractLsb (pteSetAD w a d) 7 0)) =
      _get_PTE_Flags_W (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) := by
  simp only [pteSetAD, Mk_PTE_Flags, _get_PTE_Flags_W, Sail.BitVec.extractLsb,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.extractLsb,
    _update_PTE_Flags_A, _update_PTE_Flags_D]
  bv_decide

theorem AxPtProt.pteSetAdFlagX (w : BitVec 64) (a d : BitVec 1) :
    _get_PTE_Flags_X (Mk_PTE_Flags (Sail.BitVec.extractLsb (pteSetAD w a d) 7 0)) =
      _get_PTE_Flags_X (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) := by
  simp only [pteSetAD, Mk_PTE_Flags, _get_PTE_Flags_X, Sail.BitVec.extractLsb,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.extractLsb,
    _update_PTE_Flags_A, _update_PTE_Flags_D]
  bv_decide

theorem AxPtProt.pteSetAdLeaf (w : BitVec 64) (a d : BitVec 1) :
    pteLeaf (pteSetAD w a d) ↔ pteLeaf w := by
  unfold pteLeaf pte_is_non_leaf
  rw [AxPtProt.pteSetAdFlagX, AxPtProt.pteSetAdFlagW, AxPtProt.pteSetAdFlagR]

theorem AxPtProt.pteSetAdPtr (w : BitVec 64) (a d : BitVec 1) :
    ptePtr (pteSetAD w a d) ↔ ptePtr w := by
  unfold ptePtr pte_is_non_leaf
  rw [AxPtProt.pteSetAdFlagX, AxPtProt.pteSetAdFlagW, AxPtProt.pteSetAdFlagR]

/-- Lean-only (deviation 4): on a LEAF the model's validity check is A/D-blind (the
reserved-bit clause `pte_is_non_leaf && (A || D || …)` is dead). -/
theorem AxPtProt.pteIsInvalidLeafEq (w : BitVec 64) (a d : BitVec 1) :
    pteLeaf w →
    pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb (pteSetAD w a d) 7 0))
        (ext_bits_of_PTE (pteSetAD w a d)) =
      pte_is_invalid (Mk_PTE_Flags (Sail.BitVec.extractLsb w 7 0)) (ext_bits_of_PTE w) := by
  intro hl
  have hl' : pteLeaf (pteSetAD w a d) := (AxPtProt.pteSetAdLeaf w a d).2 hl
  unfold pteLeaf at hl hl'
  rw [ext_of_pteSetAD]
  unfold pte_is_invalid
  rw [AxPtProt.pteSetAdFlagV, AxPtProt.pteSetAdFlagR, AxPtProt.pteSetAdFlagW,
    AxPtProt.pteSetAdFlagX, hl, hl']
  simp only [Bool.false_and]

/-- VALIDITY IS A/D-STABLE ONLY FOR A LEAF. -/
theorem AxPtProt.pteSetAdValidLeaf (w : BitVec 64) (a d : BitVec 1) :
    pteLeaf w → (pteValid (pteSetAD w a d) ↔ pteValid w) := by
  intro hl
  unfold pteValid
  rw [AxPtProt.pteIsInvalidLeafEq w a d hl]

theorem AxPtProt.pteSetAdNoNapot (w : BitVec 64) (a d : BitVec 1) :
    AxPtProt.pteNoNapot (pteSetAD w a d) ↔ AxPtProt.pteNoNapot w := by
  unfold AxPtProt.pteNoNapot; rw [ext_of_pteSetAD]

theorem AxPtProt.pteSetAdPbmt0 (w : BitVec 64) (a d : BitVec 1) :
    ptePbmt0 (pteSetAD w a d) ↔ ptePbmt0 w := by
  unfold ptePbmt0; rw [ext_of_pteSetAD]

/-- Rocq `PtAdBits.pte_canon_inv`: equal canonical forms means A/D-variance. -/
theorem AxPtProt.pteCanonInv (w w' : BitVec 64) :
    PtAdBits.pteCanon w' = PtAdBits.pteCanon w → ∃ a d : BitVec 1, w' = pteSetAD w a d := by
  intro h
  refine ⟨BitVec.extractLsb' 6 1 w', BitVec.extractLsb' 7 1 w', ?_⟩
  simp only [PtAdBits.pteCanon, pteSetAD, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', BitVec.extractLsb, _update_PTE_Flags_A,
    _update_PTE_Flags_D] at h ⊢
  bv_decide

theorem AxPtProt.tlbCacheOfSetLeaf (asid : BitVec 16) (t : PTree) (vpn' : BitVec 27)
    (ent : TLB_Entry) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64) (a d : BitVec 1) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    pteValid (pteSetAD p0 a d) → pteLeaf (pteSetAD p0 a d) →
    AxPtProt.pteNoNapot (pteSetAD p0 a d) → ptePbmt0 (pteSetAD p0 a d) →
    AxPtProt.tlbCacheOf asid t vpn' ent →
    AxPtProt.tlbCacheOf asid (AxPtProt.ptreeSetLeaf t vpn (pteSetAD p0 a d)) vpn' ent := by
  rintro hmaps hv hl hnap hpb ⟨vpn0, q2, q1, q0, a', d', hm0, hh, hent⟩
  by_cases hne : vpn0 = vpn
  · rw [hne] at hm0 hh hent
    obtain ⟨h2, h1, h0⟩ := AxPtProt.ptreeMapsDet t vpn q2 q1 q0 p2 p1 p0 hm0 hmaps
    rw [h2, h1, h0] at hent
    exact ⟨vpn, p2, p1, pteSetAD p0 a d, a', d',
      AxPtProt.ptreeSetLeafMapsSelf t vpn p2 p1 p0 _ hmaps hv hl hnap hpb, hh,
      by rw [hent, pteSetAD_pteSetAD]⟩
  · exact ⟨vpn0, q2, q1, q0, a', d',
      AxPtProt.ptreeSetLeafMapsOther t vpn vpn0 q2 q1 q0 _ hne hm0, hh, hent⟩

theorem AxPtProt.tlbOkPtSetLeaf (asid : BitVec 16) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64)
    (a d : BitVec 1) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    pteValid (pteSetAD p0 a d) → pteLeaf (pteSetAD p0 a d) →
    AxPtProt.pteNoNapot (pteSetAD p0 a d) → ptePbmt0 (pteSetAD p0 a d) →
    AxPtProt.tlbOkPt asid t tlbvec →
    AxPtProt.tlbOkPt asid (AxPtProt.ptreeSetLeaf t vpn (pteSetAD p0 a d)) tlbvec :=
  fun hmaps hv hl hnap hpb hok vpn' ent hget =>
    AxPtProt.tlbCacheOfSetLeaf asid t vpn' ent vpn p2 p1 p0 a d hmaps hv hl hnap hpb
      (hok vpn' ent hget)

/-- Rocq `PtTree.pt_canon_l0/l1`, `ptree_canon`: level 0 canonicalised, everything else
verbatim. -/
def AxPtProt.ptCanonL0 (t : PTree) : PTree :=
  .node t.base (fun i => PtAdBits.pteCanon (t.ents i)) t.kids
def AxPtProt.ptCanonL1 (t : PTree) : PTree :=
  .node t.base t.ents (fun i => (t.kids i).map AxPtProt.ptCanonL0)
def AxPtProt.ptreeCanon (t : PTree) : PTree :=
  .node t.base t.ents (fun i => (t.kids i).map AxPtProt.ptCanonL1)

theorem AxPtProt.ptreeMapsCanon (t : PTree) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    AxPtProt.ptreeMaps (AxPtProt.ptreeCanon t) vpn p2 p1 (PtAdBits.pteCanon p0) := by
  rintro ⟨c1, c0, hk2, hk1, he2, he1, he0, hb1, hb0, hv2, hp2, hv1, hp1, hv0, hl0, hn0, hpb0⟩
  unfold AxPtProt.ptreeMaps
  refine ⟨AxPtProt.ptCanonL1 c1, AxPtProt.ptCanonL0 c0, ?_, ?_, he2, he1, ?_, hb1, hb0,
    hv2, hp2, hv1, hp1, (AxPtProt.pteSetAdValidLeaf p0 _ _ hl0).2 hv0,
    (AxPtProt.pteSetAdLeaf p0 _ _).2 hl0, (AxPtProt.pteSetAdNoNapot p0 _ _).2 hn0,
    (AxPtProt.pteSetAdPbmt0 p0 _ _).2 hpb0⟩
  · simp only [AxPtProt.ptreeCanon, AxPtProt.kidsNode, hk2, Option.map_some]
  · simp only [AxPtProt.ptCanonL1, AxPtProt.kidsNode, hk1, Option.map_some]
  · simp only [AxPtProt.ptCanonL0, AxPtProt.entsNode, he0]

theorem AxPtProt.ptreeMapsCanonInv (t : PTree) (vpn : BitVec 27) (p2 p1 w : BitVec 64) :
    AxPtProt.ptreeMaps (AxPtProt.ptreeCanon t) vpn p2 p1 w →
    ∃ q0, AxPtProt.ptreeMaps t vpn p2 p1 q0 ∧ w = PtAdBits.pteCanon q0 := by
  rintro ⟨d1, d0, hk2, hk1, he2, he1, he0, hb1, hb0, hv2, hp2, hv1, hp1, hv0, hl0, hn0, hpb0⟩
  simp only [AxPtProt.ptreeCanon, AxPtProt.kidsNode] at hk2
  cases hc1 : t.kids (AxPtProt.vpnIdx 2 vpn) with
  | none => rw [hc1] at hk2; cases hk2
  | some c1 =>
    rw [hc1, Option.map_some] at hk2
    have e1 : AxPtProt.ptCanonL1 c1 = d1 := Option.some.inj hk2
    subst e1
    simp only [AxPtProt.ptCanonL1, AxPtProt.kidsNode] at hk1
    cases hc0 : c1.kids (AxPtProt.vpnIdx 1 vpn) with
    | none => rw [hc0] at hk1; cases hk1
    | some c0 =>
      rw [hc0, Option.map_some] at hk1
      have e0 : AxPtProt.ptCanonL0 c0 = d0 := Option.some.inj hk1
      subst e0
      have he0' : PtAdBits.pteCanon (c0.ents (AxPtProt.vpnIdx 0 vpn)) = w := he0
      subst he0'
      have hlq : pteLeaf (c0.ents (AxPtProt.vpnIdx 0 vpn)) :=
        (AxPtProt.pteSetAdLeaf _ _ _).1 hl0
      refine ⟨c0.ents (AxPtProt.vpnIdx 0 vpn), ?_, rfl⟩
      exact ⟨c1, c0, hc1, hc0, he2, he1, rfl, hb1, hb0, hv2, hp2, hv1, hp1,
        (AxPtProt.pteSetAdValidLeaf _ _ _ hlq).1 hv0, hlq,
        (AxPtProt.pteSetAdNoNapot _ _ _).1 hn0, (AxPtProt.pteSetAdPbmt0 _ _ _).1 hpb0⟩

/-- THE INVARIANCE: the Svadu write-back does not move the canonical table. -/
theorem AxPtProt.ptreeCanonSetLeaf (t : PTree) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64)
    (a d : BitVec 1) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    AxPtProt.ptreeCanon (AxPtProt.ptreeSetLeaf t vpn (pteSetAD p0 a d)) =
      AxPtProt.ptreeCanon t := by
  rintro ⟨c1, c0, hk2, hk1, -, -, he0, -⟩
  simp only [AxPtProt.ptreeSetLeaf, hk2, hk1]
  simp only [AxPtProt.ptreeCanon, AxPtProt.ptUpdKid, PTree.base_node,
      AxPtProt.entsNode, AxPtProt.kidsNode]
  congr 1
  funext i2
  split
  · rename_i h2
    rw [h2, hk2, Option.map_some, Option.map_some]
    congr 1
    simp only [AxPtProt.ptCanonL1, PTree.base_node,
      AxPtProt.entsNode, AxPtProt.kidsNode]
    congr 1
    funext i1
    split
    · rename_i h1
      rw [h1, hk1, Option.map_some, Option.map_some]
      congr 1
      simp only [AxPtProt.ptCanonL0, AxPtProt.ptUpdEnt, PTree.base_node,
      AxPtProt.entsNode, AxPtProt.kidsNode]
      congr 1
      funext i0
      split
      · rename_i h0
        rw [h0, ← he0]
        exact PtAdBits.pteCanonSetAd _ a d
      · rfl
    · rfl
  · rfl

/-- THE TRANSFER: cached-entry coherence depends on the table only through its canonical
form. -/
theorem AxPtProt.tlbOkPtCanon (asid : BitVec 16) (t t' : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) :
    AxPtProt.ptreeCanon t = AxPtProt.ptreeCanon t' →
    AxPtProt.tlbOkPt asid t tlbvec → AxPtProt.tlbOkPt asid t' tlbvec := by
  intro hcan hok vpn' ent hget
  obtain ⟨vpn, p2, p1, p0, a, d, hmaps, hh, hent⟩ := hok vpn' ent hget
  have hmc := AxPtProt.ptreeMapsCanon t vpn p2 p1 p0 hmaps
  rw [hcan] at hmc
  obtain ⟨q0, hmaps', hq⟩ := AxPtProt.ptreeMapsCanonInv t' vpn p2 p1 _ hmc
  obtain ⟨a', d', hp0⟩ := AxPtProt.pteCanonInv q0 p0 hq
  exact ⟨vpn, p2, p1, q0, a, d, hmaps', hh, by rw [hent, hp0, pteSetAD_pteSetAD]⟩

/-! ## 7. TLB-AGREES-WITH-PT -/

def tlbAgrees (asid : BitVec 16) (T : PTree) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) :
    Prop := AxPtProt.tlbOkPt asid T tlbvec

theorem tlbAgreesFlush (asid : BitVec 16) (T : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) :
    (∀ vpn', tlbvec[tlb_hash 39 vpn']! = none) → tlbAgrees asid T tlbvec :=
  AxPtProt.tlbOkPtEmpty asid T tlbvec

theorem tlbAgreesCanon (asid : BitVec 16) (T T' : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) :
    AxPtProt.ptreeCanon T = AxPtProt.ptreeCanon T' →
    tlbAgrees asid T tlbvec → tlbAgrees asid T' tlbvec :=
  AxPtProt.tlbOkPtCanon asid T T' tlbvec

theorem tlbAgreesSetLeaf (asid : BitVec 16) (T : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64)
    (a d : BitVec 1) :
    AxPtProt.ptreeMaps T vpn p2 p1 p0 →
    pteValid (pteSetAD p0 a d) → pteLeaf (pteSetAD p0 a d) →
    AxPtProt.pteNoNapot (pteSetAD p0 a d) → ptePbmt0 (pteSetAD p0 a d) →
    tlbAgrees asid T tlbvec →
    tlbAgrees asid (AxPtProt.ptreeSetLeaf T vpn (pteSetAD p0 a d)) tlbvec :=
  AxPtProt.tlbOkPtSetLeaf asid T tlbvec vpn p2 p1 p0 a d

/-- THE FILL: the three walker reads of a translation are DEMONIC; the discipline at each
slot pins them, and the entry the walk installs agrees. -/
theorem tlbAgreesWalkFill (GP : Gptw) (asid : BitVec 16) (T : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64)
    (T2 T1 T0 : Nat) (r2 r1 r0 : Geid) (q2 q1 q0 : BitVec 64) :
    gwf (gpG GP) → h5WalkValue GP →
    AxPtProt.ptreeMaps T vpn p2 p1 p0 →
    ptDisc (gpG GP) ((AxPtProt.ptAddr2 T vpn).toNat : Int) (Eq p2) T2 →
    ptDisc (gpG GP) ((AxPtProt.ptAddr1 p2 vpn).toNat : Int) (Eq p1) T1 →
    ptDisc (gpG GP) ((AxPtProt.ptAddr0 p1 vpn).toNat : Int) (pteVar p0) T0 →
    gwalk GP r2 → gwalk GP r1 → gwalk GP r0 →
    (∀ j, j < 8 → ∃ t, greadsByte (gpG GP) r2
        (accAddr ((AxPtProt.ptAddr2 T vpn).toNat : Int) j) t (nthByte (n := 8) q2 j) ∧
        T2 ≤ t) →
    (∀ j, j < 8 → ∃ t, greadsByte (gpG GP) r1
        (accAddr ((AxPtProt.ptAddr1 q2 vpn).toNat : Int) j) t (nthByte (n := 8) q1 j) ∧
        T1 ≤ t) →
    (∀ j, j < 8 → ∃ t, greadsByte (gpG GP) r0
        (accAddr ((AxPtProt.ptAddr0 q1 vpn).toNat : Int) j) t (nthByte (n := 8) q0 j) ∧
        T0 ≤ t) →
    tlbAgrees asid T tlbvec →
    q2 = p2 ∧ q1 = p1 ∧ pteVar p0 q0 ∧
    tlbAgrees asid T (vectorUpdate tlbvec (tlb_hash 39 vpn)
                       (some (uWalkEntry vpn q2 q1 q0 asid))) := by
  intro hwf hwv hmaps D2 D1 D0 W2 W1 W0 R2 R1 R0 hok
  have E2 : p2 = q2 := walkReadClass GP _ _ T2 r2 q2 hwf hwv D2 (mixClosedEq p2) W2 R2
  rw [← E2] at R1 ⊢
  have E1 : p1 = q1 := walkReadClass GP _ _ T1 r1 q1 hwf hwv D1 (mixClosedEq p1) W1 R1
  rw [← E1] at R0 ⊢
  have V0 := walkReadClass GP _ _ T0 r0 q0 hwf hwv D0 (mixClosedVar p0) W0 R0
  exact ⟨rfl, rfl, V0, AxPtProt.tlbOkPtFill asid T tlbvec vpn p2 p1 p0 q0 hmaps V0 hok⟩

/-! ## 8. THE GRAPH-LEVEL AGREEMENT INVARIANT and its establishment -/

def readsAfter (G : Gexec) (r : Geid) (pa : Int) (T0 : Nat) : Prop :=
  ∀ j t v, j < 8 → greadsByte G r (accAddr pa j) t v → T0 ≤ t

def agreesAt (GP : Gptw) (pa : Int) (r e : Geid) : Prop :=
  ∀ (x : BitVec 64) w (xw : BitVec 64),
    greadsWord (gpG GP) r pa x → gwritesWord (gpG GP) w pa xw →
    gmoLt (gpG GP) w e →
    (∀ w' j v, j < 8 → gwritesByte (gpG GP) w' (accAddr pa j) v →
       gmoLt (gpG GP) w' e → gwix (gpG GP) w' ≤ gwix (gpG GP) w) →
    PtAdBits.pteCanon x = PtAdBits.pteCanon xw

/-- H5'.2 gives `readsAfter` for a walk behind an sfence covering the install. -/
theorem readsAfterOfSfence (GP : Gptw) (f r i : Geid) (pa : Int) (w0 : BitVec 64) :
    h5Sfence GP → gsfence GP f → gwalk GP r → WeakRvwmoGraph.gpo (gpG GP) f r →
    gwritesWord (gpG GP) i pa w0 → sfCovers GP i f →
    readsAfter (gpG GP) r pa (gwix (gpG GP) i) := by
  intro hsf hf hr hfr hi hcov j t v hj hrt
  exact hsf f r _ t v i _ hf hr hfr hrt (hi j hj) hcov

/-- ESTABLISHMENT: discipline from an install gmo-before the access + a walk reading
at-or-after the install ⇒ the agreement holds. -/
theorem agreesAtOfDisc (GP : Gptw) (pa : Int) (w0 : BitVec 64) (i r e : Geid) :
    gwf (gpG GP) → h5WalkValue GP → gwalk GP r →
    gwritesWord (gpG GP) i pa w0 → gmoLt (gpG GP) i e →
    ptDisc (gpG GP) pa (pteVar w0) (gwix (gpG GP) i) →
    readsAfter (gpG GP) r pa (gwix (gpG GP) i) →
    agreesAt GP pa r e := by
  intro hwf hwv hr hi hie hd hra x w xw hx hw hwe hmax
  have V : pteVar w0 x := by
    apply walkReadClass GP pa _ (gwix (gpG GP) i) r x hwf hwv hd (mixClosedVar w0) hr
    intro j hj
    obtain ⟨t, ht⟩ := hx j hj
    exact ⟨t, ht, hra j t _ hj ht⟩
  have hle : gwix (gpG GP) i ≤ gwix (gpG GP) w := hmax i 0 _ (by omega) (hi 0 (by omega)) hie
  have Vw : pteVar w0 xw := by
    apply mixClosedVar w0
    intro j hj
    exact hd.1 w j _ hj (hw j hj) hle
  rw [pteVarCanon _ _ V, pteVarCanon _ _ Vw]

end Weak
