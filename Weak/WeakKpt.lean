/-
Weak: **the weak kernel-page-table invariant and the weak absorption theorem** (batch-6 P4).

Rocq: `iris/WeakKpt.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).  THE MIRROR of `KptShare.v` over the weak
memory model: the shared kernel-page-table invariant `wkpt_inv` (the `kpt_inv` mirror with
`ptree_own` split by role over the `γlat` latest-write elements), the per-hart residue
`wtlb_res_pt` (the `tlb_res_pt` mirror), and the weak ABSORPTION THEOREM
`wtlb_res_pt_translateAddr_at` -- the `tlb_res_pt_translateAddr_at` mirror with
`gen_heap_interp` swapped for `WeakGhost.wlat_interp` and `RiscvExec.exec` for the instrumented
`WeakCert.exec_eff` at the coherent flat projection `WeakBridge.wflat_st σ`.

THE INVARIANT, per mapped vpn of the kmap auth's map M:
  - the two POINTER slot words as kvminit-timestamped, DISCARDED (persistent) `wlat8` element
    bundles (`wptr8`): pointer words are single-message -- nothing ever stores to a PT page but
    the leaf write-back -- so their latest-write elements can be persisted, and the stored bound
    `ts ≤ T_kpt` is what lets a consumer holding the per-hart receipt (pure shadow:
    `T_kpt ≤ w_vrNew`) derive `pinned_read` for the walk's two pointer reads;
  - the LEAF window as an EXCLUSIVE `∃ ts a d, wlat8 la 1 ts (pte_set_ad w0 a d)` (`wleaf_res`)
    -- a write-back retargets it at the appended message (`wlat8_store_prim`), the lock-release
    shape;
  - the VALUE-CLOSURE and FRESH-DERIVED discipline conjuncts, CLIPPED AT THE WINDOW'S INSTALL
    TIMESTAMP `T0` and stored against a log SNAPSHOT (`wlog_lb log0`): see the design
    correction below;
  - `kmap_auth M` + `kpt_lb t` + the tree spec `kpt_tree_spec_gen root M t`, verbatim from the
    SC invariant.

DESIGN CORRECTION (vs the batch-6 block's un-clipped `wlog_variants`): the closure and
discipline conjuncts CANNOT be stated over the whole log.  The era log of a real boot contains
pre-kvminit messages into the leaf windows (freerange/kalloc memset the PT pages with 0x01/0x05
junk before kvmmake writes the canonical PTEs), so "every log message at the window writes a
variant" is FALSE and the invariant would be unmintable.  The honest form clips at the INSTALL
write `T0` (kvmmake's store of the leaf), and the collapse still goes through because the
receipt's cover bars every admissible read below `T0` (`wbyte_ok_ge`: a read floor covering the
install write forces `t ≥ T0` -- the same `readable`-coherence argument that bars the
era-initial image, one timestamp higher).  A whole-log fact cannot sit in an invariant anyway;
the stored shape is `wlog_lb log0 ∗ ⌜closure-of log0⌝` plus the leaf element, and the extension
to the CURRENT log is derived at the absorption from the element's `latest_ts` (no message
above the element's timestamp writes the window -- `wwin_no_write_above`).  This is also why
the theorem consumes `wlog_auth` alongside `wlat_interp`: the log-prefix tie (`wlog_valid`) and
the fresh snapshot at the write-back re-close (`wlog_snapshot`) both need the authority.

THE ABSORPTION THEOREM: keyed on the caller's `kmap_at` claim, opens `wkptN` mask-carrying,
and produces
  - the pure `exec_eff (translateAddr va acc) (wflat_st σ) = Ok pa` fact with the EXACT
    per-outcome trace (O1 hit: []; O2 fill: the three plain walk reads; O2' refresh: the lone
    CAS read; O3 write-back: walk reads + the adjacent CAS pair, or the CAS pair alone on the
    hit path) -- `pa` variant-independent;
  - the racy-leaf COLLAPSE facts for the 6a bridge: every admissible read of the leaf window
    (`WeakRacy.wadm`) is a variant of the canonical leaf AND `pte_ad_le`-below the latest word;
  - `pinned_read` for every byte of the two pointer slots (the `trace_pin` discharge for the
    walk's plain pointer reads);
  - the φ-upgrade: the walked leaf slot's bytes are `nv_free` at the pre-state;
  - the ghost re-establishment: `reg_interp` at the successor's registers,
    `wlog_auth`/`wlat_interp` unchanged on the quiet arms and AT THE APPENDED LOG on the
    write-back arm (the message identity `wwrite_msg tid la 8 lw'` matches
    `WeakUpdEff.wcert_ptw_upd`'s `wQ_store_w 8`), and the residue + invariant re-closed
    (`kpt_lb` survives by `ptree_canon_set_leaf` exactly as SC).

Split (protocol length rule): §§1–4 here, §5 (the absorption theorem and its three Lean-only
helpers) in `Weak/WeakKpt2.lean`.

Sections: §1 the CLIPPED closure layer (`wlogVariantsFrom` / `wfreshFrom` and their extension /
write-back / collapse kit); §2 the kperm eff twins (`wkpermVariantValid` /
`wkpermVariantCheck`); §3 the invariant (`wptr8` / `wleafRes` / `wvpnRes` / `wkptBody` /
`wkptInv`) and the residue `wtlbResPt`; §4 the pure dispatch `wptreeTranslateAddrEffCases`
with the per-outcome traces; §5 THE ABSORPTION THEOREM `wtlbResPtTranslateAddrAt`.

O2 (`notes/weak-port-o2-design.md` §1.6): the walker's plain reads are `AK_ttw`, which
classifies `wakPlain` -- the trace literals are Rocq's (`.WEread wakPlain a 8`); the A/D CAS
stays `⟨false, true, false⟩` (`WeakUpdEff` header).

**Deviations from Rocq.**

1. VOCABULARY as `Weak/WeakWalkEff.lean` / `Weak/WeakUpdEff.lean` deviation 1 and
   `Weak/WeakVariant.lean` deviation 1 (`register_lookup r s.(sregs)` ↦ `s.regs r`,
   `wm_regs σ` ↦ `σ.wmRegs`, `wm_log σ` ↦ `σ.wmLog`, `w_vrNew (wm_ws σ)` ↦ `σ.wmWs.wVrNew`,
   `l !! i` ↦ `l[i]?`, `S i` ↦ `i + 1`, `is_Some o` ↦ `o.isSome = true`, `acc_addr` ↦
   `WeakInterp.accAddr`, `pa_z` ↦ `paZ`, `nth_byte` ↦ `nthByte (n := 8)`, `pte_set_ad` ↦
   `MachCSL.pteSetAD`, `pte_set_ad_absorb` ↦ `MachCSL.pteSetAD_pteSetAD`, `mword_of_int 0 :
   mword 16` ↦ `0#16`, `autocast (PPN_of_PTE p)` ↦ `ppn0 p`, `set_reg s tlb v` ↦
   `s.setReg .tlb v`, `MState s.(sregs) (write_bytes s.(mem) a 8 v) s.(mdev)` ↦
   `s.setMem (bmWrite s.mem a 8 v)`, `wflat (wm_img σ) (wm_log σ)` ↦
   `wflatMem σ.wmImg σ.wmLog`, `AkInfo false true false` ↦ `⟨false, true, false⟩`,
   `MISA_C` ↦ `misaC`, `MENVCFG_S` ↦ `MachCSL.menvcfgS`, `'b"1000"` ↦ `8#4`,
   `'b"10"` ↦ `2#2`, `uint` ↦ `toNat`, `ram_base + ram_size` ↦ `ramEnd`).  `pt_addr*`,
   `ptree_maps`, `ptree_set_leaf`, `ptree_canon`, `tlb_ok_pt` are `AxPtProt.*`;
   `pt_slot_mem`, `ptree_blocks`, `uwe_match_other` are `WeakWalkEff.*`.
2. O2 (`WeakVariant` deviation 3): the Lean `akIfetch` arm of `wbyteOk` is not refuted by the
   data-view cover, so `wbyteOkGe` and everything built on it (`wbyteOkVariantFrom`,
   `wadmVariantFrom`, `wadmPteAdLeLatestFrom`) take `ak.akIfetch = false` (just before the
   cover premise), and the absorption theorem's collapse conjunct is stated for
   `rak.akIfetch = false` reads (a walk is `AK_ttw`, a CAS read `AK_explicit`: both qualify).
3. KERNEL LEAVES.  Rocq's `kperm` / `kperm_flags pc` (an integer flag byte at A = D = 1) /
   `mk_pte` are Lean's `MachCSL.KPerm` / `KPerm.flags` (A = D = 0, the Lean kernel's kvmmake
   bytes) / `mkPte`; since every statement is A/D-variant-closed (`pteSetAD w0 a d`) the
   choice of canonical A/D is immaterial.  The §2 reducers take the A/D pair as two
   `BitVec 1` (Rocq: `bool * bool` through `kperm_flags_ad`), in the shape
   `MachCSL.flags_of_kLeaf` leaves.  Rocq's `kperm_allows` (`KptPt`, not in the Lean tree) is
   ported as the Lean-only `WeakKpt.kpermAllows` (verbatim).
4. SC GHOST VOCABULARY (`KptGhost`/`KMap`/`KptShare`/`SmodeCore`/`KptTree`), not 1:1 in the Lean
   tree (`notes/weak-port-map.md`: ANALOG), supplied here per architecture §C.4:
   - `kpt_lb t` ↦ `WeakKpt.kptLb t`, the canonical table as a DISCARDED ghost variable
     (`γ ↪VAR{.discard} (ptreeCanon t)`; Rocq: the one-shot `Cinr (to_agree …)` -- same
     persistence and agreement) at the name of the new class `WeakKpt.KptGS`;
     `kpt_lb_agree` / `kpt_lb_canon` ↦ `WeakKpt.kptLbAgree` / `WeakKpt.kptLbCanon`.
   - `kmap_auth M` ↦ `WeakKpt.kmapAuth M` = Lean's published (`.discard`) mapping authority
     at `MachGS.kmapName`, over `RegMapF (BitVec 64)` (key `vpn.toNat`, value the canonical
     leaf -- Lean SC's `kptOn` shape); Rocq's map is `gmap (mword 27) (mword 44 * kperm)`.
     `kmap_at vpn ppn pc` ↦ `MachCSL.kmapAt vpn (kLeaf ppn pc 0#1 0#1)`;
     `kmap_at_lookup` ↦ `WeakKpt.kmapAtLookup`.  Consequently `kpt_leaf_pte_of vpn e` is the
     value `e` itself, `wvpn_res … vpn e` takes `e : BitVec 64`, the body's `[∗ map]` ranges
     over `k ↦ e` at `BitVec.ofNat 27 k`, and `kpt_tree_spec_gen` (↦ `WeakKpt.kptTreeSpecGen`)
     has the extra conjunct "every key is below `2 ^ 27`" (Rocq's key type).
   - `tlb_snap_ok` ↦ `WeakKpt.tlbSnapOk`; `pmp_config root` / `pmp_config_intro` ↦
     `WeakKpt.pmpConfig cpu root` / `WeakKpt.pmpConfigIntro` over Lean's register points-to.
   - `kpt_tree_spec_gen_set_leaf` ↦ `WeakKpt.kptTreeSpecGenSetLeaf`, proved from the walk-path
     facts (the A/D-stability of `AxPtProt`) instead of `kperm_variant_*`;
     `ptree_set_leaf_blocks` ↦ `WeakKpt.ptreeSetLeafBlocks`; `tlb_ok_pt_fill_self` ↦
     `WeakKpt.tlbOkPtFillSelf`; `uwe_match_self` ↦ `WeakKpt.uweMatchSelf`; `svpn_of` ↦
     `WeakKpt.svpnOf` (the `translateAddr` vpn expression of `WeakWalkEff` deviation 7).
   - `pma_allows_pte_read/write` ↦ `WeakKpt.pmaAllowsPteRead/Write` (Rocq's `pma_ram_access a
     8` ↦ `inRam a 8`); `pma_allows_all` ↦ `pma_regions = bootPMA` (WeakFetchEff deviation 5);
     `pma_allows_all_pte_read/write` ↦ `WeakKpt.pmaAllowsBootPteRead/Write`.
5. CONTEXTS (WeakGhost deviations 9, 10, 12): `Context {!riscvGS Σ, !weakGS Σ} {GEN CID}` ↦
   `[MachGS hlc GF] [WeakGS GF] [WeakKpt.KptGS GF]`; the ambient hart is the explicit
   `cpu : CPU` (`reg_interp` ↦ `regInterp cpu`, `r ↦ᵣ v` ↦ `r ↦ᵣ[cpu] v`); `P -∗ Q ={E}=∗ R` ↦
   `P ∗ Q ⊢ |={E}=> R`.
6. `wslot_geom a` (Rocq `addr_is_ram a ∧ addr_is_ram (pa_add a 7) ∧ aligned`) ↦
   `inRam a 8 ∧ aligned` (WeakWalkEff deviation 6).  The absorption theorem's
   `pma_allows_all` premise is `σ.wmRegs .pma_regions = bootPMA`.
7. Section variables are theorem arguments; the Rocq conclusion's `let vpn/a2/a1/la` are
   inlined (`WeakKpt.svpnOf va`, `uPteAddr …`).  Rocq's `Print Assumptions` commands are not
   declarations.  Instances `wlat8_discarded_persistent`, `wptr8_persistent`, … keep the Rocq
   instance names.
8. Lean-only helpers (file-qualified): `WeakKpt.ptreeSetLeafBase`; in `Weak/WeakKpt2.lean`
   `WeakKpt.ofNatToNat27`, `WeakKpt.bigSepMVpnDelete`, `WeakKpt.bigSepMVpnInsert`,
   `WeakKpt.wlat8StoreExcl` (the `wlat8_store_prim` call of the write-back arm, at the bundle
   level).
9. §4's `let vpn := svpn_of va` / `let p0 := pte_set_ad w a0 d0` are kept as Lean `let`s in
   the statements.

**Rocq → Lean name map.**  `wlog_variants_from` `wlogVariantsFrom`; `wfresh_from`
`wfreshFrom`; `wwin_install` `wwinInstall`; `log_byte_img_irrel` `logByteImgIrrel`;
`wwin_install_log_byte` `wwinInstallLogByte`; `wwin_install_prefix` `wwinInstallPrefix`;
`wwin_no_write_above` `wwinNoWriteAbove`; `wlog_variants_from_ext` `wlogVariantsFromExt`;
`wfresh_from_ext` `wfreshFromExt`; `wbyte_ok_ge` `wbyteOkGe`; `wbyte_ok_variant_from`
`wbyteOkVariantFrom`; `wadm_variant_from` `wadmVariantFrom`; `wwin_latest_variant_from`
`wwinLatestVariantFrom`; `wfresh_from_mono` `wfreshFromMono`; `wlog_variants_from_snoc`
`wlogVariantsFromSnoc`; `wfresh_from_writeback` `wfreshFromWriteback`;
`wadm_pte_ad_le_latest_from` `wadmPteAdLeLatestFrom`; `wkperm_inv_red` `wkpermInvRed`;
`wkperm_check_fetch/load/store/amo` `wkpermCheckFetch/Load/Store/Amo`; `wkperm_variant_valid`
`wkpermVariantValid`; `wkperm_variant_check` `wkpermVariantCheck`; `wkptN` `wkptN`;
`wslot_geom` `wslotGeom`; `wslot_geom_acc_wf` `wslotGeomAccWf`; `wptr8` `wptr8`;
`wlat8_discarded_persistent`, `wptr8_persistent`, `wptr8_timeless`, `wleaf_res_timeless`,
`wvpn_res_timeless`, `wkpt_body_timeless`, `wkpt_inv_persistent` (instances, same names);
`wleaf_res` `wleafRes`; `wvpn_res` `wvpnRes`; `wkpt_body` `wkptBody`; `wkpt_inv` `wkptInv`;
`wkpt_inv_alloc` `wkptInvAlloc`; `wtlb_res_pt` `wtlbResPt`; `wtlb_res_pt_intro`
`wtlbResPtIntro`; `wptree_translate_miss_eff_core` `wptreeTranslateMissEffCore`;
`wptree_translateAddr_eff_cases` `wptreeTranslateAddrEffCases`; `wslot_mem_of_flat`
`wslotMemOfFlat`; `wvpn_res_maps_mono` `wvpnResMapsMono`; `wtlb_res_pt_translateAddr_at`
`wtlbResPtTranslateAddrAt`.  SC twins (deviation 4, file-qualified `WeakKpt.*`): `kpt_lb`
`kptLb`, `kpt_lb_agree` `kptLbAgree`, `kpt_lb_canon` `kptLbCanon`, `kmap_auth` `kmapAuth`,
`kmap_at_lookup` `kmapAtLookup`, `kperm_allows` `kpermAllows`, `kpt_tree_spec_gen`
`kptTreeSpecGen`, `kpt_tree_spec_gen_set_leaf` `kptTreeSpecGenSetLeaf`,
`ptree_set_leaf_blocks` `ptreeSetLeafBlocks`, `tlb_ok_pt_fill_self` `tlbOkPtFillSelf`,
`uwe_match_self` `uweMatchSelf`, `svpn_of` `svpnOf`, `tlb_snap_ok` `tlbSnapOk`, `pmp_config`
`pmpConfig`, `pmp_config_intro` `pmpConfigIntro`, `pma_allows_pte_read/write`
`pmaAllowsPteRead/Write`, `pma_allows_all_pte_read/write` `pmaAllowsBootPteRead/Write`.

**Dropped:** nothing -- 4 Rocq `Definition`s of §1, 13 `Lemma`s of §1, 7 of §2, the §3
definitions/instances/lemmas (`wkptN`, `wslot_geom`, `wslot_geom_acc_wf`, `wptr8`, 4
instances, `wleaf_res` + instance, `wvpn_res` + instance, `wkpt_body` + instance, `wkpt_inv` +
instance, `wkpt_inv_alloc`, `wtlb_res_pt`, `wtlb_res_pt_intro`), §4's 2 lemmas and §5's 3
lemmas are all ported.
-/
import Weak.WeakUpdEff
import MachCSL.KMap
import MachCSL.PlatformFacts

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The clipped closure layer -/

/-- The closure, clipped: every message at timestamp `T0` or later that touches the window
writes variant bytes (the timestamp of index `i` is `i + 1`; the install write is included). -/
def wlogVariantsFrom (T0 : Nat) (log : List Wmsg) (a8 : Int) (w0 : BitVec 64) : Prop :=
  ∀ (i : Nat) (m : Wmsg), log[i]? = some m → T0 ≤ i + 1 → wmsgVariant a8 w0 m

/-- The discipline, clipped: every message STRICTLY after the install that writes byte `a`
derived its value from the latest value at its own append time with A/D bits only ORed. -/
def wfreshFrom (T0 : Nat) (img : Image) (log : List Wmsg) (a : Int) : Prop :=
  ∀ (i : Nat) (m : Wmsg) (b : BitVec 8),
    log[i]? = some m → T0 < i + 1 → msgByte m a = some b →
    ∃ bf : BitVec 8,
      logByte img (log.take i) (latestTs (log.take i) a) a = some bf ∧ adBitsLe bf b

/-- The install fact: the message at timestamp `T0` writes every byte of the window. -/
def wwinInstall (log : List Wmsg) (T0 : Nat) (ra : PAddr) : Prop :=
  1 ≤ T0 ∧
  ∃ m : Wmsg, log[T0 - 1]? = some m ∧
    ∀ j : Nat, j < 8 → (msgByte m (WeakInterp.accAddr ra j)).isSome = true

/-! ### 1a. Plumbing -/

/-- `logByte` at a message timestamp does not consult the image. -/
theorem logByteImgIrrel (img img' : Image) (log : List Wmsg) (t : Nat) (a : Int) :
    1 ≤ t → logByte img log t a = logByte img' log t a := by
  intro ht
  cases t with
  | zero => omega
  | succ i => rfl

/-- The install writes byte `j` at timestamp `T0`. -/
theorem wwinInstallLogByte (img : Image) (log : List Wmsg) (T0 : Nat) (ra : PAddr) (j : Nat) :
    j < 8 → wwinInstall log T0 ra → (logByte img log T0 (WeakInterp.accAddr ra j)).isSome = true := by
  rintro hj ⟨hT0, m, hm, hw⟩
  obtain ⟨i, rfl⟩ : ∃ i, T0 = i + 1 := ⟨T0 - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hm
  rw [logByteS, hm]
  exact hw j hj

/-- The install survives a log extension. -/
theorem wwinInstallPrefix (log0 log : List Wmsg) (T0 : Nat) (ra : PAddr) :
    wwinInstall log0 T0 ra → log0 <+: log → wwinInstall log T0 ra := by
  rintro ⟨hT0, m, hm, hw⟩ ⟨rest, rfl⟩
  exact ⟨hT0, m, lookup_app_l_Some hm, hw⟩

/-- No message at or above the element's timestamp writes the window: the element IS the
latest write per byte. -/
theorem wwinNoWriteAbove (s : Wmstate) (ra : PAddr) (ts : Nat) :
    (∀ j : Nat, j < 8 → latestTs s.wmLog (WeakInterp.accAddr ra j) = ts) →
    ∀ (i : Nat) (m : Wmsg), s.wmLog[i]? = some m → ts ≤ i →
      ∀ j : Nat, j < 8 → msgByte m (WeakInterp.accAddr ra j) = none := by
  intro hlat i m hm hge j hj
  cases hb : msgByte m (WeakInterp.accAddr ra j) with
  | none => rfl
  | some b =>
    exfalso
    have hlb : (logByte (wimg s) s.wmLog (i + 1) (WeakInterp.accAddr ra j)).isSome = true := by
      rw [logByteS, hm]
      show (msgByte m (WeakInterp.accAddr ra j)).isSome = true
      rw [hb]; rfl
    have hle := writesLeLatestTs (wimg s) s.wmLog _ _ hlb
    rw [hlat j hj] at hle
    omega

/-! ### 1b. Extension to the current log -/

theorem wlogVariantsFromExt (T0 : Nat) (log0 log : List Wmsg) (a8 : Int) (w0 : BitVec 64) :
    wlogVariantsFrom T0 log0 a8 w0 →
    log0 <+: log →
    (∀ (i : Nat) (m : Wmsg), log[i]? = some m → log0.length ≤ i →
       ∀ j : Nat, j < 8 → msgByte m (a8 + (j : Int)) = none) →
    wlogVariantsFrom T0 log a8 w0 := by
  intro hv hpref hno i m hm hT0
  by_cases hlt : i < log0.length
  · obtain ⟨rest, rfl⟩ := hpref
    rw [lookup_app_l hlt] at hm
    exact hv i m hm hT0
  · exact wmsgVariantUntouched _ _ _ (fun j hj => hno i m hm (by omega) j hj)

theorem wfreshFromExt (T0 : Nat) (img : Image) (log0 log : List Wmsg) (a : Int) :
    wfreshFrom T0 img log0 a →
    log0 <+: log →
    (∀ (i : Nat) (m : Wmsg), log[i]? = some m → log0.length ≤ i → msgByte m a = none) →
    wfreshFrom T0 img log a := by
  intro hf hpref hno i m b hm hT0 hb
  by_cases hlt : i < log0.length
  · obtain ⟨rest, rfl⟩ := hpref
    rw [lookup_app_l hlt] at hm
    obtain ⟨bf, hbf, hle⟩ := hf i m b hm hT0 hb
    refine ⟨bf, ?_, hle⟩
    rw [List.take_append_of_le_length (by omega)]
    exact hbf
  · rw [hno i m hm (by omega)] at hb
    cases hb

/-! ### 1c. The exclusion: a covered install bars everything below it -/

/-- If the hart's read floor covers a write at timestamp `tc`, no admissible non-fetch read
returns a timestamp below `tc` (deviation 2). -/
theorem wbyteOkGe (s : Wmstate) (ak : AkInfo) (a : Int) (t tc : Nat) (b : BitVec 8) :
    1 ≤ tc →
    ak.akIfetch = false →
    tc ≤ s.wmWs.wVrNew →
    (logByte (wimg s) s.wmLog tc a).isSome = true →
    wbyteOk s ak a t b →
    tc ≤ t := by
  rintro _ hif htcv htcw ⟨_, hadm⟩
  rw [hif] at hadm
  simp only [Bool.false_eq_true, ↓reduceIte] at hadm
  apply Nat.le_of_not_lt
  intro hlt
  apply hadm.1.2
  refine (writesInLogByte (wimg s) s.wmLog a _ _).2 ⟨tc, hlt, ?_, htcw⟩
  exact Nat.le_trans htcv (Nat.le_trans (loadVpreVrNew _ _) (Nat.le_max_left _ _))

/-! ### 1d. The clipped collapse at the window -/

theorem wbyteOkVariantFrom (s : Wmstate) (ak : AkInfo) (ra : PAddr) (w0 : BitVec 64) (T0 j t : Nat)
    (b : BitVec 8) :
    j < 8 →
    wlogVariantsFrom T0 s.wmLog (paZ ra) w0 →
    wwinInstall s.wmLog T0 ra →
    ak.akIfetch = false →
    T0 ≤ s.wmWs.wVrNew →
    wbyteOk s ak (WeakInterp.accAddr ra j) t b →
    ∃ a d : BitVec 1, b = nthByte (n := 8) (pteSetAD w0 a d) j := by
  intro hj hvar hinst hif hcov hok
  have hge := wbyteOkGe s ak _ t T0 b hinst.1 hif hcov
    (wwinInstallLogByte (wimg s) s.wmLog T0 ra j hj hinst) hok
  have hb := hok.1
  obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by have := hinst.1; omega⟩
  rw [logByteS] at hb
  cases hm : s.wmLog[i]? with
  | none => rw [hm] at hb; cases hb
  | some m =>
    rw [hm] at hb
    change msgByte m (WeakInterp.accAddr ra j) = some b at hb
    obtain ⟨a, d, hv⟩ := hvar i m hm (by omega)
    exact ⟨a, d, hv j hj b hb⟩

/-- THE `wadm` COLLAPSE, clipped: every admissible (non-fetch) read of the window is a variant
of the canonical leaf. -/
theorem wadmVariantFrom (s : Wmstate) (rak : AkInfo) (ra : PAddr) (w0 : BitVec 64) (T0 : Nat)
    (w : BitVec (8 * 8)) :
    wlogVariantsFrom T0 s.wmLog (paZ ra) w0 →
    wwinInstall s.wmLog T0 ra →
    rak.akIfetch = false →
    T0 ≤ s.wmWs.wVrNew →
    wadm s rak ra 8 w →
    ∃ a d : BitVec 1, w = pteSetAD w0 a d := by
  intro hvar hinst hif hcov hadm
  apply pteVariantMix
  intro j hj
  obtain ⟨t, hok⟩ := hadm j hj
  exact wbyteOkVariantFrom s rak ra w0 T0 j t _ hj hvar hinst hif hcov hok

/-- The latest window word is a variant (each byte's latest writer is at or above the
install). -/
theorem wwinLatestVariantFrom (s : Wmstate) (ra : PAddr) (w0 : BitVec 64) (T0 : Nat)
    (wl : BitVec (8 * 8)) :
    wlogVariantsFrom T0 s.wmLog (paZ ra) w0 →
    wwinInstall s.wmLog T0 ra →
    wwinLatest s ra wl →
    ∃ a d : BitVec 1, wl = pteSetAD w0 a d := by
  intro hvar hinst hlat
  apply pteVariantMix
  intro j hj
  obtain ⟨t, hlv⟩ := hlat j hj
  have hts := latestValTs _ _ _ _ _ hlv
  have hge := writesLeLatestTs (wimg s) s.wmLog _ T0
    (wwinInstallLogByte (wimg s) s.wmLog T0 ra j hj hinst)
  rw [hts] at hge
  have hb := hlv.1
  obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by have := hinst.1; omega⟩
  rw [logByteS] at hb
  cases hm : s.wmLog[i]? with
  | none => rw [hm] at hb; cases hb
  | some m =>
    rw [hm] at hb
    change msgByte m (WeakInterp.accAddr ra j) = some _ at hb
    obtain ⟨a, d, hv⟩ := hvar i m hm (by omega)
    exact ⟨a, d, hv j hj _ hb⟩

/-! ### 1e. The clipped discipline: monotone above the install -/

/-- BIT-MONOTONICITY above the install: any two writers at or above `T0` are
`adBitsLe`-ordered by timestamp. -/
theorem wfreshFromMono (T0 : Nat) (img : Image) (log : List Wmsg) (a : Int) :
    1 ≤ T0 →
    (logByte img log T0 a).isSome = true →
    wfreshFrom T0 img log a →
    ∀ (t' t : Nat) (b b' : BitVec 8),
      T0 ≤ t → t ≤ t' →
      logByte img log t a = some b →
      logByte img log t' a = some b' →
      adBitsLe b b' := by
  intro _ hinst hf t'
  induction t' using Nat.strongRecOn with
  | ind t' ih =>
  intro t b b' hT0t hle hb hb'
  by_cases hne : t = t'
  · subst hne
    rw [hb] at hb'
    injection hb' with hb'
    subst hb'
    exact adBitsLeRefl b
  · have hlt : t < t' := by omega
    obtain ⟨i', rfl⟩ : ∃ i', t' = i' + 1 := ⟨t' - 1, by omega⟩
    rw [logByteS] at hb'
    cases hm' : log[i']? with
    | none => rw [hm'] at hb'; cases hb'
    | some m' =>
      rw [hm'] at hb'
      change msgByte m' a = some b' at hb'
      obtain ⟨bf, hbf, hfb'⟩ := hf i' m' b' hm' (by omega) hb'
      have hi' : i' < log.length := lookup_lt_Some hm'
      have hLle : latestTs (log.take i') a ≤ i' := by
        have := latestTsLe (log.take i') a
        rw [List.length_take] at this
        omega
      have hinstP : (logByte img (log.take i') T0 a).isSome = true := by
        rw [logByteTake img log i' T0 a (by omega) (by omega)]; exact hinst
      have hT0L : T0 ≤ latestTs (log.take i') a := writesLeLatestTs img (log.take i') a T0 hinstP
      have hbf' : logByte img log (latestTs (log.take i') a) a = some bf := by
        rw [← logByteTake img log i' _ a hLle (by omega)]; exact hbf
      have hbp : logByte img (log.take i') t a = some b := by
        rw [logByteTake img log i' t a (by omega) (by omega)]; exact hb
      have htL : t ≤ latestTs (log.take i') a :=
        writesLeLatestTs img (log.take i') a t (by rw [hbp]; rfl)
      exact adBitsLeTrans b bf b' (ih _ (by omega) t b bf hT0t htL hb hbf') hfb'

/-! ### 1f. Preservation across the CAS write-back -/

/-- The closure extends by an appended write whose value is a variant. -/
theorem wlogVariantsFromSnoc (T0 : Nat) (log : List Wmsg) (a8 : Int) (w0 : BitVec 64) (m : Wmsg) :
    wlogVariantsFrom T0 log a8 w0 →
    wmsgVariant a8 w0 m →
    wlogVariantsFrom T0 (log ++ [m]) a8 w0 := by
  intro hv hm i m0 hi hT0
  by_cases hlt : i < log.length
  · rw [lookup_app_l hlt] at hi
    exact hv i m0 hi hT0
  · have hieq : i = log.length := by
      have := lookup_lt_Some hi
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst hieq
    rw [list_lookup_middle rfl] at hi
    injection hi with hi
    subst hi
    exact hm

/-- ... and the discipline by a write derived from the current latest value with bits only
ORed (the new index is above the install by construction). -/
theorem wfreshFromWriteback (T0 : Nat) (img : Image) (log : List Wmsg) (tid : Option Nat)
    (k : WmClass) (pa : PAddr) (acc : MemoryAccessType mem_payload) (fresh w' : BitVec 64)
    (v : BitVec (8 * 8)) :
    logByte img log (latestTs log (paZ pa)) (paZ pa) = some (nthByte (n := 8) fresh 0) →
    update_PTE_Bits fresh acc = some w' →
    v = w' →
    wfreshFrom T0 img log (paZ pa) →
    wfreshFrom T0 img (log ++ [wwriteMsg tid k pa 8 v]) (paZ pa) := by
  intro hlat hup hv hf i m b hi hT0 hb
  by_cases hlt : i < log.length
  · rw [lookup_app_l hlt] at hi
    obtain ⟨bf, hbf, hle⟩ := hf i m b hi hT0 hb
    refine ⟨bf, ?_, hle⟩
    rw [List.take_append_of_le_length (by omega)]
    exact hbf
  · have hieq : i = log.length := by
      have := lookup_lt_Some hi
      simp only [List.length_append, List.length_singleton] at this
      omega
    subst hieq
    rw [list_lookup_middle rfl] at hi
    injection hi with hi
    subst hi
    have hb0 : msgByte (wwriteMsg tid k pa 8 v) (paZ pa) = some (nthByte v 0) := by
      have h := wwriteMsgByte tid k pa 8 v 0 (by omega)
      rwa [WeakInterp.accAddr0] at h
    rw [hb0] at hb
    injection hb with hb
    subst hb hv
    refine ⟨nthByte (n := 8) fresh 0, ?_, pteAdLeByte0 _ _ (updatePTEBitsAdGe fresh v acc hup)⟩
    have htk : (log ++ [wwriteMsg tid k pa 8 v]).take log.length = log := by simp
    rw [htk]
    exact hlat

/-! ### 1g. The clipped capstone -/

/-- Every admissible (non-fetch) read of the window is a variant BELOW the latest word. -/
theorem wadmPteAdLeLatestFrom (s : Wmstate) (rak : AkInfo) (ra : PAddr) (w0 : BitVec 64) (T0 : Nat)
    (w wl : BitVec (8 * 8)) :
    wlogVariantsFrom T0 s.wmLog (paZ ra) w0 →
    wfreshFrom T0 (wimg s) s.wmLog (paZ ra) →
    wwinInstall s.wmLog T0 ra →
    rak.akIfetch = false →
    T0 ≤ s.wmWs.wVrNew →
    wwinLatest s ra wl →
    wadm s rak ra 8 w →
    pteAdLe w wl := by
  intro hvar hfd hinst hif hcov hlat hadm
  obtain ⟨aw, dw, hw⟩ := wadmVariantFrom s rak ra w0 T0 w hvar hinst hif hcov hadm
  obtain ⟨al, dl, hwl⟩ := wwinLatestVariantFrom s ra w0 T0 wl hvar hinst hlat
  obtain ⟨t0, hok0⟩ := hadm 0 (by omega)
  have ht0T0 := wbyteOkGe s rak _ t0 T0 _ hinst.1 hif hcov
    (wwinInstallLogByte (wimg s) s.wmLog T0 ra 0 (by omega) hinst) hok0
  have hb0 := hok0.1
  obtain ⟨tl, hlv⟩ := hlat 0 (by omega)
  have htl := latestValTs _ _ _ _ _ hlv
  have hbl := hlv.1
  have hinst0 := wwinInstallLogByte (wimg s) s.wmLog T0 ra 0 (by omega) hinst
  rw [WeakInterp.accAddr0] at hb0 htl hbl hinst0
  have hble : adBitsLe (nthByte w 0) (nthByte wl 0) :=
    wfreshFromMono T0 (wimg s) s.wmLog (paZ ra) hinst.1 hinst0 hfd tl t0 _ _ ht0T0
      (by rw [← htl]; exact writesLeLatestTs _ _ _ _ (by rw [hb0]; rfl)) hb0 hbl
  exact pteAdLeOfByte0 w0 w wl ⟨aw, dw, hw⟩ ⟨al, dl, hwl⟩ hble

/-! ## 2. The kperm eff twins (deviation 3) -/

theorem wkpermInvRed (pc : KPerm) (a d : BitVec 1) : ∀ s,
    execEff (pte_is_invalid (Mk_PTE_Flags (_update_PTE_Flags_D (_update_PTE_Flags_A pc.flags a) d))
      0#10) s = some (false, s, []) := by
  intro s
  cases pc <;> rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;> rfl

theorem wkpermCheckFetch (a d : BitVec 1) : ∀ (mxr dosum : Bool) s,
    execEff (check_PTE_permission (.InstructionFetch ()) .Supervisor mxr dosum
      (Mk_PTE_Flags (_update_PTE_Flags_D (_update_PTE_Flags_A KPerm.rx.flags a) d)) 0#10 ()) s =
      some (.PTE_Check_Success (), s, []) := by
  intro mxr dosum s
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;>
    cases mxr <;> cases dosum <;> rfl

theorem wkpermCheckLoad (pc : KPerm) (a d : BitVec 1) : ∀ (mxr dosum : Bool) s,
    execEff (check_PTE_permission (.Load .Data) .Supervisor mxr dosum
      (Mk_PTE_Flags (_update_PTE_Flags_D (_update_PTE_Flags_A pc.flags a) d)) 0#10 ()) s =
      some (.PTE_Check_Success (), s, []) := by
  intro mxr dosum s
  cases pc <;> rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;>
    cases mxr <;> cases dosum <;> rfl

theorem wkpermCheckStore (a d : BitVec 1) : ∀ (mxr dosum : Bool) s,
    execEff (check_PTE_permission (.Store .Data) .Supervisor mxr dosum
      (Mk_PTE_Flags (_update_PTE_Flags_D (_update_PTE_Flags_A KPerm.rw.flags a) d)) 0#10 ()) s =
      some (.PTE_Check_Success (), s, []) := by
  intro mxr dosum s
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;>
    cases mxr <;> cases dosum <;> rfl

theorem wkpermCheckAmo (a d : BitVec 1) (aq rl : Bool) : ∀ (mxr dosum : Bool) s,
    execEff (check_PTE_permission (.Atomic (.AMOSWAP, aq, rl, .Data, .Data)) .Supervisor mxr dosum
      (Mk_PTE_Flags (_update_PTE_Flags_D (_update_PTE_Flags_A KPerm.rw.flags a) d)) 0#10 ()) s =
      some (.PTE_Check_Success (), s, []) := by
  intro mxr dosum s
  rcases bv1_cases a with rfl | rfl <;> rcases bv1_cases d with rfl | rfl <;>
    cases aq <;> cases rl <;> cases mxr <;> cases dosum <;> rfl

/-- Every A/D variant of a class-keyed leaf is eff-valid. -/
theorem wkpermVariantValid (ppn : BitVec 44) (pc : KPerm) (a d : BitVec 1) :
    wpteValid (pteSetAD (mkPte ppn pc.flags) a d) := by
  intro s
  rw [show pteSetAD (mkPte ppn pc.flags) a d = kLeaf ppn pc a d from rfl, flags_of_kLeaf,
    ext_of_kLeaf]
  exact wkpermInvRed pc a d s

/-- Rocq `KptPt.kperm_allows` (Lean-only twin, deviation 3): fetch only from text (R|X),
loads from both, everything else only to R|W pages. -/
def WeakKpt.kpermAllows (pc : KPerm) (acc : MemoryAccessType mem_payload) : Prop :=
  match acc with
  | .InstructionFetch _ => pc = .rx
  | .Load _ => True
  | _ => pc = .rw

/-- The class-keyed eff check dispatcher. -/
theorem wkpermVariantCheck (ppn : BitVec 44) (pc : KPerm) (acc : MemoryAccessType mem_payload)
    (a d : BitVec 1) (mxr dosum : Bool) :
    (acc = .InstructionFetch () ∨ acc = .Load .Data ∨ acc = .Store .Data ∨
      (∃ aq rl, acc = .Atomic (.AMOSWAP, aq, rl, .Data, .Data))) →
    WeakKpt.kpermAllows pc acc →
    wpteCheckOk acc .Supervisor mxr dosum (pteSetAD (mkPte ppn pc.flags) a d) := by
  intro hacc hall s
  rw [show pteSetAD (mkPte ppn pc.flags) a d = kLeaf ppn pc a d from rfl, flags_of_kLeaf,
    ext_of_kLeaf]
  rcases hacc with rfl | rfl | rfl | ⟨aq, rl, rfl⟩
  · have h : pc = .rx := hall
    subst h
    exact wkpermCheckFetch a d mxr dosum s
  · exact wkpermCheckLoad pc a d mxr dosum s
  · have h : pc = .rw := hall
    subst h
    exact wkpermCheckStore a d mxr dosum s
  · have h : pc = .rw := hall
    subst h
    exact wkpermCheckAmo a d aq rl mxr dosum s

/-! ## 3. The invariant and the per-hart residue -/

/-- The namespace. -/
def wkptN : Namespace := ndot nroot "weakkpt"

/-- The pure per-slot geometry the SC tier derived from the physical-tier points-to
(deviation 6). -/
def wslotGeom (a : PAddr) : Prop :=
  inRam a 8 ∧ is_aligned_paddr (.Physaddr a) 8 = true

/-- An in-RAM 8-byte window does not wrap. -/
theorem wslotGeomAccWf (a : PAddr) : wslotGeom a → accWf a 8 := by
  rintro ⟨⟨_, h2⟩, _⟩
  unfold accWf paZ
  simp only [ramEnd] at h2
  omega

/-! ### 3-pre. The SC vocabulary the invariant is stated over (deviation 4) -/

/-- The ghost name of the canonical-table snapshot (Rocq `kpt_name` in `riscvGS`). -/
class WeakKpt.KptGS (GF : BundledGFunctors) where
  [varG : GhostVarG GF PTree]
  kptName : GName

attribute [reducible, instance] WeakKpt.KptGS.varG

/-- Rocq `PtTree.ptree_set_leaf_blocks` (Lean-only twin): a write-back on a mapped path keeps
every blocked vpn blocked. -/
theorem WeakKpt.ptreeSetLeafBlocks (t : PTree) (vpn vpn' : BitVec 27) (p2 p1 p0 w : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    WeakWalkEff.ptreeBlocks t vpn' →
    WeakWalkEff.ptreeBlocks (AxPtProt.ptreeSetLeaf t vpn w) vpn' := by
  rintro ⟨c1, c0, hk2, hk1, -, -, he0, -, -, -, -, -, -, hv0, -⟩ hbl
  simp only [AxPtProt.ptreeSetLeaf, hk2, hk1]
  unfold WeakWalkEff.ptreeBlocks at hbl ⊢
  simp only [AxPtProt.ptUpdKid, AxPtProt.kidsNode, AxPtProt.entsNode]
  rcases hbl with ⟨hn2, hi2⟩ | ⟨d1, hd2, hd1, hv2', hp2', hb1', hi1'⟩ |
      ⟨d1, d0, hd2, hd1, hv2', hp2', hv1', hp1', hb1', hb0', hi0'⟩
  · left
    by_cases ei2 : AxPtProt.vpnIdx 2 vpn' = AxPtProt.vpnIdx 2 vpn
    · rw [ei2, hk2] at hn2; cases hn2
    · rw [if_neg ei2]; exact ⟨hn2, hi2⟩
  · right; left
    by_cases ei2 : AxPtProt.vpnIdx 2 vpn' = AxPtProt.vpnIdx 2 vpn
    · rw [ei2, hk2] at hd2
      cases hd2
      by_cases ei1 : AxPtProt.vpnIdx 1 vpn' = AxPtProt.vpnIdx 1 vpn
      · rw [ei1, hk1] at hd1; cases hd1
      · refine ⟨AxPtProt.ptUpdKid c1 (AxPtProt.vpnIdx 1 vpn)
          (some (AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w)), ?_, ?_, hv2', hp2', ?_, hi1'⟩
        · rw [if_pos ei2]; rfl
        · simp only [AxPtProt.ptUpdKid, AxPtProt.kidsNode]
          rw [if_neg ei1]; exact hd1
        · simp only [AxPtProt.ptUpdKid, PTree.base_node]; exact hb1'
    · refine ⟨d1, ?_, hd1, hv2', hp2', hb1', hi1'⟩
      rw [if_neg ei2]; exact hd2
  · right; right
    by_cases ei2 : AxPtProt.vpnIdx 2 vpn' = AxPtProt.vpnIdx 2 vpn
    · rw [ei2, hk2] at hd2
      cases hd2
      by_cases ei1 : AxPtProt.vpnIdx 1 vpn' = AxPtProt.vpnIdx 1 vpn
      · rw [ei1, hk1] at hd1
        cases hd1
        by_cases ei0 : AxPtProt.vpnIdx 0 vpn' = AxPtProt.vpnIdx 0 vpn
        · exfalso
          rw [ei0, he0] at hi0'
          exact WeakWalkEff.pteValidInvalidExcl p0 hv0 hi0'
        · refine ⟨AxPtProt.ptUpdKid c1 (AxPtProt.vpnIdx 1 vpn)
            (some (AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w)),
            AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w, ?_, ?_, hv2', hp2', hv1', hp1', ?_, ?_, ?_⟩
          · rw [if_pos ei2]; rfl
          · simp only [AxPtProt.ptUpdKid, AxPtProt.kidsNode]
            rw [if_pos ei1]
          · simp only [AxPtProt.ptUpdKid, PTree.base_node]; exact hb1'
          · simp only [AxPtProt.ptUpdKid, AxPtProt.entsNode, AxPtProt.ptUpdEnt, PTree.base_node]
            exact hb0'
          · simp only [AxPtProt.ptUpdEnt, AxPtProt.entsNode]
            rw [if_neg ei0]; exact hi0'
      · refine ⟨AxPtProt.ptUpdKid c1 (AxPtProt.vpnIdx 1 vpn)
          (some (AxPtProt.ptUpdEnt c0 (AxPtProt.vpnIdx 0 vpn) w)), d0, ?_, ?_, hv2', hp2', ?_, ?_,
          ?_, hb0', hi0'⟩
        · rw [if_pos ei2]; rfl
        · simp only [AxPtProt.ptUpdKid, AxPtProt.kidsNode]
          rw [if_neg ei1]; exact hd1
        · simp only [AxPtProt.ptUpdKid, AxPtProt.entsNode]; exact hv1'
        · simp only [AxPtProt.ptUpdKid, AxPtProt.entsNode]; exact hp1'
        · simp only [AxPtProt.ptUpdKid, PTree.base_node]; exact hb1'
    · refine ⟨d1, d0, ?_, hd1, hv2', hp2', hv1', hp1', hb1', hb0', hi0'⟩
      rw [if_neg ei2]; exact hd2

/-- Lean-only: the write-back keeps the root. -/
theorem WeakKpt.ptreeSetLeafBase (t : PTree) (vpn : BitVec 27) (w : BitVec 64) :
    (AxPtProt.ptreeSetLeaf t vpn w).base = t.base := by
  unfold AxPtProt.ptreeSetLeaf
  split
  · split
    · rfl
    · rfl
  · rfl

/-- Rocq `KptTree.kpt_tree_spec_gen` (deviation 4): the tree agrees with the mapping -- an
entry is mapped as an A/D variant of its canonical leaf, everything else BLOCKS. -/
def WeakKpt.kptTreeSpecGen (root : BitVec 44) (M : RegMapF (BitVec 64)) (t : PTree) : Prop :=
  t.base = root ∧
  (∀ (k : Nat) (v : BitVec 64), get? M k = some v → k < 2 ^ 27) ∧
  ∀ vpn : BitVec 27,
    match get? M vpn.toNat with
    | some e => ∃ (p2 p1 : BitVec 64) (a d : BitVec 1),
        AxPtProt.ptreeMaps t vpn p2 p1 (pteSetAD e a d)
    | none => WeakWalkEff.ptreeBlocks t vpn

/-- Rocq `KptTree.kpt_tree_spec_gen_set_leaf`: the spec survives the write-back of any mapped
vpn's leaf. -/
theorem WeakKpt.kptTreeSpecGenSetLeaf (root : BitVec 44) (M : RegMapF (BitVec 64)) (t : PTree)
    (vpn : BitVec 27) (e : BitVec 64) (p2 p1 p0 : BitVec 64) (a d : BitVec 1) :
    WeakKpt.kptTreeSpecGen root M t →
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    get? M vpn.toNat = some e →
    (∃ a0 d0 : BitVec 1, p0 = pteSetAD e a0 d0) →
    WeakKpt.kptTreeSpecGen root M (AxPtProt.ptreeSetLeaf t vpn (pteSetAD p0 a d)) := by
  rintro ⟨hbase, hkeys, hall⟩ hmaps he ⟨a0, d0, hp0⟩
  have hvar : pteSetAD p0 a d = pteSetAD e a d := by rw [hp0, pteSetAD_pteSetAD]
  refine ⟨by rw [WeakKpt.ptreeSetLeafBase]; exact hbase, hkeys, fun vpn' => ?_⟩
  by_cases hne : vpn' = vpn
  · subst hne
    rw [he]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv0, hl0, hn0, hpb0⟩ := id hmaps
    have hself := AxPtProt.ptreeSetLeafMapsSelf t vpn' p2 p1 p0 (pteSetAD p0 a d) hmaps
      ((AxPtProt.pteSetAdValidLeaf p0 a d hl0).2 hv0) ((AxPtProt.pteSetAdLeaf p0 a d).2 hl0)
      ((AxPtProt.pteSetAdNoNapot p0 a d).2 hn0) ((AxPtProt.pteSetAdPbmt0 p0 a d).2 hpb0)
    refine ⟨p2, p1, a, d, ?_⟩
    rw [hvar] at hself ⊢
    exact hself
  · have h := hall vpn'
    revert h
    cases get? M vpn'.toNat with
    | some e' =>
      rintro ⟨q2, q1, a', d', hm2⟩
      exact ⟨q2, q1, a', d', AxPtProt.ptreeSetLeafMapsOther t vpn vpn' _ _ _ _ hne hm2⟩
    | none =>
      intro h
      exact WeakKpt.ptreeSetLeafBlocks t vpn vpn' p2 p1 p0 _ hmaps h

/-- Rocq `PtTree.tlb_ok_pt_fill_self` (Lean-only twin). -/
theorem WeakKpt.tlbOkPtFillSelf (asid : BitVec 16) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (vpn : BitVec 27) (p2 p1 p0 : BitVec 64) :
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    AxPtProt.tlbOkPt asid t tlbvec →
    AxPtProt.tlbOkPt asid t (vectorUpdate tlbvec (tlb_hash 39 vpn)
      (some (uWalkEntry vpn p2 p1 p0 asid))) :=
  fun hmaps hok => AxPtProt.tlbOkPtFill asid t tlbvec vpn p2 p1 p0 p0 hmaps (pteAD_refl p0) hok

/-- Rocq `PtTree.uwe_match_self` (Lean-only twin): a walk entry matches its own vpn. -/
theorem WeakKpt.uweMatchSelf (vpn : BitVec 27) (p2 p1 q0 : BitVec 64) (asid : BitVec 16) :
    match_TLB_Entry (uWalkEntry vpn p2 p1 q0 asid) asid (sign_extend (m := 57 - 12) vpn) = true := by
  unfold match_TLB_Entry uWalkEntry ptFillEnt
  simp only [zero_extend, sign_extend, ones, Sail.BitVec.zeroExtend, Sail.BitVec.signExtend]
  have h1 : sail_ones 0 = 0#0 := by decide
  rw [h1]
  simp only [beq_self_eq_true, Bool.or_true, Bool.true_and, beq_iff_eq]
  bv_decide

/-- Rocq `RiscvPtsto.svpn_of`: the vpn `translateAddr` walks for `va` (the spelling of
`WeakWalkEff.execEffTranslateAddrPtFront`'s `hvpn`). -/
def WeakKpt.svpnOf (va : BitVec 64) : BitVec 27 :=
  BitVec.setWidth 27 (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb va 38 0) 38 Functions.pagesize_bits)

/-- Rocq `KptPt.pma_allows_pte_read` (Lean-only twin, deviation 4). -/
def WeakKpt.pmaAllowsPteRead (regions : List PMA_Region) : Prop :=
  ∀ a : BitVec 64, inRam a 8 → ∃ r, matching_pma_region regions (.Physaddr a) 8 = some r ∧
    (override_PMA r.attributes .PBMT_PMA).supports_pte_read = true

/-- Rocq `PtTreeAdue.pma_allows_pte_write` (Lean-only twin, deviation 4). -/
def WeakKpt.pmaAllowsPteWrite (regions : List PMA_Region) : Prop :=
  ∀ a : BitVec 64, inRam a 8 → ∃ r, matching_pma_region regions (.Physaddr a) 8 = some r ∧
    (override_PMA r.attributes .PBMT_PMA).supports_pte_write = true

/-- Rocq `pma_allows_all_pte_read`, at the platform table. -/
theorem WeakKpt.pmaAllowsBootPteRead : WeakKpt.pmaAllowsPteRead bootPMA :=
  fun a h => ⟨ramRegion, matching_pma_ram a 8 h (by omega) (by omega), rfl⟩

/-- Rocq `pma_allows_all_pte_write`, at the platform table. -/
theorem WeakKpt.pmaAllowsBootPteWrite : WeakKpt.pmaAllowsPteWrite bootPMA :=
  fun a h => ⟨ramRegion, matching_pma_ram a 8 h (by omega) (by omega), rfl⟩

section WeakKptInv

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF] [WeakKpt.KptGS GF]

/-- Rocq `KptGhost.kpt_lb` (deviation 4): the persistent snapshot of the canonical table. -/
def WeakKpt.kptLb (t : PTree) : IProp GF :=
  WeakKpt.KptGS.kptName (GF := GF) ↪VAR{DFrac.discard} (AxPtProt.ptreeCanon t)

instance kpt_lb_persistent (t : PTree) : Persistent (WeakKpt.kptLb (GF := GF) t) := by
  unfold WeakKpt.kptLb; infer_instance

instance kpt_lb_timeless (t : PTree) : Timeless (WeakKpt.kptLb (GF := GF) t) := by
  unfold WeakKpt.kptLb; infer_instance

/-- Rocq `KptGhost.kpt_lb_agree`. -/
theorem WeakKpt.kptLbAgree (t t' : PTree) :
    WeakKpt.kptLb (GF := GF) t ∗ WeakKpt.kptLb t' ⊢
      ⌜AxPtProt.ptreeCanon t = AxPtProt.ptreeCanon t'⌝ := by
  unfold WeakKpt.kptLb
  iintro ⟨H1, H2⟩
  iapply ghost_var_agree $$ H1 H2

/-- Rocq `KptGhost.kpt_lb_canon`. -/
theorem WeakKpt.kptLbCanon (t t' : PTree) :
    AxPtProt.ptreeCanon t = AxPtProt.ptreeCanon t' → WeakKpt.kptLb (GF := GF) t ⊢ WeakKpt.kptLb t' := by
  intro he
  unfold WeakKpt.kptLb
  rw [he]

/-- Rocq `KMap.kmap_auth` (deviation 4): the published mapping authority. -/
def WeakKpt.kmapAuth (M : RegMapF (BitVec 64)) : IProp GF :=
  MachGS.kmapName (hlc := hlc) (GF := GF) ↪●MAP{DFrac.discard} M

instance kmap_auth_persistent (M : RegMapF (BitVec 64)) :
    Persistent (WeakKpt.kmapAuth (hlc := hlc) (GF := GF) M) := by
  unfold WeakKpt.kmapAuth; infer_instance

instance kmap_auth_timeless (M : RegMapF (BitVec 64)) :
    Timeless (WeakKpt.kmapAuth (hlc := hlc) (GF := GF) M) := by
  unfold WeakKpt.kmapAuth; infer_instance

/-- Rocq `KMap.kmap_at_lookup`: a claim agrees with the auth. -/
theorem WeakKpt.kmapAtLookup (M : RegMapF (BitVec 64)) (vpn : BitVec 27) (ppn : BitVec 44)
    (pc : KPerm) :
    WeakKpt.kmapAuth (hlc := hlc) (GF := GF) M ∗ kmapAt (hlc := hlc) vpn (kLeaf ppn pc 0#1 0#1) ⊢
      ⌜get? M vpn.toNat = some (kLeaf ppn pc 0#1 0#1)⌝ := by
  unfold WeakKpt.kmapAuth kmapAt
  iintro ⟨Ha, Hf⟩
  iapply ghost_map_lookup $$ Ha Hf

/-- Rocq `KptShare.tlb_snap_ok`: the hart's TLB coherence against a SNAPSHOT. -/
def WeakKpt.tlbSnapOk (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) : IProp GF :=
  iprop(∃ t0 : PTree, ⌜AxPtProt.tlbOkPt 0#16 t0 tlbvec⌝ ∗ WeakKpt.kptLb (GF := GF) t0)

/-- Rocq `SmodeCore.pmp_config` (deviation 4). -/
def WeakKpt.pmpConfig (cpu : CPU) (root : BitVec 44) : IProp GF :=
  iprop(∃ (pmpcfg0 : RegisterType Register.pmpcfg_n) (pmpaddr00 : RegisterType Register.pmpaddr_n),
    Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 ∗ Register.pmpaddr_n ↦ᵣ[cpu] pmpaddr00 ∗
    ⌜pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A pmpcfg0[0]!) = .TOR⌝ ∗
    ⌜zopz0zKzJ_u (zeros (n := 64)) pmpaddr00[0]! = false⌝ ∗
    ⌜(_get_Pmpcfg_ent_X pmpcfg0[0]! == 1#1) = true⌝ ∗
    ⌜(_get_Pmpcfg_ent_W pmpcfg0[0]! == 1#1) = true⌝ ∗
    ⌜(_get_Pmpcfg_ent_R pmpcfg0[0]! == 1#1) = true⌝ ∗
    ⌜ramEnd ≤ pmpaddr00[0]!.toNat * 4⌝)

/-- Rocq `SmodeCore.pmp_config_intro`. -/
theorem WeakKpt.pmpConfigIntro (cpu : CPU) (root : BitVec 44)
    (pmpcfg0 : RegisterType Register.pmpcfg_n) (pmpaddr00 : RegisterType Register.pmpaddr_n) :
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A pmpcfg0[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) pmpaddr00[0]! = false →
    (_get_Pmpcfg_ent_X pmpcfg0[0]! == 1#1) = true →
    (_get_Pmpcfg_ent_W pmpcfg0[0]! == 1#1) = true →
    (_get_Pmpcfg_ent_R pmpcfg0[0]! == 1#1) = true →
    ramEnd ≤ pmpaddr00[0]!.toNat * 4 →
    Register.pmpcfg_n ↦ᵣ[cpu] pmpcfg0 ∗ Register.pmpaddr_n ↦ᵣ[cpu] pmpaddr00 ⊢
      WeakKpt.pmpConfig (hlc := hlc) (GF := GF) cpu root := by
  intro hA hord hX hW hR hcov
  unfold WeakKpt.pmpConfig
  iintro ⟨Hc, Ha⟩
  iexists pmpcfg0, pmpaddr00
  iframe Hc Ha
  ipureintro
  exact ⟨hA, hord, hX, hW, hR, hcov⟩

/-! ### 3a. The POINTER-slot resource: persistent, kvminit-timestamped -/

def wptr8 (T_kpt : Nat) (a : PAddr) (w : BitVec 64) : IProp GF :=
  iprop(∃ ts : Nat, ⌜ts ≤ T_kpt⌝ ∗ ⌜wslotGeom a⌝ ∗ ⌜wpteValid w⌝ ∗
    wlat8 (GF := GF) a DFrac.discard ts w)

instance wlat8_discarded_persistent (a : PAddr) (t : Nat) (w : BitVec 64) :
    Persistent (wlat8 (GF := GF) a DFrac.discard t w) := by
  unfold wlat8 wlatPointsto wlatElem wclean wcdsEl; infer_instance

instance wptr8_persistent (T_kpt : Nat) (a : PAddr) (w : BitVec 64) :
    Persistent (wptr8 (GF := GF) T_kpt a w) := by
  unfold wptr8; infer_instance

instance wptr8_timeless (T_kpt : Nat) (a : PAddr) (w : BitVec 64) :
    Timeless (wptr8 (GF := GF) T_kpt a w) := by
  unfold wptr8; infer_instance

/-! ### 3b. The LEAF-window resource: exclusive, closure-carrying -/

def wleafRes (T_kpt : Nat) (la : PAddr) (w0 : BitVec 64) (a d : BitVec 1) : IProp GF :=
  iprop(∃ (ts T0 : Nat) (log0 : List Wmsg),
    ⌜wslotGeom la⌝ ∗
    ⌜1 ≤ T0 ∧ T0 ≤ T_kpt ∧ T0 ≤ ts ∧ ts ≤ log0.length⌝ ∗
    ⌜wwinInstall log0 T0 la⌝ ∗
    ⌜wlogVariantsFrom T0 log0 (paZ la) w0⌝ ∗
    ⌜∀ img : Image, wfreshFrom T0 img log0 (paZ la)⌝ ∗
    wlogLb (GF := GF) log0 ∗
    wlat8 (GF := GF) la (DFrac.own 1) ts (pteSetAD w0 a d))

instance wleaf_res_timeless (T_kpt : Nat) (la : PAddr) (w0 : BitVec 64) (a d : BitVec 1) :
    Timeless (wleafRes (GF := GF) T_kpt la w0 a d) := by
  unfold wleafRes; infer_instance

/-! ### 3c. The per-vpn bundle -/

def wvpnRes (T_kpt : Nat) (t : PTree) (vpn : BitVec 27) (e : BitVec 64) : IProp GF :=
  iprop(∃ (p2 p1 : BitVec 64) (a d : BitVec 1),
    ⌜AxPtProt.ptreeMaps t vpn p2 p1 (pteSetAD e a d)⌝ ∗
    wptr8 (GF := GF) T_kpt (AxPtProt.ptAddr2 t vpn) p2 ∗
    wptr8 (GF := GF) T_kpt (AxPtProt.ptAddr1 p2 vpn) p1 ∗
    wleafRes (GF := GF) T_kpt (AxPtProt.ptAddr0 p1 vpn) e a d)

instance wvpn_res_timeless (T_kpt : Nat) (t : PTree) (vpn : BitVec 27) (e : BitVec 64) :
    Timeless (wvpnRes (GF := GF) T_kpt t vpn e) := by
  unfold wvpnRes; infer_instance

/-! ### 3d. The body and the invariant -/

def wkptBody (root : BitVec 44) (T_kpt : Nat) : IProp GF :=
  iprop(∃ (t : PTree) (M : RegMapF (BitVec 64)),
    WeakKpt.kptLb (GF := GF) t ∗
    WeakKpt.kmapAuth (hlc := hlc) (GF := GF) M ∗
    ⌜WeakKpt.kptTreeSpecGen root M t⌝ ∗
    ([∗map] k ↦ e ∈ M, wvpnRes (GF := GF) T_kpt t (BitVec.ofNat 27 k) e))

instance wkpt_body_timeless (root : BitVec 44) (T_kpt : Nat) :
    Timeless (wkptBody (hlc := hlc) (GF := GF) root T_kpt) := by
  unfold wkptBody; infer_instance

def wkptInv (root : BitVec 44) (T_kpt : Nat) : IProp GF :=
  inv wkptN (wkptBody (hlc := hlc) (GF := GF) root T_kpt)

instance wkpt_inv_persistent (root : BitVec 44) (T_kpt : Nat) :
    Persistent (wkptInv (hlc := hlc) (GF := GF) root T_kpt) := by
  unfold wkptInv; infer_instance

theorem wkptInvAlloc (root : BitVec 44) (T_kpt : Nat) (E : CoPset) :
    wkptBody (hlc := hlc) (GF := GF) root T_kpt ⊢ |={E}=> wkptInv (hlc := hlc) (GF := GF) root T_kpt := by
  iintro Hbody
  unfold wkptInv
  imod inv_alloc wkptN E (wkptBody (hlc := hlc) (GF := GF) root T_kpt) $$ [Hbody] with #Hinv
  · iapply later_intro
    iexact Hbody
  imodintro
  iexact Hinv

/-! ### 3e. The per-hart residue: `KptShare.tlb_res_pt`'s mirror -/

def wtlbResPt (cpu : CPU) (root : BitVec 44) (T_kpt : Nat) : IProp GF :=
  iprop(∃ (satp0 : BitVec 64) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)),
    Register.satp ↦ᵣ[cpu] satp0 ∗
    ⌜_get_Satp64_Mode (Mk_Satp64 satp0) = 8#4⌝ ∗
    ⌜zero_extend (m := 16) (satp_to_asid satp0) = 0#16⌝ ∗
    ⌜BitVec.setWidth 44 (satp_to_ppn satp0) = root⌝ ∗
    Register.tlb ↦ᵣ[cpu] tlbvec ∗ WeakKpt.tlbSnapOk (GF := GF) tlbvec ∗
    WeakKpt.pmpConfig (hlc := hlc) (GF := GF) cpu root ∗
    wkptInv (hlc := hlc) (GF := GF) root T_kpt)

theorem wtlbResPtIntro (cpu : CPU) (root : BitVec 44) (T_kpt : Nat) (satp0 : BitVec 64)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (t0 : PTree) :
    _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4 →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = root →
    AxPtProt.tlbOkPt 0#16 t0 tlbvec →
    Register.satp ↦ᵣ[cpu] satp0 ∗ Register.tlb ↦ᵣ[cpu] tlbvec ∗ WeakKpt.kptLb (GF := GF) t0 ∗
      WeakKpt.pmpConfig (hlc := hlc) (GF := GF) cpu root ∗ wkptInv (hlc := hlc) (GF := GF) root T_kpt ⊢
      wtlbResPt (hlc := hlc) (GF := GF) cpu root T_kpt := by
  intro hmode hasid hppn hok
  unfold wtlbResPt WeakKpt.tlbSnapOk
  iintro ⟨Hsatp, Htlb, Hlb, Hpmp, Hinv⟩
  iexists satp0, tlbvec
  iframe Hsatp Htlb Hpmp Hinv
  isplitr
  · ipureintro; exact hmode
  isplitr
  · ipureintro; exact hasid
  isplitr
  · ipureintro; exact hppn
  iexists t0
  iframe Hlb
  ipureintro
  exact hok

end WeakKptInv

/-! ## 4. The pure dispatch: `KptTree.ptree_translateAddr_cases` at `execEff`

Outcomes (and their traces): O1 TLB hit, cached variant needs no bits -- `[]`; O2 miss, walk +
fill, leaf needs no bits -- the 3 plain reads; O2' hit, cached variant needs bits, memory
doesn't -- the CAS read; O3 write-back + fill (miss) / refresh (hit) -- reads + CAS pair. -/

/-- Rocq `wptree_translate_miss_eff_core`: the shared miss path -- the TLB slot misses, so the
walk runs, filling cleanly (O2) or writing the A/D update back (O3). -/
theorem wptreeTranslateMissEffCore (acc : MemoryAccessType mem_payload) (p : Privilege)
    (root : BitVec 44) (va w : BitVec 64) (tlbvec : Vector (Option TLB_Entry) (2 ^ 6))
    (p2 p1 : BitVec 64) (a0 d0 : BitVec 1) (sg : ExecSt) :
    let vpn := WeakKpt.svpnOf va
    let p0 := pteSetAD w a0 d0
    (∀ (a d : BitVec 1) (mxr dosum : Bool), wpteCheckOk acc p mxr dosum (pteSetAD w a d)) →
    (∀ a d : BitVec 1, wpteValid (pteSetAD w a d)) →
    wpteValid p2 → ptePtr p2 →
    wpteValid p1 → ptePtr p1 →
    pteLeaf p0 → AxPtProt.pteNoNapot p0 →
    WeakWalkEff.ptSlotMem sg (AxPtProt.ptAddr0 p1 vpn) p0 →
    execEff (read_pte (.Physaddr (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18))) 8) sg =
      some (.Ok p2, sg, [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8]) →
    execEff (read_pte (.Physaddr (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9))) 8) sg =
      some (.Ok p1, sg, [.WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8]) →
    execEff (read_pte (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) sg =
      some (.Ok p0, sg, [.WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) →
    execEff (read_pte_exclusive (.Physaddr (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))) 8) sg =
      some (.Ok p0, sg,
        [.WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) →
    sg.regs .misa = misaC →
    sg.regs .menvcfg = menvcfgS →
    sg.regs .htif_tohost_base = none →
    sg.regs .tlb = tlbvec →
    execEff (lookup_TLB 39 0#16 vpn) sg = some (none, sg, []) →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_W (sg.regs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4 →
    WeakKpt.pmaAllowsPteWrite (sg.regs .pma_regions) →
    ∃ (sg' : ExecSt) (es : List Weff),
      (∀ mxr dosum, execEff (translate 39 0#16 root vpn acc p mxr dosum ()) sg =
        some (.Ok (ppn0 p0, .PBMT_PMA, ()), sg', es)) ∧
      ((sg' = sg.setReg .tlb (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0 0#16))) ∧
        es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
              .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
              .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8]) ∨
       (∃ a1 d1 : BitVec 1,
          update_PTE_Bits p0 acc = some (pteSetAD p0 a1 d1) ∧
          sg' = (sg.setMem (bmWrite sg.mem (AxPtProt.ptAddr0 p1 vpn) 8 (pteSetAD p0 a1 d1))).setReg .tlb
            (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD p0 a1 d1) 0#16))) ∧
          es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                .WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                .WEwrite ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8
                  (pteSetAD p0 a1 d1)])) := by
  intro vpn p0 hchk hval hwv2 hn2 hwv1 hn1 hl0 hnap hsm0 hrd2 hrd1 hrd0 hrdx hmisa hmenv hhtif htlbv hlk
    hA hord hW hcov hpmaw
  have hpbmte : (_get_MEnvcfg_PBMTE menvcfgS == 0#1) = true := by decide
  have hadue : (_get_MEnvcfg_ADUE menvcfgS == 1#1) = true := by decide
  cases hup : update_PTE_Bits p0 acc with
  | some p0' =>
    -- O3: the walk writes the A/D-updated leaf back
    obtain ⟨_, hram0, hal0⟩ := hsm0
    obtain ⟨region0, hm0, hw0⟩ := hpmaw _ hram0
    have hwr := execEffWritePteConditionalRam (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))
      p0' region0 sg hram0 hal0 hA hord hW hcov hm0 hw0 hhtif
    obtain ⟨a1, d1, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hup
    subst hq
    refine ⟨(sg.setMem (bmWrite sg.mem (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8
        (pteSetAD p0 a1 d1))).setReg .tlb
        (vectorUpdate (sg.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD p0 a1 d1) 0#16))),
      _, fun mxr dosum => execEffTranslateMissUser vpn root 0#16 acc p mxr dosum _ sg _ _ hlk
        (execEffTranslateTLBMissUserUpd acc p mxr dosum vpn root p2 p1 p0 _ menvcfgS 0#16 _ _ _ _ _ _ sg
          hwv2 hn2 hwv1 hn1 (hval a0 d0) hl0 (hchk a0 d0 mxr dosum) hnap hup hrd2 hrd1 hrd0 hrdx hmisa hmenv
          hpbmte hadue hwr rfl),
      Or.inr ⟨a1, d1, rfl, by rw [htlbv]; rfl, rfl⟩⟩
  | none =>
    -- O2: clean fill
    refine ⟨sg.setReg .tlb (vectorUpdate (sg.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0 0#16))),
      _, fun mxr dosum => execEffTranslateMissUser vpn root 0#16 acc p mxr dosum _ sg _ _ hlk
        (execEffTranslateTLBMissUser vpn root p2 p1 p0 acc p mxr dosum hwv2 hn2 hwv1 hn1 (hval a0 d0) hl0
          (hchk a0 d0 mxr dosum) hnap 0#16 menvcfgS _ _ _ sg hmisa hup hrd2 hrd1 hrd0 hmenv hpbmte),
      Or.inl ⟨by rw [htlbv], rfl⟩⟩

/-- Rocq `wptree_translateAddr_eff_cases`: the total translation case analysis over the
walk-path facts, at an abstract SC state `sg`, with the EXACT per-outcome trace. -/
theorem wptreeTranslateAddrEffCases (acc : MemoryAccessType mem_payload) (p : Privilege)
    (root : BitVec 44) (va w pa satp0 : BitVec 64) (t : PTree)
    (tlbvec : Vector (Option TLB_Entry) (2 ^ 6)) (p2 p1 : BitVec 64) (a0 d0 : BitVec 1) (sg : ExecSt) :
    let vpn := WeakKpt.svpnOf va
    let p0 := pteSetAD w a0 d0
    (∀ (a d : BitVec 1) (mxr dosum : Bool), wpteCheckOk acc p mxr dosum (pteSetAD w a d)) →
    (∀ a d : BitVec 1, wpteValid (pteSetAD w a d)) →
    (va != sign_extend (m := 64) (Sail.BitVec.extractLsb va 38 0)) = false →
    zero_extend (m := 64) (ppn0 w +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa →
    (∀ a d : BitVec 1, ptePbmt0 (pteSetAD w a d)) →
    wpteValid p2 → wpteValid p1 →
    t.base = root →
    AxPtProt.ptreeMaps t vpn p2 p1 p0 →
    AxPtProt.tlbOkPt 0#16 t tlbvec →
    WeakWalkEff.ptSlotMem sg (AxPtProt.ptAddr2 t vpn) p2 →
    WeakWalkEff.ptSlotMem sg (AxPtProt.ptAddr1 p2 vpn) p1 →
    WeakWalkEff.ptSlotMem sg (AxPtProt.ptAddr0 p1 vpn) p0 →
    sg.regs .misa = misaC →
    sg.regs .menvcfg = menvcfgS →
    sg.regs .htif_tohost_base = none →
    sg.regs .cur_privilege = p →
    execEff (translationMode p) sg = some (.Sv39, sg, []) →
    execEff (effectivePrivilege acc (sg.regs .mstatus) p) sg = some (p, sg, []) →
    execEff (is_shadow_stack_access acc) sg = some (false, sg, []) →
    sg.regs .satp = satp0 →
    BitVec.setWidth 44 (satp_to_ppn satp0) = root →
    zero_extend (m := 16) (satp_to_asid satp0) = 0#16 →
    sg.regs .tlb = tlbvec →
    pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (sg.regs .pmpcfg_n)[0]!) = .TOR →
    zopz0zKzJ_u (zeros (n := 64)) (sg.regs .pmpaddr_n)[0]! = false →
    (_get_Pmpcfg_ent_R (sg.regs .pmpcfg_n)[0]! == 1#1) = true →
    (_get_Pmpcfg_ent_W (sg.regs .pmpcfg_n)[0]! == 1#1) = true →
    ramEnd ≤ (sg.regs .pmpaddr_n)[0]!.toNat * 4 →
    WeakKpt.pmaAllowsPteRead (sg.regs .pma_regions) →
    WeakKpt.pmaAllowsPteWrite (sg.regs .pma_regions) →
    ∃ (sg' : ExecSt) (es : List Weff),
      execEff (translateAddr (.Virtaddr va) acc) sg =
        some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
      ((sg' = sg ∧ es = []) ∨
       (sg' = sg.setReg .tlb (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0 0#16))) ∧
         (es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8] ∨
          es = [.WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8])) ∨
       (∃ a1 d1 : BitVec 1,
          update_PTE_Bits p0 acc = some (pteSetAD p0 a1 d1) ∧
          sg' = (sg.setMem (bmWrite sg.mem (AxPtProt.ptAddr0 p1 vpn) 8 (pteSetAD p0 a1 d1))).setReg .tlb
            (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD p0 a1 d1) 0#16))) ∧
          (es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                 .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                 .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                 .WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                 .WEwrite ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8
                   (pteSetAD p0 a1 d1)] ∨
           es = [.WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                 .WEwrite ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8
                   (pteSetAD p0 a1 d1)]))) := by
  intro vpn p0 hchk hval hcanon hout hvarp hwv2 hwv1 hbase hmaps htlbok hsm2 hsm1 hsm0 hmisa hmenv hhtif
    hcp htm heff hss hsatp hppn hasid htlbv hA hord hR hW hcov hpmar hpmaw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hn2, -, hn1, -, hl0, hnap, -⟩ := id hmaps
  -- the three PTE reads, at the walk's canonical slot spellings
  have ha2 : AxPtProt.ptAddr2 t vpn = uPteAddr root (Sail.BitVec.extractLsb vpn 26 18) := by
    unfold AxPtProt.ptAddr2; rw [hbase]; rfl
  have hsm2' : WeakWalkEff.ptSlotMem sg (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) p2 := ha2 ▸ hsm2
  obtain ⟨region2, hm2, hs2⟩ := hpmar _ hsm2'.2.1
  obtain ⟨region1, hm1, hs1⟩ := hpmar _ hsm1.2.1
  obtain ⟨region0, hm0, hs0⟩ := hpmar _ hsm0.2.1
  have hrd2 := wptReadPteSlot sg _ p2 region2 hsm2' hA hord hR hcov hm2 hs2 hhtif
  have hrd1 := wptReadPteSlot sg (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) p1 region1
    hsm1 hA hord hR hcov hm1 hs1 hhtif
  have hrd0 := wptReadPteSlot sg (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) p0 region0
    hsm0 hA hord hR hcov hm0 hs0 hhtif
  have hrdx := wptReadPteExclusiveSlot sg (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) p0
    region0 hsm0 hA hord hR hcov hm0 hs0 hhtif
  -- identity geometry
  have hid : zero_extend (m := 64) (ppn0 p0 +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa := by
    show zero_extend (m := 64) (PPN_of_PTE (pteSetAD w a0 d0) +++ _) = pa
    rw [ppn_of_pteSetAD]; exact hout
  have hpbmte : (_get_MEnvcfg_PBMTE menvcfgS == 0#1) = true := by decide
  have hadue : (_get_MEnvcfg_ADUE menvcfgS == 1#1) = true := by decide
  -- the shared miss path, from a missing lookup
  have hmiss : execEff (lookup_TLB 39 0#16 vpn) sg = some (none, sg, []) →
      ∃ (sg' : ExecSt) (es : List Weff),
        execEff (translateAddr (.Virtaddr va) acc) sg =
          some (.Ok (.Physaddr pa, .PBMT_PMA, init_ext_ptw), sg', es) ∧
        ((sg' = sg ∧ es = []) ∨
         (sg' = sg.setReg .tlb (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0 0#16))) ∧
           (es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                  .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                  .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8] ∨
            es = [.WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8])) ∨
         (∃ a1 d1 : BitVec 1,
            update_PTE_Bits p0 acc = some (pteSetAD p0 a1 d1) ∧
            sg' = (sg.setMem (bmWrite sg.mem (AxPtProt.ptAddr0 p1 vpn) 8 (pteSetAD p0 a1 d1))).setReg .tlb
              (vectorUpdate tlbvec (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD p0 a1 d1) 0#16))) ∧
            (es = [.WEread wakPlain (uPteAddr root (Sail.BitVec.extractLsb vpn 26 18)) 8,
                   .WEread wakPlain (uPteAddr (uNextBase p2) (Sail.BitVec.extractLsb vpn 17 9)) 8,
                   .WEread wakPlain (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                   .WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                   .WEwrite ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8
                     (pteSetAD p0 a1 d1)] ∨
             es = [.WEread ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8,
                   .WEwrite ⟨false, true, false⟩ (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8
                     (pteSetAD p0 a1 d1)]))) := by
    intro hlk
    obtain ⟨sg', es, htr, hshape⟩ := wptreeTranslateMissEffCore acc p root va w tlbvec p2 p1 a0 d0 sg
      hchk hval hwv2 hn2 hwv1 hn1 hl0 hnap hsm0 hrd2 hrd1 hrd0 hrdx hmisa hmenv hhtif htlbv hlk hA hord hW
      hcov hpmaw
    refine ⟨sg', es, execEffTranslateAddrPtFront acc p vpn root (ppn0 p0) satp0 va pa es sg sg'
      heff hss hcp htm hsatp hppn hasid hcanon rfl htr hid, ?_⟩
    rcases hshape with ⟨ho2, hes⟩ | ⟨a1, d1, hu, ho3, hes⟩
    · exact Or.inr (Or.inl ⟨ho2, Or.inl hes⟩)
    · exact Or.inr (Or.inr ⟨a1, d1, hu, ho3, Or.inl hes⟩)
  cases hslot : tlbvec[tlb_hash 39 vpn]! with
  | none =>
    -- empty slot: the walk runs
    exact hmiss (execEffLookupTLBMiss vpn 0#16 tlbvec sg htlbv hslot)
  | some ent =>
    -- resident entry
    obtain ⟨vpn0, q2, q1, qp0, a', d', hm0', -, hent⟩ := htlbok vpn ent hslot
    by_cases hne : vpn0 = vpn
    · -- HIT on this vpn's own (A/D-variant) entry
      rw [hne] at hm0' hent
      obtain ⟨h2, h1, h0⟩ := AxPtProt.ptreeMapsDet t vpn q2 q1 qp0 p2 p1 p0 hm0' hmaps
      rw [h2, h1, h0] at hent
      rw [hent] at hslot
      have habs : pteSetAD p0 a' d' = pteSetAD w a' d' := pteSetAD_pteSetAD w a0 d0 a' d'
      have hchkc : ∀ mxr dosum, wpteCheckOk acc p mxr dosum (pteSetAD p0 a' d') := by
        intro mxr dosum; rw [habs]; exact hchk a' d' mxr dosum
      have hpbc : ptePbmt0 (pteSetAD p0 a' d') := by rw [habs]; exact hvarp a' d'
      have hidc : zero_extend (m := 64)
          (ppn0 (pteSetAD p0 a' d') +++ Sail.BitVec.extractLsb va (Functions.pagesize_bits - 1) 0) = pa := by
        show zero_extend (m := 64) (PPN_of_PTE (pteSetAD p0 a' d') +++ _) = pa
        rw [ppn_of_pteSetAD]; exact hid
      have hlkhit := execEffLookupTLBHitEnt vpn 0#16 tlbvec _ sg htlbv hslot
        (WeakKpt.uweMatchSelf vpn p2 p1 (pteSetAD p0 a' d') 0#16)
      cases hupq : update_PTE_Bits (pteSetAD p0 a' d') acc with
      | some q0' =>
        -- the CACHED word wants A/D bits: split on whether MEMORY does
        have hvarm : ∃ a2 d2 : BitVec 1, p0 = pteSetAD (pteSetAD p0 a' d') a2 d2 :=
          ⟨a0, d0, by
            show pteSetAD w a0 d0 = pteSetAD (pteSetAD (pteSetAD w a0 d0) a' d') a0 d0
            rw [pteSetAD_pteSetAD, pteSetAD_pteSetAD]⟩
        cases hupm : update_PTE_Bits p0 acc with
        | some p0' =>
          -- memory needs the update too: write it back (O3, hit path)
          obtain ⟨regionw, hmw, hww⟩ := hpmaw _ hsm0.2.1
          have hwr := execEffWritePteConditionalRam (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0))
            p0' regionw sg hsm0.2.1 hsm0.2.2 hA hord hW hcov hmw hww hhtif
          obtain ⟨a1, d1, hq⟩ := PtAdBits.updatePTEBitsSetAd _ _ _ hupm
          subst hq
          refine ⟨(sg.setMem (bmWrite sg.mem (uPteAddr (uNextBase p1) (Sail.BitVec.extractLsb vpn 8 0)) 8
              (pteSetAD p0 a1 d1))).setReg .tlb
              (vectorUpdate (sg.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 (pteSetAD p0 a1 d1) 0#16))),
            _, execEffTranslateAddrPtFront acc p vpn root (ppn0 (pteSetAD p0 a' d')) satp0 va pa _ sg _
              heff hss hcp htm hsatp hppn hasid hcanon rfl (fun mxr dosum =>
                execEffTranslateHitUser vpn root 0#16 (tlb_hash 39 vpn) _ acc p mxr dosum _ sg _ _ hlkhit
                  (execEffTranslateTLBHitPtUpd acc p mxr dosum vpn p2 p1 (pteSetAD p0 a' d') q0' p0 _ menvcfgS
                    0#16 (tlb_hash 39 vpn) _ _ _ sg (hchkc mxr dosum) hupq hpbc hmenv hadue hrdx (hval a0 d0) hl0
                    (hchk a0 d0 mxr dosum) hnap hmisa hpbmte hvarm hupm hwr rfl)) hidc,
            Or.inr (Or.inr ⟨a1, d1, rfl, by rw [htlbv]; rfl, Or.inr rfl⟩)⟩
        | none =>
          -- memory ALREADY has them: refresh only (O2', trace = the CAS read)
          refine ⟨sg.setReg .tlb (vectorUpdate (sg.regs .tlb) (tlb_hash 39 vpn) (some (uWalkEntry vpn p2 p1 p0 0#16))),
            _, execEffTranslateAddrPtFront acc p vpn root (ppn0 (pteSetAD p0 a' d')) satp0 va pa _ sg _
              heff hss hcp htm hsatp hppn hasid hcanon rfl (fun mxr dosum =>
                execEffTranslateHitUser vpn root 0#16 (tlb_hash 39 vpn) _ acc p mxr dosum _ sg _ _ hlkhit
                  (execEffTranslateTLBHitPtRefresh acc p mxr dosum vpn p2 p1 (pteSetAD p0 a' d') q0' p0 menvcfgS
                    0#16 (tlb_hash 39 vpn) _ sg (hchkc mxr dosum) hupq hpbc hmenv hadue hrdx (hval a0 d0) hl0
                    (hchk a0 d0 mxr dosum) hnap hmisa hpbmte hvarm hupm)) hidc,
            Or.inr (Or.inl ⟨by rw [htlbv], Or.inr rfl⟩)⟩
      | none =>
        -- hit, A/D already sufficient (O1)
        exact ⟨sg, [], execEffTranslateAddrPtFront acc p vpn root (ppn0 (pteSetAD p0 a' d')) satp0 va pa _ sg _
          heff hss hcp htm hsatp hppn hasid hcanon rfl (fun mxr dosum =>
            execEffTranslateHitUser vpn root 0#16 (tlb_hash 39 vpn) _ acc p mxr dosum _ sg _ _ hlkhit
              (execEffTranslateTLBHitPt acc p mxr dosum vpn p2 p1 (pteSetAD p0 a' d') 0#16 (tlb_hash 39 vpn) sg
                (hchkc mxr dosum) hupq hpbc)) hidc,
          Or.inl ⟨rfl, rfl⟩⟩
    · -- foreign entry: rejected by the tag, so the walk runs
      exact hmiss (execEffLookupTLBNomatchS vpn 0#16 ent tlbvec sg htlbv hslot
        (by rw [hent]; exact WeakWalkEff.uweMatchOther vpn0 vpn q2 q1 (pteSetAD qp0 a' d') 0#16 hne))

end Weak
