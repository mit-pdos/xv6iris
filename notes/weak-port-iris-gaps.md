# Weak-memory port: Iris / stdpp / Rocq-library gaps against iris-lean

*Inventory note, 2026-10-05.  Source: the Rocq weak-memory development at
`../xv6iris-spinlock/iris/` (`Weak*.v` + `Ax*.v`: 546 files, 339k lines), compared with the
SC remainder of the same tree (925 files, 450k lines, already ported here), with iris-lean at
the pinned revision (`.lake/packages/iris`, rev `728a1714`), Lean 4.32.2 core/Std, Batteries,
and this tree's `MachCSL/` + `Xv6/`.  No Mathlib (the manifest has iris, batteries, Qq, Sail,
Lean_RV64D only).*

**Method.**  Counts are regex hits over comment-stripped `.v` sources: "occ" is occurrences, "files"
is the number of files.  Import counts overstate real use, because most weak files carry a
boilerplate import header (e.g. 132 files import `ghost_map` but only 8 use it).  So for every
camera or library below, the *use* column is the one to read.  The iris-lean side was checked
by name against its 5,633 `@[rocq_alias]`/`#rocq_ignore` entries, and every Iris lemma name
the weak files use was intersected with the Rocq iris/stdpp sources
(`~/dev/weak-memory/.opamroot/axsl/lib/coq/user-contrib`).  Regex counts have some noise (a
generic word like `map` or `closed` matches by accident).  The ordering is reliable; the
exact numbers are not.

Also note: `iris/Wk*.v` (21 files, 18k lines: WkCtxSurface, WkOwnPingPong, WkStarted*, …) are
weak-memory acceptance tests outside the `Weak*/Ax*` glob.  They use `monPred` as well, so they
belong to the port's scope.

---

## 0. Headline

* **The Iris layer is essentially complete in iris-lean.**  Every Iris lemma name the weak files
  use has an iris-lean alias, except trivial renamings (`own_mono` → `iOwn_mono`,
  `mono_nat_lb_own_valid` → `MonoNat.auth_lb_own_valid`, `later_intro` and similar BI laws
  under Lean names).  That includes the weak-only ones: `gmap_view_*`, the `big_sepM2_*`
  suite, `discrete_fun_*`, `max_nat_*`, `mono_list_*_dfrac_*`, `saved_pred_*`, `token`,
  `gset_disj_*`, `wp_strong_adequacy`, `lc_fupd_elim_later` and `monPred_at_*`.  All proof-mode
  tactics the weak files use exist as well.
* **The gaps are in stdpp and in Rocq-specific technique**:
  * stdpp's relation library (`rtc`/`tc`/`nsteps`), which is weak-only and heavy.
  * stdpp's finite-map and finite-set lemma corpus, and `set_solver`, which the weak files
    use 12× as often as the SC files.
  * `Countable` keys.
  * `Finite`/`fin_to_set`.
  * `Qp` arithmetic.
  * Hint-database automation (`gshape` & co., 451 `Hint Resolve`).
  * Heavy `vm_compute` / `vm_cast_no_check` reflection, which cannot be carried over as is,
    because `native_decide` is banned.
* **One iris-lean feature is new to this tree**: `MonPred` (`Iris/BI/MonPred.lean` and
  `Iris/ProofMode/MonPred.lean`).  It exists and has no `sorry`, but no MachCSL/Xv6 file has
  exercised it yet.

---

## 1–2. Inventory, with the Lean equivalent or the gap

### 1a. Iris algebra / ghost-state libraries

| Rocq feature | weak use (occ / files) | SC-Rocq use | Lean equivalent | status / SC precedent |
|---|---:|---:|---|---|
| `ghost_map` (`↪[γ]`, `ghost_map_auth/elem`) | 70 / 8 (imported by 132) | 197 / 35 | `Iris.Instances.Lib.GhostMap` (`GhostMapG`) | **EXISTS**, used heavily (1251 hits / 447 files) |
| `ghost_var` | 109 / 74 | 558 / 408 | `Iris.Instances.Lib.GhostVar` (`GhostVarG`) | **EXISTS**, used heavily |
| `saved_prop` / `saved_pred` | 22 / 3 (imported by 83) | 5 / 1 | `Iris.Instances.Lib.SavedProp` (`saved_pred_*` aliased) | **EXISTS**; used in `MachCSL/CrashPermInv`, `Xv6/ChildTok` |
| `mono_nat` | 111 / 42 | 120 / 21 | `Iris.BI.Lib.MonoNat`, `Iris.Algebra.Lib.MonoNat` | **EXISTS**; used via `MachCSL/Resources` |
| `mono_list` | 34 / 8 | 20 / 3 | `Iris.BI.Lib.MonoList`, `Iris.Algebra.Lib.MonoList` | **EXISTS**; used |
| `gmap_view` (`gmap_viewR`, `_alloc_big`, `_replace`, `_both_valid`, `_frag_op_valid`) | 69 / 60, **real use 1 file** (`AxTokLedger.v`) | 0 | `Iris.Algebra.HeapView` (`HeapView.Auth/Frag`; all eight lemmas aliased) | **EXISTS**; weak-only in Rocq, but Lean SC already uses `HeapView` under `ghost_map` (`MachCSL/KMap`, `Xv6/UkConsOut`) |
| `auth` (`●`/`◯`, `authR`) | 74 / 14 | 144 / 9 | `Iris.Algebra.Auth` | **EXISTS**; e.g. `Auth (LeibnizSet …)` in `Xv6/OffBoxCam`, `Auth (StampMap …)` in `MachCSL/CtxBox` |
| `gset` camera (union) | 13 lemma uses / 3 | – | `Iris.Algebra.LeibnizSet` (`LeibnizSet`) | **EXISTS**; `Xv6/OffBox` |
| `gset_disj` | 19 / 5 | 49 / 4 | `Iris.Algebra.LeibnizSet` (`DisjointLeibnizSet`, `gset_disj_*` aliased) | **EXISTS**, not yet used in this tree |
| `agree` (`to_agree`, `agreeR`) | 27 / 4 | 66 / 21 | `Iris.Algebra.Agree` (`toAgree`) | **EXISTS**; used |
| `dfrac` | 1039 / 146 | 1921 / 299 | `Iris.Algebra.DFrac` | **EXISTS**; used everywhere |
| `frac` / `Qp` | 388 / 65 (198 `%Qp` literals) | 716 / 114 | `Iris.Algebra.Frac` (`Qp := {q : Rat // 0 < q}`, thin API: `half`, `quarter`, `half_add_half`, …) | **PARTIAL**: no `add_assoc`/`add_comm`/`div`/`le` lemma set.  SC wrote local lemmas (`Xv6/FileFrac.qp_add_assoc`, `Xv6/FilePay.qp_half_add`, `Xv6/IcacheInvRef`, `Xv6/IcacheInvStore`) → see §G6 |
| `excl` / `excl_auth` | 5 / 3 | 19 / 8 | `Iris.Algebra.Excl`, `Iris.Algebra.Lib.ExclAuth` | **EXISTS**; used |
| `csum` | 0 | 10 / 4 | `Iris.Algebra.Csum` | EXISTS (SC only) |
| `dfrac_agree` | via lemma names | used | `Iris.Algebra.Lib.DFracAgree` | **EXISTS**; used (`Xv6/SlotGen`, `IcacheRefDefs`) |
| `max_nat`, `mra`, `discrete_fun` | 18 + 2 + 20 | few | `Iris.Algebra.Numbers` (`MaxNat`), `Iris.Algebra.Mra`, `Iris.Algebra.Functions` | **EXISTS** |
| `token` | 8 / 1 | – | `Iris.Instances.Lib.Token` | **EXISTS** |
| `own`, `own_alloc`, `own_update`, local updates | 123 / 62, 19 / 12, 33 / 9 | 50 / 12 … | `iOwn`, `iOwn_alloc*`, `iOwn_update`, `Iris.Algebra.LocalUpdates` | **EXISTS**; `MachCSL/OwnAllocSame` adds one name in two cameras |
| `inG` / `subG` / `gFunctors` / `Σ` | 140 / 49 (107 `axirisG` instances) | 95 / 24 | `ElemG GF F`, `BundledGFunctors` | **EXISTS, different discipline**: no `subG` (D46).  Repo rule: one capacity instance per camera.  The weak `weakGS`/`axirisG`/`axannotGS` classes become classes over `GF` with `ElemG` fields |
| `stepindex_finite` (`dist_le`) | 2 real uses (`AxWp.v`) | 0 | `OFE.Dist.le` at `Nat` step-index | **EXISTS** (iris-lean's step index is `Nat`) |
| `sts` | 0 (name collisions only) | – | – | not used |

### 1b. Base logic, program logic, BI

| Rocq feature | weak use | SC-Rocq | Lean equivalent | status |
|---|---:|---:|---|---|
| fancy updates `|={E1,E2}=>` | 143 / 49 | 157 / 49 | `BIFUpdate`, `Iris.Instances.Lib.FUpd` | **EXISTS**; 1256 hits in tree |
| invariants (`inv`, `inv_alloc`, `inv_acc`, `iInv`) | 47 / 13, `iInv` 19 / 10 | 72 / 28 | `Iris.Instances.Lib.Invariants`, tactic `iinv` | **EXISTS**; used |
| `cinv` / `na_inv` | 0 real (hits are local `cinv` lemmas in `AxCertP2`/`WeakRvwmoCert3`) | 0 | `CInvariants`, `NaInvariants` | not needed |
| later credits `£` | 2 real (`WeakEvLift.v`: `wp_lift_step`'s `£ 1`; `AxWp.v` comment) | 0 | `Iris.Instances.Lib.LaterCredits` (`lc_fupd_elim_later` aliased) | **EXISTS** (6 hits in tree) |
| `gen_heap` (`↦`) | imported by 8; `↦` is mostly the local `RiscvPtsto` | 5762 / 474 | `Iris.BI.Lib.GenHeap` (`MachCSL/Resources`) | **EXISTS** |
| `fractional` (`Fractional`, `AsFractional`) | 8 / 2 | 5 / 3 | `Iris.BI.Lib.Fractional` | **EXISTS** |
| **`monPred`** (`monPred_at*`, `monPred_in`, `Objective`, `embed`, `iris.proofmode.monpred`) | **247 / 41** (`WeakView`, `WeakVProp`, `WeakCtx*`, `WeakLock*`, `WeakLeaf*`, …; plus `Wk*.v`) | only `Wk*.v` | `Iris.BI.MonPred` (`BiIndex`, `MonPred`, `Objective`, `monPred_at_*` incl. `_big_sepL/_big_sepM`, `monPred_in_intro/elim`, fupd/bupd/embed instances) + `Iris.ProofMode.MonPred` | **EXISTS, UNEXERCISED here.**  The design (`WeakVProp.v` header) keeps the monPred altitude thin (`vwp_hold P ws := monPred_at P (ws_view ws)`).  Spike `WeakView` + `WeakVProp` first (§G8) |
| `iProp`, `iResUR` | 1460 / 213 | 1497 / 337 | `IProp GF` | **EXISTS** |
| `language` / `prim_step` | 231 / 225 | 474 / 462 | `Iris.ProgramLogic.Language` (`MachCSL/Lang`) | **EXISTS** |
| `weakestpre`, `lifting` (`wp_lift_step`), `adequacy` (`wp_strong_adequacy`) | 219 / 58, 11 / 6, 18 / 12 | … | `Iris.ProgramLogic.{WeakestPre,Lifting,Adequacy}` | **EXISTS**; `MachCSL/Wp`, `MachCSL/Adequacy`.  `Global Program Instance weak_irisGS` → a plain `instance` |
| big ops `[∗ list]` / `[∗ map]` / `[∗ set]` / `L2` / `M2` | 657/82, 542/81, 366/54, 68/29 | 1226, 176, 105, 1 | `Iris.BI.BigOp.{BigSepList,BigSepMap,BigSepSet,BigSepMap2}`, `bigSepL2` in `BigOp.lean` | **EXISTS**; every one of the 60 big-op names used is aliased.  `MachCSL/BigSepLib` has 2 local combinators.  `[∗ set]`/`M2` are ~4× / 68× SC usage, so expect new helper lemmas but no missing core |
| namespaces `nroot .@` | 8 / 4 | 44 / 16 | `Iris.Std.Namespaces`, `CoPset` | **EXISTS** |

### 1c. Proof-mode tactics (weak occurrences)

`iIntros` 4637, `iApply` 4070, `iDestruct` 2927, `iSplit*` 2319, `iPureIntro` 1568, `iFrame` 1346,
`iMod` 1273, `iModIntro` 969, `iExists` 914, `iNext` 571, `iExact` 527, `iEval` 524, `iAssert` 354,
`iPoseProof` 184, `iSpecialize` 136, `iLöb`/`iInduction` 95, `iLeft`/`iRight` 85, `iInv` 19,
`iRewrite` 9, `iSimpl` 8, `iCombine` 7, `iClear` 5, `iExFalso` 4, `iRevert` 2, `iStopProof` 1.

All of them **EXIST** in iris-lean: `iintro icases iapply isplit(l/r) ipureintro iframe imod
imodintro iexists inext iexact ieval ihave ispecialize iloeb iinduction ileft iright iinv irewrite
isimp icombine iclear iexfalso irevert istop iaccu iassumption iempintro`.  The SC port's
idioms and pitfalls are in `notes/design/iris-lean-and-sail-lean-gotchas.md`.  Use
`MachCSL/FrameFilter` (fast `iframe`) and `MachCSL/KApply` (`k_iapply`) for big contexts.
`iEval (rewrite …) in "H"` (524 uses) has no direct counterpart, because `rw … at H` is
impossible on proof-mode hypotheses.  Use `ihave H := (show A ⊢ B by rw …) $$ H` or a
goal-wide `unfold`, as in the gotchas note.

### 1d. stdpp

| stdpp feature | weak use (occ / files) | SC-Rocq | Lean equivalent | status / SC precedent |
|---|---:|---:|---|---|
| `gmap` + `fin_maps`/`fin_map_dom` lemmas (`lookup_insert(_ne)`, `insert_union_singleton_l`, `dom_*`, `map_Forall`, `kmap`, `omap`, …) | gmap ops 2217 / 524; 737 lemma calls / 94; 57 distinct fin_maps/dom names | 8440 / 551; 516 calls | `Std.ExtTreeMap K V compare` through iris-lean `LawfulPartialMap`/`LawfulFiniteMap` (`Iris.Std.PartialMap`: `dom kmap filterMap union difference ofList …`, 145 theorems; instance in `Iris.Std.HeapInstances`).  `MachCSL.RegMapF := ExtTreeMap Nat · compare` | **PARTIAL**.  The API exists; stdpp's ~1000-lemma corpus does not.  SC re-proved the lemmas it needed **file by file** (`Xv6/FsTree` map helpers, `FsAbsDefs` `omap_insert_*`, `FsAbsDelta`, `FileWriteNode.insert_insert`, `InodeInv.dataUpd` for `<[i:=v]>` on functions, `UserFd` `big_sepM_kmap_some`).  The weak files use 14 fin_maps names the SC files never used (e.g. `insert_union_singleton_l` ×64).  → §G2 |
| `gset` + `sets`/`fin_sets` lemmas (`elem_of_union`, `elem_of_list_to_set` ×177, `elem_of_filter` ×54, `size_*`, `set_eq`, `fin_to_set`) | `gset` 1094 / 189; set ops 1743 / 163 | 591 / 82 | `Std.ExtTreeSet` + iris-lean `LawfulSet`/`Iris.Std.GenSets` (`filter size ofList fold setForall`) | **PARTIAL**.  `ExtTreeSet` has no `DecidableEq` (`Xv6/FsImgCheck` deviation 3), so set equality is `ext` |
| **`set_solver`** | **838 / 128** | 72 / 19 | none (no Mathlib, no `aesop`) | **MISSING**.  SC replaced each call with a named pure lemma (`Xv6/IcacheEscrowPoolMove` dev. 4, `Xv6/UshPipeLeavesRound` dev. 2, `Xv6/BmapDefs` dev. 4, `Xv6/ItruncParts`).  That does not scale to 838 calls → §G2 |
| `gmultiset` | 0 | 0 | `Iris.Algebra.LeibnizMultiSet` | not needed |
| **`relations`** (`rtc` ×654, `rtc_transitive`, `rtc_once`, `rtc_r`, `rtc_inv`, `rtc_ind_r`, `tc_rtc(_l/_r)`, `tc_transitive`, `nsteps_trans/once`, `rtc_nsteps*`, `rtc_subrel`) | **2134 / 172** (17 lemma names, all weak-only) | 93 / 7 | `FromMathlib.Relation.ReflTransGen` (iris-lean `Iris.Std.FromMathlib`: `refl tail head head_induction_on cases_head trans single`), core `Relation.TransGen`, `Relation.Iterate` (iris-lean `Iris.Std.Relation`, with `ReflTrans_iff_exists_iterate`) | **MISSING (lemma layer)**: no `tc_rtc*`, `rtc_inv`/`rtc_ind_r` names, `rtc_subrel` (mono), or nsteps/rtc bridges.  No SC precedent (SC Lean uses `Language.NSteps` only) → §G1 |
| `list` lemmas (`take`, `lookup_lt_Some`, `elem_of_cons`, `last`, `list_find` ×42, `filter_*`, `prefix_*`, `zip_with`, `sum_list` ×40, `Forall_*`, `NoDup_*`, `Permutation`, `submseteq`, `remove_dups`, `imap`, `omap`) | 1389 / 210; **101 names weak-only** of 193 | 1259 / 235 | Lean core `List` (`l[i]?`, `List.mem_cons`, `List.getLast?`, `List.find?`/`findIdx?`, `List.IsPrefix`, `List.zipWith`, `List.sum`, `List.Perm`, `List.Subperm`, `List.Nodup`, `List.mapIdx`, `List.filterMap`, `List.flatten`, `List.eraseDups`) | **MOSTLY EXISTS, under different names**; SC used core directly (`Xv6/FileDeltasLen`, `UnionOutPureSeal`, `FsDurAllocList`).  A small alias shim for the stdpp-only shapes → §G3 |
| `sorting` (`merge_sort`, `Sorted`, `StronglySorted`) | 68 / 7 | 0 | core `List.mergeSort`, `List.mergeSort_perm`, `List.Pairwise` (`Init.Data.List.Sort`) | **EXISTS** (weak-only use) |
| `finite` / `Finite` / `fin_enum` / `fin_to_set` | 124 / 25 (`fin_to_set` 31, `fin_enum` 11) | 165 / 12 | none (Mathlib's `Fintype` is absent); `List.finRange`, `Fin` decidable quantifiers in core | **MISSING (small)** → §G5 |
| `fin` (`fin_to_nat` ×523, `nat_to_fin`) | 556 / 56 | 172 | core `Fin` (`.val`, `⟨n, h⟩`, `Fin.ofNat`) | **EXISTS** |
| `Countable` keys (20 instances) / `EqDecision` (18) / `Decision` (59) / `RelDecision` (12) | 109 instance decls | few | `DecidableEq` (derivable); ExtTreeMap/Set keys need `Ord` + `Std.TransOrd` + `Std.LawfulEqOrd`; iris-lean `Pos.Countable` exists but is not a map key | **GAP (per key type)**.  SC precedent: `MachCSL/CtxBox.instOrdProdLex` (pair keys via core `lexOrd`), `Xv6/PipesDisc.bytesCode` (stand-in for `encode_nat`) → §G4 |
| `decidable` (`bool_decide` ×354, `case_bool_decide` ×214, `case_decide` ×122) | 1959 / 268 | 817 / 129 | `decide`, `Decidable.decide`, `by_cases h : p` + `simp [h]`, `split` | EXISTS (idiom change; `Classical.propDecidable` is allowed, DU9) |
| `option` (`is_Some` ×398, `from_option`, `default`) | 802 / 86 | – | `Option.isSome`, `Option.getD`, `Option.elim` | EXISTS |
| `bitvector` (`bv n`, `Z_to_bv`, `bv_unsigned`, `bv_wrap`, `bv_eq`, `bv_add`) | 2967 / 338 | 15267 / 434 | `BitVec n` (`toNat`/`toInt`/`ofInt`/`ofNat`), `BitVec.reduce*` simprocs, `bv_omega`, `bv_decide`; `MachCSL/BvLemmas`, `MachCSL/AluFacts`, `MachCSL/ByteWord*` | **EXISTS**; SC precedent is extensive.  `bv_solve`/`bv_simplify`: 0 weak uses |
| `namespaces`, `coPset` | 39 | – | `Iris.Std.Namespaces`, `Iris.Std.CoPset` | EXISTS |
| `tactics`: `simplify_eq` ×945, `split_and!` ×3246, `naive_solver` ×116, `destruct_and!`, `case_match` ×24, `f_equiv`/`solve_proper` ×16, `inv_step` | heavy | light (naive_solver 52) | `subst`/`injection`/`simp_all`/`cases`; `and_intros` / `refine ⟨?_,…⟩` (core); `grind`; `split`; hand-written `NonExpansive` proofs | EXISTS as idioms (`Xv6/LineModelLinks` dev. 2: `split_and!` → anonymous constructor) |

### 1e. Rocq standard library and plugins

| feature | weak use | SC-Rocq | Lean | status |
|---|---:|---:|---|---|
| `ssreflect` (imported by 431 files; `move=>`/`rewrite /d //= !` 1090; `done` 10758; `have` 3484) | heavy | 1235 / 205 | `intro`/`rintro`/`obtain`, `unfold`/`simp only [d]`, `rw [..] <;> try trivial`, `repeat rw`, `cases`/`induction` | idiom map, no library needed |
| `lia` (6072 / 381); `nia`/`lra` 0; `ring` 7 | heavy | 7910 / 323 | `omega` (12998 uses in tree), `bv_omega` (218), `Nat`/`Int` simp lemmas; `ring` → `Int`/`Nat` `ac_rfl` or `grind` (no Mathlib `ring`) | EXISTS (2 files use `ring`: hand rewrite) |
| `ZArith` / `Z.*` (2959; `Z.of_nat` 540, `Z.eqb` 501, `Z.to_nat` 309); `Zquot` (31 files) | heavy | 12990 | `Int`, `Int.toNat`, `decide (a = b)`; `Z.quot`/`Z.rem` → `Int.tdiv`/`Int.tmod` (omega handles only `/`/`%` = `ediv`/`emod` by literals) | EXISTS; SC re-based most `Z` to `Nat`/`BitVec` |
| `N`/`positive` (1427, mostly `N.to_nat` from Sail widths) | 1427 | 983 | `Nat` (Lean model widths are `Nat`) | EXISTS (disappears) |
| `FunctionalExtensionality` (22 / 16) | | 35 | `funext` (core) | EXISTS |
| `Eqdep_dec` / `inj_pair2` / `eq_rect` (21 / 15) | | 130 | `cases`/`subst` on dependent equalities, `Sigma.mk.inj_iff`, `HEq`; proof irrelevance is definitional | EXISTS (simpler) |
| `Classical` | 0 | 0 | `Classical.choice` is in the audited baseline | allowed (DU9) |
| `Program` (2 `Program Instance`), `Equations` 0, `Hammer` 0, `Ltac2` 0, `RecordUpdate` 0 | | | `instance … where` | none needed |
| `Zwf`/`Wf_nat`/`lt_wf`/`Acc` well-founded recursion (209 / 58); `Fixpoint` 236; `fix IH` on `Acc` in generated files | | 130 | `termination_by`/`decreasing_by`, `WellFounded.fix`, `Nat.strongRecOn`; **but kernel `decide` cannot evaluate WF definitions** (gotchas note: `hartSupports`) | EXISTS; fuel/structural definitions are needed wherever a proof computes (§4) |
| `Module` (14 in weak vs 531 in SC) | | | `structure`/`namespace` (D30 precedent) | EXISTS |
| `Section`/`Context` (2851 / 800), `Existing Instance` 40, `Arguments` 172, `Typeclasses Opaque cur_ctx` 3, `Strategy opaque` 1 (`AxSpinE8d.v`), `simpl never` 1, `Hint Constants Opaque` 4 | | | `variable` (per-declaration `[CurCtx]` binders, the gotchas note), `attribute [instance]`, `@[irreducible]`/`seal`, the `CurCtx` class (SC already ported `cur_ctx`) | EXISTS |
| `Print Assumptions` (2133 inline) / `Time` (179) | | | `#print axioms` / drop; the audit lives in `tools/ci/audit.sh` | EXISTS |
| **SailStdpp + Rocq `Riscv.rv64d`** (`Defs.bind`, `Interface.iMon`, `ReadReq/WriteReq.access_kind`, `mword`) — 412 files | | 763 files | lean-sail free monad (`vendor/lean-sail/Sail/ConcurrencyInterfaceV1.lean`: `Outcome`, `Access_kind`/`Explicit_access_kind`, `Mem_read_request`/`Mem_write_request`), `model/Lean_RV64D` | EXISTS, but every statement over the Rocq monad's combinators must be re-derived over the Lean model (affects §G7) |

---

## 3. SC code base vs weak: what the SC port already built, and what is new

**Already built by the SC port (reuse as is):**
* Finite maps and sets on `Std.ExtTreeMap`/`ExtTreeSet` via iris-lean's `LawfulPartialMap`/`LawfulSet`
  (`MachCSL.RegMapF`, `AddrMapF`, `StampMap`), with the lexicographic pair order instance
  (`MachCSL/CtxBox`).
* Every ghost-state library: ghost_map, ghost_var, mono_nat, mono_list, saved_prop, `Auth`, `LeibnizSet`,
  `Agree`, `DFrac`, `DFracAgree`, `Excl`, `ExclAuth`, `Csum`, and `HeapView` via ghost_map.
* Invariants, cinv, later credits, adequacy, `IrisGS` (`MachCSL/Resources`, `MachCSL/Wp`,
  `MachCSL/Adequacy`); one name in two cameras (`MachCSL/OwnAllocSame`).
* `BitVec` lemma homes (`MachCSL/BvLemmas`, `AluFacts`, `ByteWord*`).
* The symbolic Sail executor and normalisers: `sail_norm`, `swp_run`, `k_norm`, the `dsimproc`s
  `reduceClosed*`, and the simp sets `sail_facts`/`k_addr`/`k_norm_simps` (`MachCSL/Tactics`,
  `MachCSL/SimpAttr`).
* The walker equations `runRead`/`runRW` with `rfl` (D50), generated per-constructor model facts
  (`MachCSL/ModelFacts`, `tools/gen_model_facts.py`), and kernel-`decide` evaluation sweeps
  (`Xv6/FsImgCheckSweeps`, `ElfRows`, `UstepEcho`).
* Fast proof-mode plumbing (`FrameFilter`, `KApply`) and the `CurCtx` class.
* An existing **TSO** memory model (`MachCSL/TsoMem`, `notes/design/tso-memory-model.md`).  The
  weak port replaces or sits beside it; the decision is the port plan's, not this note's.

**SC alternatives that exist only as scattered per-file helpers** (consolidate before the
weak port, because the weak volume is 2–12× larger):
* stdpp map lemmas: `Xv6/FsTree`, `FsAbsDefs`, `FsAbsDelta`, `FileWriteNode`, `InodeInv`, `UserFd`.
* `set_solver` replaced by named lemmas.
* `Qp` lemmas: `Xv6/FileFrac`, `FilePay`, `IcacheInvRef`, `IcacheInvStore`.

**Weak-only, new to this tree:**

| feature | weak use | SC-Rocq use |
|---|---|---|
| stdpp `relations` | 654 `rtc` | 9 |
| `set_solver` | 838 | 72 |
| `MonPred` | 41 files | `Wk*` only |
| `Hint Resolve` databases (`gshape`/`gwexec`/`gwpost`/`gpure`, `gw_solve`) | 451 | none of this kind |
| `inversion` | 1251 / 181 files | 27 / 12 files |
| stdpp `sorting` | yes | – |
| `gset_disj` | yes | – (`DisjointLeibnizSet` exists in iris-lean but this tree has never used it) |
| `vm_cast_no_check` on open Sail runs | 78 | – |
| closed RVWMO graph deciders run by `vm_compute` | litmus/cat-consistency in `WeakDeps`, `AxDeps`, `AxLitmus`, `AxGraphWit`, `WeakRvwmo*` | – |
| `Countable` instances on weak key types | event ids, agents, positions | – |

---

## 4. Rocq-specific techniques without a direct Lean analogue

**Project policy (binding):**
* `native_decide` is **banned in proofs**: `tools/ci/lint.sh` enforces it, and it is allowed
  only in `vtest-lean/`.
* `bv_decide` is **allowed**.  Each call adds one counted `_native.bv_decide.ax_*` certificate
  (the `Lean.ofReduceBool` trust class, `notes/adequacy_axioms_baseline.md`); about 500 exist
  today.
* Closed evaluation is `decide +kernel` (430 uses; the `Xv6/FsImgCheck` header: "Rocq's
  `vm_eq` … Lean's counterpart is `decide +kernel` … no compiler in the trusted base").
* `Classical.propDecidable` is allowed where a decider only case-splits (DU9).

| Rocq technique (weak count) | where | Lean replacement |
|---|---|---|
| `vm_compute; reflexivity` on **closed** checkers (`Ltac vmr`, 402 uses; `vm_compute` 2146 / 213 files; `cbv` 958) | RVWMO graph/litmus deciders (`cat_t_consistent_b_sound; vmr`, `AxDeps`, `WeakDeps` ×126, `AxLitmus`, `AxGraphWit`), Sail constant folding | `decide +kernel` on a `Bool` checker plus its soundness lemma.  **The checker must be structurally recursive or fuelled, not `termination_by`**, because the kernel does not unfold WF recursion well.  Split large evaluations into sweeps (`Xv6/FsImgCheckSweeps` precedent) and run them under `ulimit` (D34) |
| `bv_eq; vm_compute; reflexivity` for literal-address arithmetic (`AxLeafS5` ×115, …) | leaf proofs | `decide`/`rfl` on `BitVec` literals.  State the fact as a standalone lemma and `simp only [it]`: folding inside a huge Iris goal causes kernel "deep recursion" (gotchas note).  `bv_decide` for non-literal bit facts |
| **`vm_cast_no_check (eq_refl …)` on OPEN terms** (78; e.g. `AxPair.rsw_lbls_pre (w : bv 64) : adm_lbls false 172 (rsw_xr w) = replicate 172 LSilent`) | symbolic Sail runs whose control flow does not depend on `w` | **No analogue**: Lean has no unchecked cast, and `decide +kernel` needs closed goals.  Options: (1) `by rfl` / `exact rfl` with raised `maxRecDepth`/`maxHeartbeats` (the elaborator and the kernel both check, so measure first); (2) the SC way, preferred: the walker equation (`runRead`/`runRW … = some …` by `rfl`, D50) or `sail_norm`/`simp` with `dsimproc`s; (3) restate as a closed checker quantified over the few data-dependent bits |
| `Eval vm_compute in` inside Ltac + `change` (72; `zsimp`, `vm_compute_uint`) | normalising `Z.eqb (uint a) (uint b)` and similar | `dsimproc`s (MachCSL `reduceClosed*` precedent), `simp (config := {decide := true})`, `BitVec.reduce*`/`Nat.reduce*` simprocs |
| `Strategy opaque [run_on …]` (`AxSpinE8d`), `Typeclasses Opaque cur_ctx`, `Hint Constants Opaque`, `simpl never` | | `@[irreducible]` / `seal`/`unseal`; instance-transparency `abbrev` vs `def` choices; `neverUnfold` in `MachCSL/Tactics` |
| Hint-database search: `#[export] Hint Resolve … : gshape` (303) / `gwexec` (61) / `gwpost` (55) / `gpure` (24), driven by `gw_solve` (327 uses) / `gwx_solve` / `gwm_solve` / `ew_solve`; files `WeakShape*.v` (8.1k lines, 15 + 3 generated shards by `tools/gen_shape.py`) | Stage C's per-Sail-function shape/liveness sweep | `register_label_attr gshape` (core `Lean.LabelAttribute`) + `solve_by_elim … using gshape` / `apply_rules using gshape` (both in core `Init/Tactics`), or a dedicated `elab` that looks up a `DiscrTree`.  **Retarget `gen_shape.py` to `model/Lean_RV64D`**: the Rocq `Defs.bind`/`try_catch`/`liftR`/`foreachM` kit (151 lemmas) is re-proved over lean-sail's `FreeM`/`ExceptT` combinators |
| Large custom Ltac (324 definitions in 136 files): `lk` (1270 uses: `register_lookup_set`/`irrelevant_register_set` rewriting), `off` (469), `c_go`/`c_step` (262), `vr` (190), `pcs`, `tw`, `rfF_auto` (153), `toA` (144), `nseip` (141), `zsimp` (136), `leaf_peel` (71), `ev_go`/`x_go`/`p_go`/`h_go`/`g_go` | register-file rewriting, certificate walkers, event-language steppers | Lean `macro`/`elab`.  Register rewriting → `simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]` (`notes/design/pipe-proof-idioms.md`); build the simp context once per call (gotchas note: about 30 ms per `simp only` setup); `set_option hygiene false` for macros naming Iris hypotheses |
| `inversion` (1251), `simplify_eq` (945), `injection` (1081), `discriminate` (1348) | inductive step relations | `cases`/`rcases`/`obtain` (Lean's `cases` unifies indices); `injection`/`simp at h`/`nomatch`; `simp_all` |
| `naive_solver` (116), `tauto` (75), `intuition` (23), `eauto` (409), `congruence` (437), `firstorder` | | `grind` (core; 75 uses in tree), `simp_all`, `solve_by_elim`, `omega`; `exact?` interactively only.  No `tauto`/`aesop`/`cc` (Mathlib-only) |
| `split_and` (3246), `destruct_and!`, `case_bool_decide` (214), `case_decide` (122) | | `and_intros` (core) / `refine ⟨?_, …⟩`; `obtain ⟨…⟩`; `by_cases h : p <;> simp [h]`; `split` |
| ssreflect rewriting (`rewrite /d !l -[p] //=`, `move=> [a b]`, `case:`, `elim:`) | 431 files | see §1e; note that `simp` cannot rewrite dependent positions (use `dsimproc`) |
| `fix IH n` inside proofs over `Acc` (generated `gw__rec_*`) | Sail fuel recursion | `induction` on the Lean model's own recursion (`*.induct`), or theorems proved by structural recursion; `MachCSL/ModelFacts` generator precedent |
| `setoid_rewrite` (16), `f_equiv`/`solve_proper` | OFE properness | `simp only` under binders; explicit `NonExpansive` proofs (iris-lean `OFE.NonExpansive`) |

---

## G. MISSING pieces to build, in priority order (with size estimates)

1. **G1. stdpp relations shim** (`MachCSL/Rel.lean`, about 200–300 lines).  `rtc`/`tc`/`nsteps`
   over `FromMathlib.Relation.ReflTransGen`, core `Relation.TransGen` and `Relation.Iterate`: the 17
   names the weak files use (`rtc_once/r/l/transitive/inv/ind_r/subrel/tc`, `tc_rtc(_l/_r)`,
   `tc_transitive`, `nsteps_once/trans`, `rtc_nsteps(_1/_2)`), plus `Trans` instances.  Weak-only,
   2134 hits in 172 files, and it underlies every `WeakRvwmo*`/promise/robustness file.
2. **G2. stdpp finite map/set lemma library plus a `set_solver` replacement**
   (`MachCSL/StdppMap.lean`, `MachCSL/StdppSet.lean`: about 600–900 lines; tactic about 100 lines).
   * Consolidate SC's scattered map helpers and add the about 60 fin_maps/dom/sets/fin_sets
     names the weak files use (`insert_union_singleton_l`, `elem_of_list_to_set`,
     `elem_of_filter`, `size_*`, `set_eq`, …) over `LawfulPartialMap`/`LawfulSet` for
     `ExtTreeMap`/`ExtTreeSet`.
   * The tactic: `set_solver` ≈ `simp only [LawfulSet.mem_union, mem_diff, mem_singleton,
     mem_ofList, mem_filter, subset_iff, …] at * ; grind`.  Spike it on 20 representative
     calls first.  The SC note says `set_solver` inside proof mode cost minutes in Rocq
     (`Xv6/BmapDefs`), so keep set reasoning in pure lemmas.
3. **G3/G4. Key-order instances and the stdpp list alias shim.**
   * Keys (about 50–150 lines): `Ord` + `TransOrd` + `LawfulEqOrd` for every gmap/gset key type
     that `Countable` covers today.  Pairs come from `instOrdProdLex`.  Records/inductives get
     `deriving Ord` plus law proofs, or an injective `Nat` encoding.
   * List shim (about 300 lines): `list_find`, `last_Some`, `lookup_take_Some`,
     `lookup_app_Some`, `filter_cons_True/False`, `prefix_lookup_Some`, `sum_list`,
     `remove_dups`, `imap`; most names map onto core `List`.
4. **G7. Shape kit and hint-database automation** (re-derive about 8k lines; generator retarget).
   * Label attributes (`gshape`/`gwexec`/`gwpost`/`gpure`) + `solve_by_elim using`.
   * Port `WeakShape*.v` over lean-sail's `FreeM` and retarget `tools/gen_shape.py` to
     `model/Lean_RV64D`.
   * Blocks stage C (`sail_shaped`/liveness).
5. **G9. Reflection policy layer** (case by case):
   * Rewrite the closed RVWMO/litmus/cat deciders as structural or fuelled `Bool` functions
     for `decide +kernel`, sweeping where they are large.
   * Replace the 78 open-term `vm_cast_no_check` lemmas with walker equations or `sail_norm`.
   * Replace the `Eval vm_compute` Ltac with `dsimproc`s.
   * Never `native_decide`; `bv_decide` is fine.
6. **G6. `Qp` lemma shim** (`MachCSL/QpLemmas.lean`, about 100–150 lines):
   * assoc/comm/left-comm, `half`/`quarter` arithmetic, `le`/`lt` and literal `p/q` normalisation.
   * Hoist the SC lemmas from `Xv6/FileFrac`, `FilePay` and `IcacheInv*`.
7. **G8. MonPred spike** (port `WeakView` + `WeakVProp`, about 1–2k lines, as the acceptance test).
   It checks that iris-lean's `BiIndex`/`MonPred`/`Objective`/`ProofMode.MonPred` carry the
   `vwp_hold` discipline before the 41 monPred files (plus `Wk*.v`) are ported.
8. **G5. `Finite`/`fin_to_set` shim** (about 80 lines): `finToSet n := ExtTreeSet.ofList (List.finRange n)`
   with membership/size lemmas, and decidable `∀ i : Fin n` via core.
