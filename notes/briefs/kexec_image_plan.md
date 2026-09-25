# K-B plan: KexecBuilt / KexecPtImage / KexecImageAlg re-based onto Lean user memory (D18)

Agent K-B, wave 7b-0 (brief fs7b §8.1, D18). Status: PLAN FOR REVIEW. Nothing past the stack algebra
(§0 + §1–§3 of KexecBuilt, see §8) is written until the coordinator checks this plan against Rocq.

Rocq sources: `KexecBuilt.v` (2051), `KexecPtImage.v` (541), `KexecImageAlg.v` (283).
Lean base: `UMem.lean` (`umemByte/umemWrite/viewFaulted/umMapped`), `UPtDefs.lean` (`UPtd`, `procPtAt`,
`umPages`, `umBelow`, `lazyFree`, `UPtd.ext/extSz`), `UMemLemmas.lean` (`umPages_upd`, `procPtAt_elim/intro'`,
`umemWrite_in/other/off`, `viewFaulted_*`), `LazyFree.lean`, and the landed callee Specs kexec calls:
`SpecUvmalloc` (`uvmallocOk`, premise `hfree`), `SpecCopyout` (`P.extSz psz P'`, `umemWrite (viewFaulted P P' M)`),
`SpecUvmclear` (`UPtd.clearU`), `SpecWalkaddr` (`walkaddrRet` over `P.leaves`), `SpecProcPagetable`
(`procPtAt ⟨root, tfp, ∅⟩ M`), `SpecReadi` kernel arm (`rdDelivered = rdBytes ++ olds.drop tot`).

## 1. The two representations

| | Rocq | Lean |
|---|---|---|
| byte image | `M : gmap Z (bv 8)`, keyed by byte va; under `proc_pt P M`, `dom M = uva_dom P` (every byte of every mapped page, nothing else); under `proc_ptm P sz M` also every LIVE unmapped byte, at 0 (lazy view) | `M : Nat → List (BitVec 8)`, per page, TOTAL; only mapped pages are owned (`umPages`: `(M k).length = 4096 ∗ byteBuf (pte2pa w) (M k)`); unmapped pages' `M k` is junk. No lazy view: `viewFaulted` zeroes a page when it is faulted in |
| page table | `ud_um : gmap (mword 27) (mword 64)` | `P.um : RegMapF (BitVec 64)` keyed by `vpn.toNat` |
| page key of byte `b` | `kexec_pg b = svpn_of (mword_of_int b)` (bv arithmetic, needs `≤ 2^38` side conditions) | `b / 4096` (Nat) |
| uvmalloc's effect | `umem_grow M sz` (= `M ∪ zeros(live_set sz)`, left-biased) | `uvmallocOk P P' M M' old new xperm`: run `[uvmaVpn0 old, +uvmaNp)` mapped fresh at zeros, everything else unchanged |
| loadseg / page write | `umem_write M a n g` (int-keyed, `g : nat → bv 8`) | `umemWrite M a bs` (`bs : List`), P unchanged |
| copyout's effect | `umem_wr M dstva n src` (keyed by wrapping `add_vec_int`) | `umemWrite (viewFaulted P P' M) dst bs ∧ umMapped P' dst len`, `P.extSz psz P'` |
| coverage | `um_covered szv um` (`vpn*4096 < sz → is_Some`) | `lazyFree um sz` (`k*4096 < pgRoundUpN sz → isSome`) — the SAME set of vpns (a multiple of 4096 is `< sz` iff `< PGROUNDUP sz`) |
| `um_below`, `lazy_free` | ProcPtOwn / UserPerm | `umBelow`, `lazyFree` (landed) |
| uvmclear | `pte_clear_u` at the guard vpn, M untouched | `P.clearU vpn w`, M untouched |

## 2. The one device: the mapped VIEW of the Lean pair

Rocq's `M !! a` under `proc_pt P M` is a function of the Lean pair `(P, M)`. Define it once (KexecBuilt §0):

```lean
/-- Byte `n` of the address space, as Rocq's `proc_pt`-image `M !! n`: defined exactly on mapped pages. -/
def umemGet (P : UPtd) (M : Nat → List (BitVec 8)) (n : Nat) : Option (BitVec 8) :=
  if (get? P.um (n / 4096)).isSome then (M (n / 4096))[n % 4096]? else none
/-- ... at Rocq's `Z` keys (none below 0). -/
def umemView (P : UPtd) (M : Nat → List (BitVec 8)) : Int → Option (BitVec 8) :=
  fun a => if 0 ≤ a then umemGet P M a.toNat else none
```

Under `umPages` every mapped page has length 4096, so `umemView P M` is defined exactly on `uva_dom P` —
Rocq's `dom M = uva_dom P`, which `procPtAt_pageLen` (KexecPtImage §2) extracts as a pure fact. The
`[j]?` spelling (not `umemByte`, which defaults to 0) makes "defined" self-certifying: a write-lookup law
needs only "was defined", exactly Rocq's `umem_write_dom` premise.

**Every Rocq predicate over `M : gmap Z (bv 8)` is ported VERBATIM over an abstract
`Mv : Int → Option (BitVec 8)`** (`M !! a = Some b` ↦ `Mv a = some b`): `uimg_sub`, `load_win`, `load_out`,
`kx_page_zero`, `kx_zero_except`, `kx_str_at`, `kxb_args_at`, `kxb_stack_at`. Kernel proofs instantiate
`Mv := umemView P M`; the user lane's `uvis_M` (D17) is the same type. So the re-base is CONFINED to the
laws that move the view, which are stated over the landed Lean operations — no gmap lemma is transcribed:

| Rocq law (gmap) | Lean law (view over the Lean op) | consumer |
|---|---|---|
| `umem_grow_lookup_old` | `umemView_uvmalloc_old`: `uvmallocOk P P' M M' o n x` + `hfree` (uvmalloc's own premise) → `umemView P M a = some b → umemView P' M' a = some b` | C (stack grow), B3 (phdr grow) |
| `umem_grow_lookup_zero` | `umemView_uvmalloc_zero`: `a / 4096` in the run → `umemView P' M' a = some 0` | C, B3 (bss) |
| (grow keeps an outside byte) | `umemView_uvmalloc_out`: page not in run → view unchanged | B3 `load_out` |
| `umem_write_lookup_in/out` | `umemView_write_in/out` over `umemWrite M va bs`, P fixed (`in` needs the byte defined before) | B2, C |
| `umem_wr_write`, `kx_wr_linear` (no-wrap) | DROPPED: Lean's `umemWrite` is Nat-keyed, there is no wrap | — |
| `KexecPtImage §6` (`proc_pt ⊣⊢ proc_ptm` when covered) | PURE `kxCopyout_covered`: `lazyFree P.um psz → P.extSz psz P' → (∀ k, get? P'.um k = get? P.um k) ∧ viewFaulted P P' M = M` — a covered space gains no leaf, so copyout's image IS `umemWrite M dst bs` | C (both argv copyouts), D |
| (uvmclear keeps bytes) | `umemView_clearU`: mapped vpn → `umemView (P.clearU v w) M = umemView P M` | C |
| (view depends on the domain only) | `umemView_congr`: same `isSome` domain → same view | C, D |
| `proc_pt_fresh_above(_z)` (iProp, `dom M`) | PURE `umemView_none_above`: `umBelow sz P` → `bnd % 4096 = 0` → `sz ≤ bnd ≤ a` → `umemView P M a = none` (no resource: the view is defined from `P`) | B3, C |
| `proc_pt_page_bytes`/`proc_pt_dom` | `procPtAt_pageLen : procPtAt P M ⊢ ⌜∀ k w, get? P.um k = some w → (M k).length = 4096⌝` (+ kept form), and pure `umemView_some_of_mapped` | B2, C |

**Why the view and not predicates over `(P, M)` directly.** (a) The statements stay Rocq-literal, so the
invariants of B2/B3/C/D port line by line; (b) SpecKexec's `kexec_args_at`/`kexec_stack_at` and
`uimg_sub … (uvis_M W')` are about a plain byte map in Rocq too (the user-visible record), so the same Lean
predicates serve the D17 key with no second spelling; (c) the only Lean-specific facts are the table above.

**Lazy view (flag).** Rocq's `us_M` is the LAZY view (`proc_ptm`). Lean has none. Every kexec state is
covered (`lazyFree`), where the lazy view equals `umemView`; D17's `uvisM` should be defined as the lazy
view `if mapped then byte else if live then some 0 else none`, with the bridge
`lazyFree P.um sz → uvisView = umemView`. Nothing in K-B depends on that choice.

**Int keys.** Rocq keys are `Z` and the stack algebra subtracts (`kxc_sp`). The plan keys the abstract view
by `Int` (Rocq-literal) and only `umemView` knows about `toNat`. REQUIRES K-A (see §6).

## 3. KexecBuilt.v → Xv6/KexecBuilt.lean (one file, same name; pure, no iProp)

| Rocq § | content | Lean | statement change | consumer phase |
|---|---|---|---|---|
| 0 | `umem_grow_lookup_old/zero`, `pgroundup_*` | §0: `umemGet`, `umemView`, the view laws of §2 that are PURE (uvmalloc old/zero/out, write in/out, clearU, congr, none_above, covered copyout); `pgroundup` rows via landed `pgRoundUpN` + `UPtAlloc.pgRoundUpN_*` (add `_mod`, `_aligned`, `_ge` if absent) | re-based (§2) | B3, C |
| 1 | push geometry `kxc_round16_le`, `kxc_sp_gap/mono/str_disj/vec_disj`, `kxc_sp_final_gap` | verbatim over K-A's `kxcSp`/`kxcSpFinal`/`kxcRound16` (Int). `kxc_round16_le` may already be in KexecDefs (Rocq has it twice) — reuse, don't restate | none | C |
| 2 | `kxb_ustack`, `kxb_arg_addr`, `kxb_str_zone(_mono/_arg/_push)`, `kxb_arg_addr_str/vec` | verbatim (see §7 cleanup: `kxb_ustack`/`kxb_arg_addr` are twins of KexecLoad's) | none | C |
| 3 | `kx_page_zero`, `kx_page_zero_grow`, `kx_zero_except(_of_page/_mono/_write)`, `kx_str_at(_0/_step)`, `kxb_args_at`, `kxb_stack_at(_intro)`, `kxb_args_at_intro`, `kx_argv_push`, `kx_argv_vec`, `mword0_bv0` | predicates over `Mv : Int → Option`; `kx_page_zero_grow` restated over `uvmallocOk` at the stack page (the run's upper page); `kx_zero_except_write`/`kx_str_at_step`/`kxb_args_at_intro` over `umemView P (umemWrite M a bs)` with P fixed and `bs : List`; `kx_argv_push`/`kx_argv_vec` take copyout's Lean post collapsed by `kxCopyout_covered` (their `Hlin` no-wrap premise disappears; `src`'s role is played by the kernel buffer list `bs` with `bs[8*i+k]? = some (nthByte (ustack i) k)`); `mword0_bv0`/`elf_zero_byte_bv0` DROPPED (one zero in Lean) | re-based moves; predicates verbatim | C |
| 1 (image) | `uimg_sub_empty/union/segs_union/seg_map/elf_image/seg_file_map/seg_zero_map`, `uimg_sub_umem_grow/_write/_write_range/_wr` | pure over K-A's image maps; the four move rows over §2's laws (`_umem_wr` → covered copyout + write_out) | re-based moves | B3, C |
| 2 (loadseg) | `umem_write_ext_kxb` (DROP: lists), `load_win(_0/_step/_grow/_write_out/_mono/_step_g)`, `load_out(_refl/_write)`, `uimg_sub_seg_file_map_win` | verbatim over `Mv`; the step: `load_win … (umemView P (umemWrite M (va+i) bs))` with `bs[k]? = some (f[off+i+k])`; `_grow` over uvmalloc_old | re-based moves | B2, B3 |
| 3 (size) | `kx_uvmalloc`, `kx_grow`, `kexec_sz_after`, the Z.max folds, `kxb_ascending*`, `kxb_sz_after_take_step`, `phdrs_nonneg` | verbatim (pure lists / Int) | none | B3, Seam |
| 3b/3c | `kxb_phdr_at/phoff/phdr/loads*`, `kxb_at`, `kxb_walk_ok`, `kxb_walk_step`, `kxb_loadable`, `kxb_walk_loadable(_of_loadable)`, `kxb_phdr_at_parse`, `kxb_loads_of_list`, `elf_wf_ph_window`, `kxb_load_hdr_in`, `kxb_not_walk_loadable(_off)`, `kexec_sz_after_elem`, `seg_map_lookup_range`, `uimg_sub_seg_map_above`, `file_bytes_length`, `kxb_phdr_fields/flags`, `kxb_at_step_skip`, `uimg_sub_load_out`, `kxb_at_step_load`, `kxb_at_done`, `kxb_walk_phnum0`, `pgroundup_ge`, `elf_image_lookup_below`, `uimg_sub_elf_image_wr_above` | verbatim over K-A's ElfFile/ElfBridge; `kxb_at … szv Mv`; `kxb_at_step_load` takes `uvmallocOk Pi Pg Mi Mg` + `hfree` in place of `umem_grow Mi sz'` and `load_out … (umemView Pg Mg) (umemView Pg Mo)`; its "fresh above vaddr" premise is `umemView Pi Mi a = none` (supplied by `umemView_none_above`); `_wr_above` over the collapsed copyout | re-based moves | B3, Seam, C |
| 3e (a) | `kxb_perm_leaf_flags/bits/rw/clear_u` | over Lean leaves: `permLeaf (uLeaf ppn (x ||| PTE_R ||| PTE_U)) = some ⟨bx, bw⟩` for the four `flags2perm` literals (bv_decide), `permLeaf (w &&& ~~~PTE_U) = none` | re-based (leaf word = `uLeaf`) | B3, C |
| 3e (b) | `kexec_pg(_unsigned/_of_word/_vpn_at)`, `kxb_page_index`, `kexec_pg_in_run`, `kexec_pg_top_stack_ne` | `kexec_pg b` ↦ `b.toNat / 4096`; the bv lemmas collapse to Nat division: keep `kexecPgInRun` (`b % 4096 = 0 → pgRoundUpN s ≤ b < e → b/4096 ∈ [uvmaVpn0 s, uvmaVpn0 s + uvmaNp s e)`) and `kexecPg_top_stack_ne`; `_unsigned`/`_of_word`/`_vpn_at` DROPPED (identities in Lean) | simplification (checked uses: B3, C only) | B3, C |
| 3e (c) | `kxb_perm_leaves(_0/_skip/_step/_done)`, `kxb_perm_segs(_mono/_insert)`, `kexec_seg_pg_below/_ne` | over `P.um` (`get?`); `um ⊆ um'` ↦ `∀ k w, get? um k = some w → get? um' k = some w` (what `UPtd.ext` gives) | re-based keys | B, B3, Seam, C |
| 3e (d) + S6/S7 | `kexec_seg_perm`, `kexec_seg_pages`, `kxb_perm_ok`, `kxb_perm_below(_intro)`, `perm_of_of_leaf(_none)`, `kxb_perm_ok_intro(_set)` | need `uperm`/`perm_leaf`/`perm_of` — **D17's UserPerm subset**; see §5 | — | C, D, Bridge |
| 4 | `kexec_built f ef sz1 na alen afun U'` | `kexecBuilt f ef sz1 na alen afun (V' : ProcPriv) (M' : Nat → List (BitVec 8))` with `Mv := umemView V'.upt M'`, `top := (sz1.toNat : Int)`; S8 is the landed `lazyFree V'.upt.um sz1` | `U' : ustate` ↦ the pair `(V', M')` (**process-layer: FLAG**, Lean has no `ustate`; `procPriv pa pid V M` is the pair) | D, Seam, C, KexecOkQ, ProcInv (`upd_exec`), Bridge |

## 4. KexecPtImage.v → Xv6/KexecPtImage.lean (iProp; mostly dissolves)

| Rocq § | Lean | reason |
|---|---|---|
| §1 `umem_write_mono` (lazy submap survives a write), `umem_write_ext` | DROP | no lazy witness `Mz` in Lean; lists make `_ext` trivial (checked uses: KexecPtImage only) |
| §2 `proc_pt_dom` | `procPtAt_pageLen` (+ `_keep`) | the Lean fact behind `dom M = uva_dom P` |
| §2 `proc_pt_fresh_above(_z)`, `proc_pt_page_bytes` | PURE, in KexecBuilt §0 (`umemView_none_above`, `umemView_some_of_mapped` from the page-length fact) | the view is a function of `P`: no resource needed |
| §3–§5 `proc_pt_window/page_borrow/page_load/page_load_split/_f` | `procPtAt_page_load_split` (and `umPages_page_load_split` for use while the tree is open for walkaddr): out `byteBuf (pte2pa w) ((M k).take nn) ∗ byteBuf (pte2pa w + nn) ((M k).drop nn)`, closer `∀ new, ⌜new.length = nn⌝ -∗ byteBuf (pte2pa w) new -∗ byteBuf (pte2pa w + nn) ((M k).drop nn) -∗ procPtAt P (umemWrite M (k*4096) new)` — built on the landed `umPages_upd` + `umemWrite_in/off` + `byteBuf_split_td/join_td`. Its output IS readi's kernel-arm shape (`olds := (M k).take nn`, `rdDelivered … = rdBytes ++ olds.drop tot`). `_window`/`_borrow`/`_page_load`/`_f` DROPPED (checked uses: `_split` in SpecKexecB2, `_f` in ProofKexecB2 only; `_f` exists in Rocq only to rename an ∃-bound byte function, which a Lean list does not need) | Rocq's round trip through `proc_ptm` is unnecessary: `umPages` already owns exactly the page |
| §5b `proc_ptm_wf_get`, `proc_pt_acc_rep0_m`, `proc_pt_rebuild_m` | REUSE landed `procPtAt_wf`, `procPtAt_elim`, `procPtAt_intro'` | Lean's `procPtAt` already keeps the tree and `umPages` apart |
| §6 `uva_live_mapped_covered`, `proc_pt_ptm_live/covered/cov`, `proc_pt_to_ptm_cov`, `proc_ptm_to_pt_cov` | DROP; replaced by the PURE `kxCopyout_covered` (§2) | Lean contracts (uvmalloc, copyout) are all stated at `procPtAt P M`; there is no `proc_ptm` to cross into |

Size: ~150 Lean lines (Rocq 541).

## 5. The permission projection (S6/S7) — depends on D17

Rocq's `kexec_built` S6/S7 are stated at `perm_of (ud_um …) (uint sz1)`. The phase proofs themselves only
ever use leaf facts (Rocq's own header: "perm_of is applied exactly once, at the commit").

**Proposal (a), default:** port the D17 subset NOW as a small definitional `Xv6/UserPerm.lean` (PARTIAL port of
UserPerm.v §1–2): `UPerm := ⟨X, W : Bool⟩`, `upermRw`, `permBits`, `permLeaf` (U∧R ↦ `some (permBits w)`),
`permOf (um) (sz) : Nat → Option UPerm` (leaf's projection if mapped, else `upermRw` below `pgRoundUpN sz`,
else none — Rocq's `omap perm_leaf um ∪ perm_fill`), and `permOf_lookup`. `lazyFree` is already landed
(UPtDefs). Then KexecBuilt carries S6/S7 Rocq-literally (`kxbPermOk f top (permOf V'.upt.um sz1)`,
`kxbPermBelow sz1 (permOf …)`, `kxbPermBelow_intro` from `umBelow`).
**(b) fallback, if D17 is deferred:** state S6 on leaves (`kxbPermSegs` + guard leaf `permLeaf = none` + stack
leaf `= some upermRw`) and S7 as `umBelow sz1 V'.upt`, moving Rocq's `kxb_perm_ok_intro`/`_below_intro` to
KexecBridge. Statement change to kexec_built; needs only `UPerm`/`permLeaf`.

## 6. Coordination with K-A (BLOCKING for everything past §0)

KexecBuilt imports K-A's `ElfEnc`, `ElfFile`, `ElfBridge`, `KexecDefs` (and, per §7, `KexecLoad`). The
following choices must agree, and are NOT in the tree yet (checked: no `ElfFile.lean`/`KexecDefs.lean`):
1. **Numeric type of Rocq's `Z`** (ELF fields `ep_vaddr`/`ep_memsz`/…, `kxc_sp`, `kxc_round16`, `top`,
   `kexec_sz_after`, `kexec_top`): this plan assumes **`Int`** (Rocq-literal; `kxc_sp_gap` is false in `Nat`
   under underflow, so `Nat` would add `kxc_stack_ok` premises to Rocq's unconditional disjointness rows).
2. **Image maps** (`seg_file_map`, `seg_zero_map`, `seg_map`, `segs_union`, `elf_image`): this plan assumes
   `Int → Option (BitVec 8)` with left-biased union and K-A's lookup lemmas (`lookup_seg_file_map`,
   `lookup_seg_zero_map`, `segs_union_lookup_inv`, `seg_file_bytes_lookup`), i.e. the same type as `Mv`.
3. **`pgroundup` on Int** for `kexec_top`/`kexec_sz`: `pgRoundUpN` is Nat; K-A either defines an Int one or
   uses `pgRoundUpN e.toNat`. KexecBuilt follows.
4. **KexecLoad's `kexec_args_at`/`kexec_stack_at`/`kexec_arg_addr`/`kexec_ustack`** must be over
   `Mv : Int → Option (BitVec 8)` (not a Lean `(P, M)` pair), so §7's cleanup works and D17's `uvisM` fits.
If K-A has already chosen differently, KexecBuilt adapts (Nat keys: drop `umemView`'s Int wrapper).

## 7. Cleanup proposed (full picture checked): drop the `kxb_` twins

Rocq spells `kxb_ustack/kxb_arg_addr/kxb_args_at/kxb_stack_at/kxb_ascending/kxb_loadable` twice ONLY
because SpecKexec.v pulls the AU cone and the kernel-side proofs must sit below it (KexecBuilt header;
KexecImageAlg §3–§5 are identity bridges). In Lean, SpecKexec §1b is split out as the light `KexecLoad.lean`
(D21), which kernel stages may import. So: KexecBuilt imports KexecLoad and states everything at
`kexecUstack/kexecArgAddr/kexecArgsAt/kexecStackAt/loadsAscending/kexecLoadable`; KexecImageAlg keeps only
`kexec_top_of_sz_after`, `kexec_sz_of_sz_after`, `kexec_top_nonneg/_mod`, `kexec_sz_mod/_ge`,
`kexec_sz_after_take_step`/`_take_all`, `kxb_walk_ok_of_loadable`, `kexec_loadable_of_walk` (~100 Lean lines
instead of 283; `loads_ascending_kxb`, `kxb_loadable_eq`, the §5 bridges vanish). Uses checked: the twins
are named by ProofKexecC/Seam/B3/D/Bridge/ProofKexec only through these bridges. **If rejected**, the twins
are ported verbatim and KexecImageAlg is the Rocq-literal bridge file. Either way KexecImageAlg waits for
KexecLoad (and, if KexecLoad needs `kxbPermOk` for `kexec_image_ok`, that part of §1b is D17's anyway).

## 8. Order of work

1. (now, pending K-A only for `kxcSp`) **KexecBuilt §0** (view + laws, needs only landed files) and the
   **stack algebra** (§1–§3: push geometry, arg addresses, zero fill, `kx_str_at`, `kx_argv_push/vec`,
   `kxb_args_at_intro`, `kxb_stack_at_intro`). §0 can be written and built today; §1–§3 build as soon as
   `KexecDefs.lean` lands. — **STOP here for review.**
2. KexecPtImage (landed deps only).
3. KexecBuilt §1-image, §2-loadseg, §3 size/walk/loadable, §3e(a–c) (after ElfFile/ElfBridge).
4. §3e(d)/S6/S7 + `kexecBuilt` (after D17 or with proposal (a)).
5. KexecImageAlg (after KexecLoad).

## 9. Deviations to record (headers)

- D18: re-based; the byte image is `umemView P M`; the four move laws replace the gmap algebra;
  `umem_wr`/no-wrap rows, `mword0_bv0`, `umem_write_ext/_mono`, the `proc_pt ↔ proc_ptm` crossing and the bv
  page-key arithmetic are dropped (Lean-trivial or absent), each with its checked consumers.
- **Process-layer (FLAG):** `kexec_built`'s `U' : ustate` becomes `(V' : ProcPriv, M')`; `us_M U'` is
  `umemView V'.upt M'` (the MAPPED view; Rocq's is the lazy view — equal under S8 `lazyFree`).
- `um_covered` ↦ landed `lazyFree` (same vpn set); `um_below` ↦ `umBelow`.
- uvmalloc's zero fill is only the run (`uvmallocOk`), not every live unmapped byte (`umem_grow`); equal
  on a covered space, which every kexec seam is. `umemView_uvmalloc_old` needs uvmalloc's own `hfree`.

## 10. Status at hand-off (K-B, first round)

- `Xv6/KexecBuilt.lean` §0 WRITTEN and built (`lake build Xv6.KexecBuilt`, ~2 s): `umemGet`, `umemView`,
  `umPageLen`, and in `namespace Xv6.KexecBuilt`: `umemView_ofNat/_neg`, `umemGet_mapped`,
  `umemGet_some_of_mapped`, `umemGet/umemView_congr`, `umemGet/umemView_none_above`, `uvmaInRun`,
  `umemGet_uvmalloc_out/_old/_zero`, `umPageLen_uvmalloc`, `umemGet_write_out/_in`, `umPageLen_write`,
  `umemView_write_out/_in`, `kxCopyout_covered`, `kxCopyout_dom`, `umemGet/umemView_clearU`.
- The STACK ALGEBRA (§1–§3) is drafted and CHECKED against Rocq-literal Int stand-ins for K-A's
  `kxcRound16/kxcSp/kxcSpFinal/kxcStackOk` (`notes/briefs/kexec_stack_draft.lean.txt`; `lake env lean`, ~3 s):
  push geometry, `kxbUstack/kxbArgAddr/kxbStrZone` + rows, `kxPageZero`, `kx_page_zero_uvmalloc`,
  `kxZeroExcept` + rows, `kxStrAt`, `kxbArgsAt`, `kxbStackAt(_intro)`, `kx_argv_push`, `kx_argv_vec`.
  It is appended to KexecBuilt.lean (stand-ins deleted, import `Xv6.KexecDefs`) as soon as K-A lands
  KexecDefs with those names over `Int`. If §7's cleanup is approved, `kxbUstack/kxbArgAddr/kxbArgsAt/
  kxbStackAt` are replaced by KexecLoad's `kexec*` names instead. Rocq's `kx_str_at_step` and
  `kxb_args_at_intro` are subsumed by the two push rows (their only consumers are those rows).
- **Observed while handing off:** K-A's in-progress `Xv6/ElfEnc.lean` states `leAt`/`ph*`/`eh*` over `Nat`
  (and over `List (BitVec 8)`, not Rocq's `nat → bv 8`). If ElfFile follows (Nat vaddrs, Nat-keyed images),
  the abstract view becomes `Mv : Nat → Option (BitVec 8)` = `umemGet P M` (already the core of §0; drop the
  `umemView` Int wrapper). The one place `Nat` is NOT Rocq-literal is `kxc_sp`: Rocq's `kxc_sp_gap`
  (`sp (S i) + alen i < sp i`) is false under Nat truncation, so either `kxcSp` stays `Int` (recommended;
  lookups then take `.toNat` under `kxc_stack_ok`'s `base ≤ sp`, base = top − 4096 ≥ 4096) or the
  disjointness rows gain a `kxcStackOk` premise. Coordinator: please settle with K-A.
