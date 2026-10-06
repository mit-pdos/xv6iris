/-
Weak: **the weak-memory base logic's ghost state** (M1c): the per-byte latest-write picture, the
C/D/S(/L/P) state protocol over the log, the lock word's value protocol and its alternation fold,
the protected-byte footprint, the violation-freedom predicate φ with its induction algebra (the
PURE half, §§1–5 below); and the cameras, the context name `CtxId`, the resources (the log
mono-list, the publication-floor token, the context write breadcrumb and the migration invariant,
the latest-write and C/D/S ghost maps and their fragments, the per-hart weak-state cells), the
state interpretations, the T2-0 / F3″ export seams, the read records, the `IrisGS` instance and
the Φ-free weak WP `WWP` (the IRIS half, §§6–10).

Rocq: `iris/WeakGhost.v` @ xxvzwolszwmp (1cc222280).

Rocq header (verbatim in substance, Rocq vocabulary): the Iris side of [WeakLang] — the three
PER-ERA ghost families of the design doc's Decision 5 base layer, the state interpretation over
[WeakLang.wgstate], and the [irisGS] instance for [weak_riscv_lang].  WHAT IS REUSED FROM THE
EXISTING TREE, VERBATIM: every REGISTER assertion and every DEVICE assertion is the tree's,
unchanged in statement and meaning; the byte memory is now the log + the per-byte latest-write
map.  THE THREE NEW FAMILIES: [weak_log_name] (a MONO-LIST over [wmsg]; [wlog_auth] in the state
interpretation, [wlog_lb] the persistent "the log extends this" snapshot; append-only in every
[wprim_step] arm except PowerOn, which is why this is a per-era resource); [weak_lat_name] (a
[ghost_map Z (nat * bv 8)], the PER-BYTE LATEST-WRITE map: [a ↪[γlat]{dq} (t, v)] is "timestamp
[t] is the latest write to byte [a], and it wrote [v]", tied to the real log by [wlat_agree]; M2's
[↦ₘ] is built on top of this); [weak_ws_name] (one gname PER HART, a [ghost_var wstate] in the
standard halves pattern — DEVIATION from the M1c brief's [ghost_map CPU wstate]: a single map
authority cannot be FOCUSED on one hart the way [gregs_interp_acc] focuses one hart's registers,
whereas the halves pattern makes the per-hart framing one [big_sepS_delete]).  SIMPLIFICATIONS,
all deliberate and M1c-local: SINGLE ERA (the state interpretation pins [wgpow g = true] and
[wggen g = 0] ([wgen_pin]) instead of carrying the generation counter, the started counter, the
era registry and the FS tie of [RiscvPtsto.power_interp]; the era indirection slots in at
[weak_state_interp]); NO vProp (views are explicit; M2 is where [monPred] arrives).

(The design records of the Rocq file — the five C/D/S/L/P states, the two design deltas of §2b,
the alternation fold, the protected-byte footprint, the kill lemmas, the publication-floor token
spelling, the breadcrumb/migration-invariant rationale, the seam decisions — are kept as the
comments on the corresponding Lean declarations below.)

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (name map below); the inductive `wcds` is `Wcds`, its
   constructors keep their Rocq spelling (`WClean`, `WDirty`, `WSync`, `WLock`, `WProt`).
2. VOCABULARY (as `Weak/WeakMem.lean` deviation 2): `l !! i` ↦ `l[i]?`; `is_Some o` ↦
   `o.isSome`; `S n` ↦ `n + 1`; `fin_to_nat c` ↦ `c.val`; `gmap Z X` ↦ `GMapF Int X` with
   `get?`/`insert`; `gmap Arch.pa (bv 8)` ↦ `GMapF PAddr (BitVec 8)` (= `MachCSL.Mem`, the
   `WeakLang` deviation 6 spelling); `map_to_list` ↦ `toList`, `list_to_map` ↦ `ofList`;
   `l1 `prefix_of` l2` ↦ `l1 <+: l2`; `(a <= x < b)` is `a ≤ x ∧ x < b` (one conjunctive
   premise, as in Rocq); `bool_decide` ↦ a decidable `if`; `Z_to_bv 8 0` ↦ `0#8`; `V ⊑ V'` ↦
   `V ≤ V'`.
3. `wlat_init` is stated through the Lean-only list `wlatInitList img` (Rocq inlines the list
   expression); `wlat_init_keys`/`wlat_init_nodup` are stated over it (`wlat_init_nodup`'s
   `NoDup (…).*1` is iris-lean's `NoDupKeys`, which is that by definition).
4. `wcds_init img := (λ _, WClean) <$> wlat_init img` is `ofList` of the same key list with the
   constant value `WClean` (`wcdsInitList`): iris-lean's `bigSepM_map` only covers a fmap that
   keeps the value type.  Same map (same keys, value `WClean`), same two lemmas.
5. `pa_z_inj` (an `Inj` instance) is the theorem `paZInj : Function.Injective paZ`.
6. Lean-only helpers: `lookupSnocSome` (the `lookup_app_Some` + `p - length log` case split every
   snoc proof of the Rocq file inlines), `wcdsInitNodup`, `ctxwrOf_empty`, `ctxwrValid`,
   `ctxwrMintUpd` (the update `ctx_migr_mint` inlines).
7. CAMERAS (the `Weak/WeakViewMono.lean` deviation 2 precedent).  iris-lean has no `gFunctors`
   lists and no `subG`: `weakGpreS`'s `inG`/`ghost_mapG`/`ghost_varG` fields are the
   `MonoListG GF Wmsg` / `GhostMapG GF Int (Nat × BitVec 8) (GMapF Int)` /
   `GhostMapG GF Int Wcds (GMapF Int)` / `GhostVarG GF Wstate` / `WeakViewG GF` fields of
   `WeakGpreS`; `wprotG`'s `inG Σ wprecR` is `WprotG`'s `MonoListG GF (Int × Nat)`.
   `weakGS`'s `weak_preGS` is the instance field `WeakGS.pre`.
8. THE LOG'S OWN.  Rocq spelled `own weak_log_name (●ML l)` by hand ("only the ALGEBRA-level
   [mono_list] exists in this Iris"); iris-lean has the library (`Iris.BI.Lib.MonoList`), so
   `wlog_auth`/`wlog_lb` (and `prot_recs`/`prot_read`'s owns) are `MonoList.auth_own γ (own 1)`
   / `MonoList.lb_own γ` — the same `own`s of the same algebra.
9. STATEMENT SHAPES (the `WeakViewMono`/`WeakVProp` convention): Rocq `P -∗ Q -∗ R` is
   `P ∗ Q ⊢ R`, `P -∗ Q ==∗ R` is `P ∗ Q ⊢ |==> R`, `P -∗ Q ={E}=∗ R` is `P ∗ Q ⊢ |={E}=> R`.
10. `Context {!riscvGS Σ, !weakGS Σ}`: the SC instance is `[MachGS hlc GF]`, and it is required
    only by the declarations that use it (the two state interpretations and their exports, the
    invariant seams `wlock_regd`/`wprot_regd`/`wprot_rd_regd` and their exports, `weak_irisGS`,
    `WWP`); everything else is stated at `[WeakGS GF]` alone.
11. DRIFT (SC vocabulary, `notes/weak-port-architecture.md` §C.3): Rocq 08-09
    `RiscvPtsto.gregs_interp regs` → Lean `[∗list] c ∈ cpus, regInterp c (regs c)` (the
    `eraInterp` conjunct); `reg_interp` (at the ambient `CpuId`) → `regInterp cpu`;
    `dev_interp ds` → `devInterpAt MachGS.era ds`; `riscvF_invGS` → `MachFixedGS.invGS`.
12. `CpuId` (Rocq's ambient-hart class) does not exist in Lean: `wmstate_interp` and
    `wws_interp_acc` take the hart `cpu : CPU` explicitly.
13. `wws_interp`'s `[∗ set] c ∈ fin_to_set CPU` is `[∗list] c ∈ cpus` (the `eraInterp`
    precedent); `<[cpu := ws']> f` is `updCpu f cpu ws'`.
14. `sync_win a (n : N)` takes `n : Nat` (`N.to_nat` dropped); `seq 0 n` is `List.range' 0 n`;
    `acc_addr` is `WeakInterp.accAddr`.
15. `ctxwr_of m := MaxNat <$> m` is `PartialMap.map MaxNat.ofNat m`; `{[k := MaxNat t]}` is
    `PartialMap.singleton k (MaxNat.ofNat t)`; `ctxwr_fmap_op`'s `≡` is `=` (iris-lean OFEs are
    Leibniz).
16. The `irisGS` instance is the `StateInterp WGState Empty GF` instance `weakStateInterpInst`
    plus `IrisGS_gen hlc WExpr GF` `weakIrisGS` (the `MachCSL.Resources` pattern); its Rocq
    `Next Obligation` is the `stateInterp_mono` field.
17. `wwp_post_irrel`'s `wp s E e Φ1 ⊢ wp s E e Φ2` is `WP e @ s ; E {{ Φ1 }} ⊢ …`; the WWP
    notations are `WWP e @ E` / `WWP e` at precedence 20 (Rocq level 20).
18. THE NEW `WGState` FIELDS (`wgitv`, `wgrt`, Lean-only, `WeakLang` deviations 2, 4) and
    `Wmstate.wmItv` are, like Rocq's `wgib`, NOT mentioned by the state interpretations: Rocq
    has no counterpart conjunct to port.

**Rocq → Lean name map.**  Pure half: `latest_val`→`latestVal`,
`latest_val_latest/ts/agree/app/plain_le`→`latestValLatest/Ts/Agree/App/PlainLe`,
`writes_in_app_new`→`writesInAppNew`, `not_writes_in_app_new`→`notWritesInAppNew`,
`wlat_agree`→`wlatAgree`, `wlat_agree_app/insert/store`→`wlatAgreeApp/Insert/Store`, `pa_z_inj`→
`paZInj`, `wlat_init`→`wlatInit`, `wlat_init_keys/nodup/lookup/agree`→`wlatInitKeys/Nodup/
Lookup/Agree`, `big_sepM_wlat_init`→`bigSepM_wlatInit`, `wplain_at`→`wplainAt`, `wpub_upto`→
`wpubUpto`, `wpub_upto_published/len/mono/prefix/app/unsnoc/rel`→`wpubUptoPublished/Len/Mono/
Prefix/App/Unsnoc/Rel`, `pub_transfer`→`pubTransfer`, `pub_transfer_refl/snoc`→
`pubTransferRefl/Snoc`, `wcds_clean/dirty/sync`→`wcdsClean/Dirty/Sync`, `wlock_zero4(_eq)`→
`wlockZero4(Eq)`, `wlock_shaped`→`wlockShaped`, `wlp_at`→`wlpAt`, `mwrites(_true/_false)`→
`mwrites(True/False)`, `alt_step`→`altStep`, `alt_step_rel/acq/fail/zero/nonzero`→
`altStepRel/Acq/Fail/Zero/Nonzero`, `alt_fold(_app/_quiet)`→`altFold(App/Quiet)`,
`wlp_holder_at`→`wlpHolderAt`, `wlp_alt`→`wlpAlt`, `wlp_holder_small/big/step/none_mono/is_Some/
quiet/hold/app/acq_exists`→`wlpHolderSmall/Big/Step/NoneMono/IsSome/Quiet/Hold/App/AcqExists`,
`msg_search`→`msgSearch`, `wlp_alt_app/store/register/value/two_acq/open`→`wlpAltApp/Store/
Register/Value/TwoAcq/Open`, `wcds_lock`→`wcdsLock`, `wcds_ob`→`wcdsOb`, `wcds_ob_ok`→
`wcdsObOk`, `wprot_at`→`wprotAt`, `wcds_prot`→`wcdsProt`, `wcds_ok`→`wcdsOk`, `wcds_ok_ob`→
`wcdsOkOb`, `is_wlock`→`isWlock`, `is_wprot`→`isWprot`, `wcds_prot_ob/wprot`→
`wcdsProtOb/Wprot`, `wcds_lock_clean/wlp/alt`→`wcdsLockClean/Wlp/Alt`, `wcds_clean_dirty`→
`wcdsCleanDirty`, `wcds_ok_app`→`wcdsOkApp`, `wcds_own_step`→`wcdsOwnStep`,
`wcds_ok_store_own/nonplain/clean/sync/lock/lock_acq/lock_fail/lock_rel/prot`→`wcdsOkStoreOwn/
Nonplain/Clean/Sync/Lock/LockAcq/LockFail/LockRel/Prot`, `wlock_shaped_writes`→
`wlockShapedWrites`, `wcds_ok_register(_prot)`→`wcdsOkRegister(Prot)`,
`wcds_ok_deregister_prot`→`wcdsOkDeregisterProt`, `wprot_writer_holds/cs`→
`wprotWriterHolds/Cs`, `wcds_dirty_flip(_pub)`→`wcdsDirtyFlip(Pub)`, `wcds_prot_flip`→
`wcdsProtFlip`, `wcds_agree`→`wcdsAgree`, `wcds_agree_app/insert/nonplain_win/nonplain1/
store_lock`→`wcdsAgreeApp/Insert/NonplainWin/Nonplain1/StoreLock`, `wcds_init(_agree)`→
`wcdsInit(Agree)`, `big_sepM_wcds_init`→`bigSepM_wcdsInit`, `nv_byte`→`nvByte`, `nv_hart`→
`nvHart`, `no_violation`→`noViolation`, `no_violation_hart/intro/nil/step/dma`→
`noViolationHart/Intro/Nil/Step/Dma`, `nv_hart_nil/app/app_own/coh_step`→`nvHartNil/App/AppOwn/
CohStep`, `nv_byte_mono/app/app_own/clean/dirty/sync/lock/prot/ok/unwritten/of_ok/of_free/
published`→`nvByteMono/App/AppOwn/Clean/Dirty/Sync/Lock/Prot/Ok/Unwritten/OfOk/OfFree/
Published`, `nv_free`→`nvFree`, `nv_ok`→`nvOk`, `nv_ok_of_free/clean/dirty/sync/unwritten/lock/
published`→`nvOkOfFree/Clean/Dirty/Sync/Unwritten/Lock/Published`, `nv_free_clean/sync/
unwritten/lock/prot/published`→`nvFreeClean/Sync/Unwritten/Lock/Prot/Published`;
`wcds_eq_dec`→`deriving DecidableEq`.
Iris half: `wprotG`→`WprotG` (field `wprot_recG`→`recG`), `weakGpreS`→`WeakGpreS` (fields
`weak_pre_logG/latG/cdsG/wsG/viewG`→`logG/latG/cdsG/wsG/viewG`), `weakGS`→`WeakGS` (fields
`weak_preGS`→`pre`, `weak_log_name/lat_name/cds_name/ws_name`→`logName/latName/cdsName/wsName`),
`CtxId`/`CtxNames`→`CtxId`/`CtxId.mk` (fields `ctx_vn/ctx_wn`→`ctxVn/ctxWn`),
`wlog_auth/lb/snapshot/valid/update`→`wlogAuth/Lb/Snapshot/Valid/Update`, `pub_floorn`→
`pubFloorn`, `pub_floor`→`pubFloor`, `pub_floor_agree/mint/le`→`pubFloorAgree/Mint/Le`,
`pub_covers_view(_intro/_mono)`→`pubCoversView(Intro/Mono)`, `wlog_ts_ok(_get/_bound)`→
`wlogTsOk(Get/Bound)`, `pub_floorn_bound`→`pubFloornBound`, `ctxwr_of`→`ctxwrOf`,
`ctx_wr_auth`→`ctxWrAuth`, `ctx_wrote_pos`→`ctxWrotePos`, `ctx_wrote(_intro/_byte/_mono)`→
`ctxWrote(Intro/Byte/Mono)`, `ctx_migr(_all/_all_run/_empty/_pub/_mint/_park)`→
`ctxMigr(All/AllRun/Empty/Pub/Mint/Park)`, `ctx_wr_alloc`→`ctxWrAlloc`, `ctxwr_fmap_op`→
`ctxwrFmapOp`, `wlat_elem`→`wlatElem`, `wcds_el`→`wcdsEl`, `wclean`→`wclean`, `wdirty`→
`wdirty`, `sync_byte`→`syncByte`, `sync_win`→`syncWin`, `sync_win_byte`→`syncWinByte`,
`sync_win4`→`syncWin4`, `wlock_st(_lookup/_clean_excl)`→`wlockSt(Lookup/CleanExcl)`,
`wprot_st(_lookup/_clean_excl/_lock_excl/_own_excl)`→`wprotSt(Lookup/CleanExcl/LockExcl/
OwnExcl)`, `wown_st(_lookup)`→`wownSt(Lookup)`, `wclean_own_st`→`wcleanOwnSt`,
`wdirty_own_st`→`wdirtyOwnSt`, `wcds_el_sync_excl`→`wcdsElSyncExcl`, `wlat_pointsto(_elem)`→
`wlatPointsto(Elem)`, `wlat_interp(_acc)`→`wlatInterp(Acc)`, `wlat_lookup(_elem)`→
`wlatLookup(Elem)`, `wcds_lookup`→`wcdsLookup`, `sync_byte_no_plain`→`syncByteNoPlain`,
`nv_byte_of_clean/pointsto/own_st/sync/prot`→`nvByteOfClean/Pointsto/OwnSt/Sync/Prot`,
`nv_free_of_clean/pointsto/sync/lock/prot/own_pure/own_pub`→`nvFreeOfClean/Pointsto/Sync/Lock/
Prot/OwnPure/OwnPub`, `nv_ok_of_own_st/pointsto/sync/lock/wown_ctx`→`nvOkOfOwnSt/Pointsto/Sync/
Lock/WownCtx`, `wlp_at_of_lock`→`wlpAtOfLock`, `wlp_alt_of_lock`→`wlpAltOfLock`,
`wlock_register`→`wlockRegister`, `wprot_register/deregister/flip/store`→`wprotRegister/
Deregister/Flip/Store`, `wprot_at_of_prot`→`wprotAtOfProt`, `wlat_flip(_pure/_pub)`→
`wlatFlip(Pure/Pub)`, `ctx_bc`→`ctxBc`, `wown_ctx`→`wownCtx`, `wown_ctx_of_clean/dirty/own_st`
→`wownCtxOfClean/Dirty/OwnSt`, `wown_ctx_retarget`→`wownCtxRetarget`, `sync_mint(_nil)`→
`syncMint(Nil)`, `wws_auth`→`wwsAuth`, `hart_ws`→`hartWs`, `hart_ws_agree/update`→
`hartWsAgree/Update`, `wws_interp(_acc)`→`wwsInterp(Acc)`, `hart_view(_intro)`→
`hartView(Intro)`, `wgen_pin`→`wgenPin`, `weak_state_interp`→`weakStateInterp`,
`wmstate_interp`→`wmstateInterp`, `weak_state_interp_export`→`weakStateInterpExport`,
`weak_state_interp_lat`→`WeakGhost.weakStateInterpLat` (FILE-QUALIFIED,
`notes/weak-port-dupnames.json`), `weak_state_interp_lockproto`→`weakStateInterpLockproto`,
`weak_state_interp_prot`→`weakStateInterpProt`, `wlock_regd(_export/_export_alt)`→
`wlockRegd(Export/ExportAlt)`, `wprot_regd(_export)`→`wprotRegd(Export)`,
`prot_recs(_ok/_alloc/_append)`→`protRecs(Ok/Alloc/Append)`, `prot_read(_agree)`→
`protRead(Agree)`, `wprot_rd_regd(_export)`→`wprotRdRegd(Export)`, `weak_irisGS`→`weakIrisGS`
(+ `weakStateInterpInst`), `wwp_post_irrel`→`wwpPostIrrel`, `wwp_triv(_eq)`→`wwpTriv(Eq)`;
every `_persistent`/`_timeless` instance is the camelCase stem plus the Rocq suffix
(`syncByte_persistent`, `wlogLb_persistent`, …; `wlogLb_timeless` is new).
Lean-only: `wlatInitList`, `wcdsInitList`, deviation 6's helpers.

**Not ported:** `wlogR`, `wprecR` (notations), `wprotΣ`, `subG_wprotG`, `weakΣ`,
`subG_weakGpreS` (deviation 7; uses checked: only Rocq `WeakAdequacy`/`WeakEvAdequacy`'s Σ
lists, whose Lean ports list the classes instead).

**Statements checked** (diffed against Rocq by hand): all; the changed spellings are the
deviations above.
-/
import Weak.WeakLang
import Weak.WeakViewMono
import Weak.WeakView
import MachCSL.Resources
import Iris.Std.PartialMap
import Iris.BI.BigOp.BigSepMap
import Iris.Algebra.IProp
import Iris.BI.Lib.MonoList
import Iris.Instances.Lib.GhostMap
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.Invariants
import Iris.ProgramLogic.WeakestPre

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std Iris.Std.PartialMap Iris.Std.LawfulPartialMap

/-! ## 1. The C/D/S state of a byte

THE C/D/S STATE of a byte (the φ-upgrade's three-state protocol; `weak-memory-phi-upgrade.md`
§1).  It rides in a SECOND ghost map, keyed by the same addresses as the latest-write map and
carrying NO value — which is exactly what lets the S state be entered by DISCARDING while the C
and D states keep a full-fraction element that a store must consume.

* `WClean` — every `WCplain` message on the byte is PUBLISHED (some later message of the same agent
  is `WCrel`).  The state `wlatPointsto` — hence `↦w` at every fraction — carries.
* `WDirty c` — the byte's UNPUBLISHED `WCplain` messages are all hart `c`'s.  Exclusive.
* `WSync` — the byte is permanently racy-readable and NO `WCplain` message ever writes it.
  Absorbing, entered once at boot by `syncMint`, PERSISTENT.
* `WLock base n0 h` — THE FOURTH STATE (tier-2 T2-0): the byte belongs to the REGISTERED LOCK WORD
  at 4-byte base `base`, registered when the log had length `n0`; a REFINEMENT of `WClean` (the
  clean obligation PLUS the lock word's VALUE PROTOCOL on the post-registration suffix, `wlpAt`).
  The third index is the lock's CURRENT HOLDER as the pure FOLD `wlpAlt` computes it (`none` free,
  `some t` held by agent `t`).
* `WProt γ base n0 r0 d` — THE FIFTH STATE (T2-0′ / F3″): the byte is in the PAYLOAD of the lock
  word at `base` (ghost `γ`, registration point `n0`), PROTECTED from log position `r0` on; its
  obligation is φ's at the dirty author `d` (`wcdsObOk`) PLUS the protection clause `wprotAt`.
  `γ` is IDENTIFICATION ONLY.  The generic PLAIN store rule refuses it by its
  `WClean ∨ WDirty c` premise; the NON-plain rule is true at it. -/
inductive Wcds where
  | WClean
  | WDirty (c : CPU)
  | WSync
  | WLock (base : Int) (n0 : Nat) (h : Option Nat)
  | WProt (γ : Iris.GName) (base : Int) (n0 r0 : Nat) (d : Option CPU)
  deriving DecidableEq

open Wcds

/-! ## 2. The per-byte latest-write picture, as a pure predicate -/

/-- "`t` is the latest write to byte `a` in `log`, and it wrote `v`" — `WeakMem.latest` with the
value pinned; what one `γlat` element means. -/
def latestVal (img : Image) (log : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  logByte img log t a = some v ∧ ¬ writesIn log a t log.length

theorem latestValLatest (img : Image) (log : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8) :
    latestVal img log a t v → latest img log a t := by
  rintro ⟨hv, hn⟩
  exact ⟨by rw [hv]; rfl, hn⟩

theorem latestValTs (img : Image) (log : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8) :
    latestVal img log a t v → latestTs log a = t :=
  fun h => latestTsEq img log a t (latestValLatest img log a t v h)

/-- The value is determined: two elements for the same byte agree. -/
theorem latestValAgree (img : Image) (log : List Wmsg) (a : Int) (t1 : Nat) (v1 : BitVec 8)
    (t2 : Nat) (v2 : BitVec 8) :
    latestVal img log a t1 v1 → latestVal img log a t2 v2 → t1 = t2 ∧ v1 = v2 := by
  intro h1 h2
  have ht : t1 = t2 :=
    latestUnique img log a t1 t2 (latestValLatest img log a t1 v1 h1)
      (latestValLatest img log a t2 v2 h2)
  subst ht
  refine ⟨rfl, ?_⟩
  have := h1.1.symm.trans h2.1
  exact Option.some.inj this

/-- A message list cell of a snoc (Lean-only helper, deviation 6). -/
theorem lookupSnocSome {log : List Wmsg} {m m' : Wmsg} {p : Nat} :
    (log ++ [m])[p]? = some m' → log[p]? = some m' ∨ (p = log.length ∧ m' = m) := by
  intro h
  rcases lookup_app_Some.1 h with h | ⟨hge, h⟩
  · exact .inl h
  · right
    cases hk : p - log.length with
    | zero => rw [hk] at h; simp at h; exact ⟨by omega, h.symm⟩
    | succ k => rw [hk] at h; simp at h

/-- THE FRAMING FACT the memory arms of M2 live on: an element survives an append that does not
write its byte. -/
theorem latestValApp (img : Image) (log ms : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8) :
    latestVal img log a t v →
    ¬ writesIn (log ++ ms) a log.length (log ++ ms).length →
    latestVal img (log ++ ms) a t v := by
  rintro ⟨hv, hn⟩ hnew
  have hle : t ≤ log.length := logByteBounded img log t a (by rw [hv]; rfl)
  refine ⟨by rw [logByteApp img log ms t a hle]; exact hv, ?_⟩
  rintro ⟨t', hlo, hhi, hw⟩
  by_cases hle' : t' ≤ log.length
  · exact hn (writesInAppInv log ms a t log.length (Nat.le_refl _) ⟨t', hlo, hle', hw⟩)
  · exact hnew ⟨t', by omega, hhi, hw⟩

/-- THE BACKWARD READING of `latestVal`'s second conjunct: EVERY message that writes byte `a` sits
at or below the byte's latest-write timestamp. -/
theorem latestValPlainLe (img : Image) (log : List Wmsg) (a : Int) (t : Nat) (v : BitVec 8)
    (p : Nat) (m : Wmsg) :
    latestVal img log a t v → log[p]? = some m → (msgByte m a).isSome → p + 1 ≤ t := by
  rintro ⟨_, hn⟩ hp hs
  apply Classical.byContradiction
  intro hgt
  apply hn
  have hlen := lookup_lt_Some hp
  exact ⟨p + 1, by omega, by omega, m, by rw [Nat.add_sub_cancel]; exact hp, hs⟩

/-- ... and the converse reading, for the arm that must IDENTIFY the offending message: a write in
the new window comes from one of the appended messages. -/
theorem writesInAppNew (log ms : List Wmsg) (a : Int) :
    writesIn (log ++ ms) a log.length (log ++ ms).length →
    ∃ m, m ∈ ms ∧ (msgByte m a).isSome := by
  rintro ⟨t, hlo, _, m, hm, hs⟩
  refine ⟨m, ?_, hs⟩
  rw [lookup_app_r (by omega)] at hm
  exact elem_of_list_lookup_2 hm

theorem notWritesInAppNew (log ms : List Wmsg) (a : Int) :
    (∀ m, m ∈ ms → msgByte m a = none) →
    ¬ writesIn (log ++ ms) a log.length (log ++ ms).length := by
  intro hno hw
  obtain ⟨m, hm, hs⟩ := writesInAppNew log ms a hw
  rw [hno m hm] at hs
  simp at hs

/-- The state interpretation's tie: EVERY element of the `γlat` map is accurate at the current
image and log.  Deliberately an agreement, not a domain equation. -/
def wlatAgree (img : Image) (log : List Wmsg) (m : GMapF Int (Nat × BitVec 8)) : Prop :=
  ∀ a tv, get? m a = some tv → latestVal img log a tv.1 tv.2

theorem wlatAgreeApp (img : Image) (log ms : List Wmsg) (m : GMapF Int (Nat × BitVec 8)) :
    wlatAgree img log m →
    (∀ a, (get? m a).isSome → ¬ writesIn (log ++ ms) a log.length (log ++ ms).length) →
    wlatAgree img (log ++ ms) m := by
  intro hag hno a tv ha
  exact latestValApp img log ms a _ _ (hag a tv ha) (hno a (by rw [ha]; rfl))

theorem wlatAgreeInsert (img : Image) (log : List Wmsg) (m : GMapF Int (Nat × BitVec 8)) (a : Int)
    (t : Nat) (v : BitVec 8) :
    wlatAgree img log m → latestVal img log a t v → wlatAgree img log (insert m a (t, v)) := by
  intro hag hl a' tv ha'
  by_cases h : a' = a
  · subst h
    rw [lookupInsert] at ha'
    cases ha'
    exact hl
  · rw [lookupInsertNe (Ne.symm h)] at ha'
    exact hag a' tv ha'

/-- THE STORE FRAMING FACT (consumed by `WeakVProp`'s store rule): appending a message that writes
EXACTLY the byte `a` keeps the whole map accurate once `a`'s element is retargeted at the new top
timestamp. -/
theorem wlatAgreeStore (img : Image) (log : List Wmsg) (m : Wmsg) (a : Int) (v' : BitVec 8)
    (mm : GMapF Int (Nat × BitVec 8)) :
    msgByte m a = some v' →
    (∀ a', a' ≠ a → msgByte m a' = none) →
    wlatAgree img log mm →
    wlatAgree img (log ++ [m]) (insert mm a (log.length + 1, v')) := by
  intro hma hother hag a' tv ha'
  by_cases h : a' = a
  · subst h
    rw [lookupInsert] at ha'
    cases ha'
    refine ⟨?_, ?_⟩
    · show logByte img (log ++ [m]) (log.length + 1) a' = some v'
      rw [logByteS, list_lookup_middle rfl]
      exact hma
    · rintro ⟨t, hlo, hhi, _⟩
      simp only [List.length_append, List.length_singleton] at hhi
      omega
  · rw [lookupInsertNe (Ne.symm h)] at ha'
    refine latestValApp img log [m] a' _ _ (hag a' tv ha') ?_
    refine notWritesInAppNew log [m] a' ?_
    intro m0 hm0
    rw [List.mem_singleton] at hm0
    subst hm0
    exact hother a' h

/-- The address seam's key translation is lossless (Rocq `pa_z_inj`). -/
theorem paZInj : Function.Injective paZ := by
  intro a b h
  rw [← zPaPaZ a, ← zPaPaZ b, h]

/-- The initial element list of an era: one element per byte of the era-initial image, at
timestamp 0 (Lean-only name, deviation 3). -/
def wlatInitList (img : GMapF PAddr (BitVec 8)) : List (Int × (Nat × BitVec 8)) :=
  (toList img).map (fun ab : PAddr × BitVec 8 => (paZ ab.1, ((0 : Nat), ab.2)))

/-- The INITIAL map of an era. -/
def wlatInit (img : GMapF PAddr (BitVec 8)) : GMapF Int (Nat × BitVec 8) :=
  ofList (wlatInitList img)

theorem wlatInitKeys (img : GMapF PAddr (BitVec 8)) :
    (wlatInitList img).map Prod.fst = ((toList img).map Prod.fst).map paZ := by
  simp [wlatInitList, List.map_map, Function.comp_def]

theorem wlatInitNodup (img : GMapF PAddr (BitVec 8)) : NoDupKeys (wlatInitList img) := by
  unfold NoDupKeys
  rw [wlatInitKeys]
  have h0 : NoDupKeys (toList img) := LawfulFiniteMap.toList_noDupKeys (M := GMapF PAddr) (m := img)
  exact List.nodup_map_of_injective paZInj h0

theorem wlatInitLookup (img : GMapF PAddr (BitVec 8)) (z : Int) (tv : Nat × BitVec 8) :
    get? (wlatInit img) z = some tv →
    ∃ a b, z = paZ a ∧ get? img a = some b ∧ tv = (0, b) := by
  intro hlk
  have hin := LawfulFiniteMap.mem_of_mem_ofList (M := GMapF Int) hlk
  obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp hin
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨a, b, rfl, toList_get.mp hab, rfl⟩

/-- The fresh era's map is accurate: nothing has been written, so every byte of the boot image is
its own latest write, at timestamp 0. -/
theorem wlatInitAgree (img : GMapF PAddr (BitVec 8)) : wlatAgree (imgZ img) [] (wlatInit img) := by
  intro z tv hlk
  obtain ⟨a, b, rfl, hab, rfl⟩ := wlatInitLookup img z tv hlk
  refine ⟨?_, ?_⟩
  · show logByte (imgZ img) [] 0 (paZ a) = some b
    rw [logByte0, imgZLookup]
    exact hab
  · rintro ⟨t, hlo, hhi, _⟩
    simp at hhi
    omega

section BigOps
open Iris.BI

/-- ... and the big-op the initial-resource bundle is stated with: the `Int`-keyed elements ARE the
`PAddr`-keyed image bytes. -/
theorem bigSepM_wlatInit {PROP : Type _} [Iris.BI PROP] (Φ : Int → Nat × BitVec 8 → PROP)
    (img : GMapF PAddr (BitVec 8)) :
    ([∗map] z ↦ tv ∈ wlatInit img, Φ z tv) ⊣⊢ ([∗map] a ↦ b ∈ img, Φ (paZ a) (0, b)) := by
  refine (BigSepM.bigSepM_ofList (wlatInitNodup img)).trans ?_
  unfold wlatInitList
  rw [BigSepL.bigSepL_map]
  exact .rfl

end BigOps

/-! ## 2b. The C/D/S invariant, PURELY over the log

THE ONE DESIGN DELTA that matters: the publication test does not read the AUTHOR's `wPub` (which
would force the whole `Wstate` family into `wlatInterp`); `WeakMem.storePost` raises the storing
agent's `wPub` to the store's OWN timestamp whenever the store is release-class, so "some message
of agent `tid` at a log position `≥ p` is `WCrel`" IMPLIES "position `p` is published by `tid`",
and it is a predicate of the LOG ALONE.

SECOND DELTA: the DMA/boot agents.  `WeakLang.wmsgsOfMap` stamps the disk's messages
`wmTid = some nDisk`, `wmAk = WCplain`, and the disk never issues a `WCrel`; clean-purity therefore
EXEMPTS every NON-HART author (`¬ tidIsHart`). -/

/-- `p` writes byte `a` with an owned-store (`WCplain`) message `m`. -/
def wplainAt (log : List Wmsg) (a : Int) (p : Nat) (m : Wmsg) : Prop :=
  log[p]? = some m ∧ (msgByte m a).isSome ∧ m.wmAk = .WCplain

/-- THE PUBLICATION FLOOR, PURELY (φ-upgrade §1.5): agent `tid` has published EVERY position below
`n` — one release message of `tid` at index `q` with `n ≤ q + 1`. -/
def wpubUpto (log : List Wmsg) (tid : Option Nat) (n : Nat) : Prop :=
  ∃ (q : Nat) (mq : Wmsg), n ≤ q + 1 ∧ log[q]? = some mq ∧ mq.wmTid = tid ∧ mq.wmAk = .WCrel

theorem wpubUptoPublished (log : List Wmsg) (tid : Option Nat) (n p : Nat) :
    wpubUpto log tid n → p < n → wpublished log tid p := by
  rintro ⟨q, mq, hn, hq, ht, hk⟩ hp
  exact ⟨q, mq, by omega, hq, ht, hk⟩

/-- Coverage cannot outrun the log. -/
theorem wpubUptoLen (log : List Wmsg) (tid : Option Nat) (n : Nat) :
    wpubUpto log tid n → n ≤ log.length := by
  rintro ⟨q, mq, hn, hq, _⟩
  have := lookup_lt_Some hq
  omega

theorem wpubUptoMono (log : List Wmsg) (tid : Option Nat) (n n' : Nat) :
    n' ≤ n → wpubUpto log tid n → wpubUpto log tid n' := by
  rintro hle ⟨q, mq, hn, hq, ht, hk⟩
  exact ⟨q, mq, by omega, hq, ht, hk⟩

/-- The token is a fact about a PREFIX, and it survives to the whole log. -/
theorem wpubUptoPrefix (l log : List Wmsg) (tid : Option Nat) (n : Nat) :
    l <+: log → wpubUpto l tid n → wpubUpto log tid n := by
  rintro ⟨ms, rfl⟩ ⟨q, mq, hn, hq, ht, hk⟩
  exact ⟨q, mq, hn, lookup_app_l_Some hq, ht, hk⟩

theorem wpubUptoApp (log ms : List Wmsg) (tid : Option Nat) (n : Nat) :
    wpubUpto log tid n → wpubUpto (log ++ ms) tid n :=
  wpubUptoPrefix log (log ++ ms) tid n (List.prefix_append log ms)

/-- ... AND THE CONVERSE ACROSS ONE MESSAGE THAT CANNOT BE THE PUBLISHER (φ-upgrade §1.6). -/
theorem wpubUptoUnsnoc (log : List Wmsg) (mnew : Wmsg) (tid : Option Nat) (n : Nat) :
    ¬ (mnew.wmTid = tid ∧ mnew.wmAk = .WCrel) →
    wpubUpto (log ++ [mnew]) tid n → wpubUpto log tid n := by
  rintro hne ⟨q, mq, hn, hq, ht, hk⟩
  rcases lookupSnocSome hq with hq | ⟨_, rfl⟩
  · exact ⟨q, mq, hn, hq, ht, hk⟩
  · exact (hne ⟨ht, hk⟩).elim

/-- THE TRANSFER CONDITION the owned leaves quantify over: the messages the log authority is ahead
of the interpretation by publish nothing on behalf of any hart other than `c`. -/
def pubTransfer (logA log : List Wmsg) (c : CPU) : Prop :=
  ∀ (c' : CPU) (n : Nat), c' ≠ c →
    wpubUpto logA (some c'.val) n → wpubUpto log (some c'.val) n

theorem pubTransferRefl (log : List Wmsg) (c : CPU) : pubTransfer log log c :=
  fun _ _ _ h => h

theorem pubTransferSnoc (log : List Wmsg) (mnew : Wmsg) (c : CPU) :
    mnew.wmTid = some c.val → pubTransfer (log ++ [mnew]) log c := by
  intro htid c' n hne
  refine wpubUptoUnsnoc log mnew _ n ?_
  rintro ⟨ht, _⟩
  apply hne
  rw [htid] at ht
  exact (Fin.ext (Option.some.inj ht)).symm

/-- THE MINT, purely: a release-class message appended at the top publishes every position of the
log it was appended to. -/
theorem wpubUptoRel (log : List Wmsg) (mrel : Wmsg) (tid : Option Nat) :
    mrel.wmTid = tid → mrel.wmAk = .WCrel → wpubUpto (log ++ [mrel]) tid (log.length + 1) := by
  intro ht hk
  exact ⟨log.length, mrel, Nat.le_refl _, list_lookup_middle rfl, ht, hk⟩

def wcdsClean (log : List Wmsg) (a : Int) : Prop :=
  ∀ p m, wplainAt log a p m → ¬ tidIsHart m.wmTid ∨ wpublished log m.wmTid p

def wcdsDirty (log : List Wmsg) (a : Int) (c : CPU) : Prop :=
  ∀ p m, wplainAt log a p m →
    ¬ tidIsHart m.wmTid ∨ wpublished log m.wmTid p ∨ m.wmTid = some c.val

def wcdsSync (log : List Wmsg) (a : Int) : Prop :=
  ∀ p m, ¬ wplainAt log a p m

/-! ### THE LOCK WORD'S VALUE PROTOCOL (tier-2 T2-0 / S6 §4, §6b)

The one fact about the kernel's lock words that is NOT machine-derivable: writes to a registered
lock word ALTERNATE acquire-RMW / release.  It rides the C/D/S protocol as its fourth per-byte
state. -/

/-- The four zero bytes a release stores. -/
def wlockZero4 : List (BitVec 8) := List.replicate 4 0#8

theorem wlockZero4Eq : wlockZero4 = [0#8, 0#8, 0#8, 0#8] := rfl

/-- `wlockShaped m` — the message is ACQUIRE-SHAPED or RELEASE-SHAPED: four bytes wide, never an
owned plain store, and EITHER exclusive (the acquire's `amoswap` write half) OR a write of the ZERO
word (the release).  DELIBERATE WEAKENING vs. the T2-0 spec's "`WCrel` ∧ zero" release arm: the
release leaf derives only `≠ WCplain`; the extra arm (`WCexcl` writing zero) is STRICTLY more
ordered than a release. -/
def wlockShaped (m : Wmsg) : Prop :=
  m.wmData.length = 4 ∧ m.wmAk ≠ .WCplain ∧ (m.wmAk = .WCexcl ∨ m.wmData = wlockZero4)

/-- THE EXPORTED PURE FACT, per byte: `a` is a byte of the lock word at `base`, and every message
AT OR AFTER the registration point `n0` that writes `a` is a whole-word, acquire- or
release-shaped message. -/
def wlpAt (log : List Wmsg) (a base : Int) (n0 : Nat) : Prop :=
  (base ≤ a ∧ a < base + 4) ∧
  ∀ p m, log[p]? = some m → n0 ≤ p → (msgByte m a).isSome → m.wmPa = base ∧ wlockShaped m

/-! ### THE ALTERNATION FOLD (tier-2 T2-0′ / F3′, route-b §4d.3′)

Replay the post-registration messages of the word, carrying the current holder `h : Option Nat`
(`none` = free, `some t` = held by agent `t`): a ZERO-DATA message (the release) requires the fold
to be held by its own author and leaves it free; an EXCLUSIVE NONZERO message is an `amoswap` write
half — from FREE a SUCCESSFUL ACQUIRE installing its author, from HELD a FAILED SWAP changing
nothing; anything else fails the fold.  The zero-data test comes FIRST because `wlockShaped`
admits an exclusive write of the zero word. -/

/-- Does `m` write byte `a`?  As a boolean, so that it may be matched on inside the fold. -/
def mwrites (a : Int) (m : Wmsg) : Bool :=
  match msgByte m a with
  | some _ => true
  | none => false

theorem mwritesTrue (a : Int) (m : Wmsg) : mwrites a m = true ↔ (msgByte m a).isSome := by
  unfold mwrites
  cases msgByte m a <;> simp

theorem mwritesFalse (a : Int) (m : Wmsg) : mwrites a m = false ↔ msgByte m a = none := by
  unfold mwrites
  cases msgByte m a <;> simp

def altStep (h : Option Nat) (m : Wmsg) : Option (Option Nat) :=
  if m.wmData = wlockZero4 then
    match h with
    | some t => if m.wmTid = some t then some none else none
    | none => none
  else if m.wmAk = .WCexcl then
    match h with
    | none =>
      match m.wmTid with
      | some t => some (some t)
      | none => none
    | some _ => some h
  else none

/-- THE THREE STEPS, as the leaves use them. -/
theorem altStepRel (m : Wmsg) (t : Nat) :
    m.wmData = wlockZero4 → m.wmTid = some t → altStep (some t) m = some none := by
  intro hd ht
  unfold altStep
  rw [if_pos hd]
  dsimp only
  rw [if_pos ht]

theorem altStepAcq (m : Wmsg) (t : Nat) :
    m.wmData ≠ wlockZero4 → m.wmAk = .WCexcl → m.wmTid = some t →
    altStep none m = some (some t) := by
  intro hd hk ht
  unfold altStep
  rw [if_neg hd, if_pos hk]
  dsimp only
  rw [ht]

theorem altStepFail (m : Wmsg) (t : Nat) :
    m.wmData ≠ wlockZero4 → m.wmAk = .WCexcl → altStep (some t) m = some (some t) := by
  intro hd hk
  unfold altStep
  rw [if_neg hd, if_pos hk]

/-- ... and their INVERSIONS, which is what the kill lemmas read. -/
theorem altStepZero (h : Option Nat) (m : Wmsg) (h' : Option Nat) :
    m.wmData = wlockZero4 → altStep h m = some h' →
    h' = none ∧ h ≠ none ∧ m.wmTid = h := by
  intro hd hs
  unfold altStep at hs
  rw [if_pos hd] at hs
  cases h with
  | none => simp at hs
  | some t =>
    dsimp only at hs
    by_cases ht : m.wmTid = some t
    · rw [if_pos ht] at hs
      exact ⟨(Option.some.inj hs).symm, by simp, ht⟩
    · rw [if_neg ht] at hs
      simp at hs

theorem altStepNonzero (h : Option Nat) (m : Wmsg) (h' : Option Nat) :
    m.wmData ≠ wlockZero4 → altStep h m = some h' →
    m.wmAk = .WCexcl ∧ h' ≠ none ∧ (h = none → h' = m.wmTid) ∧ (h ≠ none → h' = h) := by
  intro hd hs
  unfold altStep at hs
  rw [if_neg hd] at hs
  by_cases hk : m.wmAk = .WCexcl
  · rw [if_pos hk] at hs
    cases h with
    | some t =>
      dsimp only at hs
      have := (Option.some.inj hs).symm
      subst this
      refine ⟨hk, ?_, ?_, fun _ => rfl⟩
      · simp
      · intro hc; cases hc
    | none =>
      dsimp only at hs
      cases ht : m.wmTid with
      | none => rw [ht] at hs; simp at hs
      | some t =>
        rw [ht] at hs
        have := (Option.some.inj hs).symm
        subst this
        refine ⟨hk, ?_, fun _ => rfl, ?_⟩
        · simp
        · intro hc; exact (hc rfl).elim
  · rw [if_neg hk] at hs
    simp at hs

def altFold (a : Int) (h : Option Nat) (ms : List Wmsg) : Option (Option Nat) :=
  match ms with
  | [] => some h
  | m :: ms' =>
    if mwrites a m then
      match altStep h m with
      | some h' => altFold a h' ms'
      | none => none
    else altFold a h ms'

theorem altFoldApp (a : Int) (h : Option Nat) (ms1 ms2 : List Wmsg) :
    altFold a h (ms1 ++ ms2) =
      match altFold a h ms1 with
      | some h' => altFold a h' ms2
      | none => none := by
  induction ms1 generalizing h with
  | nil => rfl
  | cons m ms1 ih =>
    simp only [List.cons_append, altFold]
    cases hw : mwrites a m with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ih h
    | true =>
      simp only [↓reduceIte]
      cases hs : altStep h m with
      | none => rfl
      | some h' => exact ih h'

theorem altFoldQuiet (a : Int) (h : Option Nat) (ms : List Wmsg) :
    (∀ m, m ∈ ms → msgByte m a = none) → altFold a h ms = some h := by
  induction ms with
  | nil => intro _; rfl
  | cons m ms ih =>
    intro hno
    simp only [altFold]
    rw [(mwritesFalse a m).2 (hno m (List.mem_cons_self))]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ih (fun m' hm' => hno m' (List.mem_cons_of_mem _ hm'))

/-- THE FOLD AT A POSITION: replay the messages of the log in the window `[n0, p)` that write
`a`.  `some h`: held by `h` just BEFORE position `p`; `none`: not a legal alternation. -/
def wlpHolderAt (log : List Wmsg) (a : Int) (n0 p : Nat) : Option (Option Nat) :=
  altFold a none ((log.take p).drop n0)

/-- THE EXPORTED FACT: the whole post-registration suffix folds, and ends at holder `h`. -/
def wlpAlt (log : List Wmsg) (a : Int) (n0 : Nat) (h : Option Nat) : Prop :=
  n0 ≤ log.length ∧ wlpHolderAt log a n0 log.length = some h

theorem wlpHolderSmall (log : List Wmsg) (a : Int) (n0 p : Nat) :
    p ≤ n0 → wlpHolderAt log a n0 p = some none := by
  intro hp
  unfold wlpHolderAt
  rw [drop_ge (by rw [length_take]; omega)]
  rfl

theorem wlpHolderBig (log : List Wmsg) (a : Int) (n0 p : Nat) :
    log.length ≤ p → wlpHolderAt log a n0 p = wlpHolderAt log a n0 log.length := by
  intro hp
  unfold wlpHolderAt
  rw [take_ge hp, take_ge (Nat.le_refl _)]

theorem wlpHolderStep (log : List Wmsg) (a : Int) (n0 p : Nat) (m : Wmsg) :
    n0 ≤ p → log[p]? = some m →
    wlpHolderAt log a n0 (p + 1) =
      match wlpHolderAt log a n0 p with
      | none => none
      | some h => if mwrites a m then altStep h m else some h := by
  intro hn0 hp
  have hlt := lookup_lt_Some hp
  unfold wlpHolderAt
  rw [take_S_r hp, drop_app_le (by rw [length_take]; omega), altFoldApp]
  cases altFold a none ((log.take p).drop n0) with
  | none => rfl
  | some h =>
    simp only [altFold]
    cases mwrites a m with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      cases altStep h m <;> rfl

theorem wlpHolderNoneMono (log : List Wmsg) (a : Int) (n0 p q : Nat) :
    p ≤ q → wlpHolderAt log a n0 p = none → wlpHolderAt log a n0 q = none := by
  induction q with
  | zero =>
    intro hpq hp
    have : p = 0 := by omega
    subst this; exact hp
  | succ q ih =>
    intro hpq hp
    by_cases hpe : p = q + 1
    · subst hpe; exact hp
    have hq : wlpHolderAt log a n0 q = none := ih (by omega) hp
    by_cases hlt : q < n0
    · rw [wlpHolderSmall log a n0 q (by omega)] at hq; cases hq
    cases hm : log[q]? with
    | some m => rw [wlpHolderStep log a n0 q m (by omega) hm, hq]
    | none =>
      have := lookup_ge_None_1 hm
      rw [wlpHolderBig log a n0 (q + 1) (by omega), ← wlpHolderBig log a n0 q (by omega)]
      exact hq

theorem wlpHolderIsSome (log : List Wmsg) (a : Int) (n0 p q : Nat) (h : Option Nat) :
    p ≤ q → wlpHolderAt log a n0 q = some h → ∃ h', wlpHolderAt log a n0 p = some h' := by
  intro hpq hq
  cases hp : wlpHolderAt log a n0 p with
  | some h' => exact ⟨h', rfl⟩
  | none =>
    rw [wlpHolderNoneMono log a n0 p q hpq hp] at hq
    cases hq

/-- The fold does not move across a stretch that does not write `a`. -/
theorem wlpHolderQuiet (log : List Wmsg) (a : Int) (n0 p q : Nat) :
    p ≤ q →
    (∀ r mr, (p ≤ r ∧ r < q) → log[r]? = some mr → msgByte mr a = none) →
    wlpHolderAt log a n0 q = wlpHolderAt log a n0 p := by
  induction q with
  | zero =>
    intro hpq _
    have : p = 0 := by omega
    subst this; rfl
  | succ q ih =>
    intro hpq hq
    by_cases hpe : p = q + 1
    · subst hpe; rfl
    rw [← ih (by omega) (fun r mr hr => hq r mr ⟨hr.1, by omega⟩)]
    by_cases hlt : q < n0
    · rw [wlpHolderSmall log a n0 (q + 1) (by omega), wlpHolderSmall log a n0 q (by omega)]
    cases hm : log[q]? with
    | some m =>
      rw [wlpHolderStep log a n0 q m (by omega) hm,
        (mwritesFalse a m).2 (hq q m ⟨by omega, by omega⟩ hm)]
      cases wlpHolderAt log a n0 q <;> rfl
    | none =>
      have := lookup_ge_None_1 hm
      rw [wlpHolderBig log a n0 (q + 1) (by omega), ← wlpHolderBig log a n0 q (by omega)]

/-- ... and it does not move across a stretch of FAILED SWAPS: while the word is held and nobody
writes zero to it, the holder stays. -/
theorem wlpHolderHold (log : List Wmsg) (a : Int) (n0 p q : Nat) (hv : Nat) (h2 : Option Nat) :
    p ≤ q →
    wlpHolderAt log a n0 p = some (some hv) →
    wlpHolderAt log a n0 q = some h2 →
    (∀ r mr, (p ≤ r ∧ r < q) → log[r]? = some mr →
       (msgByte mr a).isSome → mr.wmData ≠ wlockZero4) →
    h2 = some hv := by
  induction q generalizing h2 with
  | zero =>
    intro hpq hp hq _
    have : p = 0 := by omega
    subst this
    rw [hp] at hq
    exact (Option.some.inj hq).symm
  | succ q ih =>
    intro hpq hp hq hnz
    by_cases hpe : p = q + 1
    · subst hpe
      rw [hp] at hq
      exact (Option.some.inj hq).symm
    obtain ⟨h1, hq1⟩ := wlpHolderIsSome log a n0 q (q + 1) h2 (by omega) hq
    have hh1 : h1 = some hv :=
      ih h1 (by omega) hp hq1 (fun r mr hr => hnz r mr ⟨hr.1, by omega⟩)
    subst hh1
    have hn0 : n0 ≤ q := by
      apply Classical.byContradiction
      intro hgt
      rw [wlpHolderSmall log a n0 p (by omega)] at hp
      simp at hp
    cases hm : log[q]? with
    | some m =>
      rw [wlpHolderStep log a n0 q m hn0 hm, hq1] at hq
      dsimp only at hq
      cases hw : mwrites a m with
      | false =>
        rw [hw] at hq
        simp only [Bool.false_eq_true, ↓reduceIte] at hq
        exact (Option.some.inj hq).symm
      | true =>
        rw [hw] at hq
        simp only [↓reduceIte] at hq
        exact (altStepNonzero (some hv) m h2
          (hnz q m ⟨by omega, by omega⟩ hm ((mwritesTrue a m).1 hw)) hq).2.2.2 (by simp)
    | none =>
      have := lookup_ge_None_1 hm
      rw [wlpHolderBig log a n0 (q + 1) (by omega), ← wlpHolderBig log a n0 q (by omega), hq1] at hq
      exact (Option.some.inj hq).symm

/-- A bounded search for the FIRST position of a window at which a decidable property of the
message holds. -/
theorem msgSearch (f : Wmsg → Bool) (log : List Wmsg) (s0 e : Nat) :
    (∀ r mr, (s0 ≤ r ∧ r < e) → log[r]? = some mr → f mr = false) ∨
    (∃ r mr, (s0 ≤ r ∧ r < e) ∧ log[r]? = some mr ∧ f mr = true ∧
      ∀ r' mr', (s0 ≤ r' ∧ r' < r) → log[r']? = some mr' → f mr' = false) := by
  induction e with
  | zero => exact .inl fun r mr hr => absurd hr.2 (Nat.not_lt_zero _)
  | succ e ih =>
    rcases ih with hno | ⟨r, mr, hr, hlk, hf, hfirst⟩
    · cases hm : log[e]? with
      | some m =>
        cases hf : f m with
        | true =>
          by_cases hle : s0 ≤ e
          · exact .inr ⟨e, m, ⟨hle, by omega⟩, hm, hf, fun r' mr' hr' => hno r' mr' hr'⟩
          · exact .inl fun r mr hr => absurd hr.1 (by omega)
        | false =>
          refine .inl fun r mr hr hlk => ?_
          by_cases hre : r = e
          · subst hre; rw [hm] at hlk; cases hlk; exact hf
          · exact hno r mr ⟨hr.1, by omega⟩ hlk
      | none =>
        refine .inl fun r mr hr hlk => ?_
        by_cases hre : r = e
        · subst hre; rw [hm] at hlk; cases hlk
        · exact hno r mr ⟨hr.1, by omega⟩ hlk
    · exact .inr ⟨r, mr, ⟨hr.1, by omega⟩, hlk, hf, hfirst⟩

/-- THE FRAMING FACT for the fold: messages that do not write `a` do not move it. -/
theorem wlpAltApp (log ms : List Wmsg) (a : Int) (n0 : Nat) (h : Option Nat) :
    (∀ m, m ∈ ms → msgByte m a = none) → wlpAlt log a n0 h → wlpAlt (log ++ ms) a n0 h := by
  rintro hno ⟨hlen, hf⟩
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  unfold wlpHolderAt at hf ⊢
  rw [take_ge (Nat.le_refl _)] at hf
  rw [take_ge (Nat.le_refl _), drop_app_le hlen, altFoldApp, hf]
  exact altFoldQuiet a h ms hno

/-- ... and THE STEP: one message on the word moves it by `altStep`. -/
theorem wlpAltStore (log : List Wmsg) (mnew : Wmsg) (a : Int) (n0 : Nat) (h h' : Option Nat) :
    wlpAlt log a n0 h → (msgByte mnew a).isSome → altStep h mnew = some h' →
    wlpAlt (log ++ [mnew]) a n0 h' := by
  rintro ⟨hlen, hf⟩ hw hst
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  unfold wlpHolderAt at hf ⊢
  rw [take_ge (Nat.le_refl _)] at hf
  rw [take_ge (Nat.le_refl _), drop_app_le hlen, altFoldApp, hf]
  simp only [altFold, (mwritesTrue a mnew).2 hw, ↓reduceIte, hst]

/-- The registration point's own value: at `n0 = length log` the window is empty, so the word is
FREE. -/
theorem wlpAltRegister (log : List Wmsg) (a : Int) : wlpAlt log a log.length none :=
  ⟨Nat.le_refl _, wlpHolderSmall log a log.length log.length (Nat.le_refl _)⟩

/-! ### WHAT THE FOLD SAYS ABOUT THE WORD'S VALUE, AND THE TWO KILL LEMMAS -/

/-- LOCALITY FACT (i): the fold's state is the word's CURRENT VALUE, read off the LATEST message
writing the byte.  The word is free exactly when that message wrote zero. -/
theorem wlpAltValue (log : List Wmsg) (a : Int) (n0 : Nat) (h : Option Nat) (p : Nat) (m : Wmsg) :
    wlpAlt log a n0 h → n0 ≤ p →
    log[p]? = some m → (msgByte m a).isSome →
    (∀ q mq, p < q → log[q]? = some mq → msgByte mq a = none) →
    (h = none ↔ m.wmData = wlockZero4) := by
  rintro ⟨hlen, hf⟩ hn0 hp hw hlast
  have hlt := lookup_lt_Some hp
  have hsp : wlpHolderAt log a n0 (p + 1) = some h := by
    rw [← hf]
    exact (wlpHolderQuiet log a n0 (p + 1) log.length (by omega)
      (fun r mr hr => hlast r mr (by omega))).symm
  obtain ⟨hp', hhp⟩ := wlpHolderIsSome log a n0 p (p + 1) h (by omega) hsp
  rw [wlpHolderStep log a n0 p m hn0 hp, hhp] at hsp
  dsimp only at hsp
  rw [(mwritesTrue a m).2 hw] at hsp
  simp only [↓reduceIte] at hsp
  constructor
  · intro hnone
    subst hnone
    apply Classical.byContradiction
    intro hne
    exact (altStepNonzero hp' m none hne hsp).2.1 rfl
  · intro hd
    exact (altStepZero hp' m h hd hsp).1

/-- KILL LEMMA 1 — TWO ACQUIRES ARE SEPARATED BY THE FIRST ONE'S RELEASE.  `p` is a successful
acquire by agent `i`; the word is FREE again just before `q`.  Then `i` released in between.  (The
statement holds for `i = j` too.) -/
theorem wlpAltTwoAcq (log : List Wmsg) (a : Int) (n0 p q : Nat) (mp : Wmsg) (i : Nat) :
    n0 ≤ p → p < q →
    log[p]? = some mp → (msgByte mp a).isSome →
    mp.wmData ≠ wlockZero4 → mp.wmTid = some i →
    wlpHolderAt log a n0 p = some none →
    wlpHolderAt log a n0 q = some none →
    ∃ r mr, (p < r ∧ r < q) ∧ log[r]? = some mr ∧
      (msgByte mr a).isSome ∧ mr.wmData = wlockZero4 ∧ mr.wmTid = some i := by
  intro hn0 hpq hp hw hnz hti hfp hfq
  -- the acquire installs `i`
  obtain ⟨h1, hsp⟩ := wlpHolderIsSome log a n0 (p + 1) q none (by omega) hfq
  have hst : altStep none mp = some h1 := by
    rw [← hsp, wlpHolderStep log a n0 p mp hn0 hp, hfp]
    dsimp only
    rw [(mwritesTrue a mp).2 hw]
    simp only [↓reduceIte]
  have hfree := (altStepNonzero none mp h1 hnz hst).2.2.1 rfl
  rw [hfree, hti] at hsp
  -- the first release after it
  rcases msgSearch (fun m => mwrites a m && decide (m.wmData = wlockZero4)) log (p + 1) q with
    hnone | ⟨r, mr, hr, hlk, hf, hfirst⟩
  · exfalso
    have hcontra : (none : Option Nat) = some i := by
      refine wlpHolderHold log a n0 (p + 1) q i none (by omega) hsp hfq ?_
      intro s ms hs hls hws hzs
      have := hnone s ms hs hls
      rw [(mwritesTrue a ms).2 hws] at this
      simp [hzs] at this
    cases hcontra
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨hf1, hf2⟩ := hf
    have hf1' := (mwritesTrue a mr).1 hf1
    refine ⟨r, mr, ⟨by omega, hr.2⟩, hlk, hf1', hf2, ?_⟩
    -- the holder is still `i` at `r`
    obtain ⟨hr', hhr⟩ := wlpHolderIsSome log a n0 r q none (by omega) hfq
    have hhr' : hr' = some i := by
      refine wlpHolderHold log a n0 (p + 1) r i hr' hr.1 hsp hhr ?_
      intro s ms hs hls hws hzs
      have := hfirst s ms hs hls
      rw [(mwritesTrue a ms).2 hws] at this
      simp [hzs] at this
    subst hhr'
    obtain ⟨h2, hsr⟩ := wlpHolderIsSome log a n0 (r + 1) q none (by omega) hfq
    rw [wlpHolderStep log a n0 r mr (by omega) hlk, hhr] at hsr
    dsimp only at hsr
    rw [hf1] at hsr
    simp only [↓reduceIte] at hsr
    exact (altStepZero (some i) mr h2 hf2 hsr).2.2

/-- KILL LEMMA 2 — THE CURRENT HOLDER'S CRITICAL SECTION IS STILL OPEN.  If the word ends HELD,
then its holder's LAST acquire has no release after it at all. -/
theorem wlpAltOpen (log : List Wmsg) (a : Int) (n0 : Nat) (i p : Nat) (mp : Wmsg) :
    wlpAlt log a n0 (some i) →
    n0 ≤ p → log[p]? = some mp → (msgByte mp a).isSome →
    wlpHolderAt log a n0 p = some none →
    (∀ r mr, p < r → log[r]? = some mr → (msgByte mr a).isSome →
       wlpHolderAt log a n0 r ≠ some none) →
    ∀ r mr, p < r → log[r]? = some mr → (msgByte mr a).isSome → mr.wmData ≠ wlockZero4 := by
  rintro ⟨hlen, hf⟩ hn0 _ _ _ hlast r mr hr hlk hwr hzero
  have hrlt := lookup_lt_Some hlk
  -- the release frees the word at `r + 1`
  obtain ⟨hr', hhr⟩ := wlpHolderIsSome log a n0 r log.length (some i) (by omega) hf
  obtain ⟨h2, hsr⟩ := wlpHolderIsSome log a n0 (r + 1) log.length (some i) (by omega) hf
  have hst : altStep hr' mr = some h2 := by
    rw [← hsr, wlpHolderStep log a n0 r mr (by omega) hlk, hhr]
    dsimp only
    rw [(mwritesTrue a mr).2 hwr]
    simp only [↓reduceIte]
  have h2none := (altStepZero hr' mr h2 hzero hst).1
  subst h2none
  -- ... and the word can only be held again by a LATER successful acquire
  rcases msgSearch (mwrites a) log (r + 1) log.length with
    hnone | ⟨s, ms, hs, hls, hfs, hfirst⟩
  · rw [wlpHolderQuiet log a n0 (r + 1) log.length (by omega)
      (fun s2 ms2 hs2 hls2 => (mwritesFalse a ms2).1 (hnone s2 ms2 hs2 hls2)), hsr] at hf
    cases hf
  · apply hlast s ms (by omega) hls ((mwritesTrue a ms).1 hfs)
    rw [wlpHolderQuiet log a n0 (r + 1) s hs.1
      (fun s' ms' hs' hls' => (mwritesFalse a ms').1 (hfirst s' ms' hs' hls'))]
    exact hsr

/-- ... and the state's own obligation: the protocol ON TOP OF clean, the alternation included. -/
def wcdsLock (log : List Wmsg) (a base : Int) (n0 : Nat) (h : Option Nat) : Prop :=
  wcdsClean log a ∧ wlpAt log a base n0 ∧ wlpAlt log a n0 h

/-! ### THE PROTECTED-BYTE FOOTPRINT (tier-2 T2-0′ / F3″, route-b §4d.3′)

A byte declared to be in the lock's payload may be plain-written only by the hart the fold names as
the holder.  `n0` is the LOCK WORD's registration point (the fold's origin), `r0` the BYTE's: the
protection clause is quantified over `r0 ≤ p`. -/

/-- The fold does not see an append below its cut point. -/
theorem wlpHolderApp (log ms : List Wmsg) (a : Int) (n0 p : Nat) :
    p ≤ log.length → wlpHolderAt (log ++ ms) a n0 p = wlpHolderAt log a n0 p := by
  intro hp
  unfold wlpHolderAt
  rw [take_app_le hp]

/-- The φ obligation, indexed by the DIRTY AUTHOR: `none` is `WClean`'s, `some c` is
`WDirty c`'s. -/
def wcdsOb (b : Option CPU) : Wcds :=
  match b with
  | none => WClean
  | some c => WDirty c

def wcdsObOk (log : List Wmsg) (a : Int) (d : Option CPU) : Prop :=
  match d with
  | none => wcdsClean log a
  | some c => wcdsDirty log a c

/-- THE PROTECTION CLAUSE, per byte: every owned store at or after `r0` that reaches the byte is
the lock's holder's ("the fold is DEFINED at `p` and names exactly this message's author"). -/
def wprotAt (log : List Wmsg) (a base : Int) (n0 r0 : Nat) : Prop :=
  n0 ≤ r0 ∧
  ∀ p m, log[p]? = some m → r0 ≤ p → (msgByte m a).isSome →
    m.wmAk = .WCplain → wlpHolderAt log base n0 p = some m.wmTid

/-- ... and the state's own obligation: φ's, at the dirty author the state carries, PLUS the
protection clause. -/
def wcdsProt (log : List Wmsg) (a base : Int) (n0 r0 : Nat) (d : Option CPU) : Prop :=
  wcdsObOk log a d ∧ wprotAt log a base n0 r0

def wcdsOk (log : List Wmsg) (a : Int) (s : Wcds) : Prop :=
  match s with
  | WClean => wcdsClean log a
  | WDirty c => wcdsDirty log a c
  | WSync => wcdsSync log a
  | WLock base n0 h => wcdsLock log a base n0 h
  | WProt _ base n0 r0 d => wcdsProt log a base n0 r0 d

theorem wcdsOkOb (log : List Wmsg) (a : Int) (d : Option CPU) :
    wcdsOk log a (wcdsOb d) ↔ wcdsObOk log a d := by
  cases d <;> exact Iff.rfl

/-- The state a NON-PROTOCOL store may be taken at: a `WLock` byte is exactly the one that may
not. -/
def isWlock (s : Wcds) : Bool :=
  match s with
  | WLock _ _ _ => true
  | _ => false

/-- ... and the FIFTH state's boolean, for a site that wants to name it. -/
def isWprot (s : Wcds) : Bool :=
  match s with
  | WProt _ _ _ _ _ => true
  | _ => false

theorem wcdsProtOb (log : List Wmsg) (a : Int) (γ : Iris.GName) (base : Int) (n0 r0 : Nat)
    (d : Option CPU) : wcdsOk log a (WProt γ base n0 r0 d) → wcdsObOk log a d :=
  fun h => h.1

theorem wcdsProtWprot (log : List Wmsg) (a : Int) (γ : Iris.GName) (base : Int) (n0 r0 : Nat)
    (d : Option CPU) : wcdsOk log a (WProt γ base n0 r0 d) → wprotAt log a base n0 r0 :=
  fun h => h.2

theorem wcdsLockClean (log : List Wmsg) (a base : Int) (n0 : Nat) (h : Option Nat) :
    wcdsOk log a (WLock base n0 h) → wcdsClean log a :=
  fun h => h.1

theorem wcdsLockWlp (log : List Wmsg) (a base : Int) (n0 : Nat) (h : Option Nat) :
    wcdsOk log a (WLock base n0 h) → wlpAt log a base n0 :=
  fun h => h.2.1

theorem wcdsLockAlt (log : List Wmsg) (a base : Int) (n0 : Nat) (h : Option Nat) :
    wcdsOk log a (WLock base n0 h) → wlpAlt log a n0 h :=
  fun h => h.2.2

theorem wcdsCleanDirty (log : List Wmsg) (a : Int) (c : CPU) :
    wcdsClean log a → wcdsDirty log a c := by
  intro h p m hp
  rcases h p m hp with h | h
  · exact .inl h
  · exact .inr (.inl h)

/-- THE FRAMING FACT: a byte the appended messages do not write keeps its state, whatever it is. -/
theorem wcdsOkApp (log ms : List Wmsg) (a : Int) (s : Wcds) :
    (∀ m, m ∈ ms → msgByte m a = none) → wcdsOk log a s → wcdsOk (log ++ ms) a s := by
  intro hno
  have hback : ∀ p m, wplainAt (log ++ ms) a p m → wplainAt log a p m := by
    rintro p m ⟨hp, hs, hk⟩
    rcases lookup_app_Some.1 hp with hp | ⟨_, hp⟩
    · exact ⟨hp, hs, hk⟩
    · exfalso
      rw [hno m (elem_of_list_lookup_2 hp)] at hs
      simp at hs
  have hcln : wcdsClean log a → wcdsClean (log ++ ms) a := by
    intro hcl p m hp
    rcases hcl p m (hback p m hp) with h | h
    · exact .inl h
    · exact .inr (wpublishedApp log ms _ p h)
  have hdrt : ∀ c, wcdsDirty log a c → wcdsDirty (log ++ ms) a c := by
    intro c hdi p m hp
    rcases hdi p m (hback p m hp) with h | h | h
    · exact .inl h
    · exact .inr (.inl (wpublishedApp log ms _ p h))
    · exact .inr (.inr h)
  cases s with
  | WClean => exact hcln
  | WDirty c => exact hdrt c
  | WSync => exact fun hsy p m hp => hsy p m (hback p m hp)
  | WLock base n0 h =>
    rintro ⟨hcl, ⟨hrng, hlp⟩, halt⟩
    refine ⟨hcln hcl, ⟨hrng, ?_⟩, wlpAltApp log ms a n0 h hno halt⟩
    intro p m hp hn0 hs
    rcases lookup_app_Some.1 hp with hp | ⟨_, hp⟩
    · exact hlp p m hp hn0 hs
    · exfalso
      rw [hno m (elem_of_list_lookup_2 hp)] at hs
      simp at hs
  | WProt γ base n0 r0 d =>
    -- φ's half frames as its own state does; the protection clause is about OLD messages only
    rintro ⟨hob, hle, hpr⟩
    refine ⟨?_, hle, ?_⟩
    · cases d with
      | none => exact hcln hob
      | some c => exact hdrt c hob
    · intro p m hp hr0 hs hk
      rcases lookup_app_Some.1 hp with hp | ⟨_, hp⟩
      · rw [wlpHolderApp log ms base n0 p (by have := lookup_lt_Some hp; omega)]
        exact hpr p m hp hr0 hs hk
      · exfalso
        rw [hno m (elem_of_list_lookup_2 hp)] at hs
        simp at hs

/-- ... and the STORE step at the byte the message writes: an owned (`WCplain`) store dirties, a
release (`WCrel`) store CLEANS (the D→C flip), an exclusive (`WCexcl`) store leaves the state
alone. -/
def wcdsOwnStep (c : CPU) (k : WmClass) (s : Wcds) : Wcds :=
  match k with
  | .WCplain => WDirty c
  | .WCrel => WClean
  | .WCexcl => s

theorem wcdsOkStoreOwn (log : List Wmsg) (mnew : Wmsg) (a : Int) (c : CPU) (s : Wcds) :
    mnew.wmTid = some c.val →
    (s = WClean ∨ s = WDirty c) →
    wcdsOk log a s →
    wcdsOk (log ++ [mnew]) a (wcdsOwnStep c mnew.wmAk s) := by
  intro htid hs hok
  -- the old obligations, transported
  have hdi : wcdsDirty log a c := by
    rcases hs with rfl | rfl
    · exact wcdsCleanDirty log a c hok
    · exact hok
  have hback : ∀ p m, wplainAt (log ++ [mnew]) a p m →
      wplainAt log a p m ∨ (p = log.length ∧ m = mnew) := by
    rintro p m ⟨hp, hsm, hk⟩
    rcases lookupSnocSome hp with hp | ⟨hpe, hme⟩
    · exact .inl ⟨hp, hsm, hk⟩
    · exact .inr ⟨hpe, hme⟩
  -- the release message publishes every earlier own message of `c`
  have hpub : mnew.wmAk = .WCrel →
      ∀ p, p < log.length → wpublished (log ++ [mnew]) (some c.val) p := by
    intro hk p hp
    exact ⟨log.length, mnew, by omega, list_lookup_middle rfl, htid, hk⟩
  cases hk : mnew.wmAk with
  | WCplain =>
    -- dirty by `c`
    intro p m hp
    rcases hback p m hp with hold | ⟨rfl, rfl⟩
    · rcases hdi p m hold with h | h | h
      · exact .inl h
      · exact .inr (.inl (wpublishedApp log [mnew] _ p h))
      · exact .inr (.inr h)
    · exact .inr (.inr htid)
  | WCrel =>
    -- clean — the new message publishes `c`'s whole backlog
    intro p m hp
    rcases hback p m hp with hold | ⟨rfl, rfl⟩
    · rcases hdi p m hold with h | h | h
      · exact .inl h
      · exact .inr (wpublishedApp log [mnew] _ p h)
      · right
        rw [h]
        exact hpub hk p (lookup_lt_Some hold.1)
    · obtain ⟨_, _, hc⟩ := hp
      rw [hk] at hc
      cases hc
  | WCexcl =>
    -- the state is unchanged, and the new message is not plain
    show wcdsOk (log ++ [mnew]) a s
    rcases hs with rfl | rfl
    · intro p m hp
      rcases hback p m hp with hold | ⟨rfl, rfl⟩
      · rcases hok p m hold with h | h
        · exact .inl h
        · exact .inr (wpublishedApp log [mnew] _ p h)
      · obtain ⟨_, _, hc⟩ := hp
        rw [hk] at hc
        cases hc
    · intro p m hp
      rcases hback p m hp with hold | ⟨rfl, rfl⟩
      · rcases hok p m hold with h | h | h
        · exact .inl h
        · exact .inr (.inl (wpublishedApp log [mnew] _ p h))
        · exact .inr (.inr h)
      · obtain ⟨_, _, hc⟩ := hp
        rw [hk] at hc
        cases hc

/-- THE NON-PLAIN STORE: a message that is not an owned store adds no obligation to a C/D/S state.
IT IS FALSE AT `WLock` (an `amoswap` swapping in 5 is non-plain and yet breaks the value protocol):
hence the `isWlock` premise.  TRUE at `WProt` (`wprotAt` speaks of plain messages only). -/
theorem wcdsOkStoreNonplain (log : List Wmsg) (mnew : Wmsg) (a : Int) (s : Wcds) :
    mnew.wmAk ≠ .WCplain → isWlock s = false →
    wcdsOk log a s → wcdsOk (log ++ [mnew]) a s := by
  intro hk hnl hok
  have hback : ∀ p m, wplainAt (log ++ [mnew]) a p m → wplainAt log a p m := by
    rintro p m ⟨hp, hs, hkm⟩
    rcases lookupSnocSome hp with hp | ⟨_, rfl⟩
    · exact ⟨hp, hs, hkm⟩
    · exact (hk hkm).elim
  have hcln : wcdsClean log a → wcdsClean (log ++ [mnew]) a := by
    intro hc p m hp
    rcases hc p m (hback p m hp) with h | h
    · exact .inl h
    · exact .inr (wpublishedApp log [mnew] _ p h)
  have hdrt : ∀ c, wcdsDirty log a c → wcdsDirty (log ++ [mnew]) a c := by
    intro c hd p m hp
    rcases hd p m (hback p m hp) with h | h | h
    · exact .inl h
    · exact .inr (.inl (wpublishedApp log [mnew] _ p h))
    · exact .inr (.inr h)
  cases s with
  | WClean => exact hcln hok
  | WDirty c => exact hdrt c hok
  | WSync => exact fun p m hp => hok p m (hback p m hp)
  | WLock base n0 h => simp [isWlock] at hnl
  | WProt γ base n0 r0 d =>
    obtain ⟨hob, hle, hpr⟩ := hok
    refine ⟨?_, hle, ?_⟩
    · cases d with
      | none => exact hcln hob
      | some c => exact hdrt c hob
    · intro p m hp hr0 hs hkm
      rcases lookupSnocSome hp with hp | ⟨_, rfl⟩
      · rw [wlpHolderApp log [mnew] base n0 p (by have := lookup_lt_Some hp; omega)]
        exact hpr p m hp hr0 hs hkm
      · exact (hk hkm).elim

theorem wcdsOkStoreClean (log : List Wmsg) (mnew : Wmsg) (a : Int) :
    mnew.wmAk ≠ .WCplain → wcdsClean log a → wcdsClean (log ++ [mnew]) a :=
  fun hk => wcdsOkStoreNonplain log mnew a WClean hk rfl

theorem wcdsOkStoreSync (log : List Wmsg) (mnew : Wmsg) (a : Int) :
    mnew.wmAk ≠ .WCplain → wcdsSync log a → wcdsSync (log ++ [mnew]) a :=
  fun hk => wcdsOkStoreNonplain log mnew a WSync hk rfl

/-- A whole-word message writes EVERY byte of the word. -/
theorem wlockShapedWrites (m : Wmsg) (a base : Int) :
    m.wmPa = base → wlockShaped m → (base ≤ a ∧ a < base + 4) → (msgByte m a).isSome := by
  rintro hpa ⟨hlen, _⟩ hrng
  unfold msgByte
  rw [if_pos (by omega)]
  apply lookup_lt_is_Some_2
  rw [hlen]
  omega

/-- THE PROTOCOL STORE — the `WLock` write rule, covering BOTH the acquire's exclusive write and
the release's zero store: a whole-word, acquire- or release-shaped message keeps the state,
MOVING the holder by `altStep`. -/
theorem wcdsOkStoreLock (log : List Wmsg) (mnew : Wmsg) (a base : Int) (n0 : Nat)
    (h h' : Option Nat) :
    mnew.wmPa = base → wlockShaped mnew → altStep h mnew = some h' →
    wcdsOk log a (WLock base n0 h) →
    wcdsOk (log ++ [mnew]) a (WLock base n0 h') := by
  rintro hpa hsh hst ⟨hcl, ⟨hrng, hlp⟩, halt⟩
  have hk : mnew.wmAk ≠ .WCplain := hsh.2.1
  refine ⟨wcdsOkStoreClean log mnew a hk hcl, ⟨hrng, ?_⟩,
    wlpAltStore log mnew a n0 h h' halt (wlockShapedWrites mnew a base hpa hsh hrng) hst⟩
  intro p m hp hn0 hs
  rcases lookupSnocSome hp with hp | ⟨_, rfl⟩
  · exact hlp p m hp hn0 hs
  · exact ⟨hpa, hsh⟩

/-- THE SUCCESSFUL ACQUIRE: an exclusive nonzero write on a FREE word installs its author. -/
theorem wcdsOkStoreLockAcq (log : List Wmsg) (mnew : Wmsg) (a base : Int) (n0 t : Nat) :
    mnew.wmPa = base → wlockShaped mnew →
    mnew.wmData ≠ wlockZero4 → mnew.wmAk = .WCexcl → mnew.wmTid = some t →
    wcdsOk log a (WLock base n0 none) →
    wcdsOk (log ++ [mnew]) a (WLock base n0 (some t)) := by
  intro hpa hsh hd hk ht
  exact wcdsOkStoreLock log mnew a base n0 none (some t) hpa hsh (altStepAcq mnew t hd hk ht)

/-- THE FAILED SWAP: the same message on a HELD word leaves the holder alone. -/
theorem wcdsOkStoreLockFail (log : List Wmsg) (mnew : Wmsg) (a base : Int) (n0 t : Nat) :
    mnew.wmPa = base → wlockShaped mnew →
    mnew.wmData ≠ wlockZero4 → mnew.wmAk = .WCexcl →
    wcdsOk log a (WLock base n0 (some t)) →
    wcdsOk (log ++ [mnew]) a (WLock base n0 (some t)) := by
  intro hpa hsh hd hk
  exact wcdsOkStoreLock log mnew a base n0 (some t) (some t) hpa hsh (altStepFail mnew t hd hk)

/-- THE RELEASE: a zero write frees the word — and ONLY THE HOLDER MAY DO IT. -/
theorem wcdsOkStoreLockRel (log : List Wmsg) (mnew : Wmsg) (a base : Int) (n0 t : Nat) :
    mnew.wmPa = base → wlockShaped mnew →
    mnew.wmData = wlockZero4 → mnew.wmTid = some t →
    wcdsOk log a (WLock base n0 (some t)) →
    wcdsOk (log ++ [mnew]) a (WLock base n0 none) := by
  intro hpa hsh hd ht
  exact wcdsOkStoreLock log mnew a base n0 (some t) none hpa hsh (altStepRel mnew t hd ht)

/-- THE REGISTRATION, purely.  At the log's own length the suffix obligation is VACUOUS, and the
fold starts FREE. -/
theorem wcdsOkRegister (log : List Wmsg) (a base : Int) :
    (base ≤ a ∧ a < base + 4) → wcdsClean log a →
    wcdsOk log a (WLock base log.length none) := by
  intro hrng hcl
  refine ⟨hcl, ⟨hrng, ?_⟩, wlpAltRegister log a⟩
  intro p m hp hn0 _
  have := lookup_lt_Some hp
  omega

/-! ### THE PROTECTED-BYTE RULES (T2-0′ / F3″): REGISTER, STORE, FLIP, DEREGISTER. -/

/-- THE REGISTRATION: at the log's own length the protection clause is VACUOUS. -/
theorem wcdsOkRegisterProt (log : List Wmsg) (a base : Int) (n0 : Nat) :
    n0 ≤ log.length → wcdsClean log a → wcdsProt log a base n0 log.length none := by
  intro hn0 hcl
  refine ⟨hcl, hn0, ?_⟩
  intro p m hp hr0 _ _
  have := lookup_lt_Some hp
  omega

/-- THE PROTECTED STORE — the rule the whole export exists to enforce: an owned message may reach a
footprint byte only if its author is the lock's HOLDER at the log's top. -/
theorem wcdsOkStoreProt (log : List Wmsg) (mnew : Wmsg) (a base : Int) (n0 r0 : Nat)
    (d : Option CPU) (c : CPU) :
    mnew.wmAk = .WCplain → mnew.wmTid = some c.val →
    (d = none ∨ d = some c) →
    wlpHolderAt log base n0 log.length = some (some c.val) →
    wcdsProt log a base n0 r0 d →
    wcdsProt (log ++ [mnew]) a base n0 r0 (some c) := by
  rintro hk htid hd hhold ⟨hob, hle, hpr⟩
  refine ⟨?_, hle, ?_⟩
  · -- φ: the owned-store step of the three-state protocol, at `d`'s state
    have hs : wcdsOk log a (wcdsOb d) ∧ (wcdsOb d = WClean ∨ wcdsOb d = WDirty c) := by
      rcases hd with rfl | rfl
      · exact ⟨hob, .inl rfl⟩
      · exact ⟨hob, .inr rfl⟩
    have hstep := wcdsOkStoreOwn log mnew a c _ htid hs.2 hs.1
    rw [hk] at hstep
    exact hstep
  · intro p m hp hr0 hsm hkm
    rcases lookupSnocSome hp with hp | ⟨hpe, hme⟩
    · rw [wlpHolderApp log [mnew] base n0 p (by have := lookup_lt_Some hp; omega)]
      exact hpr p m hp hr0 hsm hkm
    · rw [hme, hpe, wlpHolderApp log [mnew] base n0 log.length (Nat.le_refl _), hhold, htid]

/-- THE DEREGISTRATION: the byte leaves the footprint carrying exactly the φ obligation its dirty
author names. -/
theorem wcdsOkDeregisterProt (log : List Wmsg) (a base : Int) (n0 r0 : Nat) (d : Option CPU) :
    wcdsProt log a base n0 r0 d → wcdsOk log a (wcdsOb d) := by
  rintro ⟨hob, _⟩
  cases d <;> exact hob

/-! ### THE KILL LEMMA (route-b §4d.3′, "what the kill consumes") -/

/-- The fold's own inversion: a held word was acquired, and has not been released since. -/
theorem wlpHolderAcqExists (log : List Wmsg) (a : Int) (n0 p j : Nat) :
    wlpHolderAt log a n0 p = some (some j) →
    ∃ q mq, (n0 ≤ q ∧ q < p) ∧ log[q]? = some mq ∧
      (msgByte mq a).isSome ∧ mq.wmData ≠ wlockZero4 ∧
      mq.wmTid = some j ∧ wlpHolderAt log a n0 q = some none ∧
      (∀ r mr, (q < r ∧ r < p) → log[r]? = some mr →
         (msgByte mr a).isSome → mr.wmData ≠ wlockZero4) := by
  induction p with
  | zero =>
    intro hp
    rw [wlpHolderSmall log a n0 0 (Nat.zero_le _)] at hp
    simp at hp
  | succ p ih =>
    intro hp
    by_cases hle : p + 1 ≤ n0
    · rw [wlpHolderSmall log a n0 (p + 1) hle] at hp; simp at hp
    cases hm : log[p]? with
    | none =>
      -- past the end of the log: the fold has not moved
      have hge := lookup_ge_None_1 hm
      rw [wlpHolderBig log a n0 (p + 1) (by omega), ← wlpHolderBig log a n0 p (by omega)] at hp
      obtain ⟨q, mq, hq, hlk, hw, hnz, ht, hfree, hno⟩ := ih hp
      refine ⟨q, mq, ⟨hq.1, by omega⟩, hlk, hw, hnz, ht, hfree, ?_⟩
      intro r mr hr hlr hwr
      by_cases hlt : r < p
      · exact hno r mr ⟨hr.1, hlt⟩ hlr hwr
      · have := lookup_lt_Some hlr; omega
    | some m =>
      have hn0p : n0 ≤ p := by omega
      rw [wlpHolderStep log a n0 p m hn0p hm] at hp
      cases hh : wlpHolderAt log a n0 p with
      | none => rw [hh] at hp; simp at hp
      | some h =>
        rw [hh] at hp
        dsimp only at hp
        cases hwm : mwrites a m with
        | false =>
          -- the message does not touch the word
          rw [hwm] at hp
          simp only [Bool.false_eq_true, ↓reduceIte] at hp
          have hp' : wlpHolderAt log a n0 p = some (some j) := by rw [hh, hp]
          obtain ⟨q, mq, hq, hlk, hw, hnz, ht, hfree, hno⟩ := ih hp'
          refine ⟨q, mq, ⟨hq.1, by omega⟩, hlk, hw, hnz, ht, hfree, ?_⟩
          intro r mr hr hlr hwr
          by_cases hlt : r < p
          · exact hno r mr ⟨hr.1, hlt⟩ hlr hwr
          · have hre : r = p := by omega
            subst hre
            rw [hm] at hlr
            cases hlr
            rw [(mwritesFalse a m).1 hwm] at hwr
            simp at hwr
        | true =>
          rw [hwm] at hp
          simp only [↓reduceIte] at hp
          have hwm' := (mwritesTrue a m).1 hwm
          by_cases hz : m.wmData = wlockZero4
          · exact absurd (altStepZero h m (some j) hz hp).1 (by simp)
          obtain ⟨_, _, hfromfree, hfromheld⟩ := altStepNonzero h m (some j) hz hp
          cases h with
          | some t =>
            -- a FAILED swap: the holder was already `j`, so the acquire is earlier
            have htj : some j = some t := hfromheld (by simp)
            rw [← htj] at hh
            obtain ⟨q, mq, hq, hlk, hw, hnzq, ht, hfree, hno⟩ := ih hh
            refine ⟨q, mq, ⟨hq.1, by omega⟩, hlk, hw, hnzq, ht, hfree, ?_⟩
            intro r mr hr hlr hwr
            by_cases hlt : r < p
            · exact hno r mr ⟨hr.1, hlt⟩ hlr hwr
            · have hre : r = p := by omega
              subst hre
              rw [hm] at hlr
              cases hlr
              exact hz
          | none =>
            -- a SUCCESSFUL acquire: `p` is the position we were looking for
            refine ⟨p, m, ⟨hn0p, by omega⟩, hm, hwm', hz, (hfromfree rfl).symm, hh, ?_⟩
            intro r mr hr
            omega

/-- THE EXPORTED CONSUMPTION.  `(P)` of route-b §4d.1 F6: the plain writer of a protected byte
holds the lock, its acquire is identified, and its critical section is still open at the write. -/
theorem wprotWriterHolds (log : List Wmsg) (a base : Int) (n0 r0 p : Nat) (m : Wmsg) (j : Nat) :
    wprotAt log a base n0 r0 →
    log[p]? = some m → r0 ≤ p → (msgByte m a).isSome →
    m.wmAk = .WCplain → m.wmTid = some j →
    wlpHolderAt log base n0 p = some (some j) := by
  rintro ⟨_, hpr⟩ hp hr0 hs hk ht
  rw [hpr p m hp hr0 hs hk, ht]

theorem wprotWriterCs (log : List Wmsg) (a base : Int) (n0 r0 p : Nat) (m : Wmsg) (j : Nat) :
    wprotAt log a base n0 r0 →
    log[p]? = some m → r0 ≤ p → (msgByte m a).isSome →
    m.wmAk = .WCplain → m.wmTid = some j →
    ∃ q mq, (n0 ≤ q ∧ q < p) ∧ log[q]? = some mq ∧
      (msgByte mq base).isSome ∧ mq.wmData ≠ wlockZero4 ∧
      mq.wmTid = some j ∧ wlpHolderAt log base n0 q = some none ∧
      (∀ r mr, (q < r ∧ r < p) → log[r]? = some mr →
         (msgByte mr base).isSome → mr.wmData ≠ wlockZero4) := by
  intro hpr hp hr0 hs hk ht
  exact wlpHolderAcqExists log base n0 p j (wprotWriterHolds log a base n0 r0 p m j hpr hp hr0 hs hk ht)

/-- THE FLIP, purely.  A byte that is dirty by `c` is CLEAN as soon as `c`'s release store is the
log's LAST message. -/
theorem wcdsDirtyFlip (log : List Wmsg) (a : Int) (c : CPU) (q : Nat) (mq : Wmsg) :
    log[q]? = some mq → mq.wmTid = some c.val → mq.wmAk = .WCrel →
    log.length ≤ q + 1 →
    wcdsDirty log a c → wcdsClean log a := by
  intro hq htid hk hlen hdi p m hp
  rcases hdi p m hp with h | h | hc
  · exact .inl h
  · exact .inr h
  · right
    rw [hc]
    have := lookup_lt_Some hp.1
    exact ⟨q, mq, by omega, hq, htid, hk⟩

/-- THE D→C FLIP, `wcdsDirtyFlip`'s twin, for the whole footprint. -/
theorem wcdsProtFlip (log : List Wmsg) (a base : Int) (n0 r0 : Nat) (c : CPU) (q : Nat)
    (mq : Wmsg) :
    log[q]? = some mq → mq.wmTid = some c.val → mq.wmAk = .WCrel →
    log.length ≤ q + 1 →
    wcdsProt log a base n0 r0 (some c) → wcdsProt log a base n0 r0 none := by
  rintro hq htid hk hlen ⟨hob, hpr⟩
  exact ⟨wcdsDirtyFlip log a c q mq hq htid hk hlen hob, hpr⟩

/-- THE LAZY UPGRADE, purely (φ-upgrade §1.5): a FLOOR — hart `c` published every position below
`n`, and the byte's whole write history is at or below its own latest-write timestamp `t` — so
`t ≤ n` flips it. -/
theorem wcdsDirtyFlipPub (img : Image) (log : List Wmsg) (a : Int) (c : CPU) (t n : Nat)
    (v : BitVec 8) :
    latestVal img log a t v → t ≤ n →
    wpubUpto log (some c.val) n →
    wcdsDirty log a c → wcdsClean log a := by
  intro hlat htn hpub hdi p m hp
  rcases hdi p m hp with h | h | hc
  · exact .inl h
  · exact .inr h
  · right
    rw [hc]
    refine wpubUptoPublished log _ n p hpub ?_
    have := latestValPlainLe img log a t v p m hlat hp.1 hp.2.1
    omega

/-- The map-level tie, the twin of `wlatAgree`. -/
def wcdsAgree (log : List Wmsg) (m : GMapF Int Wcds) : Prop :=
  ∀ a s, get? m a = some s → wcdsOk log a s

theorem wcdsAgreeApp (log ms : List Wmsg) (m : GMapF Int Wcds) :
    (∀ a, (get? m a).isSome → ∀ mg, mg ∈ ms → msgByte mg a = none) →
    wcdsAgree log m → wcdsAgree (log ++ ms) m := by
  intro hno hag a s ha
  exact wcdsOkApp log ms a s (fun mg hmg => hno a (by rw [ha]; rfl) mg hmg) (hag a s ha)

theorem wcdsAgreeInsert (log : List Wmsg) (m : GMapF Int Wcds) (a : Int) (s : Wcds) :
    wcdsAgree log m → wcdsOk log a s → wcdsAgree log (insert m a s) := by
  intro hag hok a' s' ha'
  by_cases h : a' = a
  · subst h
    rw [lookupInsert] at ha'
    cases ha'
    exact hok
  · rw [lookupInsertNe (Ne.symm h)] at ha'
    exact hag a' s' ha'

/-- The whole map survives a non-plain store PROVIDED the message's own window carries no `WLock`
byte (T2-0).  `zs` is the window. -/
theorem wcdsAgreeNonplainWin (log : List Wmsg) (mnew : Wmsg) (mc : GMapF Int Wcds) (zs : List Int) :
    mnew.wmAk ≠ .WCplain →
    (∀ z, msgByte mnew z ≠ none → z ∈ zs) →
    (∀ z s, z ∈ zs → get? mc z = some s → isWlock s = false) →
    wcdsAgree log mc → wcdsAgree (log ++ [mnew]) mc := by
  intro hk hcov hnl hag a s ha
  by_cases hnone : msgByte mnew a = none
  · refine wcdsOkApp log [mnew] a s ?_ (hag a s ha)
    intro m0 hm0
    rw [List.mem_singleton] at hm0
    subst hm0
    exact hnone
  · exact wcdsOkStoreNonplain log mnew a s hk (hnl a s (hcov a hnone) ha) (hag a s ha)

/-- The SINGLE-BYTE instance, the shape `WeakVProp`'s one-byte store rule has. -/
theorem wcdsAgreeNonplain1 (log : List Wmsg) (mnew : Wmsg) (mc : GMapF Int Wcds) (a : Int)
    (s0 : Wcds) :
    mnew.wmAk ≠ .WCplain → isWlock s0 = false →
    (∀ a', a' ≠ a → msgByte mnew a' = none) →
    get? mc a = some s0 →
    wcdsAgree log mc → wcdsAgree (log ++ [mnew]) mc := by
  intro hk hnl hother ha hag
  refine wcdsAgreeNonplainWin log mnew mc [a] hk ?_ ?_ hag
  · intro z hz
    by_cases hza : z = a
    · subst hza; exact List.mem_singleton.2 rfl
    · exact (hz (hother z hza)).elim
  · intro z s hz hs
    rw [List.mem_singleton] at hz
    subst hz
    rw [ha] at hs
    cases hs
    exact hnl

/-- ... and its PROTOCOL twin: the whole map survives an acquire- or release-shaped store to a
registered lock word. -/
theorem wcdsAgreeStoreLock (log : List Wmsg) (mnew : Wmsg) (mc mc' : GMapF Int Wcds)
    (zs : List Int) (base : Int) (n0 : Nat) (h h' : Option Nat) :
    mnew.wmPa = base → wlockShaped mnew → altStep h mnew = some h' →
    (∀ z, msgByte mnew z ≠ none → z ∈ zs) →
    (∀ z, z ∈ zs → get? mc z = some (WLock base n0 h)) →
    (∀ z, z ∈ zs → get? mc' z = some (WLock base n0 h')) →
    (∀ z, z ∉ zs → get? mc' z = get? mc z) →
    wcdsAgree log mc → wcdsAgree (log ++ [mnew]) mc' := by
  intro hpa hsh hst hcov hin hin' hout hag a s ha
  by_cases hz : a ∈ zs
  · rw [hin' a hz] at ha
    cases ha
    exact wcdsOkStoreLock log mnew a base n0 h h' hpa hsh hst (hag a _ (hin a hz))
  · rw [hout a hz] at ha
    refine wcdsOkApp log [mnew] a s ?_ (hag a s ha)
    intro m0 hm0
    rw [List.mem_singleton] at hm0
    subst hm0
    apply Classical.byContradiction
    intro hb
    exact hz (hcov a hb)

/-- The initial state element list: every byte of the era-initial image, CLEAN (Lean-only name,
deviation 4). -/
def wcdsInitList (img : GMapF PAddr (BitVec 8)) : List (Int × Wcds) :=
  (toList img).map (fun ab : PAddr × BitVec 8 => (paZ ab.1, WClean))

/-- The initial state map: every byte of the era-initial image is CLEAN (deviation 4). -/
def wcdsInit (img : GMapF PAddr (BitVec 8)) : GMapF Int Wcds := ofList (wcdsInitList img)

theorem wcdsInitAgree (img : GMapF PAddr (BitVec 8)) : wcdsAgree [] (wcdsInit img) := by
  intro a s ha
  have hin := LawfulFiniteMap.mem_of_mem_ofList (M := GMapF Int) ha
  obtain ⟨_, _, heq⟩ := List.mem_map.mp hin
  simp only [Prod.mk.injEq] at heq
  obtain ⟨_, rfl⟩ := heq
  rintro p m ⟨hp, _⟩
  simp at hp

theorem wcdsInitNodup (img : GMapF PAddr (BitVec 8)) : NoDupKeys (wcdsInitList img) := by
  unfold NoDupKeys wcdsInitList
  rw [List.map_map]
  have : (Prod.fst ∘ fun ab : PAddr × BitVec 8 => (paZ ab.1, WClean)) =
      paZ ∘ Prod.fst := rfl
  rw [this, ← List.map_map]
  have h0 : NoDupKeys (toList img) := LawfulFiniteMap.toList_noDupKeys (M := GMapF PAddr) (m := img)
  exact List.nodup_map_of_injective paZInj h0

section BigOps
open Iris.BI

theorem bigSepM_wcdsInit {PROP : Type _} [Iris.BI PROP] (Φ : Int → Wcds → PROP)
    (img : GMapF PAddr (BitVec 8)) :
    ([∗map] z ↦ s ∈ wcdsInit img, Φ z s) ⊣⊢ ([∗map] a ↦ _b ∈ img, Φ (paZ a) WClean) := by
  refine (BigSepM.bigSepM_ofList (wcdsInitNodup img)).trans ?_
  unfold wcdsInitList
  rw [BigSepL.bigSepL_map]
  exact .rfl

end BigOps

/-! ## 3. The violation-freedom predicate φ

Three spellings of the same thing: `nvByte log c' a n` — ONE hart's floor at ONE byte; `nvHart` —
one hart, all bytes, at its own `coh`; `noViolation` — the GLOBAL statement, spelled with the
message quantified first and the foreign hart last, matching `WeakRobust.violation`. -/

def nvByte (log : List Wmsg) (c' : CPU) (a : Int) (n : Nat) : Prop :=
  ∀ (p : Nat) (m : Wmsg) (c : CPU),
    log[p]? = some m → m.wmTid = some c.val →
    m.wmAk = .WCplain → ¬ wpublished log m.wmTid p →
    (msgByte m a).isSome → c' ≠ c → n < p + 1

def nvHart (log : List Wmsg) (c' : CPU) (ws : Wstate) : Prop :=
  ∀ a : Int, nvByte log c' a (coh ws a)

def noViolation (log : List Wmsg) (wsf : CPU → Wstate) : Prop :=
  ∀ (p : Nat) (m : Wmsg) (c : CPU) (a : Int),
    log[p]? = some m → m.wmTid = some c.val →
    m.wmAk = .WCplain → ¬ wpublished log m.wmTid p →
    (msgByte m a).isSome →
    ∀ c' : CPU, c' ≠ c → coh (wsf c') a < p + 1

/-- The global statement IS the per-hart one at every hart. -/
theorem noViolationHart (log : List Wmsg) (wsf : CPU → Wstate) (c' : CPU) :
    noViolation log wsf → nvHart log c' (wsf c') :=
  fun h a p m c hp ht hk hnp hs hne => h p m c a hp ht hk hnp hs c' hne

theorem noViolationIntro (log : List Wmsg) (wsf : CPU → Wstate) :
    (∀ c' : CPU, nvHart log c' (wsf c')) → noViolation log wsf :=
  fun h p m c a hp ht hk hnp hs c' hne => h c' a p m c hp ht hk hnp hs hne

/-- The empty log violates nothing — the conjunct's boot case. -/
theorem noViolationNil (wsf : CPU → Wstate) : noViolation [] wsf := by
  intro p m c a hp
  simp at hp

theorem nvHartNil (c' : CPU) (ws : Wstate) : nvHart [] c' ws := by
  intro a p m c hp
  simp at hp

/-- Lowering a floor keeps it safe. -/
theorem nvByteMono (log : List Wmsg) (c' : CPU) (a : Int) (n n' : Nat) :
    nvByte log c' a n → n' ≤ n → nvByte log c' a n' := by
  intro h hle p m c hp ht hk hnp hs hne
  have := h p m c hp ht hk hnp hs hne
  omega

/-! ## 4. The induction algebra -/

/-- APPENDS: the obligation only ever gets WEAKER along an append; the new messages are above the
floor by `ws_bounded`. -/
theorem nvByteApp (log ms : List Wmsg) (c' : CPU) (a : Int) (n : Nat) :
    nvByte log c' a n → n ≤ log.length → nvByte (log ++ ms) c' a n := by
  intro h hn p m c hp ht hk hnp hs hne
  rcases lookup_app_Some.1 hp with hp | ⟨hge, _⟩
  · exact h p m c hp ht hk (fun hpub => hnp (wpublishedApp log ms _ p hpub)) hs hne
  · omega

theorem nvHartApp (log ms : List Wmsg) (c' : CPU) (ws : Wstate) :
    nvHart log c' ws → wsBounded ws log.length → nvHart (log ++ ms) c' ws := by
  intro h hb a
  exact nvByteApp log ms c' a _ (h a) (hb.2.2.2.2.2.2.1 a)

/-- ... and the STEPPING hart's own append: every message a hart appends carries ITS OWN tid, so
the new obligations are vacuous. -/
theorem nvByteAppOwn (log ms : List Wmsg) (c : CPU) (a : Int) (n : Nat) :
    nvByte log c a n →
    (∀ m, m ∈ ms → m.wmTid = some c.val) →
    nvByte (log ++ ms) c a n := by
  intro h hown p m c0 hp ht hk hnp hs hne
  rcases lookup_app_Some.1 hp with hp | ⟨_, hp⟩
  · exact h p m c0 hp ht hk (fun hpub => hnp (wpublishedApp log ms _ p hpub)) hs hne
  · exfalso
    apply hne
    have := hown m (elem_of_list_lookup_2 hp)
    rw [this] at ht
    exact Fin.ext (Option.some.inj ht)

theorem nvHartAppOwn (log ms : List Wmsg) (c : CPU) (ws : Wstate) :
    nvHart log c ws →
    (∀ m, m ∈ ms → m.wmTid = some c.val) →
    nvHart (log ++ ms) c ws :=
  fun h hown a => nvByteAppOwn log ms c a _ (h a) hown

/-- THE FLOOR MOVE: a hart's `coh` only rises, and only at the bytes its step touched. -/
theorem nvHartCohStep (log : List Wmsg) (c : CPU) (ws ws' : Wstate) :
    nvHart log c ws →
    (∀ a : Int, coh ws a < coh ws' a → nvByte log c a (coh ws' a)) →
    nvHart log c ws' := by
  intro h hmv a
  by_cases hlt : coh ws a < coh ws' a
  · exact hmv a hlt
  · exact nvByteMono log c a (coh ws a) _ (h a) (by omega)

/-- THE REASSEMBLY: ONE hart stepped, every other hart's cell is untouched and its floors are
below the OLD log's top. -/
theorem noViolationStep (log ms : List Wmsg) (wsf wsf' : CPU → Wstate) (c : CPU) :
    noViolation log wsf →
    (∀ c0 : CPU, wsBounded (wsf c0) log.length) →
    (∀ m, m ∈ ms → m.wmTid = some c.val) →
    (∀ c0 : CPU, c0 ≠ c → wsf' c0 = wsf c0) →
    nvHart (log ++ ms) c (wsf' c) →
    noViolation (log ++ ms) wsf' := by
  intro hnv hbnd _ hfr hc
  refine noViolationIntro _ _ fun c0 => ?_
  by_cases hce : c0 = c
  · subst hce; exact hc
  · rw [hfr c0 hce]
    exact nvHartApp log ms c0 (wsf c0) (noViolationHart log wsf c0 hnv) (hbnd c0)

/-- The DEVICE/DMA arm: a disk append adds no obligation at all and no hart's floor moves. -/
theorem noViolationDma (log ms : List Wmsg) (wsf : CPU → Wstate) :
    noViolation log wsf →
    (∀ c0 : CPU, wsBounded (wsf c0) log.length) →
    noViolation (log ++ ms) wsf := by
  intro hnv hbnd
  exact noViolationIntro _ _ fun c0 =>
    nvHartApp log ms c0 (wsf c0) (noViolationHart log wsf c0 hnv) (hbnd c0)

/-! ## 5. The discharge arms, off the C/D/S invariants

At a byte whose state a load's own fragment pins, the obligation is VACUOUS: CLEAN (every
`WCplain` writer published), DIRTY BY ME (the unpublished writers are all mine), SYNC (no
`WCplain` writer at all). -/

theorem nvByteClean (log : List Wmsg) (c' : CPU) (a : Int) (n : Nat) :
    wcdsClean log a → nvByte log c' a n := by
  intro hcl p m c hp ht hk hnp hs _
  rcases hcl p m ⟨hp, hs, hk⟩ with hn | hpub
  · exact (hn (by rw [ht]; exact tidIsHartCpuIntro c)).elim
  · exact (hnp hpub).elim

theorem nvByteDirty (log : List Wmsg) (c : CPU) (a : Int) (n : Nat) :
    wcdsDirty log a c → nvByte log c a n := by
  intro hdi p m c0 hp ht hk hnp hs hne
  rcases hdi p m ⟨hp, hs, hk⟩ with hn | hpub | hc
  · exact (hn (by rw [ht]; exact tidIsHartCpuIntro c0)).elim
  · exact (hnp hpub).elim
  · exfalso
    apply hne
    rw [ht] at hc
    exact (Fin.ext (Option.some.inj hc)).symm

theorem nvByteSync (log : List Wmsg) (c' : CPU) (a : Int) (n : Nat) :
    wcdsSync log a → nvByte log c' a n :=
  fun hsy p m _ hp _ hk _ hs _ => (hsy p m ⟨hp, hs, hk⟩).elim

/-- THE FOURTH ARM (T2-0): a registered lock byte pays φ's obligation exactly as a clean one. -/
theorem nvByteLock (log : List Wmsg) (c' : CPU) (a : Int) (n : Nat) (base : Int) (n0 : Nat)
    (h : Option Nat) : wcdsLock log a base n0 h → nvByte log c' a n :=
  fun h => nvByteClean log c' a n h.1

/-- φ'S FIFTH ARM: a protected byte pays the obligation exactly as the C/D state its dirty author
names does. -/
theorem nvByteProt (log : List Wmsg) (c : CPU) (a : Int) (n : Nat) (base : Int) (n0 r0 : Nat)
    (d : Option CPU) :
    wcdsProt log a base n0 r0 d → (d = none ∨ d = some c) → nvByte log c a n := by
  rintro ⟨hob, _⟩ hd
  rcases hd with rfl | rfl
  · exact nvByteClean log c a n hob
  · exact nvByteDirty log c a n hob

/-- The uniform reading: any state a hart may legitimately PRESENT for a byte discharges the
obligation at that byte. -/
theorem nvByteOk (log : List Wmsg) (c : CPU) (a : Int) (n : Nat) (s : Wcds) :
    wcdsOk log a s → (s = WClean ∨ s = WDirty c ∨ s = WSync) → nvByte log c a n := by
  intro hok hs
  rcases hs with rfl | rfl | rfl
  · exact nvByteClean log c a n hok
  · exact nvByteDirty log c a n hok
  · exact nvByteSync log c a n hok

/-- THE FETCH ARM: a byte NO message of the log ever writes carries no obligation at all. -/
theorem nvByteUnwritten (log : List Wmsg) (c : CPU) (a : Int) (n : Nat) :
    latestTs log a = 0 → nvByte log c a n := by
  intro hlt p m c0 hp _ _ _ hs _
  exfalso
  apply latestTsTop log a
  rw [hlt]
  have hlen := lookup_lt_Some hp
  exact ⟨p + 1, by omega, by omega, m, by rw [Nat.add_sub_cancel]; exact hp, hs⟩

/-- THE BYTE-LEVEL SUMMARY a resource-holder exports: byte `a` carries no foreign unpublished
`WCplain` message, for ANY hart at ANY floor.  PURE, so it survives the closing of the invariant
the fragment came from. -/
def nvFree (log : List Wmsg) (a : Int) : Prop :=
  ∀ (c : CPU) (n : Nat), nvByte log c a n

/-- ... and its HART-INDEXED form: weaker than `nvFree` exactly by the `WDirty` arm. -/
def nvOk (log : List Wmsg) (c : CPU) (a : Int) : Prop :=
  ∀ n : Nat, nvByte log c a n

theorem nvOkOfFree (log : List Wmsg) (c : CPU) (a : Int) : nvFree log a → nvOk log c a :=
  fun h n => h c n

theorem nvOkClean (log : List Wmsg) (c : CPU) (a : Int) : wcdsClean log a → nvOk log c a :=
  fun h n => nvByteClean log c a n h

theorem nvOkDirty (log : List Wmsg) (c : CPU) (a : Int) : wcdsDirty log a c → nvOk log c a :=
  fun h n => nvByteDirty log c a n h

theorem nvOkSync (log : List Wmsg) (c : CPU) (a : Int) : wcdsSync log a → nvOk log c a :=
  fun h n => nvByteSync log c a n h

theorem nvOkUnwritten (log : List Wmsg) (c : CPU) (a : Int) : latestTs log a = 0 → nvOk log c a :=
  fun h n => nvByteUnwritten log c a n h

theorem nvByteOfOk (log : List Wmsg) (c : CPU) (a : Int) (n : Nat) :
    nvOk log c a → nvByte log c a n :=
  fun h => h n

theorem nvFreeClean (log : List Wmsg) (a : Int) : wcdsClean log a → nvFree log a :=
  fun h c n => nvByteClean log c a n h

theorem nvFreeSync (log : List Wmsg) (a : Int) : wcdsSync log a → nvFree log a :=
  fun h c n => nvByteSync log c a n h

theorem nvFreeUnwritten (log : List Wmsg) (a : Int) : latestTs log a = 0 → nvFree log a :=
  fun h c n => nvByteUnwritten log c a n h

theorem nvOkLock (log : List Wmsg) (c : CPU) (a base : Int) (n0 : Nat) (h : Option Nat) :
    wcdsLock log a base n0 h → nvOk log c a :=
  fun h n => nvByteClean log c a n h.1

theorem nvFreeLock (log : List Wmsg) (a base : Int) (n0 : Nat) (h : Option Nat) :
    wcdsLock log a base n0 h → nvFree log a :=
  fun h c n => nvByteClean log c a n h.1

theorem nvFreeProt (log : List Wmsg) (a base : Int) (n0 r0 : Nat) :
    wcdsProt log a base n0 r0 none → nvFree log a :=
  fun h c n => nvByteClean log c a n h.1

theorem nvByteOfFree (log : List Wmsg) (c : CPU) (a : Int) (n : Nat) :
    nvFree log a → nvByte log c a n :=
  fun h => h c n

/-- THE φ PAYMENT OF THE LAZY-UPGRADE ARM (φ-upgrade §1.5): a byte still `WDirty c` whose whole
write history `c` has PUBLISHED carries no obligation to ANY hart at ANY floor. -/
theorem nvFreePublished (img : Image) (log : List Wmsg) (a : Int) (c : CPU) (t n : Nat)
    (v : BitVec 8) :
    latestVal img log a t v → t ≤ n →
    wpubUpto log (some c.val) n →
    wcdsDirty log a c → nvFree log a := by
  intro hlat htn hpub hdi
  exact nvFreeClean log a (wcdsDirtyFlipPub img log a c t n v hlat htn hpub hdi)

theorem nvBytePublished (img : Image) (log : List Wmsg) (c' : CPU) (a : Int) (m : Nat) (c : CPU)
    (t n : Nat) (v : BitVec 8) :
    latestVal img log a t v → t ≤ n →
    wpubUpto log (some c.val) n →
    wcdsDirty log a c → nvByte log c' a m := by
  intro hlat htn hpub hdi
  exact nvFreePublished img log a c t n v hlat htn hpub hdi c' m

theorem nvOkPublished (img : Image) (log : List Wmsg) (c' : CPU) (a : Int) (c : CPU) (t n : Nat)
    (v : BitVec 8) :
    latestVal img log a t v → t ≤ n →
    wpubUpto log (some c.val) n →
    wcdsDirty log a c → nvOk log c' a := by
  intro hlat htn hpub hdi
  exact nvOkOfFree log c' a (nvFreePublished img log a c t n v hlat htn hpub hdi)

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap
open Iris.Std.LawfulPartialMap MachCSL MachCSL.Stdpp
open Wcds

/-! ## 6. The classes -/

/-- THE READ-RECORD ALGEBRA (T2-0′ / F3″): a persistent RECORD "byte `a` was read, as a byte of
this lock's payload, at log position `p`", one monotone list of `(a, p)` pairs per registered
lock.  A SEPARATE class: the record ghost is allocated per lock, by the lock library. -/
class WprotG (GF : BundledGFunctors) where
  recG : MonoListG GF (Int × Nat)

attribute [reducible, instance] WprotG.recG

/-- The base layer's cameras: the log mono-list, the latest-write map, the C/D/S state map, the
per-hart weak-state cells, and the max-fun authority `WeakCtx`'s objective layer is built on. -/
class WeakGpreS (GF : BundledGFunctors) where
  logG : MonoListG GF Wmsg
  latG : GhostMapG GF Int (Nat × BitVec 8) (GMapF Int)
  cdsG : GhostMapG GF Int Wcds (GMapF Int)
  wsG : GhostVarG GF Wstate
  viewG : WeakViewG GF

attribute [reducible, instance] WeakGpreS.logG WeakGpreS.latG WeakGpreS.cdsG WeakGpreS.wsG
  WeakGpreS.viewG

/-- The base layer's ghost names: the log, the latest-write map, the C/D/S map (same keys), and
one weak-state cell PER HART (see the header's DEVIATION note).  (Rocq's deleted fifth field,
`weak_view_name`, is not reintroduced.) -/
class WeakGS (GF : BundledGFunctors) where
  [pre : WeakGpreS GF]
  logName : GName
  latName : GName
  cdsName : GName
  wsName : CPU → GName

attribute [reducible, instance] WeakGS.pre

/-! ## 7. THE EXECUTION CONTEXT'S NAME (φ-upgrade §1.6)

`WeakCtx`'s `CtxId` lives HERE because the OWNED POINTS-TO is indexed by it.  TWO ghost names:
`ctxVn` is `WeakCtx`'s view authority (an `Auth CohUR`), `ctxWn` the per-hart write watermark
of §3a″ (an `Auth CtxwrUR`). -/
structure CtxId where
  ctxVn : GName
  ctxWn : GName

/-! ## 8. The resources -/

section resources

variable {GF : BundledGFunctors} [WeakGS GF]

/-! ### 3a. the global write log (mono-list) -/

def wlogAuth (l : List Wmsg) : IProp GF :=
  MonoList.auth_own (WeakGS.logName (GF := GF)) (DFrac.own 1) l

def wlogLb (l : List Wmsg) : IProp GF :=
  MonoList.lb_own (WeakGS.logName (GF := GF)) l

instance wlogLb_persistent (l : List Wmsg) : Persistent (wlogLb (GF := GF) l) := by
  unfold wlogLb; infer_instance

instance wlogLb_timeless (l : List Wmsg) : Timeless (wlogLb (GF := GF) l) := by
  unfold wlogLb; infer_instance

theorem wlogSnapshot (l : List Wmsg) : wlogAuth (GF := GF) l ⊢ wlogAuth l ∗ wlogLb l := by
  unfold wlogAuth wlogLb
  iintro Ha
  ihave #Hlb := MonoList.lb_own_get _ _ _ $$ Ha
  iframe Ha Hlb

theorem wlogValid (l l' : List Wmsg) : wlogAuth (GF := GF) l ∗ wlogLb l' ⊢ ⌜l' <+: l⌝ := by
  unfold wlogAuth wlogLb
  iintro ⟨Ha, Hf⟩
  icases MonoList.auth_lb_own_valid _ _ _ _ $$ Ha Hf with %⟨_, h⟩
  ipureintro
  exact h

theorem wlogUpdate (l ms : List Wmsg) : wlogAuth (GF := GF) l ⊢ |==> wlogAuth (l ++ ms) := by
  unfold wlogAuth
  iintro Ha
  imod MonoList.auth_own_update_app _ ms $$ Ha with ⟨Ha, -⟩
  imodintro
  iexact Ha

/-! ### 3a′. THE PUBLICATION-FLOOR TOKEN (φ-upgrade §1.5)

`pubFloor c n` — "hart `c` has published everything at or below `n`", as a PERSISTENT resource,
spelled as a snapshot of a log prefix in which `c` has already released (publication is a LOG
predicate).  The HART-INDEX-KEYED spelling `pubFloorn` is the primitive one. -/

def pubFloorn (k n : Nat) : IProp GF :=
  iprop(∃ l : List Wmsg, wlogLb l ∗ ⌜wpubUpto l (some k) n⌝)

def pubFloor (c : CPU) (n : Nat) : IProp GF := pubFloorn (GF := GF) c.val n

instance pubFloorn_persistent (k n : Nat) : Persistent (pubFloorn (GF := GF) k n) := by
  unfold pubFloorn; infer_instance
instance pubFloorn_timeless (k n : Nat) : Timeless (pubFloorn (GF := GF) k n) := by
  unfold pubFloorn; infer_instance
instance pubFloor_persistent (c : CPU) (n : Nat) : Persistent (pubFloor (GF := GF) c n) := by
  unfold pubFloor; infer_instance
instance pubFloor_timeless (c : CPU) (n : Nat) : Timeless (pubFloor (GF := GF) c n) := by
  unfold pubFloor; infer_instance

/-- AGREEMENT: what the token says about the CURRENT log. -/
theorem pubFloorAgree (log : List Wmsg) (c : CPU) (n : Nat) :
    wlogAuth (GF := GF) log ∗ pubFloor c n ⊢ ⌜wpubUpto log (some c.val) n⌝ := by
  unfold pubFloor pubFloorn
  iintro ⟨Ha, ⟨%l, Hlb, %hp⟩⟩
  ihave %hpre := wlogValid log l $$ [Ha Hlb]
  · iframe Ha Hlb
  ipureintro
  exact wpubUptoPrefix l log _ n hpre hp

/-- MINTING, at the RELEASE/HANDOFF STORE's own ghost section. -/
theorem pubFloorMint (log : List Wmsg) (mrel : Wmsg) (c : CPU) :
    mrel.wmTid = some c.val → mrel.wmAk = .WCrel →
    wlogAuth (GF := GF) (log ++ [mrel]) ⊢
      wlogAuth (log ++ [mrel]) ∗ pubFloor c (log.length + 1) := by
  intro ht hk
  iintro Ha
  icases wlogSnapshot (log ++ [mrel]) $$ Ha with ⟨Ha, #Hlb⟩
  iframe Ha
  unfold pubFloor pubFloorn
  iexists log ++ [mrel]
  iframe Hlb
  ipureintro
  exact wpubUptoRel log mrel _ ht hk

/-- A floor may always be LOWERED. -/
theorem pubFloorLe (c : CPU) (n n' : Nat) :
    n' ≤ n → pubFloor (GF := GF) c n ⊢ pubFloor c n' := by
  intro hle
  unfold pubFloor pubFloorn
  iintro ⟨%l, Hlb, %hp⟩
  iexists l
  iframe Hlb
  ipureintro
  exact wpubUptoMono l _ n n' hle hp

/-- THE VIEW-INDEXED FLOOR (φ-upgrade §1.5): "hart `c` has published everything the view `V`
can see". -/
def pubCoversView (c : CPU) (V : View) : IProp GF :=
  iprop(∃ n : Nat, pubFloor c n ∗ ⌜V ≤ viewScl n⌝)

instance pubCoversView_persistent (c : CPU) (V : View) :
    Persistent (pubCoversView (GF := GF) c V) := by
  unfold pubCoversView; infer_instance
instance pubCoversView_timeless (c : CPU) (V : View) :
    Timeless (pubCoversView (GF := GF) c V) := by
  unfold pubCoversView; infer_instance

theorem pubCoversViewIntro (c : CPU) (V : View) (n : Nat) :
    V ≤ viewScl n → pubFloor (GF := GF) c n ⊢ pubCoversView c V := by
  intro hle
  unfold pubCoversView
  iintro H
  iexists n
  iframe H
  ipureintro
  exact hle

theorem pubCoversViewMono (c : CPU) (V V' : View) :
    V' ≤ V → pubCoversView (GF := GF) c V ⊢ pubCoversView c V' := by
  intro hle
  unfold pubCoversView
  iintro ⟨%n, H, %hn⟩
  iexists n
  iframe H
  ipureintro
  exact fun a => Nat.le_trans (hle a) (hn a)

/-! ### 3a″. THE CONTEXT'S WRITE BREADCRUMB, AND THE MIGRATION INVARIANT (φ-upgrade §1.6)

`ctxWrote ξ c V` — PERSISTENT: "context `ξ` wrote, through hart `c`, at or below `V`", minted by
the owned store leaf.  `ctxMigr ξ c` — the SCHEDULER-SIDE authority: "`ξ` is running on hart `c`,
and every OTHER hart it has ever written through has published what it wrote".  THE ALGEBRA IS A
MAX PER HART (a `GMapF Nat MaxNat` auth).  The live hart's entry is NOT covered; every entry
carries the POSITION BOUND `wlogTsOk`, which is what lets the PARK discharge the exception. -/

/-- "position `n` is IN the log". -/
def wlogTsOk (n : Nat) : IProp GF :=
  iprop(∃ l : List Wmsg, wlogLb l ∗ ⌜n ≤ l.length⌝)

instance wlogTsOk_persistent (n : Nat) : Persistent (wlogTsOk (GF := GF) n) := by
  unfold wlogTsOk; infer_instance
instance wlogTsOk_timeless (n : Nat) : Timeless (wlogTsOk (GF := GF) n) := by
  unfold wlogTsOk; infer_instance

theorem wlogTsOkGet (log : List Wmsg) (n : Nat) :
    n ≤ log.length → wlogAuth (GF := GF) log ⊢ wlogAuth log ∗ wlogTsOk n := by
  intro hn
  iintro Ha
  icases wlogSnapshot log $$ Ha with ⟨Ha, #Hlb⟩
  iframe Ha
  unfold wlogTsOk
  iexists log
  iframe Hlb
  ipureintro
  exact hn

theorem wlogTsOkBound (log : List Wmsg) (n : Nat) :
    wlogAuth (GF := GF) log ∗ wlogTsOk n ⊢ ⌜n ≤ log.length⌝ := by
  unfold wlogTsOk
  iintro ⟨Ha, ⟨%l, Hlb, %hn⟩⟩
  ihave %hpre := wlogValid log l $$ [Ha Hlb]
  · iframe Ha Hlb
  ipureintro
  have := prefix_length hpre
  omega

/-- ... and a published floor is bounded too, so EVERY entry of the map is. -/
theorem pubFloornBound (log : List Wmsg) (k n : Nat) :
    wlogAuth (GF := GF) log ∗ pubFloorn k n ⊢ ⌜n ≤ log.length⌝ := by
  unfold pubFloorn
  iintro ⟨Ha, ⟨%l, Hlb, %hp⟩⟩
  ihave %hpre := wlogValid log l $$ [Ha Hlb]
  · iframe Ha Hlb
  ipureintro
  have := prefix_length hpre
  have := wpubUptoLen l _ n hp
  omega

/-- The map, as an element of the algebra. -/
def ctxwrOf (m : GMapF Nat Nat) : CtxwrUR :=
  Iris.Std.PartialMap.map (M := GMapF Nat) (fun n : Nat => MaxNat.ofNat n) m

def ctxWrAuth (ξ : CtxId) (m : GMapF Nat Nat) : IProp GF :=
  iOwn (F := CtxwrRF) ξ.ctxWn (● (ctxwrOf m))

def ctxWrotePos (ξ : CtxId) (c : CPU) (t : Nat) : IProp GF :=
  iOwn (F := CtxwrRF) ξ.ctxWn (◯ (PartialMap.singleton c.val (MaxNat.ofNat t) : CtxwrUR))

instance ctxWrotePos_persistent (ξ : CtxId) (c : CPU) (t : Nat) :
    Persistent (ctxWrotePos (GF := GF) ξ c t) := by
  unfold ctxWrotePos; infer_instance
instance ctxWrotePos_timeless (ξ : CtxId) (c : CPU) (t : Nat) :
    Timeless (ctxWrotePos (GF := GF) ξ c t) := by
  unfold ctxWrotePos; infer_instance

/-- The VIEW-indexed breadcrumb. -/
def ctxWrote (ξ : CtxId) (c : CPU) (V : View) : IProp GF :=
  iprop(∃ t : Nat, ctxWrotePos ξ c t ∗ ⌜V ≤ viewScl t⌝)

instance ctxWrote_persistent (ξ : CtxId) (c : CPU) (V : View) :
    Persistent (ctxWrote (GF := GF) ξ c V) := by
  unfold ctxWrote; infer_instance
instance ctxWrote_timeless (ξ : CtxId) (c : CPU) (V : View) :
    Timeless (ctxWrote (GF := GF) ξ c V) := by
  unfold ctxWrote; infer_instance

theorem ctxWroteIntro (ξ : CtxId) (c : CPU) (t : Nat) :
    ctxWrotePos (GF := GF) ξ c t ⊢ ctxWrote ξ c (viewScl t) := by
  unfold ctxWrote
  iintro H
  iexists t
  iframe H
  ipureintro
  exact fun _ => Nat.le_refl _

theorem ctxWroteByte (ξ : CtxId) (c : CPU) (a : Int) (t : Nat) :
    ctxWrotePos (GF := GF) ξ c t ⊢ ctxWrote ξ c (viewByte a t) := by
  unfold ctxWrote
  iintro H
  iexists t
  iframe H
  ipureintro
  intro a'
  rw [flr_scl_eq]
  by_cases h : a' = a
  · subst h; rw [flr_byte_eq]; exact Nat.le_refl _
  · rw [flr_byte_ne a t a' h]; exact Nat.zero_le _

theorem ctxWroteMono (ξ : CtxId) (c : CPU) (V V' : View) :
    V' ≤ V → ctxWrote (GF := GF) ξ c V ⊢ ctxWrote ξ c V' := by
  intro hle
  unfold ctxWrote
  iintro ⟨%t, H, %ht⟩
  iexists t
  iframe H
  ipureintro
  exact fun a => Nat.le_trans (hle a) (ht a)

/-- THE INVARIANT, as a resource: the authority plus, per hart, either "this is the hart I am
running on" or full publication coverage — and, either way, the position bound. -/
def ctxMigr (ξ : CtxId) (c : CPU) : IProp GF :=
  iprop(∃ m : GMapF Nat Nat, ctxWrAuth ξ m ∗
    [∗map] k ↦ n ∈ m, wlogTsOk n ∗ (⌜k = c.val⌝ ∨ pubFloorn k n))

/-- THE PARKED FORM: EVERY entry covered, no live hart named. -/
def ctxMigrAll (ξ : CtxId) : IProp GF :=
  iprop(∃ m : GMapF Nat Nat, ctxWrAuth ξ m ∗ [∗map] k ↦ n ∈ m, wlogTsOk n ∗ pubFloorn k n)

theorem ctxMigrAllRun (ξ : CtxId) (c : CPU) : ctxMigrAll (GF := GF) ξ ⊢ ctxMigr ξ c := by
  unfold ctxMigrAll ctxMigr
  iintro ⟨%m, Ha, #Hall⟩
  iexists m
  iframe Ha
  iapply BigSepM.bigSepM_impl $$ Hall
  imodintro
  iintro %k %n %_ ⟨#Hts, #Hp⟩
  iframe Hts
  iright
  iexact Hp

theorem ctxWrAlloc : ⊢ |==> ∃ γ : GName, iOwn (GF := GF) (F := CtxwrRF) γ (● (∅ : CtxwrUR)) := by
  imod iOwn_alloc (F := CtxwrRF) (● (∅ : CtxwrUR)) with ⟨%γ, H⟩
  · exact Auth.auth_valid.mpr Heap.valid_empty
  imodintro
  iexists γ
  iexact H

theorem ctxwrOf_empty : ctxwrOf (∅ : GMapF Nat Nat) = (∅ : CtxwrUR) := by
  refine equiv_iff_eq.mp fun k => ?_
  simp [ctxwrOf, get?_map, get?_empty]

theorem ctxMigrEmpty (ξ : CtxId) (c : CPU) :
    iOwn (GF := GF) (F := CtxwrRF) ξ.ctxWn (● (∅ : CtxwrUR)) ⊢ ctxMigr ξ c := by
  unfold ctxMigr ctxWrAuth
  iintro H
  iexists (∅ : GMapF Nat Nat)
  rw [ctxwrOf_empty]
  iframe H
  iapply (BigSepM.bigSepM_empty (Φ := fun (k n : Nat) =>
    iprop(wlogTsOk (GF := GF) n ∗ (⌜k = c.val⌝ ∨ pubFloorn k n)))).mpr
  iempintro

/-- SPENDING A BREADCRUMB — the whole point of the stage. -/
theorem ctxMigrPub (ξ : CtxId) (c c' : CPU) (V : View) :
    c' ≠ c → ctxMigr (GF := GF) ξ c ∗ ctxWrote ξ c' V ⊢ pubCoversView c' V := by
  intro hne
  unfold ctxMigr ctxWrote ctxWrAuth ctxWrotePos
  iintro ⟨⟨%m, Ha, #Hall⟩, ⟨%t, Hf, %ht⟩⟩
  icombine Ha Hf gives %hv
  have hm : ∃ n, get? m c'.val = some n ∧ t ≤ n := by
    have hinc := (Auth.auth_both_valid_discrete.mp hv).1
    obtain ⟨y, hy, hle⟩ := Heap.singleton_inc_iff.mp hinc
    rw [ctxwrOf, get?_map] at hy
    cases hn : get? m c'.val with
    | none => rw [hn] at hy; cases hy
    | some n =>
      rw [hn] at hy
      cases hy
      refine ⟨n, rfl, ?_⟩
      have h2 := MaxNat.inc_iff.mp (Option.some_inc_some_iff_is_total.mp hle)
      simpa [MaxNat.le_toNat] using h2
  obtain ⟨n, hn, htn⟩ := hm
  ihave Hent := BigSepM.bigSepM_lookup hn $$ Hall
  icases Hent with ⟨-, (%hk | Hpf)⟩
  · exact absurd (Fin.ext hk) hne
  · have hle : V ≤ viewScl n := by
      intro a
      have := ht a
      rw [flr_scl_eq] at this ⊢
      omega
    iapply pubCoversViewIntro c' V n hle
    unfold pubFloor
    iexact Hpf

theorem ctxwrValid (x : CtxwrUR) : ✓ x := fun k => by
  cases get? x k <;> trivial

/-- The algebraic step behind the mint: raising one key of the map IS op-ing the singleton in. -/
theorem ctxwrFmapOp (m : GMapF Nat Nat) (k t : Nat) :
    ctxwrOf (insert m k (max t ((get? m k).getD 0))) =
      (PartialMap.singleton k (MaxNat.ofNat t) : CtxwrUR) • ctxwrOf m := by
  refine equiv_iff_eq.mp fun i => ?_
  show get? (ctxwrOf (insert m k (max t ((get? m k).getD 0)))) i =
    get? ((PartialMap.singleton k (MaxNat.ofNat t) : CtxwrUR) • ctxwrOf m) i
  rw [Heap.get?_op, ctxwrOf, ctxwrOf, get?_map, get?_map]
  by_cases h : k = i
  · subst h
    rw [get?_insert_eq rfl, get?_singleton_eq rfl]
    cases hk : get? m k with
    | none =>
      simp only [Option.map, Option.getD]
      show some (MaxNat.ofNat (max t 0)) = some (MaxNat.ofNat t) • none
      rw [Nat.max_zero]; rfl
    | some n =>
      simp only [Option.map, Option.getD]
      show some (MaxNat.ofNat (max t n)) = some (MaxNat.ofNat t • MaxNat.ofNat n)
      congr 1
  · rw [get?_insert_ne h, get?_singleton_ne h]
    cases get? m i <;> rfl

/-- The update behind the mint (Lean-only helper, inlined in Rocq's `ctx_migr_mint`). -/
theorem ctxwrMintUpd (m : GMapF Nat Nat) (k t : Nat) :
    (● (ctxwrOf m) : Auth CtxwrUR) ~~>
      (● (ctxwrOf (insert m k (max t ((get? m k).getD 0))))) •
        ◯ (PartialMap.singleton k (MaxNat.ofNat t) : CtxwrUR) := by
  refine Auth.auth_update_alloc ?_
  have h := LocalUpdate.op_discrete (ctxwrOf m) (UCMRA.unit : CtxwrUR)
    (PartialMap.singleton k (MaxNat.ofNat t) : CtxwrUR) (fun _ => ctxwrValid _)
  have he : (PartialMap.singleton k (MaxNat.ofNat t) : CtxwrUR) • (UCMRA.unit : CtxwrUR) =
      PartialMap.singleton k (MaxNat.ofNat t) := Heap.op_empty_right
  rw [he, ← ctxwrFmapOp] at h
  exact h

/-- MINTING, at the owned store leaf. -/
theorem ctxMigrMint (ξ : CtxId) (c : CPU) (log : List Wmsg) (t : Nat) :
    t ≤ log.length →
    wlogAuth (GF := GF) log ∗ ctxMigr ξ c ⊢
      |==> (wlogAuth log ∗ ctxMigr ξ c ∗ ctxWrotePos ξ c t) := by
  intro ht
  unfold ctxMigr
  iintro ⟨Hlog, ⟨%m, Ha, #Hall⟩⟩
  -- the old entry is bounded too, so the raised one still is
  ihave %hn' : ⌜max t ((get? m c.val).getD 0) ≤ log.length⌝ $$ [Hlog]
  · cases hk : get? m c.val with
    | none =>
      ipureintro
      simp only [Option.getD]
      omega
    | some n =>
      ihave Hent := BigSepM.bigSepM_lookup hk $$ Hall
      icases Hent with ⟨#Hts, -⟩
      ihave %hb := wlogTsOkBound log n $$ [Hlog Hts]
      · iframe Hlog Hts
      ipureintro
      simp only [Option.getD]
      omega
  icases wlogTsOkGet log _ hn' $$ Hlog with ⟨Hlog, #Hts'⟩
  unfold ctxWrAuth ctxWrotePos
  imod iOwn_update (ctxwrMintUpd m c.val t) $$ Ha with H
  icases iOwn_op.1 $$ H with ⟨Ha, #Hf⟩
  imodintro
  iframe Hlog Hf
  iexists insert m c.val (max t ((get? m c.val).getD 0))
  iframe Ha
  iapply BigSepM.bigSepM_insert_elim $$ [Hts'] Hall
  iframe Hts'
  ileft
  ipureintro
  rfl

/-- THE PARK.  The migration handoff's release publishes every position at or below the log's
length, and every entry of the map is at or below that. -/
theorem ctxMigrPark (ξ : CtxId) (c : CPU) (log : List Wmsg) (N : Nat) :
    log.length ≤ N →
    wlogAuth (GF := GF) log ∗ pubFloor c N ∗ ctxMigr ξ c ⊢ wlogAuth log ∗ ctxMigrAll ξ := by
  intro hN
  unfold ctxMigr ctxMigrAll
  iintro ⟨Hlog, #Hpf, ⟨%m, Ha, #Hall⟩⟩
  ihave %hbnd : ⌜∀ k n, get? m k = some n → n ≤ log.length⌝ $$ [Hlog]
  · iintro %k %n %hkn
    ihave Hent := BigSepM.bigSepM_lookup hkn $$ Hall
    icases Hent with ⟨#Hts, -⟩
    iapply wlogTsOkBound log n $$ [Hlog Hts]
    iframe Hlog Hts
  iframe Hlog
  iexists m
  iframe Ha
  iapply BigSepM.bigSepM_impl $$ Hall
  imodintro
  iintro %k %n %hkn ⟨#Hts, Hor⟩
  iframe Hts
  icases Hor with (%hk | #Hp)
  · subst hk
    ihave Hn := pubFloorLe c N n (by have := hbnd _ n hkn; omega) $$ Hpf
    unfold pubFloor
    iexact Hn
  · iexact Hp

/-! ### 3b. the per-byte latest-write map (the BASE points-to) -/

/-- THE VALUE ELEMENT — one half of the points-to; the other half is the C/D/S state. -/
def wlatElem (a : Int) (dq : DFrac) (t : Nat) (v : BitVec 8) : IProp GF :=
  ghost_map_elem (WeakGS.latName (GF := GF)) dq a (t, v)

/-- THE STATE ELEMENTS. -/
def wcdsEl (a : Int) (dq : DFrac) (s : Wcds) : IProp GF :=
  ghost_map_elem (WeakGS.cdsName (GF := GF)) dq a s

def wclean (a : Int) (dq : DFrac) : IProp GF := wcdsEl (GF := GF) a dq WClean

def wdirty (c : CPU) (a : Int) : IProp GF := wcdsEl (GF := GF) a (DFrac.own 1) (WDirty c)

/-- The PERSISTENT sync witness: it pins no value, and it is `DFrac.discard`, so it is
INCOMPATIBLE with the full-fraction state element every owned store consumes. -/
def syncByte (a : Int) : IProp GF := wcdsEl (GF := GF) a DFrac.discard WSync

instance syncByte_persistent (a : Int) : Persistent (syncByte (GF := GF) a) := by
  unfold syncByte wcdsEl; infer_instance

/-- A WHOLE ACCESS WINDOW is sync — the shape the racy load rules take as a premise. -/
def syncWin (a : PAddr) (n : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range' 0 n, syncByte (WeakInterp.accAddr a j))

instance syncWin_persistent (a : PAddr) (n : Nat) : Persistent (syncWin (GF := GF) a n) := by
  unfold syncWin; infer_instance

theorem syncWinByte (a : PAddr) (n j : Nat) :
    j < n → syncWin (GF := GF) a n ⊢ syncByte (WeakInterp.accAddr a j) := by
  intro hj
  unfold syncWin
  have h : (List.range' 0 n)[j]? = some j := by rw [lookup_seq_lt hj, Nat.zero_add]
  exact BigSepL.bigSepL_lookup (Φ := fun _ j => syncByte (GF := GF) (WeakInterp.accAddr a j)) h

/-- The four-byte constructor, the only width any racy site in this tree uses. -/
theorem syncWin4 (a : PAddr) :
    syncByte (GF := GF) (WeakInterp.accAddr a 0) ∗ syncByte (WeakInterp.accAddr a 1) ∗
      syncByte (WeakInterp.accAddr a 2) ∗ syncByte (WeakInterp.accAddr a 3) ⊢ syncWin a 4 := by
  unfold syncWin
  iintro ⟨#H0, #H1, #H2, #H3⟩
  simp only [List.range']
  iframe H0 H1 H2 H3
  iapply BigSepL.bigSepL_nil.mpr
  iempintro

/-- THE LOCK-BYTE FRAGMENT (T2-0).  Exclusive; only its holder may write the byte. -/
def wlockSt (a base : Int) (n0 : Nat) (h : Option Nat) : IProp GF :=
  wcdsEl (GF := GF) a (DFrac.own 1) (WLock base n0 h)

instance wcdsEl_timeless (a : Int) (dq : DFrac) (s : Wcds) : Timeless (wcdsEl (GF := GF) a dq s) := by
  unfold wcdsEl; infer_instance

instance wlockSt_timeless (a base : Int) (n0 : Nat) (h : Option Nat) :
    Timeless (wlockSt (GF := GF) a base n0 h) := by
  unfold wlockSt; infer_instance

theorem wlockStLookup (a base : Int) (n0 : Nat) (h : Option Nat) (mc : GMapF Int Wcds) :
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ∗ wlockSt a base n0 h ⊢
      ⌜get? mc a = some (WLock base n0 h)⌝ := by
  unfold wlockSt wcdsEl
  iintro ⟨Ha, Hel⟩
  icombine Ha Hel gives %hlk
  ipureintro
  exact hlk

/-- A lock byte is not a clean/owned/sync one. -/
theorem wlockStCleanExcl (a base : Int) (n0 : Nat) (h : Option Nat) (dq : DFrac) :
    wlockSt (GF := GF) a base n0 h ∗ wclean a dq ⊢ False := by
  unfold wlockSt wclean wcdsEl
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %⟨_, hq⟩
  cases hq

/-- THE PROTECTED-BYTE FRAGMENT (T2-0′ / F3″).  Exclusive; the byte's registration witness AND
the carrier of the dirty author `d`. -/
def wprotSt (a : Int) (γ : GName) (base : Int) (n0 r0 : Nat) (d : Option CPU) : IProp GF :=
  wcdsEl (GF := GF) a (DFrac.own 1) (WProt γ base n0 r0 d)

instance wprotSt_timeless (a : Int) (γ : GName) (base : Int) (n0 r0 : Nat) (d : Option CPU) :
    Timeless (wprotSt (GF := GF) a γ base n0 r0 d) := by
  unfold wprotSt; infer_instance

theorem wprotStLookup (a : Int) (γ : GName) (base : Int) (n0 r0 : Nat) (d : Option CPU)
    (mc : GMapF Int Wcds) :
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ∗ wprotSt a γ base n0 r0 d ⊢
      ⌜get? mc a = some (WProt γ base n0 r0 d)⌝ := by
  unfold wprotSt wcdsEl
  iintro ⟨Ha, Hel⟩
  icombine Ha Hel gives %hlk
  ipureintro
  exact hlk

theorem wprotStCleanExcl (a : Int) (γ : GName) (base : Int) (n0 r0 : Nat) (d : Option CPU)
    (dq : DFrac) : wprotSt (GF := GF) a γ base n0 r0 d ∗ wclean a dq ⊢ False := by
  unfold wprotSt wclean wcdsEl
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %⟨_, hq⟩
  cases hq

theorem wprotStLockExcl (a : Int) (γ : GName) (base : Int) (n0 r0 : Nat) (d : Option CPU)
    (base' : Int) (n0' : Nat) (h : Option Nat) :
    wprotSt (GF := GF) a γ base n0 r0 d ∗ wlockSt a base' n0' h ⊢ False := by
  unfold wprotSt wlockSt wcdsEl
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %⟨_, hq⟩
  cases hq

/-- THE OWNED STATE: clean, or dirty by THIS hart. -/
def wownSt (c : CPU) (a : Int) : IProp GF :=
  iprop(∃ s : Wcds, wcdsEl a (DFrac.own 1) s ∗ ⌜s = WClean ∨ s = WDirty c⌝)

instance wownSt_timeless (c : CPU) (a : Int) : Timeless (wownSt (GF := GF) c a) := by
  unfold wownSt; infer_instance

theorem wcleanOwnSt (c : CPU) (a : Int) : wclean (GF := GF) a (DFrac.own 1) ⊢ wownSt c a := by
  unfold wclean wownSt
  iintro H
  iexists WClean
  iframe H
  ipureintro
  exact .inl rfl

theorem wdirtyOwnSt (c : CPU) (a : Int) : wdirty (GF := GF) c a ⊢ wownSt c a := by
  unfold wdirty wownSt
  iintro H
  iexists WDirty c
  iframe H
  ipureintro
  exact .inr rfl

theorem wprotStOwnExcl (c : CPU) (a : Int) (γ : GName) (base : Int) (n0 r0 : Nat)
    (d : Option CPU) : wprotSt (GF := GF) a γ base n0 r0 d ∗ wownSt c a ⊢ False := by
  unfold wprotSt wownSt wcdsEl
  iintro ⟨H1, ⟨%s, Hel, %hs⟩⟩
  icombine H1 Hel gives %⟨_, hq⟩
  rcases hs with rfl | rfl <;> cases hq

/-- A full-fraction state element and a sync witness cannot coexist. -/
theorem wcdsElSyncExcl (a : Int) (s : Wcds) :
    wcdsEl (GF := GF) a (DFrac.own 1) s ∗ syncByte a ⊢ False := by
  unfold syncByte wcdsEl
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %⟨hv, _⟩
  exact absurd (DFrac.valid_own_op_discard.mp hv) (by have : (1 : Qp).val = 1 := rfl; grind)

/-- THE BASE POINTS-TO: the value element PLUS the clean state, at the same fraction. -/
def wlatPointsto (a : Int) (dq : DFrac) (t : Nat) (v : BitVec 8) : IProp GF :=
  iprop(wlatElem a dq t v ∗ wclean a dq)

theorem wlatPointstoElem (a : Int) (dq : DFrac) (t : Nat) (v : BitVec 8) :
    wlatPointsto (GF := GF) a dq t v ⊢ wlatElem a dq t v := by
  unfold wlatPointsto
  iintro ⟨H, -⟩
  iexact H

def wlatInterp (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) : IProp GF :=
  iprop(∃ (m : GMapF Int (Nat × BitVec 8)) (mc : GMapF Int Wcds),
    ghost_map_auth (GF := GF) (WeakGS.latName (GF := GF)) (DFrac.own 1) m ∗ ⌜wlatAgree (imgZ img) log m⌝ ∗
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ∗ ⌜wcdsAgree log mc⌝)

/-- THE READ BRIDGE: my element IS the latest write. -/
theorem wlatLookupElem (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (dq : DFrac)
    (t : Nat) (v : BitVec 8) :
    wlatInterp (GF := GF) img log ∗ wlatElem a dq t v ⊢ ⌜latestVal (imgZ img) log a t v⌝ := by
  unfold wlatInterp wlatElem
  iintro ⟨⟨%m, %mc, Hauth, %hag, -, -⟩, He⟩
  icombine Hauth He gives %hlk
  ipureintro
  exact hag a (t, v) hlk

theorem wlatLookup (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (dq : DFrac)
    (t : Nat) (v : BitVec 8) :
    wlatInterp (GF := GF) img log ∗ wlatPointsto a dq t v ⊢ ⌜latestVal (imgZ img) log a t v⌝ := by
  unfold wlatPointsto
  iintro ⟨Hi, ⟨He, -⟩⟩
  iapply wlatLookupElem img log a dq t v
  iframe Hi He

/-- The C/D/S lookup: an owned state element is accurate at the log. -/
theorem wcdsLookup (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (dq : DFrac)
    (s : Wcds) : wlatInterp (GF := GF) img log ∗ wcdsEl a dq s ⊢ ⌜wcdsOk log a s⌝ := by
  unfold wlatInterp wcdsEl
  iintro ⟨⟨%m, %mc, -, -, Hauth, %hag⟩, He⟩
  icombine Hauth He gives %hlk
  ipureintro
  exact hag a s hlk

theorem wownStLookup (c : CPU) (a : Int) (mc : GMapF Int Wcds) :
    ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ∗ wownSt c a ⊢
      ⌜∃ s, get? mc a = some s ∧ (s = WClean ∨ s = WDirty c)⌝ := by
  unfold wownSt wcdsEl
  iintro ⟨Ha, ⟨%s, Hel, %hs⟩⟩
  icombine Ha Hel gives %hlk
  ipureintro
  exact ⟨s, hlk, hs⟩

/-- SYNC-PURITY, at the surface: a sync byte carries no owned store. -/
theorem syncByteNoPlain (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) :
    wlatInterp (GF := GF) img log ∗ syncByte a ⊢ ⌜wcdsSync log a⌝ := by
  unfold syncByte
  exact wcdsLookup img log a _ WSync

/-- The ghost readings of the three arms.  Each is one `wcdsLookup`. -/
theorem nvByteOfClean (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (dq : DFrac) (n : Nat) :
    wlatInterp (GF := GF) img log ∗ wclean a dq ⊢ ⌜nvByte log c a n⌝ := by
  unfold wclean
  iintro H
  ihave %hok := wcdsLookup img log a dq WClean $$ H
  ipureintro
  exact nvByteClean log c a n hok

theorem nvByteOfPointsto (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (dq : DFrac) (t : Nat) (v : BitVec 8) (n : Nat) :
    wlatInterp (GF := GF) img log ∗ wlatPointsto a dq t v ⊢ ⌜nvByte log c a n⌝ := by
  unfold wlatPointsto
  iintro ⟨Hi, ⟨-, He⟩⟩
  iapply nvByteOfClean img log c a dq n
  iframe Hi He

theorem nvByteOfOwnSt (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (n : Nat) : wlatInterp (GF := GF) img log ∗ wownSt c a ⊢ ⌜nvByte log c a n⌝ := by
  unfold wownSt
  iintro ⟨Hi, ⟨%s, Hel, %hs⟩⟩
  ihave %hok := wcdsLookup img log a _ s $$ [Hi Hel]
  · iframe Hi Hel
  ipureintro
  exact nvByteOk log c a n s hok (by rcases hs with h | h <;> simp [h])

theorem nvByteOfSync (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (n : Nat) : wlatInterp (GF := GF) img log ∗ syncByte a ⊢ ⌜nvByte log c a n⌝ := by
  iintro H
  ihave %hsy := syncByteNoPlain img log a $$ H
  ipureintro
  exact nvByteSync log c a n hsy

/-- The `nvFree` forms — what a site EXPORTS when it is about to give the fragment back. -/
theorem nvFreeOfClean (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (dq : DFrac) :
    wlatInterp (GF := GF) img log ∗ wclean a dq ⊢ ⌜nvFree log a⌝ := by
  unfold wclean
  iintro H
  ihave %hok := wcdsLookup img log a dq WClean $$ H
  ipureintro
  exact nvFreeClean log a hok

theorem nvFreeOfPointsto (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (dq : DFrac)
    (t : Nat) (v : BitVec 8) :
    wlatInterp (GF := GF) img log ∗ wlatPointsto a dq t v ⊢ ⌜nvFree log a⌝ := by
  unfold wlatPointsto
  iintro ⟨Hi, ⟨-, He⟩⟩
  iapply nvFreeOfClean img log a dq
  iframe Hi He

theorem nvFreeOfSync (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) :
    wlatInterp (GF := GF) img log ∗ syncByte a ⊢ ⌜nvFree log a⌝ := by
  iintro H
  ihave %hsy := syncByteNoPlain img log a $$ H
  ipureintro
  exact nvFreeSync log a hsy

/-- The hart-indexed readings. -/
theorem nvOkOfOwnSt (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int) :
    wlatInterp (GF := GF) img log ∗ wownSt c a ⊢ ⌜nvOk log c a⌝ := by
  unfold wownSt
  iintro ⟨Hi, ⟨%s, Hel, %hs⟩⟩
  ihave %hok := wcdsLookup img log a _ s $$ [Hi Hel]
  · iframe Hi Hel
  ipureintro
  exact fun n => nvByteOk log c a n s hok (by rcases hs with h | h <;> simp [h])

theorem nvOkOfPointsto (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (dq : DFrac) (t : Nat) (v : BitVec 8) :
    wlatInterp (GF := GF) img log ∗ wlatPointsto a dq t v ⊢ ⌜nvOk log c a⌝ := by
  iintro H
  ihave %h := nvFreeOfPointsto img log a dq t v $$ H
  ipureintro
  exact nvOkOfFree log c a h

theorem nvOkOfSync (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int) :
    wlatInterp (GF := GF) img log ∗ syncByte a ⊢ ⌜nvOk log c a⌝ := by
  iintro H
  ihave %h := nvFreeOfSync img log a $$ H
  ipureintro
  exact nvOkOfFree log c a h

/-! ### 3b′. THE LOCK-PROTOCOL EXPORT (T2-0 / S6 §4)

The pure per-state fact that every message overlapping a registered lock word is acquire- or
release-shaped, read off the very auth map that carries the C/D/S states. -/

theorem wlpAtOfLock (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a base : Int) (n0 : Nat)
    (h : Option Nat) :
    wlatInterp (GF := GF) img log ∗ wlockSt a base n0 h ⊢ ⌜wlpAt log a base n0⌝ := by
  unfold wlockSt
  iintro H
  ihave %hok := wcdsLookup img log a _ _ $$ H
  ipureintro
  exact wcdsLockWlp log a base n0 h hok

/-- ... and its T2-0′ twin: the ALTERNATION, off the same fragment. -/
theorem wlpAltOfLock (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a base : Int) (n0 : Nat)
    (h : Option Nat) :
    wlatInterp (GF := GF) img log ∗ wlockSt a base n0 h ⊢ ⌜wlpAlt log a n0 h⌝ := by
  unfold wlockSt
  iintro H
  ihave %hok := wcdsLookup img log a _ _ $$ H
  ipureintro
  exact wcdsLockAlt log a base n0 h hok

theorem nvFreeOfLock (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a base : Int) (n0 : Nat)
    (h : Option Nat) :
    wlatInterp (GF := GF) img log ∗ wlockSt a base n0 h ⊢ ⌜nvFree log a⌝ := by
  unfold wlockSt
  iintro H
  ihave %hok := wcdsLookup img log a _ _ $$ H
  ipureintro
  exact nvFreeLock log a base n0 h hok

theorem nvOkOfLock (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a base : Int)
    (n0 : Nat) (h : Option Nat) :
    wlatInterp (GF := GF) img log ∗ wlockSt a base n0 h ⊢ ⌜nvOk log c a⌝ := by
  iintro H
  ihave %hf := nvFreeOfLock img log a base n0 h $$ H
  ipureintro
  exact nvOkOfFree log c a hf

/-- THE REGISTRATION.  A clean byte inside the word's range becomes a lock byte, at
`n0 = length log`. -/
theorem wlockRegister (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a base : Int) :
    (base ≤ a ∧ a < base + 4) →
    wlatInterp (GF := GF) img log ∗ wclean a (DFrac.own 1) ⊢
      |==> (wlatInterp img log ∗ wlockSt a base log.length none) := by
  intro hrng
  unfold wlatInterp wclean wlockSt wcdsEl
  iintro ⟨⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩, Hel⟩
  icombine Hc Hel gives %hlk
  imod ghost_map_update (WLock base log.length none) $$ Hc Hel with ⟨Hc, Hel⟩
  imodintro
  iframe Hel
  iexists m, insert mc a (WLock base log.length none)
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  · ipureintro
    exact wcdsAgreeInsert log mc a _ hagc (wcdsOkRegister log a base hrng (hagc a WClean hlk))

/-! ### THE PROTECTED-BYTE OPERATIONS (T2-0′ / F3″) -/

/-- REGISTRATION: a clean byte joins the footprint, protected from the CURRENT log length on. -/
theorem wprotRegister (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (γ : GName)
    (base : Int) (n0 : Nat) :
    n0 ≤ log.length →
    wlatInterp (GF := GF) img log ∗ wclean a (DFrac.own 1) ⊢
      |==> (wlatInterp img log ∗ wprotSt a γ base n0 log.length none) := by
  intro hn0
  unfold wlatInterp wclean wprotSt wcdsEl
  iintro ⟨⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩, Hel⟩
  icombine Hc Hel gives %hlk
  imod ghost_map_update (WProt γ base n0 log.length none) $$ Hc Hel with ⟨Hc, Hel⟩
  imodintro
  iframe Hel
  iexists m, insert mc a (WProt γ base n0 log.length none)
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  · ipureintro
    exact wcdsAgreeInsert log mc a _ hagc
      (wcdsOkRegisterProt log a base n0 hn0 (hagc a WClean hlk))

/-- DEREGISTRATION, at `d = none`: what comes back is an ordinary clean fragment. -/
theorem wprotDeregister (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (γ : GName)
    (base : Int) (n0 r0 : Nat) :
    wlatInterp (GF := GF) img log ∗ wprotSt a γ base n0 r0 none ⊢
      |==> (wlatInterp img log ∗ wclean a (DFrac.own 1)) := by
  unfold wlatInterp wclean wprotSt wcdsEl
  iintro ⟨⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩, Hel⟩
  icombine Hc Hel gives %hlk
  imod ghost_map_update WClean $$ Hc Hel with ⟨Hc, Hel⟩
  imodintro
  iframe Hel
  iexists m, insert mc a WClean
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  · ipureintro
    exact wcdsAgreeInsert log mc a _ hagc
      (wcdsOkDeregisterProt log a base n0 r0 none (hagc a _ hlk))

/-- THE D→C FLIP at a release site, `wlatFlip`'s twin. -/
theorem wprotFlip (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (mrel : Wmsg) (c : CPU)
    (a : Int) (γ : GName) (base : Int) (n0 r0 : Nat) :
    mrel.wmTid = some c.val → mrel.wmAk = .WCrel →
    wlatInterp (GF := GF) img (log ++ [mrel]) ∗ wprotSt a γ base n0 r0 (some c) ⊢
      |==> (wlatInterp img (log ++ [mrel]) ∗ wprotSt a γ base n0 r0 none) := by
  intro htid hk
  unfold wlatInterp wprotSt wcdsEl
  iintro ⟨⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩, Hel⟩
  icombine Hc Hel gives %hlk
  imod ghost_map_update (WProt γ base n0 r0 none) $$ Hc Hel with ⟨Hc, Hel⟩
  imodintro
  iframe Hel
  iexists m, insert mc a (WProt γ base n0 r0 none)
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  · ipureintro
    refine wcdsAgreeInsert _ mc a _ hagc ?_
    exact wcdsProtFlip _ a base n0 r0 c log.length mrel (list_lookup_middle rfl) htid hk
      (by simp) (hagc a _ hlk)

/-- THE PROTECTED STORE, at the ghost altitude: the byte's VALUE element is retargeted at the
appended message and its state moves to "dirty by the storing hart". -/
theorem wprotStore (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (mnew : Wmsg) (a : Int)
    (γ : GName) (base : Int) (n0 r0 : Nat) (d : Option CPU) (c : CPU) (t : Nat) (w b : BitVec 8) :
    mnew.wmAk = .WCplain → mnew.wmTid = some c.val →
    (d = none ∨ d = some c) →
    wlpHolderAt log base n0 log.length = some (some c.val) →
    msgByte mnew a = some b →
    (∀ a', a' ≠ a → msgByte mnew a' = none) →
    wlatInterp (GF := GF) img log ∗ wlatElem a (DFrac.own 1) t w ∗ wprotSt a γ base n0 r0 d ⊢
      |==> (wlatInterp img (log ++ [mnew]) ∗ wlatElem a (DFrac.own 1) (log.length + 1) b ∗
        wprotSt a γ base n0 r0 (some c)) := by
  intro hk htid hd hhold hma hother
  unfold wlatInterp wlatElem wprotSt wcdsEl
  iintro ⟨⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩, He, Hs⟩
  icombine Hc Hs gives %hlk
  imod ghost_map_update (log.length + 1, b) $$ Hauth He with ⟨Hauth, He⟩
  imod ghost_map_update (WProt γ base n0 r0 (some c)) $$ Hc Hs with ⟨Hc, Hs⟩
  imodintro
  iframe He Hs
  iexists insert mm a (log.length + 1, b), insert mc a (WProt γ base n0 r0 (some c))
  iframe Hauth Hc
  isplit
  · ipureintro
    exact wlatAgreeStore (imgZ img) log mnew a b mm hma hother hag
  · ipureintro
    intro a' s' ha'
    by_cases h : a' = a
    · subst h
      rw [lookupInsert] at ha'
      cases ha'
      exact wcdsOkStoreProt log mnew a' base n0 r0 d c hk htid hd hhold (hagc a' _ hlk)
    · rw [lookupInsertNe (Ne.symm h)] at ha'
      refine wcdsOkApp log [mnew] a' s' ?_ (hagc a' s' ha')
      intro m0 hm0
      rw [List.mem_singleton] at hm0
      subst hm0
      exact hother a' h

/-- THE READINGS off the fragment: the protection clause itself, and φ's obligation. -/
theorem wprotAtOfProt (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (γ : GName)
    (base : Int) (n0 r0 : Nat) (d : Option CPU) :
    wlatInterp (GF := GF) img log ∗ wprotSt a γ base n0 r0 d ⊢ ⌜wprotAt log a base n0 r0⌝ := by
  unfold wprotSt
  iintro H
  ihave %hok := wcdsLookup img log a _ _ $$ H
  ipureintro
  exact wcdsProtWprot log a γ base n0 r0 d hok

theorem nvByteOfProt (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (γ : GName) (base : Int) (n0 r0 : Nat) (d : Option CPU) (n : Nat) :
    (d = none ∨ d = some c) →
    wlatInterp (GF := GF) img log ∗ wprotSt a γ base n0 r0 d ⊢ ⌜nvByte log c a n⌝ := by
  intro hd
  unfold wprotSt
  iintro H
  ihave %hok := wcdsLookup img log a _ _ $$ H
  ipureintro
  exact nvByteProt log c a n base n0 r0 d hok hd

theorem nvFreeOfProt (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (γ : GName)
    (base : Int) (n0 r0 : Nat) :
    wlatInterp (GF := GF) img log ∗ wprotSt a γ base n0 r0 none ⊢ ⌜nvFree log a⌝ := by
  unfold wprotSt
  iintro H
  ihave %hok := wcdsLookup img log a _ _ $$ H
  ipureintro
  exact nvFreeProt log a base n0 r0 hok

/-- The accessor M2's store leaf uses: take the authority out, update the elements of the bytes
the store wrote, put it back at the new log. -/
theorem wlatInterpAcc (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) :
    wlatInterp (GF := GF) img log ⊢
      ∃ (m : GMapF Int (Nat × BitVec 8)) (mc : GMapF Int Wcds),
        ghost_map_auth (GF := GF) (WeakGS.latName (GF := GF)) (DFrac.own 1) m ∗
        ⌜wlatAgree (imgZ img) log m⌝ ∗
        ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc ∗ ⌜wcdsAgree log mc⌝ ∗
        (∀ (m' : GMapF Int (Nat × BitVec 8)) (mc' : GMapF Int Wcds) (log' : List Wmsg),
          ghost_map_auth (GF := GF) (WeakGS.latName (GF := GF)) (DFrac.own 1) m' -∗
          ⌜wlatAgree (imgZ img) log' m'⌝ -∗
          ghost_map_auth (GF := GF) (WeakGS.cdsName (GF := GF)) (DFrac.own 1) mc' -∗
          ⌜wcdsAgree log' mc'⌝ -∗ wlatInterp img log') := by
  unfold wlatInterp
  iintro ⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩
  iexists m, mc
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  isplit
  · ipureintro; exact hagc
  iintro %m' %mc' %log' Hauth' %hag' Hc' %hagc'
  iexists m', mc'
  iframe Hauth' Hc'
  isplit
  · ipureintro; exact hag'
  · ipureintro; exact hagc'

/-! ### 3b‴. THE D→C FLIP and the S mint -/

/-- The ghost half of a RELEASE: once the releasing hart's `WCrel` message is the log's last,
every byte that hart had dirtied is clean. -/
theorem wlatFlip (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (mrel : Wmsg) (c : CPU)
    (a : Int) :
    mrel.wmTid = some c.val → mrel.wmAk = .WCrel →
    wlatInterp (GF := GF) img (log ++ [mrel]) ∗ wownSt c a ⊢
      |==> (wlatInterp img (log ++ [mrel]) ∗ wclean a (DFrac.own 1)) := by
  intro htid hk
  unfold wlatInterp wownSt wclean wcdsEl
  iintro ⟨⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩, ⟨%s, Hel, %hs⟩⟩
  icombine Hc Hel gives %hlk
  imod ghost_map_update WClean $$ Hc Hel with ⟨Hc, Hel⟩
  imodintro
  iframe Hel
  iexists m, insert mc a WClean
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  · ipureintro
    refine wcdsAgreeInsert _ mc a _ hagc ?_
    rcases hs with rfl | rfl
    · exact hagc a WClean hlk
    · exact wcdsDirtyFlip _ a c log.length mrel (list_lookup_middle rfl) htid hk (by simp)
        (hagc a (WDirty c) hlk)

/-! ### 3b″. THE LAZY UPGRADE — the D→C flip a MIGRATED thread does

`pubFloor c n` says `c` published everything below `n`, and the element's timestamp `t ≤ n` says
the byte's whole write history is inside that; the state element is retargeted
`WDirty c → WClean` with no premise about the current top. -/

theorem nvFreeOfOwnPure (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (t n : Nat) (v : BitVec 8) :
    t ≤ n → wpubUpto log (some c.val) n →
    wlatInterp (GF := GF) img log ∗ wlatElem a (DFrac.own 1) t v ∗ wownSt c a ⊢
      ⌜nvFree log a⌝ := by
  intro htn hpub
  unfold wownSt
  iintro ⟨Hi, Hel, ⟨%s, Hsel, %hs⟩⟩
  ihave %hlat := wlatLookupElem img log a _ t v $$ [Hi Hel]
  · iframe Hi Hel
  ihave %hok := wcdsLookup img log a _ s $$ [Hi Hsel]
  · iframe Hi Hsel
  ipureintro
  rcases hs with rfl | rfl
  · exact nvFreeClean log a hok
  · exact nvFreePublished (imgZ img) log a c t n v hlat htn hpub hok

theorem nvFreeOfOwnPub (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (t n : Nat) (v : BitVec 8) :
    t ≤ n →
    wlogAuth (GF := GF) log ∗ pubFloor c n ∗ wlatInterp img log ∗
      wlatElem a (DFrac.own 1) t v ∗ wownSt c a ⊢ ⌜nvFree log a⌝ := by
  intro htn
  iintro ⟨Hlog, #Hpf, Hi, Hel, Hs⟩
  ihave %hpub := pubFloorAgree log c n $$ [Hlog Hpf]
  · iframe Hlog Hpf
  iapply nvFreeOfOwnPure img log c a t n v htn hpub
  iframe Hi Hel Hs

theorem wlatFlipPure (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (t n : Nat) (v : BitVec 8) :
    t ≤ n → wpubUpto log (some c.val) n →
    wlatInterp (GF := GF) img log ∗ wlatElem a (DFrac.own 1) t v ∗ wownSt c a ⊢
      |==> (wlatInterp img log ∗ wlatElem a (DFrac.own 1) t v ∗ wclean a (DFrac.own 1)) := by
  intro htn hpub
  iintro ⟨Hi, Hel, Hs⟩
  ihave %hlat := wlatLookupElem img log a _ t v $$ [Hi Hel]
  · iframe Hi Hel
  unfold wownSt
  icases Hs with ⟨%s, Hsel, %hs⟩
  ihave %hok := wcdsLookup img log a _ s $$ [Hi Hsel]
  · iframe Hi Hsel
  unfold wlatInterp wclean wcdsEl
  icases Hi with ⟨%mm, %mc, Hauth, %hag, Hc, %hagc⟩
  imod ghost_map_update WClean $$ Hc Hsel with ⟨Hc, Hsel⟩
  imodintro
  iframe Hel Hsel
  iexists mm, insert mc a WClean
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  · ipureintro
    refine wcdsAgreeInsert log mc a _ hagc ?_
    rcases hs with rfl | rfl
    · exact hok
    · exact wcdsDirtyFlipPub (imgZ img) log a c t n v hlat htn hpub hok

theorem wlatFlipPub (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (c : CPU) (a : Int)
    (t n : Nat) (v : BitVec 8) :
    t ≤ n →
    wlogAuth (GF := GF) log ∗ pubFloor c n ∗ wlatInterp img log ∗
      wlatElem a (DFrac.own 1) t v ∗ wownSt c a ⊢
      |==> (wlogAuth log ∗ wlatInterp img log ∗ wlatElem a (DFrac.own 1) t v ∗
        wclean a (DFrac.own 1)) := by
  intro htn
  iintro ⟨Hlog, #Hpf, Hi, Hel, Hs⟩
  ihave %hpub := pubFloorAgree log c n $$ [Hlog Hpf]
  · iframe Hlog Hpf
  imod wlatFlipPure img log c a t n v htn hpub $$ [Hi Hel Hs] with ⟨Hi, Hel, Hcl⟩
  · iframe Hi Hel Hs
  imodintro
  iframe Hlog Hi Hel Hcl

/-! ### 3b‴′. THE CONTEXT-INDEXED OWNED STATE (φ-upgrade §1.6)

`wownCtx ξ a t` is `wownSt`'s context-indexed successor: clean (no breadcrumb), or dirty by `c`
plus `ctxWrote ξ c (viewByte a t)`.  NOTHING HERE NAMES THE RUNNING HART; `wownCtxRetarget` is the
case analysis, inside the leaf. -/

def ctxBc (ξ : CtxId) (b : Option CPU) (a : Int) (t : Nat) : IProp GF :=
  match b with
  | none => iprop(emp)
  | some c => ctxWrote ξ c (viewByte a t)

instance ctxBc_persistent (ξ : CtxId) (b : Option CPU) (a : Int) (t : Nat) :
    Persistent (ctxBc (GF := GF) ξ b a t) := by
  cases b <;> (unfold ctxBc; infer_instance)

def wownCtx (ξ : CtxId) (a : Int) (t : Nat) : IProp GF :=
  iprop(∃ b : Option CPU, wcdsEl a (DFrac.own 1) (wcdsOb b) ∗ ctxBc ξ b a t)

instance wownCtx_timeless (ξ : CtxId) (a : Int) (t : Nat) : Timeless (wownCtx (GF := GF) ξ a t) := by
  unfold wownCtx
  refine @exists_timeless _ _ _ _ fun b => ?_
  cases b <;> (unfold ctxBc; infer_instance)

theorem wownCtxOfClean (ξ : CtxId) (a : Int) (t : Nat) :
    wclean (GF := GF) a (DFrac.own 1) ⊢ wownCtx ξ a t := by
  unfold wclean wownCtx
  iintro H
  iexists none
  simp only [wcdsOb, ctxBc]
  iframe H

theorem wownCtxOfDirty (ξ : CtxId) (c : CPU) (a : Int) (t : Nat) :
    wdirty (GF := GF) c a ∗ ctxWrote ξ c (viewByte a t) ⊢ wownCtx ξ a t := by
  unfold wdirty wownCtx
  iintro ⟨H, #Hw⟩
  iexists some c
  simp only [wcdsOb, ctxBc]
  iframe H Hw

/-- ... and the form the store rule rebuilds through. -/
theorem wownCtxOfOwnSt (ξ : CtxId) (c : CPU) (a : Int) (t : Nat) :
    wownSt (GF := GF) c a ∗ ctxWrote ξ c (viewByte a t) ⊢ wownCtx ξ a t := by
  unfold wownSt wownCtx
  iintro ⟨⟨%s, Hel, %hs⟩, #Hw⟩
  rcases hs with rfl | rfl
  · iexists none
    simp only [wcdsOb, ctxBc]
    iframe Hel
  · iexists some c
    simp only [wcdsOb, ctxBc]
    iframe Hel Hw

/-- THE RETARGET — the leaf-internal upgrade.  `logA` is the log the CALLER holds the authority
at; `pubTransfer` says the extra message publishes nothing on a foreign hart's behalf. -/
theorem wownCtxRetarget (ξ : CtxId) (c : CPU) (a : Int) (t : Nat) (v : BitVec 8)
    (img : GMapF PAddr (BitVec 8)) (log logA : List Wmsg) :
    pubTransfer logA log c →
    wlogAuth (GF := GF) logA ∗ ctxMigr ξ c ∗ wlatInterp img log ∗
      wlatElem a (DFrac.own 1) t v ∗ wownCtx ξ a t ⊢
      |==> (wlogAuth logA ∗ ctxMigr ξ c ∗ wlatInterp img log ∗
        wlatElem a (DFrac.own 1) t v ∗ wownSt c a) := by
  intro htr
  unfold wownCtx
  iintro ⟨Hlog, Hmg, Hi, Hel, ⟨%b, Hst, #Hbc⟩⟩
  cases b with
  | none =>
    simp only [wcdsOb, ctxBc]
    imodintro
    iframe Hlog Hmg Hi Hel
    iapply wcleanOwnSt c a
    unfold wclean
    iexact Hst
  | some c' =>
    simp only [wcdsOb, ctxBc]
    by_cases hce : c' = c
    · subst hce
      imodintro
      iframe Hlog Hmg Hi Hel
      iapply wdirtyOwnSt c' a
      unfold wdirty
      iexact Hst
    -- THE FOREIGN-AUTHOR ARM: the invariant supplies the coverage
    ihave #Hcov := ctxMigrPub ξ c c' (viewByte a t) hce $$ [Hmg Hbc]
    · iframe Hmg Hbc
    unfold pubCoversView
    icases Hcov with ⟨%n, #Hpf, %hn⟩
    ihave %hpubA := pubFloorAgree logA c' n $$ [Hlog Hpf]
    · iframe Hlog Hpf
    have htn : t ≤ n := by
      have := hn a
      rw [flr_byte_eq, flr_scl_eq] at this
      exact this
    imod wlatFlipPure img log c' a t n v htn (htr c' n hce hpubA) $$ [Hi Hel Hst]
      with ⟨Hi, Hel, Hcl⟩
    · iframe Hi Hel
      iapply wdirtyOwnSt c' a
      unfold wdirty
      iexact Hst
    imodintro
    iframe Hlog Hmg Hi Hel
    iapply wcleanOwnSt c a
    iexact Hcl

/-- THE φ PAYMENT OF THE SAME CASE SPLIT, with no ghost step. -/
theorem nvOkOfWownCtx (ξ : CtxId) (c : CPU) (a : Int) (t : Nat) (v : BitVec 8)
    (img : GMapF PAddr (BitVec 8)) (log logA : List Wmsg) :
    pubTransfer logA log c →
    wlogAuth (GF := GF) logA ∗ ctxMigr ξ c ∗ wlatInterp img log ∗
      wlatElem a (DFrac.own 1) t v ∗ wownCtx ξ a t ⊢ ⌜nvOk log c a⌝ := by
  intro htr
  unfold wownCtx
  iintro ⟨Hlog, Hmg, Hi, Hel, ⟨%b, Hst, #Hbc⟩⟩
  cases b with
  | none =>
    simp only [wcdsOb, ctxBc]
    iapply nvOkOfOwnSt img log c a
    iframe Hi
    iapply wcleanOwnSt c a
    unfold wclean
    iexact Hst
  | some c' =>
    simp only [wcdsOb, ctxBc]
    by_cases hce : c' = c
    · subst hce
      iapply nvOkOfOwnSt img log c' a
      iframe Hi
      iapply wdirtyOwnSt c' a
      unfold wdirty
      iexact Hst
    ihave #Hcov := ctxMigrPub ξ c c' (viewByte a t) hce $$ [Hmg Hbc]
    · iframe Hmg Hbc
    unfold pubCoversView
    icases Hcov with ⟨%n, #Hpf, %hn⟩
    ihave %hpubA := pubFloorAgree logA c' n $$ [Hlog Hpf]
    · iframe Hlog Hpf
    have htn : t ≤ n := by
      have := hn a
      rw [flr_byte_eq, flr_scl_eq] at this
      exact this
    ihave %hfree := nvFreeOfOwnPure img log c' a t n v htn (htr c' n hce hpubA) $$ [Hi Hel Hst]
    · iframe Hi Hel
      iapply wdirtyOwnSt c' a
      unfold wdirty
      iexact Hst
    ipureintro
    exact nvOkOfFree log c a hfree

/-- THE S MINT.  A byte with no owned store in the log may be turned sync once and for all. -/
theorem syncMint (img : GMapF PAddr (BitVec 8)) (log : List Wmsg) (a : Int) (s : Wcds) :
    wcdsSync log a →
    wlatInterp (GF := GF) img log ∗ wcdsEl a (DFrac.own 1) s ⊢
      |==> (wlatInterp img log ∗ syncByte a) := by
  intro hsy
  unfold wlatInterp syncByte wcdsEl
  iintro ⟨⟨%m, %mc, Hauth, %hag, Hc, %hagc⟩, Hel⟩
  imod ghost_map_update WSync $$ Hc Hel with ⟨Hc, Hel⟩
  imod ghost_map_elem_persist _ _ _ _ $$ Hel with #Hel
  imodintro
  iframe Hel
  iexists m, insert mc a WSync
  iframe Hauth Hc
  isplit
  · ipureintro; exact hag
  · ipureintro; exact wcdsAgreeInsert log mc a WSync hagc hsy

/-- At boot the log is empty, so the premise is free. -/
theorem syncMintNil (img : GMapF PAddr (BitVec 8)) (a : Int) (s : Wcds) :
    wlatInterp (GF := GF) img [] ∗ wcdsEl a (DFrac.own 1) s ⊢
      |==> (wlatInterp img [] ∗ syncByte a) :=
  syncMint img [] a s (fun p m ⟨hp, _⟩ => by simp at hp)

/-! ### 3c. the per-hart weak state -/

def wwsAuth (c : CPU) (ws : Wstate) : IProp GF :=
  ghost_var (WeakGS.wsName (GF := GF) c) (DFrac.own (1 : Qp).half) ws

def hartWs (c : CPU) (ws : Wstate) : IProp GF :=
  ghost_var (WeakGS.wsName (GF := GF) c) (DFrac.own (1 : Qp).half) ws

theorem hartWsAgree (c : CPU) (ws ws' : Wstate) :
    wwsAuth (GF := GF) c ws ∗ hartWs c ws' ⊢ ⌜ws' = ws⌝ := by
  unfold wwsAuth hartWs
  iintro ⟨Ha, Hf⟩
  ihave %h := ghost_var_agree _ _ _ _ _ $$ Ha Hf
  ipureintro
  exact h.symm

theorem hartWsUpdate (c : CPU) (ws ws' ws'' : Wstate) :
    wwsAuth (GF := GF) c ws ∗ hartWs c ws' ⊢ |==> (wwsAuth c ws'' ∗ hartWs c ws'') := by
  unfold wwsAuth hartWs
  iintro ⟨Ha, Hf⟩
  iapply ghost_var_update_halves ws'' _ ws ws' $$ Ha Hf

def wwsInterp (f : CPU → Wstate) : IProp GF :=
  iprop([∗list] c ∈ cpus, wwsAuth c (f c))

/-- Focus one hart's cell, with the handle to put an updated one back. -/
theorem wwsInterpAcc (cpu : CPU) (f : CPU → Wstate) :
    wwsInterp (GF := GF) f ⊢
      wwsAuth cpu (f cpu) ∗ ∀ ws' : Wstate, wwsAuth cpu ws' -∗ wwsInterp (updCpu f cpu ws') := by
  unfold wwsInterp
  iintro H
  icases BigSepL.bigSepL_lookup_acc_impl (Φ := fun _ c => wwsAuth (GF := GF) c (f c))
    (cpus_get? cpu) $$ H with ⟨Hc, Hclose⟩
  iframe Hc
  iintro %ws' Hc'
  iapply Hclose $$ %(fun _ c => wwsAuth (GF := GF) c (updCpu f cpu ws' c))
  · imodintro
    iintro %k %y %hk %hne Hy
    have hy : y ≠ cpu := cpus_get?_ne hk cpu hne
    simp only [gwsInsertNe f cpu y ws' hy]
    iexact Hy
  · simp only [gwsInsertEq]
    iexact Hc'

/-! ### 3c′. THE CLIENT TOKEN: `hartWs` with its value hidden. -/

def hartView (c : CPU) : IProp GF := iprop(∃ ws : Wstate, hartWs c ws)

theorem hartViewIntro (c : CPU) (ws : Wstate) : hartWs (GF := GF) c ws ⊢ hartView c := by
  unfold hartView
  iintro H
  iexists ws
  iexact H

end resources

/-! ### 3d. the state interpretations -/

/-- THE SINGLE-ERA PIN: the machine is powered on and running generation 0. -/
def wgenPin (g : WGState) : Prop := g.wgpow = true ∧ g.wggen = 0

section interp

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

/-- The GLOBAL state interpretation.  The register/device/log/latest conjuncts are the existing
tree's (`eraInterp` minus its heap), the rest are the weak-memory ones.  THE SECOND CONJUNCT is the
M2b machine invariant (`wsBounded` at every hart), THE THIRD the φ conjunct (violation-freedom). -/
def weakStateInterp (g : WGState) : IProp GF :=
  iprop(⌜wgenPin g⌝ ∗
    ⌜∀ c : CPU, wsBounded (g.wgws c) g.wglog.length⌝ ∗
    ⌜noViolation g.wglog g.wgws⌝ ∗
    ⌜wlogWf g.wglog⌝ ∗
    ([∗list] c ∈ cpus, regInterp c (g.wgregs c)) ∗
    devInterpAt (MachGS.era (hlc := hlc) (GF := GF)) g.wgdev ∗
    wlogAuth g.wglog ∗
    wlatInterp g.wgimg g.wglog ∗
    wwsInterp g.wgws)

/-- ... and ONE HART's view of it, which is what the lifting rule hands to its caller. -/
def wmstateInterp (cpu : CPU) (σ : Wmstate) : IProp GF :=
  iprop(⌜wsBounded σ.wmWs σ.wmLog.length⌝ ∗
    ⌜nvHart σ.wmLog cpu σ.wmWs⌝ ∗
    ⌜wlogWf σ.wmLog⌝ ∗
    regInterp cpu σ.wmRegs ∗
    devInterpAt (MachGS.era (hlc := hlc) (GF := GF)) σ.wmDev ∗
    wlogAuth σ.wmLog ∗
    wlatInterp σ.wmImg σ.wmLog ∗
    wwsAuth cpu σ.wmWs)

/-- THE φ EXPORT (deliverable D). -/
theorem weakStateInterpExport (g : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) g ⊢ ⌜noViolation g.wglog g.wgws⌝ := by
  unfold weakStateInterp
  iintro ⟨-, -, %h, -⟩
  ipureintro
  exact h

/-! ### 3d. T2-0's EXPORT AND ITS REGISTRATION SEAM

The lock word's value protocol is read off the C/D/S auth against the client's own `WLock`
fragment, which lives inside the lock's namespace invariant; what crosses to the adequacy seam is
`wlockRegd`: the PERSISTENT invariant assertion plus an accessor. -/

def wlockRegd (N : Namespace) (a base : Int) : IProp GF :=
  iprop(∃ I : IProp GF, inv N I ∗
    □ (I -∗ ∃ (n0 : Nat) (h : Option Nat), wlockSt a base n0 h ∗ (wlockSt a base n0 h -∗ I)))

instance wlockRegd_persistent (N : Namespace) (a base : Int) :
    Persistent (wlockRegd (hlc := hlc) (GF := GF) N a base) := by
  unfold wlockRegd; infer_instance

theorem WeakGhost.weakStateInterpLat (g : WGState) :
    weakStateInterp (hlc := hlc) (GF := GF) g ⊢ wlatInterp g.wgimg g.wglog := by
  unfold weakStateInterp
  iintro ⟨-, -, -, -, -, -, -, H, -⟩
  iexact H

/-- THE PER-STATE EXPORT, off a fragment in hand. -/
theorem weakStateInterpLockproto (g : WGState) (a base : Int) (n0 : Nat) (h : Option Nat) :
    weakStateInterp (hlc := hlc) (GF := GF) g ∗ wlockSt a base n0 h ⊢
      ⌜wlpAt g.wglog a base n0⌝ := by
  iintro ⟨Hi, He⟩
  ihave Hlat := WeakGhost.weakStateInterpLat g $$ Hi
  iapply wlpAtOfLock g.wgimg g.wglog a base n0 h
  iframe Hlat He

/-- ... and THROUGH THE SEAM, in one fancy update at a mask containing the lock's namespace. -/
theorem wlockRegdExportAlt (N : Namespace) (E : CoPset) (g : WGState) (a base : Int) :
    ↑N ⊆ E →
    weakStateInterp (hlc := hlc) (GF := GF) g ∗ wlockRegd N a base ⊢
      |={E}=> ⌜∃ (n0 : Nat) (h : Option Nat),
        wlpAt g.wglog a base n0 ∧ wlpAlt g.wglog a n0 h⌝ := by
  intro hN
  iintro ⟨Hsi, #Hreg⟩
  ihave Hlat := WeakGhost.weakStateInterpLat g $$ Hsi
  unfold wlockRegd
  icases Hreg with ⟨%I, #Hinv, #Hacc⟩
  iinv Hinv with HI Hclose
  ihave HQ : ▷ (∃ (n0 : Nat) (h : Option Nat),
      wlockSt (GF := GF) a base n0 h ∗ (wlockSt a base n0 h -∗ I)) $$ [HI]
  · imodintro
    iapply Hacc $$ HI
  icases later_exists.mpr $$ HQ with ⟨%n0, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%h, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hst, Hback⟩
  ihave %hlp := wlpAtOfLock g.wgimg g.wglog a base n0 h $$ [Hlat Hst]
  · iframe Hlat Hst
  ihave %halt := wlpAltOfLock g.wgimg g.wglog a base n0 h $$ [Hlat Hst]
  · iframe Hlat Hst
  imod Hclose $$ [Hst Hback]
  · imodintro
    iapply Hback $$ Hst
  imodintro
  ipureintro
  exact ⟨n0, h, hlp, halt⟩

theorem wlockRegdExport (N : Namespace) (E : CoPset) (g : WGState) (a base : Int) :
    ↑N ⊆ E →
    weakStateInterp (hlc := hlc) (GF := GF) g ∗ wlockRegd N a base ⊢
      |={E}=> ⌜∃ n0 : Nat, wlpAt g.wglog a base n0⌝ := by
  intro hN
  iintro H
  imod wlockRegdExportAlt N E g a base hN $$ H with %⟨n0, h, hlp, _⟩
  imodintro
  ipureintro
  exact ⟨n0, hlp⟩

/-! ### 3d′. F3″'s EXPORT AND ITS SEAM — THE PROTECTED-BYTE FOOTPRINT

What travels to the adequacy seam is an invariant whose body holds BOTH the byte's `WProt`
fragment AND the lock word's own `WLock` fragment — AT THE SAME REGISTRATION POINT `n0`. -/

def wprotRegd (N : Namespace) (a base : Int) : IProp GF :=
  iprop(∃ I : IProp GF, inv N I ∗
    □ (I -∗ ∃ (γ : GName) (n0 r0 : Nat) (d : Option CPU) (h : Option Nat),
      wprotSt a γ base n0 r0 d ∗ wlockSt base base n0 h ∗
      (wprotSt a γ base n0 r0 d -∗ wlockSt base base n0 h -∗ I)))

instance wprotRegd_persistent (N : Namespace) (a base : Int) :
    Persistent (wprotRegd (hlc := hlc) (GF := GF) N a base) := by
  unfold wprotRegd; infer_instance

/-- THE PER-STATE EXPORT, off the fragments in hand. -/
theorem weakStateInterpProt (g : WGState) (a base : Int) (γ : GName) (n0 r0 : Nat)
    (d : Option CPU) :
    weakStateInterp (hlc := hlc) (GF := GF) g ∗ wprotSt a γ base n0 r0 d ⊢
      ⌜wprotAt g.wglog a base n0 r0⌝ := by
  iintro ⟨Hi, He⟩
  ihave Hlat := WeakGhost.weakStateInterpLat g $$ Hi
  iapply wprotAtOfProt g.wgimg g.wglog a γ base n0 r0 d
  iframe Hlat He

/-- ... and THROUGH THE SEAM: all three conclusions share the registration point `n0`. -/
theorem wprotRegdExport (N : Namespace) (E : CoPset) (g : WGState) (a base : Int) :
    ↑N ⊆ E →
    weakStateInterp (hlc := hlc) (GF := GF) g ∗ wprotRegd N a base ⊢
      |={E}=> ⌜∃ (γ : GName) (n0 r0 : Nat) (h : Option Nat),
        wprotAt g.wglog a base n0 r0 ∧
        wlpAt g.wglog base base n0 ∧ wlpAlt g.wglog base n0 h⌝ := by
  intro hN
  iintro ⟨Hsi, #Hreg⟩
  ihave Hlat := WeakGhost.weakStateInterpLat g $$ Hsi
  unfold wprotRegd
  icases Hreg with ⟨%I, #Hinv, #Hacc⟩
  iinv Hinv with HI Hclose
  ihave HQ : ▷ (∃ (γ : GName) (n0 r0 : Nat) (d : Option CPU) (h : Option Nat),
      wprotSt (GF := GF) a γ base n0 r0 d ∗ wlockSt base base n0 h ∗
      (wprotSt a γ base n0 r0 d -∗ wlockSt base base n0 h -∗ I)) $$ [HI]
  · imodintro
    iapply Hacc $$ HI
  icases later_exists.mpr $$ HQ with ⟨%γ, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%n0, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%r0, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%d, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%h, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hpr, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hlk, Hback⟩
  ihave %hpa := wprotAtOfProt g.wgimg g.wglog a γ base n0 r0 d $$ [Hlat Hpr]
  · iframe Hlat Hpr
  ihave %hlp := wlpAtOfLock g.wgimg g.wglog base base n0 h $$ [Hlat Hlk]
  · iframe Hlat Hlk
  ihave %halt := wlpAltOfLock g.wgimg g.wglog base base n0 h $$ [Hlat Hlk]
  · iframe Hlat Hlk
  imod Hclose $$ [Hpr Hlk Hback]
  · imodintro
    iapply Hback $$ Hpr Hlk
  imodintro
  ipureintro
  exact ⟨γ, n0, r0, h, hpa, hlp, halt⟩

/-! ### 3d″. THE READ RECORDS

The protected LOAD rule is the ordinary load plus a persistent record; the mint's side condition
(the position is at or after the footprint's registration point) is the invariant the auth
carries. -/

section records

variable [WprotG GF]

def protRecs (γr : GName) (L : List (Int × Nat)) : IProp GF :=
  MonoList.auth_own γr (DFrac.own 1) L

def protRead (γr : GName) (a : Int) (p : Nat) : IProp GF :=
  iprop(∃ L : List (Int × Nat), MonoList.lb_own γr L ∗ ⌜(a, p) ∈ L⌝)

instance protRead_persistent (γr : GName) (a : Int) (p : Nat) :
    Persistent (protRead (GF := GF) γr a p) := by
  unfold protRead; infer_instance

instance protRecs_timeless (γr : GName) (L : List (Int × Nat)) :
    Timeless (protRecs (GF := GF) γr L) := by
  unfold protRecs; infer_instance

/-- The list's own well-formedness: every record sits at or after the registration point. -/
def protRecsOk (r0 : Nat) (L : List (Int × Nat)) : Prop :=
  ∀ ap, ap ∈ L → r0 ≤ ap.2

theorem protRecsAlloc : ⊢ |==> ∃ γr : GName, protRecs (GF := GF) γr [] := by
  unfold protRecs
  imod MonoList.own_alloc (GF := GF) ([] : List (Int × Nat)) with ⟨%γr, Ha, -⟩
  imodintro
  iexists γr
  iexact Ha

/-- THE MINT, at a load site: append the record and keep a persistent copy of it. -/
theorem protRecsAppend (γr : GName) (L : List (Int × Nat)) (a : Int) (p : Nat) :
    protRecs (GF := GF) γr L ⊢ |==> (protRecs γr (L ++ [(a, p)]) ∗ protRead γr a p) := by
  unfold protRecs protRead
  iintro Ha
  imod MonoList.auth_own_update_app _ [(a, p)] $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  iframe Ha
  iexists L ++ [(a, p)]
  iframe Hlb
  ipureintro
  exact List.mem_append_right _ (List.mem_singleton.2 rfl)

theorem protReadAgree (γr : GName) (L : List (Int × Nat)) (a : Int) (p : Nat) :
    protRecs (GF := GF) γr L ∗ protRead γr a p ⊢ ⌜(a, p) ∈ L⌝ := by
  unfold protRecs protRead
  iintro ⟨Ha, ⟨%L', Hf, %hin⟩⟩
  icases MonoList.auth_lb_own_valid _ _ _ _ $$ Ha Hf with %⟨_, hpre⟩
  ipureintro
  exact elem_of_prefix hin hpre

/-- THE SEAM, `wprotRegd` plus the record authority. -/
def wprotRdRegd (N : Namespace) (γr : GName) (a base : Int) : IProp GF :=
  iprop(∃ I : IProp GF, inv N I ∗
    □ (I -∗ ∃ (γ : GName) (n0 r0 : Nat) (d : Option CPU) (h : Option Nat) (L : List (Int × Nat)),
      wprotSt a γ base n0 r0 d ∗ wlockSt base base n0 h ∗
      protRecs γr L ∗ ⌜protRecsOk r0 L⌝ ∗
      (wprotSt a γ base n0 r0 d -∗ wlockSt base base n0 h -∗ protRecs γr L -∗ I)))

instance wprotRdRegd_persistent (N : Namespace) (γr : GName) (a base : Int) :
    Persistent (wprotRdRegd (hlc := hlc) (GF := GF) N γr a base) := by
  unfold wprotRdRegd; infer_instance

theorem wprotRdRegdExport (N : Namespace) (E : CoPset) (g : WGState) (γr : GName) (a base : Int)
    (p : Nat) :
    ↑N ⊆ E →
    weakStateInterp (hlc := hlc) (GF := GF) g ∗ wprotRdRegd N γr a base ∗ protRead γr a p ⊢
      |={E}=> ⌜∃ (γ : GName) (n0 r0 : Nat) (h : Option Nat),
        r0 ≤ p ∧ wprotAt g.wglog a base n0 r0 ∧
        wlpAt g.wglog base base n0 ∧ wlpAlt g.wglog base n0 h⌝ := by
  intro hN
  iintro ⟨Hsi, #Hreg, #Hrd⟩
  ihave Hlat := WeakGhost.weakStateInterpLat g $$ Hsi
  unfold wprotRdRegd
  icases Hreg with ⟨%I, #Hinv, #Hacc⟩
  iinv Hinv with HI Hclose
  ihave HQ : ▷ (∃ (γ : GName) (n0 r0 : Nat) (d : Option CPU) (h : Option Nat)
      (L : List (Int × Nat)),
      wprotSt (GF := GF) a γ base n0 r0 d ∗ wlockSt base base n0 h ∗
      protRecs γr L ∗ ⌜protRecsOk r0 L⌝ ∗
      (wprotSt a γ base n0 r0 d -∗ wlockSt base base n0 h -∗ protRecs γr L -∗ I)) $$ [HI]
  · imodintro
    iapply Hacc $$ HI
  icases later_exists.mpr $$ HQ with ⟨%γ, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%n0, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%r0, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%d, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%h, HQ⟩
  icases later_exists.mpr $$ HQ with ⟨%L, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hpr, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hlk, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>Hrecs, HQ⟩
  icases later_sep.mp $$ HQ with ⟨>%hok, Hback⟩
  ihave %hpa := wprotAtOfProt g.wgimg g.wglog a γ base n0 r0 d $$ [Hlat Hpr]
  · iframe Hlat Hpr
  ihave %hlp := wlpAtOfLock g.wgimg g.wglog base base n0 h $$ [Hlat Hlk]
  · iframe Hlat Hlk
  ihave %halt := wlpAltOfLock g.wgimg g.wglog base base n0 h $$ [Hlat Hlk]
  · iframe Hlat Hlk
  ihave %hin := protReadAgree γr L a p $$ [Hrecs Hrd]
  · iframe Hrecs Hrd
  imod Hclose $$ [Hpr Hlk Hrecs Hback]
  · imodintro
    iapply Hback $$ Hpr Hlk Hrecs
  imodintro
  ipureintro
  exact ⟨γ, n0, r0, h, hok (a, p) hin, hpa, hlp, halt⟩

end records

/-! ## 9. The `IrisGS` instance

`stateInterp` ignores its step/observation/fork counters and `numLatersPerStep` is 0, exactly as
`MachCSL.instIrisGS`. -/

/-- The weak state interpretation as the language's `StateInterp` (deviation 11). -/
instance weakStateInterpInst : StateInterp WGState Empty GF where
  stateInterp g _ _ _ := weakStateInterp (hlc := hlc) g

/-- Rocq `weak_irisGS`. -/
instance weakIrisGS : IrisGS_gen hlc WExpr GF where
  invGS := MachFixedGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := @MachFixedGS.invGS hlc GF _
    iintro $

/-! ## 10. The Φ-free weak WP

`toVal` is unconditionally `none` (the value type is `Empty`), so a WP never inspects its
postcondition.  THE NOTATION IS `WWP`, NOT `WP`, DELIBERATELY: a distinct token makes the language
visible at every use site. -/

theorem wwpPostIrrel (s : Stuckness) (E : CoPset) (e : WExpr) (Φ1 Φ2 : Empty → IProp GF) :
    WP e @ s ; E {{ Φ1 }} ⊢ WP e @ s ; E {{ Φ2 }} :=
  wp_mono (fun v => nomatch v)

def wwpTriv (E : CoPset) (e : WExpr) : IProp GF :=
  WP e @ Stuckness.NotStuck ; E {{ fun _ => iprop(True) }}

theorem wwpTrivEq (E : CoPset) (e : WExpr) (Φ : Empty → IProp GF) :
    wwpTriv (hlc := hlc) (GF := GF) E e ⊣⊢ WP e @ Stuckness.NotStuck ; E {{ Φ }} :=
  ⟨wwpPostIrrel _ _ _ _ _, wwpPostIrrel _ _ _ _ _⟩

end interp

notation:20 "WWP " e:20 " @ " E:20 => wwpTriv E e
notation:20 "WWP " e:20 => wwpTriv ⊤ e

end Weak
