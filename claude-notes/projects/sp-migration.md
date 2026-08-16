# Project: sp-migration — owning memory at a NON-IDENTITY kernel va

The gate on the process kernel stack (`proc-struct-resources.md`: a slot cannot
own its stack, so a fresh process cannot be parked without an unpayable
premise). A KSTACK va is not identity-mapped, and nothing in the tree can own
a byte there.

## Where the identity requirement lived

A conjunct of the datum:

```coq
Definition mem_pointsto va dq v :=
  ∃ ppn, kmap_at (svpn_of va) ppn KP_rw ∗ ⌜canonical⌝ ∗ ⌜addr_is_ram (pa_of ppn va)⌝ ∗
         ⌜pa_of ppn va = va⌝ ∗                (* ← THIS *)
         pointsto (pa_of ppn va) dq v
```

`⌜pa_of ppn va = va⌝` serves exactly one proof obligation, in exactly one
place, and it is the reason `stack_own` at a KSTACK va is unsatisfiable —
which is what made the boot-deposit experiment VACUOUSLY TRUE
(`proc-struct-resources.md`).

## What `sr_adm` is, and who needs it

`SRegime.s_regime`'s `sr_absorb` must prove

```coq
exec (translateAddr (Virtaddr va) acc) σ = Some (Ok (Physaddr pa, …), σ')
```

where `pa` is fixed by the caller as `pa_of ppn va` — the address the CLAIM
says `va` maps to. Each regime reconciles that with the hardware:

- **Sv39/KPT** (`res_absorb`, `kpt_share_regime`): the walk returns
  `pa_of ppn va`, because `kmap_at` is a fragment of the very map that table
  represents. `sr_adm := fun _ _ => True`.
- **Bare** (`bare_absorb`): the hardware returns **`va` itself**
  (`exec_translateAddr_bare`). The whole use of the premise is two lines:
  `assert (Hpa : pa = va). { rewrite <- Hconcat. exact Hadm. }`.
  `sr_adm := kadm_ident`. (`bare_regime` itself is DEAD CODE — defined at
  `SRegime.v:395`, instantiated nowhere.)
- **`strans_regime`** (`IntrDefs.v:1270`, what the whole sconf tier runs at):
  `sr_inv := strans_inv` is the DISJUNCTION `Bare ∨ KPT`, so its `sr_adm` must
  be the weaker arm's — `kadm_ident`. `strans_absorb` case-splits and hands
  `Hadm` to `bare_absorb` on the left, `I` to `res_absorb` on the right.

So `sr_adm` is **the Bare arm's reconciliation, and nothing else**. Baking it
into `↦ₘ` made every kernel datum in the tree carry a fact that exists only to
serve S-mode code running with translation off.

## THE SEMANTIC FACT everything below is constrained by

In Bare mode the CPU reads physical `va`; the datum owns physical
`pa_of ppn va`. So:

- **Bare + non-static va — UNSOUND.** No restructuring changes this.
- **Bare + statically classified va — provable with NO auth and NO
  exclusivity**, from the ambient persistent bundle alone:
  `kmap_static_claims_at` gives `kmap_at vpn (kpt_leaf_ppn vpn) pc`,
  `kmap_at_agree` forces the datum's existential `ppn` to match, `pa_of_id`
  finishes. `KMap.mem_ident_phys` already performs exactly this dance.

So the ONLY open question is: **how does the leaf learn
`kmap_static (svpn_of va) KP_rw`?** There are exactly three possible sources —
a caller premise, the datum, or the regime — and the three dead ends below are
what happens when you pick the wrong one.

## DEAD END 1 — "in Bare mode only identity claims exist"

It WAS the old mechanism (`KMap.kmap_at_M0_static`: against the exact static
auth `kmap_M0`, a claim's ppn IS `kpt_leaf_ppn vpn`). Not sound any more:

- `kmap_name` is **global** (`era_kmap_name`) and the map is **monotone** —
  `kvminithart` mints the 65 non-identity claims (trampoline + 64 kstacks) and
  they are persistent.
- `strans_name : CPU -> gname` is **per-hart**. Bare-ness is one hart's satp.

The moment any hart runs `kvminithart`, non-identity claims exist globally
while other harts are legitimately still Bare.

## DEAD END 2 — a pure premise `sr_va_ok R va` on the leaf

Two things wrong, the first explaining the second:

- **The leaf's `pa` is a VIRTUAL address.** `WpSconfMem.v:242`:
  `let pa := add_vec (rget m rs1) (sign_extend' 64 imm)` — the effective
  address, pre-translation; `pa_of ppn pa` is formed separately for the
  physical one. The name is simply wrong at this altitude and should be fixed
  while the family is being touched.
- **A caller cannot discharge it.** It holds a datum; it does not know, and
  must not have to know, whether its address is identity-mapped. The premise
  would propagate through `acquire`, `printk`, `memset`, … to hundreds of
  sites where the address is abstract.

## DEAD END 3 — `kmap_auth kmap_M0` in the Bare arm of the capability

The idea: `s_regime` gains `sr_okmap : iProp` (Bare: `kmap_auth kmap_M0`;
KPT: `emp`) living inside `sr_inv`, so `kmap_at_M0_static` discharges
admissibility with no knowledge of the address and no caller-facing premise.

**KILLED by the secondary harts.** The auth is exclusive and is spent at the
table publication in `ProofMain.mn_grp_kvm`; hart 0 sets `started = 1` only
AFTER its own `kvminithart`. So by the time any secondary leaves the spin
loop, the map is already extended and no secondary can hold the auth — and a
secondary's Bare window is not a couple of literal-address loads. Per
`ProofMainSecondary.v`:

```
ms_spin            0x16 -> 0x20   iLöb spin on [started]
ms_printk          0x20 -> 0x32   jal cpuid; printk("hart %d starting\n")
ms_inithart_sched  0x32 -> …      kvminithart trapinithart plicinithart
```

i.e. **the entire printk / console / uart / lock cone runs in Bare mode on
every secondary hart**, at abstract addresses, with the extended map live and
no auth in hand. Any design that leans on hart 0's boot window is dead on
arrival.

## DEAD END 4 — `MemAcc` keyed on the REGIME RECORD (the first "surviving
## shape", superseded 2026-08-16)

The idea: make the leaf family polymorphic in the datum with a typeclass
`MemAcc (R : s_regime) D`, two datum tiers (`↦ₘˢ` static / `↦ₘ` general),
and let INSTANCE EXISTENCE do the gating — "a KSTACK datum simply has no
instance at a Bare regime".

**THE GAP: the whole sconf tier — post-boot included — runs at
`strans_regime`** (`IntrDefs.v:1270`, `sr_adm = kadm_ident`). Boot and
post-boot code hold the SAME folded slot; a typeclass keyed on the regime
record cannot tell them apart. So the general tier has no instance at
`strans_regime` either, and post-boot KSTACK access is unprovable everywhere
in the sconf tier — which defeats the project's goal (usertrap/swtch-adjacent
code driving `stack_own` at KSTACK). The discriminator between "Bare-capable"
and "KPT-only" access cannot be the regime INSTANCE; it must be a RESOURCE
(the per-hart KPT receipt), which is state-dependent and per-hart.

Also checked and rejected: have a post-boot caller UPGRADE the slot to
`kpt_share_regime` for a call's duration via `strans_inv_acc_kpt`. Dies on
the trap contract — the sie_cap/interrupt fixpoint is stated over the fixed
folded bundle, and a trap arriving mid-call needs the slot in that shape.

Two more shapes rejected on principle, recorded so they stay dead:

- **Possession-gating** ("you may not HOLD a KPT fact on a Bare hart"):
  facts flow through lock invariants and the proc table to harts in the
  other regime (kalloc during boot; hart 0 scheduling on KSTACK while a
  secondary still spins Bare). Possession must be free; USE is gated.
- **A global phase/escrow barrier** ("all harts KPT ⇒ KSTACK facts
  unlock"): wrong granularity. Usability is genuinely per-(fact, hart) —
  hart 0 legitimately uses KSTACK data while hart 2 is still Bare.
- **Hart-indexed usability baked into the datum** (`↦ₘ@c` with the witness
  inside): a kstack fact parked in a proc slot resumes on another hart with
  a stale `c` — the exact modularity failure the weak-memory branch
  machine-checked (`weak-memory-sc-parity.md` §9). Facts must stay
  hart-free; the per-hart part lives only in leaf premises where `cpu_id`
  is ambient and re-bound at `wp_next`.

## THE SETTLED DESIGN (2026-08-16): ktier-indexed datum + capability-
## carried witness + `KtierLe` inference

The structure the problem forces: the per-hart translation regime is a
MONOTONE two-point quantity (Bare→KPT, once per era — kexec starts a new
era with fresh `era_strans_name`/`era_kmap_name`, so within-era persistence
is safe), and each datum carries a PURE LOWER BOUND against it. Access =
"datum's bound ≤ hart's generation". This is the weak-memory view pattern
(monotone per-hart state, bound-in-the-fact per sc-parity §3a, witness
re-supplied at migration) — but WITHOUT the WeakCtx machinery, because here
the bounds are GLOBAL persistent facts (`kmap_at` fragments + a pure class
conjunct), not hart-relative views, so lock transfer needs no re-indexing
and no context object. Adopt the pattern, not the machinery.

### 1. The datum: `va ↦ₘ[kt] v`, kt ∈ {KT0, KT1}

- `↦ₘ[KT1]` — EXACTLY the identity-free definition now on the RED branch
  (`RiscvPtsto.v:925`).
- `↦ₘ[KT0]` — the same PLUS the pure conjunct
  `⌜ppn = kpt_leaf_ppn (svpn_of va) /\ kmap_static (svpn_of va) KP_rw⌝`
  (the PINNED form: it names the existential ppn, so a destructor gets the
  identity by `pa_of_id` alone, with NO ambient bundle needed — today's
  `%Hid` destructors change one line).  Constructors get the pin from
  `kmap_static_claims_at` + `kmap_at_agree` (the bundle is ambient in
  `hw_config`), exactly as `phys_ident_mem` already does; adequacy mints
  from `kmap_M0`, which is static by definition.
- Weakening `↦ₘ[KT0] ⊢ ↦ₘ[KT1]`; strengthening is recoverable because the
  tier conjunct is PURE (`mem_gen_strengthen : ⌜kmap_static …⌝ -∗ ↦ₘ[g] ⊢
  ↦ₘ[KT0]`) — extract the class fact before weakening, reapply after. Both
  are fallbacks; the tier-preserving leaf rule (§4) makes them rare.
- The towers (`↦₂/₄/₈`, `word_pointsto`, `str_bytes`, `stack_own`) inherit
  the index through notation (§6).
- `text_pointsto` (`↦ₓ`, TRAMPOLINE) is the same shape with the same index
  and witness; it lands SECOND — the fetch path is untouched today.

### 2. The witness: `strans_bit` ghost_var → ONESHOT; `kpt_on c` persistent

Refactor `strans_bit` (`IntrDefs.v:820`, `ghost_var (strans_name cpu_id)
(1/2)`) to a oneshot: the Bare arm of `strans_inv` holds `pending` (half),
the boot receipt is the other pending half, the kvminithart flip combines
and SHOOTS, and the shot — `kpt_on c` — is PERSISTENT. Everything the bit
does survives: `strans_inv_acc_bare`/`_acc_kpt` pin arms by pending/shot
CONFLICT instead of ghost_var agreement; the flip is the shoot. The
`trap_csrs` receipt member ("THE KPT RECEIPT", `IntrDefs.v:800-821`)
becomes a persistent conjunct — strictly more convenient for usertrapret's
satp read (no exclusive half to thread). Nothing needs post-flip
exclusivity, only pending exclusivity, which the oneshot preserves.

### 3. The regime record: `sr_kwit` + `sr_absorb_wit`

`s_regime` keeps `sr_adm`/`sr_adm_id` (the KT0 path) and gains:

```coq
sr_kwit : iProp Σ;               (* persistent: this regime honors ALL claims *)
sr_kwit_pers : Persistent sr_kwit;
sr_absorb_wit : … ⊢ sr_kwit -∗ kmap_at (svpn_of va) ppn pc -∗ …
                  (* same conclusion as sr_absorb, NO sr_adm premise *)
```

Instances: `bare_regime` → `False` (Bare+non-identity is unsound: the
witness is unsatisfiable, not the obligation unpayable); `kpt_share_regime`
→ `emp` (`res_absorb` with `I`); `strans_regime` → `kpt_on cpu_id`
(`SRegimeDef` already has `CID : CpuId` in context, `SRegime.v:192`) —
`strans_absorb_wit` case-splits the slot: Bare arm's pending × shot =
contradiction, KPT arm delegates to `res_absorb`.

### 4. The leaf rule: tier-preserving, heterogeneous, `KtierLe`-inferred

```coq
Class KtierLe (t1 t2 : ktier) : Prop := ktier_le : …
Instance ktier_le_bot t  : KtierLe KT0 t.   (* static usable everywhere *)
Instance ktier_le_top t  : KtierLe t KT1.   (* a KPT hart honors every claim *)
Instance ktier_le_refl t : KtierLe t t.    (* spec arg riding the ambient tier *)

Lemma wp_load_byte g g' `{!KtierLe g' g} … :
  ktier_wit g -∗ va ↦ₘ[g'] v -∗ … (va ↦ₘ[g'] v -∗ …) -∗ …
```

KT0 datum → identity derived internally, absorb via `sr_adm`/`sr_adm_id`
(this arm is where the ~14 RED `%Hid` sites land, patched ONCE); KT1 datum →
`KtierLe` forces `g = KT1`, absorb via `sr_absorb_wit`. THE DATUM COMES BACK AT
ITS OWN TIER — a KT0 fact stays KT0 through any number of accesses, so
re-deposit into a KT0-stated invariant (kfree → freelist) needs no
strengthening dance. Instance-set facts: the goal shapes that arise are
`KtierLe g g` (refl), `KtierLe KT0 g` (bot), `KtierLe g KT1` (top); all heads are
premise-free, so no TC search divergence; closed-corner overlap
(`KtierLe KT0 KT1` matches two) is benign for a Prop class. `KtierLe g1 g2` for
two UNRELATED variables is correctly unprovable (false at KT1,KT0) — the
caller must pin or weaken. **The set {bot, top, refl} is complete FOR THE
TWO-POINT LATTICE ONLY**; if the lattice ever grows (kexec era index was
the candidate), switch to a decision-procedure instance or Hint Extern.

### 5. Witness delivery: the CAPABILITY is ktier-indexed; nothing new is threaded

`sie_cap g m avail b p` carries one persistent conjunct `ktier_wit g`
(`ktier_wit KT0 = emp`, `ktier_wit KT1 = kpt_on cpu_id`). The SIE='1' arm PINS
`g = KT1` internally (it owns `intr_res`, post-trapinithart only — this is
the existing "interrupts enabled ⟹ KPT" invariant, `IntrDefs.v:809-816`,
promoted to an index), so the Banach trap fixpoint stays at KT1 unindexed;
only the SIE=0 capability form is g-polymorphic. Boot's capability is built
at KT0 (`sie_cap_intro_bare`); kvminithart upgrades it once
(`sie_cap_ktier_up : sie_cap KT0 … -∗ kpt_on -∗ sie_cap KT1 …`, minting
`kpt_on` at the flip — it owns the slot mid-switch). Interrupts-off code
needs no SIE-based deduction: the capability it already holds WAS BUILT at
a generation and carries the witness. Leaves get `ktier_wit` through the
engine plumbing that already destructures the capability to feed `sr_inv`.
NO function spec grows an `sr_ktier_ok`-style premise.

### 6. Notation: ambient `CurKtier` (the weak-memory Stage-1.7 trick)

```coq
Class CurKtier := cur_ktier : ktier.
Notation "a ↦ₘ v" := (mem_pointsto cur_ktier a … v).  (* + towers, sie_cap *)
```

Per-file deltas — this is the whole answer to "how wide is the cone":

- POST-BOOT-ONLY files (the fs tier, proc, pipe — the bulk):
  `Local Instance : CurKtier := KT1.` Spec/proof text otherwise UNCHANGED —
  `↦ₘ` elaborates to `↦ₘ[KT1]`, the RED-branch definition those proofs
  already use.
- BOOT-ONLY files (ProofMain, ProofMainSecondary, kvminit):
  `Local Instance : CurKtier := KT0.`
- THE DUAL-REGIME CONE (printk/printf, console, uart, string/memmove/
  memset, acquire/release, kalloc): section binder `` `{GEN : CurKtier} `` —
  the ∀g is the section variable; statements keep their spelling. Only
  genuinely mixed-tier ARGUMENTS name an explicit `[g_i]` with a `KtierLe`
  premise, e.g. printk with per-`%s` tiers:

  ```coq
  Lemma printk_spec g gf g1 `{!KtierLe gf g, !KtierLe g1 g} … :
    { sie_cap g … ∗ stack_own[g] sp n ∗ str_bytes[gf] fmt ∗ str_bytes[g1] s1 }
      printk  { …same back, same tiers… }
  ```

  ONE proof; each region independently KT0 or KT1; a boot caller instantiates
  everything at KT0 (all premises trivial); a post-boot caller sets g := KT1
  and mixes freely (top/bot instances). The stack rides the capability's g
  — boot stack0 is KT0 with the KT0 cap, kstack is KT1 with the KT1 cap; they
  genuinely co-vary, so this is not a restriction.
- DISCIPLINE, inherited verbatim from the CurCtx scar tissue on the
  weak-memory branch: `Typeclasses Opaque cur_ktier`; NAMED section binders
  (anonymous instances auto-name `H` and collide with `iIntros "%H"`); the
  boot↔post-boot SEAM proofs (kvminithart above all, scheduler entry) have
  two generations in scope and must spell `[KT0]`/`[KT1]` explicitly — with
  two `CurKtier` instances in scope, resolution silently takes the
  last-declared one.

### 7. Locks: NOTHING changes in the lock library

A lock invariant's payload spells its tier EXPLICITLY, never `cur_ktier` (an
invariant is shared across harts in different regimes; an ambient tier
would let a KT1-ambient depositor violate what a KT0 acquirer needs). That is
the whole per-lock story: an annotation on the PAYLOAD PROPOSITION, chosen
once per lock — kalloc/console/uart at KT0 (true: their data is static RAM /
.data), fs locks at whatever is true of their data. `is_lock`/`acquire`/
`release` are untouched; a Bare hart may acquire ANY lock (the lock word is
static = KT0); if the payload hands it KT1 facts it can hold, pass, and
re-deposit them — it just cannot drive leaves with them, for want of
`kpt_on`. Unsoundness is structurally unreachable, not prohibited by a side
condition. kalloc end-to-end: freelist stated at KT0; kinit/kvminit (Bare)
deposit and use at KT0; post-boot callers get KT0 pages, use them directly at
ambient KT1 (bot instance, tier preserved), kfree re-deposits at KT0; the ↦ₚ
conversion for PT nodes gets its static-class premise FROM the KT0 datum
(cleaner than today's separate `page_in_range_addr_is_kdata` threading).

The depositor obligation — "deposit at the tier the invariant states" — is
discharged for kfree by the page-class facts its spec already carries.

### 8. Relation to weak memory: shared PATTERN, deferred MERGE

Correspondence (why the intuition fired): per-hart monotone quantity
(view / generation), per-fact lower bound carried INSIDE the points-to
(sc-parity §3a), witness re-supplied at every migration target by the
scheduling protocol (new-CPU fence floor / `kpt_on CID'` in the `wp_next`
resume bundle). Divergence (why NOT to import WeakCtx): weak-memory bounds
are HART-RELATIVE, so facts crossing a lock must be re-based (wobj, ξ_L,
CtxMorph); generation bounds are GLOBAL PERSISTENT facts, so they cross any
container unchanged and no context object is needed. Merge point when the
WM port lands: Stage-1.8 `ctx_own ξ`'s ledger clause (i) gains a generation
component ("ξ's generation bound ≤ this hart's generation"), and `ktier_wit`
is discharged from `wrunning ξ` instead of the capability — specs written
against §4-§6 simplify rather than change shape. To keep that merge
mechanical: keep `ktier` a dedicated lattice type (not bool), keep the
witness behind the capability interface, and NEVER let `kpt_on` leak into a
datum definition.

### 9. Implementation order

1. Oneshot refactor of `strans_bit` (§2) — self-contained, check every
   consumer (two accessors, flip, trap_csrs, sie_cap arms).
2. `sr_kwit`/`sr_absorb_wit` on the record + the three instances (§3).
3. ktier-indexed datum + `KtierLe` + the tier-preserving leaf rules (§1, §4),
   patching the ~14 RED `%Hid` sites into the KT0 arm.
4. `sie_cap` index + `ktier_wit` + `sie_cap_ktier_up` at kvminithart (§5).
5. `CurKtier` class/notation + the per-file sweep (§6); lock payloads pinned
   explicitly (§7).
6. While the family is open: fix the mis-named `pa` binder at
   `WpSconfMem.v:242` (DEAD END 2's finding).
7. LATER, same shape: `text_pointsto`/TRAMPOLINE.

The old fallback (move the secondary's `printk("hart %d starting\n")` after
`kvminithart()` to shrink the Bare cone) is NO LONGER NEEDED — under §6 the
"cone" question is moot (post-boot files are textually unchanged; the
dual-regime cone pays one section binder). Kept here only as history.

## Implementation campaign (worklist)

Orchestrated: a coordinator agent owns design coherence; Opus/Sonnet
subagents execute. Builds run on the GCP VM (`remote-build-gcp.md`) —
a full clean build is ~6 min there, so even the IntrDefs/SmodeCore cone
is cheap to validate. One code agent at a time in this checkout (shared-
tree discipline, `durable-notes.md`); agents leave edits uncommitted and
the coordinator reviews and commits.

Landing strategy — the key observation making phases A–C individually
green: TODAY every `↦ₘ` in the tree is at a statically-classified address
(KSTACK is unownable — that is the project's premise), so the whole tree
starts at KT0, which is true and closest to the current semantics.
`CurKtier` gets a LOW-PRIORITY GLOBAL DEFAULT instance `KT0` in RiscvPtsto
(a recorded deviation from the WM CurCtx zero-instances discipline): the
~424 use-only consumer files then compile UNCHANGED — no pinning sweep
exists at all — and a post-boot file adds a `Local Instance : CurKtier :=
KT1` override only when it first needs KT1 facts (after phase D). The
default's failure direction is sound: a file that forgets the override
gets KT0 and an UNPROVABLE goal at its KT1 access, never unsoundness.
Explicit local pins beat the default via the priority gap regardless of
declaration order.

- **Phase A** (design §2; lands green on main): `strans_bit` ghost_var →
  mono_nat-backed oneshot. `strans_pending` := half auth at 0 (the Bare
  arm's + the boot receipt's halves), KPT arm := full auth at 1,
  `kpt_on c` := `mono_nat_lb_own (strans_name c) 1` — persistent, timeless.
  Conflicts: lb 1 × auth 0 → 1 ≤ 0; pending × full auth → fraction > 1.
  Flip = combine halves, update 0→1, mint lb. Touches: IntrDefs.v (def,
  arms, accessors, flip, trap_csrs member — becomes a persistent conjunct),
  SmodeCore.v (`strans_bit_bare/kpt` constants — delete if unconsumed),
  RiscvAdequacy.v (per-CPU alloc), usertrapret + kvminithart proofs.
  `ghost_varG (mword 1)` STAYS (sie_gname/intr_count use it); mono_natG is
  ADDED alongside.
- **Phase B** (design §3; green on main): `sr_kwit`/`sr_kwit_pers`/
  `sr_absorb_wit` on `s_regime` + the three instances (bare `False`,
  kpt_share `emp`, strans `kpt_on cpu_id`).
- **Phase C** (design §1, §4, §6; the big one — branch until green): the
  `ktier` lattice + `KtierLe` (new bottom file), ktier-indexed `mem_pointsto`
  (KT0 = pinned conjunct, KT1 = the RED definition), `CurKtier` class +
  notation + the global KT0 default, tier-preserving leaf rules with the
  ~14 `%Hid` sites as the KT0 arm, `WpSconfMem.v:242`'s `pa` binder
  renamed in passing (design §9 step 6). Recon facts (measured, 2026-08-16):
  - Definitions to index, all top-level in RiscvPtsto.v, no shared
    Section: `mem_pointsto` (923), `word_pointsto` (1100), `word2_` (1186),
    `word4_` (1238), `string_pointsto` (1337; the design sketches say
    `str_bytes` — THAT NAME DOES NOT EXIST, it is `string_pointsto`/`↦ₛ`),
    plus `stack_own` (StackOwn.v:136). The PHYSICAL tier (`↦ₚ`, `↦ₚ₈`,
    `stack_own_phys`) needs NO index; the text tier is Phase E.
  - Family typeclass instances to re-check under the index:
    `mem_pointsto_timeless` (943), the `*_discarded_persistent` set
    (1739/1352/1979/1981/2010); `stack_own` has none of its own.
  - Destructure footprint beyond RiscvPtsto/KMap/SmodeCorePt is EXACTLY
    the 14 `%Hid` sites: WpSconfMem 316/947/1430/1732/1940, WpSmodePtMem
    1046/1252/1457/1659, WpSmodePtLeaves 427/832, SmodeCorePt 258 (via
    `mem_pointsto_pin`; its write-back re-mint is the precedent for the
    tier-preserving KT0 arm), WpSconfLock 907, ProofAcquiresleep 220 (odd
    one out — no adjacent `sr_adm_id`; inspect before patching).
  - Constructor sites: `phys_ident_mem`/`mem_ident_phys` (KMap.v:155/141,
    already carry the static premise — trivially KT0), `phys_to_mem_map`
    (RiscvPtsto.v:1914 — the RED branch already dropped its identity
    premise; it IS the KT1 constructor), `phys_to_mem_claim`/
    `mem_to_phys_claim` (1932/1944; callers KptTree.v:509/529,
    ProcInv.v:742/761), adequacy's whole-image mint
    (RiscvAdequacy.v:427-434/513/798-816, kmap_M0 ⇒ KT0).
  - Mine the RED suite via the MERGE-BASE diff
    (`git diff 4019ec33...sp-migration-red -- iris/`) — a naive two-dot
    diff is polluted by unrelated main churn. Repaired lemmas reusable
    as the KT1 suite: agree/ne/frac_split/acc/canonical/ram/persist/pin/
    phys_to_mem_map/phys_to_mem_claim; `mem_to_phys_claim` keeps its
    identity hypothesis (inherently KT0-consuming).
  - **BINDER NAME: never `GEN` for `CurKtier`** — `GEN : GenId` (the kexec
    era index) is pre-existing and widely threaded (e.g. SpecPrintk.v:202).
    Reserve `KTR`.
  - The Module-Type "Parameter binder list must match Definition" trap
    does NOT bite Phase C (a `Local Instance`/default adds no binder);
    it goes live at the dual-regime phase, when files gain a real
    `` `{CG : CurKtier} `` — 114 Module-Type files mention family notations
    in Parameter signatures and must then be swept in matching pairs.
- **Phase D** (design §5): `sie_cap` g-index + `ktier_wit` + `sie_cap_ktier_up`
  at kvminithart; the SIE='1' arm pins KT1.
- **Phase E** (design §9 step 7, later): `text_pointsto`/TRAMPOLINE.

### Phase A findings (LANDED)

Landed as designed — 19 files, whole-tree build green. Deviations and
facts phases B–D need:

- **The one-shot's three faces are gname-explicit definitions in
  `RiscvPtsto.v`** (`strans_pending_at` / `strans_kpt_at` / `kpt_on_at`,
  beside `gen_auth`), and `IntrDefs`' `strans_pending` / `strans_kpt` /
  `kpt_on c` are those at `strans_name cpu_id` / `strans_name c`. This is
  NOT cosmetic: `DiskPtsto.diskGhostG` carries a second `mono_natG Σ`
  (`disk_nc_inG`), and `BootShared`'s allocation section binds it beside
  `riscvGS` — a raw `mono_nat_auth_own` written there resolves to the disk
  instance and then will not unify with `IntrDefs`', both printing
  identically. Anything phase B–D writes over the one-shot outside a
  `riscvGS`-only context must go through these definitions.
- **No Σ / functor / adequacy-statement change.** `mono_natG Σ` already
  reaches every site as `riscvF_genGS` (a `::` substructure of
  `riscvFixedGS`, itself one of `riscvGS`), and `mono_natΣ` is already in
  `riscvΣ`. `ghost_varG (mword 1)` stays for `sie_gname`/`spp`/`spie`.
- **`strans_inv_acc_kpt` no longer returns the receipt** (persistent), so
  its conclusion is just `∃ root_ppn, tlb_res_pt ∗ (tlb_res_pt -∗
  strans_inv)`. Its single consumer (`WpSconfCsr.wp_csrr_satp_*`) now
  introduces the receipt as `#Hkptr`. `strans_bit_flip` → `strans_flip`
  (`strans_pending -∗ strans_pending ==∗ strans_kpt ∗ kpt_on cpu_id`);
  `strans_bit_agree` is gone, replaced by `kpt_on_pending_False` and
  `strans_pending_kpt_False`. Everything else kept its name and shape.
- **`SmodeCore.strans_bit_bare` / `strans_bit_kpt` DELETED** — nothing else
  consumed them. `sie_bit_off` stays.
- **`UsertrapRes.ut_trap_parked` keeps two conjuncts**, now `strans_kpt ∗
  kpt_on cpu_id` (was two `strans_bit` halves). Nothing relied on the
  CLIENT receipt being exclusive; the "nobody is using the slot" property
  that file's comment leans on is now carried by the auth at fraction 1,
  which is strictly stronger. No escalation was needed anywhere.
- **Every other consumer was a pure textual substitution**
  (`strans_bit strans_bit_bare` → `strans_pending`,
  `strans_bit strans_bit_kpt` → `kpt_on cpu_id`) and needed NO proof
  change — including the `wp_next` continuations, where `cpu_id` resolves
  to the innermost `CpuId` exactly as the old implicit section argument
  did, so `(CID := c)` re-anchoring still works unchanged.
- **`Qp.half_half` REWRITE DIRECTION.** Combining the two pending halves
  by rewriting the goal's `1` BACKWARDS into `1/2 + 1/2` also rewrites the
  `1` inside every `1/2` in the proofmode CONTEXT — `envs_entails Δ Q` is
  one term — leaving `mono_nat_auth_own … ((1/2 + 1/2)/2)` hypotheses and
  an `iFrame: cannot frame` naming a fraction nobody wrote. Build the sum
  with the `Fractional` instance first (`iAssert … (1/2 + 1/2)`), then
  rewrite FORWARDS. `IntrDefs.strans_pending_combine` carries the note.
- For phase B: `sr_kwit := kpt_on cpu_id` is ready to use as designed;
  `kpt_on` has `Persistent` and `Timeless` instances declared, and the
  Bare-arm refutation `strans_absorb_wit` needs is exactly
  `kpt_on_pending_False`.

### Phase B findings (LANDED)

Landed exactly as designed — additive only, whole-tree build green, no
consumer touched (every call site reaches the record through the `sr_*`
projection functions, never positional/eta destructuring, so appending
three fields at the end of `SRegime.s_regime` was a pure extension).

- **The three fields, in order, at the end of the record** (`SRegime.v`):
  `sr_kwit : iProp Σ`, `sr_kwit_pers : Persistent sr_kwit`, `sr_absorb_wit`.
  All three `SRegime …` constructor applications (`bare_regime`,
  `kpt_share_regime`, `strans_regime`) only needed their three new
  positional arguments appended; nothing about the first six changed.
- **`sr_absorb_wit`'s statement** is `sr_absorb`'s premise list with the
  `sr_adm va ppn` conjunct deleted and `sr_kwit -∗` added at the head of
  the resource chain, immediately before `kmap_at (svpn_of va) ppn pc`:
  ```coq
  sr_absorb_wit : forall (acc : MemoryAccessType mem_payload) (va pa : mword 64)
      (ppn : mword 44) (pc : kperm) (σ : mstate) (E : coPset),
    s_acc_ok acc -> kperm_allows pc acc ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    register_lookup misa σ.(sregs) = MISA_C ->
    register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base σ.(sregs) = None ->
    register_lookup cur_privilege σ.(sregs) = Supervisor ->
    _get_Mstatus_SXL (register_lookup mstatus σ.(sregs)) = 'b"10" ->
    exec (effectivePrivilege acc (register_lookup mstatus σ.(sregs)) Supervisor) σ
      = Some (Supervisor, σ) ->
    exec (is_shadow_stack_access acc) σ = Some (false, σ) ->
    pma_allows_all (register_lookup pma_regions σ.(sregs)) ->
    ↑kptN ⊆ E ->
    ⊢ sr_kwit -∗ kmap_at (svpn_of va) ppn pc -∗
      reg_interp σ.(sregs) -∗ gen_heap_interp σ.(mem) -∗ sr_inv ={E}=∗
      ∃ σ' : mstate,
        ⌜ exec (translateAddr (Virtaddr va) acc) σ
          = Some (Ok (Physaddr pa, PBMT_PMA, init_ext_ptw), σ') ⌝ ∗
        ⌜ σ'.(mdev) = σ.(mdev) ⌝ ∗
        ⌜ (σ'.(sregs) = σ.(sregs) \/
           exists tv, σ'.(sregs) = register_set tlb tv σ.(sregs))%type ⌝ ∗
        ⌜ pmp_grant_facts σ' ⌝ ∗
        reg_interp σ'.(sregs) ∗ gen_heap_interp σ'.(mem) ∗ sr_inv;
  ```
  This is the exact shape phase C/D's leaf rules call: `sr_kwit` is the
  ambient witness resource (from `ktier_wit`/the capability), no `sr_adm`
  discharge needed on that arm.
- **The three instances**, each a new lemma beside the regime's existing
  `_absorb`:
  - `bare_regime` → `sr_kwit := (False : iProp Σ)`, `bare_absorb_wit`
    proved by `iIntros "H"; iDestruct "H" as %[]`. `Persistent False` is
    stock (no new instance declared).
  - `kpt_share_regime root_ppn` → `sr_kwit := emp`, `res_absorb_wit`
    proved by discarding the `emp` and delegating verbatim to `res_absorb`
    with `I` for the dropped `True` argument (`res_absorb`'s `sr_adm` was
    already `fun _ _ => True`, so the callee's signature needed no
    change). `Persistent emp` is stock.
  - `strans_regime` → `sr_kwit := kpt_on cpu_id`, new lemma
    `strans_absorb_wit` beside `strans_absorb` in `IntrDefs.v`: case-splits
    `strans_inv`, refutes the Bare arm (`strans_pending`) against the
    witness with `kpt_on_pending_False`, and the KPT arm delegates to
    `res_absorb` with `I`, mirroring `strans_absorb`'s right branch
    exactly. `Persistent (kpt_on c)` already existed from phase A.
- **No deviations from the design.** No leaf, no consumer, no notation
  touched; every `SRegime.v`/`IntrDefs.v` file elsewhere compiled
  unchanged. `sr_kwit_pers` was supplied per-instance as a plain
  `Persistent` proof term (`_` resolves to the stock instances for `False`/
  `emp`; `kpt_on_persistent` for the strans instance) — no new `Instance`
  declaration was needed anywhere.
- **Open for phase C/D**: `sr_kwit`/`sr_absorb_wit` are unused by anything
  yet (by design — "purely additive... unused"). Phase C's tier-preserving
  leaf rule is expected to call `sr_absorb_wit R` on the KT1 arm exactly as
  sketched in design §4, handing it whatever `ktier_wit g` unfolds to at
  the ambient regime.

## State

- DESIGN SETTLED 2026-08-16 (the section above), superseding the MemAcc
  sketch; nothing of it implemented yet. `main` is GREEN — the RED
  experiment does not live on it.
- **Branch `sp-migration-red`** (local, one squashed commit off `4019ec33`)
  holds the RED experiment as a QUARRY for step 3, not as a base: the
  identity conjunct removed from `mem_pointsto`, with `RiscvPtsto.v`'s own
  suite repaired (`mem_pointsto_acc`, `_pin`, `_persist`, `mem_canonical`,
  `mem_ram`, `mem_valid`, `phys_to_mem_map` — which lost its
  `pa_of ppn va = va` premise — `phys_to_mem_claim`, `mem_to_phys_claim`),
  plus `KMap.v` and `SmodeCorePt.v` destructure arities. Those repaired
  lemmas are essentially the KT1 tier's suite; step 3 adapts them under the
  g index rather than rediscovering them.
- On that branch the build stops at `WpSmodePtLeaves.v:427`, the first of
  ~14 sites that destructure `%Hid` out of the datum and feed it to
  `sr_adm_id` (`WpSconfMem` ×5, `WpSmodePtMem` ×4, `WpSmodePtLeaves` ×2,
  `SmodeCorePt`, `WpSconfLock`, `ProofAcquiresleep`). Under the settled
  design these become the KT0 arm of the tier-preserving leaf rules (step 3
  of the implementation order). Implementation should START FRESH from
  green `main` at step 1 (the oneshot refactor, which is independent and
  lands green), not by resuming the branch.
- `text_pointsto` (`↦ₓ`) still carries its own identity conjunct, so the fetch
  path is untouched. It must eventually lose it too (TRAMPOLINE is
  non-identity); the settled design covers it — same index, same witness —
  as step 7 of the implementation order.
