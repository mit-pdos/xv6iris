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

## THE SETTLED DESIGN (2026-08-16): generation-tiered datum + capability-
## carried witness + `GenLe` inference

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

### 1. The datum: `va ↦ₘ[g] v`, g ∈ {G0, G1}

- `↦ₘ[G1]` — EXACTLY the identity-free definition now on the RED branch
  (`RiscvPtsto.v:925`).
- `↦ₘ[G0]` — the same PLUS the pure conjunct
  `⌜kmap_static (svpn_of va) KP_rw⌝`. From it any consumer derives identity
  with no caller premise: `kmap_static_claims_at` (ambient in `hw_config`) +
  `kmap_at_agree` + `pa_of_id` — the `mem_ident_phys` dance, performed
  INSIDE the leaf.
- Weakening `↦ₘ[G0] ⊢ ↦ₘ[G1]`; strengthening is recoverable because the
  tier conjunct is PURE (`mem_gen_strengthen : ⌜kmap_static …⌝ -∗ ↦ₘ[g] ⊢
  ↦ₘ[G0]`) — extract the class fact before weakening, reapply after. Both
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

`s_regime` keeps `sr_adm`/`sr_adm_id` (the G0 path) and gains:

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

### 4. The leaf rule: tier-preserving, heterogeneous, `GenLe`-inferred

```coq
Class GenLe (g1 g2 : gen) : Prop := gen_le : …
Instance gen_le_bot g  : GenLe G0 g.   (* static usable everywhere *)
Instance gen_le_top g  : GenLe g G1.   (* a KPT hart honors every claim *)
Instance gen_le_refl g : GenLe g g.    (* spec arg riding the ambient gen *)

Lemma wp_load_byte g g' `{!GenLe g' g} … :
  gen_wit g -∗ va ↦ₘ[g'] v -∗ … (va ↦ₘ[g'] v -∗ …) -∗ …
```

G0 datum → identity derived internally, absorb via `sr_adm`/`sr_adm_id`
(this arm is where the ~14 RED `%Hid` sites land, patched ONCE); G1 datum →
`GenLe` forces `g = G1`, absorb via `sr_absorb_wit`. THE DATUM COMES BACK AT
ITS OWN TIER — a G0 fact stays G0 through any number of accesses, so
re-deposit into a G0-stated invariant (kfree → freelist) needs no
strengthening dance. Instance-set facts: the goal shapes that arise are
`GenLe g g` (refl), `GenLe G0 g` (bot), `GenLe g G1` (top); all heads are
premise-free, so no TC search divergence; closed-corner overlap
(`GenLe G0 G1` matches two) is benign for a Prop class. `GenLe g1 g2` for
two UNRELATED variables is correctly unprovable (false at G1,G0) — the
caller must pin or weaken. **The set {bot, top, refl} is complete FOR THE
TWO-POINT LATTICE ONLY**; if the lattice ever grows (kexec era index was
the candidate), switch to a decision-procedure instance or Hint Extern.

### 5. Witness delivery: the CAPABILITY is g-indexed; nothing new is threaded

`sie_cap g m avail b p` carries one persistent conjunct `gen_wit g`
(`gen_wit G0 = emp`, `gen_wit G1 = kpt_on cpu_id`). The SIE='1' arm PINS
`g = G1` internally (it owns `intr_res`, post-trapinithart only — this is
the existing "interrupts enabled ⟹ KPT" invariant, `IntrDefs.v:809-816`,
promoted to an index), so the Banach trap fixpoint stays at G1 unindexed;
only the SIE=0 capability form is g-polymorphic. Boot's capability is built
at G0 (`sie_cap_intro_bare`); kvminithart upgrades it once
(`sie_cap_gen_up : sie_cap G0 … -∗ kpt_on -∗ sie_cap G1 …`, minting
`kpt_on` at the flip — it owns the slot mid-switch). Interrupts-off code
needs no SIE-based deduction: the capability it already holds WAS BUILT at
a generation and carries the witness. Leaves get `gen_wit` through the
engine plumbing that already destructures the capability to feed `sr_inv`.
NO function spec grows an `sr_gen_ok`-style premise.

### 6. Notation: ambient `CurGen` (the weak-memory Stage-1.7 trick)

```coq
Class CurGen := cur_gen : gen.
Notation "a ↦ₘ v" := (mem_pointsto cur_gen a … v).  (* + towers, sie_cap *)
```

Per-file deltas — this is the whole answer to "how wide is the cone":

- POST-BOOT-ONLY files (the fs tier, proc, pipe — the bulk):
  `Local Instance : CurGen := G1.` Spec/proof text otherwise UNCHANGED —
  `↦ₘ` elaborates to `↦ₘ[G1]`, the RED-branch definition those proofs
  already use.
- BOOT-ONLY files (ProofMain, ProofMainSecondary, kvminit):
  `Local Instance : CurGen := G0.`
- THE DUAL-REGIME CONE (printk/printf, console, uart, string/memmove/
  memset, acquire/release, kalloc): section binder `` `{GEN : CurGen} `` —
  the ∀g is the section variable; statements keep their spelling. Only
  genuinely mixed-tier ARGUMENTS name an explicit `[g_i]` with a `GenLe`
  premise, e.g. printk with per-`%s` tiers:

  ```coq
  Lemma printk_spec g gf g1 `{!GenLe gf g, !GenLe g1 g} … :
    { sie_cap g … ∗ stack_own[g] sp n ∗ str_bytes[gf] fmt ∗ str_bytes[g1] s1 }
      printk  { …same back, same tiers… }
  ```

  ONE proof; each region independently G0 or G1; a boot caller instantiates
  everything at G0 (all premises trivial); a post-boot caller sets g := G1
  and mixes freely (top/bot instances). The stack rides the capability's g
  — boot stack0 is G0 with the G0 cap, kstack is G1 with the G1 cap; they
  genuinely co-vary, so this is not a restriction.
- DISCIPLINE, inherited verbatim from the CurCtx scar tissue on the
  weak-memory branch: `Typeclasses Opaque cur_gen`; NAMED section binders
  (anonymous instances auto-name `H` and collide with `iIntros "%H"`); the
  boot↔post-boot SEAM proofs (kvminithart above all, scheduler entry) have
  two generations in scope and must spell `[G0]`/`[G1]` explicitly — with
  two `CurGen` instances in scope, resolution silently takes the
  last-declared one.

### 7. Locks: NOTHING changes in the lock library

A lock invariant's payload spells its tier EXPLICITLY, never `cur_gen` (an
invariant is shared across harts in different regimes; an ambient tier
would let a G1-ambient depositor violate what a G0 acquirer needs). That is
the whole per-lock story: an annotation on the PAYLOAD PROPOSITION, chosen
once per lock — kalloc/console/uart at G0 (true: their data is static RAM /
.data), fs locks at whatever is true of their data. `is_lock`/`acquire`/
`release` are untouched; a Bare hart may acquire ANY lock (the lock word is
static = G0); if the payload hands it G1 facts it can hold, pass, and
re-deposit them — it just cannot drive leaves with them, for want of
`kpt_on`. Unsoundness is structurally unreachable, not prohibited by a side
condition. kalloc end-to-end: freelist stated at G0; kinit/kvminit (Bare)
deposit and use at G0; post-boot callers get G0 pages, use them directly at
ambient G1 (bot instance, tier preserved), kfree re-deposits at G0; the ↦ₚ
conversion for PT nodes gets its static-class premise FROM the G0 datum
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
component ("ξ's generation bound ≤ this hart's generation"), and `gen_wit`
is discharged from `wrunning ξ` instead of the capability — specs written
against §4-§6 simplify rather than change shape. To keep that merge
mechanical: keep `gen` a dedicated lattice type (not bool), keep the
witness behind the capability interface, and NEVER let `kpt_on` leak into a
datum definition.

### 9. Implementation order

1. Oneshot refactor of `strans_bit` (§2) — self-contained, check every
   consumer (two accessors, flip, trap_csrs, sie_cap arms).
2. `sr_kwit`/`sr_absorb_wit` on the record + the three instances (§3).
3. g-indexed datum + `GenLe` + the tier-preserving leaf rules (§1, §4),
   patching the ~14 RED `%Hid` sites into the G0 arm.
4. `sie_cap` index + `gen_wit` + `sie_cap_gen_up` at kvminithart (§5).
5. `CurGen` class/notation + the per-file sweep (§6); lock payloads pinned
   explicitly (§7).
6. While the family is open: fix the mis-named `pa` binder at
   `WpSconfMem.v:242` (DEAD END 2's finding).
7. LATER, same shape: `text_pointsto`/TRAMPOLINE.

The old fallback (move the secondary's `printk("hart %d starting\n")` after
`kvminithart()` to shrink the Bare cone) is NO LONGER NEEDED — under §6 the
"cone" question is moot (post-boot files are textually unchanged; the
dual-regime cone pays one section binder). Kept here only as history.

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
  lemmas are essentially the G1 tier's suite; step 3 adapts them under the
  g index rather than rediscovering them.
- On that branch the build stops at `WpSmodePtLeaves.v:427`, the first of
  ~14 sites that destructure `%Hid` out of the datum and feed it to
  `sr_adm_id` (`WpSconfMem` ×5, `WpSmodePtMem` ×4, `WpSmodePtLeaves` ×2,
  `SmodeCorePt`, `WpSconfLock`, `ProofAcquiresleep`). Under the settled
  design these become the G0 arm of the tier-preserving leaf rules (step 3
  of the implementation order). Implementation should START FRESH from
  green `main` at step 1 (the oneshot refactor, which is independent and
  lands green), not by resuming the branch.
- `text_pointsto` (`↦ₓ`) still carries its own identity conjunct, so the fetch
  path is untouched. It must eventually lose it too (TRAMPOLINE is
  non-identity); the settled design covers it — same index, same witness —
  as step 7 of the implementation order.
