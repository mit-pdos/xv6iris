# DECISION MEMO — TSO port, the last blocker class: `inv`s over ξ-indexed EXCLUSIVE data

Read-only analysis on branch `tso` @ `c9b7c991` (2026-08-26); no tree files
edited, no full build run — every claim is static reading of the sources named
plus ONE probe compiled against the real twin (§10, kept at
`/shared/xv6iris-3-fliptree-backup/ZZAbsorbProbe.v`).  Produced as the
owner-decision record for the class `tso-port.md` §0.16′ names as the whole of
what stands between here and a green tree — `BioInv.buf_escrow` and
`StartedInv.started_inv (main_deposit …)`.  **The ask is §8's ranked
recommendation and the two owner decisions restated at §11.**  Line numbers are
from that tree.

---

**Verdict up front: the ABSORB candidate is SOUND, it is the exact dual of `ctx_deposit`, and its twin image is now PROVED against the real `TsoCtxTwin2` construction. One new law + one new structural instance close both members. But the candidate as sketched is one clause short for `started_inv`, and the missing clause is a ▷ problem the sketch does not mention — §5 below is the second owner decision and it is the sharpest finding here.**

---

## 1. The law, stated

### 1.1 `TsoCtx.ctx_absorb` — the running-context dual of `ctx_deposit`

```coq
  Lemma ctx_absorb `{CID : CpuId} (R : CtxId → iProp Σ) `{!CtxMorph R}
      (ξ ξ' : CtxId) (T K : nat) :
    (T ≤ K)%nat →
    own_context ξ' -∗ hart_view_lb K -∗ ctx_parked ξ T -∗ R ξ ==∗
    own_context ξ' ∗ ctx_parked ξ T ∗ R ξ'.
```

Compare the law it mirrors (`TsoCtx.v:621`, verbatim):

```coq
  Lemma ctx_deposit `{CID : CpuId} (R : CtxId → iProp Σ) `{!CtxMorph R}
      (ξ ξc : CtxId) (T : nat) :
    own_context ξ -∗ ctx_parked ξc T -∗ R ξ ==∗
    own_context ξ ∗ ∃ T', ⌜(T ≤ T')%nat⌝ ∗ ctx_parked ξc T' ∗ R ξc.
```

Two differences, both load-bearing: the direction (parked → running, not running → parked), and the premise `hart_view_lb K ∗ ⌜T ≤ K⌝` — **the same stable pair `ctx_resume` (`TsoCtx.v:266`) already consumes.** The parked token is handed straight back at the *same* `T`, which is what makes the claim repeatable (§4 shows why that is not optional).

SC proof: 5 lines, structurally `ctx_deposit`'s (`ctx_dom_unseal` gives `True`, then `ctx_morph`, then frame). No arity change, no seal change, nothing else in `TsoCtx.v` moves.

### 1.2 The sketch's shape, corrected

The lane sketched *"a clean fact at some ∃-closed ξ with `⌜t ≤ W ≤ K⌝` evidence"* and asked what the body must carry.

**It cannot carry a stamp receipt.** The fact's timestamp `t` is sealed inside `ctx_pointsto`'s own `∃ t`, and the clean arm is `mono_nat_lb_own (tc_bnd ξ) t` — a *lower* bound at a foreign gname, from which no numeric fact follows without ξ's authority. Comparing two lower bounds is impossible; that is `tso-transport-memo.md` §1.2's refutation, and it applies verbatim here.

**It must carry the source context's own PARKED TOKEN:**

```coq
    inv N (∃ (ξ : CtxId) (T : nat), ctx_parked ξ T ∗ R ξ)
```

`ctx_parked ξ T`'s twin is `ctx_at ξ 1 T D ∗ llb T ∗ ⌜∀ k, k ∈ dom D → k.1 ≤ T⌝` (`TsoCtxTwin2.v:329`) — the *authority*, which is exactly what bounds `t ≤ T` for a clean fact (`mono_nat_lb_own_valid`) and for a dirty one (`ghost_map_lookup` + the dom bound). No `llb W`, no extra pure ties. The only pure tie is `T ≤ K` at the open site, and `T` comes out of the ∃.

### 1.3 `ctx_morph_or` — the missing structural instance

```coq
  Global Instance ctx_morph_or (R1 R2 : CtxId → iProp Σ) :
    CtxMorph R1 → CtxMorph R2 → CtxMorph (λ ξ, R1 ξ ∨ R2 ξ)%I.
```

`TsoCtx.v` has `const`, `const_pay`, `pointsto`, `word`, `sep`, `exist`, `big_sepL`, `big_sepM`, `if_then`, `if_else` — **and no disjunction.** It is needed three times on these two members' paths: `buf_escrow_body`'s three arms (`BioInv.v:353`), `FirstTok.first_tok`'s two arms (`FirstTok.v:438`), and `ProcInv.ofile_slot`'s two arms (`ProcInv.v:242`). Kit obligation at the twin, exactly as `ctx_morph_big_sepL` / `ctx_morph_if_*` carry.

---

## 2. Twin soundness — MEASURED, not argued

The probe is a copy of `iris/TsoCtxTwin2.v` with six lemmas appended before `End twin2.`, kept at `/shared/xv6iris-3-fliptree-backup/ZZAbsorbProbe.v`. **It compiles in 9.2 s, exit 0.** It validates the LAW at the proven construction — not a shape mock (contrast `tso-transport-memo.md` §5's Probes A/B, which were self-contained mirrors).

Proved, in dependency order:

```coq
  Lemma view_lb_max h K1 K2 :
    view_lb h K1 -∗ view_lb h K2 -∗ view_lb h (Nat.max K1 K2).

  Lemma ctx_dom_of_parked_stable ξ ξ' h T K :
    (T ≤ K)%nat →
    view_lb h K -∗ own_context ξ' h -∗ ctx_parked ξ T ==∗
    own_context ξ' h ∗ ctx_dom ξ ξ' ∗ (ctx_dom ξ ξ' -∗ ctx_parked ξ T).

  Lemma twin_absorb (R : CtxId → iProp Σ) `{!CtxMorph R} ξ ξ' h T K :
    (T ≤ K)%nat →
    own_context ξ' h -∗ view_lb h K -∗ ctx_parked ξ T -∗ R ξ ==∗
    own_context ξ' h ∗ ctx_parked ξ T ∗ R ξ'.

  Lemma twin_absorb_byte ξ ξ' h T K a dq v :          (* the acid test, any dq *)
  Lemma twin_escrow_roundtrip (R R' : CtxId → iProp Σ) … :  (* absorb ∘ deposit *)
  Global Instance ctx_morph_or …
```

**Is the bound-raise with foreign `t` + view evidence sound?  YES, and here is the invariant it preserves.** `own_context ξ' h` (`TsoCtxTwin2.v:318`) asserts `ctx_at ξ' 1 B D ∗ view_lb h K₀ ∗ ⌜B ≤ K₀⌝ ∗ llb W ∗ ⌜dom D ≤ W⌝ ∗ [∗ map] dirty_ok h B`. Absorb raises the bound to `Nat.max B T` and re-founds the receipt at `Nat.max K₀ K`:

- `Nat.max B T ≤ Nat.max K₀ K` from `B ≤ K₀` (the token's own) and `T ≤ K` (the premise) — **so "my clean facts ≤ my bound ≤ my hart's view" is preserved exactly**;
- the new receipt is `view_lb_max` on the token's `K₀` and the premise's `K` — and `view_lb_max` needs no cmra reasoning at all (`Nat.max K₀ K` is one of the two; keep it, drop the other — the `llb_max` idiom already in the file at `:195`);
- the dirty rows survive by the existing `dirty_ok_mono` (`:306`);
- ξ's half-authority is borrowed and returned by the existing `ctx_at_halves` / `ctx_at_agree` (`:274`, `:283`).

**The decisive structural point: absorb is INTERP-FREE.** The twin's acquire-side mint `ctx_dom_of_parked` (`:678`) needs `tso_interp` and `⌜length log ≤ tvs h⌝` — the AMO's at-the-top evidence — solely to *manufacture* the comparison `T ≤ tvs h`. Supply the comparison as a premise (the stable pair) and the interp drops out entirely. Absorb is therefore `twin_resume` (`:750`, itself a wand) generalised from a whole token to a single payload, and it sits one strict notch *below* the mint it generalises.

**Does the discarded/fractional axis survive?  YES.** `ctx_morph_pointsto` is stated at arbitrary `dq`, absorb routes through `ctx_morph`, and a discarded cell is copied rather than moved — `twin_share`'s dissolution of §0.4 item 6 (`TsoCtxTwin2.v:961`). `twin_absorb_byte` is the acid test at arbitrary `dq`, clean or dirty arm.

This is also *why* absorb is the right answer for member 2 specifically: `main_deposit`'s **entire** ξ-dependence is discarded cells — `procs_inv`'s per-slot `is_kstack`, `disk_geom`'s three `↦₈□` ring pointers, and the `kernel_pagetable ↦₈□` word. §0.16′ correctly refuses to hand those out uniformly (`t > 0`, §0.4 item 6). Absorb hands them out *against view evidence*, which is §0.15′'s own rule ("give the resource the TRANSPORT, not the uniformity") applied at the fact level rather than at `caps_morph`'s.

---

## 3. Member 1 — `BioInv.buf_escrow`

### 3.1 What the escrow's ξ-dependence actually is (measured)

`buf_escrow_body` (`BioInv.v:353`) is `buf_parked ∨ buf_chain ∨ buf_mid`. Reading the leaves:

- `buf_chain` (`:328`) — `bref_tok` + two `↦₄` + `bown` + `bmid`: **ξ-FREE outright** (stage 1 does not flip `↦₄`).
- `buf_parked` (`:316`) and `buf_mid` (`:346`) — their ONLY ξ-indexed row is `buf_own`, and `buf_own` (`BufOwn.v:48`) is
  ```coq
    (b_blockno b ↦₄{DfracOwn (1/2)} bno ∗ b_disk b ↦₄ dsk ∗ ⌜length bs = 1024%nat⌝ ∗
     ([∗ list] j ↦ byte ∈ bs, pa_add (b_data b) j ↦ₘ byte))%I
  ```
  i.e. **one 1024-element `big_sepL` of `ctx_pointsto`.** `buf_pay`/`bio_pay`/`pool_blk` are disk-tier + ghost, ξ-free.

So `CtxMorph (λ ξ, buf_escrow_body (XI:=ξ) bn V k)` is `or ∘ exist ∘ sep ∘ (const | if_then/if_else | big_sepL ∘ pointsto)`, applied AS TERMS (§0.15′'s requirement). Only `ctx_morph_or` is missing.

### 3.2 Recommended shape: ∃-close (not a named context)

```coq
  Definition buf_escrow (bn : bio_names) (V : bio_view Σ) (k : nat) : iProp Σ :=
    inv bioN (∃ (ξ : CtxId) (T : nat),
                ctx_parked ξ T ∗ buf_escrow_body (XI := ξ) bn V k).
```

A **closed term**, so `bio_ctx` → `fs_ready` → `first_tok` → `proc_priv` all lose that row. ∃-closing is sufficient *here* — and only here — because the escrow's whole access is ONE invariant open: destruct → absorb → run the existing arm-swap lemma at `cur_ctx` → `ctx_deposit` back into the same ∃-bound `ξ` → close with witnesses `(ξ, T')`. The witness never has to be recovered at a second open. (§5 shows why `started_inv` cannot do this.)

`buf_escrow` and `bio_ctx` must **move below `Section BioInv`** (`BioInv.v:219–221`, which binds `XI`): a section variable cannot be instantiated inside the section that binds it, and with `XI` in scope an unannotated row silently captures the ambient (§0.8′ rule 3; the `is_kmem` / `is_conslock` / `is_ftable` move, fourth occurrence).

### 3.3 The `sleeplock`/`lock-payload` restatement is REFUTED by measurement

The brief asked whether every open is under the buffer's sleeplock. **It is not: 4 of the 6 opens are not.**

| # | site | enclosing lemma | lock held |
|---|---|---|---|
| 1 | `ProofBread.v:687` | `bread_tail` | sleeplock (`sleeplocked …`, `:662`) |
| 2–5 | `ProofBread.v:1386, 1415, 1440, 1459` | `bread_recyc` | **bcache spinlock only** (`locked (bn_lk bn) cpu_id`) |
| 6 | `ProofBrelse.v:678` | `wp_brelse_sconf` | sleeplock (via `bio_locked → bio_held`, `BioInv.v:1040`) |

`grep -n sleeplocked ProofBread.v` returns exactly one hit — line 662. The recycler rewrites `dev`/`blockno`/`valid` under bcache.lock at `refcnt == 0` while a would-be sleeplock winner races it *by design* (`BioInv.v:8-17`; `ProofBreadParts.v:455-476`), and the arms are refuted algebraically (`escrow_open_free`, `escrow_open_mid`), not by lock ownership. **The escrow exists precisely to bridge the two lock disciplines, so neither can subsume it.**

And the sleeplock could not host ξ-indexed data anyway. `SleepLock.v:433-441`, verbatim:

```coq
  Definition is_sleeplock_gen (γl γ : gname) (slk : mword 64) (s : string)
      (R : iProp Σ) (H : Qp -> iProp Σ) : iProp Σ :=
    (sl_name slk s ∗
     is_lock γl (sl_lk slk) "sleep lock"%string <{ sl_res_gen γ slk R H }>)%I.
```

`R : iProp Σ` is unrestricted as a *proposition* but hard-wired through `const_pay` — so it is pinned at one ambient for every holder, and moving the block bytes there means `R : CtxId → iProp`, **a sleeplock-surface change**, which §0.14′ already priced and declined. The bcache lock's payload (a genuine `CtxId → iProp` slot) cannot host it either: `bread_tail` reads the block with bcache.lock released.

### 3.4 Cascade — 7 files, 20 `buf_escrow` mentions

- `BioInv.v` (24 lines touched → the definition + the two moves): the 6 arm-swap lemmas (`escrow_swap_checkout/_park/_park_now`, `escrow_open_free/_open_mid/_close_mid`) are stated ON THE BODY and are **UNCHANGED**; add one `CtxMorph` instance; `bio_init`'s `inv_alloc` (`:1221`) gains `ctx_parked_alloc` + `ctx_deposit`.
- `BioInitAt.v:204` — the second allocator, same. **Check this one**: `bio_init_at` is the "at a published record" variant and must hold an `own_context` to run `ctx_deposit`; if it does not, its parked context has to be threaded in from its caller.
- `ProofBreadParts.v` — `buf_escrow_inv` (`:52-53`) re-typed; the three `escrow_recyc_*` lemmas UNCHANGED.
- `ProofBread.v` — `bread_tail`'s premise (`:652`, it takes the raw `inv bioN (buf_escrow_body …)` directly) re-typed; 5 open sites bracketed.
- `ProofBrelse.v` — local `buf_escrow_inv` (`:217`) + 1 open site.
- `ProofForkretPark.v`, `SystemAdequacy.v` — comments only.

**Arities of `bio_ctx` / `fs_ready` / `first_tok` / `proc_priv` do not change**, so their 193 / 214 / 74 / 684 mentions across 90 / 37 / 33 / 134 files are pure echo and move nothing.

---

## 4. Member 2 — is something weaker than absorb enough?  NO, and the measurement forces it

The brief asked whether a stamped-parked-record shape (`ctx_parked` / `ctx_deposit`, no new law) might serve, since the boot deposit "is written once and claimed once per hart".

**It is written once. It is NOT claimed once per hart.** Measured:

- `main_deposit` is `Persistent` (`SpecMainSecondary.v:124`), and `started_inv_load_au` (`StartedInv.v:126`) re-closes the invariant with the *same* disjunct (`iDestruct "Hrest" as "#Hrest"` … `iApply "Hrest"` … `iExact "Hrest"`, `:139-145`).
- `ms_spin` is an `iLöb` that runs a full `started_inv_load_au` on **every iteration** (`ProofMainSecondary.v:356-358`) and drops the payload on the back edge. The tree says so: *"the iteration that goes around again just drops the payload"* (`:372-377`).
- There is **no claim token, fraction, or one-shot ghost anywhere**. `boot_hart_secondary`'s entire evidence is the persistent `started_inv` plus the pure `(fin_to_nat cpu_id <> 0)%nat` (`BootChain.v:626-640`). Adequacy hands the *same* `#Hstarted` to all eight through one `big_sepL_impl` (`SystemAdequacy.v:438-450`).
- `StartedInv.v:26-29` states the design reason: *"Up to `NCPU - 1` harts read the flag, each expecting the payload, and the invariant is re-closed unchanged after every read -- so `P` has to be duplicable."*

So an exclusive one-shot record is refuted: `ctx_resume` **consumes** the parked token, and there is exactly one. **Absorb's give-back at the same `T` is precisely the property that makes an unbounded claim work**, and no weaker law has it.

---

## 5. THE SECOND OWNER DECISION — `started_inv`'s ▷, and why ∃-closing FAILS there

This is the one thing the candidate sketch does not cover, and it is what §0.16′'s own recommended shape ("∃-close the context inside the invariant") gets wrong for this member.

`started_inv_load_au` hands the payload out **under a `▷`** and re-closes the invariant in the same fupd:

```coq
    started_inv P -∗
    (|={Eo, Eo ∖ ↑startedN}=> ∃ v : mword 32,
        started_addr ↦₄ v ∗
        (started_addr ↦₄ v ={Eo ∖ ↑startedN, Eo}=∗
           ▷ (⌜v = started_clear⌝ ∨ P)))
```

The `▷` is stripped **one instruction later**, by the acquire fence at `main+0x18` (`ProofMainSecondary.v:372-377`: *"it is still the one step whose continuation is under a `▷`, which is what turns the invariant's `▷ deposit` into the deposit"*). So:

1. absorb **cannot** run inside the AU — the payload is under a `▷` there, and `ctx_dom`'s non-persistence forbids crossing it (memo §1.2, and there is no step to spend);
2. by the time the `▷` is gone, the parked token is back inside the invariant;
3. re-opening yields a **fresh ∃-witness** `ξ₂` that cannot be tied to the payload's `ξ₁`. Dead.

**Therefore `started_inv`'s deposit context must be NAMED, not ∃-closed.** `boot_shared_alloc` — which already allocates the invariant (`BootShared.v:1668-1669`) and already returns `γd γv` existentially — mints one parked context `ξd` with `TsoCtx.ctx_parked_alloc` (pure, exported, `TsoCtx.v:228`) and returns it. Then `main_deposit ξd γd γv` states its three ξ-indexed rows at `(XI := ξd)`: **a closed term, still `Persistent`**, so `started_inv` / `started_body` / all three `StartedInv.v` lemmas are **UNCHANGED** and all eight harts share one handle. `∃ T, ctx_parked ξd T` rides as a second, *timeless* conjunct (a new row of `started_body` outside its disjunction, or its own one-line `inv`), and the secondary absorbs **after** the fence, at a second open where `ξd` is named and the token comes out of the `▷` by timelessness.

This is the port's own landed precedent one layer up — `off_hold`'s `ip` argument (§0.16′, memo §9): *pin the index as an ARGUMENT rather than ∃-closing it.* Same technique, different reason: there it removed a redundant copy; here it survives a second open.

### Cascade — 8 files, 29 `main_deposit` mentions (mostly type-level)

- `SpecMainSecondary.v` — `main_deposit` gains a leading `(ξd : CtxId)`; three rows spelled `(XI := ξd)`; add `CtxMorph (λ ξ, main_deposit ξ γd γv)` (`procs_inv` MORPH OK, `disk_geom` MORPH OK, the `↦₈□` cell `ctx_morph_word`, the rest `ctx_morph_const`).
- `BootShared.v` — mint `ξd` + its parked-token invariant beside `started_inv`; one more existential out of `boot_shared_alloc`.
- `BootChain.v` — `boot_hart_primary` / `_secondary` take `ξd`; **the primary's deposit moves OUT of the `□`-wand** (`:781-789`), because `ctx_deposit` consumes `own_context` and cannot run under a `□`. It goes into `boot_hart_primary`'s body, where the token lives. (Same lesson as §0.16′ step (ii)'s "the package's `▷` has to move onto its closer row alone" — a deposit runs at the top level or not at all.)
- `ProofMain.v` (`mn_grp_started`, the writer) — its `□`-wand's premises are now stated at `ξd`; shape otherwise unchanged.
- `ProofMainSecondary.v` (`ms_spin`) — the absorb, after the fence. **The one genuinely new proof step in this member.**
- `SpecMain.v`, `SystemAdequacy.v`, `FsCfg.v`, `FsCfgBoot.v`, `FsReady.v` — type-level echo.
- `StartedInv.v` — **UNCHANGED** (all 11 mentions internal; the `P : iProp Σ` parameter and the `{!Persistent P}` discipline survive intact).

---

## 6. Shared mechanical work (one lemma, nine uses)

Every absorb/deposit site needs `own_context cur_ctx`, which rides inside `sie_cap_gpr` (ruling 2). All six escrow openers take `sie_cap_gpr` (checked: `ProofBread.v:652`, `:1330`, `ProofBrelse.v:552`), as does `ms_spin`. `IntrDefs.sie_cap_gpr_split` / `_join` already exist (`IntrDefs.v:3318` / `:3324`) and `own_context cur_ctx` is `sie_cap`'s fourth conjunct (`:2806`, destructured as `"(Hstk & Htr & Harm & Hctx & #Htc & #Hwit)"` at `:3308`). Write ONE accessor —

```coq
Lemma sie_cap_gpr_own_ctx_acc {kt} m avail b p :
  sie_cap_gpr kt m avail b p -∗
  own_context cur_ctx ∗ (own_context cur_ctx -∗ sie_cap_gpr kt m avail b p).
```

— used at the 6 escrow opens, the 1 started claim, and the park's step (ii) (built and reverted at §0.16′; re-derive it there). It belongs in a small file, **not** `IntrDefs.v` — 425 files sit on that.

---

## 7. The M2 debt, named — and why it is the RIGHT debt

At SC the `hart_view_lb K ∗ ⌜T ≤ K⌝` premise is discharged by `TsoCtxShim.hart_view_lb_any T` at `K := T` (`T ≤ T` by reflexivity — one line, no `K` threading). Seven new sites, joining `ProofSwtch.v:374`'s existing one. Three files gain the shim import (58 files already have it).

**This is deliberately the same quarantine the scheduler's resume already owes**, and `SpecAcquire` already exports `(∃ K : nat, hart_view_lb K)` to every lock winner (`SpecAcquire.v:172`, `:229`) — so the M2 sweep that makes that `K` real is *one* item serving swtch-resume and every escrow open alike.

**Do NOT discharge these with `TsoCtxShim.ctx_dom_sc`,** which the cheaper alternative (§8 item 2) would need. The park memo's §5 makes the point and it is decisive here: *a bare `inv` has no acquire*, so a `ctx_dom` at an escrow open has no identified honest producer and would be a permanent lie. Absorb's premise is **hart-local** — it says nothing about the source context — so an acquire that knows nothing about the escrow can still supply it. That asymmetry is the entire reason to prefer absorb over the cheaper shape.

---

## 8. Alternatives, ranked

1. **(RECOMMENDED) parked-record invariant + `ctx_absorb` + `ctx_morph_or`.** One law, one instance, both twinned and proved. ~2 surface files + 7 + 8 member files + 1 shared accessor.
2. **Bare ∃-close + `ctx_morph` against `TsoCtxShim.ctx_dom_sc`** at the 6+1 sites. ~30 lines cheaper, needs *no new law*, works today. **Rejected**: pays in the wrong currency (§7), and it does not work for `started_inv` at all (§5's two-open ▷ problem).
3. **Resumer-supply** (the `park_globals` technique). Refuted for the escrow at §0.16′ (the first resumer runs before `first_done` exists) and inapplicable at boot.
4. **∀-context / uniform form.** Refuted at §0.15′/§0.16′ (`t > 0` discarded cells). Absorb is the correct replacement for exactly this case: transportability against evidence, not uniformity.
5. **Escrow rides a lock payload.** Refuted by measurement (§3.3).
6. **A `CtxMorphStep` / ▷-capable transport.** Not needed: timelessness answers the ▷.

---

## 9. Risks

- **The `▷` over the inv body: answered by TIMELESSNESS, not by later-compatibility.** `buf_escrow_body_timeless` (`BioInv.v:399`) and `ctx_parked_timeless` (`TsoCtx.v:215`) both exist; `ctx_id_inhabited` (`TsoCtx.v:87`) is what lets `▷ ∃ ξ` push inward, and its header already says it is load-bearing for exactly this. So the escrow's absorb never meets a `▷` and `ctx_dom`'s non-persistence is never tested. **The single exception is `started_inv`, and §5 is its answer.**
- **Silent capture** (§0.8′ rule 3, the highest-probability lost day): every row of the moved body must spell `(XI := ξ)`, and `buf_escrow`/`bio_ctx` must move below `Section BioInv`'s `XI` binder.
- **Performance.** Once `buf_escrow` is closed, `bio_ctx` is closed and `ctx_morph_const` resolves the whole `fs_ready` row **by search** — no big-op walk. Do not `Typeclasses Opaque` an ∃-shaped definition (§0.16′'s measured gotcha: `IntoExist` is a typeclass). Never leave a failing cross-ξ `iExact` running.
- **Residual, and it is the one thing still unmeasured.** `proc_priv`'s cone was measured only to its first failure. `proc_priv = proc_priv_core ∗ proc_ofiles`; after the escrow lands the walk still has to get through `proc_ofiles → ofile_slot`, whose disjunction is why `ctx_morph_or` is on the critical path and whose `file_ref` row is `MORPH file_ref OK`. `proc_fields`/`proc_pt`/`tf_page`/`cwd_ref` are measured ξ-free or MORPH-OK, so **no second `inv`-over-ξ-body is visible** — but that is a reading, not a measurement, and probe (b) below settles it for one file.

---

## 10. The probes

**Run, and it is the load-bearing one:** `/shared/xv6iris-3-fliptree-backup/ZZAbsorbProbe.v` — `TsoCtxTwin2.v` + the six lemmas of §2, **9.2 s, exit 0**. It answers the only question that could sink the design ("is the bound-raise with foreign `t` sound at the proven construction?") for the cost of one file and needs no tree rebuild (`TsoMem.vo` / `TsoCtxTwin.vo` are current). Compile it with

```
opam exec --switch=/shared/xv6rocq -- rocq compile -q \
  -R /shared/xv6iris-3/iris xv6iris -R /shared/xv6iris-3/model-xv6iris Riscv \
  -w -notation-overridden ZZAbsorbProbe.v
```

**Next, once the tree rebuilds, using §0.16′'s three-probe kit** (`Check @f`; `tryif reflexivity`; `tryif (apply _) then idtac "MORPH f OK"`):

- (a) `Check @buf_escrow` prints no `CurCtx`, then `MORPH bio_ctx` / `MORPH fs_ready` / `MORPH first_tok` / **`MORPH proc_priv`** — the last one is what closes `forkret_park_paid`'s sixth row and flushes the residual risk above.
- (b) `MORPH (λ ξ, main_deposit ξ γd γv)`.

Both are cheap and neither can crawl.

---

## 11. What this leaves between here and green

After the ruling lands, `ProofForkretPark.forkret_park_paid`'s six deposit rows are all payable, and §0.16′'s step (ii) — threading the parker's `own_context` through `ParkCap.park_cap` / `forkret_park_paid_body`, with the hart ∀-quantified beside the context and the package's `▷` on its closer row alone — is the re-derivable remainder (built, measured, reverted; the shape is recorded verbatim at §0.16′ step (ii)). `SystemAdequacy`'s eight-hart fan-out closes on member 2. That is the whole red list.

**Two owner decisions:** (1) adopt the parked-record idiom and `ctx_absorb` as a sealed-surface law (§1, twinned in §2); (2) name `started_inv`'s deposit context rather than ∃-closing it (§5). Everything else in this memo is mechanical and counted.
