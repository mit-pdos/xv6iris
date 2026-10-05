# Spinlock (LB/AxSL) — progress estimate, 2026-10-05

> **Lean port in progress:** the weak-memory development is being ported to Lean on bookmark `weak` (see [`notes/weak-port-map.md`](../../../notes/weak-port-map.md)); file/tactic names below are Rocq ([`claude-notes/LEAN.md`](../../../claude-notes/LEAN.md)).

Advisor read-only assessment (notes + `iris/AxSpin*`, `AxCertP*`, `AxScCat/Run*`, `AxSpinGate`, `AxTierA2`).
Scope of the effort: ~119 `AxSpin*`/`AxCertP*` files, ~39.7k lines (whole `Ax*` tree: 330 files, 151k).
No `Admitted`/`Axiom` anywhere in them; every header carries a scope/vacuity block.

## 1. What is PROVED today (layered)

**Engine / adequacy (generic, real Sail).**
- Gated tier-A adequacy at the tagged model: `AxSpinGate.tierA_adequacy_ann_gate_t` (graph premise `rvwmo_cat_consistent_t` only); joint iProp-post variant `AxSpinJ.tierA_adequacy_ann_gate_joint_t` (Theorem 2's final step); deferred-read WPd witness `AxSpinWit.spin_reload_owned` (+ race/sanity).
- Positional row-directed engine, warm TLB, SIE=0 (`ctrl_ok_SW`): BFin spine `AxSpinE..E6` (fit-or-stuck at RAM nodes, `Xx_reg/st/ld/ret`), window-bounded no-RMW/no-split bridge `AxCertP/P2/P3` + `AxSpinXP/XP2` (closes the whole-row no-RMW vacuity), row-stuck lemma `AxSpinRow`.
- Arbitrary-VA first-read chain `AxSpinVA..VA8`: mapped, misaligned, non-canonical, unmapped-at-level-2/1/0 arms proved symbolically; **not assembled** into the premise `va_first_read` (see §2).
- Certificate toolkit `AxScCat` (SC interleavings are cat_t-consistent, generic), `AxScRun/2/3` (graph_of_sc + joint tracer + run premise; demo on real spin/release-tail bytes).

**Protocol / ownership (Ixv6).** `AxSpinX..X8` joint instance `prot_xv6` (lock word, lk->cpu with Φ_cpu, nextpid with Theorem-2 ghosts, private stack/cpu fields by WOK, read-only, blocked), `xv6_Hok`, `xv6_Hob_alloc`; handle points-to + n-byte/fractional leaves `AxSpinH..H7` (separate instance `spin_ob6`); unification `AxSpinU..U4`: real-width contracts `wpd_acquire_x / reacquire / acquire_fail / release_x / lk_held_x`.

**Per-function real-code WPds (positional CPS, Hrow-pinned, warm TLB, SIE=0):** `wpd_mycpu` (AxSpinE8; certs (a) E8f modulo `va_first_read`, (b) E8d diverted-return stuck twin on a real fetch node), `wpd_holding` (HdA; both call sites with the lock-word leaf discharged, HdC), `wpd_push_off` (PO4, both arms, three mycpu calls), `wpd_pop_off` (PO6, non-panic paths). **Not done:** acquire, release, allocpid. Superseded (retired replay route, kept as record): `AxSpinCtl3.release_wpd5`, `AxSpinRow3.release_wpd6`, `AxRelease4/5`.

**Capstones — hand nodes only:** `AxSpinJ2.u_alloc2_joint` (Theorem 1 shape) and `u_alloc_open` (Theorem 2 shape, arbitrary C, ownership load-bearing; certs (a′)(b)(c′), Print Assumptions = 5 Sail params). On real code: nothing yet.

## 2. Assumptions Theorems 1/2 will rest on

| Class | Premise | Status / what it would take |
|---|---|---|
| H | `va_first_read`: `riscv_step` from any `ctrl_ok_SW` state at any PC is `FirstRd (va_rd T v)` or faults register-only to stvec | Family of Sail claims; four arms proved (VA4/7/8), **excluded**: PMP/PMA-denied fetch, A-clear / non-X leaves, unmapped stvec. Assembly ≈3–5 files; else it stays a visible hypothesis of (d). |
| H | 5 rv64d platform axioms + funext; H1–H4 (fetch oracle, trap-entry ctrl node, ctx-CSR serialization — H3 stronger than ISA, out-of-image traps) | In-definition; invisible to Print Assumptions; must be the audited C13 list. Faithful-ish model commitments, not gaps. |
| H/G | fetches and walker reads are EXPLICIT reads under riscv.cat | Stronger than HW; harmless only because text/PTEs immutable (HAD). Simplification. |
| L | Himg (real text bytes, `locked=0`, `cpu=0`, `nextpid=n0≤2³²−3`, `noff=0`), Hlayout (disjointness, cid injectivity, stack cover, satp/PT geometry, `data_at_S` translations), `*_text` facts, `cl_aligned`, `Hinj/Hstv` (canonical VAs), Hentry (pc/sp/tp/ra, SIE=0) | Faithful facts about the image/page table; discharged by vm_compute in (a). Note: the spike's page table does **not** map pid_lock — (a) needs a kvmmake-faithful table. |
| G | Hcons_t (the model), Hctrl_closed (hardware-faithful by emission; used by the policy), Hdeps + owed honesty bridge (`prog_deps_xv6 ⊆ row_deps_t`), Hharts (only A,B[,C] — no devices, no other 6 CPUs), Hnowrap, row well-formedness (`row_w8`, `no_rmw8`, `row_wle`, `no_rmwn`), `text_fixed` as a graph fact | Hdeps bridge is a gap (definitional, ~1–2 files). Hharts is a real scope restriction, not a model fact. |
| G | HAD: A/D preset, PTEs read-only | Departure from xv6's mappages (owner-accepted, must stay removable; removal route has an UNPROVED gate fix at `AxPtwModel`). |
| R | Hrow ∈ `allocpid_prefixes`: CFG path, fetch addresses, data base addresses, **branch arms** chosen by the row | TEMPORARY per owner. Carries most of the control/address integrity; with `WPd@MaybeStuck` any divergence is trivially verified. Row-integrity theorem owed (weeks). |
| S | SIE=0 throughout (`ctrl_ok_SW` is the only data regime); push_off interrupts-on entry not covered; warm TLB for every page touched; Sv39 level-0 only; HΨmid; panic-prefix rows not built; client = allocpid; stack migration/C-private memory not covered | Scope restrictions. SIE=1 needs a new regime + interrupt delivery + a kernelvec WPd whose handler EMITS memory events (register saves) — a different row shape, not "no events". |

**Suspicious / watch:** (i) `fpin`/`Hinj` ("among canonical VAs only the pinned VA fetches from the pinned PA") must be checked against the REAL kernel table (aliases, trampoline page) in (a). (ii) Panic arms in pop_off/push_off are *excluded by the row*, not refuted: `noff<1 → panic` becomes a row-stuck other arm; for conjunct 1 the panic-PREFIX row must yield False at row end, but `Xx_ld4` deposits **no annotation** for noff/intena and push/pop_off **drop** mycpu's reload annotations — the D4 field-read rule is a confirmed requirement, not yet designed for the ghost-free private class. (iii) `release`'s `sw zero` is WCrel only if the fence's release flag is carried across the instruction boundary; the positional `GoodB` tracks regime/PC/GPRs/TLB — not obviously the armed fence (the fix existed on the retired surface v3). (iv) Conjunct 1's "any consistent execution" reading is an informal prefix-closure argument.

## 3. Recovering Iris invariants and ownership

- **What is recovered:** `is_lock` as a persistent registration; `notheld` token (non-reentrance, replaces `panic_wp`); acquire post as a handle `∃c, c ↦ₐ (locked i c ∗ R c)`; owned points-to in the CS as `a ↦ₕ v` moved by owned load/store leaves along lobp; release gathers R's components at their own anchors through the fence; forwarded reloads (`fx_fwd_read`), fractional read handles for `ld x; ld x`. Private stack/cpu slots: **no ghost at all** — protocol σ's WOK (writer = owner) + a row fact ("latest earlier store") gives `reload = spill` as an annotation; `stack_own/cpu_own/kernel_text` are pure layout facts. Memory-content Iris invariants are fundamentally unavailable; ghost-only invariants unchecked.
- **Load-bearing vs graph-true:** Theorem 1's both conjuncts are graph-true given two correct rows (`AxSpinU3.u_distinct`, `AxLockSerial.cs_handoff_last`). Ownership is load-bearing for: Theorem 2's open C (demonstrated on hand nodes, `u_alloc_open` + race `ur3`), the private-slot reload values, the D4 facts (`Φ_cpu` racy read ≠ cpus_ptr i; holder's `lw lk ≠ 0`). The race/sanity certificate pairs exist at every hand level (Prot4/8, X7, U4, J2, Wit, H6/H7) — none yet on real code.
- **To make the lock usable by an arbitrary client:** Ixv6 is ONE fixed instance over a layout record with ONE lock and ONE R (`R_pid`); a new lock/resource means extending `prot_xv6`'s class table and re-proving `xv6_Hok` — no `newlock`. The generic owned interface is 1-byte; 4/8-byte leaves are instance-level and hand-node (`wpd_np_lw_x` etc. — positional versions not written). Phase-2b handle leaves live at `spin_ob6`, not Ixv6. The CPS per-function specs are caller-indexed positional lemmas, not `SpecF/LinkF` modules — SC-tier callers cannot link against them. Gap to the SC tier: zero SC-shaped whole-function specs; every `iInv`-using SC proof must be re-verified (owner D2) — the whole concurrency cone.

## 4. Remaining work to Theorem 1, then Theorem 2

Sizing by analogy (mycpu ≈ 9 files + 3 certs; holding 16; push/pop_off 19 — the three took ≈2 days of agent time).

| Piece | Size | Risk | Depends on |
|---|---|---|---|
| CertB for `amoswap.w.aq` at BFin (data page warm, fused RMW = 1 item) + `Xx_amo` via `XBkW` with `HnoSplitW`; RMW flow resources (`fx_claim/claim'/neutral`) | 3–5 files, 1.5–2.5k | M (replay `AxLeafS.CertXT_amoswap_S` at BFin; RMW-half states in `FamR_bound`) | — |
| `wpd_release` (21 instrs; holding_from_release′ + pop_off; `sd lk->cpu←0`, fence, `sw lk←0` WCrel; D4 `lw lk≠0` readback) | 12–18 files, 3–4k | M–H (release flag across boundary, §2(iii)) | fence-flag design |
| `wpd_acquire` with spin induction (push_off + k failed RMWs + claim + holding_from_acquire′ + `sd lk->cpu`), row shape over k | 15–20 files, 4–5k | H (Löb/▷ over prefix length; notheld in hand vs via handle on re-acquire) | CertB |
| allocpid body (15 instrs; positional 4-byte owned `lw/sw nextpid` leaves at Ixv6; pid readback through release's s1 spill) | 8–10 files, 2–3k | M | acquire, release |
| `allocpid_prefixes` + per-hart post (incl. panic-prefix rows ⇒ D4 field-read rule for noff; stop dropping mycpu annotations; value-level integrity conjunct) | 6–10 files, 2–3k | M–H (§2(ii)) | all WPds |
| Hdeps honesty bridge | 1–2 files, 0.5–1k | L–M | prefixes |
| Joint adequacy retarget to real rows / real layout (Σ fixed, `Hob_alloc` at the real `xlay`, HΨmid) | 3–5 files, 1–2k | M | prefixes |
| Certificates (a)(a-)(b)(c)(d): kvmmake-faithful table, cold warm-up then warm 2-hart drive (~623 events) via `graph_of_sc`; Hrow membership by vm_compute; 3-hart race C; Print Assumptions | 6–9 files, 3–4k | M–H (toolchain at scale; `va_first_read` shows in (d) unless assembled) | everything |
| `va_first_read` assembly (parallel) | 3–5 files, 1.5–2.5k | M (excluded arms) | — |
| **Theorem 2** delta: HwpC at a real-layout L3, issued-fragment readback (J2 shape exists), certs (a′)(b)(c′)(d) | 3–5 files, 1–2k | L–M | Theorem 1 |
| Row-integrity theorem (drop Hrow) | 15–25 files | **H** — needs a phase-2 fact (reload = spill) to pin a phase-1 fetch; likely a prefix-indexed adequacy (`AxWpcAdeq` residual: checkpoints need prefix graphs) | Theorem 1 |
| Interrupts-on push_off entry (+ kernelvec/sret rows) | 20+ files | **very H** | out of plan scope |

**Estimate.** Instruction coverage 77/139 (55%) but the undone 45% carries all the lock-protocol content. Theorem 1 on real code: **~45% by volume, ~40% risk-weighted**; ≈10–13 agent-days at the recent tempo. Theorem 2: +≈2–3 days after Theorem 1 (shape already proved on hand nodes). "Verified spinlock" in the ordinary sense (Hrow removed, interrupts-on entry): **~25–30%**, with the row-integrity theorem unstarted and the highest-risk item.

**Critical path:** amoswap CertB → acquire (spin induction) → allocpid body → allocpid_prefixes + D4 field-read rule → joint retarget → certificate (a) at scale → (d) [va_first_read assembly in parallel] → Theorem 1 → Theorem 2.

## 5. Top risks / where the plan may be wrong

1. **Hrow does most of the work.** With `MaybeStuck`, a diverted hart is trivially verified; today's results read "if hart i emits exactly this event row, then …". The row-integrity theorem is the real content and may hit the same F1 obstruction (phase-2 facts needed in phase 1), forcing a prefix-indexed adequacy — not in the plan's cost model.
2. **Conjunct 1 (no panic) may not be provable as stated.** Row-excluded arms give stuckness, not refutation; the private class has no value ghost, so `noff ≥ 1` must come from a WOK + row-fact chain through push_off's store — a new rule family, and push/pop_off currently drop the annotations it would need.
3. **Release's WCrel across the instruction boundary** in the positional engine is undesigned (fixed once on a retired surface).
4. **`va_first_read`** is a family of Sail claims with named excluded arms; the Hinj restriction already had to be fixed once (canonical VAs). Vacuity exposure if `va_rd` is mis-shaped.
5. **Modularity.** A single fixed instance, hand-node word leaves, no `newlock`, no spec modules: the step from "allocpid verified" to "the SC kernel's lock users re-verified" is months, and the plan's Theorem 2 does not shrink it.
6. **Check-time pressure.** 570 s limit forced 16–19-file splits for 20-instruction callees; acquire/release/allocpid compose all of them — expect more plumbing files and more spurious timeouts.
7. **HAD/explicit-walker model** is accepted but its removal route is unproved; Theorem 2's "arbitrary verified C" cannot be page-table-mutating code.
