# Layer 2 — the transfer theorem, designed as a DIRECT acyclicity theorem (2026-08-18)

**Status: DESIGN (orchestrator).  Supersedes the "Ψ ⇒ main_premises′" framing
of [`weak-memory-deps.md`](weak-memory-deps.md) §4.2 and Track B of
[`weak-memory-premise-discharge.md`](weak-memory-premise-discharge.md).
D2/D3 (dependency tracking) are LANDED; A0/A0′ (relativized premises)
LANDED; the forward bank fixed (D-7).  This file says what Layer 2 must
prove, in what shape, and what remains a site fact.**

## 1. Why the per-edge premises are the wrong INTERFACE (even relativized)

`edges_split` (per cross-rf edge, every later fulfil), `edges_split_ms`
(A0: only milestone-source fulfils, coverage at the fulfil's EXT view) and
`ee_ok` are SUFFICIENT conditions for the milestone-measure walk
(`WeakRobustAcyc2`), stated per edge so as to carry no cycle quantifier.
But xv6 has harmless edges that violate ANY per-edge form:
- `holding()`'s plain lock read before the acquire RMW (A0 fixed that one:
  the RMW is the next fulfil and its own aq read covers).
- **The walker's A/D CAS traffic** (kernel page table shared by all harts;
  `WCexcl` messages by hart k's walker CAS, read by hart j's later walk):
  j's next milestone-source store `f` may be promised below `ts_CAS`
  (nothing in RVWMO orders an implicit walk read before a later
  unrelated store), so `ts_CAS < ts_f` fails — yet no cycle can pass
  through it (k's CAS is po-before k's own data access, so k cannot read
  `f` before its CAS).
The walk consumes edge facts ONLY for readers ON A CYCLE
(`WeakRobustMain.rf_edges_ok_on TS W`, `gdep2_acyclic_on` for any `W`
closed under mutual reachability).  So the honest Layer-1 interface is:

**Layer 2 proves `gdep2_acyclic TS` (and the other conclusions of the
premise package) DIRECTLY, by minimal-cycle analysis, and Layer 1 exposes
`robust_main` in a form that consumes those conclusions.**  The per-edge
premises stay as proven sufficient conditions (useful for litmus/small
programs), not as the theorem's hypothesis.

## 2. The Layer-1 interface to build (A0″, small)

- `on_cyc TS e := tc (gdep2 TS) e e` (closed under mutual reachability);
  `edges_split_cyc nh TS DS` := `edges_split_ms` restricted to readers
  `e2` with `on_cyc TS e2` — the weakest per-bundle form; prove
  `edges_split_ms → edges_split_cyc` and re-land `gdep2_acyclic_main` on
  it via `rf_edges_ok_on_ms` at `W := on_cyc` (`gdep2_acyclic_on` at that
  `W` gives "no cycle through an on-cycle event" = `gdep2_acyclic`).
- `robust_main_acyc`: `robust_main` with the graph obligations replaced by
  their CONCLUSIONS — `gdep2_acyclic TS` (or the pointwise
  `¬ tc gdep2 e e` the cone needs), `∀ a, co_tc TS a`, `dev_wit_ok`,
  and the bad-edge handling (`bad_wf` or, better, `no_bad_edge` derived
  from φ) — so that Layer 2 can discharge them one by one.  `robust_main`
  becomes a corollary (`main_premises ⇒ those conclusions`, all existing
  lemmas).

## 3. What Layer 2 proves, and from what

Given a canonical bundle `(TS, DS)` of a full behavior, `pf_violation_free_hart`
(φ, exported), an exported pf-state predicate Ψ (§5), and the machine.

**Theorem L2-acyc: `gdep2_acyclic TS`.**  By contradiction: take a cycle
of minimal length (finite graph — `WeakRobustMain`'s `gev_enum`).  Because
`gpo` is program order (transitive), a minimal cycle visits each agent in
ONE po-segment `[h_j .. f_j]`: `h_j` entered by a cross edge (rf from a
fulfil `v` at timestamp µ, or `gE`), `f_j` a fulfil that is the next
milestone's source.  The measure walk (`mile_mu`) closes if for every
segment `µ_entry < ts(f_j)` (S1).  Cases, per segment, in the FULL trace:
- **(C1) fence** `pr∧sw` between `h` and `f`: `disciplined` — trace fact,
  S1 by the machine.
- **(C2) aq entry** (`h` is an aq read / aq RMW): S1 by the machine.
- **(C3) dependent exit** — `f`'s EXT view includes a register/`vcap`
  chain from `h`'s result (`LRegW rd [DLdRes]` … `LCtrl`/`vsrc`/`asrc` at
  `f`): S1 by the machine (NEW lemma `fcov_of_dep_chain`, D2's rules).
  With D3 this covers every store control-dependent on a branch that
  depends on `h` (`while(started==0)`, `if(holding) panic`, every CS
  store after a lock spin), i.e. all of xv6's racy sites.
- **(C4) covered exit** — `j` acquired (aq read / read+fence, po-before
  `f`) a message `ts_a` above a release `ts_r` of `v`'s agent that is
  po-after `v` with a `pw∧sw` fence between (or an A2 chain): S1 by
  Track A1/A2 (`fcov_of_acquire_before`, `covered_of_release_chain`).
- **(C5)** the entry message is `bad` (owned, unpublished): the minimal
  bad edge's cone is pf-real and φ refutes it (`bad_edge_violates`,
  existing).
- **(C6) the residue**: none of the above.  §4 says what closes it.

**Theorem L2-co: `∀ a, co_tc TS a`** (write serialization): from
`ptraces_bytes_ok` as today (A4: RMW-only bytes; single-writer bytes;
handoff chains) — the byte classification is the one site fact that is a
genuine PROPERTY OF THE PROGRAM's memory layout, see §4.

**L2-dev: `dev_wit_ok`** — a `gdep2` path from a later fabric access to an
earlier one needs a backward-in-behavior-time rf edge (a promise read)
across a fabric access; C1–C4 at that segment give the same S1 inequality
and contradict the witness order (details to be worked out; the segment
structure is the same as L2-acyc's).

## 4. The residue (C6), and the pf-realness argument that shrinks it

At a minimal cycle, the strict ancestry `U` of the cycle is acyclic and
pf-replayable, so every segment head `h_j` has a pf-real PRE-state σ_h
(the pool holds `j`'s residual monad, so σ_h names the instruction).  Two
consequences that are THEOREMS about traces (to be mechanized as the core
of L2-acyc):
- **Lock-mediated reads cannot be cycle entries.**  If `h` is a plain read
  of byte `b` whose message `m` (author `i`) sits inside `i`'s critical
  section of lock word `L` (`ts_i(acq) < ts_m < ts_r(i)`, RMW-only lock
  word, so `excl_ok` totally orders the CS windows), and `j`'s read `h`
  sits inside `j`'s CS of `L` with `j`'s acquire pf-real, then `i`'s
  release is in `U`, hence `m` is in the pf log, hence `h` is NOT an early
  read and its rf edge cannot come from the cycle: the entry into `j`
  must be `j`'s ACQUIRE (aq, C2) or earlier.  If `j`'s CS is BEFORE `i`'s
  in gmo, `h` reading `m` early contradicts the release fence between `h`
  and `j`'s release (EXT).  So for lock-protected bytes, C1–C5 are
  exhaustive PROVIDED the two site facts hold: **(SF-1)** `m` was written
  inside its author's CS of `L` and `h` read inside the reader's CS of the
  SAME `L`.
- **Sync bytes** (lock words, `started`/`first`, the disk's used index,
  PTE A/D bits): entries are aq RMWs (C2), or plain reads followed by a
  dependent branch/fence (C1/C3), or walker reads whose later stores are
  never on a cycle through the CAS (the A/D structural fact — to be
  proved: k's CAS precedes k's data access in po).
- **Private bytes** (single-agent): no cross edges.
So the residue is exactly the ownership discipline of the byte: **(SF-1)
lock protection per edge, (SF-2) the sync-byte discipline per site, (SF-3)
the byte classification** — the same three facts the M6 design called
"Layer 2 site facts".  They are NOT machine-visible.

## 5. Ψ — what the pf side can export, and how it supplies SF-1/2/3

Ψ is exported at every pf-reachable state, like φ, from `weak_state_interp`.
What is expressible without ghost history: (i) the READ WATERMARK
`w_rdw` (inert `wstate` field: max ts of plain foreign reads since the
last `pr∧sw` fence) with the invariant "no fulfil with EXT view <
`w_rdw`" — this is S1 as a pf-state invariant and covers C1/C3-shaped
sites; (ii) a per-hart "in CS of lock word `L`" inert component
`w_lock : option Z` set by an aq RMW on `L` (the acquire) and cleared by
the release store to `L` — MACHINE-computable (the RMW's byte address is
in the label), and gives "j's read/store of b happened while j held L"
as a trace fact; (iii) SF-1 then needs "b is protected by L", which is
NOT machine-computable — the honest options: (α) an explicit per-image
side condition (a byte→lock map for the kernel's shared data, checked
against the WP proof's lock ownership — D-M6-8's decision), or (β) a
GHOST byte→lock map in the state interpretation whose evolution is tied
to the release/acquire leaves and exported per state, plus a
monotonicity lemma making the per-state exports coherent along a trace.
⚑ **Decision for the user**: (α) now, (β) as the upgrade — or (β)
directly.  Everything else in §3–4 is machine work.

## 6. Staging

- **A0″** (Layer 1, small): `on_cyc`, `edges_split_cyc`, `robust_main_acyc`.
- **L2-M1** (Layer 1, machine facts): `fcov_of_dep_chain` (C3),
  `S1_of_fence`/`S1_of_aq` restated for the segment shape, the CS-window
  lemma (mutual exclusion from `excl_ok` on an RMW-only lock word), the
  "lock-mediated read is not an early read" structural lemma over
  `U`-pf-realness (uses the exhibit's replay of `U`), the A/D CAS
  structural fact.
- **L2-M2**: the minimal-cycle skeleton (`gev_enum`, minimal length,
  one-segment-per-agent via `gpo` transitivity), the case split, L2-acyc
  under SF-1/2/3 as explicit hypotheses.
- **L2-M3**: `w_rdw`/`w_lock` in the machine + the export; SF-2 from the
  export; L2-co from `bytes_ok`; L2-dev.
- **L2-M4**: SF-1/SF-3 by (α) or (β) per the decision.

## 7. LANDED (A0″, L2-M1) — 2026-08-18

Whole tree green; `Print Assumptions` unchanged (`robust_main` closed,
`WeakEvCapstone.xv6_ev_weak_robust` at the 5 rv64d axioms);
`WeakRobustL2.v` closed under the global context; no `Admitted`/`Axiom`.

### 7.1 A0″ — the cycle-relativized interface (`iris/WeakRobustMain.v`)

```coq
Definition on_cyc TS (e : gev) : Prop := tc (gdep2 TS) e e.

Lemma on_cyc_mr TS u x :
  on_cyc TS u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → on_cyc TS x.

Definition edges_split_cyc nh TS DS : Prop :=          (* = edges_split_ms + [on_cyc TS e2] *)
  ∀ e1 e2 T ts a k' ev',
    gev_ts TS e1 = Some ts → gev_reads TS e2 a ts → e1.1 ≠ e2.1 →
    on_cyc TS e2 →                                     (* ← THE ONLY ADDITION *)
    pt_trs TS !! e2.1 = Some T → (e2.2 < k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    (∃ y, gmile TS (e2.1, k') y) →
    edge_ok_f T e2.2 k' ts ∨ bad nh TS DS e1 e2.

Lemma edges_split_ms_cyc          : edges_split_ms nh TS DS → edges_split_cyc nh TS DS.
Lemma edges_split_edges_split_cyc : ptraces_wf pstep TS → edges_split nh TS DS →
                                    edges_split_cyc nh TS DS.
```

The relativization costs NOTHING, and that is the point:

```coq
Theorem gdep2_acyclic_on_cyc TS (W : gev → Prop) :
  ptraces_wf pstep TS → ptraces_fwd_own TS →
  rf_edges_ok_on_ms TS (λ e, W e ∧ on_cyc TS e) → ee_ok TS →
  (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
  ∀ e, W e → ¬ tc (gdep2 TS) e e.
```

The walk's only consumer of the premise (`mile_mu_gain_on`) is reached
only from `on_cycle2_advance_on`, whose `on_cycle2_on` carries
`mile_mu TS mu v u ∧ rtc (gdep2 TS) u v` — i.e. a cycle THROUGH the
reader `u`.  So `W` may always be intersected with `on_cyc` (which is
itself closed under mutual reachability, `on_cyc_mr`), and at the
conclusion's `e` the cycle hypothesis IS the extra conjunct.  Everything
below runs through this one lemma.

Re-landed on `edges_split_cyc`, statements otherwise VERBATIM:
`rf_edges_ok_on_min` (now at `W ∩ on_cyc`), `cone_acyc2_of_min`,
`cone_acyc_of_min`, `cone_acyc_of_min_nil`, `gdep2_acyclic_bad_free`,
`gdep2_acyclic_main`, `gdep3_acyclic_main`, `main_premises`,
`main_premises_nil`, and — as pure pass-through of a WEAKER premise —
`WeakComposeLang.tb_facts` and the four `Hsplit` section contexts of
`WeakRobustCone`/`WeakSailCone`.  `robust_main`, `robust_main_bundle`,
`robust_transport` and `WeakEvCapstone.xv6_ev_weak_robust` keep their
statements; `main_premises` got strictly weaker, so every supplier owes
less.

### 7.2 `robust_main_acyc` — the acyclicity-consuming entry point

```coq
Lemma robust_main_acyc img d0 ps c mid TS DS :
  lat_free_prog pstep → ts_oblivious pstep → pcls_obl pcls →
  rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
  ptraces_dev_of pstep pdev TS DS mid c →
  (∀ p m i, pc_log mid !! p = Some m → wm_tid m = Some i →           (* fulfil accounting *)
     ∃ T, pt_trs TS !! i = Some T ∧
       (∃ k ev, at_evs T !! k = Some ev ∧ ae_ts ev = Some (S p)) ∧
       (∀ k1 k2 ev1 ev2, at_evs T !! k1 = Some ev1 → ae_ts ev1 = Some (S p) →
          at_evs T !! k2 = Some ev2 → ae_ts ev2 = Some (S p) → k1 = k2)) →
  (∀ a, co_tc TS a) →                                                 (* L2-co *)
  gdep3_acyclic TS DS →                                               (* L2-acyc + L2-dev *)
  cls_canonical pcls TS →
  ∃ cf, rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
```

THE EXACT HYPOTHESIS LIST — ten, in order: `lat_free_prog pstep`,
`ts_oblivious pstep`, `pcls_obl pcls`, the promise run to `mid`, the
traced/fabric decomposition `ptraces_dev_of`, the FULFIL ACCOUNTING,
`∀ a, co_tc TS a`, `gdep3_acyclic TS DS`, `cls_canonical pcls TS`.
(The accounting is genuinely consumed — `ptraces_of_writes_fulfilled`
needs it; it was NOT dead weight in `robust_main_bundle`.)

WHAT DISAPPEARS relative to `robust_main_bundle`: the whole graph
package (`edges_split_cyc`, `bad_wf`, `ee_ok`, `dev_wit_ok`,
`ptraces_bytes_ok`), `pf_violation_free_hart`, and the hart count `nh` —
they enter only through `gdep3_acyclic_main` and `co_serialized_pkg`,
both of which `robust_main_bundle` now calls before delegating.
`robust_main_bundle` is proved as a corollary (same statement), and
`robust_main`/`robust_transport` through it.

### 7.3 L2-M1 — `iris/WeakRobustL2.v` (new, after `WeakRobustDisc.v`)

Generic over `{P D}`, `pstep`, `TS` with `ptraces_wf pstep TS` and
`ptraces_fwd_own TS`; nothing else.

**The D2 view layer** (`Section astep`, one case per label):
`astep_ok_regv_ne` (only an `LRegW rd _` moves `regv rd`),
`astep_ok_regw_eq` (`regv rd := V(srcs)`), `astep_ok_ldv_ge` (`w_ldv`
only grows except at `LInstr`), `astep_ok_read_ldv` (an UNFORWARDED read
banks its timestamp in `w_ldv` — `DLdRes`), `astep_ok_ctrl_vcap`,
`astep_ok_read_nowrites` (`readable`'s floor at the agent's own `coh`),
`astep_ok_read_fulfil_coh` (an rmw's fulfilled timestamp lands in the
`coh` of the byte its READ half named).  Supporting `wstate` lemmas:
`fulfil_vext_vcap`, `fulfil_vext_srcs` (EXT dominates `w_vcap` and the
label's own `asrc`/`vsrc` views — RVWMO ppo 9/10/11), `srcs_view_ge`,
plus the `w_regv`/`w_ldv` fold lemmas for `load_post_run_d` /
`store_post_run_d` / `ctrl_post` / `fence_post` / `instr_post`.

**C3 — the dependent exit** (the headline).  Carriers
`ldcarry T k ts` (`w_ldv ≥ ts`), `rcarry T k r ts` (`regv r ≥ ts`),
`vcapat T k ts` (`w_vcap ≥ ts`), and the two NAMED windows the D2
non-monotonicity forces: `no_instr T k1 k2` and `no_regw T k1 k2 r`.

```coq
Lemma ldcarry_of_read   : (a,ts) ∈ lb_reads (ae_lb evr) → read_unforwarded Log i _ ts →
                          ldcarry T (S kr) ts
Lemma ldcarry_mono      : no_instr T k1 k2 → ldcarry T k1 ts → ldcarry T k2 ts
Lemma rcarry_of_ldres   : ae_lb ev1 = LRegW rd srcs → DLdRes ∈ srcs →
                          ldcarry T k1 ts → rcarry T (S k1) rd ts
Lemma rcarry_of_regw    : ae_lb ev  = LRegW rd srcs → DReg r ∈ srcs →
                          rcarry T k2 r ts → rcarry T (S k2) rd ts
Lemma rcarry_mono       : no_regw T k1 k2 r → rcarry T k1 r ts → rcarry T k2 r ts
Lemma vcapat_of_ctrl    : ae_lb evc = LCtrl srcs → DReg r ∈ srcs →
                          rcarry T kc r ts → vcapat T (S kc) ts
Lemma vcapat_mono       : (w_vcap IS in ws_le — no window needed)
Lemma fcov_of_vcap      : vcapat T kc ts → kc ≤ k' → is_Some (ae_ts ev') → fcov T k' ts

Theorem fcov_of_ctrl_dep : … LCtrl on the chain's register at kc < k' … → fcov T k' ts
Theorem fcov_of_data_dep : DReg r ∈ lb_asrc (ae_lb ev') ∨ DReg r ∈ lb_vsrc (ae_lb ev') →
                           rcarry T k' r ts → fcov T k' ts
Theorem regv_of_dep_chain : rcarry T k r ts → rchain T k r hs →
                            rcarry (rchain_end k r hs).1 (rchain_end k r hs).2 ts
Theorem fcov_of_dep_chain : load at kr → LRegW rd0 [… DLdRes …] at k0 (no_instr between)
                            → register chain hs → LCtrl at kc → fulfil at k' > kc
                            → fcov T k' ts
```

`rchain`/`rchain_end` are the `WeakRobustDisc.chain_ok`/`chain_end`
idiom over `list (nat * wreg)`; the NO-OVERWRITE side condition is
explicit inside `rchain`, because `regv` is not monotone (the D2
finding) — the view has to be tracked per register between the writes.
`no_instr` is the analogous window for `DLdRes`: the load-result bank is
reset by `LInstr`, so the register write that consumes it must sit in
the SAME instruction as the load.

**C1/C2 in the segment's coordinates**: `S1_of_disciplined` — a foreign
entry read at `h` that is `aq`, or followed by a `pr∧sw` fence before
`kd ≤ kf`, has `ts < ts_f` at the segment's exit fulfil.  (The agent
record at `kd` is derived, not supplied.)

**The rmw co-chain**: `writes_b_po_lt` (same agent, same byte, later
trace index ⟹ later timestamp) and

```coq
Theorem rmw_reads_pred L e tr t e' t' :
  gev_reads TS e L tr → gev_ts TS e = Some t → writes_b TS L e' t' →
  ¬ ((tr < t')%nat ∧ (t' < t)%nat).
```

— every rmw reads the write IMMEDIATELY BELOW its own.  Foreign writes
in the window die by `excl_ok` (`WeakRobustSer.gev_read_fulfil`); own
writes below by `readable`'s `coh` floor (`astep_ok_read_nowrites`) and
own writes above by the rmw's own coherence gain
(`astep_ok_read_fulfil_coh`).

**The CS windows**:

```coq
Definition cs_window L i ka kr t_a t_w t_r :=
  gev_reads TS (i,ka) L t_a ∧ writes_b TS L (i,ka) t_w ∧
  (ka < kr)%nat ∧ writes_b TS L (i,kr) t_r.
Definition win_excl L i t_w t_r :=
  ∀ e t, writes_b TS L e t → e.1 ≠ i → ¬ ((t_w < t)%nat ∧ (t < t_r)%nat).

Theorem cs_windows_ordered … : i ≠ j → cs_window L i … → cs_window L j … →
  win_excl L i tw_i tr_i → win_excl L j tw_j tr_j →
  (tr_i ≤ ta_j)%nat ∨ (tr_j ≤ ta_i)%nat.
```

⚠ **FINDING — §4's "excl_ok totally orders the CS windows" is WRONG.**
`excl_ok` makes the RMW ITSELF atomic (no foreign write between its read
and its write); it says nothing about the interval between an agent's
acquire and its release.  A coherence order that INTERLEAVES two
windows (`t_w(i) < t_w(j) < t_r(i) < t_r(j)`) violates no rule of the
machine — mutual exclusion is a statement about the lock word's VALUES,
which Layer 1 never inspects.  Disjointness is therefore SF-1 itself and
enters as the named premise `win_excl`.  What IS machine-derivable, and
is what `cs_windows_ordered` proves from it, is the strengthening
`t_r(i) ≤ t_a(j)`: given disjointness, `rmw_reads_pred` upgrades "i's
release precedes j's acquire write" to "j's acquire READS at or above
i's release", which is the inequality the coverage argument needs.
(A second small machine fact used here: two writes of a byte at the same
timestamp have the same author, via `writes_b_author`.)

**The lock-mediated read**:

```coq
Theorem cs_read_covered        : j's acquire is [aq] and read ta_j ≥ ts_m ⟹ covered Tj h ts_m
Corollary cs_read_covered_window : the same with the two windows and win_excl in front,
                                   the inequality supplied by cs_windows_ordered
Theorem cs_read_before_absurd  : j's window BEFORE i's ⟹ ts_m < tr_j ≤ ta_i < ts_m, absurd
```

so under SF-1 a plain critical-section read is ALWAYS covered or
contradictory — the design's §4 claim, in trace terms, with no
pf-realness anywhere.

**The A/D CAS structural fact**: `gpo_no_return` (premise-free:
`¬ gpo TS d c` when `c` is po-before `d`) and
`no_gdep2_back_to_po_pred` (under `gdep2_acyclic`, no `gdep2` path from
a po-later event of the same agent back to `c`).

### 7.4 What L2-M1 did NOT close

- **C4/C5** are already Layer-1 lemmas (`WeakRobustDisc`'s Track A,
  `bad_edge_violates`) — nothing was owed.
- **C6 / SF-1** stays a site fact, now with a machine-checked NAME
  (`win_excl`) and a machine-checked consequence (`cs_windows_ordered`).
  §5's ⚑ decision (α vs β for the byte→lock map) is untouched.
- **SF-2, SF-3** untouched (L2-M3's `w_rdw`/`w_lock` exports).
- **L2-M2** (the minimal-cycle skeleton: `gev_enum`, minimal length,
  one-segment-per-agent, the case split, L2-acyc under SF-1/2/3) is the
  next stage; A0″ and `robust_main_acyc` are exactly the interface it
  targets, and C1/C2/C3 are now available to it as machine facts.
- **`ldcarry_of_read` still takes `read_unforwarded`** (as every
  Track-A lemma does); `WeakRobustDisc.foreign_ts_unforwarded` discharges
  it for any cross-agent edge, which is the only case a cycle segment
  has.


## 8. NO SIDE CONDITIONS — the certification route (2026-08-18, after the user's veto of SF-1/2/3)

The user rejects any manual side condition; SF-1/2/3 must come from the WPs.
The mechanism that makes this possible is CERTIFICATION, and the reason it
was invisible so far is that our full machine has unconditional promises:

- PARM proves `Machine.exec p m ↔ certified_exec p m`
  (`lcertify/CertifyComplete.v: certified_exec_equivalent`; the completeness
  direction is `interference_certify`, RISC-V's "certification survives
  memory extension"), and `axiomatic_to_promising` builds `Machine.exec`.
  So the CERTIFIED promising machine has exactly hardware's behaviors, and
  we may reason as if every outstanding promise in a behavior is
  certifiable at every point by a THREAD-LOCAL PROMISE-FREE run.
- Consequence for Layer 2: at a segment head `h` (pf-real pre-state, §4)
  reading a promise `m` of agent `i` EARLY, extend the pf-real prefix with
  `i`'s certifying run (a pf run: it fulfils `m` at the pf top) and then
  `h`'s read of `m` IS a pf read (`readable` at the top).  So EVERY read the
  full machine performs, early or not, is a read of some pf run — and φ
  and every WP-exported invariant apply to it.  In particular an early read
  of an OWNED message that its author has not yet published is a φ
  violation of a pf-reachable configuration — IMPOSSIBLE.  SF-1 (the
  byte→lock map) is not needed at all: no per-byte logging, no ghost map.
- Sync bytes: lock words (RMW aq entries, `holding()` covered by the RMW's
  own read — machine facts), `started`/`first` (control-dependent branch +
  fence — machine facts after D2/D3), the disk's used index (fence after the
  read — trace fact).  Mutual exclusion in gmo, which `excl_ok` alone does
  not give (§7), follows from the RECORDED VALUES: RMWs write 1, releases
  write 0, an RMW reads its co-predecessor, and an agent's CS events exist
  only after an RMW that READ 0 (the program branches on it) — a trace
  theorem given the lock word's value protocol, which the tree's lock
  invariant (`wlockN`) already establishes and adequacy can export.
- What this costs (the new plan of record, replacing L2-M3/M4):
  **D8 — certification in the full machine**: `WPPromise` becomes a
  CERTIFIED promise (a thread-local `wp_pf`-style solo run fulfils all of
  the agent's outstanding promises), plus OUR proof that the uncertified
  behaviors are certified behaviors (a port of `CertifyComplete` +
  `interference_certify`; the RISC-V-specific view arithmetic it uses —
  the SC-result view `RES = ts` — is exactly D-2's missing component, so
  D8 likely has to add the AMO's own write timestamp to the aq raise; to
  audit against RVWMO ppo 5); **E1 — the extended exhibit**: replay
  `U ++ certifying runs ++ the early read` as a pf run (the cone replay
  plus solo runs); **L2′** — the case analysis with the extended pf runs:
  φ refutes early reads of owned-unpublished messages; sync bytes by
  machine facts + the exported lock-word protocol.
- OBSTACLE found while checking the acyclicity route against xv6: the
  hardware walker's A-bit CAS may be performed EARLY (speculatively) — a
  full-machine RMW promise — and a walk of another hart may read it; with
  a lock-mediated data flow back this forms a REAL `gdep2` cycle
  (`c1 →rf→ j-walk →po→ f →rf→ k-read →po→ c1`) whose behavior IS robust
  (the pf twin has j's walker set the A bit itself: same final program
  states and memory, DIFFERENT events).  So `gdep2_acyclic` is SUFFICIENT
  for robustness but can be FALSE for xv6 with speculative A/D updates,
  and any acyclicity-based proof is inapplicable to those behaviors.  To
  resolve: (a) check the privileged spec on speculative A/D setting; if the
  ISA forbids early A/D updates, make the walker's CAS non-promisable
  (append-at-fulfil) in the full machine — a machine change with a
  containment argument; (b) otherwise generalize the exhibit to replay
  walker A/D updates up to idempotence (the pf twin performs the CAS
  itself).  Neither is a side condition; both are model/theorem work.

## 9. LANDED (L2-M2) — 2026-08-18

Whole tree green; `Print Assumptions` UNCHANGED (`robust_main` closed under
the global context, `WeakEvCapstone.xv6_ev_weak_robust` at the five `rv64d`
axioms); every new theorem of `iris/WeakRobustL2b.v` closed under the global
context; no `Admitted`/`Axiom`; `lemma_diff --ref 212a5edd` shows additions
only.  New file `iris/WeakRobustL2b.v` (≈1050 lines), after
`WeakRobustL2.v` in `_CoqProject`; nothing else in the tree depends on it,
which is why the two capstones cannot have moved.

### 9.1 The SCC skeleton (§1 of the file)

Generic in a DECIDABLE edge relation `R` on `gev` with
`Rwf : ∀ x y, R x y → gev_wf TS x ∧ gev_wf TS y` and (for the head lemmas
only) `Rpo : ∀ x y, gpo TS x y → R x y`.  Instantiated at `gdep2 TS` (the
design's names) and at `gdep3 TS DS` (what the replay needs — §8.2).

```coq
Definition sccR   R e f := rtc R e f ∧ rtc R f e.
Definition oncycR R e   := tc R e e.                 (* = WeakRobustMain.on_cyc at gdep2 *)
Definition sanc TS R e  := anc R (gev_enum TS) e.    (* the COMPUTED ancestor closure *)

Definition sccR_min TS R f :=                        (* MINIMAL IN THE SCC DAG *)
  ¬ Exists (λ x, oncycb TS R x ∧ tcb TS R x f ∧ ¬ sccb TS R f x) (gev_enum TS).

Definition Uanc TS R f x := tcb TS R x f ∧ ¬ sccb TS R f x.     (* the design's U *)
Definition scc_headR TS R f h :=
  sccR R f h ∧ ∀ k, (k < h.2)%nat → ¬ sccR R f (h.1, k).
```

**Everything is decidable through `anc`.**  `tc R x y` holds iff some
`R`-successor of `x` lies in `anc R (gev_enum TS) y` — an `Exists` over a
computed list (`tcb`/`tcb_iff`); `rtcb`, `sccb`, `oncycb` follow, and
`sccR_min` is stated as the negation of a decidable `Exists` so that the
DECISION and the WITNESS EXTRACTION (`dec_stable`) are both free.  No
classical axiom, no `Finite` instance beyond `gev_enum`.

**Existence** (`sccR_min_exists : oncycR R e → ∃ f, oncycR R f ∧ sccR_min TS R f
∧ rtc R f e`) is a descent on `length (sanc TS R e)`: if `e` is not minimal
there is an on-cycle `x` with `tc R x e` and `¬ rtc R e x`, and then
`sanc x ⊊ sanc e` — every ancestor of `x` is an ancestor of `e`
(`sanc_incl`), `e ∈ sanc e`, and `e ∉ sanc x` (it would give `rtc R e x`) —
so `e :: sanc x` is a `NoDup` sublist of `sanc e` and the measure drops
(`sanc_len_lt`).

**`U` is acyclic and downward closed.**  `Uanc_not_oncyc`/`Uanc_acyc`: at a
MINIMAL component nothing in the strict ancestry is on a cycle (else
`sccR_min_spec` would put it in the component).  `Uanc_dc` /`Ustrict_dc` /
`Ustrict3_dc`: `dc TS R (Uanc TS R f)`.  `scc_headR_exists` builds the
least-index event of an agent in the component; `scc_headR_po_pred` shows
every po-predecessor of a head is in `U` (`Rpo` + head minimality);
`scc_headR_not_U` that the head itself is not.

The `gdep2` names the design asked for: `scc`, `scc_min`, `Ustrict`,
`scc_min_exists`, `Ustrict_not_on_cyc`, `Ustrict_acyclic`, `Ustrict_dc`,
`Ustrict_wf`.

### 8.2 FINDING — the head-prestate replay runs on `gdep3`, not `gdep2`

`WeakRobustSim.Qinv_step` demands that every **`gdep3`** predecessor of the
event being replayed is already processed (the fabric clause: a
fabric-touching event must be handed the fabric it recorded).  A `gdep2`-only
`U` is NOT `gdep3`-downward-closed, so the SCC skeleton the replay consumes
has to be the `gdep3` one: `scc3`, `scc_min3`, `Ustrict3`, and the
`gdep3` instances of every lemma above.  The two graphs agree on WHICH
EVENTS ARE ON A CYCLE — `on_cyc_gdep3 : ptraces_wit → dev_wit_ok →
(oncycR (gdep3 TS DS) e ↔ on_cyc TS e)`, the ⇒ direction being A0′'s
`gdep3_acyclic_at_wit` — but they need NOT agree on the components, and
nothing below assumes they do.

### 8.3 The generalized cone replay, and `head_prestate_pf_real`

`WeakRobustMain.cone_Qinv` replays the `gdep3`-ancestry of ONE root and
needs that root OFF every cycle (`Hrr`, `Hconeacyc`) — which a segment head
is not.  `U_Qinv` is the minimal generalization, same proof with the cone
replaced by an abstract set:

```coq
Theorem U_Qinv (U : gev → Prop) `{!∀ e, Decision (U e)} :
  (∀ e, U e → gev_wf TS e) → dc TS (gdep3 TS DS) U →
  (∀ e, U e → ¬ tc (gdep3 TS DS) e e) →
  ∃ order, Qinv pstep pcls TS DS img d0 ps order ∧
           (∀ e, e ∈ order ↔ (gev_wf TS e ∧ U e)).
```

(`Ured TS DS U := gdep3 ∩ U²`, `topo_sort` at `gev_enum_S TS U`, the same
`Qinv_step` prefix induction.  `cone_Qinv` is the instance at
`U := Ucone`; it was left untouched.)

```coq
Theorem head_prestate_pf_real f h T :
  oncycR (gdep3 TS DS) f → sccR_min TS (gdep3 TS DS) f →
  scc_headR TS (gdep3 TS DS) f h → pt_trs TS !! h.1 = Some T →
  ∃ order cf agn,
    Qinv pstep pcls TS DS img d0 ps order ∧
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ Uanc TS (gdep3 TS DS) f e)) ∧
    rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
    pc_img cf = img ∧ pc_log cf = pf_log TS order ∧
    at_ags T !! h.2 = Some agn ∧
    pc_ags cf !! h.1 = Some (WPAgent (pa_st agn)
      (aevs_post (pi TS order) (take h.2 (at_evs T)) ws_init) ∅).
```

The positioning fact is `nproc_of_po_prefix`, NOT `WeakRobustSim.nproc_cur`:
`nproc_cur` asks for EVERY `gdep2` predecessor of the event to be processed,
and a segment head's cross-agent rf predecessor is ON THE CYCLE, hence not in
`U`.  `nproc` counts only the agent's own events, so the po-prefix suffices —
that is the whole content of the replacement (six lines, `qorder_mem` twice).

`cycle_min_scc_heads` packages §1+§2 end to end: from ANY `on_cyc TS e0`, a
minimal `gdep3` component none of whose strict ancestors is on a cycle, and,
for every agent with an event in it, its head `h` together with a pf-run
whose agent `h.1` sits at `at_ags T !! h.2`.

### 8.4 FINDING — C5 cannot be discharged inside the SCC (`scc_no_bad`)

Machine-checked, one line:

```coq
Lemma bad_min_not_on_cyc nh TS DS e1 e2 :
  bad nh TS DS e1 e2 → bad_min nh TS DS e2 → ¬ on_cyc TS e2.
```

`WeakRobustMain.bad_edge_violates` takes `bad_min nh TS DS b2` and its FIRST
use of it is at the bad edge itself, yielding `¬ tc (gdep3 TS DS) b2 b2`: the
exhibit replays the STRICT `gdep3`-ancestor cone OF THE READER and then
appends the reader, so an on-cycle reader is its own ancestor and the replay
is circular.  There is therefore **no way to refute a bad edge that enters a
minimal SCC by replaying anything at that SCC** — the design's C5 as written
("the minimal bad edge's cone is pf-real and φ refutes it") is a statement
about a bad edge OFF every cycle.  So L2-M2 takes

```coq
Definition scc_no_bad nh TS DS := ∀ e1 e2, bad nh TS DS e1 e2 → ¬ on_cyc TS e2.
Lemma scc_no_bad_strong : scc_no_bad nh TS DS ↔ bad_wf_strong nh TS DS.   (* by [done] *)
```

as a hypothesis — it is CONVERTIBLE with `WeakRobustMain.bad_wf_strong`, the
"strong-residue shortcut" that file already recorded — and records the
φ-derived route as a theorem:

```coq
Theorem scc_no_bad_of_phi … :
  sf_edges nh TS DS → pf_violation_free_hart cls_of pub_of nh pstep pcls img d0 ps →
  bad_wf nh TS DS → scc_no_bad nh TS DS.
```

(`bad_wf` says SOME bad edge is minimal; by `bad_min_not_on_cyc` that one is
off every cycle, the exhibit applies to it and φ refutes it, so NO bad edge
exists at all.  The exhibit consumes the per-edge premise, which `sf_edges`
supplies — the circularity is only apparent.)

### 8.5 `sf_edges` — the site facts as TRACE SHAPES

```coq
Definition sf_shape TS j T kr a ts k' : Prop :=
  (* C1/C2 *) disciplined T kr k'
  (* C3 *) ∨ (∃ evr k0 ev0 rd0 srcs0 hs kc rend evc ctrl,
       at_evs T !! kr = Some evr ∧ (a, ts) ∈ lb_reads (ae_lb evr) ∧
       (S kr ≤ k0)%nat ∧ no_instr T (S kr) k0 ∧
       at_evs T !! k0 = Some ev0 ∧ ae_lb ev0 = LRegW rd0 srcs0 ∧ DLdRes ∈ srcs0 ∧
       rchain T (S k0) rd0 hs ∧ rchain_end (S k0) rd0 hs = (kc, rend) ∧
       at_evs T !! kc = Some evc ∧ ae_lb evc = LCtrl ctrl ∧ DReg rend ∈ ctrl ∧
       (kc < k')%nat)
  (* C4 *) ∨ (∃ L i ka_i kr_i ta_i tw_i tr_i ka_j kr_j ta_j tw_j tr_j esrc evaj,
       i ≠ j ∧ cs_window TS L i ka_i kr_i ta_i tw_i tr_i
             ∧ cs_window TS L j ka_j kr_j ta_j tw_j tr_j ∧
       win_excl TS L i tw_i tr_i ∧ win_excl TS L j tw_j tr_j ∧
       (ta_i < tr_j)%nat ∧ (ta_i < ts)%nat ∧ (ts < tr_i)%nat ∧
       at_evs T !! ka_j = Some evaj ∧ lb_aq (ae_lb evaj) = true ∧
       esrc.1 ≠ j ∧ gev_ts TS esrc = Some ta_j ∧ (ka_j < kr)%nat)
  (* already discharged *) ∨ fcov T k' ts.

Definition sf_edges nh TS DS : Prop :=          (* = edges_split_cyc with sf_shape for edge_ok_f *)
  ∀ e1 e2 T ts a k' ev',
    gev_ts TS e1 = Some ts → gev_reads TS e2 a ts → e1.1 ≠ e2.1 →
    on_cyc TS e2 → pt_trs TS !! e2.1 = Some T → (e2.2 < k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    (∃ y, gmile TS (e2.1, k') y) →
    sf_shape TS e2.1 T e2.2 a ts k' ∨ bad nh TS DS e1 e2.
```

`sf_shape_edge_ok_f` discharges `edge_ok_f T kr k' ts` from each shape with
L2-M1's lemmas: C1/C2 is `edge_ok_f`'s own left disjunct; C3 is
`fcov_of_dep_chain` (its `read_unforwarded` side condition is DISCHARGED
here, not required of the site — the edge is cross-agent, so
`foreign_ts_of_fulfil` + `foreign_ts_unforwarded`); C4 is
`cs_read_covered_window` (giving `covered T kr ts`) then
`edge_ok_edge_ok_f`.  Hence
`sf_edges_edges_split_cyc : ptraces_wf → ptraces_fwd_own → sf_edges nh TS DS
→ edges_split_cyc nh TS DS`.

**FINDING — `sf_edges` is NOT logically weaker than `edges_split_cyc`; it is
EQUIVALENT** (`edges_split_cyc_sf_edges` is the converse, three lines: the
two halves of `edge_ok_f` are two of the four shapes).  That is forced: any
SOUND shape implies `edge_ok_f`, so a discharge theorem in this direction can
only ever produce an equivalence, and the task's "strictly weaker" is not
achievable by this route.  What `sf_edges` buys is VOCABULARY, not strength:
its obligations are statements about the LABELS of one agent's trace (a
`pr∧sw` fence or an `aq` bit; a `LRegW`/`LCtrl` register chain; two lock
windows with `win_excl`), which a site can exhibit from the program text,
whereas `edge_ok_f`'s `fcov` is a statement about the machine's view
arithmetic, which it cannot.  The genuine weakening of the per-edge premise
was already banked at A0″ (`edges_split` ⇒ `edges_split_ms` ⇒
`edges_split_cyc`).

### 8.6 The theorems

```coq
Theorem l2_gdep2_acyclic pstep TS (Hwf : ptraces_wf pstep TS) (Hfo : ptraces_fwd_own TS)
    nh DS : ee_ok TS → sf_edges nh TS DS → scc_no_bad nh TS DS → gdep2_acyclic TS.
Theorem l2_gdep3_acyclic … : ptraces_wit TS DS → dev_wit_ok TS DS → … → gdep3_acyclic TS DS.
Theorem l2_gdep2_acyclic_phi … : … → sf_edges → pf_violation_free_hart → bad_wf → gdep2_acyclic TS.

Theorem robust_main_l2 pstep pcls pdev nh img d0 ps c mid TS DS :
  lat_free_prog pstep → ts_oblivious pstep → pcls_obl pcls →
  rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
  ptraces_dev_of pstep pdev TS DS mid c →
  (the FULFIL ACCOUNTING, verbatim robust_main_acyc's) →
  (∀ a, co_tc TS a) →
  ee_ok TS →
  sf_edges nh TS DS → scc_no_bad nh TS DS → dev_wit_ok TS DS →   (* ← replaces gdep3_acyclic *)
  cls_canonical pcls TS →
  ∃ cf, rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
```

`robust_main_l2`'s hypothesis list, in order: `lat_free_prog`,
`ts_oblivious`, `pcls_obl`, the promise run, `ptraces_dev_of`, the fulfil
accounting, `∀ a, co_tc TS a`, `ee_ok TS`, `sf_edges nh TS DS`,
`scc_no_bad nh TS DS`, `dev_wit_ok TS DS`, `cls_canonical pcls TS`.
Relative to `robust_main_acyc` it ADDS `ee_ok` and the hart count `nh` (both
consumed by the walk) and REPLACES `gdep3_acyclic TS DS` by the three
Layer-2 obligations; `ptraces_wf`/`ptraces_fwd_own`/`ptraces_wit` are
re-derived from the promise run exactly as `robust_main_bundle` does.

### 8.7 What L2-M2 did NOT close

- `sf_edges` is a HYPOTHESIS.  Its C1/C2/C3 disjuncts are dischargeable per
  site from the trace; C4 carries SF-1 (`win_excl`) unchanged; C6 (none of
  the four) is still the residue.  L2-M3's `w_rdw`/`w_lock` exports and
  L2-M4's byte→lock map (§5's ⚑ α/β decision) are untouched.
- `head_prestate_pf_real` is BUILT but not yet SPENT: the design's §4
  argument ("lock-mediated reads cannot be cycle entries", which would turn
  C4 from a hypothesis into a theorem about the pf-real prefix) needs the
  pre-state to be connected to the pool's residual monad and to `Ψ`.  That is
  L2-M3 work; §1/§2 exist precisely so it has a place to stand.
- `scc_no_bad` is a HYPOTHESIS (with `scc_no_bad_of_phi` as its φ route) —
  see the FINDING in §8.4.
- The `gdep2` and `gdep3` SCC skeletons are both built, but no lemma relates
  their COMPONENTS (only their on-cycle sets, `on_cyc_gdep3`).  Nothing needs
  it yet; a future segment argument on `gdep2` cycles that wants the `gdep3`
  replay would.


## 10. Two open technical questions before D8 (2026-08-18, orchestrator)

1. **Does `interference_certify` transfer to our machine, and what does it
   depend on?**  PARM's `certify` runs are `state_step ∪ write_step`
   (a `write_step` = promise-and-fulfil AT THE TOP, i.e. our pf store), so a
   certifying run IS a `wp_pf`-style solo run — good.  But the naive
   argument for "certification survives another agent's promise" fails on
   the following shape: `i` promised `m` (ts_m) and its certifying run
   makes a NEW store `s` po-before `m` with a `pw∧sw` fence between; `s`
   lands at the top, so after `k` foreign appends `s`'s timestamp exceeds
   `ts_m` and `m`'s EXT (`vwNew ⊒ ts_s`) fails.  PARM proves
   `interference_certify` for RISC-V regardless (`CertifyProgressRiscV.v`,
   ~1 200 lines, a `sim_eu` simulation), so their machine handles this —
   probably through the RISC-V-specific view arithmetic (`RES = ts` for
   exclusive writes feeding `vcap`) or a stronger promise-time invariant.
   BEFORE D8 an investigation must read that proof and answer: which
   components (`RES` view, `vcap`, exbank) it uses; whether our D2 machine
   (no `RES` view — deviation D-2) admits the theorem; and what to add if
   not.  If `interference_certify` is genuinely unavailable for our machine,
   the certification route still works with certification checked at the
   POINT OF USE (we only need: at the pf-real head state σ_h the promise `m`
   is certifiable) — which is exactly what `certified_exec_complete` gives
   for behaviors, once ported.
2. **Speculative A-bit updates** (privileged spec: "updates of the A bit may
   be performed as a result of speculation, but updates to the D bit must
   be exact"): decide between the hardware-fidelity assumption "A-bit
   updates are not observed early" (a MODEL assumption in the class of
   no-icache, NOT a kernel side condition — record it as such if taken;
   it lets the walker's CAS be append-at-fulfil in the full machine) and the
   generalized exhibit (walker-idempotent replay).  Either way, no manual
   condition on the kernel.


## 11. ANSWER to §10.1 (2026-08-18, read-only investigation of the PARM sources — full report in [`parm-certification-notes.md`](parm-certification-notes.md))

- There are TWO `interference_certify` lemmas in PARM.  The one
  `certified_exec_complete` uses is `lcertify/CertifyComplete.v:101` —
  the RESTRICTION direction (`certify (mem ++ interference) ⇒ certify mem`),
  ARCH-GENERIC (`CertifySim.v`, no `arch == riscv` anywhere); the RISC-V
  one (`CertifyProgressRiscV.v:1233`, EXTENSION) serves only
  `certified_deadlock_free`.  §8/§10.1's worry about `RES = ts` was
  mis-targeted: **completeness needs neither `RES` nor the RISC-V
  forwarding rule; our D2 machine suffices as it is.**
- The "new store above a fixed promise with a fence between" shape is
  NOT certifiable in either memory (EXT already fails in the given run):
  nothing to repair.  `sim_eu`'s essential ingredients: register views
  (value agreement), `vcap` (irreplaceable: `certify_step_vcap_promise` —
  once `vcap ≥ ts_p` the promise `ts_p` can never be fulfilled — is the
  termination guard), `fwdbank`, `exbank`, `Memory.exclusive`; `RES` is
  provably unused (both `condtac` branches close arch-blind).
- `certify_step` = `state_step ∪ write_step` (promise+fulfil at the top =
  our pf store); NO new promises inside a certifying run; promised fulfils
  at fixed ts/loc/VALUE.  Our port needs `wp_cert_step i := (wpstep at i,
  minus WPPromise) ∪ (PFStore/PFRmw)` — `wp_pf_step` alone has no arm
  fulfilling an EXISTING promise.
- `axiomatic_to_promising` produces the unconstrained `Machine.exec` by
  promising everything up front — our `WPPromise` shape.
- THE THREE REAL D8 RISKS (none of them view arithmetic): (i) the DEVICE
  FABRIC `pc_dev` (PARM has no shared component beyond memory; interference
  moves the fabric — reuse G4/G5's `qfab`/`gdev` machinery for a `sim_dev`);
  (ii) `lat = true` reads (`latest_ts`-indexed, unstable under removing
  messages — never emitted by the language, so restrict certification to
  lat-free programs, as Layer 1 already does); (iii) the fused RMW
  (`excl_ok`'s per-byte window becomes an in-case obligation of the
  restriction simulation).  D-5b (forward-bank gate on the load's `aq`
  rather than the banked store's `ex`) matters only for PROGRESS, which we
  do not need.
- RECOMMENDATION for D8: port the arch-generic `CertifySim.v` line only;
  start with the two `vcap` lemmas (`Certify.v:144/166`), then the
  restriction simulation `sim_wpcfg` with its four invariants, then
  `certified_exec_complete`'s backward induction.


## 12. ANSWER to §10.2's first half — WHAT THE ISA SAYS ABOUT A/D SPECULATION

Source: `riscv-isa-manual`, `src/priv/supervisor.adoc`, the non-`Svade`
scheme (the scheme this build is in — `menvcfg.ADUE = 1`, see
[`execution-model.md`](execution-model.md)).  The normative sentences that
bind Layer 2, and what each one settles:

- *"The PTE update must be atomic with respect to other accesses to the PTE,
  and must atomically perform all page-table walk checks for that leaf PTE as
  part of, and before, conditionally updating the PTE value."* — the Sail
  fork's atomic recheck (shape 4 of
  [`weak-memory-walk-bridge.md`](weak-memory-walk-bridge.md)) is exactly this,
  so the walker's A/D write is an RMW in the machine, by right.
- *"Updates of the A bit may be performed as a result of speculation, even if
  the associated memory access ultimately is not performed architecturally."*
  ⇒ **§8's option (a) is NOT an ISA fact for the A bit.**  Making the walker's
  A-bit RMW append-at-fulfil is a MODEL RESTRICTION (an assumption in the
  no-icache / dropped-fence-I/O-bits class), never a theorem.  Note the
  strength of the licence: the update may exist with *no* architectural access
  behind it at all.
- *"However, updates to the D bit, resulting from an explicit store, must be
  exact (i.e., non-speculative), and observed in program order by the local
  hart."* ⇒ **option (a) IS an ISA theorem for the D bit.**  If the machine
  ever splits the two, the D-bit RMW is non-promisable by right and needs no
  assumption.
- *"The PTE update must appear in the global memory order before the memory
  access that caused the PTE update and before any subsequent explicit memory
  access to that virtual page by the local hart."* — a usable gmo-position
  fact, but note its direction: it orders the update EARLIER.  **Nothing in the
  ISA orders a walker A-write after anything.**
- *"The ordering on loads and stores provided by FENCE instructions and the
  acquire/release bits on atomic instructions also orders the PTE updates
  associated with those loads and stores as observed by remote harts"*, with
  the note *"The PTE updates due to memory accesses ordered-after a FENCE are
  not themselves ordered by the FENCE."* ⇒ a fence orders the update of an
  access BEFORE it and does NOT order the update of an access AFTER it.  So
  §8's obstacle shape (a walker RMW floating above the fence that precedes the
  access it serves) is precisely what the ISA permits: **the obstacle is real,
  not an artifact of our promise machine.**
- *"Implementations are of course still permitted to perform both A and D bit
  updates only in an exact manner"*, together with *"the address-translation
  algorithm may be executed speculatively at any time, for any virtual
  address, as long as `satp` is active"* ⇒ **option (b)'s pf twin is a legal
  implementation, AND it may perform an otherwise-unmotivated walk at its own
  pf position.**  That second clause is load-bearing for the exhibit: an
  *exact*-A/D twin cannot reproduce an A bit the weak run set speculatively
  for an access that never happened architecturally, and robustness's
  conclusion is memory EQUALITY at every address — the twin needs the licence
  to do the same unmotivated walk, not just the exact ones.

Two standing facts about xv6 that make option (b) tractable:

- **xv6 never reads or writes A/D** (`grep 'PTE_A\|PTE_D' xv6-riscv/kernel/*.[ch]`
  is empty).  The hardware walker is the ONLY agent that touches those bits,
  and it only ever SETS them.  So the bits are monotone, the RMW fires at most
  once per leaf per boot, and no software read observes them.
- **Do not "resolve" the obstacle by presetting the kernel table's A/D bits.**
  `kvmmake`/`mappages` write `PTE_R|PTE_W`/`PTE_R|PTE_X` and nothing else, so a
  faithful run DOES fire the walker RMW on the table shared by all harts; the
  A/D-preset instance is a WP-tier instance choice
  ([`tlb-translation.md`](tlb-translation.md)), not a property of the image.

⇒ **The decision §10.2 asks for is now a clean either/or.**  (a) survives only
as an explicit model assumption, and only for the A bit; (b) is the route the
ISA leaves fully open, at the price of generalizing the EXHIBIT (Layer 1's
replay, `WeakRobustProv`/`Ord`/`Sim`/`Cone`) so the pf run may differ from the
weak run in walker events — because for the behaviors at issue
`gdep2_acyclic` is FALSE, so no amount of Layer-2 case analysis reaches them.

**BEFORE EITHER OPTION: NOTHING IN THE PIPELINE CAN NAME WALKER TRAFFIC.**
Both (a) and (b) need to distinguish the walker's A/D RMW from a software
AMO — (a) to make it non-promisable, (b) to replay it up to idempotence
(replaying an arbitrary RMW that way is unsound: a software CAS feeds `rd`).
The label alphabet does not: `LRmw aq rl base tvs data asrc vsrc` carries no
marker, the generated model emits no `TranslationStart`/`TranslationEnd`
(upstream `sail-riscv` has no such concurrency-interface event at all), and
D-8 in [`../../iris/WeakEvLang.v`](../../iris/WeakEvLang.v) records the
consequence for reads — a PTE read and a data load are the same node.  What
IS available, in increasing cost:
- a WRITTEN-VALUE discriminator: the walker's RMW writes an A/D VARIANT of
  the word it read (`PtAdBits.pte_set_ad`, with `pte_set_ad_absorb` already
  proving variant-of-variant collapses) and has no architectural `rd`.  This
  is label-and-value-level, needs no model change, and is the first thing to
  test before pricing anything else;
- a `pcls`-style STATE classification (the class function already takes `P`,
  so "the address is a PTE reachable from `satp`" is expressible);
- a MODEL fork adding walker markers to `vmem.sail` (the `-D SYMBOLIC`
  announce nodes are the precedent, but those existed upstream and these do
  not) — plus the machine parameter and a full tower re-land.


## 13. DECISION (the user, 2026-08-18) — the walker A/D RMW is NON-PROMISABLE, as SAIL FIDELITY

**The model of record for A/D updates is the generated Sail model, and the Sail
model does not issue speculative A-bit writebacks**: the PTE A/D update happens
inside the translating access's own execution (the atomic recheck,
[`weak-memory-walk-bridge.md`](weak-memory-walk-bridge.md) shape 4), never
detached from it.  So the full machine makes the walker's A/D RMW
append-at-fulfil (§8's option (a) mechanics), and the justification is fidelity
to the Sail model — NOT a new assumption class.  For the D bit it is an ISA
theorem regardless (§12).  What binds future work:

- The model boundary reads: hardware that makes a speculative A-bit update
  VISIBLE TO OTHER HARTS before the access it serves is outside the model of
  record, exactly as hardware outside the other recorded Sail-model boundaries
  (dropped FENCE I/O bits, no-icache) is.  Record it with those, not as a
  kernel side condition.
- `gdep2_acyclic` stays Layer 2's target theorem; no exhibit generalization
  for walker events is owed.  D8/E1/L2′ proceed.
- The machine change still needs to NAME walker traffic (§12's last item); the
  non-promisability gate is scoped by whatever discriminator that
  investigation lands.  Worklist:
  [`../projects/weak-memory-certification.md`](../projects/weak-memory-certification.md).

**§13 REALIZATION CONSTRAINT (the user, 2026-08-18): NO PREMISES.**  Stating
§13 as an undischarged hypothesis of `robust_main_l2` (the investigated
`no_early_ad` traced-bundle premise) is REJECTED: no assumption that is not a
machine-checked theorem.  The two admissible realizations: (i) the machine
DEFINITION itself never exhibits the behavior (like no-icache — a property of
the model, not a hypothesis), with whatever that costs re-proved; or (ii) the
behavior stays in the machine and the ROBUSTNESS THEOREM covers it (the
generalized, walker-idempotent exhibit of §12's option (b)).  Two recorded
obstacles to (i): a `WPPromise`-side gate is impossible (the arm carries no
label — the discriminator's read value does not exist at promise time), and
an append-at-fulfil arm breaks `wp_behavior_factor`'s frozen-log phase.
OPEN (investigation in flight): whether (i) even SUFFICES — the §8 cycle has
a variant where the early promise is the ORDINARY store `f` (promisable in
any promise machine) and the unordered thing is the walk READ, so the cycle
may survive walker-write non-promisability; if so (ii), or a Layer-2 case
that closes walker-entry segments by the certification analysis, is forced
regardless.

**The RMW split (the user, 2026-08-18): CONFIRMED.**  Layer 1 and the event
language mirror the reservation design of `main-cycle-port.md` §3a (shape
borrowed, not the file): the fused `LRmw` dies; exclusive read and
conditional write become separate labels with an agent-local reservation;
`excl_ok`'s window moves to the write's fulfil; the SC tier's blocking
self-loops do NOT cross over.  Design:
[`weak-memory-rmw-split.md`](weak-memory-rmw-split.md).
