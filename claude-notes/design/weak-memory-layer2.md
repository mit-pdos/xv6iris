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
