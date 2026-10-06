# Weak port: O2 — fetch and walker reads under the Lean (MachCSL) semantics

*Design-advisor note, 2026-10-05.  Owner decision O2 (`weak-port-architecture.md`): the Lean weak tier
classifies `AK_ifetch` as the i-cache agent (moves no view) and `AK_ttw` per MachCSL (a plain read).
Inputs: `MachCSL/Lang.lean` (`evStep`), `TsoMem.lean` (`ifetchAgent`, `akIfetch/akPlain/akExcl/akAcq`),
`claude-notes/design/icache.md`, `weak-port-sail-drift.md`, the Rocq weak sources named below.*

## 0. The two facts the design rests on

1. **Walker reads are unchanged in meaning.**  MachCSL puts `AK_ttw` on the plain arm (`akPlain k := !akIfetch k
   && !akExcl k`), which is Rocq Decision 6's "walks are plain weak loads".  So `classify (AK_ttw ()) =
   AkInfo false false false = wak_plain`: every walker trace and every `WeakWalkEff`/`AxWalk*`/`WkWalk*`
   certificate keeps its *value*; only closed request literals change payload.  O2 is a **fetch-only** redesign.
2. **Kernel text is never written, and the Lean tree already has the lemma in i-cache form.**
   `MachCSL.imgBytes_readable : genHeapInterp m ∗ imgBytes pa n w ⊢ ⌜∀ h tvn, m.readBytes h tvn pa n w⌝`
   is the twin of Rocq's `WeakEvLift.etext_byte_pin`.  The immutable-text argument (Rocq Decision 4)
   survives O2; it stops depending on the read's view floor.

## 1. The promising / view tier

### 1.1 `classify`

Keep Rocq's three-Boolean record so the 64 files that branch on it keep their statement shapes, but define it
**from MachCSL's classifiers**, so the weak dispatch is MachCSL's by definition:

```lean
structure AkInfo where
  ifetch : Bool   -- Rocq ak_coh, renamed: the i-cache read (NOT "coherent/latest" any more)
  latest : Bool   -- exclusive / RMW read half (unchanged)
  sync   : Bool   -- acquire on reads, release on writes (unchanged)
def classify (k : AK) : AkInfo := ⟨akIfetch k, akExcl k, akAcq k⟩
theorem classify_ttw : classify (.AK_ttw ()) = ⟨false,false,false⟩ := rfl
theorem classify_ifetch : classify (.AK_ifetch ()) = ⟨true,false,false⟩ := rfl
abbrev wakPlain  : AkInfo := ⟨false,false,false⟩
abbrev wakIfetch : AkInfo := ⟨true,false,false⟩
```

Deviation to record in `Weak/WeakInterp.lean`: `ak_coh` ↦ `ifetch`; the "dead arm" findings (§3 (1)) are
deleted; `AkInfo true _ _` is live and means i-cache.

### 1.2 The i-cache read: admissibility and post-state

MachCSL (`evStep`, fetch arm): pick `tvn` with `σ.itv cpu ≤ tvn ≤ σ.top`, read every byte as `ifetchAgent cpu`
(no forwarding: `HEnt.visible` never fires on `tid`), `σ' = σ`.  In log vocabulary, byte `a` returns the
write `t` that is latest at `tvn`.  The weak tier is per-byte (as every `tvs` list is), so:

```lean
/-- byte j of a fetch may read (t, v): message t writes v at a (t = 0: the image),
    and t is the latest write to a at SOME instruction view tvn ≥ itv. -/
def ifetchByteOk (img : Image) (log : List Wmsg) (itv : Nat) (a : Int) (t : Nat) (v : BitVec 8) : Prop :=
  logByte img log t a = some v ∧ ¬ writesIn log a t (max t itv)
def ifetchOk (img) (log) (itv) (base : Int) (tvs : List (Nat × BitVec 8)) : Prop :=
  ∀ j t v, tvs[j]? = some (t, v) → ifetchByteOk img log itv (base + j) t v
```

(`¬ writesIn log a t (max t itv)` is "no write to `a` in `(t, max t itv]`", i.e. there is a legal `tvn ≥ itv`
at which `t` is latest; MachCSL's single footprint-wide `tvn` is one such choice per byte, so **MachCSL ⊆
weak**, §3.)  No `readable`, no `load_vpre`, no coherence floor, no forward bank.  **Post-state: identity**
on `wstate` — no `load_post_run`, no `w_ldv`/`w_tbank` move (the F7 "second `LInstr` reset" stays, but it now
has nothing to reset from the fetch).

**Where `itv` lives — two stages (owner decision D2).**
- *Stage A (recommended for the port):* **no `itv`**: `itv := 0` everywhere, `fence.i` stays the identity
  it is in Rocq.  `ifetchByteOk` degenerates to `logByte img log t a = some v` — a fetch may return any value
  the byte ever held.  A sound over-approximation of MachCSL (`tvn ≥ itv ≥ 0`): no view moves, no
  forwarding, not "latest" — O2 minus Zifencei.  xv6's verified kernel path never executes `fence.i`
  (`weak-memory-lb-axsl.md` §0), so no theorem in the port can tell the difference, and **no state field
  is added** — `Weak/WeakMem.lean`, already ported, is untouched.
- *Stage B (G5 / user text, later):* a per-hart instruction view **outside** `wstate`
  (`wmstate.wmItv : Nat`, `wgstate.wgItv : CPU → Nat`, promise-machine `paItv`, `WeakAxiomatic.mstate.msItv`),
  0 at era birth; the `Barrier_RISCV_i` arm sets `itv' := max itv (max ws.wVrNew ws.wVwOld)` (MachCSL:
  `max itv (fencePost true false tv rv pub)` — data floor and own last store).  `ws_le` ignores it, so
  `barrier_post_le`/`wrun_ws_le` stand.

### 1.3 `WeakInterp.wrun`/`wexec`, `WeakInterpProj`, `WeakBridge`

- `wbyte_ok s ak a t b`: the `ak_coh` branch becomes `ifetchByteOk (wimg s) (wm_log s) itv a t b`; `wread_post`
  keeps `if ak.ifetch then s else …` (identity — the same line, new reason).
- `wexec`: the i-cache arm **consumes the oracle** like a plain read (today it reads `coh_ts` without the
  oracle); `wread_bytes_complete` then still holds (any admissible fetch is some oracle choice).  Drop `coh_ts`.
- `WeakInterpProj` finding (2) "coherent reads are silent" (project to `exec`'s flat read) is false for an
  arbitrary i-cache read; the ifetch arm projects **under pinnedness**, exactly like the plain arm:
  `ak_pins ak := ak.latest` (the `ak_coh ||` disjunct goes).  `WeakBridge.wbyte_ok_pinned` gains the ifetch
  case: `latest_ts log a = 0 → ifetchByteOk … a t v → t = 0` (any `t > 0` would be a message writing `a`).

### 1.4 Labels: `LIFetch`, the program half, the event language

Add one constructor to `WeakPromise.wlabel` (Lean `Weak/WeakPromise.lean`, already ported — one arm per
exhaustive match there and in `WeakPromiseFact`):

```lean
| LIFetch (base : Int) (tvs : List (Nat × BitVec 8))   -- no aq, no lat, no asrc
```

Do **not** reuse `LLoad`'s dead `lat := true` slot: `lat_free` (no `lat` loads in the Sail LTS) is a premise
of the robustness tier and must stay true; `lat` remains inert (D5).

- `WeakEvInst.pnode_step` MemRead arm: the `ak_coh … = false ∧ (plain ∨ exclusive)` guard becomes a total
  three-way split on `classify`: `ifetch → l = LIFetch pa tvs` (no `asrc`: a fetch has no address
  dependency in RVWMO; this also removes the review's Q2 hazard, §2), `plain → LLoad`, `latest → LExLoad`.
  `WeakSailLTS`'s stuck arm (d) and `no_coh_reads`/`sail_shaped`: **moot — the file is retired** (owner
  decision 3); `WeakCompose` (6) likewise.
- `WeakEvLang.ecycle_step` MemRead arm: same split; the ifetch case is
  `∃ w tvs, length tvs = n ∧ bytes tvs = w ∧ ifetchOk (imgZ (wgimg σ)) lg0 0 pa tvs ∧ e' = ECycle gen c (k (inl (w,None))) None ∧ σ' = σ`.
  Barrier arm: unchanged in Stage A.
- Promise machine (`WeakPromise.pstep`): arm `WPIFetch`: `ifetchOk img log 0 base tvs`, state and log
  unchanged.  Robustness invariants (`pcls_obl`, `ts_oblivious`, `aev_post`, `astep_ok`) gain a
  state-identity arm each; Layer 1's theorems are over `LLoad`/`LStore` edges and do not see it.
- `WeakRvwmoConf.hlbl_realizes`: `LIFetch base tvs` realizes the row item `LFetch base tvs.*2` (§2);
  `lbl_post k ws (LFetch …) = ws`.

### 1.5 The lift (`WeakEvLift` §5c) and the fetch leaves

`ewp_ev_fetch` is re-derived from `ifetchByteOk` + pinnedness; it gets **simpler**:

```lean
theorem ewpEvFetch (gen : Nat) (c : CPU) (n) (req) (K) (w : BitVec (8*n)) (ws : Wstate) :
    gen = 0 → devAddr req.pa = false → akIfetch req.access_kind = true →
    etextWord (paZ req.pa) n w -∗ hartWs c ws -∗
    ▷ (hartWs c ws -∗ EWP (ECycle gen c (K (.inl (w, none))) none) @ ⊤) -∗
    EWP (ECycle gen c (.next (.memRead n _ req) K) none) @ ⊤
```

Deltas against Rocq: premises `ak_coh = false ∧ ak_latest = false` ↦ `akIfetch … = true`; **`efetch_ws`
disappears** (the continuation gets `hartWs c ws` back unchanged — 4 files thread `efetch_ws`:
`WeakEvLift`, `WeakEvStarted`, `WeakEvFunnel`, `WeakEvExecEff`); enabledness is the all-zero `tvs`, admissible
by `logByte img log 0 a = img a`.  `ewp_ev_seq_fetch` (§7c) follows.  What replaces the F7 artefacts:

| Rocq | Lean under O2 |
|---|---|
| `WeakFetchEff.wak_plain` at the fetch (`WEread wak_plain pc 4`) | `WEread wakIfetch pc 4`; `wakPlain` stays for walker/data reads |
| `WeakEvStarted.ev_fetch_plain : classify … = AkInfo false false false` | `evFetchIfetch : classify evReqf.access_kind = wakIfetch := by decide` |
| `ev_fetch_req` and every closed `ReadReq` literal of a fetch | restated with `access_kind := .AK_ifetch ()` |
| `WeakFetchEff` §2 `exec_eff_read_ram_plain_4` → §3 chain through `checked_mem_read` | derived from `runRW`/`runRead` walk equations (architecture §A, `exec_of_runRW`); the kind match is in the Lean model already |
| `WeakCert.wP_eff` certificates (quantified over the fetch's `akinfo`) | unchanged |
| the fetch's `read_ok`/`load_post_run` bookkeeping in `WeakLeaf*`, `WkFetchPeel`, `WkStepPeel`, `WkEntryNew` | deleted — the fetch is view-silent |

### 1.6 Walker reads

`WeakWalkEff`, `WeakWalkStale`, `WeakKpt*`, `WeakStale`, `WkWalk*`, `WkUnmapMp`, `AxWalk*`, `AxPtProt*`:
`WEread wak_plain a 8` is still what `classify (AK_ttw ())` yields.  Changes: header correction (the
"`read_pte` goes through `read_kind_of_flags` → `Read_plain`" sentence), closed request literals, and the A/D
CAS stays `AK_explicit{exclusive}` (both pins).  No certificate value moves.

## 2. The axiomatic / AxSL tier

**Decision (D1, recommended): the fetch is NOT a graph memory event.**  riscv.cat has no instruction-fetch
events; the Rocq tier put fetches in rows as `LLoad` reads (into `po-loc` rules 1–3, `fr`, and `AxDeps`'s
`dt_ld`/`dt_adr` — `weak-memory-lb-axsl-review-fetch.md` Q2 flagged these *outgoing* fetch edges as sound
only via "T is never written", xv6 content that fails the §0 audit criterion).  Under O2 the fetch reads an
agent outside the store order: the faithful graph treatment is an **oracle read on T with no edges**, which
is what `AxOpsem.AStepFetch` already is.

- `WeakAxiomatic.lbl` gains `| LFetch (base : Z) (vs : list (bv 8))` (no `ts`: nothing to `rf` from).
  `aident (LFetch b vs) := IFetch b (length vs)` (new identity constructor); `lb_is_mem`, hence `AxWp.gmem_b`,
  is `false` on it; it is not in `gx_gmo`, not an `R`, has no `rf`/`co`/`fr`/`ppo`/deps edges; `dstep_t`'s
  arm is `(s, [])`.  **Row positions are preserved**: today's fetch item `LLoad false pc ts vs` at position
  `k` becomes `LFetch pc vs` at the same `k`, so the AxSpin row shapes keep their `k`/`S k` arithmetic and
  lose their fetch-item `rf` obligations ("fetch items RF" from timestamp 0) outright.
- `AxOpsem`: `AStepFetch` matches `row !! k = Some (LFetch b vs)`, `fetch_answers b vs`, and the program
  label `LIFetch b tvs` with `tvs.*2 = vs`; `aread_step` no longer realizes fetches (`aident_rd (IFetch …) =
  None`).  Header fact (3)'s hazard — two realizations of one position — is gone: `AxAdequacy`'s
  `astep_any_nf`/`wlabel_is_fetch` (39 files) become exact by construction (drop, or keep `rfl`-trivial);
  `AxLifting`'s header FINDING closes.  `AxWp` already `wp_skip_step`s the fetch.
- `AxFetch` (4,951 lines): `af_astep_fetch_of_memread` and the §2 peel restated with `LIFetch`/`LFetch` and
  `wakIfetch`; the `.mem`-invariance round trip (c) is unchanged.  Split the file (map risk list).
- `AxSpinE3.FirstRd.fr_mrd` (18 files) needs only `ak_latest … = false` — true of `AK_ifetch`; **no change**.
- The capstone clause `∀ w ∈ writes GD, ¬ text_byte (addr w)` stays and is now justified in-model: with no
  write to T every byte of T has only its timestamp-0 entry, so every admissible i-cache read returns the
  image (§1.3) — view tier and oracle agree.  The in-definition hardware statement "a fetch observes only
  writes performed before the fetching instruction" (`weak-memory-lb-axsl.md` §0) is **no longer needed**;
  record its deletion in the capstone's assumption audit.
- Certificates: the AxSym engine's coherent-read arm (`AxSymMem`, `AxSymLd`, `AxSymEngine*`, `AxSymCtl`:
  "ak_coh = true ⇒ latest") is rewritten to the i-cache arm before any ledger is re-derived; J0 ledgers and
  `AxSmodeProbe.ak_tag` outputs change value at every fetch (tag 1) and are recomputed by `decide +kernel`.
  `WeakCert`/`AxCert*` general certificates are robust.

Fallback if D1 is refused (fetch stays a graph `LLoad`): O2 holds at the view tier only; the AxSL tier keeps
its stronger-than-hardware fetch edges and the Q2 caveat; §2's alphabet work disappears, §1 stands.

## 3. The bridge to MachCSL

One-directional, per event, stated over the pure machines (no Iris):

```lean
def logOf (σ : MState) : List Wmsg   -- from σ.log (authors) and σ.mem histories (histOk gives the bytes)
def imgOf (σ : MState) : Image       -- the timestamp-0 entries
theorem evStep_ifetch_refines (hmm : mmOk σ) (hk : akIfetch req.access_kind = true) (hram : ramBytes req.pa n) :
    evStep cpu (.memRead n vs req) σ (.Ok (w, none)) σ' →
    ∃ tvs, ifetchOk (imgOf σ) (logOf σ) (σ.itv cpu) (paZ req.pa) tvs ∧
           (∀ j, j < n → (tvs[j]?.map (·.2)) = some (nthByte w j)) ∧ σ' = σ
theorem evStep_ttw_refines … : akPlain … → … readOk … ∧ σ' ≈ afterLoad …   -- the existing plain-read bridge
theorem fence_i_refines (Stage B) : (σ.fence cpu .Barrier_RISCV_i).itv cpu = max (σ.itv cpu) (max tv pub) …
```

Text: `MachCSL.imgBytes pa n w` ↔ `etextWord (paZ pa) n w` (both "latest write = timestamp 0, persistent");
`imgBytes_readable` ↔ `etextBytePin`.  The full "every TsoMem run is a promise-free run" theorem stays out of
scope; these lemmas are what O2 adds, and the first is the spike's acceptance test.

## 4. File classes (Rocq weak sources, 609 files; counts from `grep -l`)

**Unaffected:** `WeakMem` (Stage A), `WeakDeps`, `WeakRvwmoGraph`/`AxGraph*`/`AxGraphCat` (one `LFetch` arm in
kind predicates aside), `WeakFence`, `WeakView`/`WeakVProp`, all `WeakLeaf*` *data* reasoning,
`AxSpinE*/PO*/Hd*` (FirstRd), `WeakCert`/`AxCert*` general certificates, `WeakRvwmoCert*`, `AxLock*`,
`KernelPins*`, `VirtioProg`, the device files.

**Mechanical (restate, same shape):**
- `wak_plain`/request literals at the fetch: the 33 `wak_plain` files (`WeakFetchEff/2/Rvc`, `WeakEvFunnel`,
  13 `WeakLeaf*`, `WkFetchPeel`, `WkStepPeel`, `WkEntryNew`, `AxFetch`, `AxRegOnly`, `AxRowConf`,
  `AxEpiChain`) and the 16 `AkInfo false false false` files;
- walker lane (§1.6): `WeakWalkEff`, `WeakWalkStale`, `WeakKpt*`, `WeakStale`, `WkWalk*`, `WkUnmapMp`,
  `AxWalk*`, `AxPtProt*` — headers and literals only;
- one new label arm: every exhaustive match on `wlabel`/`lbl` (≈25 machine/graph/projection files of the 155
  mentioning `LLoad`; estimate), `AxDeps.dstep_t`, `AxWp.gmem_b`, `WeakRvwmoConf.hlbl_realizes`;
- `WeakInterpProj` (`ak_pins`), `WeakBridge` (pinned arm), `WeakEvCapstone`/`WeakEvAdequacy` (drop the
  "vacuous for rv64d" discharge).

**Redesign:** `WeakInterp` §3–4; `WeakEvInst`/`WeakEvLang` read arms; `WeakPromise`/`WeakPromiseFact`
(`LIFetch` arm, invariants); `WeakEvLift` §5c/§7c and the 4 `efetch_ws` files; `AxOpsem` (`AStepFetch`,
`aident`), `AxAdequacy`, `AxLifting`, `AxFetch`, `AxRowConf`; the AxSym engine's coherent arm (`AxSymMem`,
`AxSymLd`, `AxSymEngine*`, `AxSymCtl*`); the capstone's assumption audit.

**Retired (skipped, owner decision 3):** `WeakSailLTS*`, `WeakSailComplete/Cone`, `WeakShape*` (incl.
`WeakShapeMem`'s `rk ≠ Read_ifetch` discharge — the only `Read_ifetch` users), `WeakCompose*`, `WeakRetag`.

## 5. Risks and incremental order

Risks: (R1) the two-alphabet extension is wide but shallow — do it in Phase 0, before any `Ax*` port, with a
`simp` set for the identity arms; (R2) the AxSym engine may have "latest" baked into lemma *statements*
(check `AxSymLd` first); (R3) ledgers/probes change value at every fetch — compute cost only, but the engine
lands first; (R4) Stage A admits stale fetches of *user* text — G5 needs Stage B and MachCSL's
`iviewLb`/`ctxBytesX` stamp discipline; (R5) `logOf`/`imgOf` need history well-formedness — state the bridge
under `mmOk`.

Order (spike first, ≈ 1 agent-week):
1. `Weak/WeakInterp.lean` §1.1–1.3 with `ifetchByteOk`; `wexec_wrun`; `wread_bytes_complete`.
2. `LIFetch` in `WeakPromise.lean`/`WeakPromiseFact.lean`; `LFetch` in `Weak/WeakAxiomatic.lean`.
3. `evStep_ifetch_refines` (§3) against `MachCSL.Lang` — the acceptance test that the weak i-cache arm
   admits MachCSL's.
4. `WeakEvInst`/`WeakEvLang` read arms; `WeakEvLift.ewpEvFetch`; one fetch leaf (`WeakEvStarted`'s publisher,
   whose `ev_fetch_req` is width 2 — the RVC case) proved with the new rule, confirming the `efetch_ws` deletion.
5. `AxOpsem.AStepFetch` + the `wt_fetch` witness; `AxDeps.dstep_t`'s arm; then the rest by the map's lanes.

## 6. Owner decisions this design needs

- **D1** Fetch out of the graph (`LFetch`, no edges) — recommended — vs fetch stays a graph `LLoad`.
- **D2** Stage A (no `itv`, `fence.i` identity, sound over-approximation) for the port; Stage B at G5.
- **D3** Per-byte i-cache view (weak-tier style) rather than MachCSL's single footprint `tvn`; bridge one-way.
- **D4** New `LIFetch` constructor, `lat` kept inert (not the `lat := true` reuse).
- **D5** Confirm the retired list covers `WeakSailLTS*`/`WeakShape*`/`WeakCompose*` so `no_coh_reads` is moot.
