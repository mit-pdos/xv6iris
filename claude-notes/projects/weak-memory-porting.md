# Porting guide: the weak-memory (RVWMO) sweep — M4

Written from what the M3b vertical slice taught (branch `weak-memory`;
design: [`../design/weak-memory.md`](../design/weak-memory.md); staged
worklist + established-facts blocks:
[`weak-memory.md`](weak-memory.md)).  The precedent for the FORM of this file
is [`../completed/explicit-cpuid-porting-guide.md`](../completed/explicit-cpuid-porting-guide.md):
what is mechanical, what needs thought, and — the part that pays for itself —
the failure modes that COMPILE.

Read this before porting your first file, then keep it open; every section
below is something the slice actually hit.

---

## 0. Build discipline (non-negotiable — other agents work concurrently)

- `eval $(opam env --switch=/shared/xv6rocq)` in every shell that runs `coqc`.
- Compile ONLY your own file, one at a time:
  `coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -w -notation-overridden <file>.v`
- NEVER `make clean-proofs`, never `pkill -f coqc` (see the durable notes:
  the pattern matches the killer's own shell).  Wait on a sentinel
  (`…; echo "EXIT=$?" >> log`), never on `pgrep`.
- Adding a file to `iris/` means adding it to `iris/_CoqProject`
  (`proof_coverage.py --check` fails CI otherwise), and the file list is read
  from `_CoqProject` at make time — but `CoqMakefile`/`CoqMakefile.conf` are
  regenerated only when you ask, so run
  `coq_makefile -f _CoqProject -o CoqMakefile` after editing `_CoqProject`.
- Per batch: full `make -f CoqMakefile -j16` (grep the log for `Error`),
  `tools/proof_coverage.py --check`, `tools/lemma_diff.py`,
  `tools/spec_vacuity.py` — and, because the weak layer's contracts are plain
  lemmas rather than `_body` definitions, **also
  `tools/spec_vacuity.py --lemmas iris/Weak*.v`** (the bare run scans only
  `Spec*.v`/`Wp*.v`/`Code*.v` for `Definition …_body`, so it says nothing at
  all about a `Weak*.v`; the file-argument + `--lemmas` mode was added at M3c
  for exactly that).

---

## 1. The five mechanical spellings

These are search-and-replace with a type check, in the order you hit them.

| SC | weak | note |
|---|---|---|
| `a ↦ₘ{dq} v` (mutable RAM byte) | `a ↦w{dq} v` (`WeakVProp`) | KEY CHANGE: the address is a **`Z`** (`pa_z a` / `WeakInterp.acc_addr a j`), not an `Arch.pa` |
| `a ↦₄ w` (4-byte word) | `a ↦w₄{dq} w` (`WeakInstr.wpt4`) | carries 4-alignment AND `acc_wf` (wrap-freedom) as pure conjuncts; NOT a `big_sepL` — four explicit `∗`s, so extraction is `destruct j as [|[|[|[|]]]]` |
| `a ↦ₘ□ v`, `kernel_text bs` | `wpt_img`, `WeakInstr.wkernel_text bs` | an `iProp`: OBJECTIVE and freely shareable; `wkernel_text_v` is its `vProp` twin, identified by `wkernel_text_at` |
| `instr`/decode facts over `exec … σ` | the SAME facts over `WeakBridge.wflat_st σ` | `wflat_st σ := MState (wm_regs σ) (wflat (wm_img σ) (wm_log σ)) (wm_dev σ)` — registers and devices are literally the same objects |
| `σ.(mem) !! pa_add ea j = Some b` | `wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some b` | produced by `wpt4_flat` / `wkernel_text_flat` / `wlat_flat_lookup`, with NO view hypothesis |
| `iProp Σ` (a spec's resources) | `vProp Σ` (`WeakVProp`) | only for assertions about mutable RAM; everything else stays an `iProp` and is embedded `⎡·⎤` |
| `instr pc is_rvc i` | `WeakFunnel.winstr pc is_rvc i` | the DECODE half transfers verbatim (it is a pure fact about an arbitrary `mstate`); the byte half becomes timestamp-0 `wlat_pointsto` text elements — and the footprint is always FOUR bytes, even for a compressed instruction |
| `InstrBytes.wp_instr` | `WeakFunnel.wwp_instr` | see §2d; same premises, one extra `set_reg` on the caller's execute fact, two fewer register obligations |

**The register/CSR/config tower does not move at all.**  `hw_config`,
`mmode_config`, the sconf bundles, `kmap_static_claims`, `pc_is`, `↦ᵣ`, all
ghost state and every pure fact are `iProp`s over `riscvGS`, which the weak
side carries unchanged; embedded into `vProp` they are objective by
`embed_objective`.  `reg_valid`/`reg_valid_dq`/`reg_update` apply VERBATIM,
because `wmstate_interp σ` contains `reg_interp (wm_regs σ)` and
`wm_regs σ = sregs (wflat_st σ)`.  The only non-transferring lemmas are the
ones that consume `RiscvPtsto.mstate_interp` AS A BUNDLE
(`fetch_from_instr_bytes`, `instr_lift`, `dispatchInterrupt_none_from_regs`,
`state_interp_reg_dq`, `wp_instr`) — and **all five are done, in
`iris/WeakFunnel.v` (§2d)**.  The one worth knowing about is the fetch:
restated over pure register lookups and pure byte/`addr_is_ram` facts
(`WeakFunnel.exec_fetch_flat`) it has NO Iris in it at all, and the
`kmap_static`/`text_ident_phys` VA→PA machinery disappears because weak
addresses are already physical.

---

## 2. The `wstep_cert` skeleton — what an instruction costs

**Do not walk the model.**  M3a estimated the per-instruction peel
(`WeakBridge.wstep_ok` over `riscv_step`) at the size of
`RiscvExec.exec_riscv_step_hart_active` + `SmodeCore.exec_hart_active_progress_base_gen`
+ the three `exec_fetch_*` reductions, mirrored.  `iris/WeakCert.v` replaces
all of that with ONE theorem, and the recipe is fixed:

> **Run the SC interpreter on a memory RESTRICTED to the window.**  `exec`'s
> RAM read arm returns `None` on a byte the map does not contain, so if
> `exec (riscv_step tick) (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ))`
> succeeds, every read of the run is inside `W`.  Writes are confined by the
> domain of the FINAL memory (memory only grows along a run).  And the
> restriction agrees with the real memory, so the confined run IS the real
> run.

Per instruction, the whole obligation is `WeakCert.wP_conf σ`:

1. `wlog_wf (wm_log σ)` — a conjunct of `wmstate_interp`, hand it through;
2. a window `W : gset Arch.pa` — the instruction's text word plus its data
   word — with `∀ a ∈ W, pa_z a ≠ 0` (RAM is above 0x80000000; this is what
   gives `acc_wf` for free, via `WeakCert.acc_wf_window`: a wrapping range
   passes through address 0);
3. `∀ a ∈ W, pinned_read σ (pa_z a)` — `WeakInstr.wkernel_text_pinned` for
   the text half (never written this era ⇒ free) and `wpt4_pinned` for an
   OWNED data word.  An AMO's data word needs no pinnedness (its read half is
   `ak_latest`) but must still be listed in `W`, because the WRITE's footprint
   is confined by `W` too;
4. `∀ tick, ∃ t', exec (riscv_step tick) (MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)) = Some (tt, t') ∧ dom (mem t') ⊆ W`
   — **your own SC library lemma, instantiated at a second state.**  Its
   register/config premises are literally the same terms; its memory premises
   are `wmem_restrict_lookup` of the same `wpt4_flat`/`wkernel_text_flat`
   facts you already produced for the flat state.

Then `WeakCert.wstep_cert_conf_none` / `wstep_cert_of_conf` gives
`WeakInstr.wstep_cert`.  Measured marginal cost: **the second instantiation
and the window, ~20–40 lines, no model reduction, no `vm_compute`.**

**What the skeleton does NOT give you** is the certificate's `Q` — the
instruction's WEAK-MEMORY EFFECT (the `.aq` raised the scalar floor; the
fence moved the index; the store appended THIS message).  `exec` ignores
access kinds and barriers entirely, so no argument over `exec` can produce
it.  It stays a per-instruction ISA obligation of the same nature as a decode
fact: see §2c, which is the recipe for it and the honest price.

---

## 2b. Composing a leaf into a WP: the four moves (M3c)

`iris/WeakAcquire.v` is the worked example — the spinlock's acquire, its spin
loop, the release and the `started` setter, each ONE `wp_winstr` application.
Four things recur, and they are the whole pattern:

1. **BORROW THE LATEST-WRITE AUTHORITY, NOTHING ELSE.**
   `WeakGhost.wmstate_interp σ` is seven conjuncts and a racy leaf needs to
   update exactly one of them — `wlat_interp (wm_img σ) (wm_log σ)`, the "every
   element IS the latest write" authority. `WeakAcquire.wmstate_rest` +
   `wmstate_interp_split` peel it off; the leaf's caller keeps registers,
   devices, the log auth and this hart's `wstate` cell, and updates them with
   the SC register tower it already has. A caller that only READS memory
   (deriving `wpt4_flat` / `wkernel_text_flat` facts) borrows the authority and
   hands it straight back — that is why the callbacks below take it and return
   it.

2. **OPEN THE INVARIANT AT ⊤, HOLD IT ACROSS THE `▷`, CLOSE IT ON THE WAY
   BACK.** `wp_winstr`'s callback is `wmstate_interp σ ={⊤,∅}=∗ … ▷ (… ={∅,⊤}=∗
   …)`, i.e. the ordinary atomic-step shape, so `iInv wlockN as … "Hclose"`
   inside it just works and what the leaf's own caller then sees is the SAME
   callback at `⊤ ∖ ↑wlockN`. `iNext` in the continuation strips the `▷` off
   the invariant body along with everything else. The invariant body must be
   destructed under the `▷` (`iInv … as (st t v) "(>Hw & Hlk)"`): the element
   bundle is timeless and comes out, the payload `monPred_at R V` is NOT
   timeless and stays under the later until after the step, which is exactly
   where it is wanted.

3. **READ THE SHARED WORD OUT OF THE ELEMENTS *BEFORE* THE STEP.**
   The caller's `exec` fact is a statement about `WeakBridge.wflat_st σ`, so it
   can only be supplied at a KNOWN word. `WeakLock.wlat4_flat_gen` turns the
   invariant's `wlat4` bundle into that word with no view hypothesis and no
   ownership (`iDestruct … as %pure` keeps the bundle), so the callback is
   parameterised by the value `v` the AMO will return and the post-step branch
   is on the same `v`. When a core (`wacquire_core`) re-derives the word for
   itself, identify the two with `WeakAcquire.wflat_word_agree`.

4. **THE LOOP IS THE LÖB RULE AND NOTHING ELSE.**
   `WeakAcquire.wwp_spin_loop : □ (K -∗ ▷ (K -∗ WP) -∗ WP) -∗ K -∗ WP`. A
   spinlock's weak-memory content is entirely in the ONE attempt that succeeds
   — a failed `amoswap` leaves `⌜v ≠ 0⌝` and no resource — so the loop needs no
   weak-memory reasoning at all, and the `▷` it consumes is the one every
   `wp_winstr` already provides. Until the branch leaves are ported the retry
   edge is a premise of the loop lemma (`wwp_acquire_loop`); when they exist,
   the body becomes `attempt ; branch` and the statement does not change.

---

## 2c. The certificate's `Q` half: the ONE thing that is irreducibly per-instruction

`WeakCert`'s confinement trick discharges the `wstep_ok` half of
`WeakInstr.wstep_cert` for every instruction at once. **It cannot produce the
`Q` half, and no argument over `exec` can**, because `Q` is about the weak
machine's own effects: which message the step appended, that the `.aq` raised
the scalar floor, that the fence moved the index. Three consequences worth
internalising before the sweep:

- **`Q` is over the successor STATE (`wmstate -> wmstate -> Prop`), not its
  views.** An invariant that owns a byte's latest-write ELEMENTS must retarget
  them at the message the step appended, so the certificate has to name that
  message (`wQ_store tid ea v`'s second conjunct). `wstep_post`'s
  `∃ l, log' = log ++ l` is not enough. (M3b found this the hard way; the fix
  landed at M3c and cost ~40 lines across four files.)
- **Do not try to derive the message identity from the memory.** The tempting
  routes all fail: the SC successor's `mem` pins the final VALUE of every byte
  but not how many messages wrote it; a domain-growth argument sees only
  writes to bytes that were absent from the confined map, so it can never rule
  out a (value-preserving) write to the TEXT, which is precisely what would
  invalidate the `wkernel_text` elements. Something structural about the run
  is genuinely needed.
- **So the `Q` half is a per-instruction ISA obligation of the same nature as
  a decode fact** — state it that way, as a premise of the leaf, and discharge
  it by the model peel the durable notes describe (lazymatch dispatch, folded
  state, resolve reads instantly). Its per-instruction shape is short: an
  effect list `[fetch read; the instruction's own access]`, over which every
  `wQ_*` is view arithmetic.

---

## 2d. THE FUNNEL: what a leaf hands `WeakFunnel.wwp_instr` (M4-prep)

`WeakInstr.wp_winstr` owes the WHOLE `exec (riscv_step tick) (wflat_st σ)` —
fetch, decode, wrapper and all — while an SC leaf owes ONE `execute` fact.
`wwp_instr` is the bridge, for the **M-mode tier**; port a leaf by keeping its
statement and changing four things.

1. **`instr` becomes `winstr`.**  Build it with
   `winstr_bytes_of_text` (from `WeakInstr.wkernel_text`, plus the per-byte
   lookups and `addr_is_ram`, both `vm_compute`-discharged) and `winstr_intro`
   with the file's EXISTING decode fact — unchanged, because `winstr`'s decode
   field is that fact, as a plain `Prop` over an arbitrary `mstate`.  4–8 lines.
   Text pinnedness is free (`winstr_pinned`: text is unwritten this era).
2. **The execute fact moves by ONE `set_reg`.**  It is now instantiated at
   `set_reg (wflat_st σ) (R_bool minstret_increment) b`, with `b` chosen by the
   funnel and handed to the callback: `wp_winstr` demands the `exec` fact at
   the state the WEAK machine holds, so the wrapper's `minstret_increment`
   pre-write is INSIDE the run.  Every SC execute lemma is state-generic, so
   this costs nothing.  **Do NOT** also supply `hart_state`/`minstret_increment`
   facts about `s_exec`: unlike the SC funnel, the weak one holds those cells
   itself.
3. **The registers go through `reg_interp`, not `mstate_interp`.**  The
   callback receives `reg_interp (sregs …)` and returns `reg_interp (sregs
   s_exec)`; the seam for the weak-memory conjuncts is
   `WeakFunnel.wmstate_norg` (`WeakAcquire.wmstate_rest` minus the registers).
   The post-step continuation is parameterised by the SC successor `t`, because
   `wstep_post`'s memory/device conjuncts are stated against it.
4. **The certificate is the only irreducible part**, and it is §2/§2c: the
   window `W` plus the same SC library lemma re-instantiated at
   `WeakCert.wmem_restrict σ W`.

Measured budget on top of the SC leaf: **~30–55 lines for a register-only or
load leaf, ~60–90 for a store/AMO leaf**, of which 20–40 is the window.

**THE sconf TIER IS NOT PORTED.**  Its fetch (`SmodeCorePt.tlb_inv_pt_fetch`)
opens the kpt tree invariant, walks the page table and may write A/D bits back;
what it needs is listed in [`weak-memory.md`](weak-memory.md)'s M4-prep block.
Do not start an S-mode leaf batch before that is designed.

---

## 2e. `exec_eff` FACTS ARE MOSTLY FREE — use the empty-memory detector

`WeakEff` is the toolkit for the certificate's `wP_eff` obligation, and the
rule of thumb is short:

- **A memory-free run costs ONE `apply`.**  `WeakEff.exec_eff_quiet_of_empty`:
  instantiate your existing SC lemma at `MState rs ∅ d`; if it still succeeds
  with an empty final domain then the run performed no RAM access (a read of an
  absent byte returns `None`; a write GROWS the domain), and it therefore runs
  identically at any memory with a QUIET trace.  The decoder, every
  register-only `execute`, `pmpCheck`, `translateAddr`, `within_clint` and
  `currentlyEnabled` all fall to this.
- **A memory-touching run is a REPLAY, not a re-proof.**
  `WeakEff.exec_eff_bind_nil` / `_bind0_nil` are drop-in replacements for
  `RiscvExec.exec_bind_Some` / `exec_bind0_Some`; `_bind_Some` / `_bind_cons`
  carry the trace.  Measured on the whole `try_step` wrapper
  (`exec_eff_riscv_step_hart_active`): 65 SC lines → 68, 45 s of wall time.
- **Do not pin the fetch's trace element by element.**
  `WeakEff.wcert_store_gen` / `_load_gen` / `_amo_aq_gen` / `_fence_gen` allow
  ARBITRARY WRITE-FREE traces around the instruction's own access.
- **A branch/jump/ALU instruction's `Q` is `WeakEff.wQ_pure` (or `wQ_quiet`),
  NOT `wQ_none`** — see `iris/WeakBranch.v`'s header for why `wQ_none` cannot
  re-establish `wlat_interp`.
- **The zero-width residue is real and is documented.**  A zero-width access is
  invisible to `exec`, so the detector gives `quiet_trace` (which tolerates it)
  rather than `nowrite_trace` (which does not).  A syntactic bind-peel gives
  `nowrite` outright, since those arms are not in the program.
  **This is what decides where the detector may be used** (batch 0): a
  register-only sub-run INSIDE a bind spine must be mirrored to an empty
  trace, because `WeakEff.wcert_store_gen` / `_load_gen` / `_amo_aq_gen` need
  `nowrite_trace` and a zero-width write still appends a byte-less message
  (which falsifies `wQ_store`'s `wm_log σ' = wm_log σ ++ [msg]`).  Weakening
  the certificates to "up to `qmsgs`" was considered and rejected — the
  store's timestamp shifts by the quiet prefix's length, so `wQ_store` would
  have to name the timestamp existentially and the change ripples through
  `WeakLock` / `WeakAcquire` / `WeakStarted` / `WeakStore`.  The detector is
  for a WHOLE `execute` that touches no memory (branch / jump / ALU), where
  `wQ_quiet` is the right `Q` anyway.

---

## 2f. THE STEP SKELETON (M4 batch 0): what a leaf's `wP_eff` is made of

`iris/WeakEffSkel.v` is the `exec_eff` twin of the whole chain below
`WeakEff.exec_eff_riscv_step_hart_active`.  Two things to know before writing
a leaf:

1. **THE WHOLE STEP'S TRACE IS `es_fetch ++ es_execute`.**
   `WeakEffSkel.exec_eff_riscv_step_base` (and `_rvc`) takes the fetch's and
   the `execute`'s `exec_eff` facts — plus exactly the register/config
   premises `WeakFunnel.wwp_instr` already collects — and returns the step's.
   Everything between them (the privilege read, `should_inc_minstret`, the
   `minstret_increment` pre-write, the hart-active gate, the decode, the
   landing-pad check, the `nextPC` write, the PC tick, the `minstret` bump) is
   register-only and contributes nothing.  So **the only per-instruction
   `exec_eff` fact a leaf owes is its own `execute`'s.**
2. **THE JOIN WITH THE CERTIFICATE IS FREE.**
   `WeakEffSkel.wcert_load_via_skeleton` / `_store_` / `_amo_aq_` are
   `WeakCert`'s three certificates stated at `es_f ++ es_x`, and at
   `es_f := [fetch read]` that IS their own 2-/3-element list on the nose
   (`app` of singletons).  No adapter, no peeling.
   `WeakEffSkel.wP_eff_of_window` turns a window plus the per-`tick` run fact
   into `wP_eff` in one `apply`.

3. **BOTH SHARED PIECES ARE NOW LANDED** (batch 0b): the fetch's own
   `exec_eff` reduction (`iris/WeakFetchEff.v` §2–§4, over
   `iris/WeakPmpEff.v`) and the `tick_clock` mirror
   (`iris/WeakTickEff.v`, joined by `WeakFetchEff` §7). **A leaf now closes
   `wP_eff` — see §2g for the recipe.** Two boundaries to know:
   - **only the 4-aligned `F_Base` fetch arm is mirrored.** A compressed or
     2-aligned instruction has no `wP_eff` route yet (the split fetch emits
     TWO 2-byte reads, so it also needs a 3-element `wcert_*`).
   - **the fetch's trace element is `WEread (AkInfo false false false) pc 4`**
     (`WeakFetchEff.wak_plain`) — rv64d emits `AK_explicit`/`AV_plain`, not
     `AK_ifetch`, so the fetch is an ordinary view-raising read.

---

## 2g. THE COMPLETED RECIPE: what a batch-2 leaf writes, in order

Landed at batch 0b/1. Five moves; nothing else about an instruction enters.

1. **The certificate.** `wcert_load_base4` / `wcert_store_base4` /
   `wcert_amo_aq_base4` (`WeakFetchEff` §9a) are `WeakCert`'s three, stated
   at the concrete fetch element this tree produces. ONE `exact`. The `P`
   they name is `wP_eff (Some cid) ([WEread wak_plain pc 4] ++ es_x)`, and
   `[a] ++ [b]` IS `[a; b]`, so it is the recipe's conclusion on the nose —
   **no adapter, no `app` lemma, no peeling.**
2. **The `execute`'s `exec_eff` fact.** Batch 1's per-shape lemma
   (`WeakLeafEff8.exec_eff_execute_LOAD_8_gpr`,
   `WeakLeafEff8s.exec_eff_execute_STORE_8_gpr`, …), instantiated TWICE: once
   at `wflat_st σ` for the funnel's SC obligation, once at
   `MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)` for the certificate.
   Every such lemma is state-generic, so the second instantiation is free
   except for its memory premises, which come from the same
   `wpt*_flat` / `wkernel_text_flat` facts through
   `WeakCert.wmem_restrict_lookup`.
3. **The decode fact costs ONE extra `vm_compute`.** Use
   `WeakFetchEff.decode_bridge_eff D dst` (or `exec_eff_decode_bridge`)
   exactly where the SC leaf uses `WpDecodeBridge.decode_bridge D dst`; the
   only new obligation is `goodb0 D (ext_decode w) dst = true`, discharged
   by `vm_compute; reflexivity` like its `goodb` sibling. **Do not restate
   decode lemmas at `exec_eff`.**
4. **The window and `wP_eff`.** `WeakFetchEff.wP_eff_of_leaf_base`, fed the
   window's three obligations (`pa_z a ≠ 0` from `addr_is_ram`;
   `pinned_read` from `WeakFunnel.winstr_pinned` for the text and
   `wpt4_pinned`/`wpt8_pinned` for the data), the M-mode config tower (the
   SAME facts `wwp_instr` already collects), the four text bytes in the
   CONFINED memory, the decode of (3) and the `execute` fact of (2).
   Its window binder is spelled `(W : _)` for the instance-trap reason in §4
   below; keep it that way at every call site.
5. **The WP.** `WeakFunnel.wwp_instr` with that `P` and the shape's `Q`, and
   §2b's four moves for the Iris half.

**What is NOT free and is the whole per-leaf cost:** the window `W` and the
second instantiation of the shape lemma at the restricted memory. Everything
else above is an `apply` or an `exact`.

## 3. What needs thought: the racy sites, and only those

A function that OWNS its memory — directly or through a lock — ports
mechanically: `↦w`'s load and store rules ARE the SC rules (Cosmo), and
`WeakInstr.wstep_post`'s `ws_le` conjunct carries every untouched resource
across a step for free (`WeakVProp.vwp_hold_mono`, `wpt4_mono`).  The sites
that need real thought are the ones that read a byte another hart may be
writing:

- **the lock word** — `iris/WeakLock.v`; nothing else in the kernel touches
  it, so port `acquire`/`release` once and every client is unchanged in
  statement (`wlocked γ i` IS `WpLock.locked γ i`);
- **the view layer is NOT re-exported** (a five-minute trap, hit twice): a
  file that `Require Import WeakInstr`s still does not have `view`, `ws_view`,
  `amo_acq_gain` in scope — `Require Import` is not transitive. Any file that
  names a view-layer constant must require `WeakView WeakVProp WeakFence`
  itself. The error is `The reference view was not found`;

- **`started`** — `iris/WeakStarted.v`; the reader's load may read a STALE
  message, which is the one thing the SC escrow never had to say.  The escrow
  carries `wstarted_oneshot` (every non-clear write to the byte is the
  setter's message) precisely to turn "the value I read is nonzero" into "the
  timestamp I read is the escrow's".
  **AND ITS LOAD IS THE ONE INSTRUCTION `wp_winstr` CANNOT RUN** (M3c, see the
  note at the end of `iris/WeakAcquire.v`): the rule rests on the
  PINNED-fragment bridge, whose read arm demands that the hart's index already
  cover the latest write to every byte read, and a waiting hart legally reads
  the era image while the flat projection already holds the setter's 1 — so no
  `exec` fact about `wflat_st σ` describes the step. The AMO is unaffected
  (its read half is `ak_latest`, whose admissibility condition IS "read the
  latest"), which is why the whole SPINLOCK composes and this does not.
  What it needs is a load rule that quantifies over the ADMISSIBLE READ
  RESULTS — one `exec` fact per admissible value (two, for a one-shot flag),
  yielding a disjunction that `wstarted_oneshot` collapses — built over
  `WeakExec.wp_wrun_step`, the primitive rule that has no bridge premise.
  **Build that rule before porting `ProofMainSecondary`;** the setter
  (`WeakAcquire.wwp_started_set`) and the reader's FENCE
  (`wwp_fence_step` + `wwp_started_fence_deliver`) are done;
- **the virtio ring and the MMIO seams** — M5, and the driver gets patched
  (`fence w,o` / `fence i,r`) rather than the model accommodated.

For each racy site the shape is the same and it is worth internalising it as
a slogan: **the invariant is an `iProp`, the payload is `monPred_at P V`, and
the number that links the two halves is the message's timestamp.**

---

## 4. The failure modes that COMPILE

Every one of these type-checks and is wrong or vacuous.

1. **A `↦w□` at a timestamp > 0 is PERSISTENT but NOT OBJECTIVE.**  Putting
   one in an invariant is unsound.  Only `wpt_img` (timestamp 0 — the era
   image, i.e. text and rodata) is objective.  Persistence and objectivity
   are independent here; the type checker will not tell you.
2. **Depositing at the WRONG view still type-checks.**  `monPred_at R V` is
   monotone in `V`, so depositing at a view that is too LARGE is unprovable
   (good) but depositing at one that is too SMALL is provable and useless —
   and the uselessness only surfaces at the far end of the handoff, in the
   acquirer's proof.  Deposit at `view_scl (S (length (wm_log σ)))`
   (`WeakInstr.wwp_release_deposit`) and nowhere else.
3. **Forgetting to update the latest-write ELEMENTS after a store.**  The
   state interpretation's `wlat_interp` says every element IS the latest
   write; a store that appends a message writing bytes whose elements you did
   not retarget makes `wmstate_interp σ'` unprovable — but the failure
   appears at the END of the leaf, in the "give the interpretation back"
   obligation, hundreds of lines from the store.  Use
   `WeakStore.wlat4_store` / `wpt4_store`, and remember an AMO writes too
   (even the contended arm: `amoswap` swaps 1 in when it read 1).
4. **A window `W` that omits the data word still proves `wstep_ok` — until
   the write arm.**  The read footprint is confined by the map's domain but
   the WRITE footprint is confined by `dom (mem t') ⊆ W`.  If you forget the
   store's target, that conjunct is what fails, and it fails in the caller,
   not in `WeakCert`.
5. **`acc_wf` (wrap-freedom) silently controls whether the `Z`-keyed log and
   the `Arch.pa`-keyed flat map agree.**  It is carried IN `wpt4` for exactly
   that reason; if you build a bundle by hand and drop it, `acc_wf_byte`
   stops applying and the failure reads as a "does not match any subterm" on
   an address that visibly matches.
6. **The vacuity trap is unchanged** (`tools/spec_vacuity.py`): an
   unparenthesised `∀` inside a wand chain swallows the trailing `WP`.  The
   tool now takes file arguments and a `--lemmas` mode; run
   `tools/spec_vacuity.py --lemmas iris/Weak*.v` per batch (§0), because the
   default run scans only `_body` definitions and a `Weak*.v` has none.
7. **A `Q` that is too WEAK still type-checks and still composes** — until the
   invariant has to be re-established, hundreds of lines later, in the
   `wmstate_interp σ'` obligation.  The characteristic version is a store
   whose `Q` gives views but not the message (see §2c).  Fix the `Q`, never
   the proof.
8. **A window `W` big enough for the reads but not the writes** is failure
   mode 4 above; the twin at the `Q` level is an effect list that omits the
   FETCH read.  Every instruction's trace begins with the fetch — rv64d emits
   `Read_plain` for instruction fetch, so it is an ordinary weak read that
   raises views, and a `Q` proved against a trace without it is about a
   different machine.
9. **`Print Assumptions` is the only real check on a functor/seal cone.**
   Expect the 5 rv64d platform axioms for anything mentioning `riscv_step`,
   and "Closed under the global context" for everything that does not — the
   whole vProp/view/bridge/certificate layer is axiom-free, so a NEW axiom in
   that layer is a regression, not a cost of doing business.

10. **A MIRROR FILE MUST IMPORT `iris.proofmode` EVEN WITH NO IRIS IN IT.**
   Every SC script in the `exec`/`execR` cone uses ssreflect's
   space-separated `rewrite a b c` and `rewrite H /=`; without the import
   those are *syntax errors reported at the `/=`*, which reads as a
   nonsensical complaint about a line you did not change.  Two smaller ones
   from the same batch: stdpp's `by` does not parse inside
   `try (…; by tac)` in such a file (write `; tac; reflexivity`), and `mword`
   must be spelled `SailStdpp.Values.mword` (the instance-leak rule in the
   durable notes).
11a. **A `gset Arch.pa` BINDER IS AN INSTANCE TRAP IN ANY FILE THAT IMPORTS
   `SailStdpp.Base`** — and the mirror files must import it (`'b"1"`, `Ok`,
   `generic_eq` all live there).  A binder spelled `(W : gset Arch.pa)` then
   elaborates against `Countable_mword` while `WeakCert.wmem_restrict` uses
   `bv_countable`; the two print IDENTICALLY and every application fails with
   an unreadable type mismatch.  Write **`(W : _)`** and let
   `wmem_restrict σ W` pin it.  A `Section Context` cannot do this (it will
   not accept a hole), which is why `wP_eff_of_leaf_base` is one `Lemma` with
   a commented premise list rather than a Section — keep it that way.
11. **A domain-growth argument can never exclude a VALUE-PRESERVING write.**
   This is why the fetch needs a syntactic `exec_eff` mirror and cannot be
   detected: running it at the confined memory and observing
   `mem t' = mem s` is consistent with a write that stored the same bytes,
   and such a write would invalidate the `wkernel_text` elements.  Recorded
   at M3c for the general case; it bites again at the fetch.

---

## 5. Order of the sweep (revised after M4-prep)

0a. **DONE** — `iris/WeakEffSkel.v` (834 lines / 3.9 s): `execR_eff` plus its
   rewriting kit, the two `run_hart_active` progress mirrors, the step
   assembly and the certificate join (§2f).
0b. **DONE** — the fetch's `exec_eff` reduction (`iris/WeakFetchEff.v` §2–§4
   over `iris/WeakPmpEff.v`), the `tick_clock` mirror
   (`iris/WeakTickEff.v`), and `wP_eff_of_leaf_base` (§2g). 1867 lines /
   9.8 s, vs the 250–350 + 25 estimate — **price the transitive cone a chain
   NAMES, not the chain in front of you.** 4-aligned `F_Base` arm only.
1. **The memory `execute` mirrors, by SHAPE not by call site.**  LOAD 8 and
   STORE 8 are **DONE** (`iris/WeakLeafEff8.v`, `iris/WeakLeafEff8s.v`, ≈ 700
   lines each — not the 30–60 estimated, for the same transitive-cone
   reason).  LOAD 4 / STORE 4 / AMOSWAP 4 additionally need their SC lemma
   written (the M-mode library has width 8 only, and only S-/U-flavoured
   AMO chains exist).  Widths 1 and 2 are batch-6 territory: recorded, not
   built.
2. The M-mode leaf libraries through `WeakFunnel.wwp_instr` (§2d) —
   `WpMmodeLoad`, `WpMmodeStore`, the `WpMmodeLeaf*` family.  Their config
   tower and decode facts transfer as-is.
3. `WpLock` clients — nothing to do beyond the `iProp`→`vProp` altitude change
   of `R`, since the interface is unchanged; the `↦w₈` tower
   (`iris/WeakWord8.v`) now covers the lock's `cpu`/`name` fields.
4. The straight-line M-mode function proofs, batched by subagent.
5. `StartedInv` consumers (`ProofMainSecondary`) on the racy-load rule (§3).
6. **The sconf tier** — blocked on the page-table-walk design (§2d); do NOT
   schedule an S-mode batch before it.
7. The virtio cone (M5).

The BRANCH leaves are no longer on this list: `iris/WeakBranch.v` landed them,
and `wwp_acquire_loop_real` is the acquire loop with the retry edge proved.

`tools/lemma_diff.py` after every batch: the characteristic failure of a
sweep is not a red build, it is a file that compiles because something was
quietly dropped.
