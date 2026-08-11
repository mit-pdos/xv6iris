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
| `WP e` (SC, Φ-free since main's postcondition removal) | `WWP e` / `WWP e @ E` (`WeakGhost.wwp_triv`) | a DISTINCT token, deliberately: both languages' `expr` convert to `mexpr`, so a same-syntax `WP` twin could elaborate a weak statement at the WRONG language and still compile.  No `{{ Φ }}` anywhere; no `(… : expr weak_riscv_lang)` annotation either — `wwp_triv`'s argument type pins the language.  If a generic iris wp lemma fails to `iApply`, pin `(Λ := weak_riscv_lang)` |

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
3. pinnedness — `WeakInstr.wkernel_text_pinned` for the text half (never
   written this era ⇒ free) and `wpt4_pinned` for an OWNED data word.  THE
   EXACT ACCOUNTING IS TRACE-KEYED (`WeakCert.trace_pin`): pinnedness is
   needed precisely for the reads whose kind does NOT self-pin
   (`ak_pins ak = false`); a self-pinning read — `ak_coh` (fetch/walker) or
   `ak_latest` (an AMO's read half) — is exempt.  The whole-window form
   `∀ a ∈ W, pinned_read σ (pa_z a)` (what `wP_conf`/`wP_eff` demand)
   over-approximates: right for owned-data leaves, UNPROVABLE for a contended
   AMO — such a leaf uses `WeakCert.wP_eff_pin` and pins only the fetch.
   Either way an AMO's data word must still be listed in `W`, because the
   WRITE's footprint is confined by `W` too;
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
- **KNOW THE BOUNDARY: a racy read's view GAIN is NOT in this class** (batch
  5, and it cost a first attempt). "The timestamp behind the byte I read is
  under my `w_vrOld`" looks per-instruction — `Q` is a relation on STATES and
  cannot name the read word — but the BRIDGE's own induction has the
  timestamp list (`wread_ok`'s `ts`) and `WeakMem.load_post_run_vrOld` puts it
  under the floor on the spot, so it comes out of the same traversal as
  `wadm`: `WeakRacy.wgain`, proved by `exec_of_wrun_gain`, exposed as
  `wp_wracy_load_gain`. What is left for the leaf (`WeakRacy.wreads_win`, "the
  step READS the window") has no weak-memory content at all. **A view
  obligation that looks per-instruction is usually a bridge obligation plus an
  SC one; check before making the leaf pay.**

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
   **GIVE THE FUNNEL THE WHOLE `mmode_config`, and do not split it.**  The
   callback is handed `⌜WeakFunnel.wcfg_regs σ pmpcfg0⌝` — the twelve config
   facts the funnel has just read (cur_privilege / hart_state / misa /
   mseccfg / pmpcfg_n / pma_regions / htif, plus the misa.S, mstatus.MIE,
   mstatus.MPRV, mseccfg.PMM and elp bits), all at `wm_regs σ` and in exactly
   the shape `wP_eff_of_leaf_base` and the `execute` lemmas consume — and the
   bundle comes back whole for the continuation.  The only register a leaf
   still reads for itself is the one the funnel cannot know: its own operand
   (`reg_valid` + `WeakLeafLd8.reg_at_flat`, two lines).
   **The device frame is handed over too**, as `⌜mdev t = mdev s_exec⌝`;
   combine it with your `execute`'s own "moved no device" fact (the
   `ld8_sexec_facts` conjunct) to get `wm_dev σ' = wm_dev σ` for
   `dev_interp`.  Both arrived after batch 2 measured what their absence
   cost: 116 + 43 lines per leaf.
4. **The certificate is the only irreducible part**, and it is §2/§2c: the
   window `W` plus the same SC library lemma re-instantiated at
   `WeakCert.wmem_restrict σ W`.

Measured budget on top of the SC leaf: see §2g — the whole first leaf is
**472 code lines / 3.1×**, of which the window is 65.

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
   - **the two 4-ALIGNED fetch arms are mirrored**, `F_Base`
     (`wP_eff_of_leaf_base`) and `F_RVC` (`iris/WeakFetchRvc.v`,
     `wP_eff_of_leaf_rvc4`) — compressed or not, any 4-aligned pc. A pc that
     is 2- but not 4-aligned has no `wP_eff` route yet (the split fetch
     emits TWO 2-byte reads, so it also needs a 3-element `wcert_*`).
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
   decode lemmas at `exec_eff`.** The same bridge carries a STATE-GENERIC SC
   fact — a compressed instruction's `ExecuteAs` expansion, any register-only
   `execute` — with no reference state at all:
   `WeakFetchRvc.exec_eff_of_goodb0_self` is the bridge at `dst := s`.
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

**THE UNIT PRICE, MEASURED AND THEN FIXED** (`iris/WeakLeafLd8.v`, the
`ld`-class 8-byte load — read it before writing your second one). Code lines,
comments and blanks excluded, against the SC leaf `WpMmodeLoad.wp_ld_gpr` at
152 by the same count:

| | at batch 2 | after the two seam fixes |
|---|---|---|
| the width-generic certificate (§1) | 37 | 37 — **once per FAMILY** |
| the window + its 3 obligations (§2a/b) | 65 | 65 |
| the `execute` lemma at a generic `s0` (§2c) | 137 | 137 |
| the `wP_eff` half (§2d) | 102 | 102 |
| the second replay, for the device frame (§3a) | 116 | **0** |
| the WP composition (§3b) | 191 | 142 |
| **per-leaf total** (all but the certificate) | **611 / 4.0×** | **472 / 3.1×** |

Of the 472, 137 is the `execute` block hoisted to a generic `s0` (~50 of which
the SC leaf does inline) and 167 is the window + `wP_eff` half this guide
predicted; the genuinely new work is 309, half of it the WP composition.

**THE TWO SEAMS ARE FIXED — do not re-derive what the funnel now hands you.**
`wwp_cb`'s post-step arguments include `⌜mdev t = mdev s_exec⌝` (do NOT replay
`riscv_step` at the flat state to learn the device frame) and its pre-step
arguments include `⌜WeakFunnel.wcfg_regs σ pmpcfg0⌝` (do NOT split
`mmode_config` and re-read the config). See §2d.3.

**ONE THING THE BUNDLE DOES NOT FIX:** the decode bridge's `agree_on D`
premise is still ∀-over-register-files in a LEAF'S STATEMENT — a leaf is
stated before `σ` exists, since `wwp_cb` quantifies over it — but
instantiating it is now three `exact`s off `wcfg_regs` (cur_privilege = Machine,
misa = MISA_C, mseccfg = 0), not three register reads.

**TWO CONVENTIONS to follow from leaf one:** state the `execute` lemma over an
ARBITRARY `s0 : mstate` (so confined and flat are the same lemma twice, and
the `gmap Arch.pa` binder trap never arises), and define any `gset Arch.pa`
window ABOVE the `SailStdpp.Base` import.

**AND ONE FILE TO ADD TO, NOT COPY FROM: `iris/WeakLeafEffCommon.v`.** The
`exec_eff` twins of `returnM` / the two boolean connectives / the two bus
arms, and every width- and access-INDEPENDENT leaf (`split_misaligned`
unsplit at the physical address, the page-boundary split, `pma_ok_eff_peel`
and the mag/assert kit — the whole post-sail-bump pmaCheck walk —
`translationMode Machine`, `rX_bits`/`wX_bits`/`ext_data_get_addr` over
the GPR file, the one-turn `untilMT`), live there. A new shape file requires
it; it does not re-declare them. (Batch 1's four shape files each had their
own copy — 40 lemmas of duplication, retired.)

## 2h′. WRITE A WHOLE-FUNCTION CHAIN ON THE SC-SHAPED INTERFACE (current recipe)

**Read this before §2h, which is the superseded hoisted-leaf recipe kept for
its trap list.** As of the 2026-08-11 conversion (`weak-memory.md`, "THE CALL
SITES ARE CONVERTED") a whole-function M-mode chain is written on
`WeakLeafO`'s `_run` wrappers and comes out at **1.4× its SC twin**, not 3×.
`iris/WkTimerinit.v` (21 instructions) and `iris/WkStartNew.v` (39) are the
two worked examples; read the shorter one.

The recipe, in order:

1. **Statement.** `mmode_config (DfracOwn q)` → `WeakLeafO.whart_run ξ q`;
   every frame → `WeakCtx.cobj ξ R`; add `(ξ : CtxId)` as the first binder.
   NO `ws` binder, NO `∀ ws'`, NO `⌜ws_le …⌝` in the continuation. If the
   function's last instruction is `mret`, the postcondition hands back a bare
   `wrunning ξ` (the bundle is dissolved, not preserved).
2. **A `Wk<F>Aux.v` file** with one `wsti_NN` token per instruction, built
   with `WeakLeafM.winstr_m_of_text` — see `WkTimerinitAux.v` (written from
   scratch) or `WkStartAux` §4b/§5 (which reuses decode facts that were
   already there). The token is the ONLY place a decode fact is named.
3. **Per instruction, two lines**: `iPoseProof (wsti_NN kbs Hcov with "Htext")
   as "#HiNN".` then `iApply (wwp_X_run ξ … with "Hrun Hpcf Hpc Hfile HiNN").`
   and one `iIntros` naming the resources back. Everything else at the site
   is the register-map bookkeeping the SC file also does.
4. **Frames are not threaded.** Split the stack bundle ONCE at the top with
   `cobj_mono`/`cobj_sep`/`cobj_exist`, leave each piece in the context, and
   re-bundle at the end. No `vwp_hold_mono`, ever.
5. **`pc_is` stays bundled** — the `_run` wrappers take and return it whole,
   so there is no `iDestruct "Hpc" as "[Hpc Hnpc]"` and one
   `iEval (rewrite P_NN) in "Hpc"` per step.
6. **A cell-based site** (`csrr`/`csrw mstatus`, `csrw pmpcfg0`, `mret`) is
   `whart_run_open` → the SC file's own unbundle/join dance → `wwp_X_o` with
   `Hview` → re-split → `mmode_config_rebuild` → `whart_run_close`.

Its own traps: the four in the conversion slice's list (the missing `al4` on
`csrw mstatus`, the wider CSR-name collision, `(kbs : _)`, `iFrame` on a
`cobj`), plus — **check for callers of the function whose statement you are
changing, with a full grep, before you start**: a converted callee needs a
converted caller.

## 2h. WHOLE-FUNCTION CHAINS OVER THE HOISTED LEAVES (from wwp_timerinit) — SUPERSEDED BY §2h′

*The chain shape here (leaf per instruction, `ws` threaded, frame bundled and
bumped) is no longer how a chain is written; the traps below are still real
for anyone working BELOW the wrapper layer, which is why the section stays.*

`iris/WkTimerinit.v` was the first whole-function chain built entirely by
applying the hoisted leaves (21 instructions, one leaf application each,
~1650 lines ≈ 3× the SC file — vs `WkEntryNew`'s 9.8× inline price).
Statement = the SC statement under §1's swaps; `ti_*`/`m_*` vocabulary
imported unchanged. The traps, all of which COMPILE until late:

1. **The gpr-file accessors take raw `gpr_pt`, not the plain register
   points-to the leaves hand back** — every fold-the-cell-back step needs
   the REVERSE `gpr_pt_nz` rewrite, not a second forward application.
2. **A load's two-cell reinsertion is NOT symmetric with a store's**: the
   base cell round-trips unchanged but the destination's new value must
   survive as a distinct `<[rd:=v]>` layer to match the SC file's named
   maps (the SC leaf is file-based and never re-touches the base, so its
   maps have no base reinsertion at all). Collapsing both keys with the
   store-shaped lemma silently produces the wrong map shape.
3. **A CSR read whose value is only known when the leaf returns** (csrr
   time's `tv`) cannot use `gpr_file_insert_acc` (which fixes the
   reinsertion value at extraction time) — use the ∀-target
   generalization (`WkTimerinit.gpr_file_reinsert_acc`; hoist it on next
   touch).
4. **The TOR leaves' 16-premise lists have TWO `eq_refl`-closable slots
   that are not adjacent** — an extra `eq_refl` inserted off by one
   type-checks as "one too many args" only at Qed-adjacent unification.
5. **`vwp_hold_mono` must be bumped per leaf for every carried stack
   word** — each `vwp_hold` is indexed by a specific view and every leaf
   mints a fresh one; a skipped bump surfaces as an `iSpecialize`
   mismatch far from the omission.
6. **`vm_compute; reflexivity` can fail on propositionally-equal
   bitvector constructions** — close with a `bv_eq`-backed reflexivity
   (the `decode_bridge_ms_bv` recipe), not bare `vm_compute`.
7. Concurrent-agent note: transient "inconsistent assumptions" errors
   from OTHER files rebuilding underneath you clear on their own — poll,
   never `make`, never touch the flagged files.
8. **`rewrite !vwp_hold_sep` SHATTERS `wpt8`.**  A frame bundle is
   `vwp_hold (w1 ∗ w2 ∗ rest)`, but `wpt8` is ITSELF a `∗`-chain
   (alignment + `acc_wf` + eight byte points-tos), so the `!` recurses
   into it and `iFrame` is left with nothing to match the unshattered
   `vwp_hold (wpt8 …)` hypothesis against.  Peel ONE `∗` at a time
   (`iEval (rewrite vwp_hold_sep). iSplitL "H"; [iExact "H"|]. …`), in
   both directions.  The failure reads as `This proof is focused, but
   cannot be unfocused this way` at the closing brace — nowhere near the
   rewrite.
9. **A store leaf's payload `R` is `⌜True⌝ : vProp Σ`, not `emp`** —
   built with `iAssert (vwp_hold (⌜True⌝ : vProp Σ) ws) as "HR". {
   rewrite vwp_hold_pure. done. }`.  Passing `emp%I` and discharging it
   with the `[//]` spec pattern fails as `iSpecialize: (IAnon N) not
   found`, which names neither the payload nor the leaf.
10. **Bump ONE bundled `vwp_hold`, not each word.**  Bundle the whole
   frame (both own slots + the callee's 2-slot sub-frame + the deep
   rest) into a single `vwp_hold` right after the prologue's stores;
   each later instruction then costs exactly one `vwp_hold_mono` line
   instead of five.  Split it only at the call site and at the final
   re-bundle.  Feed the leaves the cells at their NAMED values
   (`-(rf_lookup m k) Lk` after `gpr_pt_nz`), which also makes the
   store's ea premise `eq_refl`.

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
  **THAT RULE IS BUILT AND THE WHOLE HANDOFF COMPOSES** (M4-prep + batch 5):
  `WeakRacy.wp_wracy_load` and, with the view gain proved from the model,
  `wp_wracy_load_gain`; the escrow's reader is `WkStartedLoad.wwp_started_load`
  (premises `ak_coh rak = false` + `WeakRacy.wreads_win`, plus a
  `WeakRacy.wunwritten` out of the σ-callback — the hart must not have stored
  to the flag itself, or it reads its own forward bank); the setter is
  `WeakAcquire.wwp_started_set`; the fence is `wwp_fence_step` +
  `wwp_started_fence_gen`/`_r`, stated at any pred-R kind
  (`WeakFence.acq_pred_r`), which is what the kernel's `fence r,rw` needs.
  `iris/WkStartedMp.v` is the end-to-end MP composition, with
  `mp_load_alone_does_not_deliver` / `mp_fence_delivers` for why the fence is
  there. What still blocks `ProofMainSecondary` is the S-mode funnel (batch
  6c), not the rule;
- **the virtio ring and the MMIO seams** — M5, and the model is not
  accommodated to a driver that does not fence I/O.  The driver side is
  already done: virtio_disk.c's barrier sites are `io_fence()` =
  `fence iorw,iorw`, which covers the `w,o` and `i,r` edges.

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
12. **A TRANSPARENT `kb_word_at` IN A LEAF'S FETCH WORD IS A 100× COMPILE
   CLIFF** — and it does not fail, it just never finishes, so it reads as
   "Iris is slow" rather than as a bug.  `kb_word_at A` is four lookups in
   the whole `KernelInstrs.kernel_bytes` map.  `vm_compute` dispatches it in
   microseconds (measured: 0.0 s), but the UNIFIER inside `iApply` reduces
   with LAZY conversion, so a leaf instantiated at
   `h := subrange_vec_dec (kb_word_at …) 15 0` makes every unification step
   walk that map.  Measured on `wwp_start`: ONE `wwp_addi_rvc_leaf` did not
   finish in 10 minutes at `kb_word_at` and takes 2.7 s at
   `mword_of_int 0x1141`; the decode-fact file went 9 min → 15 s and the
   whole 39-instruction chain from >30 min (never finished) → 53 s.
   **Define every instruction word as a closed `mword_of_int` literal**
   (`WkTimerinit` did this from the start; `WkStartAux` §0 now carries the
   39 of them with the derivation in a header comment) and tie it back to
   the image ONLY in the `stkb_*` byte-window lemmas, whose `kb_win` proof
   is a `vm_compute` and so is cheap.  Price of the literal form: the
   `subrange_vec_dec w 15 0 = h` conjunct needs `apply bv_eq` before its
   `vm_compute`.  **The same rule applies to any image-derived term a leaf
   is INSTANTIATED at** — if `iApply` can see it, it must be a literal.
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
1. **DONE — all five shapes**: LOAD/STORE at 8 (`iris/WeakLeafEff8.v`,
   `WeakLeafEff8s.v`), LOAD/STORE at 4 (`WeakLeafBase4.v`) and the M-mode
   `amoswap.w.aq` (`WeakLeafAmo4.v`).  **4082 lines, ≈ 800 per shape**
   against the 30–60 estimate — the same transitive-cone correction as 0b
   (the `vmem_read`/`vmem_write` cone below an `execute` is not detectable
   either, so it is mirrored whole).  Three of the five needed their SC
   lemma written as well (the M-mode library had width 8 only, and only
   S-/U-flavoured AMO chains existed); those halves are 399–613 lines and
   replay the width-8 template essentially line for line.  Widths 1 and 2
   remain batch-6 territory: recorded, not built.
2. The M-mode leaf libraries through `WeakFunnel.wwp_instr` (§2d, §2g; the FIRST one is landed, `iris/WeakLeafLd8.v` — read it) —
   `WpMmodeLoad`, `WpMmodeStore`, the `WpMmodeLeaf*` family.  Their config
   tower and decode facts transfer as-is.
3. `WpLock` clients — nothing to do beyond the `iProp`→`vProp` altitude change
   of `R`, since the interface is unchanged; the `↦w₈` tower
   (`iris/WeakWord8.v`) now covers the lock's `cpu`/`name` fields.
4. The straight-line M-mode function proofs, batched by subagent.
5. `StartedInv` consumers (`ProofMainSecondary`) on the racy-load rule (§3) —
   **the rule, the escrow, the gain and the fence delivery are all landed**;
   the file itself is pure-sconf, so it now waits on 6 below, not on §3.
6. **The sconf tier** — blocked on the page-table-walk design (§2d); do NOT
   schedule an S-mode batch before it.
7. The virtio cone (M5).

The BRANCH leaves are no longer on this list: `iris/WeakBranch.v` landed them,
and `wwp_acquire_loop_real` is the acquire loop with the retry edge proved.

`tools/lemma_diff.py` after every batch: the characteristic failure of a
sweep is not a red build, it is a file that compiles because something was
quietly dropped.
