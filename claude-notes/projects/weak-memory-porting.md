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
  `tools/spec_vacuity.py`.

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

**The register/CSR/config tower does not move at all.**  `hw_config`,
`mmode_config`, the sconf bundles, `kmap_static_claims`, `pc_is`, `↦ᵣ`, all
ghost state and every pure fact are `iProp`s over `riscvGS`, which the weak
side carries unchanged; embedded into `vProp` they are objective by
`embed_objective`.  `reg_valid`/`reg_valid_dq`/`reg_update` apply VERBATIM,
because `wmstate_interp σ` contains `reg_interp (wm_regs σ)` and
`wm_regs σ = sregs (wflat_st σ)`.  The only non-transferring lemmas are the
ones that consume `RiscvPtsto.mstate_interp` AS A BUNDLE
(`fetch_from_instr_bytes`, `instr_lift`, `dispatchInterrupt_none_from_regs`,
`state_interp_reg_dq`, `wp_instr`) — each is a mechanical restatement with
the memory hypothesis taken as the pure fact `WeakInstr` §1 produces.

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
fact, and only the three sync instructions have one worth stating.

---

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
- **`started`** — `iris/WeakStarted.v`; the reader's load may read a STALE
  message, which is the one thing the SC escrow never had to say.  The escrow
  carries `wstarted_oneshot` (every non-clear write to the byte is the
  setter's message) precisely to turn "the value I read is nonzero" into "the
  timestamp I read is the escrow's";
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
   unparenthesised `∀` inside a wand chain swallows the trailing `WP`.  Note
   that the tool scans `Spec*.v`/`Wp*.v`/`Code*.v` for `_body` definitions and
   IGNORES a file argument — a new `Weak*.v` is not covered, so hand-check
   that every `∀` in a wand chain is a Coq binder before the chain.
7. **`Print Assumptions` is the only real check on a functor/seal cone.**
   Expect the 5 rv64d platform axioms for anything mentioning `riscv_step`,
   and "Closed under the global context" for everything that does not — the
   whole vProp/view/bridge/certificate layer is axiom-free, so a NEW axiom in
   that layer is a regression, not a cost of doing business.

---

## 5. Order of the sweep

1. the leaf libraries' MEMORY arms (`Wp*Load`, `Wp*Store`, `WpSconfMem`) —
   each is one `wpt4_flat` + one `wstep_cert` per instruction shape;
   everything else in them is the config tower and transfers as-is;
2. `WpLock` clients — nothing to do beyond the `iProp`→`vProp` altitude
   change of `R`, since the interface is unchanged;
3. the straight-line function proofs, batched by subagent;
4. `StartedInv` consumers (`ProofMainSecondary`), then the virtio cone (M5).

`tools/lemma_diff.py` after every batch: the characteristic failure of a
sweep is not a red build, it is a file that compiles because something was
quietly dropped.
