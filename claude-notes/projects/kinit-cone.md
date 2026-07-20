# Project: the kinit cone (kinit → initlock + freerange, over kfree)

`kinit()` = `initlock(&kmem.lock)` then `freerange(end, PHYSTOP)`, with the
`is_kmem` lock invariant allocated (via `newlock`) in between.

## initlock (WpInitlock.v)

Whole-function WP for the 11-instruction `initlock` (prologue / 3 field stores
name·locked·cpu / epilogue).  Spec owns the spinlock's three struct fields as
raw memory (`lk ↦₄ vlock`, `lk+8 ↦₈ vname`, `lk+16 ↦₈ vcpu`) and returns them
initialised (`lk ↦₄ 0`, `lk+8 ↦₈ name`, `lk+16 ↦₈ 0`) + `callee_saved`.

Reusable leaf **`wp_sw_zero_s`** (+`_pt`/`_scfg`): the plain 4-byte zero store
over a PLAINLY-owned `↦₄` word (width-4 sibling of `wp_sd_zero_s`).  Needed
because `lk->locked := 0` precedes the lock's invariant — the `_lockinv`
sw-zero leaf does not apply pre-lock.

RULE: x0 stores MUST use the zero leaves (value `zero_reg`); the generic
`wp_sw_s`/`wp_sd_s` post `m!!!Regidx rs2` is only correct for `rs2≠0` (the model
reads x0 = 0).

## kfree — cell threading

kfree returns the three per-CPU scratch cells in its post
(`q_noff ↦₄ q_noff_ret`, `q_intena ↦₄ q_int_ret`, `q_cpu ↦₈ zero_reg`), so a
repeated caller (freerange) can thread the same fixed cells across iterations.
Address gotcha: `release`'s `m` is `Rrel` (not kfree's m), so its post cells are
keyed on `Rrel!!!{4,10}` — convert with the same facts kfree used to pass them
IN (`rewrite HRrela0 -Hlk` for cpu; `rewrite HRreltp -Ha0fcpu` for noff/int).

## freerange (TODO — the hard loop) @ 0x80000ab2, 30 instrs (+0x00..+0x46)

Shape: prologue saves ra@40/s0@32/s1@24 (48-byte frame); computes
`s1 = PGROUNDUP(pa_start)+PGSIZE` (c.lui a5,1 / addi a4,-1 / add / c.lui
a4,0xfffff mask / c.and / c.add); `bltu a1,s1` (+0x1a) SKIPS the loop to the
epilogue when no full page fits — the CONDITIONAL s2/s3/s4 saves (+0x1e..+0x28)
and the loop live only on the fall-through; loop body (+0x2a..+0x34):
`a0 = s1+s4 = p` (s4 = -PGSIZE mask), `jal kfree`, `s1 += PGSIZE`, `bgeu s2,s1`
back edge; then restore s2/s3/s4; epilogue.  s1 holds `p+PGSIZE` throughout;
a0 = s1-PGSIZE = the page freed.

- BOUNDED loop ⇒ fuel induction (NOT iLöb — packaged leaves strip the ▷).
  Fuel = length of the remaining page list.  Two exit paths (loop-skipped vs
  loop-ran) converge at the epilogue with DIFFERENT s2/s3/s4 states (skipped:
  never saved, unchanged ⇒ callee_saved trivially; ran: saved+restored).
- Spec: `is_kmem γ lk fl` (persistent) ∗ `smode_config`+ghost SIE+`sr_inv` ∗
  a page big-sep `[∗ list] p ∈ ps, page_own p` where `ps` = the pages
  PGROUNDUP(pa_start)..(pa_end, PGSIZE-step), each `page_valid` ∗ a DEEP
  `stack_own` slice (≥14 slots below freerange's sp) to LEND kfree (kfree's
  sp0 = freerange's post-frame sp) ∗ the three per-CPU cells.  Post =
  `callee_saved` + cells back + stack back (pages consumed into the lock).
- Cell-threading resolutions (all make side conditions vm_computable):
  require `qnoff = zeros' 32` (noff=0 at boot-time kinit) ⇒ `q_noff_ret(0)=0`
  and `q_int_ret(0)=0` are CONCRETE (vm_compute), so the loop is stable at
  noff=0/intena=0.  `initlock` zeroes `lk->cpu` BEFORE freerange runs, so
  freerange enters with `q_cpu = zero_reg`; every kfree returns `q_cpu =
  zero_reg`, so the loop is stable there too — and kfree's `Hcpune`
  (`qcpuold ≠ mycpu`) reduces to the STANDING hypothesis `eq_vec zero_reg
  (mycpu_ret (m!!!Regidx 4)) = false` (mycpu is a nonzero .bss address;
  `mycpu_ret` is symbolic in tp, so take it as a freerange/kinit hypothesis,
  discharged ultimately from the boot cpus-array address).  Callee-saved pins
  across the kfree call: s0,s1,s2,s3,s4 (the loop registers).

## kinit (TODO)

prologue (ra@8/s0@0, 16-byte frame) → auipc/addi set a1="kmem" a0=&kmem →
`jal initlock` (wp_initlock) → **`newlock` ghost step** building
`is_kmem γ lk (kmem_res fl)` from `lk ↦₄ 0` (initlock's output) + `fl ↦₈ 0`
(kmem.freelist BSS-zero) + empty `freelist_chain nullp []` → li/slli set
a1=PHYSTOP, auipc/addi a0=end → `jal freerange` → epilogue.  Precondition owns
the `kmem` struct bytes (lock 3 fields + freelist word) + ALL physical pages
`[PGROUNDUP(end), PHYSTOP)` + the cells (noff=0) + the `mycpu≠0` hypothesis.

## Robustness rails

axiom check (`Print Assumptions`, baseline + funext + kerneltrap_returns) and
full `make proofs` per stage.  Resync stale `.vo` (`make proofs`) before
diagnosing any "impossible" literal mismatch — a kernel-image regen can change an
instruction immediate and hide behind a stale `.vo`.
