# DECISION MEMO — the M4 racy lock-internal cells

READ-ONLY ANALYSIS (2026-08-27) against the main repo on branch `tso` @ `53124a5c`
for the notes and the SC-degenerate code, and the FLIP WORKSPACE mirror
`/shared/xv6iris-3-fliptree-backup` (the real-Ztso kit) for the machine/kit code.
Nothing in either tree was modified; the two probes (§7) were compiled from a
scratch directory against the main tree's `.vo` set and are archived at the
backup root beside `ZZPinProbe.v` / `ZZAbsorbProbe.v`.

PURPOSE: the owner-decision record for the M4 racy lock-internal cells — the last
unopened design box, and the one gating `WpSconfLock`'s 160-file cone. THE ASK is
§6's four rulings.

Read against `tso-port.md` §0.8′ (ruling 2 + the M4 markers), §0.18′–§0.19′;
`tso-machine-flip.md` A6.50–A6.55 (the canon pin), A6.66/A6.68 (the honest lock
kit and `WpSconfLock`'s refile), A6.71 (the red 12); `tso-pin-memo.md`;
`tso-absorb-memo.md` §12.

---

## THE M4 QUESTION — verdict

**Headline: the four lock leaves split three ways, and only ONE of them needs new
machinery. That one is `wp_cld_lkcpu_lockopen_notheld_s_sconf`, and no kit of the
canon-pin family can pay it — the constraint is a byte-layout fact, computed
below, and it is decisive.**

---

## 1. The site inventory (measured, not estimated)

`WpSconfLock` has 8 lock-invariant leaves. Consumer counts across the whole main
tree (`grep -rl`, all `.v`):

| leaf | cell | access | consumers | receipt in hand? |
|---|---|---|---|---|
| `wp_clw_lockopen_s_sconf` (:155) | word | plain load, any value | `ProofHolding` ×1 | no |
| `wp_clw_lockopen_locked_s_sconf` (:217) | word | plain load, must be ≠0 | `ProofHolding` ×1 | **holder = author of the AMO write** |
| `wp_amoswap_lockopen_s_sconf` (:906) | word | AMO (exclusive, top of log) | `ProofAcquire` | yes, by construction |
| `wp_sw_zero_lockfin_s_sconf` | word | store | `ProofRelease` | holder |
| `wp_cld_lkcpu_lockopen_s_sconf` (:456) | cpu | plain load, `phi = fun _ => True` | **ZERO — `WpSconfLock.v` only** | — |
| `wp_cld_lkcpu_lockopen_notheld_s_sconf` (:509) | cpu | plain load, `phi = fun c => c <> cpuv` | `ProofHolding:281` | **NO** |
| `wp_cld_lkcpu_lockopen_locked_s_sconf` (:579) | cpu | plain load, `phi = fun c => c = cpuv` | `ProofHolding:644` | **holder = author of its own `lk->cpu = mycpu()`** |
| `wp_csd_lkcpu` / `wp_sd_zero_lkcpu` | cpu | stores | `ProofAcquire` / `ProofRelease` | acquirer / holder |

**(a) The "no evidence" cpu read is DEAD CODE — delete it.** Zero consumers in
either tree. That removes one third of the M4 surface for free.

**(b) What the two live consumers need is EXACT, not weakened.** `SpecHolding`'s
two exported bodies conclude
`mh !!! Regidx (mword_of_int 10) = (mword_of_int 0 : mword 64)` and
`... = (mword_of_int 1 : mword 64)` respectively. **This kills design (d) —
"the postcondition weakens to some value in the set, possibly stale" — outright**:
a weakened read makes `a0` nondeterministic and both contracts unstatable. The
blast radius is not local; `SpecAcquire.v`'s header says the panic arm is dead
*because* of the `notheld` leaf:

> "acquire's `if(holding(lk)) panic("acquire")` arm used to be discharged by a
> panic credential — so the spec read "acquire either returns holding the lock, or
> panics". It now reads "acquire returns holding the lock", because the arm is
> DEAD … and `[WpSconfLock.wp_cld_lkcpu_lockopen_notheld_s_sconf]`, which cashes
> it."

Re-instating the credential is a precondition change under **59 files importing
`SpecAcquire` / 83 naming `locked`** — exactly the surface that must not move.

**(c) Design (b) — "∃-context + accessor, sound where every ACCESS is under the
lock" — is REFUTED by measurement.** Two of the four reads happen without
holding: the `notheld` cpu read (acquire's pre-AMO check) and the free-path
lock-word read. So the accessor's ∃-elimination is not rescuable by "it is under
the lock".

---

## 2. Two of the three hard sites are FREE, and the tree already has the lemma

This is the largest single finding and it does not appear anywhere in the notes.

`TsoCtx.ledger_read_vis_ok` (fliptree `TsoCtx.v:3161`) is exactly the racy-read
gate for an **own-write**:

```coq
  Lemma ledger_read_vis_ok `{CID : CpuId} (g : gstate)
      (a : Arch.pa) (dq : dfrac) (v : bv 8) (t B : nat) :
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗
    view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    ledger_vis (hart_agent cpu_id) B t -∗
    phys_ledger_at a dq v t -∗
    ⌜forall tv' : nat, (g.(gtv) cpu_id <= tv')%nat ->
       tso_read g.(gimg) g.(glog) (hart_agent cpu_id) tv' a = Some v⌝.
```

with
`ledger_vis h B t := (⌜(t ≤ B)%nat⌝ ∨ ∃ i m, ⌜t = S i⌝ ∗ ledger_msg_at i m ∗ ⌜pm_tid m = h⌝)%I`
— persistent, and the right arm is **pure store forwarding, which needs `B = 0`
and therefore `view_lb_0`, which is free** (`TsoGhost.v:188`).

The two leaves whose reader *is* the author of the cell's last write —
`wp_cld_lkcpu_lockopen_locked_s_sconf` (the holder reads its own
`lk->cpu = mycpu()`) and `wp_clw_lockopen_locked_s_sconf` (the holder reads the
word its own `amoswap` set) — are therefore **honest with no new kit, no receipt
and no pin**: the invariant's held arm carries the `ledger_msg_at` fragment the
store gate already hands back (`ledger_store_ok` returns
`ledger_msg_at (length g.(glog)) (PWMsg Pnew auth)`, `TsoCtx.v:2558/2672`), and
the reader cashes it with `ledger_vis_own` + `view_lb_0`. `phys_ledger_word`
(`TsoCtx.v:2265`) is the context-free 8-byte carrier; at `KT0` `ktier_pin` *is*
`pa_of ppn va = va`, so the persistent `mem_claim` from `lock_claims` supplies
everything the ctx window supplied.

The four **store** leaves and the AMO are the parked-record idiom (option (c)),
and it works there: the acquirer's AMO receipt dominates the record's stamp by
§0.18′'s own recorded tie (`T' ≤ t_release`, and the AMO drains past
`t_release`). `TsoCtx.ctx_absorb` (interp form, A6.66) pays the AMO leaf;
`ctx_absorb_lb` (receipt form) pays the later stores.

**So options (b) and (c) are not competitors — (c) pays the writes,
`ledger_vis_own` pays the holder's reads, and the residue is ONE site.**

---

## 3. The residue: `notheld`, and why the pin (option (a)) cannot pay it

What the site must conclude: `∀ tv' ≥ my view, the 64-bit word read ≠ cpus_ptr cpu_id`.

**The pin gives value-in-set, and value-in-set is not it.**
`ledger_read_pin_ok`'s conclusion is
`∀ (h : agent) (tv' : nat), gtv cpu_id ≤ tv' → ∃ b, tso_read … = Some b ∧ b ∈ Sv`,
agent-generic *by design* ("Agent-generic on purpose — the confinement holds of
every agent, which is what makes it usable inside `fobl_ram`'s ∀-quantified
view"). `Sv` for this cell is `{0} ∪ {cpus_ptr j}` — nine values, and
`cpus_ptr cpu_id` is one of them.

**And no per-agent generalisation of `pin_ok` can fix that.** Maintenance under
an append by author `A` writing `b`: a reader at the *top* view sees the new
message regardless of who it is, so the obligation is `∀ h, P h b` — every
store's value must be allowed for every reader. The exclusion we want is
precisely `¬ P cpu_id (cpus_ptr cpu_id)`. Contradiction. **The exclusion is not a
property of the value; it is a property of the reader's own write history**, and
it is true only because `read_down` scans *down from the top* and `visibleb_own`
makes a hart's own message visible at every view (`TsoMemPa.v:104`) — so a read
can only return `cpus_ptr h` if the message is `h`'s own **latest** write to that
address.

### The two facts that do pay it — probed green

`ZZRacyProbe.v` (§7), 164 lines, six lemmas, `Closed under the global context`,
no `Admitted`/`Axiom`:

```coq
  Definition own_last (log : list pwmsg) (h : agent) (a : Arch.pa) (t : nat) : Prop :=
    forall i m, log !! i = Some m -> pm_tid m = h ->
      is_Some (msg_byte m a) -> (S i <= t)%nat.

  Definition writer_pin (log : list pwmsg) (a : Arch.pa)
      (Sf : agent -> bv 8 -> Prop) : Prop :=
    forall i m c, log !! i = Some m -> msg_byte m a = Some c ->
      Sf (pm_tid m) c.

  Lemma racy_read_split img log h a tv t v b Sf :
    (t <= length log)%nat -> visibleb h tv log t = true ->
    log_byte img log t a = Some v -> own_last log h a t -> writer_pin log a Sf ->
    tso_read img log h tv a = Some b ->
    b = v \/ exists h', h' <> h /\ Sf h' b.
```

plus `racy_read_not_mine` (the consumer shape), `racy_read_own` (the free half,
re-deriving §2 from `visibleb_own`), and the three maintenance lemmas —
`own_last_app_frame` (any append that is not h's own write to `a`: free),
`own_last_app_self` (h's own store: free, the top), `writer_pin_app` (side
condition `Sf (pm_tid m) c` — *the author is already a parameter of every store
gate*).

Both facts are **coverage claims over the log**, so `tso-pin-memo.md` §3's
refutation applies verbatim — they must live in the interp, i.e. in the
`ts_elem` option payload beside the pin, not in an invariant.

### THE MEASUREMENT THAT DECIDES THE SHAPE

`tso-pin-memo.md` §2 ruled that "a BYTE-KEYED confinement fact is exactly as
strong as a window-keyed one … so the fix can stay byte-keyed and needs no
window-shaped ghost." **That is true for the PTE and FALSE here.** Computed from
`KernelSyms.mycpu = 0x800018ba`, `KernelConsts.mycpu_cpus_auipc = 0x11`,
`KernelConsts.mycpu_cpus_addi = 0xb20` and `ProcGeom.mycpu_a5`'s shift of 7
(`sizeof(struct cpu) = 128`):

```
base = 0x800123e8, stride 128
i=0 0x800123e8   i=1 0x80012468   i=2 0x800124e8   i=3 0x80012568
i=4 0x800125e8   i=5 0x80012668   i=6 0x800126e8   i=7 0x80012768
byte 0 ∈ {0xe8, 0x68}   byte 1 ∈ {0x23,0x24,0x25,0x26,0x27}   bytes 2..7 identical
distinguishing single byte offset, per hart:  hart 0 → [1];  harts 1..6 → [];  hart 7 → [1]
```

For harts 1..6 there is **no byte offset at which `cpus_ptr h` differs from every
other hart's byte and from 0**. A byte-keyed writer-pin therefore permits a
*forged* word assembled from two different messages' bytes, and the exclusion
fails. **The kit must be window-shaped**: the reader needs "all 8 bytes came from
one message". Cheapest honest encoding: hang the window payload on byte 0's
element — `(n, W : agent → gset (bv (8*n)), B, L : gmap agent nat)`, with the
interp conjunct "every message writing byte `a` writes the whole n-byte window,
and the assembled word is in `W (pm_tid m)`". One element, no second ghost map;
the pin's existing PT customer instantiates it at `n = 1` with `W` constant.

---

## 4. Two corrections to the standing record

**(i) `tso-pin-memo.md` §4 is refuted in its own terms.** It rejected candidate
(iii) (write-history) partly because "The M4 dual-use claim does not hold up. I
checked `WpLock.v:271–327` and the flip note's M4 entry …: the marker is the
**parked-context** idiom … not a racy-history fact. The lock word is taken by AMO
… and `lk_cpu_res` is transferred exclusively, not read racily." A6.68
re-diagnosed this correctly and the measurement above confirms it: `lk->cpu`
**is** read racily, by a non-holder, at `holding+0x12`, and that read is the whole
content of `SpecAcquire`'s dead-panic-arm story. **The second customer exists.**
(§4's *verdict on the shape* still stands — a `list nat` history is dominated;
what is wanted is `own_last` + a writer-pin, both O(1) per address.)

**(ii) THE FLIPTREE AND MAIN HAVE DIVERGED ON `lock_word`, AND THE FLIPTREE'S
VERSION IS UNSOUND AT MULTI-HART.** Main (§0.19′) has:

```coq
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    (∃ ξ : CtxId, ctx_word4_pointsto ξ lk (DfracOwn 1) v)%I.
```

The fliptree (`WpLock.v:228`) still has `lock_word lk v := (lk ↦₄ v)%I` — i.e.
`ctx_word4_pointsto cur_ctx`, under `Context {XI : CurCtx}` at `WpLock.v:67`. So
in the fliptree `lock_inv` — and therefore `is_lock`, the *persistent handle* —
is ξ-indexed. That is exactly the falsity §0.19′ names ("would have become
AMBIENT-indexed, which drags a context into the persistent `is_lock` handle and
would have falsified the park rows outright, with no payload conversion able to
repair it"), and it has not fired only because the fliptree's `WpSconfLock` cone
(160 files, including every `is_lock` client and `UsertrapRes`'s park rows) is
unreached. **§0.19′'s ruling must be replayed into the fliptree as part of this
tranche**, and doing so turns the two `wp_clw_lockopen_*` leaves red as well — so
the honest M4 site count in `WpSconfLock` is 3 red sites, not 1.

---

## 5. Scoping: does one kit serve all the racy cells?

The `_acc` / `SC-only` markers split into two classes, and they want **different**
kits:

- **Class A — ∃-context only because an `inv`/`cinv` body must be a closed term;
  every access is under a lock.** `IcacheInv.iref_cell_acc` (:1405),
  `FileInvDefs.off_cell_acc` (:1044) + `off_resident`/`off_raw`/`off_mark`,
  `IcacheEscrow.ic_escrow_body_reindex`, and the ~20
  `TsoCtxShim.ctx_word{2,4}_reindex` uses. These are **not racy** — the opener
  holds the lock and therefore an acquire receipt. Their fix is the parked-record
  + `ctx_absorb_lb`, exactly as `IcacheEscrow.v:3526` and `FileInvDefs.v:1030`
  already predict. **No racy kit needed.**
- **Class B — genuinely racy plain reads.** The lock owner cell, the lock word,
  and `StartedInv.started_cell_acc` (:105). `started` is the boot message-passing
  flag; its consumers (`ProofMain:2004`, `ProofMainSecondary:362`) need
  "started ≠ 0 ⟹ the publication is visible", which is the *publication/drain*
  shape (`tso-pin-memo.md` §5.6(b), the `__sync_synchronize` drain — already
  A6.71's queue item 3), **not** the exclusion shape. So Class B is itself split,
  and the `own_last` / writer-pin kit has exactly one customer: `lk->cpu`.
- **Out of scope:** `SpecProcdump` is a deliberately unlinkable contract ("its
  being unsatisfiable from anything currently in the tree is not a gap in the
  spec — it IS the statement that procdump is racy"); it asks for read-shares,
  not a racy-read law.

---

## 6. Ranked recommendation

### Owner rulings (four, in this order)

1. **Delete `wp_cld_lkcpu_lockopen_s_sconf`.** Zero consumers, both trees. Free.
2. **Ratify the split**: the four stores + the AMO take the
   parked-record/`ctx_absorb` idiom (option (c), already ratified for the payload
   at §0.18′); the two *holder* reads take `ledger_vis_own` + `view_lb_0` at
   `phys_ledger_word` (context-free, no new law); only `notheld` gets new
   machinery. This is the ruling that shrinks M4 from "a racy kit" to "one
   lemma".
3. **Ratify that the racy kit is `own_last` + a WINDOW-shaped writer-pin in the
   `ts_elem` option payload, and record the byte-layout measurement as the
   reason** — so nobody re-proposes the byte-keyed form on the strength of
   `tso-pin-memo.md` §2. Reject the per-agent `pin_ok` generalisation explicitly
   (the top-view maintenance obligation forces `∀ h, P h b`).
4. **Replay §0.19′'s `lock_word` ∃-ruling into the fliptree** before anything else
   in `WpLock` moves. This is a correctness fix, not a chore.

### Mechanical work, once ruled (≈10 files, no client files)

`TsoMemPa` (the probed lemmas, verbatim) → `TsoGhost` (1 class field) →
`RiscvPtsto`/`RiscvExec` (`ts_ok` grows; the pin's precedent says positional
destructurings stay put because `ts_ok` bundles) → `TsoCtx`
(`ledger_store_pin_ok` gains the author premise + the `own_last` update; new
`ledger_read_racy_ok`; `ledger_pin_mint` seeds the map) → **`HartSMem` +
`WpSconfMem`: the S-mode value-after-view load.** This is the one genuinely new
lane and it is smaller than it looks: `HartEvents.wp/swp_hart_ram_read_plain_ex`
already exists (A6.51) and `swp_execute_LOAD_S_gen_ex` takes its node *and* its
obligation as arguments (measured at the `WpSconfMem.v:596–650` call site), so
what is needed is `Mobl_ram_exv` beside `Mobl_ram_ex`,
`swp_read_ram_node{1,2,4,8}_exv`, and `wp_load_s_sconf_au_exv`. Note
`HartSMem.Mobl_ram_ex` (`:3699`) is **not** it — its `∃ bytes` sits *outside* the
`∀ tv'`, i.e. it is `tso-pin-memo.md` §0's refuted shape. → `WpLock` (`lock_word`
∃; `lk_cpu_res` re-shaped to `phys_ledger_word` + the residue) → `WpSconfLock`
(3 leaves re-proved, 1 deleted) → `ProofHolding` (2 call sites, statements
unchanged).

**`SpecAcquire`, `SpecRelease`, `SpecHolding`, `is_lock`, `locked`,
`lock_openable` do not move.** `lock_openable` hands out `▷ lock_inv γ lk s R`, so
16 files *see* the body — but only `WpSconfLock` and `ProofAcquire`/`ProofRelease`
destructure it.

### Risks

- The window-shaped payload is a bigger `ts_elem` than the pin's, and
  `ledger_store_ok`'s frame arm has to stay definitional for unpinned payers (the
  pin's central claim — it held there, and the `None` default preserves it, but it
  is the thing to check first). `ts_name` occurs 25 times across 6 files in the
  fliptree (`DiskInv`, `RiscvAdequacy`, `CtxPinMint`, `TsoCtx`, `RiscvExec`,
  `RiscvPtsto`) — still the contained change the pin memo measured.
- The S-mode `_exv` lane is where A6.64's forty-argument elaboration hazard lives;
  the rule ("when threading the token into a leaf, move the NODE argument too")
  applies to the new node argument.
- `own_last` must be maintained for **all eight harts** at every store to the
  cell; the frame lemma is `own_last_app_frame` and its side condition is
  `pm_tid m = h → msg_byte m a = None`, which the store gate discharges from its
  own `auth`.

---

## 7. THE PROBES — BOTH RUN, BOTH GREEN, BOTH AXIOM-FREE

Archived at the backup root beside `ZZPinProbe.v` / `ZZAbsorbProbe.v`:

- `/shared/xv6iris-3-fliptree-backup/ZZRacyProbe.v` — 164 lines, the per-BYTE
  read theorem and its maintenance.
- `/shared/xv6iris-3-fliptree-backup/ZZWinProbe.v` — 252 lines, the WINDOW
  reassembly (§8).

Both compile against the MAIN tree's `TsoMemPa.vo` — the read semantics
(`msg_byte` / `log_byte` / `visibleb` / `read_down` / `tso_read` and the
`read_down_le` / `read_down_latest` pair) are character-identical in the two
trees, and the fliptree carries no `.vo` set. THE COMPILE LINE actually run
(from any scratch directory holding the two files):

```sh
eval $(opam env --switch=/shared/xv6rocq) && \
coqc -w -notation-overridden \
     -R /shared/xv6iris-3/iris xv6iris \
     -R /shared/xv6iris-3/model-xv6iris Riscv \
     -R /shared/xv6iris-3/kernel-rocq Kernel \
     -R /shared/xv6iris-3/user-rocq User -I . \
     ZZRacyProbe.v && \
coqc -w -notation-overridden \
     -R /shared/xv6iris-3/iris xv6iris \
     -R /shared/xv6iris-3/model-xv6iris Riscv \
     -R /shared/xv6iris-3/kernel-rocq Kernel \
     -R /shared/xv6iris-3/user-rocq User -I . \
     ZZWinProbe.v
# ~1 s each, no output = green.  ZZWinProbe requires ZZRacyProbe (own_last).
```

`Print Assumptions` on `racy_read_split`, `racy_read_not_mine`, `racy_read_own`,
`own_last_app_frame`, `own_last_app_self`, `writer_pin_app`, `read_down_win`,
`racy_read_window`, `racy_read_window_pin` and `lkcpu_not_mine`: **`Closed under
the global context`**, all ten. No `Admitted`, no `admit`, no `Axiom`.

The fliptree variant (the `ZZPinProbe.v` recipe) once that tree has a `.vo` set:

```sh
cp /shared/xv6iris-3-fliptree-backup/ZZRacyProbe.v FLIPTREE/iris/ && \
cp /shared/xv6iris-3-fliptree-backup/ZZWinProbe.v  FLIPTREE/iris/ && \
cd FLIPTREE/iris && eval $(opam env --switch=/shared/xv6rocq) && \
coqc -w -notation-overridden -R . xv6iris -R ../model-xv6iris Riscv \
     -R ../kernel-rocq Kernel -R ../user-rocq User ZZRacyProbe.v ZZWinProbe.v
# then remove the .v/.vo/.vos/.vok/.glob/.aux
```

---

## 8. MEASURED — THE WINDOW-REASSEMBLY PROBE GOES THROUGH

The one step §6's ruling 3 was waiting on. **VERDICT: GREEN, first design, no
fallback needed. `ts_elem` does NOT need a second ghost map.**

`ZZWinProbe.v` proves, over the real machine, that a single timestamp resolves
every byte of the window — which is exactly what makes the forgery the byte-layout
measurement exposed impossible.

The two premises, both per-address and both interp-maintainable:

```coq
  (* (W1) every timestamp writes the WHOLE window or none of it *)
  Definition win_ok : Prop :=
    forall t : nat,
      (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j)))
      \/ (forall j, (j < n)%nat -> log_byte img log t (pa_add a j) = None).

  (* (W2) every message touching the window writes a word allowed for ITS AUTHOR,
     stated on the message's byte FUNCTION so no [bv] width arithmetic is needed *)
  Definition wpin (Wf : agent -> (nat -> option (bv 8)) -> Prop) : Prop :=
    forall i m, log !! i = Some m ->
      is_Some (msg_byte m (pa_add a 0)) ->
      Wf (pm_tid m) (fun j => msg_byte m (pa_add a j)).
```

and the theorem:

```coq
  Lemma racy_read_window (h : agent) (tv t : nat) :
    win_ok ->
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    (forall j, (j < n)%nat -> is_Some (log_byte img log t (pa_add a j))) ->
    (forall j, (j < n)%nat -> own_last log h (pa_add a j) t) ->
    exists T : nat,
      (t <= T)%nat
      /\ (forall j, (j < n)%nat ->
            tso_read img log h tv (pa_add a j) = log_byte img log T (pa_add a j))
      /\ (T = t \/ exists i m, T = S i /\ log !! i = Some m /\ pm_tid m <> h
                            /\ is_Some (msg_byte m (pa_add a 0))).
```

The proof machinery is three small lemmas over `read_down`: a `find_top` function
computing the timestamp `read_down` settles on **at byte 0**, `read_down_win`
(`win_ok` transports that timestamp to every byte of the window — this is the
reassembly), and `find_top_spec` / `find_top_max` (it is visible, it writes, and
it is maximal). `own_last` at a COMMON index across the window is what forces the
`T > t` arm to name a message by someone else.

**And the consumer instance is the sharp statement of the byte-vs-window ruling:**

```coq
  Lemma lkcpu_not_mine (h : agent) (tv t : nat)
      (z : nat -> bv 8) (cp : agent -> nat -> bv 8) :
    win_ok ->
    wpin (fun j f => (forall k, (k < n)%nat -> f k = Some (z k))
                  \/ (forall k, (k < n)%nat -> f k = Some (cp j k))) ->
    (t <= length log)%nat ->
    visibleb h tv log t = true ->
    (forall j, (j < n)%nat -> log_byte img log t (pa_add a j) = Some (z j)) ->
    (forall j, (j < n)%nat -> own_last log h (pa_add a j) t) ->
    (exists k, (k < n)%nat /\ z k <> cp h k) ->
    (forall h', h' <> h -> exists k, (k < n)%nat /\ cp h' k <> cp h k) ->
    exists k, (k < n)%nat /\ tso_read img log h tv (pa_add a k) <> Some (cp h k).
```

Read the two final premises: each asks only for a distinguishing offset **per
other hart** — i.e. `cpus_ptr` injective and `cpus_ptr h ≠ 0`, both WORD-level and
both true. The byte-keyed kit would have needed ONE offset separating `h` from all
harts at once, which §3's layout computation says does not exist for harts 1..6.
That gap is precisely what `win_ok` closes.

**THREE CONSEQUENCES FOR THE COST ESTIMATE, and one of them raises it:**

1. The interp conjunct has **three** parts, not two: `win_ok`, the writer-pin, and
   `own_last`. `win_ok` is itself a coverage claim over the log (`∀ t`), so it
   cannot be carried by the invariant either — `tso-pin-memo.md` §3 again. All
   three ride in the one `ts_elem` option payload at byte 0.
2. `win_ok`'s maintenance is trivial at the lock: every write to `lk->cpu` is one
   8-byte `sd`, so the appended message writes all eight bytes, and the era image
   covers RAM (the `t = 0` arm). It is a per-store side condition of the same
   shape as the pin's `vnew ∈ Sv`.
3. **No second ghost map, and no `bv`-width dependent-type work.** Stating `wpin`
   on the message's byte function `nat -> option (bv 8)` keeps the whole window
   layer free of `bv (8*n)` arithmetic; `bv_eq_of_bytes` is needed only where the
   leaf already assembles the word.

**What is now unprobed: nothing in the pure layer.** The remaining risk is
entirely Iris-side — the `ts_ok` growth and the `Mobl_ram_exv` lane of §6 — and
neither is a design question.
