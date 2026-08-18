# PARM certification: what `interference_certify` really is, and what D8 must port

Sources: shallow clone at
`/tmp/claude-0/-shared-xv6iris-2/36d033b8-a541-4970-8c24-4e924a5dca1a/scratchpad/parm/src`
(commit = tip of `snu-sf/promising-arm`). All line numbers are from that tree.

## HEADLINE FINDING (correcting `weak-memory-layer2.md` §8 / §10.1)

**There are TWO different `interference_certify` lemmas, in opposite directions,
and `certified_exec_complete` does NOT use the RISC-V one.**

| | `lcertify/CertifyComplete.v:101` | `lcertify/CertifyProgressRiscV.v:1233` |
|---|---|---|
| direction | `certify (mem ++ mem_interference)` ⟹ `certify mem` (memory **restriction**) | `certify mem` ⟹ `certify (mem ++ mem_interference)` (memory **extension**) |
| simulation | `CertifySim.v` `sim_eu tid ts ts_private src_promises eu1 eu2` (6 args), `sim_view` is **equality** below `ts` | `CertifyProgressRiscV.v` `sim_eu tid ts eu1 eu2` (4 args), `sim_view` is **one-sided `le`** below `ts` |
| `arch == riscv` hypothesis | **NONE** — `grep -c RISCV lcertify/CertifySim.v` = 0; the lemma is arch-generic | `(RISCV: arch == riscv)` at `:1238`, propagated from `sim_eu_step:526` / `sim_eu_rtc_step:1182` |
| consumer | `certified_exec_complete` (`CertifyComplete.v:179`) — i.e. `Machine.exec → certified_exec` | `certified_deadlock_free` (`CertifyProgressRiscV.v:1357`, used at `:1417`) |
| files | `CertifyComplete.v` imports `Certify.v` + `CertifySim.v` only | `CertifyProgressRiscV.v` imports `Certify.v` only — it is a **self-contained duplicate**, not a refinement |

The direction xv6iris needs for D8 ("every full-machine behavior is a certified
behavior") is `certified_exec_complete`, hence the **arch-generic** lemma.
The RISC-V arithmetic (`RES = ts`, no-forwarding-from-exclusive) is used only by
the *progress/deadlock-freedom* theorem, which D8 does not need.
So §10.1's premise ("PARM proves `interference_certify` for RISC-V ... probably
through the RISC-V-specific view arithmetic (`RES = ts` ...)") is mis-targeted:
the completeness direction needs neither.

---

## 1. `lcertify/Certify.v` — the definitions

```coq
(* Certify.v:25 *)
Inductive write_step (tid) (loc) (val) (view_pre) (eu1 eu2) : Prop :=
| write_step_intro
    ex ord vloc vval res ts e lc
    (EVENT:   e = Event.write ex ord vloc vval res)
    (STATE:   State.step e eu1.(state) eu2.(state))
    (PROMISE: Local.promise vloc.(val) vval.(val) ts tid eu1.(local) eu1.(mem) lc eu2.(mem))
    (FULFILL: Local.fulfill ex ord vloc vval res ts tid view_pre lc eu2.(mem) eu2.(local)).

(* Certify.v:38 *)
Inductive certify_step (tid) (eu1 eu2) : Prop :=
| certify_step_state (STEP: ExecUnit.state_step tid eu1 eu2)
| certify_step_write loc val view_pre (STEP: write_step tid loc val view_pre eu1 eu2).

(* Certify.v:48 *)
Inductive certify (tid) (eu1) : Prop :=
| certify_intro eu2 (STEPS: rtc (certify_step tid) eu1 eu2)
                    (NOPROMISE: eu2.(local).(Local.promises) = bot).

(* Certify.v:192 *)
Inductive certified_eu_step (tid) (eu1 eu2) : Prop :=
| certified_eu_step_intro (STEP: ExecUnit.step tid eu1 eu2) (CERTIFY: certify tid eu2).

(* Certify.v:198 *)
Inductive certified_exec (p) (m) : Prop :=
| exec_intro (STEP: rtc (Machine.step certified_eu_step) (Machine.init p) m)
             (NOPROMISE: Machine.no_promise m).
```

Answers to the three sub-questions:

* **Does `write_step` append at the top of memory?** **Yes.** `Local.promise`
  (`promising/Promising.v:798`) requires `MEM2: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2)`,
  and `Memory.append msg mem := (S (length mem), mem ++ [msg])`
  (`Promising.v:73`). So a certifying run's own stores land at `S (length mem)`
  and are fulfilled in the *same* step. **A certifying run is therefore exactly
  a `wp_pf`-style solo run** for its own new stores — this part of §8 is right.
* **Are the promised fulfils at fixed timestamps?** **Yes.** The other arm,
  `ExecUnit.state_step`, reaches `Local.fulfill` (`Promising.v:891`), which
  requires `PROMISE: Promises.lookup ts lc1.(promises)` (`:901`) and
  `MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc val tid)` (`:900`).
  Timestamp, location and *value* were all frozen at promise time.
* **May the certifying run make NEW promises?** **No.** `certify_step` has
  exactly two arms and neither is `ExecUnit.promise_step`
  (`ExecUnit.step = state_step ∪ promise_step`, `Promising.v:1300`;
  `certify_step` uses `state_step`, `Certify.v:40`). The only appends are
  `write_step`'s promise-and-immediately-fulfil.

Supporting lemmas in the same file that the argument leans on:
`certify_step_wf:75`, `rtc_certify_step_wf:86`, `certify_step_incr:108`
(`ExecUnit.le` — all views monotone), `certify_step_vcap:128`
(`le lc.(vcap) lc'.(vcap)`), and the load-bearing

```coq
(* Certify.v:144 *)
Lemma certify_step_vcap_promise tid ts eu eu'
      (STEP: certify_step tid eu eu') (WF1: ExecUnit.wf tid eu)
      (VCAP: ts <= eu.(local).(Local.vcap).(View.ts))
      (PROMISES: Promises.lookup ts eu.(local).(Local.promises)):
  Promises.lookup ts eu'.(local).(Local.promises).
```
i.e. **once `vcap` has reached a promise's timestamp, that promise can never be
fulfilled again** — proved from `writable`'s `EXT: view_pre.ts < ts` with
`view_pre ⊒ vcap` (`Promising.v:873, 883`); the `lia` at `Certify.v:157` is the
whole content. `rtc_certify_step_vcap_promise:166` iterates it.

## 2. `interference_certify` — statement and proof structure

### 2a. The one that matters (arch-generic, `CertifyComplete.v:101`)

```coq
Lemma interference_certify tid st lc mem mem_interference
      (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem_interference)
      (CERTIFY: certify tid (ExecUnit.mk st lc (mem ++ mem_interference)))
      (WF: ExecUnit.wf tid (ExecUnit.mk st lc mem)):
  certify tid (ExecUnit.mk st lc mem).
```
Proof: three lines of real content — build
`sim_eu tid (length mem) (length mem) bot (mk st lc mem) (mk st lc (mem++mem_interference))`
(`:112`–`:140`) and apply `sim_eu_rtc_step_bot` (`CertifySim.v:1231`) with
`src_promises = bot`.

### 2b. `sim_eu` (`CertifySim.v:141`)

`sim_eu tid ts ts_private src_promises eu1 eu2` = `sim_state ∧ sim_lc ∧ sim_mem`,
where **`eu1` is the SOURCE (small memory, the run being constructed) and `eu2`
the TARGET (big memory, the run we are given)**. The parameter `ts` is the
length of the *common prefix*:

```coq
(* CertifySim.v:62 *)  sim_mem ... mem1 mem2 :=
   ∃ mem mem1' mem2', ts = length mem ∧ mem1 = mem ++ mem1' ∧ mem2 = mem ++ mem2'
   ∧ (TS_PRIVATE: ∀ tsp msg, ts_private < tsp → get_msg tsp mem1 = Some msg → msg.(tid) = tid)
   ∧ (MEM1': ∀ n1 msg1, nth_error mem1' n1 = Some msg1 → ¬ promised →
        msg1.(tid) = tid ∧ S (length mem)+n1 ≤ (coh1 msg1.(loc)).ts ∧ ∃ matching msg2 in mem2') ...

(* CertifySim.v:26/33 *)  sim_time ts v1 v2 := v2 ≤ ts → v1 = v2
                          sim_view ts v1 v2 := v2.(View.ts) ≤ ts → v1 = v2
```
So the relation says: **everything the target can *see* at or below `ts` is
identical in the source; everything above `ts` is unconstrained.** The two
memories agree on `mem` and diverge freely above it, and — crucially — **every
source message above the boundary belongs to `tid` itself** (`MEM1'`/`TS_PRIVATE`).

`sim_lc` (`:124`) relates `coh, vrn, vwn, vro, vwo, vcap, vrel` pointwise by
`sim_view`, `fwdbank` by `sim_fwdbank` (`:95`, two arms: *below* — same value,
equal view, `sim_time` on `ts`; *above* — target's fwd view `> ts`, source's fwd
entry merely `Memory.latest`), `exbank` by `sim_exbank` (`:110`, same two arms,
each carrying `Memory.exclusive tid eb1.loc eb1.ts ts mem1`), and promises by
`PROMISES1: tsp ≤ ts → lookup tsp p1 = lookup tsp p2` /
`PROMISES2: tsp > ts → lookup tsp p1 = lookup tsp src_promises`.

### 2c. How the "new store above the promised fulfil" case is handled

**Answer: (b) — such a configuration is not certifiable in the first place —
plus (a) for the new stores, and (d) for the escape hatch. Not (c).**
In detail, three mechanisms, none RISC-V-specific:

1. **New stores ARE re-timed (a).** The target's `write_step` is mimicked by a
   source `write_step` at `S (length mem1)` (`CertifySim.v:539`–`:668`; the
   append is visible at `:578` `rewrite nth_error_app2, Nat.sub_diag`). More
   striking: a *target fulfil of a promise above `ts`* is mimicked by a source
   **`write_step`** — `econs 2` at `:1022`, case `(* fulfilling a new promise > ts
   (only in tgt) *)` `:1019`. Everything above the boundary is re-timed.
2. **The promised fulfils below `ts` keep their exact timestamp, and EXT is
   *transferred*, not re-proved (b).** Case `(* fulfilling a promise <= ts *)`
   `:947`. The target's `WRITABLE` gives `EXT: view_pre₂.ts < ts₀ ≤ ts`, hence
   `view_pre₂.ts ≤ ts`, hence by `sim_view` **`view_pre₁ = view_pre₂`**:
   ```coq
   (* CertifySim.v:963 *) inv WRITABLE. econs; eauto.
   - symmetry. eapply sim_view_eq; cycle 1.
     { etrans; [by apply Time.lt_le_incl; eauto|]. eauto. }
     s. repeat apply sim_view_join; ss. ...
   ```
   So the shape §10.1 worries about — new store `s` at the top, `dmb pw∧sw`,
   then the promised fulfil `m` at `ts_m` — **is refuted in the given run
   itself**: `s` lands above the boundary in *both* memories (`S (length mem_i) > ts ≥ ts_m`),
   the fence raises `vwn ⊒ ts_s`, and `view_pre ⊒ vwn` makes
   `EXT: view_pre < ts_m` false in the run we were handed. Nothing has to be
   repaired, because nothing certifiable has that shape. **This argument is
   symmetric in the two directions** (in the progress direction the given run's
   store is also above `ts` — `mem2 = mem`, `mem2' = []`), which is why
   `RES`/`vcap` arithmetic is not what saves it.
3. **The escape hatch when `vcap` leaves the prefix (d).** `sim_eu_step`
   (`CertifySim.v:517`) carries the hypothesis `VCAP: eu2'.(local).(vcap).(View.ts) <= ts`.
   The driver `sim_eu_rtc_step_bot` (`:1231`) does
   `destruct (le_lt_dec (View.ts (Local.vcap (ExecUnit.local y))) ts)` (`:1251`)
   and, in the `>` branch, **stops the source run** and closes the goal with
   `sim_eu_promises` (`:1218`) + `rtc_certify_step_vcap_promise`: once the
   target's `vcap` exceeds `ts`, every promise `≤ ts` must *already* be
   fulfilled (`:1271`–`:1277`), so the source is done. This is what lets the
   source read a *different value* when the target read a fresh message — case
   `(* Case 1: Tgt's post-view > ts. Src reads the latest msg. *)` (`:698`) — the
   register then has target view `> ts` and `sim_val` is vacuous
   (`apply sim_val_above`, `:719`); `vcap` is the guarantee that no such value
   ever reaches an address or a branch condition below the boundary
   (`sem_expr` views enter `vcap` at `Local.read`'s `vcap ⊔= view(addr)`,
   `Promising.v:855`, and at `Local.control`, `:826`; used at `:693`, `:944`, `:1165`).

Lemmas that carry the argument, by name: `sim_eu_step` (`CertifySim.v:517`),
`sim_eu_rtc_step` (`:1180`), `sim_eu_rtc_step_bot` (`:1231`),
`sim_eu_promises` (`:1218`), `certify_step_vcap` / `certify_step_vcap_promise` /
`rtc_certify_step_vcap_promise` (`Certify.v:128/144/166`),
`sim_view_eq/sim_view_above/sim_view_join/sim_val_above` (`CertifySim.v:225/234/201/257`),
`sim_mem_no_msgs` (`:405`), `sim_mem1_exclusive` (`:388`),
`sim_fwd_view1/2` (`:430/:452`), `sim_fwdbank_mon` (`:476`), `sim_exbank_mon` (`:503`).
There is **no** `*_dmb*` lemma and no `*_view_pre*` lemma: `dmb` is one line
(`:1153`–`:1158`, `eauto 10 using sim_view_join, sim_view_ifc, sim_view_bot`),
because the fence only joins views that are already related.

### 2d. Where `arch == riscv` is genuinely used (progress direction only)

`grep -n RISCV lcertify/CertifyProgressRiscV.v` → hypothesis sites
`:383, :526, :1182, :1238, :1362` and **four** real uses:
* `:552`, `:1033` — `apply sim_rmap_add; ss. rewrite RISCV. s. apply sim_val_above.`
  This is the **`RES = ts`** view (`Promising.v:902`,
  `RES: res = ValA.mk _ 0 (View.mk (ifc (ex && (arch == riscv)) ts) ...)`):
  with `riscv`, the SC-result register's view is the *new* write's timestamp,
  which is above the boundary, so `sim_val` is vacuous. **This is a convenience,
  not a necessity**: with `ifc false` the two `res` values are literally equal
  (`ValA.mk 0 (View.mk 0 tt)`, `A = unit`), which `sim_val_const`/`ss` closes —
  and indeed the arch-generic file closes exactly that goal with
  `unfold ifc. condtac; ss. intro Y. ... lia.` (`CertifySim.v:583`, `:1059`).
* `:761, :853, :863, :870` — `rewrite EX, RISCV in E0. ss.` These kill the third
  arm of the RISC-V `sim_fwdbank`, `sim_fwdbank_above'` (`:87`,
  `ABOVE: ts < fwd2.ts`, `EX: fwd2.ex`), using RISC-V's **unconditional
  no-forwarding-from-an-exclusive-store**: `FwdItem.read_view`
  (`Promising.v:528`) returns `View.mk tsx bot` whenever
  `fwd.ex && (arch == riscv || ord ≥ acquire_pc)`, and at `riscv` that is
  `fwd.ex` alone. **This is the only load-bearing RISC-V fact in PARM's
  certification development, and it is needed only for progress.**

## 3. Which components of `Local.t` the (generic) proof depends on

`Local.t = mk coh vrn vwn vro vwo vcap vrel fwdbank exbank promises`
(`Promising.v:778`).

| component | verdict for `CertifyComplete.interference_certify` |
|---|---|
| **register views (`rmap` annotations)** | **USED, essential.** `sim_rmap`/`sim_val` (`CertifySim.v:47/40`) is *the* mechanism by which "values with view ≤ ts agree"; `sim_rmap_expr` (`:336`) is invoked at every address (`:541, :691, :942`), value (`:949`) and branch condition (`:1164`). |
| **`vcap`** | **USED, essential and irreplaceable.** It is the simulation's termination guard (`sim_eu_step`'s `VCAP`, `:527`), and `certify_step_vcap_promise` (`Certify.v:144`) is what makes stopping sound. Remove `vcap` and the "source reads a different message" case (`:698`) becomes unsound. |
| **`vrn`, `vwn`, `vro`, `vwo`** | USED, but **only through `sim_view_join` monotonicity** — they would hold for any collection of monotone views. `vrn` appears specially at `VRNEQ` (`:746`), still just `sim_view_below`. |
| **`vrel`** | **Used only through a lemma that would hold without it** — `VREL` field of `sim_lc` (`:132`), `VRELEQ` (`:750`), and `sim_view_ifc`. Nothing in the proof depends on release semantics. |
| **`fwdbank`** | **USED, essential** — it needs its own two-armed relation `sim_fwdbank` (`:95`), because the source's forwarded store has a *different* timestamp. Consumers: `sim_fwd_view1/2` (`:430/:452`) and read Cases 2/3 (`:761/:860`). Not removable if the machine has forwarding. |
| **`exbank`** | **USED, essential for the RMW arm.** `sim_exbank` (`:110`) carries `Memory.exclusive tid eb1.loc eb1.ts ts mem1` in *both* arms — that is the payload discharging `writable`'s `EX` obligation on the source side (`:560`–`:577`, `:1036`–`:1054`). |
| **`RES = ts` view of exclusive writes** (`Promising.v:902`) | **NOT USED.** Discharged either vacuously (target view above `ts`) or by literal equality; see `CertifySim.v:583` / `:1059` — `condtac` splits on `ex && (arch == riscv)` and both branches close without knowing `arch`. |
| **`ifc (ex && riscv) exbank.view` in `writable`'s `view_pre`** (`Promising.v:876`) | USED only through `sim_view_join` + the `sim_exbank` view field (`CertifySim.v:970`, `CertifyProgressRiscV.v:988`–`:992`). Would hold without it — and D2 already includes this term unconditionally (deviation D-2), which is *stronger*, i.e. still fine. |
| **`Memory.exclusive`** (`Promising.v:98`) | **USED, essential**, via `sim_mem1_exclusive` (`CertifySim.v:388`): exclusivity extends from the boundary `ts` upward *because every source message above `ts` belongs to `tid`* (`sim_mem`'s `MEM1'`/`SRC_PROMISES`/`TS_PRIVATE`). This is the single most important structural invariant to reproduce. |
| **`promises`** | Essential, obviously — `PROMISES1`/`PROMISES2` (`:135/:136`) and `Local.wf`'s `PROMISES` fields (`Promising.v:1031, :1032`). |

## 4. `certified_exec_complete`'s induction (`CertifyComplete.v:148`)

```coq
Theorem certified_exec_complete p m (EXEC: Machine.exec p m): certified_exec p m.
```
Structure (`:152`–`:186`): convert the forward `rtc` to `clos_rt_rtn1` (`:153`)
and induct **backwards from the terminal state**. The strengthened invariant is

```coq
CERTIFY: ∀ tid st lc, IdMap.find tid m.(tpool) = Some (st,lc) →
         certify tid (ExecUnit.mk st lc m.(mem))
```
seeded at the end by `Machine.no_promise` (`:156`). At each backward step from
`m₁ --tid--> m₂`, one shows `CERTIFY` for `m₁` from `CERTIFY` for `m₂`, split three ways:

* **the stepping thread `tid`** (`:167`–`:172`): `step_certify`.
* **another thread, `tid` did a `state_step`** (`:174`–`:176`): memory is
  unchanged (`MEM`), so the certificate is literally reused.
* **another thread, `tid` did a `promise_step`** (`:177`–`:185`): memory grew by
  one message owned by `tid`; strip it with `interference_certify`
  (`mem_interference = [msg]`, `INTERFERENCE` discharged by `congr` on
  `Msg.tid msg = tid ≠ tid0`).

Per-step lemmas needed, with statements:

```coq
(* Certify.v:182 *)  state_step_certify   tid eu1 eu2 (CERTIFY: certify tid eu2)
                       (STEP: ExecUnit.state_step tid eu1 eu2): certify tid eu1.   (* trivial: prepend *)
(* CertifyComplete.v:27 *) promise_step_certify tid eu1 eu2 (CERTIFY: certify tid eu2)
                       (STEP: ExecUnit.promise_step tid eu1 eu2) (WF: ExecUnit.wf tid eu1):
                       certify tid eu1.   (* the real content: sim_eu + sim_eu_rtc_step_bot *)
(* CertifyComplete.v:78 *) step_certify = the union of the two.
(* CertifyComplete.v:90 *) eu_wf_interference tid st lc mem mem_interference
                       (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem_interference)
                       (WF: ExecUnit.wf tid (mk st lc mem)):
                       ExecUnit.wf tid (mk st lc (mem ++ mem_interference)).
(* CertifyComplete.v:101 *) interference_certify   (§2a above)
```
plus infrastructure: `Machine.rtc_step_step_wf` and `Machine.init_wf` (`:163`),
`ExecUnit.rmap_interference_wf` (`Promising.v:1459`), `Local.interference_wf`
(`Promising.v:1120`), `Local.wf_promises_above` (`Promising.v:1143`),
`Memory.latest_ts_spec`, `Memory.read_mon` (`Promising.v:101`).
Note that `promise_step_certify` and `interference_certify` have *identical*
proof bodies modulo the extra promise bit (`CertifyComplete.v:38`–`:70` vs
`:112`–`:140`) — one shared "restrict the memory" simulation covers both.
The reverse `certified_exec_sound` (`Certify.v:206`) is four lines
(`rtc_mon`), and `certified_exec_equivalent` (`CertifyComplete.v:188`) is the pair.

## 5. `axiomatic/AtoP.v: axiomatic_to_promising`

Confirmed:

```coq
(* AtoP.v:1318 *)
Theorem axiomatic_to_promising p ex (EX: Valid.ex p ex):
  exists m, <<STEP: Machine.exec p m>> /\
            <<TERMINAL: Valid.is_terminal EX -> Machine.is_terminal m>> /\
            <<STATE: IdMap.Forall2 (fun tid sl aeu => sim_state_weak (fst sl) aeu.(AExecUnit.state))
                        m.(Machine.tpool) EX.(Valid.aeus)>> /\
            <<MEM: sim_mem ex m.(Machine.mem)>>.
```
with `Machine.exec p m := rtc (Machine.step ExecUnit.step) (init p) m ∧ no_promise m`
(`Promising.v:1750`) — the **unconstrained** promising machine. Composed with
`certified_exec_equivalent` you get: axiomatic ⟹ *certified* promising.
The construction promises **everything up front**: it linearizes `ob` into
`mem_of_ex ex ob` and starts from `Machine.pf_init_with_promises p mem`
(`AtoP.v:1333`–`:1336`, `Local.init_with_promises (Machine.promises_from_mem tid ...)`,
`:1462`), then runs promise-free. That is *exactly* our `WPPromise`-unconditional
shape, so nothing about the promise discipline is smuggled in here.
RISC-V case: the only `arch == riscv` in `AtoP.v` is `:555`, inside the
forwarding argument — it feeds `Axiomatic.v:870`'s
`⦗codom_rel rmw⦘ ⨾ rfi ⨾ ⦗arch = riscv ∨ is_acquire_pc⦘` `ob` clause (and
`Axiomatic.v:907`'s `ifc (arch == riscv) rmw`), i.e. the same
no-forwarding-from-an-exclusive fact as §2d, on the axiomatic side.
It is *not* a certification dependency.

## 6. Assessment for the D2 machine (PARM-per-byte, no `RES = ts`)

**Verdict: `interference_certify` in the direction D8 needs
(`CertifyComplete.v:101`, memory restriction) is provable for the D2 machine.
No `RES` and no aq-raise change is required.** Reasoning:

1. The `RES = ts` view is not used by the arch-generic proof at all (§3, row 7):
   the two sites that touch `res` (`CertifySim.v:583`, `:1059`) `condtac` on
   `ex && (arch == riscv)` and close **both** branches without the hypothesis.
   D2's choice — an AMO's `rd` gets the read half's post-view — is *strictly
   easier*: if that post-view is `> ts` the `sim_val` goal is vacuous
   (`sim_val_above`), and if it is `≤ ts` then by the read case the source read
   the *same* message with the *same* view, so `rd`'s value and view are equal.
   The concern recorded in `weak-memory-layer2.md` §8 ("D8 likely has to add the
   AMO's own write timestamp to the aq raise") is **not forced**; it would only
   be forced by the *progress* direction, and even there only at
   `CertifyProgressRiscV.v:552/:1033`, where an equality argument replaces it.
2. D2 already has the term that PARM's `writable` gates on `ex && riscv` — the
   read half's post-view in `fulfil_vpre` (deviation D-2, `weak-memory-deps.md`
   §2.3′) — unconditionally, i.e. **stronger** than PARM. Stronger `view_pre`
   only makes `EXT` harder in the *given* run, which is the hypothesis side:
   free.
3. The shape that motivated the whole question (new store above the boundary,
   fence, promised fulfil below) is not a certifiable configuration in *either*
   machine (§2c(2)); no view arithmetic rescues or needs to rescue it.

**The lemma that *would* break, and what it costs.** The single genuinely
RISC-V-dependent step in PARM's development is
`CertifyProgressRiscV.v:761/:853/:863/:870` — the `sim_fwdbank_above'` arm
(`:87`) killed by `FwdItem.read_view`'s `fwd.ex && (arch == riscv)` disjunct
(`Promising.v:528`). D2 deviates here (recorded as **D-5b**): `WeakMem.fwd_view`
disables forwarding when the *load* is `aq`, not when the *banked store* was
exclusive. **If D8 ever wants the progress/deadlock-freedom direction, that arm
is where it breaks**, and the fix is D-5b's already-scoped follow-up: add an
`ex` flag to `w_fwd`'s payload and disable forwarding on `fwd.ex` (dropping the
`aq` test). It is unrelated to `RES`.

**Three *new* obligations that PARM does not have**, which are the actual D8
risk (none is a view-arithmetic problem):

* **The device fabric `pc_dev`.** PARM's `ExecUnit` has no shared component
  beyond memory, so "interference" is purely `mem ++ mem_interference`. Ours is
  `(pc_log, pc_dev)`; a certifying run of agent `i` moves `pc_dev`
  (`WeakPromise.v:451` and every `pstep`), and interference moves it too. `sim_eu`
  needs a `sim_dev` component and `eu_wf_interference` a fabric analogue. This
  is where the G4/G5 fabric machinery (`qfab`, `gdev`, `dev_epoch_ok`) has to be
  re-used, and it is the single largest delta.
* **`lat = true` (flat / latest-indexed) reads.** `read_ok_d … lat …`
  (`WeakPromiseBridge.v:167`, `WeakPromise.v:459`) indexes by `latest_ts`, which
  is **not** stable under removing messages: the source memory has *fewer*
  foreign messages but *more* of `i`'s own new stores above the boundary, so the
  latest message at a location can differ on both sides. PARM's read rule always
  names an explicit `ts` and so never meets this. G6a already recorded the
  refutation of "the disk-flat pstep input"; the certification port inherits it.
  Expect to need either a `latest`-specific arm of the read case (source reads
  the latest, target view `> ts` — PARM's Case 1 shape, `CertifySim.v:698`) or
  the same "irreducible delta (i)" residue.
* **The fused RMW.** PARM splits LR/SC into two steps linked by `exbank`; D2's
  `WPRmw`/`PFRmw` fuse them, so the read-half choice and the write-half
  timestamp move together. `sim_exbank`'s payload (`Memory.exclusive tid loc
  eb.ts ts mem1`, `CertifySim.v:110`) becomes an obligation *inside* the single
  RMW case rather than a carried invariant — mechanically simpler, but the
  `sim_mem1_exclusive` argument (`:388`, "every source message above the
  boundary is `tid`'s") must be reproduced for `excl_ok`, and `excl_ok`'s window
  is per-byte over `tvs`.

Also note `certify_step` is **not** `wp_pf_step`: `wp_pf_step` has no arm that
fulfils an *existing* promise. The port's certification relation must be
`wp_cert_step i := (wpstep at agent i, minus WPPromise) ∪ (PFStore/PFRmw)` —
exactly PARM's `state_step ∪ write_step`.

---

## Recommendation for D8

Port the **arch-generic** `CertifySim.v` line (`sim_eu` with equality below the
boundary, `sim_eu_step`/`sim_eu_rtc_step_bot`, `promise_step_certify`,
`interference_certify`, `certified_exec_complete`) and **skip
`CertifyProgressRiscV.v` entirely** — it proves deadlock-freedom, not
completeness, and it is the only place `arch == riscv` and the `RES = ts` view
do any work. Concretely: define `wp_cert_step i` as agent `i`'s `wpstep` arms
minus `WPPromise`, unioned with `PFStore`/`PFRmw` (fused, append-at-top), and
`wp_certify i cfg := ∃ cfg', rtc (wp_cert_step i) cfg cfg' ∧ prom_i cfg' = ∅`;
prove the two `vcap` lemmas first (`Certify.v:144/166` — `EXT ⊒ w_vcap` is the
whole proof and D2 already has `w_vcap` in `fulfil_vpre`), then `sim_wpcfg` with
the four invariants that actually carry the argument (views equal below the
boundary; **every source message above the boundary is agent `i`'s**; the
forward bank two-armed; `excl_ok` extended upward from the boundary). Budget the
effort against the three deltas above — the device fabric `pc_dev`, `lat`-indexed
flat reads, and the fused RMW — **not** against view arithmetic: neither `RES`
nor a change to the acquire raise is needed, and D2's D-2 (unconditional read-half
post-view in `fulfil_vpre`) is already stronger than what PARM needs.
`weak-memory-layer2.md` §8/§10.1 should be amended accordingly, and D-5b noted
as the only genuine RISC-V gap — relevant solely if progress is ever wanted.
