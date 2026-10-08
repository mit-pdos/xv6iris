# Q20 — the off-row return under Stage C (design note, advisory)

Owner ruling Q20 (2026-10-08): rework the off-row argument so that a diverted fetch outside
kernel text is a NO-IMAGE fetch (stuck via `FirstRd.frNf` / `FEC.fcNf` / `ekey.ENf`), restoring
Rocq's "a diverted c.ret is stuck" (`AxSpinE6.Xx_ret`, consumed by `AxSpinE8.wpd_mycpu`).

**Verdict in one line.** The restriction is implementable, but for xv6's page table it never
produces a stuck verdict on the c.ret path: every executable page IS kernel text, and every
other diverted target traps into `kernelvec`, which is ALSO kernel text.  What Rocq's row fetch
pin really did under Stage C is done by a GRAPH-VALUE pin on the `ra` reload (§D, Option V,
recommended) — the exact Stage C form of the "TEMPORARY ROW PINNING" assumption the Rocq chain
already carries (AxSpinPO1.v header, owner decision 2026-10-03).

Sources read: protocol "Cross-file facts" (Stage C, Q12, Q13, AxSpinVA*, AxSpinE/E3/E4/E5,
KERNEL DRIFT); `Weak/AxSpinE3.lean` (FirstRd arms, `Foff`, `offrowRowStuck`, `wpdOffrowM`),
`Weak/AxSpinE4.lean`, `Weak/AxSpinE5.lean` (`OutSt`/`OutLd`/`RLfact`), `Weak/AxSpinVA.lean`
(ENf/fcNf/`noPinOfImgNone`), `Weak/AxSpinE9.lean`, `Weak/WeakAxRealize.lean` (`fetchPin`),
`Weak/AxSymEngine.lean` (`imgBytes`, `textFixed`), `Weak/AxSpineOk.lean`/`AxSpineOk6.lean`
(`imgOf`/`imgS`), `Weak/WeakRvwmoSupply.lean` (`emFetchImg`), the parked
`weak-orch/parked/AxSpinE6/{AxSpinE6.lean,PROGRESS-AxSpinE6.md}`, Rocq `AxSpinE6.v` (Xx_ret,
va_first_read, Off), `AxSpinE8.v` (Row_mycpu, rf_fetch), `AxSpinE8d.v`, `AxSpinPO1.v` headers,
`Xv6/KernelImage.lean` symbols, xv6 `kernel/vm.c` `kvmmake`, `kernel/trap.c` `w_stvec`.

## A. What "restrict the image to kernel text" has to mean

**Which image.** Two images are in play and both must change together:

1. The GRAPH's image `GD.gdG.gxImg` — the fetch oracle `WeakAxRealize.fetchPin img l` reads it
   (a pinned `LIFetch base tvs` has `img (base+j) = tvs[j].2`, timestamp 0), and
   `AxSpinE3.wpdOffrowM` already demands `HGimg : ∀ GD, G GD → GD.gdG.gxImg = img`.  Stuckness
   via `frNf`/`fcNf` is `imgBytes img pa n = none` ⇒ `¬ fetchPin img (.LIFetch pa tvs)`
   (`AxSpinVA.noPinOfImgNone`) ⇒ no pinned step.  So the verdict is about `gxImg`, and only a
   graph whose `gxImg` is `none` off kernel text can be stuck there.
2. The CERTIFICATE image `imgS σi = imgOf σi` (= `σi.mem`, `Int`-indexed), tied to the graph by
   `Hfix : textFixed (gtAdGd GT) i (imgS σi)` whose first conjunct is only `imgS σi ⊆ gxImg`.
   Hence: if `gxImg` is text-only, `σi.mem` must be text-only too (plus whatever else is in the
   restricted set) — a hypothesis on the certificate state, not a change to `imgS`.

**The restricted set must be "the fixed region", not literally text.** `textFixed`'s second
conjunct answers EVERY row read of image bytes from the image (D3: text AND page tables are
immutable); the walker's `AK_ttw` reads (AxSmodeProbe, AxSpinVA4 `walkKeys`) are answered this
way.  So the set `R` must contain kernel text and the page-table pages of `T`, and must EXCLUDE
the stack slots (otherwise `textFixed` would pin `mycpu`'s reloads to the image value, defeating
the WOK/private-slot argument — check that the concrete `σi` of AxSpinSpikeRun already has
`none` on the slot pages; `E8d` says "memory = its image + two c.nop", which suggests it does).
Recommended spelling (Lean-only, file-qualified):

```
def AxSpinE6.imgOnly (img : Image) (R : Int → Prop) : Prop := ∀ a, ¬ R a → img a = none
theorem AxSpinE6.imgBytesNoneOfOut : imgOnly img R → ¬ R pa → 0 < n → imgBytes img pa n = none
```

with `R := fun a => KernelSyms.«_entry» ≤ a ∧ a < KernelSyms.«etext» ∨ ptPage T a` at the xv6
instance.  A new premise of the shape Q12's `HGimg` (`∀ GD, G GD → GD.gdG.gxImg = imgK`) suffices
for the GRAPH side; at Ixv6 (`G GD := GD = gtAdGd GT`) it is one equation `(gtAdGd GT).gdG.gxImg
= imgK` plus `imgOnly imgK R`.  The capstone side is a genuine MODEL change: `gdexecQconf boot
d0 (imgZ σ0.wgimg) N` pins fetches to the BOOTED memory `σ0.wgimg`, i.e. text+rodata+data; to
have `gxImg` text-only the boot tie must pin to `restrict (imgZ σ0.wgimg) R` ("executing
non-text is stuck" as a modelling decision).  That touches WeakRvwmoSupply/Capstone/Glue2
statements, not just the E-chain — the owner should know the blast radius before choosing O.

(i) Legitimate kernel fetches keep their bytes: every fetch the spinlock/E-chain proofs make
(`AxSpinE7.mycpuText`, `textAtS`/`textAt4S`, AxSpinVA4 `fetchMappedImg4` at 0x80000000, the
AxSpinHd/PO/Ap words) is at a text pc, so `imgK = imgS σi` on `R` keeps `textOkB`/`tokB`
discharges unchanged.  (ii) The diverted targets the Rocq argument wants stuck — see §B: most are
NOT off-image.

## B. Where xv6's diverted targets actually land

Layout of this tree (`Xv6/KernelImage.lean`): `_entry` 0x80000000, `kernelvec` 0x800057c0,
`trampoline` 0x80006000, `etext` 0x80007000, `stack0` 0x8000a420, `cpus` 0x80012530, `end`
0x80023b10.  `mycpu` 0x8000195c, `push_off` 0x80000c1e.  Kernel page table (`kvmmake`):
`[KERNBASE, etext)` R-X, `[etext, PHYSTOP)` R-W (no X), `TRAMPOLINE` R-X → 0x80006000 (inside
text).  `trapinithart`: `w_stvec(kernelvec)`.  Under `ctrlOkSW T satp0` with `tlbExact T`:

| diverted target `tgt = jalrTgt 0 ra'`           | what the fetch does                    | stuck by frNf? |
|-------------------------------------------------|----------------------------------------|----------------|
| canonical, mapped X (⇒ PA ∈ [0x80000000,etext)) | image-answered fetch, runs kernel code | NO             |
| canonical, mapped non-X (data: stack0, cpus, …) | instruction page fault → PC = stv      | NO (traps)     |
| unmapped / non-canonical (AxSpinVA7 noncanon)   | fault → PC = stv                       | NO (traps)     |
| `stv = kernelvec` itself (0x800057c0)           | in text; first graph event is the 8-byte `sd ra,0(sp)` after `addi sp,sp,-256` | NO |

So with xv6's `T` the only executable PAs are kernel text: a fetch at a non-text PA is never
issued (the PTE X check fails first — `translateAddr` returns the fault before any RAM read,
exactly as AxSpinVA7 `F_translateAddr_noncanon` / `chain_fault_noncanon` show for the
non-canonical case).  `frNf` is UNREACHABLE on the c.ret path for the real page table; it is
reachable only for an abstract `T` with an executable mapping onto a non-text PA (the synthetic
AxSpinVA2 tables, `eF a := .ENf (a,4)`).  The Rocq argument closed the trap path with `Hstv`
("stv's fetch PA ≠ pret", an off-row FETCH); under Stage C the trap path's first graph event
is a WRITE, which `FirstRd` has no arm for — `vaFirstRd` with Rocq's `Q` (`PC = stv`) is
unprovable at the TLB-hit register-only case AND the trap case cannot be made off-row.
Plainly: a target inside kernel text, and the trap vector, are NOT stuck under any image
restriction.  Option O restores the Rocq meaning for none of the targets that matter.

## C. Change lists

### C.1 Option O (owner's ruling, as specified) — what it would take

1. `AxSpinE6.imgOnly`, `imgBytesNoneOfOut` (Lean-only, new).
2. `AxSpinE3`: generalise `FirstRd` to a `FirstEv` with memory-WRITE and FENCE first-event arms
   (`frMwr`, `frMfence`), `Foff` to writes, `offrowRowStuck`'s `Hrej` to `aidentWr`/fence, and
   `frsClosed`/`FirstRdStep` accordingly; restate `vaFirstRd`'s `Q` as "returned at a boundary
   whose PC is again in `Off`" (the image-answered register-only case) — `Off` must then be
   closed under in-text execution, which it is not.  This step has no sound instantiation at
   Ixv6 for in-text targets (B); it only serves abstract `T`.
3. `AxSpinE5`: `HtextX` unchanged; add `HimgK : (gtAdGd GT).gdG.gxImg = imgK` and
   `imgOnly imgK R` to the section (or thread via `G`).
4. `AxSpinE6.XxRet`: continuation at `k` (c.ret is register-only, e = 0; PROGRESS plan), premise
   `k < LEN`; stuck branch only when `tgt`'s translation under `T` is X-mapped to a PA with
   `imgBytes imgK pa 2 = none`; targets in text or trapping go to the CONTINUATION with
   `PC = tgt` — i.e. the statement degenerates to `xxRetTgt` plus a side stuck lemma.
5. Capstone/boot tie: `gdexecQconf`'s image argument restricted (`WeakRvwmoSupply`,
   `WeakRvwmoCapstone`, `WeakRvwmoGlue2`, `WeakRvwmoAdm` instances) — model change, large.
6. `AxSpinE8` (unported): still cannot name `ret` (the row has no fetch item), so it needs the
   value pin of C.2 anyway.  Net: O is strictly C.2 plus dead weight.

### C.2 Option V (recommended) — pin the graph VALUE, one rework worker, in order

Facts it rests on (all merged): `AxSpinE5.OutLd` hands `XxLd`'s continuation
`⌜graphValue (gtAdGd GT) (i, k) = some v⌝` purely, so after the `ld ra,8(sp)` the register
`ra` is `wordOfBytes 8 v` with `v` a function of the PINNED graph; the c.ret target is therefore
determined by `GT`, not by a physical divergence.  Stage C positions of `mycpu` (14 instrs:
`addi sp,-16; sd ra,8(sp); sd s0,0(sp); addi s0; mv a5,tp; sext.w; slli; auipc a0; addi a0;
add a0; ld ra,8(sp); ld s0,0(sp); addi sp,16; ret`): row items `k` = spill ra, `k+1` = spill
s0, `k+2` = reload ra, `k+3` = reload s0; the c.ret leaves the boundary at `k+4`.

1. **AxSpinE6** (finish the parked partial; `Hmid0`, `XxReg`, `XxSt`, `XxLd` as in
   PROGRESS-AxSpinE6.md).  `XxRet` restated, Lean-only shape (header: Rocq `Xx_ret` restated
   under Stage C, deviation "the row fetch pin is a graph value pin"):
   ```
   theorem XxRet … (s rs k pc) :
     RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
     textOkB σi T satp0 pc true (JALR …) → rfF (execute (JALR …)) → k < LEN →
     (∀ rs' ib', ⌜GoodB T satp0 rs pc true (some (jalrTgt 0 (gpr 1 rs))) none rs'⌝ -∗
        WPd ⟨PHart cpu (.pure ()) rs' none ib', k⟩ {{Ψ}}) -∗ WPd s {{Ψ}}
   ```
   (= PROGRESS's `xxRetTgt`; proof = `certJALR` + `linkOwZero` + `XxReg`).  Drop `stv`,
   `vaFirstRd`, `Hpin`, `Hn`, `Hinj`, `Hstv`, `ctrlOkSWSeip` (keep if E8 wants it).  Section
   header lists them under **Dropped** with the reason "Stage C: no row item pins a fetch".
   Optional Lean-only `AxSpinE6.retStuckNoImg`: if `tgt` translates (X) to `pa` with
   `imgBytes (gtAdGd GT).gdG.gxImg pa 2 = none`, the boundary at `k` has no pinned step
   (`AxSpinVA.rowStuckOfChainNf` / `noPinOfImgNone` + `wpdMStuck`) — records the only stuck
   meaning that survives, costs ~30 lines, has no consumer; include only if the owner wants it.
2. **AxSpinE8** (port): `Row_mycpu k row pra ps0` := `k + 4 ≤ row.length` ∧ the four `mshape`
   items (writes 8 at pra/ps0 at k, k+1; reads 8 at pra/ps0 at k+2, k+3) — no `pret`/`nret`,
   `rf_fetch` DROPPED (no fetch positions).  New premise, the Stage C pin:
   `Hval : graphValue (gtAdGd GT) (i, k + 2) = some (stBytes 8 ret)`.  Continuation at `k + 4`
   with `PC = ret`, the two `RLann` annotations at `(i,k+2)`/`(i,k+3)`.  `Hinj`/`Hstv`/`stv`/
   `va_first_read` DROPPED.  Header: "ROW PINNING (Rocq, owner 2026-10-03) ↦ GRAPH-VALUE
   PINNING: the row cannot pin control flow under Stage C; the reload's graph value does; the
   follow-up ROW-INTEGRITY theorem discharges `Hval` from the `RLfact` readback (reload bytes =
   spill bytes = entry `ra`)".
3. **AxSpinE8d/E8e/E8f**: E8d's `reach_off` ("diverted reload ⇒ stuck at the real next-fetch
   node") is FALSE under Stage C for an in-text target (as `race2_hart1_stuck` was): restate as
   "reach_off reaches the boundary with PC = the diverted value, not stuck" or drop; E8e's
   `hinj_unmapped` finding is moot (no `Hinj`) — drop.  `AxSpinE9.frb` keeps compiling; note
   in its header that its intended consumer (E8d twin) no longer exists.
4. **AxSpinPO1…PO6 / POx / POr** (unported): `fpin` for mycpu's return and for the branch arm's
   target become value pins (`Hval` for `ra`; for the `beqz` the bit `b` is `(ld_res false 4 vn
   == 0)` with `graph_value GD0 (i,k+30) = Some vn` ALREADY in PO1's continuation — the
   Rocq `AxSpinPOx.Xx_pin` "other arm row-stuck" becomes a plain case on `vn`, no stuck
   branch).  Same pattern for AxSpinHd8/9/A/B/C, AxSpinAm4, AxSpinAp9 (`Xx_ret` users).
5. **No statement changes** in AxSpinE3/E4/E5, AxSpinVA*, AxSpinE9: `FirstRd`, `vaFirstRd`,
   `wpdOffrowM`, `firstEvOffrow`, `offrowRowStuck` stay as ported, now without a consumer
   (lint: dead but faithful; header note "consumer dropped under Stage C, see Q20 note").
6. Protocol "Cross-file facts" entry: "Q20 (Stage C): control flow is pinned by GRAPH VALUES
   (`graphValue GD0 (i,k) = some v` premises), never by fetch items; `XxRet`'s continuation
   PC is `jalrTgt 0 (gpr 1 rs)`; `Row_*` shapes carry no fetch positions."

Size: V = one worker, ~2 files reworked (E6 finish, E8 port) + 3 twin files trimmed; O = the
same PLUS a model change across 4 WeakRvwmo* files, a `FirstEv` generalisation in E3, and
still no stuck verdict at Ixv6.

## D. Risks and the owner question

Risks of V: (a) the ROW-INTEGRITY follow-up grows — it must discharge value pins (from
`RLfact`/`fxPrivReadn` readback) where Rocq's discharged fetch pins; same mechanism, so the
plan's shape is unchanged; (b) `Hval` is a hypothesis on `GT` like `Row_mycpu`: a graph whose
reload value differs is simply outside the theorem's hypotheses (not stuck, not rejected) —
exactly Rocq's "this theorem proves nothing about a diverted hart" caveat, now for values.
Risks of O: model change to the boot tie; `vaFirstRd` has no true instantiation at Ixv6
(TLB-hit register-only returns normally; trap path's first event is a write); vacuous `XxRet`.

**Q20' (for the owner).**  Rocq's row FETCH pin cannot exist under Stage C.  Replace it with a
GRAPH-VALUE pin (`Hval : graphValue GD0 (i, k+2) = some (stBytes 8 ret)`; `XxRet` continues at
`PC = jalrTgt 0 (gpr 1 rs)`, no stuck branch; E8d's stuck twin dropped) — Option V — instead
of restricting the image (Option O, which never yields a stuck verdict for xv6's page table,
since every X-mapped page and `kernelvec` are kernel text)?  **Recommended: V.**  Sub-choices
if V: keep `FirstRd`/`wpdOffrowM`/E9 as consumer-less faithful ports (recommended: keep); add
the optional `AxSpinE6.retStuckNoImg` (recommended: skip until a consumer appears).
