/-
Weak: **the FRAME FACT as a corollary of `chainOkAt`** — Q-TRAPRES option T2 ([OWN.79]; plan
`notes/weak-allocproc-plan.md` rev 52 §D Q-TRAPRES (T2), §C W9a (B) (B2-free's `texcM` relation
`FR`, sub-item W9b1-FRAME); stop report `PROGRESS-W8trapres.md` (T2), B2's `PROGRESS-W9aB2.md`).
Lean-only, no Rocq twin.

**What is consumed.**  B2-free's alignment `texcM FR` (`Weak/PinTrap.lean`, `texcFree`: `FR w k :=
grf G (i, w) (i, k)`) and W9b-1's two `ld ra` (`Weak/PinHoldingCtrl.lean`: `mycpu+0x18`,
`holding+0x22`) need ONE fact about xv6: a restore READS FROM its slot's last spill.  Spec first:
RVWMO's load-value axiom lets the restore return the spill or any store to the byte coherence-after
it; rule 12 (`gppo12`) needs the `rfi`; RVWMO/riscv.cat/Sail say nothing about which hart may write
which address; trap entry and `sret` are not fences; Zifencei/PMAs are silent (the stack is RAM).
So the fact is about xv6's program — every route below PROVES it from the export: FAITHFUL.

**The argument (T2).**  Hart `j`'s restore at `pa` reads the FIRST visible entry of `pa`'s history
(`Hist.readEnt`: own entries always visible, `HEnt.visible`).  The spill `es` is `j`'s own, so the
source `e0` is `es` or LATER (`findDesc`, the histories descend).  If later:
  * `e0` is `j`'s own — excluded by `ownClearAfter` (no own store to `pa` after the spill: the
    census's slot keys, `frameSlotsOk`);
  * `e0` is a DMA author's — excluded by (iii) `frameNoDmaAfter`;
  * `e0` is a FOREIGN hart's — then `j`'s coherence floor at `pa` names it, and on a byte that is
    not exempt as of `e0.t` ((ii) `frameUnexemptAfter`) `chainOkAt` gives a `syncPath` from
    `e0`'s author to `j`: by the `hopChain`/`pubCover` time order (`hopChainLast`: every hop
    rises) `j` made a HOP-BYTE ACQUIRE after `e0.t` (`hopAcqAfter`) or OBSERVED A PUBLICATION
    STORE after `e0.t` (`pubSeenAfter`) — `foreignFloorSync`, the corollary proper.  Neither
    happens between a spill and its restore: the windows contain NO AMO/LR (`frameWindowsNoAmo`)
    and NO `started` load site (`frameWindowsNoStarted`), decided over the image.
`restoreSrcSpill` is the state-level theorem; `frameRfOfRestore` / **`frameRf`** lift it through
W2's `R` (`rmem`) to the graph's `grf` — the plug-in B5 calls at every `texcM` restore and at
W9b1-FRAME's two `ld ra`.

**What is NAMED after it (exact statements: `frameUnexemptAfter`, `frameNoDmaAfter`).**
  (ii) `frameUnexemptAfter σ pa s`: as of every position after the spill the frame byte's custody
       is not `lockw`/`pub`/`pte`/`racy` (static for `stack0`; for `kalloc`'d `kstack` pages an
       allocator fact — not in the export);
  (iii) `frameNoDmaAfter σ pa s`: every entry on the frame byte after the spill is a hart's
       (`chainOkAt` exempts DMA authors — not in the export).
**The realization interface** (`FrameWin`, W11-F's composition / B5's per-state discharge, of the
same kind as `RvwmoXv6Adequacy.readAt`/`syncRealized`): the restore's MachCSL source is the graph
read's stamp (`restoreAt`); in-order realization of `j` over the window; and the two TEXT facts
`syncRealized` already carries (a hop byte's nonzero word store is an `.aq` AMO; a read of
`started` is a read of a publication byte at `main+0x16`).  `FrameQuiet` is the event-level reading
of the decided census facts (B5: the window's items are the census pcs' items).

**Deviation (spec-first, see `PROGRESS-trapT2.md`).**  "No `started` load in the window" is NOT
decidable as an ADDRESS fact over the image: the windows hold non-`sp` loads whose addresses are
register VALUES (`holding+0x12`'s `lk->cpu` — the caller's lock pointer; `uartintr`'s `lbu`s through
the `uarts[i].base` word; `push_off`/`pop_off`/`myproc` through `mycpu()`'s return).  What IS
decided is the SITE fact (no `started`-load site in any window); the address half rides the text
interface (`FrameWin.pubIn`), as `syncRealized`'s does.  Alternative (proved, `k2OfBoot`): the
one-shot publication (`MachCSL.pubOneShot_of_rsv`, from `rsvAllOk` — `powerInterp_rsvOk`) plus the
boot order "`started = 1` precedes the spill" (a hart `≠ 0` reaches no trap path and no `holding`
before its gate).

Every Lean-only helper is file-qualified (`PinTrapFrame.*`).
-/
import Weak.RvwmoXv6Adequacy
import Weak.PinTrapSites
import Weak.AxGraph

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std PfStepTsoMem
open Xv6.AccessDiscipline (custAt chainOkAt hopByteAt xv6Env xv6AccessDisc xv6Rsv)

namespace PinTrapFrame

/-! ## 1. The named facts and the window conditions (state level) -/

/-- **(ii) at one position**: the frame byte is not exempt from `chainOkAt` as of `t` — not a
lock-layer word, a publication word, a live page-table byte, nor an audited racy word. -/
def frameUnexempt (σ : MState) (pa : PAddr) (t : Nat) : Prop :=
  (∀ b, custAt σ pa t ≠ .lockw b) ∧ (∀ w, custAt σ pa t ≠ .pub w) ∧ custAt σ pa t ≠ .pte ∧
    custAt σ pa t ≠ .racy

/-- **(ii) NAMED**: the frame byte is unexempt as of every position after the spill `s`. -/
def frameUnexemptAfter (σ : MState) (pa : PAddr) (s : Nat) : Prop :=
  ∀ t, s < t → frameUnexempt σ pa t

/-- **(iii) NAMED**: no DMA entry on the frame byte after the spill `s` — every later entry is a
hart's. -/
def frameNoDmaAfter (σ : MState) (pa : PAddr) (s : Nat) : Prop :=
  ∀ (H : Hist) (e : HEnt), σ.mem[pa]? = some H → e ∈ H → s < e.t → e.tid < NCPU

/-- Hart `j` made a HOP-BYTE ACQUIRE entry at a position in `(s, σ.top]` (a `syncHop`'s acquire). -/
def hopAcqAfter (σ : MState) (j : CPU) (s : Nat) : Prop :=
  ∃ (b : PAddr) (C : CPU) (r a : Nat), s < a ∧ a ≤ σ.top ∧ hopByteAt σ b a ∧ syncHop σ.mem b C r j a

/-- Hart `j`'s floor at a publication byte (writer `w ≠ j`) has reached a store LATER than `s`. -/
def pubSeenAfter (σ : MState) (j : CPU) (s : Nat) : Prop :=
  ∃ (f : PAddr) (w : CPU) (r : Nat) (v : BitVec 8) (H : Hist), j ≠ w ∧ (xv6Env σ).isPub f w ∧
    σ.mem[f]? = some H ∧ (⟨r, hartAgent w, v⟩ : HEnt) ∈ H ∧ s < r ∧ r ≤ (σ.hr j).coh f

/-- No own entry of `j` on `pa` after the spill `s` (the load-value half: the census's slot map
records the LAST spill). -/
def ownClearAfter (σ : MState) (j : CPU) (pa : PAddr) (s : Nat) : Prop :=
  ∀ (H : Hist) (e : HEnt), σ.mem[pa]? = some H → e ∈ H → e.tid = hartAgent j → s < e.t → False

/-- Every byte history descends in the timestamp (latest first). -/
def memDesc (m : FlatMem) : Prop :=
  ∀ (pa : PAddr) (H : Hist), m[pa]? = some H → H.Pairwise (fun e e' => e'.t < e.t)

theorem memDescOfRhist {m : FlatMem} {img : Image} {log : List Wmsg} (hr : rhist m img log) :
    memDesc m := fun pa H h => by
  rw [RvwmoXv6Adequacy.rhistGet hr h]
  exact RvwmoXv6Adequacy.histOfDesc img log (paZ pa)

theorem hopAcqAfterMono {σ : MState} {j : CPU} {s t : Nat} (hst : s ≤ t) :
    hopAcqAfter σ j t → hopAcqAfter σ j s :=
  fun ⟨b, C, r, a, h1, h2, h3, h4⟩ => ⟨b, C, r, a, Nat.lt_of_le_of_lt hst h1, h2, h3, h4⟩

theorem pubSeenAfterMono {σ : MState} {j : CPU} {s t : Nat} (hst : s ≤ t) :
    pubSeenAfter σ j t → pubSeenAfter σ j s :=
  fun ⟨f, w, r, v, H, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨f, w, r, v, H, h1, h2, h3, h4, Nat.lt_of_le_of_lt hst h5, h6⟩

/-! ## 2. The corollary of `chainOkAt` and the restore's source -/

/-- In a descending history the first `p`-entry is at or above every `p`-entry. -/
theorem findDesc {H : Hist} (hd : H.Pairwise (fun e e' => e'.t < e.t)) {p : HEnt → Bool}
    {x y : HEnt} (hx : H.find? p = some x) (hy : y ∈ H) (hpy : p y = true) : x = y ∨ y.t < x.t := by
  induction H with
  | nil => simp at hx
  | cons z H ih =>
    rw [List.pairwise_cons] at hd
    cases hz : p z with
    | true =>
      simp only [List.find?_cons, hz, Option.some.injEq] at hx
      subst hx
      rcases List.mem_cons.1 hy with rfl | hy
      · exact .inl rfl
      · exact .inr (hd.1 y hy)
    | false =>
      simp only [List.find?_cons, hz] at hx
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hz] at hpy; cases hpy
      · exact ih hd.2 hx hy

/-- A hop's acquire is later than its release (descending histories). -/
theorem syncHopLtD {m : FlatMem} (hd : memDesc m) {b : PAddr} {A : CPU} {r : Nat} {B : CPU}
    {a : Nat} (h : syncHop m b A r B a) : r < a := by
  obtain ⟨H1, H2, e0, va, hb, -⟩ := h
  exact RvwmoXv6Adequacy.descConsLt (x := ⟨a, hartAgent B, va⟩) (y := ⟨r, hartAgent A, 0⟩)
    (H1 := H1) (H2 := e0 :: H2) (hd b _ hb) rfl

/-- **The hop chain's time order** (`MachCSL/ChainDefs.lean` `hopChain`): the chained entries
(at or below `t`) precede the LAST acquire `a`, which is the reader's entry on a hop byte. -/
theorem hopChainLast {m : FlatMem} (hd : memDesc m) {isLk : PAddr → Nat → Prop} {A : CPU} {t : Nat}
    {B : CPU} {a : Nat} (h : hopChain m isLk A t B a) :
    t < a ∧ ∃ (b : PAddr) (C : CPU) (r : Nat), isLk b a ∧ syncHop m b C r B a := by
  induction h with
  | base b hb hh ht => exact ⟨Nat.lt_trans ht (syncHopLtD hd hh), b, _, _, hb, hh⟩
  | step b _ hb hh ha ih =>
    exact ⟨Nat.lt_trans ih.1 (Nat.lt_trans ha (syncHopLtD hd hh)), b, _, _, hb, hh⟩

/-- **THE COROLLARY OF `chainOkAt`** (T2, header): if hart `j`'s coherence floor at `pa` names a
FOREIGN hart's post-power-on entry `e` on a byte unexempt as of `e.t`, then `j` made a hop-byte
acquire after `e.t` or observed a publication store after `e.t`. -/
theorem foreignFloorSync (σ : MState) (hC : chainOkAt σ) (hd : memDesc σ.mem) (j : CPU)
    (pa : PAddr) (H : Hist) (e : HEnt) (hH : σ.mem[pa]? = some H) (he : e ∈ H) (ht0 : e.t ≠ 0)
    (hcoh : e.t = (σ.hr j).coh pa) (hA : e.tid < NCPU) (hne : e.tid ≠ hartAgent j)
    (hu : frameUnexempt σ pa e.t) : hopAcqAfter σ j e.t ∨ pubSeenAfter σ j e.t := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  rcases hC j pa H e hH he ht0 hcoh hA hne h1 h2 h3 with hs | ⟨hr, -⟩
  · rcases hs with ⟨a, ha, hc⟩ | ⟨f, w, r, v, Hf, hjw, hp, hf, hew, hrc, harm⟩
    · obtain ⟨hta, b, C, r, hb, hh⟩ := hopChainLast hd hc
      exact .inl ⟨b, C, r, a, hta, by simp only [MState.top] at ha ⊢; omega, hb, hh⟩
    · have hlt : e.t < r := by
        rcases harm with ⟨-, h⟩ | ⟨a, ha, hc⟩
        · exact h
        · exact Nat.lt_trans (hopChainLast (m := σ.mem) hd hc).1 ha
      exact .inr ⟨f, w, r, v, Hf, hjw, hp, hf, hew, hlt, hrc⟩
  · exact absurd hr h4

/-- **THE RESTORE READS ITS SPILL** (state level, header): hart `j`'s load of `pa` at view `tv`
returns the first visible entry `e0`; `es` is `j`'s own spill; under (ii), (iii) and the three
window conditions, `e0` IS `es`. -/
theorem restoreSrcSpill (σ : MState) (hC : chainOkAt σ) (hd : memDesc σ.mem) (j : CPU)
    (pa : PAddr) (H : Hist) (hH : σ.mem[pa]? = some H) (es e0 : HEnt) (hes : es ∈ H)
    (hesj : es.tid = hartAgent j) (tv : Nat)
    (hsrc : H.find? (HEnt.visible (hartAgent j) tv) = some e0)
    (hcoh : e0.tid ≠ hartAgent j → (σ.hr j).coh pa = e0.t)
    (hu : frameUnexemptAfter σ pa es.t) (hdma : frameNoDmaAfter σ pa es.t)
    (hk1 : ¬ hopAcqAfter σ j es.t) (hk2 : ¬ pubSeenAfter σ j es.t)
    (hk3 : ownClearAfter σ j pa es.t) : e0 = es := by
  have hvis : HEnt.visible (hartAgent j) tv es = true := by
    simp [HEnt.visible, hesj]
  rcases findDesc (hd pa H hH) hsrc hes hvis with h | hlt
  · exact h
  · exfalso
    have he0 : e0 ∈ H := List.mem_of_find?_eq_some hsrc
    by_cases hown : e0.tid = hartAgent j
    · exact hk3 H e0 hH he0 hown hlt
    · rcases foreignFloorSync σ hC hd j pa H e0 hH he0 (by omega) (hcoh hown).symm
          (hdma H e0 hH he0 hlt) hown (hu e0.t hlt) with h | h
      · exact hk1 (hopAcqAfterMono (Nat.le_of_lt hlt) h)
      · exact hk2 (pubSeenAfterMono (Nat.le_of_lt hlt) h)

/-! ## 3. Through `R`: the graph's `grf` -/

/-- **The realized restore** (an INTERFACE, as `RvwmoXv6Adequacy.readAt`): a MachCSL state `σ`
(the restore's post-state) related to the pf configuration `c` by `R`'s memory half, with the
export, `c`'s log a prefix of `log`, and hart `j`'s load of the RAM byte `pa` returning the first
visible entry `e0` of its history (`Hist.readEnt`) at the graph read's stamp `p + 1`, with `j`'s
floor at the byte that stamp when the source is foreign (`cohSrc`'s stamp at the post-state). -/
def restoreAt (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState)
    (j : CPU) (pa : PAddr) (p : Nat) : Prop :=
  rmem c st σ ∧ xv6AccessDisc σ ∧ c.pcLog <+: log ∧ inRam pa 1 ∧
  ∃ (H : Hist) (tv : Nat) (e0 : HEnt), σ.mem[pa]? = some H ∧
    H.find? (HEnt.visible (hartAgent j) tv) = some e0 ∧ e0.t = p + 1 ∧
    (e0.tid ≠ hartAgent j → (σ.hr j).coh pa = p + 1)

/-- **The restore's rf is the spill** (graph level): at a realized restore `(j, k)` reading byte
`pa` at stamp `p + 1`, the spill `Sp` (a graph write of `j` to `pa`, executed by `σ`) is its
rf-source at `pa`, under (ii), (iii) and the window conditions at the spill's write index. -/
theorem frameRfOfRestore (G : Gexec) (log : List Wmsg) (c : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p k : Nat) (v : BitVec 8)
    (Sp : Geid) (hre : restoreAt log c st σ j pa p) (hwf : gwf G) (hlog : logOf G log)
    (hrd : greadsByte G (hartAgent j, k) (paZ pa) (p + 1) v)
    (hSp : Sp ∈ gwrites G) (hSpj : Sp.1 = hartAgent j) (hSpb : ∃ v', gwritesByte G Sp (paZ pa) v')
    (hSpx : gwix G Sp ≤ c.pcLog.length)
    (hu : frameUnexemptAfter σ pa (gwix G Sp)) (hdma : frameNoDmaAfter σ pa (gwix G Sp))
    (hk1 : ¬ hopAcqAfter σ j (gwix G Sp)) (hk2 : ¬ pubSeenAfter σ j (gwix G Sp))
    (hk3 : ownClearAfter σ j pa (gwix G Sp)) :
    grfAt G (paZ pa) Sp (hartAgent j, k) := by
  obtain ⟨hR, hD, hpre, hram, H, tv, e0, hH, hsrc, he0t, hcoh⟩ := hre
  have hr := hR.2.2.1
  obtain ⟨v', hv'⟩ := hSpb
  have hgw := gwriteAtGwix G Sp hSp
  have hix0 : gwix G Sp ≠ 0 := by
    intro h0
    rw [h0] at hgw
    simp [gwriteAt] at hgw
  obtain ⟨rest, hrest⟩ := hpre
  obtain ⟨m, hm, hgm⟩ := logOfWrite G log Sp hwf hlog hSp
    (by rw [← hrest, List.length_append]; omega)
  have hmc : c.pcLog[gwix G Sp - 1]? = some m := by
    rw [← hrest, lookup_app_l (by omega)] at hm
    exact hm
  have hmb : msgByte m (paZ pa) = some v' :=
    (WeakRvwmoKillArms.gmsgByte G Sp m (paZ pa) v' hgm).2 hv'
  have hes := RvwmoXv6Adequacy.histOfMem c.pcImg c.pcLog (paZ pa) (gwix G Sp - 1) m v' hmc hmb
  rw [gmsgTid G Sp m hgm, Nat.sub_add_cancel (Nat.pos_of_ne_zero hix0)] at hes
  simp only [Option.getD_some] at hes
  rw [← RvwmoXv6Adequacy.rhistGet hr hH] at hes
  have heq := restoreSrcSpill σ hD.1 (memDescOfRhist hr) j pa H hH ⟨gwix G Sp, Sp.1, v'⟩ e0 hes
    hSpj tv hsrc (fun h => by rw [hcoh h, he0t]) hu hdma hk1 hk2 hk3
  have hp : p + 1 = gwix G Sp := by rw [← he0t, heq]
  exact ⟨p + 1, v, hrd, by rw [hp]; exact hgw⟩

/-! ## 4. The window conditions from the realization and the census -/

/-- A graph event reads a byte of a publication word (as of `σ`'s registry). -/
def greadsPub (G : Gexec) (σ : MState) (e : Geid) : Prop :=
  ∃ (f : PAddr) (w : CPU) (t : Nat) (v : BitVec 8), (xv6Env σ).isPub f w ∧ greadsByte G e (paZ f) t v

/-- **THE WINDOW'S REALIZATION** (an INTERFACE, W11-F / B5 — of `syncRealized`'s kind): at the
restore's post-state `σ`, for the spill `(j, w)` (write index `s`) and the restore `(j, k)`:
`acqIn` — a graph write of `j` at a hop-ACQUIRE entry after `s` is an `.aq` event (xv6's text: a
hop byte's nonzero word store is `acquire`'s `amoswap.w.aq`) po-between the two (in-order
realization); `pubIn` — `j`'s observation of a publication store after `s` is a read of a
publication byte po-between the two (the floor rises only at a load of the byte; the store did not
exist at the spill); `ownIn` — a write of `j` to `pa` after `s` executed by `σ` is po-between the two
(in-order realization). -/
structure FrameWin (G : Gexec) (σ : MState) (j : CPU) (pa : PAddr) (s w k : Nat) : Prop where
  acqIn : ∀ W, W ∈ gwrites G → W.1 = hartAgent j → s < gwix G W → gwix G W ≤ σ.top →
    (∃ (b : PAddr) (C : CPU) (r : Nat), hopByteAt σ b (gwix G W) ∧ syncHop σ.mem b C r j (gwix G W)) →
    glblIs G W lbAq ∧ w < W.2 ∧ W.2 < k
  pubIn : pubSeenAfter σ j s → ∃ x, w < x ∧ x < k ∧ greadsPub G σ (hartAgent j, x)
  ownIn : ∀ W, W ∈ gwrites G → W.1 = hartAgent j → s < gwix G W → gwix G W ≤ σ.top →
    (∃ v, gwritesByte G W (paZ pa) v) → w < W.2 ∧ W.2 < k

/-- **THE WINDOW IS QUIET** (the event-level reading of the decided census facts §5; B5: the
window's events are the items of the census pcs between the spill and the restore): no `.aq`
event (no AMO/LR, `frameWindowsNoAmo`), no read of a publication byte (no `started`-load site,
`frameWindowsNoStarted`), no other write to `pa` (`frameSlotsOk`: the slot keys are 8-aligned
doublewords, the slot map holds the LAST spill). -/
structure FrameQuiet (G : Gexec) (σ : MState) (j : CPU) (pa : PAddr) (w k : Nat) : Prop where
  noAcq : ∀ x, w < x → x < k → ¬ glblIs G (hartAgent j, x) lbAq
  noPub : ∀ x, w < x → x < k → ¬ greadsPub G σ (hartAgent j, x)
  noOwn : ∀ x, w < x → x < k → ∀ v, ¬ gwritesByte G (hartAgent j, x) (paZ pa) v

theorem k1OfWindow (G : Gexec) (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel))
    (σ : MState) (j : CPU) (pa : PAddr) (s w k : Nat) (hR : rmem c st σ) (hpre : c.pcLog <+: log)
    (hwf : gwf G) (hlog : logOf G log) (hW : FrameWin G σ j pa s w k) (hQ : FrameQuiet G σ j pa w k) :
    ¬ hopAcqAfter σ j s := by
  rintro ⟨b, C, r, a, hsa, hat, hb, hh⟩
  obtain ⟨Hb, va, hHb, hmem⟩ := RvwmoXv6Adequacy.syncHopAcq hh
  obtain ⟨W, hW', hix, hW1, -⟩ :=
    RvwmoXv6Adequacy.entGraph hR hpre hwf hlog hHb hmem (by simp only; omega)
  simp only at hix hW1
  obtain ⟨haq, h1, h2⟩ := hW.acqIn W hW' hW1 (by omega) (by omega)
    ⟨b, C, r, by rw [hix]; exact hb, by rw [hix]; exact hh⟩
  obtain ⟨W1, W2⟩ := W
  simp only at hW1 h1 h2
  subst hW1
  exact hQ.noAcq W2 h1 h2 haq

theorem k2OfWindow (G : Gexec) (σ : MState) (j : CPU) (pa : PAddr) (s w k : Nat)
    (hW : FrameWin G σ j pa s w k) (hQ : FrameQuiet G σ j pa w k) : ¬ pubSeenAfter σ j s :=
  fun h => let ⟨x, h1, h2, h3⟩ := hW.pubIn h; hQ.noPub x h1 h2 h3

theorem k3OfWindow (G : Gexec) (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel))
    (σ : MState) (j : CPU) (pa : PAddr) (s w k : Nat) (hR : rmem c st σ) (hpre : c.pcLog <+: log)
    (hwf : gwf G) (hlog : logOf G log) (hW : FrameWin G σ j pa s w k) (hQ : FrameQuiet G σ j pa w k) :
    ownClearAfter σ j pa s := by
  intro H e hH he hej hse
  rw [RvwmoXv6Adequacy.rhistGet hR.2.2.1 hH] at he
  rcases RvwmoXv6Adequacy.histOfMemInv _ _ _ _ he with h0 | ⟨mq, hq, hb, htq⟩
  · omega
  · obtain ⟨rest, hrest⟩ := hpre
    have hlen := (List.getElem?_eq_some_iff.1 hq).1
    have hq' : log[e.t - 1]? = some mq := by rw [← hrest]; exact lookup_app_l_Some hq
    obtain ⟨W, -, hgm, hix, hW'⟩ := logOfLookup G log (e.t - 1) mq hwf hlog hq'
    have hwb := (WeakRvwmoKillArms.gmsgByte G W mq (paZ pa) e.v hgm).1 hb
    rw [gmsgTid G W mq hgm] at htq
    simp only [Option.getD_some] at htq
    have hll : c.pcLog.length = σ.log.length := by
      have := congrArg List.length hR.1.1
      simpa using this
    obtain ⟨h1, h2⟩ := hW.ownIn W hW' (by rw [← htq]; exact hej) (by omega)
      (by simp only [MState.top]; omega) ⟨e.v, hwb⟩
    obtain ⟨W1, W2⟩ := W
    simp only at h1 h2 htq
    have e1 : W1 = hartAgent j := by rw [← htq]; exact hej
    subst e1
    exact hQ.noOwn W2 h1 h2 e.v hwb

/-- **The boot-order alternative** for the publication arm (proved; see the header's deviation):
the publication bytes are one-shot (`MachCSL.pubOneShot_of_rsv`, from the reserved regions'
discipline, `powerInterp_rsvOk`), and a post-power-on store of each of them precedes the spill. -/
theorem k2OfBoot (σ : MState) (j : CPU) (s : Nat) (hone : rsvAllOk xv6Rsv σ.mem)
    (hboot : ∀ (f : PAddr) (w : CPU) (H : Hist), (xv6Env σ).isPub f w → j ≠ w → σ.mem[f]? = some H →
      ∃ e, e ∈ H ∧ e.t ≠ 0 ∧ e.t ≤ s) :
    ¬ pubSeenAfter σ j s := by
  rintro ⟨f, w, r, v, H, hjw, hp, hf, he, hsr, -⟩
  obtain ⟨e, he', he0, hes⟩ := hboot f w H hp hjw hf
  have := pubOneShot_of_rsv (wit := slotWit xv6Rsv) (σ := σ) hone f w H _ e hp hf he he'
    (by simp only; omega) he0
  simp only at this
  omega

/-! ## 5. THE PLUG-IN (B5 calls it at every `texcM` restore and at W9b1-FRAME's two `ld ra`) -/

/-- **THE FRAME FACT, discharged** (header): at a realized restore `(j, k)` reading byte `pa` of
its slot, the spill `(j, w)` (a write of `j` to `pa`, executed by the restore's post-state, write
index `s`) is its rf-source — `texcM`'s `FR w k` (`fun w k => grf G (i, w) (i, k)`, `i = j`) —
from the export's `chainOkAt` (inside `restoreAt`), the realization interface (`FrameWin`), the
decided quiet window (`FrameQuiet`), and the two NAMED facts (ii) `frameUnexemptAfter`, (iii)
`frameNoDmaAfter`. -/
theorem frameRf (G : Gexec) (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel))
    (σ : MState) (j : CPU) (pa : PAddr) (p w k : Nat) (v : BitVec 8)
    (hre : restoreAt log c st σ j pa p) (hwf : gwf G) (hlog : logOf G log)
    (hrd : greadsByte G (hartAgent j, k) (paZ pa) (p + 1) v)
    (hSp : (hartAgent j, w) ∈ gwrites G) (hSpb : ∃ v', gwritesByte G (hartAgent j, w) (paZ pa) v')
    (hSpx : gwix G (hartAgent j, w) ≤ c.pcLog.length)
    (hii : frameUnexemptAfter σ pa (gwix G (hartAgent j, w)))
    (hiii : frameNoDmaAfter σ pa (gwix G (hartAgent j, w)))
    (hW : FrameWin G σ j pa (gwix G (hartAgent j, w)) w k) (hQ : FrameQuiet G σ j pa w k) :
    WeakRvwmoAcyc.grf G (hartAgent j, w) (hartAgent j, k) := by
  have hR := hre.1
  have hpre := hre.2.2.1
  exact grfAtGrf G (paZ pa) _ _
    (frameRfOfRestore G log c st σ j pa p k v (hartAgent j, w) hre hwf hlog hrd hSp rfl hSpb hSpx
      hii hiii (k1OfWindow G log c st σ j pa _ w k hR hpre hwf hlog hW hQ)
      (k2OfWindow G σ j pa _ w k hW hQ) (k3OfWindow G log c st σ j pa _ w k hR hpre hwf hlog hW hQ))

/-! ## 6. The census half, decided over the image (`decide +kernel`, no premise)

The WINDOWS: every pc a fence-free trap path executes between a spill and its restore lies in the
free region of a `trapFreeFuns` function (`PinTrapSites.trapRunFreeFuns`), so `frameTrapPcs` (the
union of those regions) covers `kernelvec`'s 16 pairs and the callee-save pairs; W9b1-FRAME's
windows are `mycpu+0x2..+0x18` and `holding+0xa..+0x22` with `mycpu`'s body (called at
`holding+0x16`). -/

open PinTrapSites KernelPinsDef

/-- An instruction of the AMO major opcode (`0x2f`: AMOs, LR, SC) — the only encodings with an
`aq` bit (Sail `AMO`/`LOADRES`; every plain load's `aq` is false). -/
def isAmoLr (pc : Int) : Bool := !wIsRvc (kw pc) && wOp (kw pc) == 0x2f

/-- The trap windows: the free regions of the fence-free functions. -/
def frameTrapPcs : List Int := trapFreeFuns.flatMap (freeOf trapTab)

/-- The straight-line pcs from `lo` to `hi` (fuel-bounded). -/
def pcRange : Nat → Int → Int → List Int
  | 0, _, _ => []
  | f + 1, lo, hi => if hi < lo then [] else lo :: pcRange f (lo + wSize (kw lo)) hi

/-- `mycpu`'s body (its window: `sd ra,8(sp)` at `+0x2`, `ld ra,8(sp)` at `+0x18`). -/
def frameMycpuPcs : List Int :=
  pcRange 32 (KernelSyms.«mycpu» : Int) ((KernelSyms.«mycpu» : Int) + 0x1e)

/-- `holding`'s window (`sd ra,24(sp)` at `+0xa`, `ld ra,24(sp)` at `+0x22`) with `mycpu`'s body. -/
def frameHoldingPcs : List Int :=
  pcRange 32 ((KernelSyms.«holding» : Int) + 0xa) ((KernelSyms.«holding» : Int) + 0x22) ++
    frameMycpuPcs

/-- Every window. -/
def frameWinPcs : List Int := frameTrapPcs ++ frameHoldingPcs

/-- The windows' ends are the pairs' instructions (shape check, non-vacuity): `mycpu`'s and
`holding`'s `ra` spill/restore, the call into `mycpu`, and `kernelvec`'s first spill, its call of
`kerneltrap` and its last restore lie in the windows. -/
theorem frameHoldEnds :
    spSt ((KernelSyms.«mycpu» : Int) + 0x2) = some 8 ∧
    spLd ((KernelSyms.«mycpu» : Int) + 0x18) = some 8 ∧
    spSt ((KernelSyms.«holding» : Int) + 0xa) = some 24 ∧
    spLd ((KernelSyms.«holding» : Int) + 0x22) = some 24 ∧
    intMem ((KernelSyms.«holding» : Int) + 0x16) frameHoldingPcs = true ∧
    intMem ((KernelSyms.«holding» : Int) + 0x22) frameHoldingPcs = true ∧
    intMem ((KernelSyms.«mycpu» : Int) + 0x18) frameMycpuPcs = true ∧
    kflowOf ((KernelSyms.«holding» : Int) + 0x16) = .FLcall (KernelSyms.«mycpu» : Int) ∧
    intMem (kvPc + 0x2) frameTrapPcs = true ∧ intMem (kvPc + 0x24) frameTrapPcs = true ∧
    intMem (kvPc + 0x48) frameTrapPcs = true := by
  decide +kernel

/-- **NO ACQUIRE AMO** in any window (header): no AMO/LR encoding, no AMO role. -/
theorem frameWindowsNoAmo :
    frameWinPcs.all (fun pc => !isAmoLr pc &&
      (match krole pc with | .ORamo _ _ _ => false | _ => true)) = true := by
  decide +kernel

/-- The `started` load sites (generator: the image's ONLY load whose static address is
`started`): the boot gate `while(started == 0)` at `main+0x16` (`lw a5,0(a4)`, `a4` = `started`
from `main+0xc`'s `auipc`/`addi`), followed by `fence r,rw`. -/
def startedLoadSites : List Int := [(KernelSyms.«main» : Int) + 0x16]

theorem startedLoadSitesShape :
    startedLoadSites.all (fun pc => roleIsLoad (krole pc)) = true := by decide +kernel

/-- **NO `started` LOAD SITE** in any window (header). -/
theorem frameWindowsNoStarted :
    frameWinPcs.all (fun pc => !intMem pc startedLoadSites) = true := by decide +kernel

/-- An `sp`-based access of a DOUBLEWORD (`sd`/`ld`, `c.sdsp`/`c.ldsp`). -/
def spAcc8 (w : Nat) : Bool :=
  if wIsRvc w then (w &&& 3) == 2 && (wfield w 15 13 == 7 || wfield w 15 13 == 3)
  else (wOp w == 0x23 || wOp w == 0x03) && wF3 w == 3

/-- Every spill/restore of a fence-free walk state is a doubleword at an 8-aligned slot key (the
key `sp + o` of `texcM`'s slot map, offset from the trap's entry `sp`): distinct keys are disjoint
bytes. -/
def slotOkb : Bool :=
  trapFlow.all (fun row =>
    match spSt row.1.tPc, spLd row.1.tPc with
    | some o, _ => (row.2.1 + o) % 8 == 0 && spAcc8 (kw row.1.tPc)
    | none, some o => (row.2.1 + o) % 8 == 0 && spAcc8 (kw row.1.tPc)
    | none, none => true)

/-- **THE SLOT KEYS ARE DISJOINT DOUBLEWORDS** (header). -/
theorem frameSlotsOk : slotOkb = true := by decide +kernel

/-- W9b1-FRAME's windows' stores: `holding`'s three saves (keys 24, 16, 8 of its frame) and
`mycpu`'s two (8, 0 of ITS frame, 16 below: keys −8, −16) — none but the spill hits key 24; in
`mycpu`'s own window the only store besides the spill is key 0. -/
theorem frameHoldStores :
    (frameHoldingPcs.filter isStoreb).map (fun pc => (pc, spSt pc)) =
      [((KernelSyms.«holding» : Int) + 0xa, some 24), ((KernelSyms.«holding» : Int) + 0xc, some 16),
       ((KernelSyms.«holding» : Int) + 0xe, some 8), ((KernelSyms.«mycpu» : Int) + 0x2, some 8),
       ((KernelSyms.«mycpu» : Int) + 0x4, some 0)] ∧
    spAdj (kw (KernelSyms.«mycpu» : Int)) = some (-16) := by
  decide +kernel

end PinTrapFrame
end Weak

