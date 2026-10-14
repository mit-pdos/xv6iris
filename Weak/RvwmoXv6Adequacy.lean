/-
Weak: **W11 part C — the LOG-LEVEL `badSeg` arm and its refutation through the access-discipline
export** (allocproc plan rev 50, §C top "W11 — LAUNCH PLAN", part W11-C; §C W11 (i); rulings
[OWN.61], [OWN.63], [OWN.64], [OWN.70]).  Lean-only (no Rocq source).

## What this file proves

* `badSeg GD log prev s` — the LOG-LEVEL bad arm of one segment: the entry reads a byte from the
  write `prev` at log position `p` (`gwriteAt (p + 1) = some prev`), whose message is `.WCplain`
  (owned, `clsOf = .SCowned`), authored by a hart `i` FOREIGN to the entry's hart (both harts,
  `< NCPU`: DMA authors and the disk agent's reads are outside, as in `violationHart` and in
  the export's `e.tid < NCPU`), and unpublished at `log` (`¬ wpublished log m.wmTid p`, i.e. no
  later release-class message of `i` — `pubOf`'s log predicate).
* `l2ClaimAtB GD P` — `l2ClaimAt`'s text (`WeakRvwmoGlue.lean:442`) with `badSeg GD log prev s`
  in place of the run-level `Bad` (`badRun`, refuted only over EVERY `epfRun`-reachable
  configuration, `noBadRun`); `Glue` is untouched (W11-F restates the capstones).
* `rawChainChainB` — the composition: a raw chain classified by `l2ClaimAtB`, with `¬ badSeg` at
  each of its segments, IS a `WeakRvwmoKillArms.chain` (the `badSeg` twin of `rawChainChain`).
* `ownedUnpubRefuted` — **the refutation at a realized read, through `R`**: at a MachCSL state
  `σ` related to a pf configuration `c` by W2's memory relation `rmem` (`R-log`, `R-hist`: the
  memory is the pf log's per-byte history `TsoOfPf.histOf`, timestamp = position + 1, author =
  `wmTid`), whose access discipline holds (`xv6AccessDisc σ`, the export, from
  `powerInterp_accessDisc`), where hart `j`'s coherence floor at the byte is the read's foreign
  source (`(σ.hr j).coh pa = p + 1` — `cohSrc`'s stamp at the read's post-state, the floor only
  rises), the message is NOT owned-and-unpublished at any extension `log` of `c.pcLog` — UNLESS
  the byte is, as of the entry, in a class the export does not chain (`benignAt`: a lock-layer
  word, a publication word, a live page-table byte, or an audited racy word whose value is
  in the value set).  The chained case: `chainOkAt` gives a sync path from the author's
  entries at or below `p + 1` to `j`; its first move is the author's own release
  (`syncHop`'s `⟨r, A, 0⟩`, `r > p + 1`) or its publication store (`pubCover`'s
  `⟨r, w, v⟩`, `r > p + 1`); `R-hist` turns that entry into the log message at `r - 1` by the
  author; the static release-site fact `relSiteWCrel` (a NAMED premise: such a message is
  `.WCrel`) publishes the source.
* `badSegBenign` — the graph-level corollary: a `badSeg` whose entry read is realized
  (`segRealized`) survives only on a `benignAt` byte.
* The value arms, read off the export: `lkCpuArm` (the lock-layer route, [OWN.64]: a non-holder's
  read of `lk->cpu` never returns its own pointer, `lkCpuReadAt`), `irefArm` (the `ip->ref`
  route, [OWN.63]: `racyValOk` is the registry's value-set fact `racyValAt`, the word `≥ 1`).

## Deviations from the plan text / open points (see `PROGRESS-W11C.md`)

1. `relSiteWCrel` is a NAMED premise of `ownedUnpubRefuted`, not a theorem: the plan cites "the
   static release-site fact `fence rw,w; sw`, W9a, carried by `R`'s log identification", which
   is not in the tip (the pf class of a store is `pclsEv`'s `wRelp` flag, invisible to MachCSL's
   histories).  Spec: RVWMO/riscv.cat/Sail/Zifencei/PMAs are silent on a proof's message
   classes; the premise is a program fact about xv6's text (true of the image's release sites as
   far as checked: `fence rw,w` immediately before `sw zero` in `release`, `fence; sw` for
   `started = 1`).
2. **`badSeg` is NOT refuted on `benignAt` bytes** — the lock-layer and `ip->ref` arms give
   VALUE facts (`lkCpuArm`, `irefArm`), not `¬ badSeg`: `badSeg` as the plan defines it is TRUE
   at a real xv6 run whose certified log prefix ends while the holder of a lock has written
   `lk->cpu = mycpu()` (`acquire+0x28`, `.WCplain`: `mycpu`'s prologue store clears `wRelp`
   after the fence) and a non-holder's `holding()` has read it (`holding+0x12`, `PResidue`).
   The plan clause "badSeg is refuted there by `lkCpu_read_not_mine`" is therefore not provable
   as stated; `PROGRESS-W11C.md` gives the spec-first options.
3. The realized read (`readAt`/`segRealized`) is an INTERFACE: producing it from the certified
   run (graph → candidate → pf run → W4's `SimRel`, the read's post-state) is W11-F's
   composition; this file consumes exactly `rmem`, the floor equation and the export.

Every Lean-only helper is file-qualified (`RvwmoXv6Adequacy.*`).
-/
import Weak.WeakRvwmoGlue
import Weak.PfStepTsoMem
import Xv6.AccessDiscipline

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std PfStepTsoMem

/-! # 1. The log-level bad arm and the restated claim -/

/-- **The LOG-LEVEL bad arm** (plan §C W11 (i)): the segment's entry reads a byte from the write
`prev` at log position `p`, whose message is `.WCplain`, by a hart `i` foreign to the entry's
hart, and unpublished at `log` (no later `.WCrel` message of `i`). -/
def badSeg (GD : Gdexec) (log : List Wmsg) (prev : Geid) (s : Seg) : Prop :=
  ∃ (p : Nat) (m : Wmsg) (i : Nat) (a : Int) (v : BitVec 8),
    greadsByte GD.gdG s.sgEntry a (p + 1) v ∧ gwriteAt GD.gdG (p + 1) = some prev ∧
    log[p]? = some m ∧ m.wmTid = some i ∧ i < NCPU ∧ s.sgEntry.1 < NCPU ∧ s.sgEntry.1 ≠ i ∧
    m.wmAk = .WCplain ∧ ¬ wpublished log m.wmTid p

/-- **The LOG-LEVEL L2′ claim**: `l2ClaimAt`'s text with `badSeg` in place of the run-level
`Bad`. -/
def l2ClaimAtB (GD : Gdexec) (P : Int → Int → Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoMinusDepsConsistent GD →
    logOf GD.gdG log →
    protReg P log →
    ss ≠ [] → rawChain GD z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → gcross GD.gdG prev s.sgEntry → segRun GD s →
      segPin GD s ∨ csHyps GD P log prev s ∨ badSeg GD log prev s

/-- **The composition** (`rawChainChain`'s `badSeg` twin): a raw chain whose segments are
classified with `¬ badSeg` at each of them IS a certified chain. -/
theorem rawChainChainB (GD : Gdexec) (P : Int → Int → Prop) (log : List Wmsg) (ss : List Seg) :
    rvwmoMinusDepsConsistent GD → logOf GD.gdG log → protReg P log →
    (∀ prev s, s ∈ ss → gcross GD.gdG prev s.sgEntry → segRun GD s →
       segPin GD s ∨ csHyps GD P log prev s ∨ badSeg GD log prev s) →
    (∀ prev s, s ∈ ss → gcross GD.gdG prev s.sgEntry → ¬ badSeg GD log prev s) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → rawChain GD x y ss' → WeakRvwmoKillArms.chain GD.gdG x y ss' := by
  intro hcons hlog hpr hcl hnb x y ss'
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := fun t ht => hsub (List.mem_cons_of_mem s ht)
    show Cert GD.gdG x s ∧ WeakRvwmoKillArms.chain GD.gdG s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hc | hb
    · exact segPinCert GD x s hcons hx hp
    · exact csHypsCert GD P log x s hcons hlog hpr hc hx
    · exact absurd hb (hnb x s hs hx)

/-- The `l2ClaimAtB` instance at a classified cycle, composed (`cycleKillArms`). -/
theorem cycleKillB (GD : Gdexec) (P : Int → Int → Prop) (log : List Wmsg) (z : Geid)
    (ss : List Seg) :
    rvwmoMinusDepsConsistent GD → logOf GD.gdG log → protReg P log →
    l2ClaimAtB GD P → ss ≠ [] → rawChain GD z z ss →
    (∀ prev s, s ∈ ss → gcross GD.gdG prev s.sgEntry → ¬ badSeg GD log prev s) → False := by
  intro hcons hlog hpr hcl hne hch hnb
  exact cycleKillArms GD.gdG z ss hcons.1 hne
    (rawChainChainB GD P log ss hcons hlog hpr (hcl log z ss hcons hlog hpr hne hch) hnb z z ss
      (fun _ h => h) hch)

/-! # 2. `R`'s per-byte history, both directions -/

/-- A log message's byte is an entry of `R`'s history (timestamp = position + 1). -/
theorem RvwmoXv6Adequacy.histOfMem (img : Image) (log : List Wmsg) (a : Int) (p : Nat) (m : Wmsg)
    (v : BitVec 8) (hp : log[p]? = some m) (hv : msgByte m a = some v) :
    (⟨p + 1, m.wmTid.getD 0, v⟩ : HEnt) ∈ TsoOfPf.histOf img log a := by
  unfold TsoOfPf.histOf
  apply List.mem_append_left
  rw [List.mem_reverse, List.mem_filterMap]
  refine ⟨p, List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1, ?_⟩
  simp [hp, hv]

/-- Every entry of `R`'s history is the image's (timestamp 0) or a log message's. -/
theorem RvwmoXv6Adequacy.histOfMemInv (img : Image) (log : List Wmsg) (a : Int) (e : HEnt)
    (h : e ∈ TsoOfPf.histOf img log a) :
    e.t = 0 ∨ ∃ m, log[e.t - 1]? = some m ∧ msgByte m a = some e.v ∧ e.tid = m.wmTid.getD 0 := by
  unfold TsoOfPf.histOf at h
  rcases List.mem_append.1 h with h | h
  · right
    rw [List.mem_reverse, List.mem_filterMap] at h
    obtain ⟨i, -, hi⟩ := h
    cases hl : log[i]? with
    | none => simp [hl] at hi
    | some m =>
      cases hb : msgByte m a with
      | none => simp [hl, hb] at hi
      | some v =>
        simp only [hl, hb, Option.bind_some, Option.map_some, Option.some.injEq] at hi
        subst hi
        exact ⟨m, by simpa using hl, hb, rfl⟩
  · left
    cases himg : img a with
    | none => simp [himg] at h
    | some v =>
      simp only [himg, Option.map_some, Option.toList_some, List.mem_singleton] at h
      subst h
      rfl

/-- Under `rhist`, a byte the memory holds is a RAM byte whose history is `R`'s. -/
theorem RvwmoXv6Adequacy.rhistGet {m : FlatMem} {img : Image} {log : List Wmsg} {pa : PAddr}
    {H : Hist} (hr : rhist m img log) (h : m[pa]? = some H) :
    H = TsoOfPf.histOf img log (paZ pa) := by
  by_cases hram : inRam pa 1
  · rw [hr.1 pa hram] at h
    exact (Option.some.inj h).symm
  · rw [hr.2 pa hram] at h
    cases h

/-! # 3. The release-site premise and the first move of a sync path -/

/-- The entries a sync path's FIRST move consists of: a `syncHop`'s release entry on a hop byte,
or a publication store. -/
def RvwmoXv6Adequacy.relEntAt (σ : MState) (r : Nat) : Prop :=
  (∃ (b : PAddr) (A C : CPU) (a' : Nat), syncHop σ.mem b A r C a' ∧
      Xv6.AccessDiscipline.hopByteAt σ b a') ∨
  (∃ (f : PAddr) (w : CPU) (v : BitVec 8) (H : Hist),
      (Xv6.AccessDiscipline.xv6Env σ).isPub f w ∧ σ.mem[f]? = some H ∧ ⟨r, hartAgent w, v⟩ ∈ H)

/-- **The static release-site fact** (NAMED premise, deviation 1; the plan's "WCrel on the pf
log (the static release-site fact `fence rw,w; sw`, W9a, carried by `R`'s log identification)"):
every log message whose entry is a sync path's first move — a lock release or a publication
store — is release-class. -/
def relSiteWCrel (σ : MState) (log : List Wmsg) : Prop :=
  ∀ (q : Nat) (mq : Wmsg), log[q]? = some mq → RvwmoXv6Adequacy.relEntAt σ (q + 1) →
    mq.wmAk = .WCrel

/-- A hop chain's first hop: the author's own release after its entry. -/
theorem RvwmoXv6Adequacy.hopChainFirst {m : FlatMem} {isLk : PAddr → Nat → Prop} {A : CPU}
    {t : Nat} {B : CPU} {a : Nat} (h : hopChain m isLk A t B a) :
    ∃ (b : PAddr) (r : Nat) (C : CPU) (a' : Nat), isLk b a' ∧ syncHop m b A r C a' ∧ t < r := by
  induction h with
  | base b hb hh ht => exact ⟨b, _, _, _, hb, hh, ht⟩
  | step b _ _ _ _ ih => exact ih

/-- A `syncHop`'s release entry is in the hop byte's history. -/
theorem RvwmoXv6Adequacy.syncHopRel {m : FlatMem} {b : PAddr} {A : CPU} {r : Nat} {C : CPU}
    {a : Nat} (h : syncHop m b A r C a) :
    ∃ H, m[b]? = some H ∧ (⟨r, hartAgent A, 0⟩ : HEnt) ∈ H := by
  obtain ⟨H1, H2, e0, va, hb, -⟩ := h
  exact ⟨_, hb, by simp⟩

/-- **A sync path's first move** from author `A`'s entries at or below `t`: an entry of `A` above
`t` that is a lock release or a publication store, held in some byte's history. -/
theorem RvwmoXv6Adequacy.syncPathFirst {σ : MState} {A : CPU} {t : Nat} {B : CPU} {τ : Nat}
    (h : Xv6.AccessDiscipline.syncPath σ A t B τ) :
    ∃ (r : Nat) (pa : PAddr) (H : Hist) (v : BitVec 8), t < r ∧ σ.mem[pa]? = some H ∧
      (⟨r, hartAgent A, v⟩ : HEnt) ∈ H ∧ RvwmoXv6Adequacy.relEntAt σ r := by
  have hop : ∀ {B' : CPU} {a : Nat}, hopChain σ.mem (Xv6.AccessDiscipline.hopByteAt σ) A t B' a →
      ∃ (r : Nat) (pa : PAddr) (H : Hist) (v : BitVec 8), t < r ∧ σ.mem[pa]? = some H ∧
        (⟨r, hartAgent A, v⟩ : HEnt) ∈ H ∧ RvwmoXv6Adequacy.relEntAt σ r := by
    intro B' a hc
    obtain ⟨b, r, C, a', hb, hh, ht⟩ := RvwmoXv6Adequacy.hopChainFirst hc
    obtain ⟨H, hH, he⟩ := RvwmoXv6Adequacy.syncHopRel hh
    exact ⟨r, b, H, 0, ht, hH, he, .inl ⟨b, A, C, a', hh, hb⟩⟩
  rcases h with ⟨a, -, hc⟩ | ⟨f, w, r, v, H, -, hp, hf, he, -, harm⟩
  · exact hop hc
  · rcases harm with ⟨rfl, ht⟩ | ⟨a, -, hc⟩
    · exact ⟨r, f, H, v, ht, hf, he, .inr ⟨f, A, v, H, hp, hf, he⟩⟩
    · -- `hopChain X.m X.isLk` is `hopChain σ.mem (hopByteAt σ)` by definition
      exact hop hc

/-! # 4. The refutation at a realized read, through `R` -/

/-- **The classes the export does not chain** (as of position `t`): a lock-layer word, a
publication word, a live page-table byte, or an audited racy word whose value is in the value
set (`chainOkAt`'s exemptions and its `racyValOk` arm). -/
def benignAt (σ : MState) (pa : PAddr) (t : Nat) : Prop :=
  (∃ b, Xv6.AccessDiscipline.custAt σ pa t = .lockw b) ∨
  (∃ w, Xv6.AccessDiscipline.custAt σ pa t = .pub w) ∨
  Xv6.AccessDiscipline.custAt σ pa t = .pte ∨
  (Xv6.AccessDiscipline.custAt σ pa t = .racy ∧ Xv6.AccessDiscipline.racyValOk σ pa t)

/-- **A realized read** of byte `pa` by hart `j` from log position `p` (message `m`): a MachCSL
state `σ` related to the pf configuration `c` by `R`'s memory half (`rmem`), with the export and
the release-site fact, `c`'s log a prefix of `log`, the message writing the byte, and `j`'s floor
at the byte the read's source (`cohSrc`'s stamp at the read's post-state). -/
def readAt (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState)
    (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg) : Prop :=
  rmem c st σ ∧ Xv6.AccessDiscipline.xv6AccessDisc σ ∧ relSiteWCrel σ c.pcLog ∧
  c.pcLog <+: log ∧ c.pcLog[p]? = some m ∧ (msgByte m (paZ pa)).isSome ∧ inRam pa 1 ∧
  (σ.hr j).coh pa = p + 1

/-- **THE REFUTATION** (plan §C W11-C): at a realized read of a FOREIGN hart's message, the
message is not owned-and-unpublished at `log`, unless the byte is `benignAt`. -/
theorem ownedUnpubRefuted (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel))
    (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg) (i : Nat)
    (hrd : readAt log c st σ j pa p m) (hi : m.wmTid = some i) (hiN : i < NCPU)
    (hij : i ≠ hartAgent j) :
    benignAt σ pa (p + 1) ∨ ¬ (m.wmAk = .WCplain ∧ ¬ wpublished log m.wmTid p) := by
  obtain ⟨hR, hD, hrel, hpre, hp, hv, hram, hcoh⟩ := hrd
  obtain ⟨⟨htid, -⟩, -, hr, -⟩ := hR
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv
  -- every log message has an author (`R-log`)
  have hsome : ∀ (q : Nat) (mq : Wmsg), c.pcLog[q]? = some mq → ∃ k, mq.wmTid = some k := by
    intro q mq hq
    have h1 : (c.pcLog.map Wmsg.wmTid)[q]? = some mq.wmTid := by simp [hq]
    rw [htid] at h1
    simp only [List.getElem?_map] at h1
    cases hq' : σ.log[q]? with
    | none => simp [hq'] at h1
    | some k => simp only [hq', Option.map_some, Option.some.injEq] at h1; exact ⟨k, h1.symm⟩
  -- the source entry, in the memory's history of the byte (`R-hist`)
  have hH := hr.1 pa hram
  have he : (⟨p + 1, i, v⟩ : HEnt) ∈ TsoOfPf.histOf c.pcImg c.pcLog (paZ pa) := by
    have := RvwmoXv6Adequacy.histOfMem c.pcImg c.pcLog (paZ pa) p m v hp hv
    rwa [hi] at this
  by_cases hb : benignAt σ pa (p + 1)
  · exact .inl hb
  right
  rintro ⟨-, hnp⟩
  have h1 : ∀ b, Xv6.AccessDiscipline.custAt σ pa (p + 1) ≠ .lockw b :=
    fun b hb' => hb (.inl ⟨b, hb'⟩)
  have h2 : ∀ w, Xv6.AccessDiscipline.custAt σ pa (p + 1) ≠ .pub w :=
    fun w hw => hb (.inr (.inl ⟨w, hw⟩))
  have h3 : Xv6.AccessDiscipline.custAt σ pa (p + 1) ≠ .pte := fun h => hb (.inr (.inr (.inl h)))
  rcases hD.1 j pa _ ⟨p + 1, i, v⟩ hH he (by simp) hcoh.symm hiN hij h1 h2 h3 with hs | hrc
  · -- the chained case: the author's first move after its entry is release-class
    obtain ⟨r, pb, H, w, hlt, hHb, heb, hrelr⟩ := RvwmoXv6Adequacy.syncPathFirst hs
    rw [RvwmoXv6Adequacy.rhistGet hr hHb] at heb
    rcases RvwmoXv6Adequacy.histOfMemInv _ _ _ _ heb with h0 | ⟨mq, hq, -, htq⟩
    · simp only at h0 hlt
      omega
    · simp only at hq htq
      obtain ⟨k, hk⟩ := hsome _ _ hq
      have hr1 : r - 1 + 1 = r := by simp only at hlt; omega
      have hcls := hrel (r - 1) mq hq (by rw [hr1]; exact hrelr)
      apply hnp
      obtain ⟨rest, hrest⟩ := hpre
      refine ⟨r - 1, mq, by simp only at hlt; omega, ?_, ?_, hcls⟩
      · rw [← hrest]; exact lookup_app_l_Some hq
      · rw [hk, hi]
        rw [hk] at htq
        exact congrArg some htq.symm
  · exact hb (.inr (.inr (.inr hrc)))

/-- **The graph-level corollary**: a realized entry read (`segRealized`, W11-F's composition
supplies it from the certified run) leaves `badSeg` only on a `benignAt` byte. -/
def segRealized (GD : Gdexec) (log : List Wmsg) (s : Seg) : Prop :=
  ∀ (p : Nat) (m : Wmsg) (a : Int) (v : BitVec 8),
    greadsByte GD.gdG s.sgEntry a (p + 1) v → log[p]? = some m →
    ∃ (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr),
      j.val = s.sgEntry.1 ∧ paZ pa = a ∧ readAt log c st σ j pa p m

theorem badSegBenign (GD : Gdexec) (log : List Wmsg) (prev : Geid) (s : Seg) :
    segRealized GD log s → badSeg GD log prev s →
    ∃ (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr)
      (p : Nat) (m : Wmsg),
      readAt log c st σ j pa p m ∧ benignAt σ pa (p + 1) := by
  rintro hre ⟨p, m, i, a, v, hrd, -, hp, hi, hiN, -, hne, hcl, hnp⟩
  obtain ⟨c, st, σ, j, pa, hj, -, hat⟩ := hre p m a v hrd hp
  rcases ownedUnpubRefuted log c st σ j pa p m i hat hi hiN
      (fun h => hne (by rw [← hj]; exact h.symm)) with hb | hb
  · exact ⟨c, st, σ, j, pa, p, m, hat, hb⟩
  · exact absurd ⟨hcl, hnp⟩ hb

/-- Off the `benignAt` bytes, the realized certified run has NO `badSeg`. -/
theorem noBadSegOfRealized (GD : Gdexec) (log : List Wmsg) (prev : Geid) (s : Seg) :
    segRealized GD log s →
    (∀ (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr)
       (p : Nat) (m : Wmsg), readAt log c st σ j pa p m → ¬ benignAt σ pa (p + 1)) →
    ¬ badSeg GD log prev s := by
  intro hre hnb hbad
  obtain ⟨c, st, σ, j, pa, p, m, hat, hb⟩ := badSegBenign GD log prev s hre hbad
  exact hnb c st σ j pa p m hat hb

/-! # 5. The value arms, read off the export -/

/-- **The lock-layer route** ([OWN.64], `lkCpuReadAt`): for every exported lock word, a hart that
is not the holder never reads its own pointer `&cpus[c]` out of `lk->cpu` -- the value fact
`holding()`'s compare consumes (NOT a refutation of `badSeg`, deviation 2).  Static-lock case; since W8 (f3-pipelk) the export's
`lkCpuReadAt` has a second arm for live pipe locks (`xv6DynLock`), read off the export directly. -/
theorem lkCpuArm (σ : MState) (hD : Xv6.AccessDiscipline.xv6AccessDisc σ) (b : PAddr) (t : Nat)
    (hb : Xv6.AccessDiscipline.xv6LockWord σ b t)
    (hs : b ∈ Xv6.AccessDiscipline.xv6StaticLocks) :
    ∃ (W : WordHist 4) (W' : WordHist 8) (Hold Hold' : Nat → Hist) (st : Option (CPU × Bool))
      (B : Nat),
      wordHistAt σ.mem b 4 W Hold ∧ wordHistAt σ.mem (b + 16#64) 8 W' Hold' ∧
      lockDiscW (cpuPtrAt KernelGeom.cpusBase) st B W W' ∧
      ∀ (c : CPU), (∀ k, st ≠ some (c, k)) → ∀ (tvn : Nat) (v0 w : BitVec 64), v0 ≠ cpuAddr c →
        ReadCases W' (hartAgent c) tvn v0 w → w ≠ cpuAddr c :=
  (hD.2.2.2.1 b t hb).1 hs

/-- **The `ip->ref` route** ([OWN.63]): on a `racy` byte whose entry is value-safe, the audited
word, as of the entry, is in the registry's value set (`racyValAt`: `[1, 2^31)`, the guard
`ip->ref < 1` reads `≥ 1`) -- NO sync path claimed (NOT a refutation of `badSeg`, deviation 2). -/
theorem irefArm (σ : MState) (pa : PAddr) (t : Nat)
    (h : Xv6.AccessDiscipline.custAt σ pa t = .racy ∧ Xv6.AccessDiscipline.racyValOk σ pa t) :
    racyValAt Xv6.AccessDiscipline.xv6Rsv σ.mem t pa :=
  h.2

/-- On a `benignAt` byte that is no lock-layer, publication or page-table byte, the value fact. -/
theorem benignValue (σ : MState) (pa : PAddr) (t : Nat) (hb : benignAt σ pa t)
    (h1 : ∀ b, Xv6.AccessDiscipline.custAt σ pa t ≠ .lockw b)
    (h2 : ∀ w, Xv6.AccessDiscipline.custAt σ pa t ≠ .pub w)
    (h3 : Xv6.AccessDiscipline.custAt σ pa t ≠ .pte) :
    racyValAt Xv6.AccessDiscipline.xv6Rsv σ.mem t pa := by
  rcases hb with ⟨b, hb⟩ | ⟨w, hw⟩ | hp | hr
  · exact absurd hb (h1 b)
  · exact absurd hw (h2 w)
  · exact absurd hp h3
  · exact irefArm σ pa t hr

end Weak
