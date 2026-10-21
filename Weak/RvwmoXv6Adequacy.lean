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

## W11 part D (§6; plan rev 52 §C W11-D; [OWN.75])

* `chainHyps GD prev s` — the NEW arm for the cross-hart kill INTO a process-stack read
  (`csHyps`' `wprotAt` is false for stack bytes, written without `p->lock`; `wprotAt` stays for the
  registered bytes): `csChained` generalised to `syncPath` hops, at graph level — a write `W` LATER
  in the log than `prev` (on writes gmo IS the log order) is gmo-before-or-at the reader's ordering
  point `Y`, which orders before the exit by rule 5 (`.aq`) or rule 4 (a fence) (`syncInto`).
  `chainHypsCertC` / `chainHypsCert`: it is a `CSchained` certificate (cat / RVWMO⁻).
* `l2ClaimAtD` / `rawChainChainD` / `cycleKillD` (RVWMO⁻) and `l2ClaimAtCD` / `rawChainChainCD` /
  `cycleKillCD` (cat): the claims with the arm added (`l2ClaimAtDOfB`: it only widens).
* **`chainHypsOfSyncPath`** — the derivation: at a realized read (`readAt`) of a foreign message
  off the `benignAt` bytes, `chainOkAt`'s `syncPath`, through `R` (`rhist` + `logOf`), IS
  `chainHyps`: the hop chain's last acquire (the reader's) or the boot hop's publication store is
  the terminal write (`hopChainSpan`: through `R`'s DESCENDING histories, `histOfDesc`, every hop
  rises; `entGraph`: a history entry is a graph write).  The reader-side realization is the
  INTERFACE `syncRealized` (in-order realization + xv6's acquire / boot-fence text), W11-F's to
  produce, like `segRealized`.  `chainHypsCertOfRealized`: the certificate.
* **`rrInOfHopChain`** — W11-A's hop premise derived: a hop chain's FIRST release (the author's)
  and LAST acquire are graph writes in log order, so `rrIn REL ACQ` holds into the reader.
* Non-vacuity: `rrMigChainHyps` / `rrMigChainHypsCert` (the migration split's reader segment).
* **No owner-uniqueness premise** (`kOwnerAt`): the hop is the export's `syncPath`, which
  `chainOkAt` gives for EVERY foreign entry off the exempt classes, whoever owns the byte.

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
4. (W11-D) The plan states `kOwnerAt` uniqueness as a NAMED hypothesis of D's lemma; the lemma
   does not consume it (see `PROGRESS-W11BD.md`) — no named premise enters from D.  The
   reader-side `syncRealized` is an interface (as `segRealized`).

Every Lean-only helper is file-qualified (`RvwmoXv6Adequacy.*`).
-/
import Weak.WeakRvwmoGlue
import Weak.PfStepTsoMem
import Xv6.AccessDiscipline
import Weak.CatLinChain
import Weak.CatReroute

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
  (∃ (b : PAddr) (A C : CPU) (a' : Nat), syncHop (σ.mem.landedOnly σ.lp) b A r C a' ∧
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

/-- Under eager landing (route P, design D5) the landed-only memory is the memory. -/
theorem RvwmoXv6Adequacy.landedOnlyEager (m : FlatMem) (lp : LandPos)
    (h : ∀ (a : PAddr) (H : Hist), m[a]? = some H → ∀ e ∈ H, lp e.t = some e.t) :
    m.landedOnly lp = m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro a
  rw [FlatMem.landedOnly_get?]
  cases hH : m[a]? with
  | none => rfl
  | some H =>
    simp only [Option.map_some, Option.some.injEq]
    apply List.filter_eq_self.2
    intro e he
    simp [h a H hH e he]

/-- **A sync path's first move** from author `A`'s entries at or below `t`: an entry of `A` above
`t` that is a lock release or a publication store, held in some byte's history. -/
theorem RvwmoXv6Adequacy.syncPathFirst {σ : MState} {A : CPU} {t : Nat} {B : CPU} {τ : Nat}
    (hlo : σ.mem.landedOnly σ.lp = σ.mem)
    (h : Xv6.AccessDiscipline.syncPath σ A t B τ) :
    ∃ (r : Nat) (pa : PAddr) (H : Hist) (v : BitVec 8), t < r ∧ σ.mem[pa]? = some H ∧
      (⟨r, hartAgent A, v⟩ : HEnt) ∈ H ∧ RvwmoXv6Adequacy.relEntAt σ r := by
  have hop : ∀ {B' : CPU} {a : Nat}, hopChain σ.mem (Xv6.AccessDiscipline.hopByteAt σ) A t B' a →
      ∃ (r : Nat) (pa : PAddr) (H : Hist) (v : BitVec 8), t < r ∧ σ.mem[pa]? = some H ∧
        (⟨r, hartAgent A, v⟩ : HEnt) ∈ H ∧ RvwmoXv6Adequacy.relEntAt σ r := by
    intro B' a hc
    obtain ⟨b, r, C, a', hb, hh, ht⟩ := RvwmoXv6Adequacy.hopChainFirst hc
    obtain ⟨H, hH, he⟩ := RvwmoXv6Adequacy.syncHopRel hh
    exact ⟨r, b, H, 0, ht, hH, he, .inl ⟨b, A, C, a', by rw [hlo]; exact hh, hb⟩⟩
  rcases h with ⟨a, -, hc⟩ | ⟨f, w, r, v, H, -, hp, hf, he, -, harm⟩
  · rw [hlo] at hc; exact hop hc
  · have hf' : σ.mem[f]? = some H := by
      have e : (Xv6.AccessDiscipline.xv6Env σ).lm = σ.mem := hlo
      rw [← e]; exact hf
    rcases harm with ⟨rfl, ht⟩ | ⟨a, -, hc⟩
    · exact ⟨r, f, H, v, ht, hf', he, .inr ⟨f, A, v, H, hp, hf', he⟩⟩
    · -- `hopChain X.lm X.isLk` is `hopChain σ.mem (hopByteAt σ)` under eager landing
      have e : (Xv6.AccessDiscipline.xv6Env σ).lm = σ.mem := hlo
      rw [e] at hc
      exact hop hc

/-! # 4. The refutation at a realized read, through `R` -/

/-- **The classes the export does not chain** (as of position `t`): a lock-layer word, a
publication word, a live page-table byte, or an audited racy word whose value is in the value
set (`chainOkAt`'s exemptions and its `racyValOk` arm). -/
def benignAt (σ : MState) (pa : PAddr) (t : Nat) : Prop :=
  (∃ b, Xv6.AccessDiscipline.custAtP σ pa t = .lockw b) ∨
  (∃ w, Xv6.AccessDiscipline.custAtP σ pa t = .pub w) ∨
  Xv6.AccessDiscipline.custAtP σ pa t = .pte ∨
  (Xv6.AccessDiscipline.custAtP σ pa t = .racy ∧ Xv6.AccessDiscipline.racyValOkP σ pa t)

/-- **A realized read** of byte `pa` by hart `j` from log position `p` (message `m`): a MachCSL
state `σ` related to the pf configuration `c` by `R`'s memory half (`rmem`), with the export and
the release-site fact, `c`'s log a prefix of `log`, the message writing the byte, and `j`'s floor
at the byte the read's source (`cohSrc`'s stamp at the read's post-state). -/
def readAt (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState)
    (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg) : Prop :=
  rmem c st σ ∧ Xv6.AccessDiscipline.xv6AccessDisc σ ∧ relSiteWCrel σ c.pcLog ∧
  c.pcLog <+: log ∧ c.pcLog[p]? = some m ∧ (msgByte m (paZ pa)).isSome ∧ inRam pa 1 ∧
  (σ.hr j).coh pa = p + 1 ∧ σ.llog = List.range' 1 σ.log.length

/-- **THE REFUTATION** (plan §C W11-C): at a realized read of a FOREIGN hart's message, the
message is not owned-and-unpublished at `log`, unless the byte is `benignAt`. -/
theorem ownedUnpubRefuted (log : List Wmsg) (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel))
    (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg) (i : Nat)
    (hrd : readAt log c st σ j pa p m) (hi : m.wmTid = some i) (hiN : i < NCPU)
    (hij : i ≠ hartAgent j) :
    benignAt σ pa (p + 1) ∨ ¬ (m.wmAk = .WCplain ∧ ¬ wpublished log m.wmTid p) := by
  obtain ⟨hR, hD, hrel, hpre, hp, hv, hram, hcoh, heg⟩ := hrd
  have hm := PfStepTsoMem.memEager c st σ hR heg
  have hlo := RvwmoXv6Adequacy.landedOnlyEager σ.mem σ.lp hm
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
  have h1 : ∀ b, Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .lockw b :=
    fun b hb' => hb (.inl ⟨b, hb'⟩)
  have h2 : ∀ w, Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .pub w :=
    fun w hw => hb (.inr (.inl ⟨w, hw⟩))
  have h3 : Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .pte := fun h => hb (.inr (.inr (.inl h)))
  rw [← hcoh] at h1 h2 h3
  rcases hD.1 j pa _ ⟨p + 1, i, v⟩ hH he (by simp) (by rw [hm pa _ hH _ he, hcoh]) hiN hij h1 h2 h3
    with hs | hrc
  · -- the chained case: the author's first move after its entry is release-class
    obtain ⟨r, pb, H, w, hlt, hHb, heb, hrelr⟩ := RvwmoXv6Adequacy.syncPathFirst hlo hs
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
  · rw [hcoh] at hrc
    exact hb (.inr (.inr (.inr hrc)))

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
    (hb : Xv6.AccessDiscipline.xv6LockWordP σ b t)
    (hs : b ∈ Xv6.AccessDiscipline.xv6StaticLocks) :
    ∃ (W : WordHist 4) (W' : WordHist 8) (Hold Hold' : Nat → Hist) (st : Option (CPU × Bool))
      (B : Nat),
      wordHistAt σ.mem b 4 W Hold ∧ wordHistAt σ.mem (b + 16#64) 8 W' Hold' ∧
      lockDiscW (cpuPtrAt KernelGeom.cpusBase) st B W W' ∧
      ∀ (c : CPU), (∀ k, st ≠ some (c, k)) → ∀ (tvn : Nat) (v0 w : BitVec 64), v0 ≠ cpuAddr c →
        ReadCasesP σ.lp W' (hartAgent c) tvn v0 w → w ≠ cpuAddr c :=
  (hD.2.2.2.1 b t hb).1 hs

/-- **The `ip->ref` route** ([OWN.63]): on a `racy` byte whose entry is value-safe, the audited
word, as of the entry, is in the registry's value set (`racyValAt`: `[1, 2^31)`, the guard
`ip->ref < 1` reads `≥ 1`) -- NO sync path claimed (NOT a refutation of `badSeg`, deviation 2). -/
theorem irefArm (σ : MState) (pa : PAddr) (t : Nat)
    (h : Xv6.AccessDiscipline.custAtP σ pa t = .racy ∧ Xv6.AccessDiscipline.racyValOkP σ pa t) :
    racyValAtP Xv6.AccessDiscipline.xv6Rsv σ.mem σ.lp t pa :=
  h.2

/-- On a `benignAt` byte that is no lock-layer, publication or page-table byte, the value fact. -/
theorem benignValue (σ : MState) (pa : PAddr) (t : Nat) (hb : benignAt σ pa t)
    (h1 : ∀ b, Xv6.AccessDiscipline.custAtP σ pa t ≠ .lockw b)
    (h2 : ∀ w, Xv6.AccessDiscipline.custAtP σ pa t ≠ .pub w)
    (h3 : Xv6.AccessDiscipline.custAtP σ pa t ≠ .pte) :
    racyValAtP Xv6.AccessDiscipline.xv6Rsv σ.mem σ.lp t pa := by
  rcases hb with ⟨b, hb⟩ | ⟨w, hw⟩ | hp | hr
  · exact absurd hb (h1 b)
  · exact absurd hw (h2 w)
  · exact absurd hp h3
  · exact irefArm σ pa t hr

/-! # 6. W11-D — the `chainHyps` arm: a cross-hart read chained by the export's sync path

The cross-hart kill INTO a process-stack read ([R23.1]'s third shape; [R24.s4]: A's `sched`
prologue pushes on `p->kstack`, A's scheduler `c->proc = 0; release(&p->lock)`, B
`acquire(&p->lock); c->proc = p; swtch`, B's `sched` epilogue loads A's words).  `csHyps`' side
condition `wprotAt` is FALSE for stack bytes (written WITHOUT `p->lock`), so `csHyps` cannot
classify the segment; `wprotAt` stays for the registered bytes.  The new arm `chainHyps` is
`csChained` generalised to `syncPath` hops: at graph level a hop chain collapses to its gmo
consequence — every write of the chain's terminal move is LATER in the log than the predecessor's
exit (`gwixLtGmo`: on writes, gmo IS the log order), and the reader orders it before its exit by
rule 5 (the acquire `amoswap.w.aq`) or rule 4 (the boot hop's `fence` after the `started` loop). -/

/-- The reader-side ordering point `Y` before the exit: an acquire read po-before-or-at the exit
(rule 5; the shape of `rrIn`), or a read covered by a fence before the exit (rule 4). -/
def syncInto (G : Gexec) (Y exit : Geid) : Prop :=
  (glblIs G Y lbIsR ∧ glblIs G Y lbAq ∧
      (Y = exit ∨ (WeakRvwmoGraph.gpo G Y exit ∧ gmem G exit))) ∨
    gfenceCovers G Y exit

/-- **THE `chainHyps` ARM**: the predecessor's exit `prev` is a write; a write `W` LATER in the
log (the sync path's terminal write: the reader's acquire, or the publication store it observed)
is gmo-before-or-at the reader's ordering point `Y`, which orders before the segment's exit. -/
def chainHyps (GD : Gdexec) (prev : Geid) (s : Seg) : Prop :=
  ∃ (W Y : Geid), prev ∈ gwrites GD.gdG ∧ W ∈ gwrites GD.gdG ∧
    gwix GD.gdG prev < gwix GD.gdG W ∧ (W = Y ∨ gmoLt GD.gdG W Y) ∧ syncInto GD.gdG Y s.sgExit

/-- The arm's gmo consequence, from rule 5 and rule 4 (each layer supplies its own). -/
theorem RvwmoXv6Adequacy.chainHypsGmoOf (G : Gexec) (prev : Geid) (s : Seg) (GD : Gdexec)
    (hG : GD.gdG = G) (hwf : gwf G)
    (h5 : ∀ a x, WeakRvwmoGraph.gpo G a x → glblIs G a lbIsR → glblIs G a lbAq → gmem G x →
      gmoLt G a x)
    (h4 : ∀ x y, gfenceCovers G x y → gmoLt G x y) :
    chainHyps GD prev s → gmoLt G prev s.sgExit := by
  subst hG
  rintro ⟨W, Y, hp, hw, hlt, hWY, hsi⟩
  have h1 : gmoLt GD.gdG prev W := gwixLtGmo GD.gdG prev W hwf hp hw hlt
  have h2 : gmoLt GD.gdG prev Y := by
    rcases hWY with rfl | h
    · exact h1
    · exact gmoLtTrans _ _ _ _ h1 h
  rcases hsi with ⟨hr, haq, rfl | ⟨hpo, hm⟩⟩ | hf
  · exact h2
  · exact gmoLtTrans _ _ _ _ h2 (h5 Y s.sgExit hpo hr haq hm)
  · exact gmoLtTrans _ _ _ _ h2 (h4 Y s.sgExit hf)

/-- **The arm is a `CSchained` certificate over cat**, at any cross order. -/
theorem chainHypsCertC (GD : Gdexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (prev : Geid) (s : Seg) :
    CatLin.rvwmoCatAD GD ad → chainHyps GD prev s → CatLin.CertC GD.gdG X prev s :=
  fun hc h => .CSchained (RvwmoXv6Adequacy.chainHypsGmoOf GD.gdG prev s GD rfl hc.1
    (fun a x => CatLin.acqGmoAfterC GD.gdG a x hc.2.1)
    (fun x y => CatLin.fenceGmoAfterC GD.gdG x y hc.2.1) h)

/-- …and over RVWMO⁻ (`Cert`). -/
theorem chainHypsCert (GD : Gdexec) (prev : Geid) (s : Seg) :
    rvwmoMinusDepsConsistent GD → chainHyps GD prev s → Cert GD.gdG prev s :=
  fun hc h => .CSchained (RvwmoXv6Adequacy.chainHypsGmoOf GD.gdG prev s GD rfl hc.1.1
    (fun a x => acqGmoAfter GD.gdG a x hc.1.2.1)
    (fun x y => fenceGmoAfter GD.gdG x y hc.1.2.1) h)

/-! ## 6.1 The claims with the new arm -/

/-- **The LOG-LEVEL L2′ claim with the `chainHyps` arm** (RVWMO⁻): `l2ClaimAtB` plus
`chainHyps`. -/
def l2ClaimAtD (GD : Gdexec) (P : Int → Int → Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    rvwmoMinusDepsConsistent GD →
    logOf GD.gdG log →
    protReg P log →
    ss ≠ [] → rawChain GD z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → gcross GD.gdG prev s.sgEntry → segRun GD s →
      segPin GD s ∨ csHyps GD P log prev s ∨ chainHyps GD prev s ∨ badSeg GD log prev s

/-- `l2ClaimAtB` implies `l2ClaimAtD` (the new arm only widens the claim). -/
theorem l2ClaimAtDOfB (GD : Gdexec) (P : Int → Int → Prop) : l2ClaimAtB GD P → l2ClaimAtD GD P :=
  fun h log z ss hc hl hp hne hch prev s hs hx hr =>
    (h log z ss hc hl hp hne hch prev s hs hx hr).elim .inl
      (fun h' => .inr (h'.elim .inl (fun hb => .inr (.inr hb))))

theorem rawChainChainD (GD : Gdexec) (P : Int → Int → Prop) (log : List Wmsg) (ss : List Seg) :
    rvwmoMinusDepsConsistent GD → logOf GD.gdG log → protReg P log →
    (∀ prev s, s ∈ ss → gcross GD.gdG prev s.sgEntry → segRun GD s →
       segPin GD s ∨ csHyps GD P log prev s ∨ chainHyps GD prev s ∨ badSeg GD log prev s) →
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
    rcases hcl x s hs hx hrun with hp | hc | hch | hb
    · exact segPinCert GD x s hcons hx hp
    · exact csHypsCert GD P log x s hcons hlog hpr hc hx
    · exact chainHypsCert GD x s hcons hch
    · exact absurd hb (hnb x s hs hx)

theorem cycleKillD (GD : Gdexec) (P : Int → Int → Prop) (log : List Wmsg) (z : Geid)
    (ss : List Seg) :
    rvwmoMinusDepsConsistent GD → logOf GD.gdG log → protReg P log →
    l2ClaimAtD GD P → ss ≠ [] → rawChain GD z z ss →
    (∀ prev s, s ∈ ss → gcross GD.gdG prev s.sgEntry → ¬ badSeg GD log prev s) → False := by
  intro hcons hlog hpr hcl hne hch hnb
  exact cycleKillArms GD.gdG z ss hcons.1 hne
    (rawChainChainD GD P log ss hcons hlog hpr (hcl log z ss hcons hlog hpr hne hch) hnb z z ss
      (fun _ h => h) hch)

/-- **The cat claim with the new arm** (`CatLin.l2ClaimAtC`'s text, `chainHyps` added, `badSeg`
for the run-level `Bad`). -/
def l2ClaimAtCD (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop) : Prop :=
  ∀ (log : List Wmsg) (z : Geid) (ss : List Seg),
    CatLin.rvwmoCatAD GD ad →
    logOf GD.gdG log →
    protReg P log →
    ss ≠ [] → CatLin.rawChainC GD (CatLin.gcrossE GD.gdG) z z ss →
    ∀ (prev : Geid) (s : Seg),
      s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → CatLin.segRunC GD s →
      CatLin.segPinC GD ad s ∨ csHyps GD P log prev s ∨ chainHyps GD prev s ∨
        badSeg GD log prev s

theorem rawChainChainCD (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop)
    (log : List Wmsg) (ss : List Seg) :
    CatLin.rvwmoCatAD GD ad → logOf GD.gdG log → protReg P log →
    (∀ prev s, s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → CatLin.segRunC GD s →
       CatLin.segPinC GD ad s ∨ csHyps GD P log prev s ∨ chainHyps GD prev s ∨
         badSeg GD log prev s) →
    (∀ prev s, s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → ¬ badSeg GD log prev s) →
    ∀ (x y : Geid) (ss' : List Seg),
      ss' ⊆ ss → CatLin.rawChainC GD (CatLin.gcrossE GD.gdG) x y ss' →
      CatLin.chainC GD.gdG (CatLin.gcrossE GD.gdG) x y ss' := by
  intro hc hlog hpr hcl hnb x y ss'
  have hX : ∀ x y, CatLin.gcrossE GD.gdG x y → gmoLt GD.gdG x y :=
    fun x y => CatLin.gcrossEGmo GD.gdG x y hc.1 hc.2.2.1
  induction ss' generalizing x with
  | nil => intro _ hch; exact hch
  | cons s ss' ih =>
    intro hsub hch
    obtain ⟨hx, hrun, hrest⟩ := hch
    have hs : s ∈ ss := hsub (by simp)
    have hsub' : ss' ⊆ ss := fun t ht => hsub (List.mem_cons_of_mem s ht)
    show CatLin.CertC GD.gdG (CatLin.gcrossE GD.gdG) x s ∧
      CatLin.chainC GD.gdG (CatLin.gcrossE GD.gdG) s.sgExit y ss'
    refine ⟨?_, ih _ hsub' hrest⟩
    rcases hcl x s hs hx hrun with hp | hcs | hch | hb
    · exact CatLin.segPinCCert GD ad _ x s hc hx hp
    · exact CatLin.csHypsCertC GD ad _ P log x s hc hX hlog hpr hcs hx
    · exact chainHypsCertC GD ad _ x s hc hch
    · exact absurd hb (hnb x s hs hx)

theorem cycleKillCD (GD : Gdexec) (ad : List (Geid × Geid)) (P : Int → Int → Prop)
    (log : List Wmsg) (z : Geid) (ss : List Seg) :
    CatLin.rvwmoCatAD GD ad → logOf GD.gdG log → protReg P log →
    l2ClaimAtCD GD ad P → ss ≠ [] → CatLin.rawChainC GD (CatLin.gcrossE GD.gdG) z z ss →
    (∀ prev s, s ∈ ss → CatLin.gcrossE GD.gdG prev s.sgEntry → ¬ badSeg GD log prev s) →
    False := by
  intro hc hlog hpr hcl hne hch hnb
  exact CatLin.cycleKillArmsC GD.gdG z ss hc.1 hc.2.2.1 hne
    (rawChainChainCD GD ad P log ss hc hlog hpr (hcl log z ss hc hlog hpr hne hch) hnb z z ss
      (fun _ h => h) hch)

/-! ## 6.2 Hop chains through `R`: the timestamps rise, the entries are graph writes -/

/-- `R`'s histories are strictly descending in the timestamp (latest first). -/
theorem RvwmoXv6Adequacy.histOfDesc (img : Image) (log : List Wmsg) (a : Int) :
    (TsoOfPf.histOf img log a).Pairwise (fun e e' => e'.t < e.t) := by
  unfold TsoOfPf.histOf
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_reverse, List.pairwise_filterMap]
    refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro i i' hii' b hb b' hb'
    simp only [Option.map_eq_some_iff] at hb hb'
    obtain ⟨_, -, rfl⟩ := hb
    obtain ⟨_, -, rfl⟩ := hb'
    simp only
    omega
  · cases img a <;> simp
  · intro e he e' he'
    rw [List.mem_reverse, List.mem_filterMap] at he
    obtain ⟨i, -, hi⟩ := he
    simp only [Option.map_eq_some_iff] at hi
    obtain ⟨_, -, rfl⟩ := hi
    cases himg : img a with
    | none => simp [himg] at he'
    | some v =>
      simp only [himg, Option.map_some, Option.toList_some, List.mem_singleton] at he'
      subst he'
      simp

/-- Consecutive entries of a descending history. -/
theorem RvwmoXv6Adequacy.descConsLt {H H1 H2 : Hist} {x y : HEnt}
    (hd : H.Pairwise (fun e e' => e'.t < e.t)) (hH : H = H1 ++ x :: y :: H2) : y.t < x.t := by
  subst hH
  rw [List.pairwise_append] at hd
  have := hd.2.1
  rw [List.pairwise_cons] at this
  exact this.1 y (by simp)

/-- A hop's acquire is LATER than its release (`R`'s histories descend). -/
theorem RvwmoXv6Adequacy.syncHopLt {m : FlatMem} {img : Image} {log : List Wmsg} {b : PAddr}
    {A : CPU} {r : Nat} {B : CPU} {a : Nat} (hr : rhist m img log) (h : syncHop m b A r B a) :
    r < a := by
  obtain ⟨H1, H2, e0, va, hb, -⟩ := h
  have hH := RvwmoXv6Adequacy.rhistGet hr hb
  exact RvwmoXv6Adequacy.descConsLt (x := ⟨a, hartAgent B, va⟩) (y := ⟨r, hartAgent A, 0⟩)
    (hH ▸ RvwmoXv6Adequacy.histOfDesc img log (paZ b)) rfl

/-- A hop's acquire entry is in the hop byte's history. -/
theorem RvwmoXv6Adequacy.syncHopAcq {m : FlatMem} {b : PAddr} {A : CPU} {r : Nat} {B : CPU}
    {a : Nat} (h : syncHop m b A r B a) :
    ∃ H va, m[b]? = some H ∧ (⟨a, hartAgent B, va⟩ : HEnt) ∈ H := by
  obtain ⟨H1, H2, e0, va, hb, -⟩ := h
  exact ⟨_, va, hb, by simp⟩

/-- **A hop chain's span through `R`**: the author's entries at or below `t` precede the chain's
FIRST release (the author's, at `r1 > t`), which precedes the LAST acquire `a` (the reader's). -/
theorem RvwmoXv6Adequacy.hopChainSpan {m : FlatMem} {img : Image} {log : List Wmsg}
    {isLk : PAddr → Nat → Prop} {A : CPU} {t : Nat} {B : CPU} {a : Nat}
    (hr : rhist m img log) (h : hopChain m isLk A t B a) :
    (∃ (b1 : PAddr) (r1 : Nat) (C1 : CPU) (a1 : Nat), isLk b1 a1 ∧ syncHop m b1 A r1 C1 a1 ∧
        t < r1 ∧ r1 < a) ∧
      ∃ (b : PAddr) (C : CPU) (r : Nat), isLk b a ∧ syncHop m b C r B a := by
  induction h with
  | base b hb hh ht =>
    exact ⟨⟨b, _, _, _, hb, hh, ht, RvwmoXv6Adequacy.syncHopLt hr hh⟩, b, _, _, hb, hh⟩
  | step b _ hb hh ha ih =>
    obtain ⟨⟨b1, r1, C1, a1, hb1, hh1, ht1, hr1⟩, -⟩ := ih
    exact ⟨⟨b1, r1, C1, a1, hb1, hh1, ht1,
      Nat.lt_trans hr1 (Nat.lt_trans ha (RvwmoXv6Adequacy.syncHopLt hr hh))⟩, b, _, _, hb, hh⟩

/-- **A history entry is a graph write** (through `R-hist` and the log identification): its
timestamp is the write's index, its author the write's hart. -/
theorem RvwmoXv6Adequacy.entGraph {c : Wpcfg Pexv6 Efab} {st : List (Nat × Wlabel)} {σ : MState}
    {log : List Wmsg} {G : Gexec} {b : PAddr} {H : Hist} {e : HEnt}
    (hR : rmem c st σ) (hpre : c.pcLog <+: log) (hwf : gwf G) (hlog : logOf G log)
    (hb : σ.mem[b]? = some H) (he : e ∈ H) (ht : e.t ≠ 0) :
    ∃ W, W ∈ gwrites G ∧ gwix G W = e.t ∧ W.1 = e.tid ∧ e.t ≤ c.pcLog.length := by
  have hr := hR.2.2.1
  rw [RvwmoXv6Adequacy.rhistGet hr hb] at he
  rcases RvwmoXv6Adequacy.histOfMemInv _ _ _ _ he with h0 | ⟨mq, hq, -, htq⟩
  · exact absurd h0 ht
  · have hlen := (List.getElem?_eq_some_iff.1 hq).1
    have hq' : log[e.t - 1]? = some mq := by
      obtain ⟨rest, hrest⟩ := hpre
      rw [← hrest]; exact lookup_app_l_Some hq
    obtain ⟨W, -, hm, hix, hmem⟩ := logOfLookup G log (e.t - 1) mq hwf hlog hq'
    refine ⟨W, hmem, by rw [hix]; omega, ?_, by omega⟩
    rw [htq, gmsgTid G W mq hm]
    rfl

/-! ## 6.3 The realization interface and THE DERIVATION -/

/-- **The sync path's terminal move, realized** (an INTERFACE, as `segRealized`; W11-F's
composition supplies it from the certified run — in-order realization of hart `j` at the read's
post-state `σ`, and xv6's text: a hop byte's nonzero word store is `acquire`'s `amoswap.w.aq`, the
boot harts' `while(started == 0);` is followed by `__sync_synchronize()`):
(a) every graph write of the reader `j` at a hop ACQUIRE entry at or below `σ.top` is an acquire
read po-before-or-at the segment's entry; (b) `j`'s observation of a publication store at `r`
(floor `≥ r`) is a read `Y` of `j`, gmo-after-or-at a write at or after `r`, fence-covered before
the segment's exit. -/
def syncRealized (GD : Gdexec) (σ : MState) (j : CPU) (s : Seg) : Prop :=
  (∀ (W : Geid) (b : PAddr) (C : CPU) (r : Nat), W ∈ gwrites GD.gdG → W.1 = hartAgent j →
      gwix GD.gdG W ≤ σ.top → Xv6.AccessDiscipline.hopByteAt σ b (gwix GD.gdG W) →
      syncHop σ.mem b C r j (gwix GD.gdG W) →
      glblIs GD.gdG W lbIsR ∧ glblIs GD.gdG W lbAq ∧
        (W = s.sgEntry ∨ WeakRvwmoGraph.gpo GD.gdG W s.sgEntry)) ∧
  (∀ (f : PAddr) (w : CPU) (r : Nat) (v : BitVec 8) (H : Hist), j ≠ w →
      (Xv6.AccessDiscipline.xv6Env σ).isPub f w → σ.mem[f]? = some H →
      (⟨r, hartAgent w, v⟩ : HEnt) ∈ H → r ≤ (σ.hr j).coh f →
      ∃ (W Y : Geid), W ∈ gwrites GD.gdG ∧ r ≤ gwix GD.gdG W ∧ (W = Y ∨ gmoLt GD.gdG W Y) ∧
        gfenceCovers GD.gdG Y s.sgExit)

/-- **THE DERIVATION** (plan §C W11-D): at a realized read (`readAt`, W11-C's interface) of a
FOREIGN hart's message off the `benignAt` bytes — a process-stack byte is one (custody `free`) —
`chainOkAt`'s sync path, through `R`, IS the `chainHyps` arm.  NO owner-uniqueness premise: the
hop is the export's `syncPath`, which `chainOkAt` gives for EVERY foreign entry off the exempt
classes, whoever owns the byte. -/
theorem chainHypsOfSyncPath (GD : Gdexec) (log : List Wmsg) (c : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg)
    (i : Nat) (prev : Geid) (s : Seg)
    (hrd : readAt log c st σ j pa p m) (hi : m.wmTid = some i) (hiN : i < NCPU)
    (hij : i ≠ hartAgent j) (hnb : ¬ benignAt σ pa (p + 1))
    (hwf : gwf GD.gdG) (hlog : logOf GD.gdG log) (hprev : gwriteAt GD.gdG (p + 1) = some prev)
    (hrun : s.sgEntry = s.sgExit ∨ WeakRvwmoGraph.gpo GD.gdG s.sgEntry s.sgExit)
    (hmx : gmem GD.gdG s.sgExit) (hre : syncRealized GD σ j s) :
    chainHyps GD prev s := by
  obtain ⟨hR, hD, -, hpre, hp, hv, hram, hcoh, heg⟩ := hrd
  have hm := PfStepTsoMem.memEager c st σ hR heg
  have hlo := RvwmoXv6Adequacy.landedOnlyEager σ.mem σ.lp hm
  have hlo' : (Xv6.AccessDiscipline.xv6Env σ).lm = σ.mem := hlo
  have hr := hR.2.2.1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv
  obtain ⟨hpw, hpix⟩ := gwriteAtInv GD.gdG (p + 1) prev hwf.1 hprev
  have hH := hr.1 pa hram
  have he : (⟨p + 1, i, v⟩ : HEnt) ∈ TsoOfPf.histOf c.pcImg c.pcLog (paZ pa) := by
    have := RvwmoXv6Adequacy.histOfMem c.pcImg c.pcLog (paZ pa) p m v hp hv
    rwa [hi] at this
  have h1 : ∀ b, Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .lockw b :=
    fun b hb' => hnb (.inl ⟨b, hb'⟩)
  have h2 : ∀ w, Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .pub w :=
    fun w hw => hnb (.inr (.inl ⟨w, hw⟩))
  have h3 : Xv6.AccessDiscipline.custAtP σ pa (p + 1) ≠ .pte := fun h => hnb (.inr (.inr (.inl h)))
  rw [← hcoh] at h1 h2 h3
  rcases hD.1 j pa _ ⟨p + 1, i, v⟩ hH he (by simp) (by rw [hm pa _ hH _ he, hcoh]) hiN hij h1 h2 h3
    with hs | hrc
  · rcases hs with ⟨a, ha, hc⟩ | ⟨f, w, r, v', H', hne, hpub, hf, hew, hrle, harm⟩
    · rw [hlo] at hc
      -- the hop chain: the reader's own acquire is the terminal write
      obtain ⟨⟨_, _, _, _, _, _, ht1, h1a⟩, b, C, r, hbl, hsh⟩ :=
        RvwmoXv6Adequacy.hopChainSpan hr hc
      simp only at ht1
      obtain ⟨Hb, va, hHb, hmemA⟩ := RvwmoXv6Adequacy.syncHopAcq hsh
      obtain ⟨W, hW, hix, hW1, -⟩ :=
        RvwmoXv6Adequacy.entGraph hR hpre hwf hlog hHb hmemA (by simp only; omega)
      simp only at hix hW1
      obtain ⟨hWR, hWaq, hWe⟩ := hre.1 W b C r hW hW1 (by rw [hix]; omega)
        (by rw [hix]; exact hbl) (by rw [hix]; exact hsh)
      refine ⟨W, W, hpw, hW, by rw [hix, hpix]; omega, .inl rfl, .inl ⟨hWR, hWaq, ?_⟩⟩
      rcases CatLin.CatReroute.poOrEq GD.gdG _ _ _ hWe hrun with heq | hpo
      · exact .inl heq
      · exact .inr ⟨hpo, hmx⟩
    · -- the boot hop: the observed publication store is the terminal write
      have hlt : p + 1 < r := by
        rcases harm with ⟨-, h⟩ | ⟨a, ha, hc⟩
        · exact h
        · rw [hlo'] at hc
          obtain ⟨⟨_, _, _, _, _, _, ht1, h1a⟩, -⟩ :=
            RvwmoXv6Adequacy.hopChainSpan (m := σ.mem) hr hc
          simp only at ht1
          omega
      have hf' : σ.mem[f]? = some H' := by rw [← hlo']; exact hf
      have hrle' : r ≤ (σ.hr j).coh f := by
        obtain ⟨q, hq, hle⟩ := hrle
        have hlr : σ.lp r = some r := hm f H' hf' _ hew
        have hlr' : (Xv6.AccessDiscipline.xv6Env σ).lp r = some r := hlr
        rw [hlr'] at hq
        cases hq
        exact hle
      obtain ⟨W, Y, hW, hrW, hWY, hfc⟩ := hre.2 f w r v' H' hne hpub hf' hew hrle'
      exact ⟨W, Y, hpw, hW, by rw [hpix]; omega, hWY, .inr hfc⟩
  · rw [hcoh] at hrc
    exact absurd (.inr (.inr (.inr hrc))) hnb

/-- **…as the certificate** (cat, any cross order): the cross-hart kill into the read. -/
theorem chainHypsCertOfRealized (GD : Gdexec) (ad : List (Geid × Geid))
    (X : Geid → Geid → Prop) (log : List Wmsg) (c : Wpcfg Pexv6 Efab)
    (st : List (Nat × Wlabel)) (σ : MState) (j : CPU) (pa : PAddr) (p : Nat) (m : Wmsg)
    (i : Nat) (prev : Geid) (s : Seg)
    (hc : CatLin.rvwmoCatAD GD ad)
    (hrd : readAt log c st σ j pa p m) (hi : m.wmTid = some i) (hiN : i < NCPU)
    (hij : i ≠ hartAgent j) (hnb : ¬ benignAt σ pa (p + 1))
    (hlog : logOf GD.gdG log) (hprev : gwriteAt GD.gdG (p + 1) = some prev)
    (hrun : CatLin.segRunC GD s) (hmx : gmem GD.gdG s.sgExit) (hre : syncRealized GD σ j s) :
    CatLin.CertC GD.gdG X prev s :=
  chainHypsCertC GD ad X prev s hc
    (chainHypsOfSyncPath GD log c st σ j pa p m i prev s hrd hi hiN hij hnb hc.1 hlog hprev
      (CatLin.CatReroute.runPo GD ad _ _ hc hrun) hmx hre)

/-- **THE HAND-OFF HOP `rrIn` from a hop chain** (W11-A's deviation: the re-route's hop premise,
derived): the chain's FIRST release (the author `A`'s, after its entries at or below `t`) and its
LAST acquire (the reader `j`'s) are graph writes in log order, so `REL <gmo ACQ`, and the realized
acquire makes `rrIn REL ACQ` hold into the reader's segment. -/
theorem rrInOfHopChain (GD : Gdexec) (X : Geid → Geid → Prop) (log : List Wmsg)
    (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (A j : CPU) (t a : Nat)
    (s : Seg) (hR : rmem c st σ) (hpre : c.pcLog <+: log) (hwf : gwf GD.gdG)
    (hlog : logOf GD.gdG log)
    (hc : hopChain σ.mem (Xv6.AccessDiscipline.hopByteAt σ) A t j a) (ha : a ≤ σ.top)
    (hrun : s.sgEntry = s.sgExit ∨ WeakRvwmoGraph.gpo GD.gdG s.sgEntry s.sgExit)
    (hmx : gmem GD.gdG s.sgExit) (hre : syncRealized GD σ j s) :
    ∃ (REL ACQ : Geid), REL ∈ gwrites GD.gdG ∧ REL.1 = hartAgent A ∧ t < gwix GD.gdG REL ∧
      gwix GD.gdG REL < gwix GD.gdG ACQ ∧ CatLin.rrIn GD.gdG X REL ACQ s.sgExit := by
  have hr := hR.2.2.1
  obtain ⟨⟨b1, r1, C1, a1, -, hsh1, ht1, h1a⟩, b, C, r, hbl, hsh⟩ :=
    RvwmoXv6Adequacy.hopChainSpan hr hc
  obtain ⟨H1, hH1, hrel1⟩ := RvwmoXv6Adequacy.syncHopRel hsh1
  obtain ⟨REL, hRELw, hRix, hREL1, -⟩ :=
    RvwmoXv6Adequacy.entGraph hR hpre hwf hlog hH1 hrel1 (by simp only; omega)
  obtain ⟨Hb, va, hHb, hmemA⟩ := RvwmoXv6Adequacy.syncHopAcq hsh
  obtain ⟨W, hW, hix, hW1, -⟩ :=
    RvwmoXv6Adequacy.entGraph hR hpre hwf hlog hHb hmemA (by simp only; omega)
  simp only at hix hW1 hRix hREL1
  obtain ⟨hWR, hWaq, hWe⟩ := hre.1 W b C r hW hW1 (by rw [hix]; exact ha)
    (by rw [hix]; exact hbl) (by rw [hix]; exact hsh)
  refine ⟨REL, W, hRELw, hREL1, by rw [hRix]; exact ht1, by rw [hRix, hix]; exact h1a,
    .inr (gwixLtGmo GD.gdG REL W hwf hRELw hW (by rw [hRix, hix]; exact h1a)), hWR, hWaq, ?_⟩
  rcases CatLin.CatReroute.poOrEq GD.gdG _ _ _ hWe hrun with heq | hpo
  · exact .inl heq
  · exact .inr ⟨hpo, hmx⟩

/-! ## 6.4 Non-vacuity: the migration split's reader segment is `chainHyps`

`CatLin.rrMig` (`CatReroute.lean` §4.1, computed riscv.cat-consistent): hart 0 spills
`E = sb [8]` then `fence rw,w; REL`; hart 1 `ACQ = amoswap.aq [4]` (reads `REL`), `R = lb [8]`
(reads `E`, cross-hart), `E' = sb [9]`.  The segment `(R, E')` entered from `E` is `chainHyps` —
`ACQ` is later in the log than `E` and orders before `E'` by `.aq` — hence certified. -/

theorem rrMigChainHyps : chainHyps CatLin.rrMig (0, 1) ⟨1, (1, 1), (1, 2)⟩ :=
  ⟨(1, 0), (1, 0), by decide +kernel, by decide +kernel, by decide +kernel, .inl rfl,
    .inl ⟨(glblBSpec _ _ _).1 (by decide +kernel), (glblBSpec _ _ _).1 (by decide +kernel),
      .inr ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
        ⟨Lbl.LStore false 9 [1#8] .WCplain, by decide +kernel, rfl⟩⟩⟩⟩

theorem rrMigChainHypsCert :
    CatLin.CertC CatLin.rrMig.gdG (CatLin.gcrossE CatLin.rrMig.gdG) (0, 1) ⟨1, (1, 1), (1, 2)⟩ :=
  chainHypsCertC _ _ _ _ _ CatLin.rrMigCatAD rrMigChainHyps

end Weak
