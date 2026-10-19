/-
Weak: **W13 (K-cat′) — `ioSegPinnedC` under the NAMED per-step condition `ioStepCloses`**
(plan `notes/weak-allocproc-plan.md` rev 48, §C top STAGE 2 ROADMAP "(K-cat′)"; Q-KCAT RULED (a)
[OWN.61]).  Lean-only, no Rocq twin.  §§1–2 below are the predecessor's (K-cat) STOP finding,
KEPT: `kcatCex` is the permanent counter-model.

  §3  THE NAMED CONDITION.  `ioStepCloses GF ad x u v` := `ioStepClosesGmo ∨ ioStepClosesFwd`,
      the closing arms of a same-row step `u → v` after the I/O event `x`.  GMO arms (put `v`
      gmo-after `x`): (1) `v` a RAM write — (R2); (2) `v` an I/O event — (R3); (3) a cat-ordered
      step (`CatLin.pinStep`: rules 1–5, 7, deps, rule 12 over `ad`) out of `x` or out of a
      gmo-after-`x` event; (4) a `pw` fence (`gfenceBetween u v _ true _ _` with the successor bit
      covering `v`) out of a read forwarded from a write gmo-after `x`.  FORWARDING arms (keep `v`
      in `afterIo`): (5) `grfi u v`; (6) `gpoloc` R→R ON the forwarded byte — `v` reads a byte that
      `u` reads from a same-hart write gmo-after `x`; (7) `gpoloc` W→R on a byte `u` writes.
      `ioStepC` = `rsameC ∧ ioStepCloses`; `ioExitCloses` (the exit has no own-hart rf source, or
      its last step is a GMO arm).
  §4  THE CLOSURE `rsameCAfterIo`: `afterIo x u` (or `u = x`) → `rsameC u v` → `ioStepCloses` →
      `afterIo x v`.  The per-byte core is `WeakRvwmoKillIOC.fwdByte` (load value per byte: the
      source of `v`'s byte is the after-`x` write or coherence-after it — no rule-2 order used).
  §5  `ioSegAfterIoC` (entry gmo-before `x`, every later event in `afterIo`), **`ioSegPinnedC`**
      (`entry <gmo exit` under `ioStepCloses` on every step after `x` and `ioExitCloses`), and
      `ioSegCertC` (the `CertC.Pinned` certificate at any cross order `X`).
  §6  NON-VACUITY.  `kcatCexNotCloses`: the counterexample's step `u → v` is OUTSIDE the
      condition (for every `ad`) — the condition bites exactly where riscv.cat is silent.
      `kcatOk*`: a riscv.cat-consistent (tagged, computed), residue-satisfying graph that is NOT
      RVWMO⁻ (`kcatOkNotMinus`), on which `ioSegPinnedC` applies through arms (1), (5), (6), (1)
      (`kcatOkSegPinned`) and whose forwarded read is gmo-BEFORE `x` (`kcatOkFwdOnly`).
      `w13fIoStepCloses`: the `w13f` instance — every `rsameC` step of `w13fIo` meets the
      condition (row 0 has NO step after the UART store; row 1's is a write target).

**What is NOT covered here (W11's, [OWN.61]).**  A segment taking a step outside
`ioStepCloses` — a same-source same-address R→R `gpoloc` (ppo rule 2's `\ rsw` exemption) off the
forwarded byte or out of a gmo-after-`x` read, as in `kcatCex` — and a FORWARDED exit reached by a
forwarding arm (it may be gmo-before the entry; `ioExitCloses` fails) are certified through the
lock hand-offs of the access-discipline export (`chainOkAt`, the CS-chained route).

**Spec standing.**  FAITHFUL: the hypothesis is the cat chain's `CatLin.rvwmoCatAD` (implied by the
published tagged riscv.cat model) plus the trusted residue `ioResidueGmo`; RVWMO⁻'s same-address
R→R order is NOT assumed ([OWN.2]) — arm (6) is proved from the per-byte load-value axiom.
`ioStepCloses`/`ioExitCloses` are NAMED proof-device conditions, not trusted text.

**Name map (K-cat′).**  `ioStepClosesGmo`, `ioStepClosesFwd`, `ioStepCloses`, `ioStepC`,
`ioExitCloses`, `rsameCAfterIo`, `ioSegAfterIoC`, `ioSegPinnedC`, `ioSegCertC`,
`kcatCexNotCloses`, `kcatOkProg`, `kcatOkGmo`, `kcatOkT`, `kcatOk`, `kcatOkCatT`, `kcatOkCatAD`,
`kcatOkNotMinus`, `kcatOkResidue`, `kcatOkSegPinned`, `kcatOkFwdOnly`, `w13fIoStepCloses`;
Lean-only helpers `WeakRvwmoKillIOC.{gisWNotIo, gisWGlbl, gpoOfGmo, fwdByte, rsameCGpo, stepGmo,
stepFwd, kcatOkLbl, kcatOkGpow}`.

---- The predecessor's (K-cat) STOP finding (kept) ----

**W13 (K-cat) — STOP FINDING: the plan's refined cat invariant is NOT closed** (plan
`notes/weak-allocproc-plan.md` rev 45, §C top THIRD LAUNCH SET "W13 (K-cat)", §C W13 R5; review
R41 [R41.s3]).

Lean-only, no Rocq twin.  The plan asks for the cat twin of `ioSegPinned`
(`WeakRvwmoKillIO.lean` §7) on `CatLin.rsameC` with the refined invariant "after the I/O event
`x`, every event of the segment is gmo-after `x`, OR a read FORWARDED (`grfi`) from a write
gmo-after `x`" (`WeakRvwmoKillIOC.afterIo`), claimed closed under every `gpow`/`gppo`/deps/rfi
step EXCEPT a `PR∧SR∧¬PW` fence (side condition `WeakRvwmoKillIOC.noPrSrFenceInSeg`).

**That closure is FALSE under riscv.cat**, by a COMPUTED counterexample (§2), with NO fence at
all.  `CatLin.rsameC`'s `gppo` arm is RVWMO⁻'s ppo, whose `gpoloc` R→R same-byte arm riscv.cat
does NOT order (ppo rule 2 is `([R];po-loc-no-w;[R]) \ rsw` — same-source reads are exempt), and
`grfi` is a PER-BYTE relation (one forwarded byte makes the whole read "forwarded"):

    H0: (0,0) x  = MMIO store (UART IER)      H1: (1,0) w2 = sb 0 <- 1
        (0,1) w  = sb 1 <- 1                      (1,1) y  = MMIO store (UART IER)
        (0,2) u  = lh 0  (byte 0 = image, byte 1 FORWARDED from w)
        (0,3) v  = lb 0  (byte 0 = image — the SAME source as u's byte 0)
    gmo = [u; v; w2; y; x; w]

  * `kcatCexCatT`: the TAGGED model `rvwmoCatConsistentT` holds (computed) — so
    `kcatCexCatAD`: the cat chain's hypothesis `CatLin.rvwmoCatAD`; `kcatCexResidue`: the
    trusted residue's pre-[OWN.116] arms hold ((R1) `w2 <gmo y`, (R2) `x <gmo w`, nothing else);
    since [OWN.116] its (R2″) arm EXCLUDES the graph (`kcatCexExcluded`: `x` before the read `u`).
  * `kcatCexAfterIoU`: `u` satisfies the invariant (forwarded from `w`, po- and gmo-after `x`);
    `kcatCexStep`: `u → v` is an `rsameC` step (`gpoloc` on byte 0);
    `kcatCexNoFence`: the side condition holds (the row has no fence);
    **`kcatCexAfterIoV`: `v` FAILS the invariant** (gmo-BEFORE `x`, reads only the image).
  * `kcatCexRacyDIOCycle`: `racyDIO` is CYCLIC on this cat + residue graph
    (`x →gpow w →rfi u →gpoloc v →fr w2 →(R1) y →gmo|IO x`), and the segment
    `x → w → u → v` has its exit `v` gmo-before `x` — no `CertC` certificate exists for it, so
    the cat-side kill (`WeakRvwmoKillIO.cycleKillIOC` + certificates) cannot pin this segment
    from the I/O event under ANY side condition that only constrains fences.

The single-byte case of the plan's argument is sound (a `gpoloc` W→R / R→R step whose source
byte IS the forwarded byte keeps the read forwarded-from-after-`x` or coherence-after; see
`PROGRESS-W13W.md`), but the invariant as stated quantifies over whole reads, and the same-source
`gpoloc` R→R arm also breaks "gmo-after `x`" by itself when the shared byte is not a forwarded one.

**Spec standing.**  No trusted text: `afterIo`/`noPrSrFenceInSeg` are proof-device definitions,
the counterexample is a riscv.cat-consistent (tagged) graph that also satisfies the trusted
`ioResidueGmo`.  The RVWMO⁻ twin (`rsameNoReadEdge`, `ioSegPinnedMinus`) stays PROVED; it is
STRONGER than RVWMO exactly at the rule-2 same-source exemption and at forwarding.

**Name map.**  Lean-only: `WeakRvwmoKillIOC.afterIo`, `WeakRvwmoKillIOC.noPrSrFenceInSeg`,
`kcatCexProg`, `kcatCexGmo`, `kcatCexT`, `kcatCex`, `kcatCexCatT`, `kcatCexCatAD`,
`kcatCexResidue`, `kcatCexAfterIoU`, `kcatCexStep`, `kcatCexNoFence`, `kcatCexAfterIoV`,
`kcatCexRacyDIOCycle`.  NOT delivered (the plan's `ioSegPinnedC`, `rsameCAfterIo`): FALSE as
specified, see `PROGRESS-W13W.md` for the options — superseded by (K-cat′) §§3–6 above.
-/
import Weak.WeakRvwmoKillIO

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Lbl

/-! # 1. The plan's invariant and side condition -/

/-- The plan's refined invariant (§C W13 (K-cat)): `v` is po-after the I/O event `x` and is
gmo-after `x`, or a read forwarded (`grfi`) from a write po- and gmo-after `x`. -/
def WeakRvwmoKillIOC.afterIo (GF : Gfexec) (x v : Geid) : Prop :=
  WeakRvwmoGraph.gpo GF.gfGd.gdG x v ∧
    (gmoLt GF.gfGd.gdG x v ∨
      ∃ w, CatLin.grfi GF.gfGd.gdG w v ∧ WeakRvwmoGraph.gpo GF.gfGd.gdG x w ∧
        gmoLt GF.gfGd.gdG x w)

/-- The plan's named side condition: no `PR∧SR∧¬PW` fence label in `x`'s hart row strictly
between `x` and the exit `e`. -/
def WeakRvwmoKillIOC.noPrSrFenceInSeg (G : Gexec) (x e : Geid) : Prop :=
  ∀ k sw, x.2 < k → k < e.2 → gxLbl G (x.1, k) ≠ some (LFence true false true sw)

/-! # 2. The counterexample -/

def kcatCexProg : List (List Lbl) :=
  [[LIo .wr 0x10000001 [0], LStore false 1 [b1] .WCplain, LLoad false 0 [0, 2] [b0, b1],
    LLoad false 0 [0] [b0]],
   [LStore false 0 [b1] .WCplain, LIo .wr 0x10000001 [0]]]

def kcatCexGmo : List Geid := [(0, 2), (0, 3), (1, 0), (1, 1), (0, 0), (0, 1)]

/-- The graph, TAGGED (no dependencies). -/
def kcatCexT : GdexecT := mkgt kcatCexProg kcatCexGmo []

/-- The fabric bundle: the chain's graph, EMPTY fabric list. -/
def kcatCex : Gfexec := ⟨forget kcatCexT, []⟩

/-- The published quantifier's model holds (computed). -/
theorem kcatCexCatT : rvwmoCatConsistentT kcatCexT :=
  catTConsistentBSound _ (by decide +kernel)

/-- … hence the cat chain's hypothesis. -/
theorem kcatCexCatAD : CatLin.rvwmoCatAD kcatCex.gfGd (gtAd kcatCexT.gtG kcatCexT.gtDeps) :=
  CatLin.catADOfCatT kcatCexT kcatCexCatT

theorem WeakRvwmoKillIOC.kcatCexLbl (e : Geid) :
    (gxLbl kcatCex.gfGd.gdG e).isSome = true →
      e = (0, 0) ∨ e = (0, 1) ∨ e = (0, 2) ∨ e = (0, 3) ∨ e = (1, 0) ∨ e = (1, 1) := by
  obtain ⟨i, k⟩ := e
  intro h
  rcases i with _ | _ | i <;> rcases k with _ | _ | _ | _ | k <;>
    simp [gxLbl, kcatCex, kcatCexT, mkgt, forget, kcatCexProg] at h ⊢

/-- The trusted residue's pre-[OWN.116] arms hold ((R1), (R2), (R2′), (R3)); since [OWN.116] the
residue also carries (R2″) and EXCLUDES this graph (`kcatCexExcluded`). -/
theorem kcatCexResidue : ∀ x y, ioResidue kcatCex x y →
    ¬ (WeakRvwmoGraph.gpo kcatCex.gfGd.gdG x y ∧ gisIo kcatCex.gfGd.gdG x = true ∧
      gisR kcatCex.gfGd.gdG y = true) → gmoLt kcatCex.gfGd.gdG x y := by
  intro x y hr hn6
  have hxy : (gxLbl kcatCex.gfGd.gdG x).isSome = true ∧
      (gxLbl kcatCex.gfGd.gdG y).isSome = true := by
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hx, hy, -⟩ | ⟨hx, hy, -⟩ | ⟨hp, -⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨GraphFabResidue.gisIoSome _ _ hx, GraphFabResidue.gisIoSome _ _ hy⟩
    · exact ⟨GraphFabResidue.gmemSome _ _ hx, GraphFabResidue.gmemSome _ _ hy⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
  rcases WeakRvwmoKillIOC.kcatCexLbl x hxy.1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases WeakRvwmoKillIOC.kcatCexLbl y hxy.2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | (show gmoLt kcatCex.gfGd.gdG _ _; exact (gmoLtBSpec _ _ _).1 (by decide +kernel))
  | (exfalso
     rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp⟩ |
       ⟨hx, hy, hb⟩ | ⟨hp, hx, hy⟩
     all_goals first
       | exact hn6 ⟨hp, hx, hy⟩
       | exact absurd hp.2.1 (by decide)
       | exact absurd hp.1 (by decide)
       | exact absurd hx (by decide +kernel)
       | exact absurd hy (by decide +kernel)
       | exact absurd hn (by decide)
       | (obtain ⟨i, j, hi, -⟩ := hb; simp [kcatCex] at hi))

/-- **SINCE [OWN.116] THE TRUSTED RESIDUE EXCLUDES THE COUNTER-MODEL**: (R2″) orders the UART store
`x = (0,0)` before the po-later read `u = (0,2)`, which this gmo puts first. -/
theorem kcatCexExcluded : ¬ ioResidueGmo kcatCex := by
  intro h
  have := h (0, 0) (0, 2) (.inr (.inr (.inr (.inr (.inr ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
    by decide +kernel, by decide +kernel⟩)))))
  exact absurd ((gmoLtBSpec _ _ _).2 this) (by decide +kernel)

/-- `u = (0,2)` satisfies the invariant: its byte 1 is forwarded from `w = (0,1)`, po- and
gmo-after `x = (0,0)`. -/
theorem kcatCexAfterIoU : WeakRvwmoKillIOC.afterIo kcatCex (0, 0) (0, 2) :=
  ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
    Or.inr ⟨(0, 1), ⟨(grfBSpec _ _ _).1 (by decide +kernel), rfl⟩,
      (gpoBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩⟩

/-- `u → v` is a same-row step of the cat chain (`gppo`'s `gpoloc` arm, byte 0). -/
theorem kcatCexStep : CatLin.rsameC kcatCex.gfGd (0, 2) (0, 3) :=
  Or.inr (Or.inl (Or.inl ((gpolocBSpec _ _ _).1 (by decide +kernel))))

/-- The plan's side condition holds: the segment's row has no fence. -/
theorem kcatCexNoFence : WeakRvwmoKillIOC.noPrSrFenceInSeg kcatCex.gfGd.gdG (0, 0) (0, 3) := by
  intro k sw h1 h2
  have hk : k = 1 ∨ k = 2 := by simp at h1 h2; omega
  rcases hk with rfl | rfl <;> cases sw <;> decide +kernel

/-- **…and `v = (0,3)` FAILS the invariant**: it is gmo-BEFORE `x` and reads only the image
(no write is its `grf` source). -/
theorem kcatCexAfterIoV : ¬ WeakRvwmoKillIOC.afterIo kcatCex (0, 0) (0, 3) := by
  rintro ⟨-, hmo | ⟨w, ⟨⟨a, t, val, hrd, hat⟩, -⟩, -⟩⟩
  · exact absurd ((gmoLtBSpec _ _ _).2 hmo) (by decide +kernel)
  · obtain ⟨l, base, ts, vs, j, hl, hrd, hts, -⟩ := hrd
    simp [gxLbl, kcatCex, kcatCexT, mkgt, forget, kcatCexProg] at hl
    subst hl
    simp [lbRd] at hrd
    obtain ⟨-, rfl, -⟩ := hrd
    have ht : t = 0 := by
      rcases j with _ | j <;> simp at hts
      exact hts.symm
    subst ht
    simp [gwriteAt] at hat

/-- **`racyDIO` is CYCLIC on the cat + residue graph**: `x →gpow w →rfi u →gpoloc v →fr w2
→(R1) y →gmo|IO x`. -/
theorem kcatCexRacyDIOCycle : tc (racyDIO kcatCex) (0, 0) (0, 0) := by
  -- x → w: rule-14's own edge `gpow`
  have e1 : racyDIO kcatCex (0, 0) (0, 1) :=
    Or.inl (Or.inl (Or.inl ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
      GraphFabResidue.gisIoGmem _ _ (by decide +kernel), by decide +kernel⟩))
  -- w → u: rf (same hart: rfi)
  have e2 : racyDIO kcatCex (0, 1) (0, 2) :=
    Or.inl (Or.inl (Or.inr (Or.inl ((grfBSpec _ _ _).1 (by decide +kernel)))))
  -- u → v: ppo⁻ `gpoloc` (byte 0, same source)
  have e3 : racyDIO kcatCex (0, 2) (0, 3) :=
    Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((gpolocBSpec _ _ _).1 (by decide +kernel))))))))
  -- v → w2: fr (v reads the image at byte 0, w2 overwrites it)
  have e4 : racyDIO kcatCex (0, 3) (1, 0) :=
    Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ((gfrBSpec _ _ _).1 (by decide +kernel)))))))
  -- w2 → y: residue (R1)
  have e5 : racyDIO kcatCex (1, 0) (1, 1) :=
    Or.inr (Or.inl (Or.inl ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
      ⟨LStore false 0 [b1] .WCplain, by decide +kernel, rfl⟩, by decide +kernel,
      by decide +kernel⟩))
  -- y → x: gmo|IO
  have e6 : racyDIO kcatCex (1, 1) (0, 0) :=
    Or.inr (Or.inr (Or.inl ⟨by decide +kernel, by decide +kernel,
      (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩))
  exact tc_l e1 (tc_l e2 (tc_l e3 (tc_l e4 (tc_l e5 (tc_once e6)))))


/-! # 3. (K-cat′): the NAMED per-step condition `ioStepCloses` (Q-KCAT (a), [OWN.61])

Each arm below is a step `u → v` of the segment after the I/O event `x` that KEEPS the
invariant `afterIo`.  The GMO arms put `v` gmo-after `x` outright; the FORWARDING arms may leave
`v` only "forwarded from a write gmo-after `x`" (riscv.cat performs such a read early).  A step
outside every arm — `kcatCex`'s `u → v` (`kcatCexNotCloses`): a same-source R→R `gpoloc` off the
forwarded byte, or out of a gmo-after-`x` read, which riscv.cat's ppo rule 2 does NOT order
(`\ rsw`) — is W11's to certify (the CS-chained route, [OWN.61]). -/

/-- The GMO-closing arms. -/
def ioStepClosesGmo (GF : Gfexec) (ad : List (Geid × Geid)) (x u v : Geid) : Prop :=
  -- (1) a RAM write target: after `x` by (R2)
  gisW GF.gfGd.gdG v = true ∨
  -- (2) an I/O target: after `x` by (R3)
  gisIo GF.gfGd.gdG v = true ∨
  -- (3) a cat-ordered arm (rules 1–5, 7; deps; rule 12 over `ad`) out of `x` or out of a
  --     gmo-after-`x` event
  ((u = x ∨ gmoLt GF.gfGd.gdG x u) ∧ CatLin.pinStep GF.gfGd ad u v) ∨
  -- (4) a `pw` fence out of a read forwarded from a write gmo-after `x` (the fence orders the
  --     source write before `v`)
  ((∃ w, CatLin.grfi GF.gfGd.gdG w u ∧ gmoLt GF.gfGd.gdG x w) ∧
    ∃ pr sr sw, gfenceBetween GF.gfGd.gdG u v pr true sr sw ∧
      ((glblIs GF.gfGd.gdG v lbIsR ∧ sr = true) ∨ (glblIs GF.gfGd.gdG v lbIsW ∧ sw = true)))

/-- The FORWARDING arms. -/
def ioStepClosesFwd (GF : Gfexec) (x u v : Geid) : Prop :=
  -- (5) forwarding (`grfi`) from the write `u`
  CatLin.grfi GF.gfGd.gdG u v ∨
  -- (6) `gpoloc` R→R ON the forwarded byte: `v` reads a byte `a` that `u` reads from a same-hart
  --     write gmo-after `x`
  (∃ w a t val, greadsByte GF.gfGd.gdG u a t val ∧ gwriteAt GF.gfGd.gdG t = some w ∧
    w.1 = u.1 ∧ gmoLt GF.gfGd.gdG x w ∧ ∃ t' val', greadsByte GF.gfGd.gdG v a t' val') ∨
  -- (7) `gpoloc` W→R on a byte the write `u` writes
  (∃ a val, gwritesByte GF.gfGd.gdG u a val ∧ ∃ t' val', greadsByte GF.gfGd.gdG v a t' val')

/-- **THE NAMED PER-STEP CONDITION** of (K-cat′). -/
def ioStepCloses (GF : Gfexec) (ad : List (Geid × Geid)) (x u v : Geid) : Prop :=
  ioStepClosesGmo GF ad x u v ∨ ioStepClosesFwd GF x u v

/-- A segment step after `x`: a cat same-row step meeting the named condition. -/
def ioStepC (GF : Gfexec) (ad : List (Geid × Geid)) (x u v : Geid) : Prop :=
  CatLin.rsameC GF.gfGd u v ∧ ioStepCloses GF ad x u v

/-- The NAMED exit condition of `ioSegPinnedC`: the exit reads no byte from its own hart, or its
last step is a GMO arm.  (A forwarded exit reached by a forwarding arm may be gmo-before the
entry; its outgoing cross edge is W11's, like a non-closing step.) -/
def ioExitCloses (GF : Gfexec) (ad : List (Geid × Geid)) (x exit : Geid) : Prop :=
  (¬ ∃ w, CatLin.grfi GF.gfGd.gdG w exit) ∨
  ∃ u, rtc (ioStepC GF ad x) x u ∧ CatLin.rsameC GF.gfGd u exit ∧ ioStepClosesGmo GF ad x u exit

/-! # 4. The closure -/

theorem WeakRvwmoKillIOC.gisWNotIo (G : Gexec) (e : Geid) :
    gisW G e = true → gisIo G e = false := by
  unfold gisW gisIo
  cases gxLbl G e with
  | none => simp
  | some l => cases l <;> simp [lbIsW, lbIsIo]

theorem WeakRvwmoKillIOC.gisWGlbl (G : Gexec) (e : Geid) :
    gisW G e = true → glblIs G e lbIsW := by
  intro hw
  unfold gisW at hw
  rcases h : gxLbl G e with _ | l <;> rw [h] at hw
  · cases hw
  · exact ⟨l, h, hw⟩

/-- A same-hart write gmo-after the I/O event `x` is po-after it: po-before would put it
gmo-before `x` by (R1). -/
theorem WeakRvwmoKillIOC.gpoOfGmo (GF : Gfexec) (x w : Geid) :
    ioResidueGmo GF → gisIo GF.gfGd.gdG x = true → gisW GF.gfGd.gdG w = true →
    w.1 = x.1 → gmoLt GF.gfGd.gdG x w → WeakRvwmoGraph.gpo GF.gfGd.gdG x w := by
  intro hres hx hw hag hxw
  have hxs := GraphFabResidue.gisIoSome _ _ hx
  have hwm := WeakRvwmoGraph.glblIsWGmem _ _ (WeakRvwmoKillIOC.gisWGlbl _ _ hw)
  have hws := GraphFabResidue.gmemSome _ _ hwm
  rcases Nat.lt_trichotomy w.2 x.2 with hlt | heq | hgt
  · exfalso
    have hwx : gmoLt GF.gfGd.gdG w x :=
      hres w x (Or.inl ⟨⟨hag, hlt, hws, hxs⟩, hwm, WeakRvwmoKillIOC.gisWNotIo _ _ hw, hx⟩)
    exact gmoLtIrrefl _ x (gmoLtTrans _ _ _ _ hxw hwx)
  · exfalso
    have hwx : w = x := Prod.ext hag heq
    subst hwx
    rw [WeakRvwmoKillIOC.gisWNotIo _ _ hw] at hx
    cases hx
  · exact ⟨hag.symm, hgt, hxs, hws⟩

/-- THE PER-BYTE CORE (riscv.cat's per-byte rf and load value): a read `v` of a byte `a` that a
po-earlier write `w`, gmo-after `x`, wrote is in `afterIo` — its source for `a` is `w` or
coherence-after it, so either gmo-before `v` (then `v` is gmo-after `x`) or forwarded. -/
theorem WeakRvwmoKillIOC.fwdByte (GF : Gfexec) (x w v : Geid) (a : Int) (val : BitVec 8)
    (t : Nat) (vv : BitVec 8) :
    gwf GF.gfGd.gdG → gloadValue GF.gfGd.gdG → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gwritesByte GF.gfGd.gdG w a val → gmoLt GF.gfGd.gdG x w →
    WeakRvwmoGraph.gpo GF.gfGd.gdG x v → WeakRvwmoGraph.gpo GF.gfGd.gdG w v →
    greadsByte GF.gfGd.gdG v a t vv → WeakRvwmoKillIOC.afterIo GF x v := by
  intro hwf hlv hres hx hwb hxw hxv hwv hrd
  refine ⟨hxv, ?_⟩
  have hwg := gwritesByteGwrites _ _ _ _ hwf hwb
  obtain ⟨h1, h2⟩ := hlv v a t vv hrd
  have hle : gwix GF.gfGd.gdG w ≤ t := h2 w val hwb (Or.inr hwv)
  have hpos := WeakRvwmoGraph.gwixPos _ w hwg
  cases t with
  | zero => omega
  | succ i =>
    obtain ⟨w', hat, -, hvis⟩ := h1
    obtain ⟨hw'g, hix⟩ := gwriteAtInv _ _ _ hwf.1 hat
    have hxw' : gmoLt GF.gfGd.gdG x w' := by
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact gmoLtTrans _ _ _ _ hxw (gwixLtGmo _ _ _ hwf hwg hw'g (by omega))
      · have hww : w = w' := gwixInj _ _ _ hwf.1 hwg hw'g (by omega)
        subst hww
        exact hxw
    rcases hvis with hmo | hpo
    · exact Or.inl (gmoLtTrans _ _ _ _ hxw' hmo)
    · refine Or.inr ⟨w', ⟨⟨a, i + 1, vv, hrd, hat⟩, hpo.1⟩, ?_, hxw'⟩
      exact WeakRvwmoKillIOC.gpoOfGmo GF x w' hres hx ((gwritesElemOf _ _).1 hw'g).2
        (hpo.1.trans hxv.1.symm) hxw'

/-- `rsameC` is program order. -/
theorem WeakRvwmoKillIOC.rsameCGpo (GD : Gdexec) (ad : List (Geid × Geid)) (u v : Geid) :
    CatLin.rvwmoCatAD GD ad → CatLin.rsameC GD u v → WeakRvwmoGraph.gpo GD.gdG u v := by
  intro hc h
  obtain ⟨h1, h2⟩ := CatLin.rsameCLex GD ad u v hc h
  rcases h with h | h | h | h
  · exact h.1
  · obtain ⟨m1, m2⟩ := gppoGmem _ u v h
    exact ⟨h1, h2, GraphFabResidue.gmemSome _ _ m1, GraphFabResidue.gmemSome _ _ m2⟩
  · obtain ⟨-, -, ⟨l1, hl1, -⟩, ⟨l2, hl2, -⟩⟩ := hc.2.2.2.2.1 (u, v) h
    exact ⟨h1, h2, by simp [hl1], by simp [hl2]⟩
  · obtain ⟨⟨a, t, vv, ⟨l, base, ts, vs, j, hl, -⟩, hat⟩, -⟩ := h
    have hug := (gwriteAtInv _ _ _ hc.1.1 hat).1
    exact ⟨h1, h2,
      GraphFabResidue.gmemSome _ _ (gwfGmoMem _ _ hc.1 ((gwritesElemOf _ _).1 hug).1),
      by simp [hl]⟩

/-- The GMO arms put `v` gmo-after `x`. -/
theorem WeakRvwmoKillIOC.stepGmo (GF : Gfexec) (ad : List (Geid × Geid)) (x u v : Geid) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gisIo GF.gfGd.gdG x = true →
    WeakRvwmoGraph.gpo GF.gfGd.gdG x v → WeakRvwmoGraph.gpo GF.gfGd.gdG u v →
    ioStepClosesGmo GF ad x u v → gmoLt GF.gfGd.gdG x v := by
  intro hc hres hx hxv huv h
  rcases h with hw | hio | ⟨hux, hp⟩ | ⟨⟨w, hwu, hxw⟩, pr, sr, sw, hfb, hsucc⟩
  · exact hres x v (Or.inr (Or.inl ⟨hxv, hx, hw⟩))
  · exact hres x v (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, hio, hxv⟩))))
  · have huv' := CatLin.pinStepGmo _ ad u v hc hp
    rcases hux with rfl | hxu
    · exact huv'
    · exact gmoLtTrans _ _ _ _ hxu huv'
  · obtain ⟨hag, hlt⟩ := CatLin.grfiLex _ w u hc.2.1 hc.2.2.1 hwu
    obtain ⟨-, -, kf, hk1, hk2, hkl⟩ := hfb
    have hwW : glblIs GF.gfGd.gdG w lbIsW := by
      obtain ⟨⟨a0, t0, v0, hrd0, hat⟩, -⟩ := hwu
      exact WeakRvwmoKillIOC.gisWGlbl _ _
        ((gwritesElemOf _ _).1 (gwriteAtInv _ _ _ hc.1.1 hat).1).2
    have hcov : gfenceCovers GF.gfGd.gdG w v :=
      ⟨pr, true, sr, sw,
        ⟨hag.trans huv.1, by omega, kf, by omega, hk2, by rw [hag]; exact hkl⟩,
        Or.inr ⟨hwW, rfl⟩, hsucc⟩
    exact gmoLtTrans _ _ _ _ hxw (hc.2.1 w v (Or.inr (Or.inr (Or.inr (Or.inl hcov)))))

/-- The FORWARDING arms keep `afterIo`. -/
theorem WeakRvwmoKillIOC.stepFwd (GF : Gfexec) (ad : List (Geid × Geid)) (x u v : Geid) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gisIo GF.gfGd.gdG x = true →
    (u = x ∨ WeakRvwmoKillIOC.afterIo GF x u) →
    WeakRvwmoGraph.gpo GF.gfGd.gdG x v → WeakRvwmoGraph.gpo GF.gfGd.gdG u v →
    ioStepClosesFwd GF x u v → WeakRvwmoKillIOC.afterIo GF x v := by
  intro hc hres hx hu hxv huv h
  have hwf := hc.1
  have hlv := hc.2.2.1
  -- a WRITE `u` in the segment is po-after `x`, hence gmo-after it by (R2)
  have hW : gisW GF.gfGd.gdG u = true →
      WeakRvwmoGraph.gpo GF.gfGd.gdG x u ∧ gmoLt GF.gfGd.gdG x u := by
    intro huW
    have hxu : WeakRvwmoGraph.gpo GF.gfGd.gdG x u := by
      rcases hu with rfl | hu
      · rw [WeakRvwmoKillIOC.gisWNotIo _ _ huW] at hx
        cases hx
      · exact hu.1
    exact ⟨hxu, hres x u (Or.inr (Or.inl ⟨hxu, hx, huW⟩))⟩
  rcases h with hrf | ⟨w, a, t, val, hrdu, hat, hag, hxw, t', val', hrdv⟩ |
    ⟨a, val, hwb, t', val', hrdv⟩
  · -- (5) forwarding
    obtain ⟨⟨a0, t0, v0, hrd0, hat⟩, -⟩ := id hrf
    obtain ⟨hxu, hmo⟩ := hW ((gwritesElemOf _ _).1 (gwriteAtInv _ _ _ hwf.1 hat).1).2
    exact ⟨hxv, Or.inr ⟨u, hrf, hxu, hmo⟩⟩
  · -- (6) `gpoloc` on the forwarded byte
    have hwb : gwritesByte GF.gfGd.gdG w a val := by
      cases t with
      | zero => simp [gwriteAt] at hat
      | succ i =>
        obtain ⟨w0, hat0, hwb0, -⟩ := (hlv u a (i + 1) val hrdu).1
        have hw0 : w0 = w := Option.some.inj (hat0.symm.trans hat)
        subst hw0
        exact hwb0
    obtain ⟨-, hlt⟩ := CatLin.grfiLex _ w u hc.2.1 hlv ⟨⟨a, t, val, hrdu, hat⟩, hag⟩
    have hwv : WeakRvwmoGraph.gpo GF.gfGd.gdG w v :=
      ⟨hag.trans huv.1, by have := huv.2.1; omega,
        WeakRvwmoLock.gwritesByteLbl _ _ _ _ hwb, huv.2.2.2⟩
    exact WeakRvwmoKillIOC.fwdByte GF x w v a val t' val' hwf hlv hres hx hwb hxw hxv hwv hrdv
  · -- (7) `gpoloc` W→R on a byte `u` writes
    obtain ⟨-, hmo⟩ := hW (WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hwb)
    exact WeakRvwmoKillIOC.fwdByte GF x u v a val t' val' hwf hlv hres hx hwb hmo hxv huv hrdv

/-- **THE CLOSURE** (K-cat′): a cat same-row step meeting `ioStepCloses` keeps the invariant. -/
theorem rsameCAfterIo (GF : Gfexec) (ad : List (Geid × Geid)) (x u v : Geid) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF → gisIo GF.gfGd.gdG x = true →
    (u = x ∨ WeakRvwmoKillIOC.afterIo GF x u) → CatLin.rsameC GF.gfGd u v →
    ioStepCloses GF ad x u v → WeakRvwmoKillIOC.afterIo GF x v := by
  intro hc hres hx hu hs h
  have huv := WeakRvwmoKillIOC.rsameCGpo _ ad u v hc hs
  have hxv : WeakRvwmoGraph.gpo GF.gfGd.gdG x v := by
    rcases hu with rfl | hu
    · exact huv
    · exact gpoTrans _ _ _ _ hu.1 huv
  rcases h with h | h
  · exact ⟨hxv, Or.inl (WeakRvwmoKillIOC.stepGmo GF ad x u v hc hres hx hxv huv h)⟩
  · exact WeakRvwmoKillIOC.stepFwd GF ad x u v hc hres hx hu hxv huv h

/-! # 5. The segment through an I/O event -/

/-- A segment `entry →⁺ x →* exit` (cat same-row steps; after `x`, `ioStepC` steps): the entry
is gmo-before `x` ((R1)/(R3)) and every later event satisfies `afterIo`. -/
theorem ioSegAfterIoC (GF : Gfexec) (ad : List (Geid × Geid)) (x entry exit : Geid) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG entry →
    tc (CatLin.rsameC GF.gfGd) entry x → rtc (ioStepC GF ad x) x exit →
    gmoLt GF.gfGd.gdG entry x ∧ (exit = x ∨ WeakRvwmoKillIOC.afterIo GF x exit) := by
  intro hc hres hio hm hex hxe
  have hpoe : WeakRvwmoGraph.gpo GF.gfGd.gdG entry x :=
    WeakRvwmoKillIO.tcGpo _ _ _ _ (fun u v h => WeakRvwmoKillIOC.rsameCGpo _ ad u v hc h) hex
  refine ⟨?_, ?_⟩
  · cases he : gisIo GF.gfGd.gdG entry with
    | false => exact hres entry x (Or.inl ⟨hpoe, hm, he, hio⟩)
    | true => exact hres entry x (Or.inr (Or.inr (Or.inr (Or.inl ⟨he, hio, hpoe⟩))))
  · refine rtc_ind_r (fun v => v = x ∨ WeakRvwmoKillIOC.afterIo GF x v) x (Or.inl rfl) ?_ exit hxe
    intro u v _ huv ih
    exact Or.inr (rsameCAfterIo GF ad x u v hc hres hio ih huv.1 huv.2)

/-- **`ioSegPinnedC`** (K-cat′): the cat twin of `ioSegPinned`, under the NAMED per-step
condition `ioStepCloses` (every step after `x`) and the NAMED exit condition `ioExitCloses`:
`entry <gmo exit` — the `CertC.Pinned` premise. -/
theorem ioSegPinnedC (GF : Gfexec) (ad : List (Geid × Geid)) (x entry exit : Geid) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG entry →
    tc (CatLin.rsameC GF.gfGd) entry x → rtc (ioStepC GF ad x) x exit →
    ioExitCloses GF ad x exit → gmoLt GF.gfGd.gdG entry exit := by
  intro hc hres hio hm hex hxe hexit
  obtain ⟨hen, hae⟩ := ioSegAfterIoC GF ad x entry exit hc hres hio hm hex hxe
  rcases hexit with hnf | ⟨u, hxu, hs, hg⟩
  · rcases hae with rfl | ⟨-, hmo | ⟨w, hw, -⟩⟩
    · exact hen
    · exact gmoLtTrans _ _ _ _ hen hmo
    · exact absurd ⟨w, hw⟩ hnf
  · have hu := (ioSegAfterIoC GF ad x entry u hc hres hio hm hex hxu).2
    have huv := WeakRvwmoKillIOC.rsameCGpo _ ad u exit hc hs
    have hxv : WeakRvwmoGraph.gpo GF.gfGd.gdG x exit := by
      rcases hu with rfl | hu
      · exact huv
      · exact gpoTrans _ _ _ _ hu.1 huv
    exact gmoLtTrans _ _ _ _ hen (WeakRvwmoKillIOC.stepGmo GF ad x u exit hc hres hio hxv huv hg)

/-- …as the cat chain's certificate (`CertC.Pinned`, at any gmo-forward cross order `X`). -/
theorem ioSegCertC (GF : Gfexec) (ad : List (Geid × Geid)) (X : Geid → Geid → Prop)
    (prev x : Geid) (s : Seg) :
    CatLin.rvwmoCatAD GF.gfGd ad → ioResidueGmo GF →
    gisIo GF.gfGd.gdG x = true → gmem GF.gfGd.gdG s.sgEntry →
    tc (CatLin.rsameC GF.gfGd) s.sgEntry x → rtc (ioStepC GF ad x) x s.sgExit →
    ioExitCloses GF ad x s.sgExit → X prev s.sgEntry → CatLin.CertC GF.gfGd.gdG X prev s :=
  fun hc hres hio hm hex hxe hexit hX =>
    .Pinned hX (ioSegPinnedC GF ad x s.sgEntry s.sgExit hc hres hio hm hex hxe hexit)

/-! # 6. The condition BITES at the counterexample, and is satisfiable -/

/-- **`kcatCex`'s step `u → v` is OUTSIDE `ioStepCloses`** (for every rule-12 list): `v` is a
read, not I/O; `u` is not gmo-after `x`; there is no fence; `v` reads only byte 0, where `u`'s
source is the image (byte 1 is the forwarded one); `u` writes nothing. -/
theorem kcatCexNotCloses (ad : List (Geid × Geid)) :
    ¬ ioStepCloses kcatCex ad (0, 0) (0, 2) (0, 3) := by
  rintro ((hw | hio | ⟨hux, -⟩ | ⟨-, pr, sr, sw, hfb, -⟩) |
    (hrf | ⟨w, a, t, val, hrdu, hat, -, -, t', val', hrdv⟩ | ⟨a, val, hwb, -⟩))
  · exact absurd hw (by decide +kernel)
  · exact absurd hio (by decide +kernel)
  · rcases hux with h | h
    · simp at h
    · exact absurd ((gmoLtBSpec _ _ _).2 h) (by decide +kernel)
  · obtain ⟨-, -, kf, h1, h2, -⟩ := hfb
    simp at h1 h2
    omega
  · obtain ⟨⟨a, t, vv, ⟨l, base, ts, vs, j, hl, hrd, hts, -⟩, hat⟩, -⟩ := hrf
    simp [gxLbl, kcatCex, kcatCexT, mkgt, forget, kcatCexProg] at hl
    subst hl
    simp [lbRd] at hrd
    obtain ⟨-, rfl, -⟩ := hrd
    have ht : t = 0 := by
      rcases j with _ | j <;> simp at hts
      exact hts.symm
    subst ht
    simp [gwriteAt] at hat
  · -- `v` reads only byte 0 …
    obtain ⟨l, base, ts, vs, j, hl, hrd, hts, -, hacc⟩ := hrdv
    simp [gxLbl, kcatCex, kcatCexT, mkgt, forget, kcatCexProg] at hl
    subst hl
    simp [lbRd] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    have hj : j = 0 := by
      rcases j with _ | j
      · rfl
      · simp at hts
    subst hj
    simp [accAddr] at hacc
    subst hacc
    -- … where `u`'s source is the image (timestamp 0)
    obtain ⟨l', base', ts', vs', j', hl', hrd', hts', -, hacc'⟩ := hrdu
    simp [gxLbl, kcatCex, kcatCexT, mkgt, forget, kcatCexProg] at hl'
    subst hl'
    simp [lbRd] at hrd'
    obtain ⟨rfl, rfl, rfl⟩ := hrd'
    have hj' : j' = 0 := by simp [accAddr] at hacc'; omega
    subst hj'
    simp at hts'
    subst hts'
    simp [gwriteAt] at hat
  · obtain ⟨l, base, vs, j, hl, hwr, -⟩ := hwb
    simp [gxLbl, kcatCex, kcatCexT, mkgt, forget, kcatCexProg] at hl
    subst hl
    simp [lbWr] at hwr


/-! ## 6.1 A satisfying instance: riscv.cat, NOT RVWMO⁻, the forwarding arms exercised

One hart: `e` = acquire `lb [0]` (the entry; rule 5 orders it before `x`), `x` = the UART MMIO
store, `w` = `sb [1] ← 1`, `u` = `lb [1]` and `v` = `lb [1]` (both FORWARDED from `w`, the SAME
source — riscv.cat leaves `u, v` unordered and lets both perform before `x`), `z` = `sb [2] ← 1`
(the exit).  gmo = `[e; u; v; x; w; z]`.  The segment `e → x →gpow w →rfi u →gpoloc v →gpow z`
meets every named condition (arms (1), (5), (6), (1)); `ioSegPinnedC` gives `e <gmo z`. -/

def kcatOkProg : List (List Lbl) :=
  [[LLoad true 0 [0] [b0], LIo .wr 0x10000001 [0], LStore false 1 [b1] .WCplain,
    LLoad false 1 [1] [b1], LLoad false 1 [1] [b1], LStore false 2 [b1] .WCplain]]

def kcatOkGmo : List Geid := [(0, 0), (0, 3), (0, 4), (0, 1), (0, 2), (0, 5)]

/-- The graph, TAGGED (no dependencies). -/
def kcatOkT : GdexecT := mkgt kcatOkProg kcatOkGmo []

/-- The fabric bundle: EMPTY fabric list. -/
def kcatOk : Gfexec := ⟨forget kcatOkT, []⟩

/-- The published quantifier's model holds (computed). -/
theorem kcatOkCatT : rvwmoCatConsistentT kcatOkT :=
  catTConsistentBSound _ (by decide +kernel)

theorem kcatOkCatAD : CatLin.rvwmoCatAD kcatOk.gfGd (gtAd kcatOkT.gtG kcatOkT.gtDeps) :=
  CatLin.catADOfCatT kcatOkT kcatOkCatT

/-- …and it is NOT RVWMO⁻: `w →gpoloc u` (W→R, byte 1) is gmo-reversed. -/
theorem kcatOkNotMinus : ¬ gppoGmo kcatOk.gfGd.gdG := by
  intro h
  have := h (0, 2) (0, 3) (Or.inl ((gpolocBSpec _ _ _).1 (by decide +kernel)))
  exact absurd ((gmoLtBSpec _ _ _).2 this) (by decide +kernel)

theorem WeakRvwmoKillIOC.kcatOkLbl (e : Geid) :
    (gxLbl kcatOk.gfGd.gdG e).isSome = true →
      e = (0, 0) ∨ e = (0, 1) ∨ e = (0, 2) ∨ e = (0, 3) ∨ e = (0, 4) ∨ e = (0, 5) := by
  obtain ⟨i, k⟩ := e
  intro h
  rcases i with _ | i <;> rcases k with _ | _ | _ | _ | _ | _ | k <;>
    simp [gxLbl, kcatOk, kcatOkT, mkgt, forget, kcatOkProg] at h ⊢

/-- The trusted residue's pre-[OWN.116] arms hold ((R1), (R2), (R2′), (R3)); since [OWN.116] the
residue also carries (R2″) and EXCLUDES this graph (`kcatOkExcluded`). -/
theorem kcatOkResidue : ∀ x y, ioResidue kcatOk x y →
    ¬ (WeakRvwmoGraph.gpo kcatOk.gfGd.gdG x y ∧ gisIo kcatOk.gfGd.gdG x = true ∧
      gisR kcatOk.gfGd.gdG y = true) → gmoLt kcatOk.gfGd.gdG x y := by
  intro x y hr hn6
  have hxy : (gxLbl kcatOk.gfGd.gdG x).isSome = true ∧
      (gxLbl kcatOk.gfGd.gdG y).isSome = true := by
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hx, hy, -⟩ | ⟨hx, hy, -⟩ | ⟨hp, -⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨GraphFabResidue.gisIoSome _ _ hx, GraphFabResidue.gisIoSome _ _ hy⟩
    · exact ⟨GraphFabResidue.gmemSome _ _ hx, GraphFabResidue.gmemSome _ _ hy⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
  rcases WeakRvwmoKillIOC.kcatOkLbl x hxy.1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases WeakRvwmoKillIOC.kcatOkLbl y hxy.2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | (show gmoLt kcatOk.gfGd.gdG _ _; exact (gmoLtBSpec _ _ _).1 (by decide +kernel))
  | (exfalso
     rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp⟩ |
       ⟨hx, hy, hb⟩ | ⟨hp, hx, hy⟩
     all_goals first
       | exact hn6 ⟨hp, hx, hy⟩
       | exact absurd hp.2.1 (by decide)
       | exact absurd hp.1 (by decide)
       | exact absurd hx (by decide +kernel)
       | exact absurd hy (by decide +kernel)
       | exact absurd hn (by decide)
       | (obtain ⟨i, j, hi, -⟩ := hb; simp [kcatOk] at hi))

/-- **SINCE [OWN.116] THE TRUSTED RESIDUE EXCLUDES `kcatOk`**: (R2″) orders the UART store `(0,1)`
before the po-later read `(0,3)`, which this gmo puts first. -/
theorem kcatOkExcluded : ¬ ioResidueGmo kcatOk := by
  intro h
  have := h (0, 1) (0, 3) (.inr (.inr (.inr (.inr (.inr ⟨(gpoBSpec _ _ _).1 (by decide +kernel),
    by decide +kernel, by decide +kernel⟩)))))
  exact absurd ((gmoLtBSpec _ _ _).2 this) (by decide +kernel)

theorem WeakRvwmoKillIOC.kcatOkGpow (u v : Geid) :
    gpoB kcatOk.gfGd.gdG u v = true → gmem kcatOk.gfGd.gdG u →
    gisW kcatOk.gfGd.gdG v = true → ioStepC kcatOk (gtAd kcatOkT.gtG kcatOkT.gtDeps) (0, 1) u v :=
  fun hpo hm hw => ⟨Or.inl ⟨(gpoBSpec _ _ _).1 hpo, hm, hw⟩, Or.inl (Or.inl hw)⟩

/-- **`ioSegPinnedC` applies**: every OTHER hypothesis is met, the conclusion is `e <gmo z`.  Since
[OWN.116] the residue hypothesis is the theorem's own (the graph violates (R2″), `kcatOkExcluded`), so
this instance is conditional — a record of the arms (1), (5), (6), (1). -/
theorem kcatOkSegPinned (hres : ioResidueGmo kcatOk) : gmoLt kcatOk.gfGd.gdG (0, 0) (0, 5) := by
  have hrfi : CatLin.grfi kcatOk.gfGd.gdG (0, 2) (0, 3) :=
    ⟨(grfBSpec _ _ _).1 (by decide +kernel), rfl⟩
  have s1 := WeakRvwmoKillIOC.kcatOkGpow (0, 1) (0, 2) (by decide +kernel)
    (GraphFabResidue.gisIoGmem _ _ (by decide +kernel)) (by decide +kernel)
  have s2 : ioStepC kcatOk (gtAd kcatOkT.gtG kcatOkT.gtDeps) (0, 1) (0, 2) (0, 3) :=
    ⟨Or.inr (Or.inr (Or.inr hrfi)), Or.inr (Or.inl hrfi)⟩
  have s3 : ioStepC kcatOk (gtAd kcatOkT.gtG kcatOkT.gtDeps) (0, 1) (0, 3) (0, 4) :=
    ⟨Or.inr (Or.inl (Or.inl ((gpolocBSpec _ _ _).1 (by decide +kernel)))),
      Or.inr (Or.inr (Or.inl ⟨(0, 2), 1, 1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel),
        by decide +kernel, rfl, (gmoLtBSpec _ _ _).1 (by decide +kernel), 1, b1,
        (grbBSpec _ _ _ _ _).1 (by decide +kernel)⟩))⟩
  have s4 := WeakRvwmoKillIOC.kcatOkGpow (0, 4) (0, 5) (by decide +kernel)
    ⟨LLoad false 1 [1] [b1], by decide +kernel, rfl⟩ (by decide +kernel)
  have hent : CatLin.rsameC kcatOk.gfGd (0, 0) (0, 1) :=
    Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ((gacqBSpec _ _ _).1 (by decide +kernel))))))
  refine ioSegPinnedC kcatOk _ (0, 1) (0, 0) (0, 5) kcatOkCatAD hres
    (by decide +kernel) ⟨LLoad true 0 [0] [b0], by decide +kernel, rfl⟩ (tc_once hent)
    (rtc_l s1 (rtc_l s2 (rtc_l s3 (rtc_once s4)))) (Or.inl ?_)
  rintro ⟨w, ⟨a, t, vv, ⟨l, base, ts, vs, j, hl, hrd, -⟩, -⟩, -⟩
  simp [gxLbl, kcatOk, kcatOkT, mkgt, forget, kcatOkProg] at hl
  subst hl
  simp [lbRd] at hrd

/-- …and the FORWARDED disjunct is load-bearing: `v` is in `afterIo` yet gmo-BEFORE `x`. -/
theorem kcatOkFwdOnly :
    WeakRvwmoKillIOC.afterIo kcatOk (0, 1) (0, 4) ∧ ¬ gmoLt kcatOk.gfGd.gdG (0, 1) (0, 4) := by
  refine ⟨⟨(gpoBSpec _ _ _).1 (by decide +kernel), Or.inr ⟨(0, 2),
    ⟨(grfBSpec _ _ _).1 (by decide +kernel), rfl⟩, (gpoBSpec _ _ _).1 (by decide +kernel),
    (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩⟩, ?_⟩
  exact fun h => absurd ((gmoLtBSpec _ _ _).2 h) (by decide +kernel)

/-! ## 6.2 The `w13f` instance: every same-row step of `w13fIo` closes

Row 0 is `[UART store; ld]`: there is NO same-row step after the UART store at all (the load
is not ordered after an I/O event by any `rsameC` arm, and no fence follows it); row 1's only
step is `MMIO →gpow st`, a write target (arm (1)). -/

theorem w13fIoStepCloses (ad : List (Geid × Geid)) (x u v : Geid) :
    CatLin.rsameC w13fIo.gfGd u v → ioStepCloses w13fIo ad x u v := by
  intro h
  have hc : CatLin.rvwmoCatAD w13fIo.gfGd w13fIo.gfGd.gdDeps :=
    CatLin.catADOfMinus _ ⟨w13fIoConsistent, fun p hp => by simp [w13fIo] at hp,
      fun p hp => by simp [w13fIo] at hp⟩
  obtain ⟨hag, hlt, hu, hv⟩ := WeakRvwmoKillIOC.rsameCGpo _ _ u v hc h
  rcases GraphFabResidue.w13fIoLbl u hu with rfl | rfl | rfl | rfl <;>
  rcases GraphFabResidue.w13fIoLbl v hv with rfl | rfl | rfl | rfl <;>
    simp at hag hlt
  · exfalso
    rcases h with h | h | h | h
    · exact absurd h.2.2 (by decide +kernel)
    · rcases h with ⟨-, a, ha, -⟩ | ⟨-, -, -, -, ⟨-, -, kf, h1, h2, -⟩, -⟩ | ⟨-, hr, -⟩ | ⟨-, hr, -⟩
      · rcases ha with ⟨vv, l, base, vs, j, hl, hwr, -⟩ | ⟨t, vv, l, base, ts, vs, j, hl, hrd, -⟩
        · simp [gxLbl, w13fIo, w13fIoG] at hl
          subst hl
          simp [lbWr, GraphFabResidue.uartIer] at hwr
        · simp [gxLbl, w13fIo, w13fIoG] at hl
          subst hl
          simp [lbRd, GraphFabResidue.uartIer] at hrd
      · simp at h1 h2
        omega
      · exact absurd ((glblBSpec _ _ _).2 hr) (by decide +kernel)
      · exact absurd ((glblBSpec _ _ _).2 hr) (by decide +kernel)
    · simp [w13fIo] at h
    · exact absurd ((grfBSpec _ _ _).2 h.1) (by decide +kernel)
  · exact Or.inl (Or.inl (by decide +kernel))

end Weak
