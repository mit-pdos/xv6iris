/-
Weak: **W13 (K-cat) — STOP FINDING: the plan's refined cat invariant is NOT closed** (plan
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
    trusted residue `ioResidueGmo` holds ((R1) `w2 <gmo y`, (R2) `x <gmo w`, nothing else).
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
specified, see `PROGRESS-W13W.md` for the options.
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

/-- The trusted residue holds. -/
theorem kcatCexResidue : ioResidueGmo kcatCex := by
  intro x y hr
  have hxy : (gxLbl kcatCex.gfGd.gdG x).isSome = true ∧
      (gxLbl kcatCex.gfGd.gdG y).isSome = true := by
    rcases hr with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨hx, hy, -⟩ | ⟨hx, hy, -⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ⟨GraphFabResidue.gisIoSome _ _ hx, GraphFabResidue.gisIoSome _ _ hy⟩
    · exact ⟨GraphFabResidue.gmemSome _ _ hx, GraphFabResidue.gmemSome _ _ hy⟩
  rcases WeakRvwmoKillIOC.kcatCexLbl x hxy.1 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases WeakRvwmoKillIOC.kcatCexLbl y hxy.2 with rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | (show gmoLt kcatCex.gfGd.gdG _ _; exact (gmoLtBSpec _ _ _).1 (by decide +kernel))
  | (exfalso
     rcases hr with ⟨hp, hm, hx, hy⟩ | ⟨hp, hx, hy⟩ | ⟨hp, hx, hy, hn⟩ | ⟨hx, hy, hp⟩ |
       ⟨hx, hy, hb⟩
     all_goals first
       | exact absurd hp.2.1 (by decide)
       | exact absurd hp.1 (by decide)
       | exact absurd hx (by decide +kernel)
       | exact absurd hy (by decide +kernel)
       | exact absurd hn (by decide)
       | (obtain ⟨i, j, hi, -⟩ := hb; simp [kcatCex] at hi))

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

end Weak
