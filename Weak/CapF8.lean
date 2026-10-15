/-
Weak: **W11-F [OWN.102] increment 11 — `readAt`'s source-message clauses at a realized load**.
Lean-only, no Rocq twin.

`CapF8.loadReadAtParts`: `CapF7.loadFloorRealized` plus, for a source timestamp `t = p + 1 ≥ 1`, the
message clauses of `readAt` (`Weak/RvwmoXv6Adequacy.lean:272`): the realized configuration's log holds
the source message `m` at position `p` (`cf.pcLog[p]? = some m`) and `m` writes the read byte
(`(msgByte m a).isSome`) — from `scaByte`'s first clause at the load's pre-state and the log's growth
to the post-state (`execLogPrefix`).  Left in `readAt`: `inRam pa 1` and `relSiteWCrel` (see PROGRESS).

Spec: FAITHFUL (proof organisation).  Names: `CapF8.*`.
-/
import Weak.CapF7

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow PfStepTsoView
open MachOfPf

/-- A logged (`t ≥ 1`) byte source is a message of the log that writes the byte. -/
theorem CapF8.msgOfLogByte (img : Image) (log : List Wmsg) (p : Nat) (a : Int)
    (h : (logByte img log (p + 1) a).isSome) : ∃ m, log[p]? = some m ∧ (msgByte m a).isSome := by
  rw [logByteS] at h
  cases hm : log[p]? with
  | none => rw [hm] at h; cases h
  | some m => rw [hm] at h; exact ⟨m, rfl, by simpa using h⟩

/-- **`readAt`'s floor, export, `rmem` and message clauses at a realized candidate load** (header). -/
theorem CapF8.loadReadAtParts (σ0 : WGState) (c : Cand) (pst : Nat → List Pexv6) (dv : Nat → Efab)
    (itvOf : Nat → Nat → Nat) (fiOf : Nat → Nat → Bool)
    (hP : srvwmoXv6M2Premises σ0 c pst dv itvOf fiOf)
    (g0 : GState) (hg0 : g0.gen = 0) (hp0 : g0.pow = false) (hgd : σ0.wgdev = g0.m.devs.reset)
    (hfs : diskOf g0.m.devs = Xv6.fsImgDisk)
    (k : Nat) (s : Estep) (hs : (candExec c).exTr[k]? = some s) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (hl : s.esLb = .LLoad aq base ts vs) (j p au' : Nat)
    (hj : ts[j]? = some (p + 1))
    (hsrc : shSrc (shadowRun cohSrc s.esAg ((candExec c).exTr.take k)).1 (p + 1) = some (au', p + 1))
    (hne : au' ≠ s.esAg) (cpu : CPU) (hcpu : hartAgent cpu = s.esAg) (pa : PAddr)
    (hpa : paZ pa = accAddr base j) :
    ∃ (cf : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (t' : List Expr) (g : GState) (m : Wmsg),
      CapF1.realAt g0 cf st t' g ∧ cf.pcLog = elog (candExec c) (k + 1) ∧
      (g.m.hr cpu).coh pa = p + 1 ∧ cf.pcLog[p]? = some m ∧ (msgByte m (paZ pa)).isSome := by
  obtain ⟨cf, st, t', g, hreal, hlog, hcoh⟩ :=
    CapF7.loadFloorRealized σ0 c pst dv itvOf fiOf hP g0 hg0 hp0 hgd hfs k s hs aq base ts vs hl j
      (p + 1) au' hj hsrc hne cpu hcpu pa hpa
  obtain ⟨-, -, -, hcons, -, -, -, -, hscaT, -, -, -⟩ := hP
  obtain ⟨hwf, -, -⟩ := srvwmoRealizable c hcons
  obtain ⟨tvn, -, -, hb⟩ := hscaT k s hs aq base ts vs hl
  obtain ⟨m, hm, hmb⟩ := CapF8.msgOfLogByte _ _ p _ (hb j (p + 1) hj).1
  have hk : k + 1 ≤ (candExec c).exTr.length := lookup_lt_Some hs
  obtain ⟨rest, hrest⟩ := execLogPrefix (candExec c) k (k + 1) hwf (by omega) hk
  refine ⟨cf, st, t', g, m, hreal, hlog, hcoh, ?_, by rw [hpa]; exact hmb⟩
  rw [hlog, ← hrest]
  exact lookup_app_l_Some hm

end Weak
