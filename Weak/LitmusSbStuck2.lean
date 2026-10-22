/-
Weak: **allocproc route P, P-W3 completion — finding F-P-W3-3: the gated-read head row H3**
(`notes/weak-allocproc-plan-review-R45.md` §2.4 table row H3; plan rev 55 row P-W3; coordinator ruling
F-P-W3-1 → the VALUE read rule).  Lean-only, no Rocq twin.  A leaf of the route-P record.

The per-head table claimed (R45 H3) that a BLOCKED racy plain-read head is gmo-before every later
event of its row, by a static hop per site.  Two machine-checked facts about that row:

* **§1 `SbStuck.l7` — the unrestricted per-state claim is FALSE at the INITIAL walk state** of an
  xv6-shaped graph, under the value gate AND the source gate.  Hart z = `acquire+0x1c`'s `amoswap.w.aq`
  (`lk` 0 → 1); hart y = `holding+0x0` reading z's 1, then `holding+0x12` (`ld lk->cpu`) reading the
  image — gmo `r1 < a_z < r0` (load–load reordering; rule 11 orders `ctrl;[W]` only).  At the initial
  state `r0` is blocked (the landed top is 0, z has not issued) and `r1` is gmo-before it:
  `SbStuck.l7HeadOrdFalse` (any gate that rejects `r0` there; `SbStuck.l7ValBlk`, `SbStuck.l7SrcBlk`).
  Nothing is stuck (z's swap is free to go): the measure must ignore events nothing waits on.  The
  restricted interface `SbOrd.HeadOrdRd` (later WAITED-ON events only, `SbOrd.waitedOn`) holds there
  (`SbStuck.l7HeadOrdRd`; `SbStuck.l7R1Idle`: `r1` is waited on by nothing).
* **§2 `SbStuck.l8` — the restricted claim does not follow from RVWMO + the text alone.**  A (non-xv6)
  text where the store a stale read races with is PENDING behind a draining fence that precedes the
  AMO the racy read reads: z = `C := 1; fence rw,rw; amoswap.aq L (0 → 1)`, y = `r0 := L` (1, from the
  swap), `r1 := C` (0, the image).  RVWMO-consistent (`SbStuck.l8Cat`), and NO member exists under the
  read gate (`SbStuck.l8NoMember`: `p r0 < p r1 < q C <drain p f < p a_z < p r0`; the swap is the only
  writer of `L`, `SbStuck.l8OnlyW`, so the value gate is the source gate at `r0`).  xv6's text never
  has this shape: `lk->cpu` is written only by the holder, and the holder's release (`sw zero`, epoch-
  after its `lk->cpu` stores) has not landed, so the landed `locked` byte is 1 and `holding+0x0`'s value
  gate passes.  Discharging `HeadOrdRd` therefore needs the LOCK PROTOCOL AT THE REALIZED PREFIX (a
  FAITHFUL program-layer fact, like Q-6M-PTE (a)'s PTE custody) plus the emission's static hops
  (rule 11 into `amoswap.aq`, `fence r,rw` after `started`) — PROGRESS F-P-W3-3.

Spec: theorems about the existing model; nothing assumed.  Lean-only helpers `SbStuck.*`.
-/
import Weak.LitmusSbStuck
import Weak.SbOrdWalk
import Weak.LockFacts

namespace Weak

open MachCSL MachCSL.Stdpp
open Lbl SbWalk SbAgree SbReplay SbOrd

/-! # 1. `SbStuck.l7` — the unrestricted head order fails at the initial state -/

def SbStuck.l7Prog : List (List Lbl) :=
  [[LRmw true false 0 [0] [b0] [b1] .WCexcl],
   [LLoad false 0 [1] [b1],
    LLoad false 1 [0] [b0]]]

def SbStuck.l7Gmo : List Geid := [(1, 1), (0, 0), (1, 0)]

def SbStuck.l7 : Gdexec := AxLitmus.mkgd SbStuck.l7Prog SbStuck.l7Gmo []

/-- **THE EXECUTION IS RVWMO-CONSISTENT** (`r1` before `r0`: no rule orders two plain loads). -/
theorem SbStuck.l7Cat : rvwmoCatConsistent SbStuck.l7 := catConsistentBSound _ (by decide +kernel)

/-- With `holding`'s branch into the swap's write and nothing else (rule 11 is `ctrl;[W]`). -/
theorem SbStuck.l7CatT : rvwmoCatConsistentT (mkgt SbStuck.l7Prog SbStuck.l7Gmo []) :=
  catTConsistentBSound _ (by decide +kernel)

/-- The former per-head interface (R45 table H3–H5 as stated): a BLOCKED non-`.aq` memory head is
gmo-before EVERY later memory event of its row. -/
def SbStuck.HeadOrdAll (pol : SbPol) (G : Gexec) (X : Geid → Prop) (rdG : RdG) (dev : List Geid)
    (w : WS) : Prop :=
  ∀ x l, gxLbl G (hd w x) = some l → lbIsMem l = true → ¬ enb pol G X rdG dev w (.hd x) →
    (lbIsR l && lbAq l) = false →
    ∀ m, m ∈ G.gxGmo → m.1 = x → (hd w x).2 < m.2 → gmoLt G (hd w x) m

/-- The walk invariant holds at the initial state (reachable). -/
theorem SbStuck.l7Init (X : Geid → Prop) :
    PInv 2 AxLitmus.imgw SbStuck.l7.gdG X [] (init AxLitmus.imgw) :=
  pinvInit 2 AxLitmus.imgw _ X []

theorem SbStuck.l7Lbl : gxLbl SbStuck.l7.gdG (1, 0) = some (LLoad false 0 [1] [b1]) := rfl

/-- **THE UNRESTRICTED ORDER FAILS** at the initial state for any gate rejecting `r0` there. -/
theorem SbStuck.l7HeadOrdFalse (pol : SbPol) (rdG : RdG)
    (hrd : ¬ rdG (init AxLitmus.imgw) 1 0 [1] [b1]) :
    ¬ SbStuck.HeadOrdAll pol SbStuck.l7.gdG (fun _ => False) rdG [] (init AxLitmus.imgw) := by
  intro h
  have hb : ¬ enb pol SbStuck.l7.gdG (fun _ => False) rdG [] (init AxLitmus.imgw) (.hd 1) := by
    rintro ⟨-, l, hl, -, hen⟩
    have hl' : gxLbl SbStuck.l7.gdG (1, 0) = some l := hl
    rw [SbStuck.l7Lbl, Option.some.injEq] at hl'
    subst hl'
    rcases hen with h0 | ⟨-, -, h1⟩
    · exact h0
    · exact hrd h1
  have := h 1 _ SbStuck.l7Lbl rfl hb rfl (1, 1) (by decide) rfl (by decide)
  revert this
  unfold gmoLt
  decide +kernel

/-- The VALUE gate rejects `r0` at the initial state (the landed top of `lk` is the image's 0). -/
theorem SbStuck.l7ValBlk : ¬ valGate (init AxLitmus.imgw) 1 0 [1] [b1] := by
  intro h
  rcases h 0 b1 rfl with h1 | ⟨-, t, ⟨hs, -⟩, hv⟩
  · exact absurd h1 (by decide)
  · cases t with
    | zero => exact absurd hv (by decide)
    | succ i => exact absurd hs (by simp [logByte, init])

/-- …and so does the SOURCE gate (z's swap has not landed). -/
theorem SbStuck.l7SrcBlk : ¬ srcGate SbStuck.l7.gdG (init AxLitmus.imgw) 1 0 [1] [b1] := by
  intro h
  rcases h 0 1 b1 rfl rfl with h1 | ⟨-, h2⟩
  · exact absurd h1 (by decide)
  · rcases h2 with ⟨h3, -⟩ | ⟨src, -, hl⟩
    · exact absurd h3 (by decide)
    · simp [wrAtW, init] at hl

/-- `r1` is waited on by nothing at the initial state (no pending entry; the only AMO head writes `lk`,
not `lk->cpu`). -/
theorem SbStuck.l7R1Idle : ¬ waitedOn SbStuck.l7.gdG [] (init AxLitmus.imgw) (1, 1) := by
  rintro (h | h | ⟨a, t, v, hr, -, ⟨i, p, hp, -⟩ | ⟨x, aq, rl, base, ts, rvs, wvs, kc, hl, hw⟩ |
    ⟨x, rl, base, vs, kc, hx, hl, -⟩⟩)
  · simp at h
  · exact absurd h (by decide)
  · simp [init] at hp
  · obtain ⟨l, base', ts', vs', j, hl1, hrd, htj, -, ha⟩ := hr
    have hl1' : gxLbl SbStuck.l7.gdG (1, 1) = some (LLoad false 1 [0] [b0]) := rfl
    rw [hl1', Option.some.injEq] at hl1
    subst hl1
    simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, -⟩ := hrd
    have hj : j = 0 := by
      have := lookup_lt_Some htj
      simp at this; omega
    subst hj
    have ha' : a = 1 := by rw [← ha]; rfl
    subst ha'
    have hx : hd (init AxLitmus.imgw) x = (x, 0) := rfl
    rw [hx] at hl hw
    rcases x with _ | _ | x
    · exact absurd hw (by decide +kernel)
    · simp [gxLbl, SbStuck.l7, AxLitmus.mkgd, SbStuck.l7Prog] at hl
    · simp [gxLbl, SbStuck.l7, AxLitmus.mkgd, SbStuck.l7Prog] at hl
  · -- a device-row store head: `l7` has no device row
    have hx' : hd (init AxLitmus.imgw) x = (x, 0) := rfl
    rw [hx'] at hl
    have h8 : NCPU = 8 := rfl
    rcases x with _ | _ | x
    · omega
    · omega
    · simp [gxLbl, SbStuck.l7, AxLitmus.mkgd, SbStuck.l7Prog] at hl

/-- **THE RESTRICTED INTERFACE HOLDS THERE**: the only gated read head with a later event is `r0`, and
its later event `r1` is waited on by nothing. -/
theorem SbStuck.l7HeadOrdRd (rdG : RdG) :
    HeadOrdRd SbStuck.l7.gdG (fun _ => False) rdG [] (init AxLitmus.imgw) := by
  intro x base ts vs hl _ _ m hm hmx hlt hwo
  have hx : hd (init AxLitmus.imgw) x = (x, 0) := rfl
  rw [hx] at hl hlt
  have hmG : m = (1, 1) ∨ m = (0, 0) ∨ m = (1, 0) := by
    simpa [SbStuck.l7, AxLitmus.mkgd, SbStuck.l7Gmo] using hm
  rcases hmG with rfl | rfl | rfl
  · exact absurd hwo SbStuck.l7R1Idle
  · simp at hlt
  · simp at hlt

/-! # 2. `SbStuck.l8` — RVWMO + text alone do not give the restricted order -/

/-- Bytes: `L` = 0, `C` = 1.  Row 0 (z): `C := 1` (0,0); `fence rw,rw` (0,1); `amoswap.aq L` 0 → 1
(0,2).  Row 1 (y): `r0` (1,0) reads `L = 1` from the swap (#2); `r1` (1,1) reads `C = 0` (image).
Witness gmo: `r1 < C:=1 < a_z < r0`. -/
def SbStuck.l8Prog : List (List Lbl) :=
  [[LStore false 1 [b1] .WCplain,
    LFence true true true true,
    LRmw true false 0 [0] [b0] [b1] .WCexcl],
   [LLoad false 0 [2] [b1],
    LLoad false 1 [0] [b0]]]

def SbStuck.l8Gmo : List Geid := [(1, 1), (0, 0), (0, 2), (1, 0)]

def SbStuck.l8 : Gdexec := AxLitmus.mkgd SbStuck.l8Prog SbStuck.l8Gmo []

theorem SbStuck.l8Cat : rvwmoCatConsistent SbStuck.l8 := catConsistentBSound _ (by decide +kernel)

theorem SbStuck.l8Rf : gwriteAt SbStuck.l8.gdG 2 = some (0, 2) := by decide +kernel

theorem SbStuck.l8NoRl : SbStuck.l8Prog.flatten.all (fun l => !lbRl l) = true := by decide +kernel

/-- The swap is the ONLY writer of `L` (so at `r0` a value gate is the source gate). -/
theorem SbStuck.l8OnlyW : (gevents SbStuck.l8.gdG).filter (fun e => gwrB SbStuck.l8.gdG 0 e) = [(0, 2)] := by
  decide +kernel

/-- **NO MEMBER UNDER THE READ GATE** — for ANY issue/landing positions with program order, the read
gate (`ReadsGF`) and the draining fence's law (the pending `C := 1` lands before the fence goes):
`p r0 < p r1 < q C < p f < p a_z < p r0`. -/
theorem SbStuck.l8NoMember (p q : Geid → Nat)
    (hpo : ∀ e1 e2, WeakRvwmoGraph.gpo SbStuck.l8.gdG e1 e2 → p e1 < p e2)
    (hr : SBAcqP.ReadsGF SbStuck.l8.gdG p q) (hdr : q (0, 0) < p (0, 1)) : False := by
  have hlaz : SBAcqP.lpos SbStuck.l8.gdG p q (0, 2) = p (0, 2) := by
    unfold SBAcqP.lpos; exact if_neg (by decide +kernel)
  have hlC : SBAcqP.lpos SbStuck.l8.gdG p q (0, 0) = q (0, 0) := by
    unfold SBAcqP.lpos; exact if_pos (by decide +kernel)
  have a1 : p (0, 2) < p (1, 0) := by
    rcases hr.1 (1, 0) 0 2 b1 (0, 2) ((grbBSpec _ _ _ _ _).1 (by decide +kernel)) SbStuck.l8Rf with
      ⟨hgp, -⟩ | ⟨hl, -⟩
    · exact absurd hgp.1 (by decide)
    · rw [hlaz] at hl; exact hl
  have a2 := hpo (1, 0) (1, 1) ((gpoBSpec _ _ _).1 (by decide +kernel))
  have a3 : p (1, 1) < q (0, 0) := by
    have := (hr.2 (1, 1) 1 b0 ((grbBSpec _ _ _ _ _).1 (by decide +kernel))).1 (0, 0) b1
      ((gwbBSpec _ _ _ _).1 (by decide +kernel)) (by decide)
    rw [hlC] at this; exact this
  have a4 := hpo (0, 1) (0, 2) ((gpoBSpec _ _ _).1 (by decide +kernel))
  omega

/-! # 3. The image halves of `SbOrd.ImgFacts` (`decide +kernel` over the text walk)

`ImgFacts` is stated on GF's labels; its transport label ↔ instruction (an `LRmw`/`LFence` event of a
hart row is emitted by an AMO/FENCE word fetched from the text) is the realization's and stays named.
The image halves are census facts. -/

/-- **G1, image half**: every AMO-opcode word of the text walk is `.aq` and not `.rl` (the one AMO is
`acquire+0x1c`'s `amoswap.w.aq`, `LockFacts.amoCensus`). -/
theorem SbOrd.imgAmoAq :
    (textPcs.filter (fun p => wIsAmoop (kw p))).all (fun p => wAmoAq (kw p) && !wAmoRl (kw p)) = true := by
  decide +kernel

/-- **Every draining fence word of the text walk has `sw`** (`pw ∧ sr → sw`; the draining fences are the
four `fence iorw,iorw` of the virtio driver, `LockFacts.fenceCensus`). -/
theorem SbOrd.imgFenceSw :
    (textPcs.filter (fun p => wIsFence (kw p))).all
      (fun p => !(wFencePw (kw p) && wFenceSr (kw p)) || wFenceSw (kw p)) = true := by
  decide +kernel

/-! # 4. F-P-W4-1 — RVWMO lets a store land after its hart's later `.aq` AMO

The P member's log is LANDING order; route T read program order off it (`gwrowGmo`,
`CertZ24.poOfRowR4`).  Spec first: RVWMO orders a plain store before a po-later `.aq` AMO of ANOTHER
byte by no rule (rule 1 needs the same byte, rule 4 a fence, rule 5 orders only what FOLLOWS the
`.aq`, rule 6/7 need `.rl`).  Row 0: `x` = `sw` to byte 1 (0,0); `A` = `amoswap.w.aq` on byte 0
(0,1).  gmo `A < x`: RVWMO-consistent, so the member may land `x` after `A` although `x <po A` — the
two program-order facts of `csChainedT4` are issue-order facts (`SbKill.csIssue`), not ppo. -/

def SbStuck.l9Prog : List (List Lbl) :=
  [[LStore false 1 [b1] .WCplain, LRmw true false 0 [0] [b0] [b1] .WCexcl]]

def SbStuck.l9 : Gdexec := AxLitmus.mkgd SbStuck.l9Prog [(0, 1), (0, 0)] []

theorem SbStuck.l9Cat : rvwmoCatConsistent SbStuck.l9 := catConsistentBSound _ (by decide +kernel)

/-- The store is po-BEFORE the `.aq` AMO and gmo-AFTER it. -/
theorem SbStuck.l9StoreAfterAmo :
    WeakRvwmoGraph.gpo SbStuck.l9.gdG (0, 0) (0, 1) ∧ gmoLt SbStuck.l9.gdG (0, 1) (0, 0) :=
  ⟨(gpoBSpec _ _ _).1 (by decide +kernel), (gmoLtBSpec _ _ _).1 (by decide +kernel)⟩

end Weak
