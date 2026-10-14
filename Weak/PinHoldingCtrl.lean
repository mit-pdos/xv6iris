/-
Weak: **W9b-1 (ctrl) — the CALLER-SIDE control certificate for `holding+0x12`** (plan
`notes/weak-allocproc-plan.md` rev 51 §C W11 part list, item W9b-1; ruling [OWN.73] = Q-W11C-LOCK
(a); Lean-only, no Rocq twin).

**The site.**  `holding+0x12` (`0x80000c04`, `ld a5,16(a0)`) is the unlocked `lk->cpu` read of
`holding()` — the benign race of [OWN.64] (`notes/xv6-holding-race.md`).  It is the ONLY one of
the three benign-read sites that the pin table does not certify: `ilock+0xe` and `iunlock+0x1c`
are `PCtrl` (`Weak/KernelPins.lean:936,952`), `holding+0x12` is `PResidue` (`:255`).  In THIS
image (xv6-riscv b72cbac1) `holding` is

    holding+0x00  lw   a5,0(a0)       ; lk->locked              (PCtrl, the bnez below)
    holding+0x02  bnez a5,holding+0x8
    ...           (frame: addi sp,-32; sd ra/s0/s1; addi s0)
    holding+0x12  ld   a5,16(a0)      ; lk->cpu                 <- THE SITE
    holding+0x14  mv   s1,a5
    holding+0x16  jal  mycpu          ; mycpu spills ra/s0 to ITS frame, returns &cpus[tp]
    holding+0x1a  sub  a0,s1,a0
    holding+0x1e  seqz a0,a0          ; the compare RESULT, in a0
    holding+0x22  ld   ra,24(sp) ; ld s0 ; ld s1 ; addi sp,32
    holding+0x2a  ret

(no `push_off`/`pop_off` in this image's `holding` — the plan text's shape is an older xv6's).
The branch that tests the compare is the CALLER's: `acquire+0x18` (`bnez a0`), `release+0x10`
(`beqz a0`), `sched+0x18` (`beqz a0`), each the first branch after the call returns.  The
checker's walk (`KernelPinsDef.pstep`) fails at `holding`'s `ret` (empty return stack) — hence
`PResidue` (`holdingCtrlNotAllPaths` below).

**What this file proves.**

  §1  THE STATIC CLASSIFICATION (all `decide +kernel` over the image, no premise):
      * the fall-through walk (`own = true`: `mycpu`'s two frame spills skipped) reaches
        `holding`'s `ret` with exactly `a0` tainted (`holdingRetTaint`), on a branch-free stretch
        (`holdingStretchLinear`: every step has ONE successor, so any path is the fall-through);
      * the direct callers of `holding` are exactly the three call sites
        (`holdingCallersCover`), nothing jumps or branches into `holding`'s body from outside it
        (`holdingNoJumpIn`), and nothing falls into it (`holdingNoFallIn`);
      * resumed at each caller's return point with that taint and an empty return stack, the
        walk is CONTROL-pinned on every path by the caller's branch, with `own = false`
        (`holdingCallersPinned`).
  §2  THE CERTIFICATE (riscv.cat ppo rule 11): from an alignment of the emission with that walk
      — `holding`'s stretch (`reaches true`), the `ret`'s own group (`grpOkb`), and the caller's
      stretch from the return point (`reaches false`) — the read's row position is in `dsCtl` at
      the caller's `LCtrl` item, so EVERY po-later store's `dedges` carries it
      (`holdingCtrlRowDeps`), hence `segPinC` for any segment entering at the read and exiting at
      such a store (`holdingCtrlSegPinC`).  The control list may be the emitted DYNAMIC one
      (`LCtrl srcs` covering the decoded list, as `pinSegPinCtrlSupC'`).

**What is NOT proved — the stop condition of the brief.**  The alignment premises of §2 are of
the same kind as `psites`/`psitesA` (the R-3 residual W9a (B) discharges), but they contain TWO
`ret`s whose `ra` came back from the stack: `mycpu`'s (a descended call, `ld ra,8(sp)`) and
`holding`'s own (`ld ra,24(sp)`, with an EMPTY static return stack: the premise "the run
continues at a return point in `holdingCallSites`" is the frame/return fact).  Discharging them
needs (i) each `ld ra` reads its own `sd ra` spill (own-stack rfi — no foreign write to the
slot), and (ii) `holding` was entered by one of the three direct calls (the static half is
`holdingCallersCover`/`holdingNoJumpIn`/`holdingNoFallIn`; no INDIRECT transfer targets
`holding` is NOT decided here).  W9a (B)'s plan avoids every frame-`ret` obligation (B3 (s3)
demotes the one `ret` walk, `kexec+0x1b4`), so this site re-introduces exactly the W9a (B)
frame/return facts — `PROGRESS-W9b1.md`.

Spec: no trusted text.  Rule 11 is riscv.cat's (`ctrl; [W]` in ppo); the syntactic control
dependency runs through registers only (`s1 → a0` across `mycpu`'s call and `holding`'s `ret`,
neither of which writes `a0` after `seqz`), exactly what the taint walk tracks.  A `ret` is not
treated as an ordering point anywhere.
-/
import Weak.WeakRvwmoPinBridge3
import Weak.KernelPins

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)
open CatLin

/-! ## 1. The static classification -/

/-- The site: `holding+0x12`, `ld a5,16(a0)` (the `lk->cpu` read). -/
def holdingCtrlPc : Int := (KernelSyms.«holding» : Int) + 0x12

/-- `holding`'s `ret`. -/
def holdingRetPc : Int := (KernelSyms.«holding» : Int) + 0x2a

/-- `holding`'s callers: (return point, the caller's branch on the returned `a0`). -/
def holdingCallSites : List (Int × Int) :=
  [ ((KernelSyms.«acquire» : Int) + 0x16, (KernelSyms.«acquire» : Int) + 0x18)
  , ((KernelSyms.«release» : Int) + 0x10, (KernelSyms.«release» : Int) + 0x10)
  , ((KernelSyms.«sched» : Int) + 0x18, (KernelSyms.«sched» : Int) + 0x18) ]

/-- The site is in the pin table as `PResidue` — the classification this file supersedes. -/
theorem holdingCtrlTableResidue : (holdingCtrlPc, Pin.PResidue) ∈ pins := by decide +kernel

/-- ... because the all-paths search fails at `holding`'s `ret` (empty return stack), with or
without the sp-frame assumption. -/
theorem holdingCtrlNotAllPaths :
    allPathsPinned true holdingCtrlPc = false ∧ allPathsPinned false holdingCtrlPc = false := by
  decide +kernel

theorem holdingRetIsRet : kflowOf holdingRetPc = .FLret := by decide +kernel

/-- The fall-through walk reaches `holding`'s `ret` with exactly `a0` (x10) tainted; it needs
`own = true` (`mycpu`'s `sd ra`/`sd s0` to its own frame). -/
theorem holdingRetTaint :
    fwalk pinFuel true holdingRetPc (pinStart holdingCtrlPc) = some [10] := by decide +kernel

/-- The `ret`'s own decoded update keeps the taint. -/
theorem holdingRetTaintStep : taintStep [10] holdingRetPc = [10] := by decide +kernel

/-- A walk to `stop` along which EVERY step has exactly ONE `pstep` successor — so the
fall-through path is the only path (no branch, no pin, no failure on the way). -/
def PinHoldingCtrl.linTo : Nat → Bool → Int → PState → Bool
  | 0, _, _, _ => false
  | f + 1, own, stop, s =>
      if s.psPc == stop then true
      else match pstep own s with
        | some [s'] => PinHoldingCtrl.linTo f own stop s'
        | _ => false

/-- `holding`'s stretch from the site to its `ret` is branch-free (the descent into `mycpu` and
its return included). -/
theorem holdingStretchLinear :
    PinHoldingCtrl.linTo pinFuel true holdingRetPc (pinStart holdingCtrlPc) = true := by
  decide +kernel

/-- EVERY direct call of `holding` in the flat text walk returns to one of the three return
points. -/
theorem holdingCallersCover :
    textPcs.all (fun pc =>
      match kflowOf pc with
      | .FLcall tgt =>
          !(tgt == (KernelSyms.«holding» : Int))
            || holdingCallSites.any (fun ab => ab.1 == pc + wSize (kw pc))
      | _ => true) = true := by
  decide +kernel

/-- `x` is strictly inside `holding`'s body (past its entry, up to its `ret`). -/
def PinHoldingCtrl.inBody (x : Int) : Bool :=
  decide ((KernelSyms.«holding» : Int) < x) && decide (x ≤ holdingRetPc)

/-- A direct transfer at `pc` lands inside `holding`'s body only from inside it. -/
def PinHoldingCtrl.noJumpInAt (pc : Int) : Bool :=
  match kflowOf pc with
  | .FLjump tgt | .FLbranch tgt | .FLcall tgt =>
      !(PinHoldingCtrl.inBody tgt) || PinHoldingCtrl.inBody pc
  | _ => true

/-- No direct jump, branch or call from OUTSIDE `holding` lands inside its body. -/
theorem holdingNoJumpIn : textPcs.all PinHoldingCtrl.noJumpInAt = true := by
  decide +kernel

/-- ... and nothing falls into it: the word before `holding` is a `ret`. -/
theorem holdingNoFallIn : kflowOf ((KernelSyms.«holding» : Int) - 2) = .FLret := by
  decide +kernel

/-- A `PCtrl` witness from an ARBITRARY walk state (the caller-side resumption): the fall-through
walk reaches a branch on the taint, and every path out of the state is pinned. -/
def PinHoldingCtrl.ctrlFrom (fuel : Nat) (own : Bool) (s : PState) (pc' : Int) : Bool :=
  match fwalk fuel own pc' s with
  | some t =>
      roleIsBranch (krole pc') && srcsTainted t (depsCtrl (krole pc'))
        && pdfs pdfsFuel own [] [s]
  | none => false

/-- **THE CALLER SIDE**: resumed at each return point with `a0` tainted and an empty return
stack, the walk is CONTROL-pinned by the caller's branch on every path, skipping no store. -/
theorem holdingCallersPinned :
    holdingCallSites.all (fun ab =>
      PinHoldingCtrl.ctrlFrom pinFuel false (PState.PSt ab.1 [10] []) ab.2) = true := by
  decide +kernel

theorem PinHoldingCtrl.ctrlFromInv (fuel : Nat) (own : Bool) (s : PState) (pc' : Int) :
    PinHoldingCtrl.ctrlFrom fuel own s pc' = true →
    ∃ t, fwalk fuel own pc' s = some t ∧ srcsTainted t (depsCtrl (krole pc')) = true := by
  unfold PinHoldingCtrl.ctrlFrom
  cases h : fwalk fuel own pc' s with
  | none => intro hc; cases hc
  | some t =>
    intro hc
    simp only [Bool.and_eq_true] at hc
    exact ⟨t, rfl, hc.1.2⟩

theorem PinHoldingCtrl.callerPinned (a b : Int) :
    (a, b) ∈ holdingCallSites →
    ∃ t, fwalk pinFuel false b (PState.PSt a [10] []) = some t
      ∧ srcsTainted t (depsCtrl (krole b)) = true := by
  intro hm
  have h := List.all_eq_true.1 holdingCallersPinned (a, b) hm
  exact PinHoldingCtrl.ctrlFromInv _ _ _ _ h

/-! ## 2. The certificate: rule 11 through the caller's branch -/

/-- **THE ROW EDGE.**  Along an emission aligned with the walk — `holding`'s stretch from the
site to its `ret` (`mid1`), the `ret`'s group (`g1 ++ g2`), the caller's stretch from the return
point `a` to its branch `b` (`mid2`) — the caller's control item puts the read's row position `j`
in `dsCtl`, so the po-later store at `k` carries the edge `(j, k)`. -/
theorem holdingCtrlRowDeps (es : List Eitem) (j k : Nat)
    (base mid1 g1 g2 mid2 mid post : List Eitem) (sR s2 : PState) (a b : Int)
    (srcs : List Dsrc) (kc : Option Nat) (rl : Bool) (adr : Int) (v : List (BitVec 8))
    (asrc vsrc : List Dsrc) :
    invOk j (dsRun dsInit base) (pinT0 holdingCtrlPc) →
    reaches true holdingRetPc (pinStart holdingCtrlPc) mid1 sR →
    grpOkb holdingRetPc g1 g2 = true →
    (a, b) ∈ holdingCallSites →
    reaches false b (PState.PSt a (taintStep sR.psT holdingRetPc) []) mid2 s2 →
    es = base ++ mid1 ++ (g1 ++ g2) ++ mid2 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl adr v asrc vsrc, some k) :: post) →
    dsubb (depsCtrl (krole b)) srcs = true →
    j < k →
    (j, k) ∈ rowDeps es := by
  intro hbase hr1 hg hab hr2 hes hcov hlt
  -- the taint at `holding`'s `ret` is the static one, `[10]`
  have hT : [10] = sR.psT := reachesFwalk true _ _ _ _ hr1 pinFuel _ holdingRetTaint
  rw [← hT, holdingRetTaintStep] at hr2
  -- the invariant, carried across the three pieces
  have i1 := reachesInv j true _ _ _ _ hr1 _ hbase
  rw [← hT] at i1
  have i2 := grpSound j _ _ _ _ _ hg i1
  rw [holdingRetTaintStep] at i2
  have i3 := reachesInv j false _ _ _ _ hr2 _ i2
  -- the caller's branch tests a tainted register
  obtain ⟨t, hw, htn⟩ := PinHoldingCtrl.callerPinned a b hab
  have ht : t = s2.psT := reachesFwalk false _ _ _ _ hr2 pinFuel t hw
  rw [ht] at htn
  obtain ⟨r, hr, hrt⟩ := srcsTaintedReg _ _ htn
  have hj := i3 r hrt
  have hpre : dsRun dsInit (base ++ mid1 ++ (g1 ++ g2) ++ mid2)
      = dsRun (dsRun (dsRun (dsRun dsInit base) mid1) (g1 ++ g2)) mid2 := by
    simp only [dsRunApp]
  rw [← hpre] at hj
  have hctl : j ∈ (dsRun dsInit
      (base ++ mid1 ++ (g1 ++ g2) ++ mid2 ++ [(Wlabel.LCtrl srcs, kc)])).dsCtl := by
    rw [dsRunApp, dsRunCons, dsRunNil]
    exact dstepCtlIntro _ _ _ _ _ (dsubbElem _ _ _ hcov hr) hj
  have hctl' : j ∈ (dsRun dsInit
      (base ++ mid1 ++ (g1 ++ g2) ++ mid2 ++ (Wlabel.LCtrl srcs, kc) :: mid)).dsCtl := by
    have hsplit : base ++ mid1 ++ (g1 ++ g2) ++ mid2 ++ (Wlabel.LCtrl srcs, kc) :: mid
        = (base ++ mid1 ++ (g1 ++ g2) ++ mid2 ++ [(Wlabel.LCtrl srcs, kc)]) ++ mid := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hsplit, dsRunApp]
    exact dsRunCtlSub _ _ hctl
  apply rowDepsItem _ (base ++ mid1 ++ (g1 ++ g2) ++ mid2 ++ (Wlabel.LCtrl srcs, kc) :: mid)
    (Wlabel.LStore rl adr v asrc vsrc, some k) post
  · rw [hes]; simp only [List.append_assoc, List.cons_append]
  · exact dedgesCtl _ _ _ _ _ hlt hctl'

/-- **`holding+0x12` INTO `segPinC`** (rule 11 through the caller's branch): a segment entering
at the read (row position `j`) and exiting at a store po-after the caller's branch is pinned,
under the walk alignment of `holdingCtrlRowDeps`. -/
theorem holdingCtrlSegPinC (GD : Gdexec) (ad : List (Geid × Geid)) (i : Nat) (em : Hemission)
    (sg : Seg) (j k : Nat) (base mid1 g1 g2 mid2 mid post : List Eitem) (sR s2 : PState)
    (a b : Int) (srcs : List Dsrc) (kc : Option Nat) (rl : Bool) (adr : Int)
    (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    sg.sgEntry = (i, j) → sg.sgExit = (i, k) →
    invOk j (dsRun dsInit base) (pinT0 holdingCtrlPc) →
    reaches true holdingRetPc (pinStart holdingCtrlPc) mid1 sR →
    grpOkb holdingRetPc g1 g2 = true →
    (a, b) ∈ holdingCallSites →
    reaches false b (PState.PSt a (taintStep sR.psT holdingRetPc) []) mid2 s2 →
    em.emItems = base ++ mid1 ++ (g1 ++ g2) ++ mid2 ++ (Wlabel.LCtrl srcs, kc)
      :: (mid ++ (Wlabel.LStore rl adr v asrc vsrc, some k) :: post) →
    dsubb (depsCtrl (krole b)) srcs = true →
    j < k →
    segPinC GD ad sg := by
  intro hconf he hx hbase hr1 hg hab hr2 hes hcov hlt
  exact WeakRvwmoPinBridge3.segPinCOfSegPin GD ad sg
    (segPinOfRowDeps GD i em sg j k hconf he hx
      (holdingCtrlRowDeps _ j k base mid1 g1 g2 mid2 mid post sR s2 a b srcs kc rl adr v asrc
        vsrc hbase hr1 hg hab hr2 hes hcov hlt))

end Weak
