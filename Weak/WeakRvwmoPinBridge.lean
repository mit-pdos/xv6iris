/-
Weak: **the static pin checker meets the graph** (R-1(B) slice 2, deliverable 3).

Rocq: `iris/WeakRvwmoPinBridge.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`KernelPinsDef` decides a VALUE-INDEPENDENT property of the kernel image: at every load site,
what the kernel does with the loaded value before its hart's next store.  `WeakRvwmoGlue.segPin`
is the graph-level property the certification walk consumes: the segment's entry is ordered
before its exit by ppo rule 5, rule 4, or the store-dep fragment.  This file is the bridge, in
three layers, so that what is PROVED and what is HYPOTHESIZED are separated by a file boundary.

* §1–§2 PROVED, NO HYPOTHESIS: the emission-side arithmetic.  `rowDeps` is a left fold, so an
  edge emitted at ONE item is an edge of the whole emission (`rowDepsItem`); a store item's
  `dedges` contains every source position of its operand lists (`dedgesReg`) and every position
  in `dsCtl` (`dedgesCtl`); and `dsCtl` never shrinks (`dsRunCtlSub`) -- the whole content of
  "a control dependency taints EVERY po-later store".
* §3 THE HYPOTHESIS, stated precisely: `checkerTaintSubProv`.  The checker's taint is a
  SUB-approximation of the emission's provenance: if the checker's fall-through walk from the
  load at image pc `pcL` (row position `j`) reaches the instruction at `pc'` carrying register
  `r` in its taint set, then the emission's dataflow state just before `pc'`'s item has `j` in
  `dprov r`.  It is a hypothesis because the induction lining an emission's item list up with
  the checker's pc walk (the announce-boundary structure of `pstepEv` runs, and DEC-7's dynamic
  read set being a superset of the decoded sources along a run) is `WeakRvwmoAdm`-tier
  machinery; the direction is the safe one.
* §4–§6 PROVED FROM §3: `PDep` ⇒ a `rowDeps` edge ⇒ (conformance) `gdDeps` ⇒ `segPin`;
  `PCtrl` ⇒ the `LCtrl` item puts `j` in `dsCtl` ⇒ every later store's `dedges` carries
  `(j, k)`; `PFence` ⇒ `gfenceCovers`, from a row fact alone (no taint hypothesis).
* §7 THE INSTANCE on `WeakRvwmoAdm`'s computed stretch: hart 1's spin loop.  The checker's
  taint says `a5` (x15) carries the value of the `lw a5,0(a4)` at `main+0x16` when control
  reaches the `c.beqz` at `main+0x1e`, the checker's decoder says that branch's control sources
  are exactly `[DReg 15]`, and `WeakRvwmoAdm.lcCtrl` says the instance EMITS `LCtrl [DReg 15]`
  there -- by kernel computation on real image bytes.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); Rocq `Z` pcs ↦ `Int`, `agent` ↦ `Nat`, `wreg` ↦
   `Nat`, `l !! n` ↦ `l[n]?`, `dev_state` ↦ `Efab`, `CPU` ↦ `CPU`.  The Rocq section variables
   (`es`, `sites`, `pcL`, `j`) are explicit leading arguments, in that order.  Graph fences are
   written `Lbl.LFence` (the Wlabel alphabet has its own `LFence`).
2. §7's pcs are `KernelSyms.«main» + 0x16/0x18/0x1e` at the LEAN kernel image
   (`KernelPinsDef` deviation 1); the computations are `decide +kernel` (closed `Bool`/`Option`
   facts), Rocq's `vm_cast_no_check (eq_refl _)`.
3. §8's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).

**Rocq → Lean name map.**  `ds_run` `dsRun`, `ds_run_nil` `dsRunNil`, `ds_run_cons`
`dsRunCons`, `ds_run_app` `dsRunApp`, `row_deps_aux_app` `WeakRvwmoPinBridge.rowDepsAuxApp`
(duplicated name), `row_deps_item` `rowDepsItem`, `dsrcs_pos_reg` `dsrcsPosReg`,
`dedges_intro` `dedgesIntro`, `dedges_reg` `dedgesReg`, `dedges_ctl` `dedgesCtl`,
`dstep_ctl_sub` `dstepCtlSub`, `ds_run_ctl_sub` `dsRunCtlSub`, `dstep_ctl_intro`
`dstepCtlIntro`, `checker_taint_sub_prov` `checkerTaintSubProv`, `srcs_tainted_reg`
`srcsTaintedReg`, `pinnedb_dep_inv` `pinnedbDepInv`, `pinnedb_ctrl_inv` `pinnedbCtrlInv`,
`pdep_row_deps` `pdepRowDeps`, `pctrl_row_deps` `pctrlRowDeps`, `seg_pin_of_row_deps`
`segPinOfRowDeps`, `seg_pin_of_row_fence` `segPinOfRowFence`, `pin_seg_pin` `pinSegPin`,
`la_load_rd` `laLoadRd`, `la_taint_at_branch` `laTaintAtBranch`, `la_ctrl_srcs` `laCtrlSrcs`,
`la_ctrl_checker_agrees` `laCtrlCheckerAgrees`, `la_ctrl_carrier_in_run` `laCtrlCarrierInRun`.

**Dropped:** nothing (Rocq 27 declarations; Lean 27).
-/
import Weak.WeakRvwmoGlue
import Weak.WeakRvwmoAdm
import Weak.KernelPinsDef

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open KernelPinsDef
open WeakRvwmoConf (Dstate dstep)

/-! ## 1. `rowDeps`, decomposed at one item -/

def dsRun (s : Dstate) (es : List Eitem) : Dstate :=
  es.foldl (fun s it => (dstep s it).1) s

theorem dsRunNil (s : Dstate) : dsRun s [] = s := rfl

theorem dsRunCons (s : Dstate) (it : Eitem) (es : List Eitem) :
    dsRun s (it :: es) = dsRun (dstep s it).1 es := rfl

theorem dsRunApp (s : Dstate) (es1 es2 : List Eitem) :
    dsRun s (es1 ++ es2) = dsRun (dsRun s es1) es2 := by
  simp only [dsRun, List.foldl_append]

theorem WeakRvwmoPinBridge.rowDepsAuxApp (s : Dstate) (es1 es2 : List Eitem) :
    rowDepsAux s (es1 ++ es2) = rowDepsAux s es1 ++ rowDepsAux (dsRun s es1) es2 := by
  induction es1 generalizing s with
  | nil => rfl
  | cons it es1 ih =>
    show (dstep s it).2 ++ rowDepsAux (dstep s it).1 (es1 ++ es2)
      = ((dstep s it).2 ++ rowDepsAux (dstep s it).1 es1) ++ rowDepsAux (dsRun s (it :: es1)) es2
    rw [ih, List.append_assoc]
    rfl

/-- THE DECOMPOSITION: an edge the item at a given split emits is an edge of the emission. -/
theorem rowDepsItem (es pre : List Eitem) (it : Eitem) (post : List Eitem) (jk : Nat × Nat) :
    es = pre ++ it :: post →
    jk ∈ (dstep (dsRun dsInit pre) it).2 →
    jk ∈ rowDeps es := by
  rintro rfl hjk
  unfold rowDeps
  rw [WeakRvwmoPinBridge.rowDepsAuxApp]
  exact List.mem_append_right _ (List.mem_append_left _ hjk)

/-! ## 2. What a store item's `dedges` contains -/

theorem dsrcsPosReg (s : Dstate) (xs : List Dsrc) (r j : Nat) :
    Dsrc.DReg r ∈ xs → j ∈ dprov s r → j ∈ dsrcsPos s xs := by
  intro hx hj
  unfold dsrcsPos
  exact List.mem_flatten.mpr ⟨dsrcPos s (.DReg r), List.mem_map_of_mem hx, hj⟩

theorem dedgesIntro (s : Dstate) (k : Nat) (asrc vsrc : List Dsrc) (j : Nat) :
    j < k →
    j ∈ dsrcsPos s asrc ++ (dsrcsPos s vsrc ++ (s.dsCtl ++ (s.dsLd ++ dprov s wsatp))) →
    (j, k) ∈ dedges s k asrc vsrc := by
  intro hlt hj
  unfold dedges
  exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨hj, decide_eq_true hlt⟩, rfl⟩

theorem dedgesReg (s : Dstate) (k : Nat) (asrc vsrc : List Dsrc) (j r : Nat) :
    j < k → (Dsrc.DReg r ∈ asrc ∨ Dsrc.DReg r ∈ vsrc) → j ∈ dprov s r →
    (j, k) ∈ dedges s k asrc vsrc := by
  intro hlt hr hj
  apply dedgesIntro _ _ _ _ _ hlt
  rcases hr with hr | hr
  · exact List.mem_append_left _ (dsrcsPosReg _ _ _ _ hr hj)
  · exact List.mem_append_right _ (List.mem_append_left _ (dsrcsPosReg _ _ _ _ hr hj))

theorem dedgesCtl (s : Dstate) (k : Nat) (asrc vsrc : List Dsrc) (j : Nat) :
    j < k → j ∈ s.dsCtl → (j, k) ∈ dedges s k asrc vsrc := by
  intro hlt hj
  apply dedgesIntro _ _ _ _ _ hlt
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hj))

/-- `dsCtl` NEVER SHRINKS: `dstep`'s `LCtrl` arm APPENDS, and no arm resets the field. -/
theorem dstepCtlSub (s : Dstate) (it : Eitem) : s.dsCtl ⊆ (dstep s it).1.dsCtl := by
  intro x hx
  obtain ⟨l, k⟩ := it
  cases l <;> (try cases k) <;> simp only [dstep] <;>
    first | exact hx | exact List.mem_append_left _ hx

theorem dsRunCtlSub (s : Dstate) (es : List Eitem) : s.dsCtl ⊆ (dsRun s es).dsCtl := by
  induction es generalizing s with
  | nil => exact fun _ h => h
  | cons it es ih =>
    intro x hx
    rw [dsRunCons]
    exact ih _ (dstepCtlSub s it hx)

/-- ... and the `LCtrl` item is what PUTS a position there. -/
theorem dstepCtlIntro (s : Dstate) (srcs : List Dsrc) (k : Option Nat) (r j : Nat) :
    Dsrc.DReg r ∈ srcs → j ∈ dprov s r →
    j ∈ (dstep s (Wlabel.LCtrl srcs, k)).1.dsCtl := by
  intro hr hj
  show j ∈ s.dsCtl ++ dsrcsPos s srcs
  exact List.mem_append_right _ (dsrcsPosReg _ _ _ _ hr hj)

/-! ## 3. The hypothesis

A SITE ORACLE `sites pre it pc'` reads "the item `it`, reached after the prefix `pre`, is
emitted by the instruction at image pc `pc'`".  It is a parameter. -/

/-- THE CHECKER'S TAINT IS A SUB-APPROXIMATION OF THE EMISSION'S PROVENANCE. -/
def checkerTaintSubProv (es : List Eitem) (sites : List Eitem → Eitem → Int → Prop)
    (pcL : Int) (j : Nat) (own : Bool) : Prop :=
  ∀ (pre : List Eitem) (it : Eitem) (post : List Eitem) (pc' : Int) (t : List Nat) (r : Nat),
    es = pre ++ it :: post →
    sites pre it pc' →
    fwalk pinFuel own pc' (pinStart pcL) = some t →
    taintMem r t = true →
    j ∈ dprov (dsRun dsInit pre) r

/-- A `srcsTainted` verdict NAMES a tainted register. -/
theorem srcsTaintedReg (t : List Nat) (l : List Dsrc) :
    srcsTainted t l = true → ∃ r, Dsrc.DReg r ∈ l ∧ taintMem r t = true := by
  unfold srcsTainted
  induction l with
  | nil => intro h; simp at h
  | cons x l ih =>
    intro h
    rw [List.any_cons, Bool.or_eq_true] at h
    rcases h with hx | hl
    · cases x with
      | DReg r => exact ⟨r, List.mem_cons_self .., hx⟩
      | DLdRes => simp [dsrcTainted] at hx
    · obtain ⟨r, hr, ht⟩ := ih hl
      exact ⟨r, List.mem_cons_of_mem _ hr, ht⟩

/-- The two witness INVERSIONS. -/
theorem pinnedbDepInv (fuel : Nat) (pc pc' : Int) (own : Bool) :
    pinnedb fuel pc (.PDep pc' own) = true →
    ∃ t, fwalk fuel own pc' (pinStart pc) = some t ∧
         (srcsTainted t (depsAddr (krole pc')) = true ∨
          srcsTainted t (depsVsrc (krole pc')) = true) := by
  unfold pinnedb
  cases roleIsLoad (krole pc) <;> simp only [Bool.false_and, Bool.true_and] <;> intro h
  · exact absurd h (by decide)
  · revert h
    cases fwalk fuel own pc' (pinStart pc) with
    | none => intro h; exact absurd h Bool.false_ne_true
    | some t =>
      intro h
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      exact ⟨t, rfl, h.1.2⟩

theorem pinnedbCtrlInv (fuel : Nat) (pc pc' : Int) (own : Bool) :
    pinnedb fuel pc (.PCtrl pc' own) = true →
    ∃ t, fwalk fuel own pc' (pinStart pc) = some t ∧
         srcsTainted t (depsCtrl (krole pc')) = true := by
  unfold pinnedb
  cases roleIsLoad (krole pc) <;> simp only [Bool.false_and, Bool.true_and] <;> intro h
  · exact absurd h (by decide)
  · revert h
    cases fwalk fuel own pc' (pinStart pc) with
    | none => intro h; exact absurd h Bool.false_ne_true
    | some t =>
      intro h
      simp only [Bool.and_eq_true] at h
      exact ⟨t, rfl, h.1.2⟩

/-! ## 4. The `PDep` arm: a dependency witness IS a `rowDeps` edge -/

theorem pdepRowDeps (es : List Eitem) (sites : List Eitem → Eitem → Int → Prop) (pcL : Int)
    (j : Nat) (own : Bool) (pc' : Int) (k : Nat) (pre post : List Eitem) (rl : Bool) (a : Int)
    (v : List (BitVec 8)) :
    checkerTaintSubProv es sites pcL j own →
    es = pre ++ (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k)
      :: post →
    sites pre (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k) pc' →
    j < k →
    pinnedb pinFuel pcL (.PDep pc' own) = true →
    (j, k) ∈ rowDeps es := by
  intro hsub hes hsite hlt hpin
  obtain ⟨t, hw, htn⟩ := pinnedbDepInv pinFuel pcL pc' own hpin
  have hr : ∃ r, (Dsrc.DReg r ∈ depsAddr (krole pc') ∨ Dsrc.DReg r ∈ depsVsrc (krole pc')) ∧
      taintMem r t = true := by
    rcases htn with h | h
    · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
      exact ⟨r, Or.inl hr, ht⟩
    · obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ h
      exact ⟨r, Or.inr hr, ht⟩
  obtain ⟨r, hr, ht⟩ := hr
  -- THE HYPOTHESIS: the checker's taint is the emission's provenance.
  have hj := hsub pre _ post pc' t r hes hsite hw ht
  -- ... and the store item's `dedges` therefore carries the edge.
  apply rowDepsItem _ pre _ post _ hes
  exact dedgesReg _ _ _ _ _ _ hlt hr hj

/-! ## 5. The `PCtrl` arm: one control item pins EVERY later store -/

theorem pctrlRowDeps (es : List Eitem) (sites : List Eitem → Eitem → Int → Prop) (pcL : Int)
    (j : Nat) (own : Bool) (pc' : Int) (k : Nat) (pre mid post : List Eitem) (kc : Option Nat)
    (rl : Bool) (a : Int) (v : List (BitVec 8)) (asrc vsrc : List Dsrc) :
    checkerTaintSubProv es sites pcL j own →
    es = pre ++ (Wlabel.LCtrl (depsCtrl (krole pc')), kc)
      :: (mid ++ (Wlabel.LStore rl a v asrc vsrc, some k) :: post) →
    sites pre (Wlabel.LCtrl (depsCtrl (krole pc')), kc) pc' →
    j < k →
    pinnedb pinFuel pcL (.PCtrl pc' own) = true →
    (j, k) ∈ rowDeps es := by
  intro hsub hes hsite hlt hpin
  obtain ⟨t, hw, htn⟩ := pinnedbCtrlInv pinFuel pcL pc' own hpin
  obtain ⟨r, hr, ht⟩ := srcsTaintedReg _ _ htn
  have hj := hsub pre _ _ pc' t r hes hsite hw ht
  -- the control item puts `j` in `dsCtl` ...
  have hctl : j ∈ (dsRun dsInit (pre ++ [(Wlabel.LCtrl (depsCtrl (krole pc')), kc)])).dsCtl := by
    rw [dsRunApp, dsRunCons, dsRunNil]
    exact dstepCtlIntro _ _ _ _ _ hr hj
  -- ... and `dsCtl` never shrinks, so it is still there at the store.
  have hsplit : pre ++ (Wlabel.LCtrl (depsCtrl (krole pc')), kc) :: mid
      = (pre ++ [(Wlabel.LCtrl (depsCtrl (krole pc')), kc)]) ++ mid := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hctl' : j ∈ (dsRun dsInit (pre ++ (Wlabel.LCtrl (depsCtrl (krole pc')), kc) :: mid)).dsCtl := by
    rw [hsplit, dsRunApp]
    exact dsRunCtlSub _ _ hctl
  apply rowDepsItem _ (pre ++ (Wlabel.LCtrl (depsCtrl (krole pc')), kc) :: mid)
    (Wlabel.LStore rl a v asrc vsrc, some k) post
  · rw [hes]; simp only [List.append_assoc, List.cons_append]
  · exact dedgesCtl _ _ _ _ _ hlt hctl'

/-! ## 6. From an edge (or a fence) to `segPin` -/

theorem segPinOfRowDeps (GD : Gdexec) (i : Nat) (em : Hemission) (s : Seg) (j k : Nat) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    s.sgEntry = (i, j) → s.sgExit = (i, k) →
    (j, k) ∈ rowDeps em.emItems →
    segPin GD s := by
  intro hconf he hx hjk
  refine Or.inr (Or.inr ?_)
  rw [he, hx]
  exact hconf (j, k) hjk

/-- THE FENCE ARM needs no taint hypothesis at all. -/
theorem segPinOfRowFence (GD : Gdexec) (i : Nat) (s : Seg) (j kf k : Nat)
    (pr pw sr sw : Bool) :
    s.sgEntry = (i, j) → s.sgExit = (i, k) →
    j < kf → kf < k →
    gxLbl GD.gdG (i, kf) = some (Lbl.LFence pr pw sr sw) →
    glblIs GD.gdG (i, j) lbIsR → pr = true →
    glblIs GD.gdG (i, k) lbIsW → sw = true →
    segPin GD s := by
  intro he hx hj hk hf hr hpr hw hsw
  subst hpr hsw
  refine Or.inr (Or.inl ⟨true, pw, sr, true, ?_, Or.inl ⟨?_, rfl⟩, Or.inr ⟨?_, rfl⟩⟩)
  · rw [he, hx]
    exact ⟨rfl, Nat.lt_trans hj hk, kf, hj, hk, hf⟩
  · rw [he]; exact hr
  · rw [hx]; exact hw

/-- `pinSegPin` -- THE STATEMENT THE WALK CONSUMES, in Glue's vocabulary. -/
theorem pinSegPin (GD : Gdexec) (i : Nat) (em : Hemission) (s : Seg)
    (sites : List Eitem → Eitem → Int → Prop) (pcL pc' : Int) (j k : Nat) (own : Bool)
    (pre post : List Eitem) (rl : Bool) (a : Int) (v : List (BitVec 8)) :
    (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps) →
    s.sgEntry = (i, j) → s.sgExit = (i, k) →
    checkerTaintSubProv em.emItems sites pcL j own →
    em.emItems
      = pre ++ (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k)
        :: post →
    sites pre (Wlabel.LStore rl a v (depsAddr (krole pc')) (depsVsrc (krole pc')), some k) pc' →
    j < k →
    pinnedb pinFuel pcL (.PDep pc' own) = true →
    segPin GD s := by
  intro hconf he hx hsub hes hsite hlt hpin
  exact segPinOfRowDeps GD i em s j k hconf he hx
    (pdepRowDeps _ sites pcL j own pc' k pre post rl a v hsub hes hsite hlt hpin)

/-! ## 7. The instance -- hart 1's spin loop, on real image bytes -/

/-- The spin load is `lw a5,0(a4)` -- destination register 15. -/
theorem laLoadRd : loadRd ((KernelSyms.«main» : Int) + 0x16) = some 15 := by decide +kernel

/-- The checker's taint at the branch, three instructions later: register 15 still carries the
loaded value. -/
theorem laTaintAtBranch :
    (match walkTo pinFuel false ((KernelSyms.«main» : Int) + 0x18)
        ((KernelSyms.«main» : Int) + 0x1e) [15] with
     | some t => taintMem 15 t
     | none => false) = true := by decide +kernel

/-- The checker's decoder, at the branch: its control sources. -/
theorem laCtrlSrcs : depsCtrl (krole ((KernelSyms.«main» : Int) + 0x1e)) = [.DReg 15] := by
  decide +kernel

/-- THE AGREEMENT, on the nose: the list the CHECKER decodes at `main+0x1e` is the list the
INSTANCE emits there. -/
theorem laCtrlCheckerAgrees :
    (admLbls false 400 lcSt)[12]?
      = some (Wlabel.LCtrl (depsCtrl (krole ((KernelSyms.«main» : Int) + 0x1e)))) := by
  rw [laCtrlSrcs, lcCtrl]

/-- ... and the same item lives inside a genuine `admRun` of the instance. -/
theorem laCtrlCarrierInRun (cpu : CPU) (d : Efab) :
    ∃ ls, admRun true (ahP cpu lcSt) d ls (ahP cpu lcX9) d ∧
      Wlabel.LCtrl (depsCtrl (krole ((KernelSyms.«main» : Int) + 0x1e))) ∈ ls := by
  rw [laCtrlSrcs]
  exact lcCtrlInRun cpu d

end Weak
