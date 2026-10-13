/-
Weak: **the `esil` → `admRun` bridge** (route B).

Rocq: `iris/WeakRvwmoAdm.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakRvwmoConfWit2` §6(b) named the one missing mechanism for a multi-event hart row: every
emitted block on the tree started AT its memory node with an EMPTY administrative run
(`ARnil`), because nothing turned a certified silent stretch (`WeakEvStarted`'s `esil`/`ecurLoop`
composition, a WP-tier object) into an `admRun` at the `pstepEv` tier.  The translation is not a
formality: the nodes of a stretch emit `LRegW`, `LCtrl` and `LInstr` (not `LSilent`), they move
the per-instruction channel `ib` (`ibRd`/`ibAnn`), and those are exactly the labels
`WeakRvwmoConf.rowDeps` reads.

(1) §1 THE DEFINITIONAL BRIDGE `admRunOfPevrun`: a `pstepEv` chain (`WeakEvProv.pevrun`) all of
    whose labels are `lbAdmin` IS an `admRun` with that very label list -- and back.
(2) §2 THE REFLECTIVE CHECKER.  `esilNode`'s label-carrying twin `admNode` over the
    administrative hart state `aht` (register file, channel, monad): it steps the `pure` node
    (the instruction BOUNDARY, `LInstr` + the announce reset), `regRead` (silent, the DEC-7 read
    set grows), `regWrite` (the label is `erwLabel` of the instance's own classification), the
    announce and the silent nodes; every memory node, barrier and `choose` STOPS it.
    `admIter`/`admLbls` are TOTAL, and `admRunOfIter` is the ONCE-PROVEN soundness: for every
    fuel and every state, `admLbls` IS an `admRun true` from the cursor to `admIter`'s cursor.
    No hypothesis, no footprint; the fabric is untouched.
(3) §3 THE STRETCH at hart 1's spin load `lw a5,0(a4)` (`main+0x16`): 117 administrative nodes
    from the load's RESUME to the next memory node, computed -- crossing the instruction
    boundary (item 9) and carrying, as its FIRST item, `LRegW 15 [DLdRes, DReg 14, …]`: the
    load's own destination-register write with the load-result source.
(4) §4 THE TWO-EVENT ROW `laHartConf`: hart 1's row is the spin load and THE FETCH of the next
    instruction (`main+0x18`), with §3's stretch between them -- the first row on the tree of
    length > 1 whose `hemit` derivation uses a non-empty `admRun`.  (Lean, Stage C: the fetch is
    administrative, so the second event is the `fence r,rw` itself -- deviation 3.)
(5) §5 THE TWO-HART GRAPH `mp2` with a two-event row (genuine program order), its consistency and
    its `gdexecQconf` bundle `mp2Qconf`.
(6) §6 THE CONTROL CARRIER: the taken `beqz` at `main+0x1e` emits `LCtrl [DReg 15]` (item 12
    of the stretch at the branch's fetch), inside a genuine `admRun` (`lcCtrlInRun`).

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); `WeakRvwmoConfWit2`'s vocabulary (`regstate` ↦
   `RegFile`, `oib32` ↦ `Ibch`, `M unit` ↦ `SailM Unit`, `dev_state` ↦ `Efab`, `agent` ↦ `Nat`,
   `bv_unsigned w` ↦ `w.toNat`, `Forall P l` ↦ `∀ x ∈ l, P x`, `forallb` ↦ `List.all`,
   `l !! n` ↦ `l[n]?`, `default x o` ↦ `o.getD x`).  `aht` keeps Rocq's nesting
   `(RegFile × Ibch) × SailM Unit` (so `ahRs x = x.1.1`).  `eread_width` returns `Option Nat`.
2. THE STEP: Lean's `pnodeStep` carries the executed barrier `obar` (`WeakEvInst` deviation 4),
   so `pstepEvNode` takes it as an extra argument.  `admNode`'s arms are `pnodeStep`'s (one per
   lean-sail `Outcome` constructor; `getCycleCount` answers `(0 : Nat)`, an `.error` node stops).
   Requests are indexed by the VA width too (`ereadReqAt n va`), so `ahLoadPstep` takes `va`.
3. O2 / STAGE C — THE FETCH IS ADMINISTRATIVE (owner ruling Q-C1,
   `notes/weak-port-o2-stageC.md` item 17).  The Lean model tags fetches `AK_ifetch` and
   `pstepEv` emits `LIFetch base tvs` for them (Rocq: a plain `LLoad` row item, finding F7); under
   Stage C `LIFetch` is an `lbAdmin true` label with NO row item (`projLbl` sends it to `none`).
   So Rocq's second row event (the fetch at `main+0x18`) cannot be a row event; the row's second
   event is the NEXT genuine memory event, the `fence r,rw` at `main+0x18` (`laRow t w =
   [LLoad …, LFence true false true true]`), and the fetch sits as an ADMINISTRATIVE item
   before that instruction's `LInstr`:
   `laEm`'s items are `(laWl0, some 0) :: eadm (WeakRvwmoAdm.laAdm w) ++ [(laWlF, some 1)]`, with
   `laAdm w = laLs w ++ laWl1 :: (stretch ++ laWlH :: stretch)` -- §3's 117-node stretch, the low
   fetch `laWl1` (`0x000f`), a computed stretch, the HIGH fetch `WeakRvwmoAdm.laWlH` (`0x0230`,
   at `main+0x1a = 2147487464`) and a computed stretch to the barrier node
   (`WeakRvwmoAdm.laBar`: `Barrier_RISCV_r_rw`, uniformly in the word read).  `laFetchPlain`
   reads `classify … = ⟨true, false, false⟩` (`akIfetch`).  Lean-only: `WeakRvwmoAdm.ahFetchPstep`
   (the i-cache arm), `WeakRvwmoAdm.ahBarPstep` / `WeakRvwmoAdm.ahFenceRealizes` (the fence
   block), `WeakRvwmoAdm.admRunApp` (runs compose), `WeakRvwmoAdm.laX4/laX5/laX6`,
   `WeakRvwmoAdm.laX5IsRead`, `WeakRvwmoAdm.laReqh`, `WeakRvwmoAdm.laFetchHiReq/Plain/Ram/Pa`,
   `WeakRvwmoAdm.laTxtHi`, `WeakRvwmoAdm.laTxtHiKw`, `WeakRvwmoAdm.laTvh`, `WeakRvwmoAdm.laWlH`,
   `WeakRvwmoAdm.laWlF`, `WeakRvwmoAdm.laAdm`, `WeakRvwmoAdm.laP6`, `WeakRvwmoAdm.laPfin`,
   `WeakRvwmoAdm.laAdmMem`, `WeakRvwmoAdm.eadmAllNostore`.  The graph `mp2`: hart 1's row is
   `[load, fence]`, gmo `[(0,0), (1,0)]` (a fence is no memory event), `mp2Rd` has only the flag
   disjunct; `mp2Img` carries the flag word and BOTH fetched halves (`mp2ImgTxt`,
   `WeakRvwmoAdm.mp2ImgTxtHi`), so the extra `gdexecQconf` slot `emFetchImg` is discharged by
   `WeakRvwmoAdm.laEmFetchImg` (the pinned bytes are the kernel image's: `laTxtKw`,
   `laTxtHiKw`).  Stage B's `WeakRvwmoAdm.ahFetchRealizes` is DELETED.
4. THE CONCRETE STATE (`WeakRvwmoConfWit2` deviation 2): the cursors start at `ldRs0` and resume
   the Lean fetch window `ldWf : BitVec 32`.  THE MEASUREMENTS MATCH ROCQ (106 + 97 nodes to the
   load; 117-node stretch, `LRegW 15 [DLdRes, DReg 14, DReg 39, DReg 45, DReg 44]` at item 0,
   `LInstr` at item 9; the fetched words `0x000f`, `0x0230`, `0x2781`, `0x00efdfe5`; a 128-node
   stretch at the branch with `LCtrl [DReg 15]` at item 12).  The ADDRESSES are the Lean kernel
   image's: `main+0x18 = 0x80000ee6` (`laFetchPa = 2147487462`), `&started = 0x8000a100`
   (`laFlagPa = 2147525632`), the loop-back fetch at `main+0x16 = 2147487460`.
   `laReqd`/`laReqf` are `Option.get`s (Lean-only proof arguments `WeakRvwmoAdm.laX2IsRead`,
   `WeakRvwmoAdm.laX3IsRead`); `laLoadPa` is stated at `@Eq PAddr`.
5. THE COMPUTATIONS: Rocq's `vm_cast_no_check (eq_refl _)` -- including the facts UNIFORM IN THE
   WORD READ `w`, whose evaluation never branches on `w` -- are closed by the Lean-only tactic
   `weak_adm_krfl`: `Eq.refl` handed straight to the KERNEL as an auxiliary theorem abstracted
   over the local context (the mechanism of `decide +kernel` for an equation with free variables;
   the same tactic as `MachCSL.URunRW`'s `kernel_rfl`, renamed so the two never meet).  Closed
   `Bool`/`Int` facts use `decide +kernel`.
6. §7's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): the private interpreter `admNode` returns `none` at an SFENCE.VMA announce (the marker is not an administrative label); `admNodePstep`/`admNodeAdmok` have the matching cases.

**Rocq → Lean name map.**  `adm_run_of_pevrun` `admRunOfPevrun`, `pevrun_of_adm_run`
`pevrunOfAdmRun`, `aht` `aht`, `ah_rs/ib/m` `ahRs/ahIb/ahM`, `ahP` `ahP`, `adm_node` `admNode`,
`adm_iter` `admIter`, `adm_lbls` `admLbls`, `adm_count` `admCount`, `eread_width` `ereadWidth`,
`eread_pa_at` `ereadPaAt`, `ah_read/write/bar` `ahRead/ahWrite/ahBar`, `pstep_ev_node`
`pstepEvNode`, `adm_node_pstep` `admNodePstep`, `adm_run_of_iter` `admRunOfIter`,
`pevrun_of_iter` `pevrunOfIter`, `la_x0..3` `laX0..3`, `la_reqd/reqf` `laReqd/laReqf`,
`la_load_req/pa/plain/ram` `laLoadReq/Pa/Plain/Ram`, `la_stretch_len/regw/instr`
`laStretchLen/Regw/Instr`, `la_fetch_req/plain/ram/pa` `laFetchReq/Plain/Ram/Pa`, `la_flag_pa`
`laFlagPa`, `la_txt` `laTxt`, `ah_load_pstep` `ahLoadPstep`, `ah_load_realizes`
`ahLoadRealizes`, `la_wl0/wl1` `laWl0/laWl1`, `la_tvf` `laTvf`, `la_row` `laRow`, `la_ls`
`laLs`, `la_p0..3` `laP0..3`, `la_em` `laEm`, `la_hart_conf` `laHartConf`, `wl_admok`
`wlAdmok`, `adm_node_admok` `admNodeAdmok`, `adm_lbls_admok` `admLblsAdmok`, `forallb_elem_of`
`forallbElemOf`, `it_nostore` `itNostore`, `row_deps_aux_nostore` `rowDepsAuxNostore`,
`row_deps_nostore` `rowDepsNostore`, `eadm_nostore` `eadmNostore`, `la_em_items_fst`
`laEmItemsFst`, `la_em_devfree` `laEmDevfree`, `forallb_nostore_shape` `forallbNostoreShape`,
`la_row_deps_empty` `laRowDepsEmpty`, `la_txt_pa` `laTxtPa`, `mp2_img` `mp2Img`, `mp2` `mp2`,
`mp2d` `mp2d`, `la_txt_pa_val` `laTxtPaVal`, `la_bytes_disj` `laBytesDisj`, `mp2_lbl` `mp2Lbl`,
`mp2_pos` `mp2Pos`, `mp2_noaq` `mp2Noaq`, `mp2_gpo_inv` `mp2GpoInv`, `mp2_wr` `mp2Wr`, `mp2_rd`
`mp2Rd`, `mp2_img_txt` `mp2ImgTxt`, `mp2_gwrites` `mp2Gwrites`, `mp2_gwix0` `mp2Gwix0`,
`mp2_write_at1` `mp2WriteAt1`, `mp2_gvis0` `mp2Gvis0`, `mp2_ppo_gmo` `mp2PpoGmo`,
`mp2_consistent` `mp2Consistent`, `mp2_deps_consistent` `mp2DepsConsistent`, `mp2_boot`
`mp2Boot`, `mp2_qconf` `mp2Qconf`, `lc_x4..9` `lcX4..9`, `lc_st` `lcSt`, `lc_fetch_hi`
`lcFetchHi`, `lc_bar` `lcBar`, `lc_bar_nopark` `lcBarNopark`, `lc_fetch_addiw` `lcFetchAddiw`,
`lc_fetch_beqz` `lcFetchBeqz`, `lc_stretch_len` `lcStretchLen`, `lc_loop_back` `lcLoopBack`,
`lc_loop_back_pa` `lcLoopBackPa`, `lc_ctrl` `lcCtrl`, `lc_ctrl_in_run` `lcCtrlInRun`.
Lean-only (file-qualified): `WeakRvwmoAdm.lbAdminErwLabel`, `WeakRvwmoAdm.laX2IsRead`,
`WeakRvwmoAdm.laX3IsRead`, `WeakRvwmoAdm.laTxtKw` (the fetched half IS the image's),
and deviation 3's list, and the tactic `weak_adm_krfl` (deviation 5).

**Dropped:** nothing (Rocq 103 declarations; Lean 103 + 29 Lean-only + the tactic).
-/
import Weak.WeakRvwmoConfWit2
import Weak.WeakEvProv

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

open Lean Elab Tactic Meta in
/-- (Lean-only, deviation 5) Close `lhs = rhs` by KERNEL defeq: `Eq.refl lhs` as an auxiliary
theorem abstracted over the local context (no elaborator-side check). -/
elab "weak_adm_krfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := tgt.eq? | throwError "weak_adm_krfl: the goal is not an equation"
    let pf ← mkEqRefl lhs
    let aux ← mkAuxTheorem tgt pf
    g.assign aux
    replaceMainGoal []

/-! ## 1. THE DEFINITIONAL BRIDGE: an all-admin `pevrun` IS an `admRun` -/

theorem admRunOfPevrun (instr : Bool) (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6)
    (d' : Efab) :
    pevrun ls p d p' d' → (∀ l ∈ ls, lbAdmin instr l) → admRun instr p d ls p' d' := by
  intro h
  induction h with
  | nil p d => intro _; exact .ARnil p d
  | more hs _ ih =>
    intro hall
    exact .ARcons _ _ _ _ _ _ _ _ (hall _ (List.mem_cons_self ..))
      hs (ih (fun l hl => hall l (List.mem_cons_of_mem _ hl)))

theorem pevrunOfAdmRun (instr : Bool) (ls : List Wlabel) (p : Pexv6) (d : Efab) (p' : Pexv6)
    (d' : Efab) :
    admRun instr p d ls p' d' → pevrun ls p d p' d' ∧ ∀ l ∈ ls, lbAdmin instr l := by
  intro h
  induction h with
  | ARnil p d => exact ⟨.nil p d, fun _ hl => absurd hl List.not_mem_nil⟩
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    refine ⟨.more hs ih.1, ?_⟩
    intro l0 hl0
    rcases List.mem_cons.1 hl0 with rfl | hl0
    · exact ha
    · exact ih.2 l0 hl0

/-! ## 2. THE REFLECTIVE CHECKER -/

abbrev aht : Type := (RegFile × Ibch) × SailM Unit

def ahRs (x : aht) : RegFile := x.1.1
def ahIb (x : aht) : Ibch := x.1.2
def ahM (x : aht) : SailM Unit := x.2

/-- The hart program state at an administrative cursor: no parked fence. -/
def ahP (cpu : CPU) (x : aht) : Pexv6 := .PHart cpu (ahM x) (ahRs x) none (ahIb x)

noncomputable def admNode (tick : Bool) (x : aht) : Option (Wlabel × aht) :=
  match x with
  | ((rs, ib), m) =>
    match m with
    | .pure _ => some (LInstr, ((rs, ibNone), riscvStep tick))
    | .impure (.error _) _ => none
    | .impure (.ok o) k =>
      match o, k with
      | .regRead r, k => some (LSilent, ((rs, ibRd ib r), k (rs r)))
      | .regWrite r v, k =>
          some (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r), ((rs.set r v, ib), k PUnit.unit))
      -- Q7: an sfence.vma announce is a graph event (the marker), not an admin step: stop
      | .instrAnnounce n w, k =>
          if sfAnnB n w then none else some (LInstr, ((rs, ibAnn (ibOfBvn w)), k ()))
      | .branchAnnounce _ _, k => some (LSilent, ((rs, ib), k ()))
      | .cacheOp _, k => some (LSilent, ((rs, ib), k ()))
      | .tlbi _, k => some (LSilent, ((rs, ib), k ()))
      | .takeException _, k => some (LSilent, ((rs, ib), k ()))
      | .returnException _, k => some (LSilent, ((rs, ib), k ()))
      | .translationStart _, k => some (LSilent, ((rs, ib), k ()))
      | .translationEnd _, k => some (LSilent, ((rs, ib), k ()))
      | .cycleCount, k => some (LSilent, ((rs, ib), k ()))
      | .message _, k => some (LSilent, ((rs, ib), k ()))
      | .getCycleCount, k => some (LSilent, ((rs, ib), k (0 : Nat)))
      | _, _ => none

noncomputable def admIter (tick : Bool) : Nat → aht → aht
  | 0, x => x
  | n + 1, x =>
    match admNode tick x with
    | some (_, y) => admIter tick n y
    | none => x

noncomputable def admLbls (tick : Bool) : Nat → aht → List Wlabel
  | 0, _ => []
  | n + 1, x =>
    match admNode tick x with
    | some (l, y) => l :: admLbls tick n y
    | none => []

/-- The stretch's LENGTH, i.e. where it stopped. -/
noncomputable def admCount (tick : Bool) : Nat → aht → Nat
  | 0, _ => 0
  | n + 1, x =>
    match admNode tick x with
    | some (_, y) => admCount tick n y + 1
    | none => 0

/-- A memory node's WIDTH and its address (width-free readbacks). -/
def ereadWidth (m : SailM Unit) : Option Nat :=
  match m with
  | .impure (.ok (.memRead n _ _)) _ => some n
  | _ => none

def ereadPaAt (m : SailM Unit) : Option Int :=
  match m with
  | .impure (.ok (.memRead _ _ rq)) _ => some (paZ rq.pa)
  | _ => none

/-- The three RESUME functions, at the administrative state. -/
def ahRead (v : Nat) (x : aht) : aht := ((ahRs x, ahIb x), ereadResume v (ahM x))
def ahWrite (x : aht) : aht := ((ahRs x, ahIb x), ewriteResume (ahM x))
def ahBar (x : aht) : aht := ((ahRs x, ahIb x), ebarResume (ahM x))

/-! ### 2.1 Soundness -/

/-- One `pnodeStep` arm, at the program tier: no parked fence, no fabric move. -/
theorem pstepEvNode (cpu : CPU) (d : Efab) (m m' : SailM Unit) (rs : RegFile) (ib : Ibch)
    (l : Wlabel) (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind) :
    pnodeStep m rs ib d.efDev l m' ors none d.efDev oib obar →
    pstepEv (.PHart cpu m rs none ib) d l (.PHart cpu m' (ors.getD rs) none (oib.getD ib)) d :=
  fun h => ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl ⟨h, rfl⟩⟩

/-- (Lean-only) every classified register write is administrative. -/
theorem WeakRvwmoAdm.lbAdminErwLabel (instr : Bool) (k : ErwKind) : lbAdmin instr (erwLabel k) := by
  cases k <;> trivial

theorem admNodePstep (tick : Bool) (cpu : CPU) (d : Efab) (x : aht) (l : Wlabel) (y : aht) :
    admNode tick x = some (l, y) →
    lbAdmin true l ∧ pstepEv (ahP cpu x) d l (ahP cpu y) d := by
  obtain ⟨⟨rs, ib⟩, m⟩ := x
  intro h
  match m, h with
  | .pure u, h =>
    simp only [admNode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, pstepEvNode cpu d _ _ rs ib LInstr none (some ibNone) none
      ⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | .impure (.error _) _, h => simp [admNode] at h
  | .impure (.ok o) k, h =>
    cases o <;> simp only [admNode, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case regRead r =>
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨trivial, pstepEvNode cpu d _ _ rs ib LSilent none (some (ibRd ib r)) none
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    case regWrite r v =>
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨WeakRvwmoAdm.lbAdminErwLabel true _,
        pstepEvNode cpu d _ _ rs ib _ (some (rs.set r v)) none none
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    case instrAnnounce a w =>
      cases hs : sfAnnB a w <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, pstepEvNode cpu d _ _ rs ib LInstr none (some (ibAnn (ibOfBvn w))) none
        ⟨(annLabelNot hs).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨trivial, pstepEvNode cpu d _ _ rs ib LSilent none none none
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- THE BRIDGE, once and for all: every computed stretch IS an `admRun`. -/
theorem admRunOfIter (tick : Bool) (n : Nat) (cpu : CPU) (d : Efab) (x : aht) :
    admRun true (ahP cpu x) d (admLbls tick n x) (ahP cpu (admIter tick n x)) d := by
  induction n generalizing x with
  | zero => exact .ARnil _ _
  | succ n ih =>
    rcases hn : admNode tick x with _ | ⟨l, y⟩
    · simp only [admLbls, admIter, hn]
      exact .ARnil _ _
    · simp only [admLbls, admIter, hn]
      obtain ⟨ha, hs⟩ := admNodePstep tick cpu d x l y hn
      exact .ARcons _ _ l _ _ _ _ _ ha hs (ih y)

/-- … and its `pevrun` form, which is what `WeakEvProv`'s kit consumes. -/
theorem pevrunOfIter (tick : Bool) (n : Nat) (cpu : CPU) (d : Efab) (x : aht) :
    pevrun (admLbls tick n x) (ahP cpu x) d (ahP cpu (admIter tick n x)) d :=
  (pevrunOfAdmRun true _ _ _ _ _ (admRunOfIter tick n cpu d x)).1

/-! ## 3. THE STRETCH — hart 1's spin load, and what follows it -/

noncomputable def laX0 : aht := ((ldRs0, ibNone), riscvStep false)
noncomputable def laX1 : aht := admIter false 400 laX0
noncomputable def laX2 : aht := admIter false 600 (ahRead ldWf.toNat laX1)
noncomputable def laX3 (w : BitVec 32) : aht := admIter false 200 (ahRead w.toNat laX2)

theorem WeakRvwmoAdm.laX2IsRead : (ereadReqAt 4 64 (ahM laX2)).isSome = true := by
  decide +kernel

theorem WeakRvwmoAdm.laX3IsRead : (ereadReqAt 2 64 (ahM (laX3 lockZero))).isSome = true := by
  decide +kernel

/-- The two requests, by readback of a total projection. -/
noncomputable def laReqd : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 4 64 (ahM laX2)).get WeakRvwmoAdm.laX2IsRead

noncomputable def laReqf : Mem_read_request 2 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 2 64 (ahM (laX3 lockZero))).get WeakRvwmoAdm.laX3IsRead

/-- (i) THE DATA LOAD: width 4 at `&started`, plain, RAM. -/
theorem laLoadReq : ereadReqAt 4 64 (ahM laX2) = some laReqd := (Option.some_get _).symm
theorem laLoadPa : laReqd.pa = evFlag := (by decide +kernel : @Eq PAddr laReqd.pa evFlag)
theorem laLoadPlain : classify laReqd.access_kind = ⟨false, false, false⟩ := by decide +kernel
theorem laLoadRam : devAddr laReqd.pa = false := by decide +kernel

/-- (ii) THE STRETCH ITSELF: 117 administrative nodes, UNIFORMLY IN THE WORD READ. -/
theorem laStretchLen (w : BitVec 32) : admCount false 200 (ahRead w.toNat laX2) = 117 := by
  weak_adm_krfl

/-- (iii) THE CARRIER, computed: the load's own destination-register write. -/
theorem laStretchRegw (w : BitVec 32) :
    (admLbls false 200 (ahRead w.toNat laX2))[0]? =
      some (LRegW 15 [.DLdRes, .DReg 14, .DReg 39, .DReg 45, .DReg 44]) := by
  weak_adm_krfl

/-- (iv) … AND IT CROSSES AN INSTRUCTION BOUNDARY: item 9 is the boundary's `LInstr`. -/
theorem laStretchInstr (w : BitVec 32) :
    (admLbls false 200 (ahRead w.toNat laX2))[9]? = some LInstr := by
  weak_adm_krfl

/-- (v) WHERE IT STOPS: the FETCH of the next instruction, `fence r,rw` at `main+0x18` -- width
2, an i-cache read (deviation 3), RAM. -/
theorem laFetchReq (w : BitVec 32) : ereadReqAt 2 64 (ahM (laX3 w)) = some laReqf := by
  weak_adm_krfl
theorem laFetchPlain : classify laReqf.access_kind = ⟨true, false, false⟩ := by decide +kernel
theorem laFetchRam : devAddr laReqf.pa = false := by decide +kernel
theorem laFetchPa : paZ laReqf.pa = 2147487462 := by decide +kernel
theorem laFlagPa : paZ evFlag = 2147525632 := by decide +kernel

/-! ## 4. THE TWO-EVENT ROW -/

/-- The fetched halfword at `main+0x18`: the low half of `fence r,rw` (`0x0230000f`). -/
def laTxt : BitVec 16 := BitVec.ofNat 16 0xf

/-- (Lean-only) … which IS the kernel image's. -/
theorem WeakRvwmoAdm.laTxtKw : kw ((KernelSyms.«main» : Int) + 0x18) % 0x10000 = laTxt.toNat := by
  decide +kernel

/-! ### 4.0 (Lean-only, deviation 3) past the fetch: the upper half and the fence

Under Stage C the fetch is ADMINISTRATIVE (no row item), so the row's second event is the next
genuine memory event after it: the `fence r,rw` at `main+0x18` itself, reached through the low
fetch, a stretch, the HIGH fetch (`0x0230`), and a second stretch. -/

/-- The upper fetched halfword at `main+0x1a`. -/
def WeakRvwmoAdm.laTxtHi : BitVec 16 := BitVec.ofNat 16 0x0230

/-- … the kernel image's too. -/
theorem WeakRvwmoAdm.laTxtHiKw :
    kw ((KernelSyms.«main» : Int) + 0x18) / 0x10000 % 0x10000 = WeakRvwmoAdm.laTxtHi.toNat := by
  decide +kernel

noncomputable def WeakRvwmoAdm.laX4 (w : BitVec 32) : aht := ahRead laTxt.toNat (laX3 w)
noncomputable def WeakRvwmoAdm.laX5 (w : BitVec 32) : aht :=
  admIter false 400 (WeakRvwmoAdm.laX4 w)
noncomputable def WeakRvwmoAdm.laX6 (w : BitVec 32) : aht :=
  admIter false 400 (ahRead WeakRvwmoAdm.laTxtHi.toNat (WeakRvwmoAdm.laX5 w))

theorem WeakRvwmoAdm.laX5IsRead :
    (ereadReqAt 2 64 (ahM (WeakRvwmoAdm.laX5 lockZero))).isSome = true := by
  decide +kernel

noncomputable def WeakRvwmoAdm.laReqh : Mem_read_request 2 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 2 64 (ahM (WeakRvwmoAdm.laX5 lockZero))).get WeakRvwmoAdm.laX5IsRead

/-- The HIGH fetch, uniformly in the word read: width 2, an i-cache read, RAM, at `main+0x1a`. -/
theorem WeakRvwmoAdm.laFetchHiReq (w : BitVec 32) :
    ereadReqAt 2 64 (ahM (WeakRvwmoAdm.laX5 w)) = some WeakRvwmoAdm.laReqh := by
  weak_adm_krfl
theorem WeakRvwmoAdm.laFetchHiPlain :
    classify WeakRvwmoAdm.laReqh.access_kind = ⟨true, false, false⟩ := by decide +kernel
theorem WeakRvwmoAdm.laFetchHiRam : devAddr WeakRvwmoAdm.laReqh.pa = false := by decide +kernel
theorem WeakRvwmoAdm.laFetchHiPa : paZ WeakRvwmoAdm.laReqh.pa = 2147487464 := by decide +kernel

/-- … and THE FENCE, uniformly in the word read. -/
theorem WeakRvwmoAdm.laBar (w : BitVec 32) :
    ebarAt (ahM (WeakRvwmoAdm.laX6 w)) = some .Barrier_RISCV_r_rw := by
  weak_adm_krfl

/-- A DATA-load node's step, once: the request's own width, address and kind, ANY word. -/
theorem ahLoadPstep (n va : Nat) (cpu : CPU) (d : Efab) (x : aht)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (tvs : List (Nat × BitVec 8)) (w : BitVec (8 * n)) :
    ereadReqAt n va (ahM x) = some req →
    devAddr req.pa = false →
    classify req.access_kind = ⟨false, false, false⟩ →
    tvs.length = n →
    (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    pstepEv (ahP cpu x) d (LLoad false false (paZ req.pa) tvs []) (ahP cpu (ahRead w.toNat x)) d := by
  intro hreq hram hcls hlen hbytes
  obtain ⟨K, Hm, Hres⟩ := ereadReqAtInv n va (ahM x) req hreq
  have Hm' : ahM (ahRead w.toNat x) = K (.Ok (w, none)) := Hres w
  have hstep := pstepEvNode cpu d (ahM x) (ahM (ahRead w.toNat x)) (ahRs x) (ahIb x)
    (LLoad false false (paZ req.pa) tvs []) none none none
  apply hstep
  rw [Hm', Hm]
  simp only [pnodeStep, hram, Bool.false_eq_true, if_false]
  refine Or.inr ⟨by rw [hcls], Or.inl ⟨by rw [hcls], w, tvs, hlen, hbytes, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  all_goals first | trivial | (rw [hcls])

/-- (Lean-only, deviation 3) … and a FETCH node's step: the i-cache arm, `LIFetch`. -/
theorem WeakRvwmoAdm.ahFetchPstep (n va : Nat) (cpu : CPU) (d : Efab) (x : aht)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (tvs : List (Nat × BitVec 8)) (w : BitVec (8 * n)) :
    ereadReqAt n va (ahM x) = some req →
    devAddr req.pa = false →
    (classify req.access_kind).akIfetch = true →
    tvs.length = n →
    (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    pstepEv (ahP cpu x) d (LIFetch (paZ req.pa) tvs) (ahP cpu (ahRead w.toNat x)) d := by
  intro hreq hram hif hlen hbytes
  obtain ⟨K, Hm, Hres⟩ := ereadReqAtInv n va (ahM x) req hreq
  have Hm' : ahM (ahRead w.toNat x) = K (.Ok (w, none)) := Hres w
  have hstep := pstepEvNode cpu d (ahM x) (ahM (ahRead w.toNat x)) (ahRs x) (ahIb x)
    (LIFetch (paZ req.pa) tvs) none none none
  apply hstep
  rw [Hm', Hm]
  simp only [pnodeStep, hram, Bool.false_eq_true, if_false]
  refine Or.inl ⟨hif, w, tvs, hlen, hbytes, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals trivial

/-- (Lean-only, deviation 3) a non-parking BARRIER node's step: `ebarLabel b`. -/
theorem WeakRvwmoAdm.ahBarPstep (cpu : CPU) (d : Efab) (x : aht) (b : barrier_kind) :
    ebarAt (ahM x) = some b → ebarPark b = none →
    pstepEv (ahP cpu x) d (ebarLabel b) (ahP cpu (ahBar x)) d := by
  intro hb hpk
  obtain ⟨K, Hm, Hres⟩ := ebarAtInv (ahM x) b hb
  have Hm' : ahM (ahBar x) = K () := Hres
  have hstep := pstepEvNode cpu d (ahM x) (ahM (ahBar x)) (ahRs x) (ahIb x) (ebarLabel b)
    none none (some b)
  apply hstep
  rw [Hm', Hm]
  exact ⟨rfl, rfl, rfl, hpk.symm, rfl, rfl, rfl⟩

/-- … and its axiomatic image, at any class. -/
theorem ahLoadRealizes (p : Pexv6) (ws : Wstate) (base : Int) (tvs : List (Nat × BitVec 8)) :
    hlblRealizes p ws (.LLoad false base (tvs.map Prod.fst) (tvs.map Prod.snd))
      (LLoad false false base tvs []) :=
  ⟨trivial, rfl, rfl, rfl⟩

/-- (Lean-only, deviation 3) a fence's image is the graph fence. -/
theorem WeakRvwmoAdm.ahFenceRealizes (p : Pexv6) (ws : Wstate) (pr pw sr sw : Bool) :
    hlblRealizes p ws (.LFence pr pw sr sw) (LFence pr pw sr sw) :=
  ⟨trivial, trivial, trivial, rfl⟩

/-- (Lean-only) administrative runs compose. -/
theorem WeakRvwmoAdm.admRunApp (instr : Bool) (p : Pexv6) (d : Efab) (ls1 : List Wlabel)
    (pm : Pexv6) (dm : Efab) (ls2 : List Wlabel) (p' : Pexv6) (d' : Efab) :
    admRun instr p d ls1 pm dm → admRun instr pm dm ls2 p' d' →
    admRun instr p d (ls1 ++ ls2) p' d' := by
  intro h1
  induction h1 with
  | ARnil p d => intro h2; exact h2
  | ARcons p d l p1 d1 ls q e ha hs _ ih =>
    intro h2
    exact .ARcons _ _ _ _ _ _ _ _ ha hs (ih h2)

/-- THE ITEMS: the load, the two ADMINISTRATIVE fetches, and the fence. -/
def laWl0 (t : Nat) (w : BitVec 32) : Wlabel := LLoad false false (paZ evFlag) (ldTvs t w) []

def laTvf : List (Nat × BitVec 8) := [(0, nthByte (n := 2) laTxt 0), (0, nthByte (n := 2) laTxt 1)]

noncomputable def laWl1 : Wlabel := LIFetch (paZ laReqf.pa) laTvf

def WeakRvwmoAdm.laTvh : List (Nat × BitVec 8) :=
  [(0, nthByte (n := 2) WeakRvwmoAdm.laTxtHi 0), (0, nthByte (n := 2) WeakRvwmoAdm.laTxtHi 1)]

noncomputable def WeakRvwmoAdm.laWlH : Wlabel := LIFetch (paZ WeakRvwmoAdm.laReqh.pa) WeakRvwmoAdm.laTvh

/-- The fence's label: `fence r,rw` = `ebarLabel .Barrier_RISCV_r_rw`. -/
def WeakRvwmoAdm.laWlF : Wlabel := LFence true false true true

/-- THE ROW — two events, in program order: the spin load and the `fence r,rw`. -/
def laRow (t : Nat) (w : BitVec 32) : List Lbl :=
  [.LLoad false (paZ evFlag) (ldTs t) (WeakRvwmoConfWit2.ldVs w), .LFence true false true true]

noncomputable def laLs (w : BitVec 32) : List Wlabel := admLbls false 200 (ahRead w.toNat laX2)

/-- (Lean-only) the whole administrative run between the two events. -/
noncomputable def WeakRvwmoAdm.laAdm (w : BitVec 32) : List Wlabel :=
  laLs w ++ laWl1 :: (admLbls false 400 (WeakRvwmoAdm.laX4 w) ++
    WeakRvwmoAdm.laWlH :: admLbls false 400 (ahRead WeakRvwmoAdm.laTxtHi.toNat (WeakRvwmoAdm.laX5 w)))

noncomputable def laP0 (cpu : CPU) : Pexv6 := ahP cpu laX2
noncomputable def laP1 (w : BitVec 32) (cpu : CPU) : Pexv6 := ahP cpu (ahRead w.toNat laX2)
noncomputable def laP2 (w : BitVec 32) (cpu : CPU) : Pexv6 := ahP cpu (laX3 w)
noncomputable def laP3 (w : BitVec 32) (cpu : CPU) : Pexv6 :=
  ahP cpu (ahRead laTxt.toNat (laX3 w))
/-- (Lean-only) at the fence node, and past it. -/
noncomputable def WeakRvwmoAdm.laP6 (w : BitVec 32) (cpu : CPU) : Pexv6 :=
  ahP cpu (WeakRvwmoAdm.laX6 w)
noncomputable def WeakRvwmoAdm.laPfin (w : BitVec 32) (cpu : CPU) : Pexv6 :=
  ahP cpu (ahBar (WeakRvwmoAdm.laX6 w))

noncomputable def laEm (t : Nat) (w : BitVec 32) (cpu : CPU) : Hemission :=
  ⟨(laWl0 t w, some 0) :: (eadm (WeakRvwmoAdm.laAdm w) ++ [(WeakRvwmoAdm.laWlF, some 1)]),
    WeakRvwmoAdm.laPfin w cpu⟩

/-- THE WITNESS.  The second block's administrative premise is a NON-EMPTY run: three computed
stretches (`admRunOfIter`) and the two fetch steps between them. -/
theorem laHartConf (i t : Nat) (w : BitVec 32) (cpu : CPU) (d0 : Efab) :
    hartConf i (laRow t w) (laP0 cpu) (fun _ => d0) (laEm t w cpu) := by
  have hld : pstepEv (laP0 cpu) d0 (laWl0 t w) (laP1 w cpu) d0 := by
    have h := ahLoadPstep 4 64 cpu d0 laX2 laReqd (ldTvs t w) w laLoadReq laLoadRam laLoadPlain
      rfl (by
        intro j hj
        rcases j with _ | _ | _ | _ | j
        · rfl
        · rfl
        · rfl
        · rfl
        · omega)
    rw [laLoadPa] at h
    exact h
  have hft : pstepEv (laP2 w cpu) d0 laWl1 (laP3 w cpu) d0 :=
    WeakRvwmoAdm.ahFetchPstep 2 64 cpu d0 (laX3 w) laReqf laTvf laTxt (laFetchReq w) laFetchRam
      (by rw [laFetchPlain]) rfl (by
        intro j hj
        rcases j with _ | _ | j
        · rfl
        · rfl
        · omega)
  have hfh : pstepEv (ahP cpu (WeakRvwmoAdm.laX5 w)) d0 WeakRvwmoAdm.laWlH
      (ahP cpu (ahRead WeakRvwmoAdm.laTxtHi.toNat (WeakRvwmoAdm.laX5 w))) d0 :=
    WeakRvwmoAdm.ahFetchPstep 2 64 cpu d0 (WeakRvwmoAdm.laX5 w) WeakRvwmoAdm.laReqh
      WeakRvwmoAdm.laTvh WeakRvwmoAdm.laTxtHi (WeakRvwmoAdm.laFetchHiReq w)
      WeakRvwmoAdm.laFetchHiRam (by rw [WeakRvwmoAdm.laFetchHiPlain]) rfl (by
        intro j hj
        rcases j with _ | _ | j
        · rfl
        · rfl
        · omega)
  have hbar : pstepEv (WeakRvwmoAdm.laP6 w cpu) d0 WeakRvwmoAdm.laWlF
      (WeakRvwmoAdm.laPfin w cpu) d0 :=
    WeakRvwmoAdm.ahBarPstep cpu d0 (WeakRvwmoAdm.laX6 w) .Barrier_RISCV_r_rw
      (WeakRvwmoAdm.laBar w) rfl
  have hadm : admRun true (laP1 w cpu) d0 (WeakRvwmoAdm.laAdm w) (WeakRvwmoAdm.laP6 w cpu) d0 :=
    WeakRvwmoAdm.admRunApp true _ d0 (laLs w) (laP2 w cpu) d0 _ _ d0
      (admRunOfIter false 200 cpu d0 (ahRead w.toNat laX2))
      (.ARcons _ _ laWl1 (laP3 w cpu) d0 _ _ _ rfl hft
        (WeakRvwmoAdm.admRunApp true _ d0 _ (ahP cpu (WeakRvwmoAdm.laX5 w)) d0 _ _ d0
          (admRunOfIter false 400 cpu d0 (WeakRvwmoAdm.laX4 w))
          (.ARcons _ _ WeakRvwmoAdm.laWlH _ d0 _ _ _ rfl hfh
            (admRunOfIter false 400 cpu d0
              (ahRead WeakRvwmoAdm.laTxtHi.toNat (WeakRvwmoAdm.laX5 w))))))
  exact hemit.HEone (dv := fun _ => d0) 0 wsInit
    (.LLoad false (paZ evFlag) (ldTs t) (WeakRvwmoConfWit2.ldVs w)) _ (laP0 cpu) [] (laP0 cpu) d0
    (laWl0 t w) (laP1 w cpu) _ (WeakRvwmoAdm.laPfin w cpu) (.ARnil _ _)
    (ahLoadRealizes (laP0 cpu) wsInit (paZ evFlag) (ldTvs t w)) hld
    (hemit.HEone 1 _ (.LFence true false true true) [] (laP1 w cpu) (WeakRvwmoAdm.laAdm w)
      (WeakRvwmoAdm.laP6 w cpu) d0 WeakRvwmoAdm.laWlF (WeakRvwmoAdm.laPfin w cpu) []
      (WeakRvwmoAdm.laPfin w cpu) hadm
      (WeakRvwmoAdm.ahFenceRealizes (WeakRvwmoAdm.laP6 w cpu) _ true false true true) hbar
      (.HEnil _ _ _))

/-! ### 4.1 The emission is fabric-free and dependency-free -/

def wlAdmok (l : Wlabel) : Bool :=
  match l with
  | LSilent | LRegW _ _ | LCtrl _ | LInstr => true
  | _ => false

theorem admNodeAdmok (tick : Bool) (x : aht) (l : Wlabel) (y : aht) :
    admNode tick x = some (l, y) → wlAdmok l = true := by
  obtain ⟨⟨rs, ib⟩, m⟩ := x
  intro h
  match m, h with
  | .pure u, h =>
    simp only [admNode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .impure (.error _) _, h => simp [admNode] at h
  | .impure (.ok o) k, h =>
    cases o <;> simp only [admNode, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case regWrite r v =>
      obtain ⟨rfl, rfl⟩ := h
      cases erwOf (depsOfIb ib.ibBits) ib.ibRds r <;> rfl
    case instrAnnounce a w =>
      cases hs : sfAnnB a w <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    all_goals
      obtain ⟨rfl, rfl⟩ := h
      rfl

theorem admLblsAdmok (tick : Bool) (n : Nat) (x : aht) : (admLbls tick n x).all wlAdmok = true := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rcases hn : admNode tick x with _ | ⟨l, y⟩
    · simp only [admLbls, hn]
      rfl
    · simp only [admLbls, hn, List.all_cons, admNodeAdmok tick x l y hn, Bool.true_and]
      exact ih y

theorem forallbElemOf {A : Type _} (f : A → Bool) (l : List A) (x : A) :
    l.all f = true → x ∈ l → f x = true := by
  intro hall hx
  exact List.all_eq_true.1 hall x hx

/-- `rowDeps` of a store-free item list is empty. -/
def itNostore (it : Eitem) : Bool :=
  match it.1 with
  | LStore .. | LExStore .. | LRmw .. => false
  | _ => true

theorem rowDepsAuxNostore (s : WeakRvwmoConf.Dstate) (es : List Eitem) :
    es.all itNostore = true → rowDepsAux s es = [] := by
  induction es generalizing s with
  | nil => intro _; rfl
  | cons it es ih =>
    intro hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hit, hall⟩ := hall
    obtain ⟨l, k⟩ := it
    have h2 : (WeakRvwmoConf.dstep s (l, k)).2 = [] := by
      cases l <;> simp only [itNostore, reduceCtorEq] at hit <;> cases k <;> rfl
    simp only [rowDepsAux, h2, List.nil_append]
    exact ih _ hall

theorem rowDepsNostore (es : List Eitem) : es.all itNostore = true → rowDeps es = [] :=
  rowDepsAuxNostore _ es

theorem eadmNostore (ls : List Wlabel) : ls.all wlAdmok = true → (eadm ls).all itNostore = true := by
  induction ls with
  | nil => intro _; rfl
  | cons l ls ih =>
    intro hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hl, hall⟩ := hall
    have := ih hall
    simp only [eadm, List.map_cons, List.all_cons] at this ⊢
    rw [this, Bool.and_true]
    cases l <;> first | rfl | exact absurd hl (by simp [wlAdmok])

/-- (Lean-only) the administrative run's labels: computed-stretch labels or one of the two
fetches. -/
theorem WeakRvwmoAdm.laAdmMem (w : BitVec 32) (l : Wlabel) :
    l ∈ WeakRvwmoAdm.laAdm w → wlAdmok l = true ∨ l = laWl1 ∨ l = WeakRvwmoAdm.laWlH := by
  intro h
  simp only [WeakRvwmoAdm.laAdm, List.mem_append, List.mem_cons] at h
  rcases h with h | h | h | h | h
  · exact Or.inl (forallbElemOf wlAdmok (laLs w) l (admLblsAdmok false 200 _) h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (forallbElemOf wlAdmok _ l (admLblsAdmok false 400 _) h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (forallbElemOf wlAdmok _ l (admLblsAdmok false 400 _) h)

theorem laEmItemsFst (t : Nat) (w : BitVec 32) (cpu : CPU) :
    emLabels (laEm t w cpu) = laWl0 t w :: (WeakRvwmoAdm.laAdm w ++ [WeakRvwmoAdm.laWlF]) := by
  simp only [emLabels, laEm, List.map_cons, List.map_append, eadmFst, List.map_nil]

theorem laEmDevfree (t : Nat) (w : BitVec 32) (cpu : CPU) : emDevfree (laEm t w cpu) := by
  unfold emDevfree
  rw [laEmItemsFst]
  intro kd ba bs sa sv h
  rcases List.mem_cons.1 h with h | h
  · simp [laWl0] at h
  · rcases List.mem_append.1 h with h | h
    · rcases WeakRvwmoAdm.laAdmMem w (LDev kd ba bs sa sv) h with hx | hx | hx
      · simp [wlAdmok] at hx
      · simp [laWl1] at hx
      · simp [WeakRvwmoAdm.laWlH] at hx
    · simp [WeakRvwmoAdm.laWlF] at h

theorem forallbNostoreShape (l0 l1 : Wlabel) (ls : List Wlabel) (k0 k1 : Nat) :
    itNostore (l0, some k0) = true → itNostore (l1, some k1) = true →
    ls.all wlAdmok = true →
    ((l0, some k0) :: (eadm ls ++ [(l1, some k1)])).all itNostore = true := by
  intro h0 h1 hls
  simp only [List.all_cons, List.all_append, h0, eadmNostore ls hls, h1, List.all_nil,
    Bool.and_self]

/-- (Lean-only) an administrative item list is store-free label by label. -/
theorem WeakRvwmoAdm.eadmAllNostore (ls : List Wlabel) :
    (∀ l, l ∈ ls → itNostore (l, none) = true) → (eadm ls).all itNostore = true := by
  intro h
  rw [List.all_eq_true]
  intro it hit
  simp only [eadm, List.mem_map] at hit
  obtain ⟨l, hl, rfl⟩ := hit
  exact h l hl

theorem laRowDepsEmpty (t : Nat) (w : BitVec 32) (cpu : CPU) :
    rowDeps (laEm t w cpu).emItems = [] := by
  apply rowDepsNostore
  have hadm : (eadm (WeakRvwmoAdm.laAdm w)).all itNostore = true := by
    apply WeakRvwmoAdm.eadmAllNostore
    intro l hl
    rcases WeakRvwmoAdm.laAdmMem w l hl with h | rfl | rfl
    · cases l <;> first | rfl | exact absurd h (by simp [wlAdmok])
    · rfl
    · rfl
  simp only [laEm, List.all_cons, List.all_append, hadm, List.all_nil]
  rfl

/-! ## 5. THE TWO-HART GRAPH WITH A TWO-EVENT ROW -/

noncomputable def laTxtPa : Int := paZ laReqf.pa

/-- The era image: the flag word CLEAR and the fence word `0x0230000f` at `main+0x18` (the two
fetched halves; deviation 3). -/
noncomputable def mp2Img : Image := fun a =>
  if paZ evFlag ≤ a ∧ a < paZ evFlag + 4 then some (nthByte (n := 4) lockZero (a - paZ evFlag).toNat)
  else if laTxtPa ≤ a ∧ a < laTxtPa + 2 then some (nthByte (n := 2) laTxt (a - laTxtPa).toNat)
  else if laTxtPa + 2 ≤ a ∧ a < laTxtPa + 4 then
    some (nthByte (n := 2) WeakRvwmoAdm.laTxtHi (a - (laTxtPa + 2)).toNat)
  else none

noncomputable def mp2 : Gexec :=
  ⟨mp2Img, [evRow, laRow 1 lockOne], [(0, 0), (1, 0)]⟩

noncomputable def mp2d : Gdexec := ⟨mp2, [], []⟩

/-- THE ADDRESS ARITHMETIC: the flag word and the fetched halfword do not overlap. -/
theorem laTxtPaVal : laTxtPa = 2147487462 := laFetchPa

theorem laBytesDisj (j j' : Nat) :
    j < 4 → j' < 2 → accAddr (paZ evFlag) j = accAddr laTxtPa j' → False := by
  intro hj hj' h
  unfold accAddr at h
  rw [laFlagPa, laTxtPaVal] at h
  omega

theorem mp2Lbl (e : Geid) (l : Lbl) :
    gxLbl mp2 e = some l →
    (e = (0, 0) ∧ l = .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain) ∨
    (e = (1, 0) ∧ l = .LLoad false (paZ evFlag) (ldTs 1) (WeakRvwmoConfWit2.ldVs lockOne)) ∨
    (e = (1, 1) ∧ l = .LFence true false true true) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i
  · rcases k with _ | k
    · simp only [gxLbl, mp2, evRow] at hl
      exact Or.inl ⟨rfl, (Option.some.inj hl).symm⟩
    · simp [gxLbl, mp2, evRow] at hl
  · rcases k with _ | _ | k
    · simp only [gxLbl, mp2, laRow] at hl
      exact Or.inr (Or.inl ⟨rfl, (Option.some.inj hl).symm⟩)
    · simp only [gxLbl, mp2, laRow] at hl
      exact Or.inr (Or.inr ⟨rfl, (Option.some.inj hl).symm⟩)
    · simp [gxLbl, mp2, laRow] at hl
  · simp [gxLbl, mp2] at hl

theorem mp2Pos (e : Geid) : (gxLbl mp2 e).isSome = true →
    e = (0, 0) ∨ e = (1, 0) ∨ e = (1, 1) := by
  intro h
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
  rcases mp2Lbl e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem mp2Noaq (e : Geid) : ¬ glblIs mp2 e lbAq := by
  rintro ⟨l, hl, haq⟩
  rcases mp2Lbl e l hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq

theorem mp2GpoInv (e1 e2 : Geid) :
    WeakRvwmoGraph.gpo mp2 e1 e2 → e1 = (1, 0) ∧ e2 = (1, 1) := by
  rintro ⟨hag, hlt, hs1, hs2⟩
  rcases mp2Pos e1 hs1 with rfl | rfl | rfl <;> rcases mp2Pos e2 hs2 with rfl | rfl | rfl <;>
    simp at hag hlt ⊢

theorem mp2Wr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte mp2 e a v →
    e = (0, 0) ∧ ∃ j : Nat, j < 4 ∧ a = accAddr (paZ evFlag) j ∧ v = nthByte (n := 4) lockOne j := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases mp2Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    obtain ⟨hj, rfl⟩ := WeakRvwmoConfWit2.wbytesLookupInv lockOne j v hv
    exact ⟨rfl, j, hj, ha.symm, rfl⟩
  · simp [lbWr] at hwr
  · simp [lbWr] at hwr

/-- The only read is the spin load (deviation 3: the fetch is no graph event). -/
theorem mp2Rd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte mp2 e a t v →
    e = (1, 0) ∧ t = 1 ∧
      ∃ j : Nat, j < 4 ∧ a = accAddr (paZ evFlag) j ∧ v = nthByte (n := 4) lockOne j := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases mp2Lbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    obtain ⟨hj, rfl⟩ := WeakRvwmoConfWit2.ldVsLookup lockOne j v hv
    exact ⟨rfl, WeakRvwmoConfWit2.ldTsLookup 1 j t ht, j, hj, ha.symm, rfl⟩
  · simp [lbRd] at hrd

theorem mp2ImgTxt (j : Nat) : j < 2 → mp2Img (accAddr laTxtPa j) = some (nthByte (n := 2) laTxt j) := by
  intro hj
  have hf := laFlagPa
  have ht := laTxtPaVal
  unfold mp2Img accAddr
  rw [if_neg (by omega), if_pos (by omega), show (laTxtPa + (j : Int) - laTxtPa).toNat = j by omega]

/-- (Lean-only) … and the upper half. -/
theorem WeakRvwmoAdm.mp2ImgTxtHi (j : Nat) :
    j < 2 → mp2Img (accAddr (laTxtPa + 2) j) = some (nthByte (n := 2) WeakRvwmoAdm.laTxtHi j) := by
  intro hj
  have hf := laFlagPa
  have ht := laTxtPaVal
  unfold mp2Img accAddr
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (laTxtPa + 2 + (j : Int) - (laTxtPa + 2)).toNat = j by omega]

theorem mp2Gwrites : gwrites mp2 = [(0, 0)] := by decide +kernel
theorem mp2Gwix0 : gwix mp2 (0, 0) = 1 := by decide +kernel
theorem mp2WriteAt1 : gwriteAt mp2 1 = some (0, 0) := by decide +kernel

theorem mp2Gvis0 : gvisible mp2 (0, 0) (1, 0) :=
  Or.inl ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem mp2PpoGmo : gppoGmo mp2 := by
  intro e1 e2 h
  exfalso
  rcases h with hloc | hf | hacq | hrel
  · obtain ⟨hpo, a, _, ha2⟩ := hloc
    obtain ⟨rfl, rfl⟩ := mp2GpoInv e1 e2 hpo
    rcases ha2 with ⟨v2, hw2⟩ | ⟨t2, v2, hr2⟩
    · exact absurd (mp2Wr _ _ _ hw2).1 (by simp)
    · exact absurd (mp2Rd _ _ _ _ hr2).1 (by simp)
  · obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, hk1, hk2, _⟩, _, h2r⟩ := hf
    have hs2 : (gxLbl mp2 e2).isSome = true := by
      rcases h2r with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> rw [hl] <;> rfl
    rcases mp2Pos e2 hs2 with rfl | rfl | rfl <;> dsimp only at hk2 <;> omega
  · exact mp2Noaq e1 hacq.2.2.1
  · -- rule 7 (D35-fix [OWN.54]: riscv.cat's RCsc `grcsc`): `mp2` carries no annotated access
    obtain ⟨_, ⟨l, hl, hrc⟩, _⟩ := hrel
    rcases mp2Lbl e1 l hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbRcsc, lbAq, lbRl] at hrc

theorem mp2Consistent : rvwmoMinusConsistent mp2 := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, mp2PpoGmo, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      simp only [mp2, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, hm⟩
      rcases mp2Lbl e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, rfl⟩
      · simp [mp2]
      · simp [mp2]
      · simp [lbIsMem, lbIsR, lbIsW, lbIsIo] at hm
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [mp2] at hp <;> subst hp
    · rcases k with _ | k <;> simp [evRow] at hk
      subst hk
      exact wbytesNonnil 4 lockOne (by decide)
    · rcases k with _ | _ | k <;> simp [laRow] at hk <;> subst hk <;> first | rfl | trivial
  · intro e a t v hrd
    obtain ⟨rfl, rfl, j, hj, rfl, rfl⟩ := mp2Rd e a t v hrd
    refine ⟨⟨(0, 0), mp2WriteAt1, ⟨_, paZ evFlag, WeakInterpProj.wbytes 4 lockOne, j, rfl, rfl,
      wbytesLookup 4 (m := 4) lockOne j hj, rfl⟩, mp2Gvis0⟩, ?_⟩
    intro w' v' hw' _
    obtain ⟨rfl, _⟩ := mp2Wr w' _ v' hw'
    rw [mp2Gwix0]
    exact Nat.le_refl _
  · intro e a t v hrd hw
    obtain ⟨l, hl, hlw⟩ := hw
    obtain ⟨rfl, _⟩ := mp2Rd e a t v hrd
    have hl0 : gxLbl mp2 (1, 0) =
        some (.LLoad false (paZ evFlag) (ldTs 1) (WeakRvwmoConfWit2.ldVs lockOne)) := rfl
    rw [hl0] at hl
    cases hl
    simp [lbIsW] at hlw

theorem mp2DepsConsistent : rvwmoMinusDepsConsistent mp2d :=
  ⟨mp2Consistent, fun _ h => by simp [mp2d] at h, fun _ h => by simp [mp2d] at h⟩

/-! ### 5.1 THE BUNDLE — the first `gdexecQconf` with a two-event row -/

/-- (Lean-only, deviation 3) THE FETCH PIN: both administrative fetches of the emission read
the image at timestamp 0 (`laTxtKw` / `laTxtHiKw`: the very bytes of the kernel image). -/
theorem WeakRvwmoAdm.laEmFetchImg (t : Nat) (w : BitVec 32) (cpu : CPU) :
    emFetchImg mp2Img (laEm t w cpu) := by
  have hpa : paZ WeakRvwmoAdm.laReqh.pa = laTxtPa + 2 := by
    rw [WeakRvwmoAdm.laFetchHiPa, laTxtPaVal]
    decide
  intro l hl
  rw [laEmItemsFst] at hl
  rcases List.mem_cons.1 hl with rfl | hl
  · trivial
  rcases List.mem_append.1 hl with hl | hl
  · rcases WeakRvwmoAdm.laAdmMem w l hl with h | rfl | rfl
    · cases l <;> first | trivial | exact absurd h (by simp [wlAdmok])
    · show (∀ t ∈ laTvf.map Prod.fst, t = 0) ∧
        ∀ j, j < laTvf.length → mp2Img (laTxtPa + (j : Int)) = (laTvf.map Prod.snd)[j]?
      refine ⟨fun t ht => by simp [laTvf] at ht; omega, fun j hj => ?_⟩
      have hj2 : j < 2 := hj
      rw [show laTxtPa + (j : Int) = accAddr laTxtPa j from rfl, mp2ImgTxt j hj2]
      rcases j with _ | _ | j
      · rfl
      · rfl
      · omega
    · show (∀ t ∈ WeakRvwmoAdm.laTvh.map Prod.fst, t = 0) ∧
        ∀ j, j < WeakRvwmoAdm.laTvh.length →
          mp2Img (paZ WeakRvwmoAdm.laReqh.pa + (j : Int)) = (WeakRvwmoAdm.laTvh.map Prod.snd)[j]?
      refine ⟨fun t ht => by simp [WeakRvwmoAdm.laTvh] at ht; omega, fun j hj => ?_⟩
      have hj2 : j < 2 := hj
      rw [hpa, show laTxtPa + 2 + (j : Int) = accAddr (laTxtPa + 2) j from rfl,
        WeakRvwmoAdm.mp2ImgTxtHi j hj2]
      rcases j with _ | _ | j
      · rfl
      · rfl
      · omega
  · rw [List.mem_singleton] at hl
    subst hl
    trivial

noncomputable def mp2Boot (cpu0 cpu1 : CPU) (rs0 : RegFile) (ib0 : Ibch) : Nat → Pexv6 :=
  fun i =>
    match i with
    | 0 => evP0 cpu0 rs0 ib0
    | 1 => laP0 cpu1
    | _ => .PDisk none

theorem mp2Qconf (cpu0 cpu1 : CPU) (rs0 : RegFile) (ib0 : Ibch) (d0 : Efab) :
    gdexecQconf (mp2Boot cpu0 cpu1 rs0 ib0) d0 mp2Img 2 mp2d := by
  refine ⟨rfl, by decide +kernel, ?_⟩
  intro i row hrow
  rcases i with _ | _ | i
  · obtain rfl : evRow = row := Option.some.inj hrow
    exact ⟨evEm cpu0 rs0 ib0, evHartConf _ _ _ _ _, evEmDevfree _ _ _,
      WeakRvwmoConfWit2.evEmFetchImg _ _ _ _,
      fun jk hjk => (evRowDepsEmpty cpu0 rs0 ib0 jk hjk).elim⟩
  · obtain rfl : laRow 1 lockOne = row := Option.some.inj hrow
    refine ⟨laEm 1 lockOne cpu1, laHartConf _ _ _ _ _, laEmDevfree _ _ _,
      WeakRvwmoAdm.laEmFetchImg _ _ _, ?_⟩
    intro jk hjk
    rw [laRowDepsEmpty 1 lockOne cpu1] at hjk
    exact absurd hjk List.not_mem_nil
  · simp [mp2d, mp2] at hrow

/-! ## 6. THE CONTROL CARRIER — the taken `beqz` at `main+0x1e` -/

noncomputable def lcX4 : aht := ahRead laTxt.toNat (laX3 lockZero)
noncomputable def lcX5 : aht := admIter false 400 lcX4
noncomputable def lcX6 : aht := admIter false 400 (ahRead 0x0230 lcX5)
noncomputable def lcX7 : aht := admIter false 400 (ahBar lcX6)
noncomputable def lcX8 : aht := admIter false 400 (ahRead 0x2781 lcX7)
noncomputable def lcSt : aht := ahRead 0x00efdfe5 lcX8
noncomputable def lcX9 : aht := admIter false 400 lcSt

/-- The four intervening nodes: two fetch halves of the fence, the barrier, the `c.addiw`'s
fetch (and the branch's aligned fetch). -/
theorem lcFetchHi : ereadWidth (ahM lcX5) = some 2 := by weak_adm_krfl
theorem lcBar : ebarAt (ahM lcX6) = some .Barrier_RISCV_r_rw := by weak_adm_krfl
theorem lcBarNopark : ebarPark .Barrier_RISCV_r_rw = none := rfl
theorem lcFetchAddiw : ereadWidth (ahM lcX7) = some 2 := by weak_adm_krfl
theorem lcFetchBeqz : ereadWidth (ahM lcX8) = some 4 := by weak_adm_krfl

/-- THE STRETCH AT THE BRANCH: 128 administrative nodes, ending at the LOOP-BACK fetch. -/
theorem lcStretchLen : admCount false 400 lcSt = 128 := by weak_adm_krfl

theorem lcLoopBack : ereadWidth (ahM lcX9) = some 4 := by weak_adm_krfl

theorem lcLoopBackPa : ereadPaAt (ahM lcX9) = some 2147487460 := by weak_adm_krfl

/-- THE CARRIER, computed: item 12 of that stretch. -/
theorem lcCtrl : (admLbls false 400 lcSt)[12]? = some (LCtrl [.DReg 15]) := by weak_adm_krfl

/-- … and it lies inside a genuine `admRun`, by §2's bridge. -/
theorem lcCtrlInRun (cpu : CPU) (d : Efab) :
    ∃ ls, admRun true (ahP cpu lcSt) d ls (ahP cpu lcX9) d ∧ LCtrl [.DReg 15] ∈ ls :=
  ⟨admLbls false 400 lcSt, admRunOfIter false 400 cpu d lcSt, List.mem_of_getElem? lcCtrl⟩

end Weak
