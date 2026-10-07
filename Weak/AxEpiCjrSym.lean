/-
Weak: the `c.jr ra` LEDGER FOR A SYMBOLIC RETURN ADDRESS: after the epilogue's reload
`c.ldsp ra,8(sp)` the value of `x1` is whatever the (demonic) load returned, so `c.jr` is verified
for EVERY `ra`.  State `tWithRa ra` = `AxEpiProbe.probeRegs pcJr` with `x1 := ra`; `pcJr` is
4-aligned, so the model fetches 4 bytes there (`cjrVs4`, cf. `AxEpiProbe.q2CjrFalse`).  Post:
`postRaSym ra` -- PC = `jalrTarget ra`, the model's own `ra + sext 0` with bit 0 cleared
(`jalrTargetSpec`: value `ra - ra % 2`).  `riscvStep true` is NOT covered (as Rocq).

Rocq: `iris/AxEpiCjrSym.v` @ xxvzwolszwmp.

## The Rocq method, and the Lean one

Rocq: `vm_compute` is stuck on `jump_to`'s two bit tests of the symbolic target (a wrapping
`bv` op on a symbolic word does not compute), so `execute_JALR` is rewritten
(`execute_JALR_s_eq`) to `execute_JALR_gen` over wrap-free STRUCTURAL twins `b0_s`/`b1_s`/`T_s`
(`clear0`: a match on the `positive`), `ra = BV z pf` is split on `z`'s last two constructors, and
each case is `vm_compute`d, the comparison `pc_eqb` generalised to `E` with `E x x = true`.

Lean: no representation of a free `BitVec 64` makes a bit test reduce in the kernel (`Nat`
arithmetic on a non-literal is stuck), so the case split is on the STUCK TESTS THEMSELVES.
`branchSym` unfolds the step down to `execute`, rewrites `executeJALRSEq` and `tgtImm0` (as Rocq),
generalises `pcEqb` to `E` (as Rocq) and the two bit-test functions `b0S`/`b1S` to free functions
`A0`/`A1`.  Then the KERNEL evaluates the whole ledger branch with `ra` free; it can only stop at
an application of a free function.  Lean-only tactics: `ax_epi_cjr_sym_kcases h` replaces the goal
`lhs = true` by its kernel spine (`AxEpiCjrSym.kspine`: `Kernel.whnf`, recursively into the stuck
major premise of each recursor / struct of each projection; `lhs = spine` an auxiliary
kernel-`Eq.refl` theorem) and cases on the stuck leaf (`A0 tgt`: the `false` arm is absurd by
`AxEpiCjrSym.b0SAligned`; then `A1 tgt`: both arms continue); `ax_epi_cjr_sym_kclose HE` closes
the final leaf `E pc (clear0 ra)` by `HE (clear0 ra)`, the kernel checking `pc ≡ clear0 ra`.
`ax_epi_cjr_sym_kshow` is a diagnostic (logs the leaf).  REUSE these for later symbolic-`ra`
branches (AxEpiCjrFrame, AxLdgSeal …): generalise every function whose application on the
symbolic word sits in monad position, then `kcases`/`kclose`.  `branchSym` needs
`maxHeartbeats 1000000` (Meta bookkeeping on the spine terms); the file builds in ~40 s.

## Deviations from Rocq

1. Two pin answers (`AxEpiLedger` deviation 1): `branchSym ra v' v` (meip answer `v'`, seip `v`);
   the ledger instance uses `AxEpiProbe.drNopin` for `Dr_noseip` and four branch fields.
2. O2 Stage C (`AxEpiLedger` deviation 3): `wpdCjrSym` takes `Hgd` as `AxCjrWpd.fetchImgOk`;
   `Hflow`/`Hloc` are dropped; `RetS` at `kk` (Rocq `S kk`); generic `hlc` (Rocq `HasNoLc`).
3. Types: `mword 64` ↦ `BitVec 64`, `Z` ↦ `Int`/`Nat`.  `clear0_Z` (a match on the `positive`)
   ↦ `if 0 ≤ z then z - z % 2 else z` (same function; structurality is moot in Lean);
   `clear0_wf` ↦ the range fact `(clear0Z x.toNat).toNat < 2 ^ 64`; `b0_s`/`b1_s` use
   `Nat.testBit`; `T_s`'s `bool_decide` ↦ `if`; `pc_eqb` ↦ `decide`.  `extract_bit_unsigned` /
   `eq_vec_bit` lose the premise `0 ≤ i` (Lean index `i : Nat`; true for every `i`) and state
   `toNat` (Rocq `bv_unsigned`); `eq_vec` ↦ `==`, `Z.eqb (Z.b2z …)` ↦ `(… .toNat == …)`.
   `jalrTargetSpec` is stated in `Nat` (`r.toNat - r.toNat % 2`, exact since `r % 2 ≤ r`).
4. `JGen.jump_to_gen`/`execute_JALR_gen` follow the LEAN model's `jump_to`/`execute_JALR`
   (`SailME.run`, `Functions.not`); `execute_JALR_gen_eq` holds by kernel `Eq.refl`
   (`ax_epi_ledger_krfl`; Meta `rfl` hits the recursion limit).  `b0_real` ↦
   `Sail.BitVec.access t 0 == 0#1`.
5. `vm_compute; reflexivity` ↦ `decide +kernel` (closed fields) / `ax_epi_ledger_krfl`
   (`lfToSeip`, `ra` free) / the spine tactics (branches).

**Rocq → Lean name map.**  `t_with_ra` `tWithRa`, `cjr_vs4` `cjrVs4`, `JGen.jump_to_gen`
`jumpToGen`, `JGen.b0_real` `b0Real`, `JGen.b1_real` `b1Real`, `JGen.tgt_real` `tgtReal`,
`JGen.execute_JALR_gen` `executeJALRGen`, `JGen.execute_JALR_gen_eq` `executeJALRGenEq`,
`JGen.imm0` `AxEpiCjrSym.imm0` (dup), `clear0_Z` `clear0Z`, `clear0_Z_bounds` `clear0ZBounds`,
`clear0_wf` `clear0Wf`, `clear0` `clear0`, `b0_s` `b0S`, `b1_s` `b1S`, `T_s` `TS`,
`extract_bit_unsigned` `extractBitUnsigned`, `eq_vec_bit` `eqVecBit`, `b0_eq` `b0Eq`, `b1_eq`
`b1Eq`, `tgt_imm0` `tgtImm0`, `T_s_eq` `TSEq`, `execute_JALR_s_eq` `executeJALRSEq`, `pc_eqb`
`pcEqb`, `pc_eqb_refl` `pcEqbRefl`, `jalr_target` `jalrTarget`, `post_ra_sym` `postRaSym`,
`branch_sym` `branchSym`, `jalr_target_spec` `jalrTargetSpec`, `epi_ledger_cjr_sym`
`epiLedgerCjrSym`, `wpd_cjr_sym` `wpdCjrSym`.  Lean-only: `AxEpiCjrSym.b0SAligned`,
`AxEpiCjrSym.kspine`, `AxEpiCjrSym.kspineGoal`, tactics `ax_epi_cjr_sym_kshow`,
`ax_epi_cjr_sym_kcases`, `ax_epi_cjr_sym_kclose`.

**Dropped:** nothing (Rocq 31 definitions/lemmas; Lean 31 + 3 Lean-only + 3 tactics).
`Set Printing Depth` / `Time` have no twin.
-/
import Weak.AxEpiLedger

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-- Rocq `t_with_ra`: the probe state at `pcJr` with `x1 := ra`. -/
def tWithRa (ra : BitVec 64) : ExecSt := ⟨(probeRegs pcJr).set .x1 ra, probeMem, testDevs⟩

/-- Rocq `cjr_vs4`: the 4 bytes fetched at the 4-aligned `pcJr` (c.jr and the next halfword). -/
def cjrVs4 : List (BitVec 8) := [0x82#8, 0x80#8, 0x82#8, 0x80#8]

/-! ## 1. `execute_JALR` with the ra-dependent pieces abstracted (Rocq `Module JGen`) -/

/-- Rocq `JGen.jump_to_gen`: `jump_to` with its two bit tests abstracted. -/
def jumpToGen (b0 b1 : BitVec 64 → Bool) (target : BitVec 64) : SailM ExecutionResult :=
  SailME.run do
  match (ext_control_check_pc target) with
  | .some e => SailME.throw ((.Ext_ControlAddr_Check_Failure e) : ExecutionResult)
  | none => (pure ())
  assert (b0 target) "extensions/I/base_insts.sail:59.25-59.26"
  if ((← do
       if ((b1 target) : Bool)
       then (pure (Functions.not (← (currentlyEnabled .Ext_Zca))))
       else (pure false)) : Bool)
  then (memory_exception (.Virtaddr target) (.E_Fetch_Addr_Align ()))
  else
    (do
      (set_next_pc target)
      (pure RETIRE_SUCCESS))

/-- Rocq `JGen.b0_real`. -/
def b0Real (target : BitVec 64) : Bool := (Sail.BitVec.access target 0) == 0#1
/-- Rocq `JGen.b1_real`. -/
def b1Real (target : BitVec 64) : Bool := bit_to_bool (Sail.BitVec.access target 1)
/-- Rocq `JGen.tgt_real`. -/
def tgtReal (w : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  Sail.BitVec.update (w + sign_extend (m := 64) imm) 0 0#1

/-- Rocq `JGen.execute_JALR_gen`. -/
def executeJALRGen (b0 b1 : BitVec 64 → Bool) (T : BitVec 64 → BitVec 12 → BitVec 64)
    (imm : BitVec 12) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (update_elp_state rs1)
  let link_address ← do (get_next_pc ())
  let w ← rX_bits rs1
  match (← (jumpToGen b0 b1 (T w imm))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (.Retire_Success ())))
  | failure => (pure failure)

theorem executeJALRGenEq : execute_JALR = executeJALRGen b0Real b1Real tgtReal := by
  ax_epi_ledger_krfl

/-- Rocq `JGen.imm0`. -/
def AxEpiCjrSym.imm0 : BitVec 12 := zeros (n := 12)


/-! ## 2. The twins of the three ra-dependent functions -/

/-- Rocq `clear0_Z`: clear bit 0 of a non-negative integer (identity on negatives). -/
def clear0Z (z : Int) : Int := if 0 ≤ z then z - z % 2 else z

theorem clear0ZBounds (z : Int) : 0 ≤ z → 0 ≤ clear0Z z ∧ clear0Z z ≤ z := by
  intro hz; unfold clear0Z; split <;> omega

theorem clear0Wf (x : BitVec 64) : (clear0Z (x.toNat : Int)).toNat < 2 ^ 64 := by
  have := x.isLt; unfold clear0Z; split <;> omega

/-- Rocq `clear0`. -/
def clear0 (x : BitVec 64) : BitVec 64 := BitVec.ofFin ⟨(clear0Z (x.toNat : Int)).toNat, clear0Wf x⟩

/-- Rocq `b0_s`. -/
def b0S (x : BitVec 64) : Bool := !(x.toNat.testBit 0)
/-- Rocq `b1_s`. -/
def b1S (x : BitVec 64) : Bool := x.toNat.testBit 1
/-- Rocq `T_s`. -/
def TS (x : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  if imm = AxEpiCjrSym.imm0 then clear0 x else tgtReal x imm

theorem extractBitUnsigned (x : BitVec 64) (i : Nat) :
    (Sail.BitVec.access x i).toNat = (x.toNat.testBit i).toNat := by
  unfold Sail.BitVec.access
  by_cases h : i < 64
  · simp [h, BitVec.getElem_eq_testBit_toNat]
  · have : x.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [h, this]

theorem eqVecBit (x : BitVec 64) (i : Nat) (c : BitVec 1) :
    (Sail.BitVec.access x i == c) = ((x.toNat.testBit i).toNat == c.toNat) := by
  rw [← extractBitUnsigned x i]
  cases h : (Sail.BitVec.access x i == c) <;> simp_all [BitVec.toNat_eq]

theorem b0Eq (x : BitVec 64) : b0Real x = b0S x := by
  unfold b0Real b0S; rw [eqVecBit]; cases x.toNat.testBit 0 <;> rfl

theorem b1Eq (x : BitVec 64) : b1Real x = b1S x := by
  have h : Sail.BitVec.access x 1 = BitVec.ofBool (x.toNat.testBit 1) := by
    apply BitVec.eq_of_toNat_eq; rw [extractBitUnsigned, BitVec.toNat_ofBool]
  unfold b1Real b1S; rw [h]; cases x.toNat.testBit 1 <;> rfl

theorem tgtImm0 (x : BitVec 64) : tgtReal x AxEpiCjrSym.imm0 = clear0 x := by
  have h1 : Sail.BitVec.update x 0 0#1 = x - (x &&& 1#64) := by
    unfold Sail.BitVec.update Sail.BitVec.updateSubrange'; bv_decide
  have hs : sign_extend (m := 64) AxEpiCjrSym.imm0 = 0#64 := by decide +kernel
  unfold tgtReal; rw [hs, BitVec.add_zero, h1]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have ha : (x &&& 1#64).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
  rw [BitVec.toNat_sub, ha]
  show _ = (clear0Z (x.toNat : Int)).toNat
  unfold clear0Z; split <;> omega

theorem TSEq : tgtReal = TS := by
  funext x imm; unfold TS
  by_cases h : imm = AxEpiCjrSym.imm0
  · subst h; simp [tgtImm0]
  · simp [h]

theorem executeJALRSEq : execute_JALR = executeJALRGen b0S b1S TS := by
  rw [executeJALRGenEq, ← TSEq]
  have e0 : b0Real = b0S := funext b0Eq
  have e1 : b1Real = b1S := funext b1Eq
  rw [e0, e1]

/-- Rocq `pc_eqb`. -/
def pcEqb (x y : BitVec 64) : Bool := decide (x = y)
theorem pcEqbRefl (x : BitVec 64) : pcEqb x x = true := by simp [pcEqb]

/-- Rocq `jalr_target`: the model's jalr target for `c.jr ra`, `(ra + sext 0)` with bit 0 cleared. -/
def jalrTarget (r : BitVec 64) : BitVec 64 := tgtReal r AxEpiCjrSym.imm0
/-- Rocq `post_ra_sym`. -/
def postRaSym (r : BitVec 64) (rs : RegFile) : Bool := pcEqb (rs .PC) (jalrTarget r)

/-- (Lean-only) every twin target has bit 0 clear. -/
theorem AxEpiCjrSym.b0SAligned (w : BitVec 64) (imm : BitVec 12) : b0S (TS w imm) = true := by
  rw [← TSEq, ← b0Eq]
  unfold b0Real tgtReal Sail.BitVec.update Sail.BitVec.updateSubrange' Sail.BitVec.access
  simp

/-! ## 3. Kernel spine tactics (Lean-only) -/

open Lean Meta in
/-- (Lean-only) The kernel's weak head normal form of `e`, with the stuck major premise of every
recursor (and the struct of every projection) on the spine recursively normalised; returns the
rebuilt term (definitionally `e`) and the innermost stuck term. -/
partial def AxEpiCjrSym.kspine (env : Environment) (lctx : LocalContext) (e : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let w ← ofExceptKernelException (Kernel.whnf env lctx e)
  let f := w.getAppFn
  match f with
  | .proj s i b =>
    let (b', l) ← AxEpiCjrSym.kspine env lctx b
    return (mkAppN (.proj s i b') w.getAppArgs, l)
  | _ =>
    match f with
    | .const n _ =>
      match env.find? n with
      | some (.recInfo rv) =>
        let args := w.getAppArgs
        let mi := rv.getMajorIdx
        if h : mi < args.size then
          let (m', l) ← AxEpiCjrSym.kspine env lctx args[mi]
          return (mkAppN f (args.set mi m'), l)
        else return (w, w)
      | _ => return (w, w)
    | _ => return (w, w)

open Lean Elab Tactic Meta in
/-- (Lean-only) Replace the goal `lhs = rhs` by `W = rhs`, `W` the kernel spine of `lhs`
(`AxEpiCjrSym.kspine`), via an auxiliary kernel-checked theorem `lhs = W`; returns the new goal
and the stuck leaf. -/
def AxEpiCjrSym.kspineGoal (g : MVarId) : MetaM (MVarId × Lean.Expr) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.consumeMData
  let some (_, lhs, rhs) := tgt.eq? | throwError "kspine: the goal is not an equation: {tgt.getAppFn} {tgt.getAppNumArgs}"
  let (W, leaf) ← AxEpiCjrSym.kspine (← getEnv) (← getLCtx) lhs
  let aux ← mkAuxTheorem (← mkEq lhs W) (← mkEqRefl lhs)
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq W rhs) (← g.getTag)
  g.assign (← mkEqTrans aux g')
  return (g'.mvarId!, leaf)

open Lean Elab Tactic Meta in
/-- (Lean-only, diagnostic) Replace the goal by its kernel spine and show the stuck leaf. -/
elab "ax_epi_cjr_sym_kshow" : tactic => do
  let (g', leaf) ← AxEpiCjrSym.kspineGoal (← getMainGoal)
  replaceMainGoal [g']
  logInfo m!"leaf: {leaf}"

open Lean Elab Tactic Meta in
/-- (Lean-only) Case on the (Bool) stuck leaf of the goal's kernel spine, with hypothesis `h`. -/
elab "ax_epi_cjr_sym_kcases " h:ident : tactic => do
  let (g', leaf) ← AxEpiCjrSym.kspineGoal (← getMainGoal)
  let gs ← g'.withContext do
    let gT ← instantiateMVars (← g'.getType)
    let mk (c : Lean.Expr) : Lean.Expr := gT.replace fun e => if e == leaf then some c else none
    let bTy := mkConst ``Bool
    let motive ← withLocalDeclD `b bTy fun b => do
      mkLambdaFVars #[b] (← mkArrow (← mkEq leaf b) (mk b))
    let ff := mkConst ``Bool.false
    let tt := mkConst ``Bool.true
    let mF ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← mkEq leaf ff) (mk ff))
    let mT ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← mkEq leaf tt) (mk tt))
    let pf := mkApp (mkAppN (mkConst ``Bool.rec [Level.zero]) #[motive, mF, mT, leaf])
      (← mkEqRefl leaf)
    g'.assign pf
    let (_, gF) ← mF.mvarId!.intro h.getId
    let (_, gT') ← mT.mvarId!.intro h.getId
    return [gF, gT']
  replaceMainGoal gs

open Lean Elab Tactic Meta in
/-- (Lean-only) Close a goal whose kernel spine is `E a b = rhs` with `HE b`, the kernel
checking `a ≡ b`. -/
elab "ax_epi_cjr_sym_kclose " t:term : tactic => do
  let (g', leaf) ← AxEpiCjrSym.kspineGoal (← getMainGoal)
  g'.withContext do
    let args := leaf.getAppArgs
    unless args.size ≥ 1 do throwError "kclose: leaf {leaf} is not an application"
    let h ← elabTerm t none
    let pf := mkApp h args[args.size - 1]!
    g'.assign (← mkExpectedTypeHint pf (← g'.getType))
  replaceMainGoal []

/-! ## 4. The branch, for every `ra` -/

set_option maxHeartbeats 1000000 in
theorem branchSym (ra : BitVec 64) (v' v : BitVec 1) :
    branchAt AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4 (postRaSym ra) (tWithRa ra) v' v
      = true := by
  unfold branchAt riscvStep Functions.try_step Functions.run_hart_active Functions.execute
  rw [executeJALRSEq]
  unfold postRaSym jalrTarget
  rw [tgtImm0]
  have HE : ∀ x, pcEqb x x = true := pcEqbRefl
  generalize pcEqb = E at HE ⊢
  generalize hA0 : b0S = A0
  generalize b1S = A1
  rcases bv1Cases v' with rfl | rfl <;> rcases bv1Cases v with rfl | rfl
  all_goals
    ax_epi_cjr_sym_kcases h0
    · exfalso; rw [← hA0, AxEpiCjrSym.b0SAligned] at h0; exact Bool.noConfusion h0
    · ax_epi_cjr_sym_kcases h1
      all_goals ax_epi_cjr_sym_kclose HE

theorem jalrTargetSpec (r : BitVec 64) : (jalrTarget r).toNat = r.toNat - r.toNat % 2 := by
  unfold jalrTarget; rw [tgtImm0]
  show (clear0Z (r.toNat : Int)).toNat = _
  unfold clear0Z; split <;> omega

/-- THE LEDGER, for every `ra`. -/
theorem epiLedgerCjrSym (ra : BitVec 64) :
    AxEpiModelFacts (tWithRa ra) AxEpiProbe.drNopin DwAll DPost (pcJr : Int) cjrVs4
      (postRaSym ra) where
  lfSeipDr := by decide +kernel
  lfMeipDr := by decide +kernel
  lfSeipD := by decide +kernel
  lfMeipD := by decide +kernel
  lfHead := by decide +kernel
  lfToSeip := by ax_epi_ledger_krfl
  lfBranch00 := branchSym ra _ _
  lfBranch01 := branchSym ra _ _
  lfBranch10 := branchSym ra _ _
  lfBranch11 := branchSym ra _ _

section wpdSym
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdCjrSym (ra : BitVec 64) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch)
    (kk : Nat)
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcJr : Int) cjrVs4⌝) :
    ⊢ ((∀ s', ⌜RetS cpu (postRaSym ra) kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv (tWithRa ra) AxEpiProbe.drNopin DwAll DPost cjrVs4 cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) ((probeRegs pcJr).set .x1 ra) none ib, kk⟩
        Φ :=
  wpdCjrStepOfLedger i Φ cpu ib kk (tWithRa ra) _ _ _ _ _ _ (epiLedgerCjrSym ra) Hgd

end wpdSym

end Weak
