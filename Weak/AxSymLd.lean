/-
Weak: **discharging AxSymReg's `wp_ld_forallv` hypothesis for the real ld8 instruction** (AxSL
tier; LB/AxSL design rev 7).

Rocq: `iris/AxSymLd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

1. `wpLd8ForallvAx` -- THE CORE RESULT: under the concrete graph-agreement instance
   `skelAxirisG γg Φp`, the axiomatic WP of an athread sitting at the real ld8 data-read event
   (`AxSymLd.s0`) follows, by an ordinary entailment, from `graphAgree γg GD`, the "wire already
   handled" premise, and a continuation proved for EVERY value of the right width (no `v = x0`
   premise -- AxReadAll's genuine `∀ v` demonic read rule in wand form).  The proof is a
   one-line corollary of `AxGraphAgree.wpLd8ForallvOfGraphAgree`.
2. `symldSymWpLd` -- `AxSymReg.sym_wp_ld` replayed at a DEGENERATE SC surface (`symldPt`,
   `symldProvl`, `symldValid` all trivial); it does not use (1).  Rocq's FINDING 2: reaching the
   real register surface still needs reg_bridge (C7) and the acert→fetch/decode→execute bridge
   (C3) -- not attempted here (as Rocq).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  `ea0`, `s0` are duplicated Rocq names and `K0`
   would be a bare one-letter global, so all three are FILE-QUALIFIED (`AxSymLd.ea0`,
   `AxSymLd.s0`, `AxSymLd.k0`).  They take the node's data explicitly (Rocq section
   variables); `AxSymLd.s0`/`AxSymLd.k0` are definitionally `ld8State`/`ld8Cont` (same literal),
   as Rocq intends.  Vocabulary as AxGraphAgree deviation 1 (`Interface.ReadReq.t 8` ↦
   `Mem_read_request 8 va …` with a new parameter `va`; `oib32` ↦ `Ibch`; `regstate` ↦
   `RegFile`; `inl (w, None)` ↦ `.Ok (w, none)`; `S k` ↦ `k + 1`).
2. O2 STAGE C (`notes/weak-port-o2-stageC.md` §D, AxSym engine): the fetch is an admin label, so
   the `AStepFetch` absorption Rocq's header discusses does not arise (handled inside
   AxGraphAgree, which also receives and discards the Q8 pin); the oracle parameter `Tax` of
   `skel_axirisG γg Φp Tax` is deleted (AxWp deviation 10).  This file has no ledgers and no row
   items, so nothing is recomputed.
3. PREMISES: as Rocq's section closing, `wpLd8ForallvAx` takes `Hdev`, `Hlat`, `Hsync` but not
   `Hcoh` (unused; the Lean i-cache exclusion is derived from `Hread0` inside AxGraphAgree).
   `[InvGS_gen hlc GF]` for any `hlc` (Rocq `invGS_gen HasNoLc Σ`); the instance is named in the
   statement (`@AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ …`, AxWp deviation 8).
4. The degenerate surface lives over `IProp GF` (Rocq `iProp Σ`); `Goal` is an explicit
   argument.  Rocq `A -∗ B -∗ C` lemmas are stated `A ⊢ B -∗ C` (AxSymReg deviation 2) except
   the main result, which is stated `⊢ …` as AxGraphAgree's.

**Rocq → Lean name map.**  `ea0` `AxSymLd.ea0`, `s0` `AxSymLd.s0`, `K0` `AxSymLd.k0`,
`wp_ld8_forallv_ax` `wpLd8ForallvAx`, `symld_loc` `symldLoc`, `symld_val` `symldVal`,
`symld_prov` `symldProv`, `symld_pt` `symldPt`, `symld_provl` `symldProvl`, `symld_valid`
`symldValid`, `symld_instr_ld` `symldInstrLd`, `symld_data_instr` `symldDataInstr`,
`symld_provl_persistent` `symldProvlPersistent`, `symld_data_instr_persistent`
`symldDataInstrPersistent`, `symld_provl_carry` `symldProvlCarry`,
`symld_instr_ld_persistent` `symldInstrLdPersistent`, `symld_instr_ld_carries`
`symldInstrLdCarries`, `symld_wp_ld_forallv` `symldWpLdForallv`, `symld_sym_wp_ld`
`symldSymWpLd`.

**Dropped:** nothing.
-/
import Weak.AxGraphAgree
import Weak.AxSymReg

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! ## 1. The core result -/

section node
variable (cpu : CPU) (va : Nat) (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
  (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
  (ib : Ibch) (k : Nat)

/-- The data address of the ld8 request. -/
def AxSymLd.ea0 : Int := paZ req.pa

/-- The hart at the real ld8 data-read event (definitionally `ld8State`). -/
def AxSymLd.s0 : Athread :=
  ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) rs none ib, k⟩

/-- The state after receiving the bytes `vs` (definitionally `ld8Cont`). -/
def AxSymLd.k0 (vs : List (BitVec 8)) : Athread :=
  ⟨.PHart cpu (KK (.Ok (wordOfBytes 8 vs, none))) rs none ib, k + 1⟩

end node

section main
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxgraphG GF] [Axpol] (γg : GName) (Φp : Gdexec → Geid → IProp GF)

/-- THE CORE RESULT: the axiomatic WP at the real ld8 data-read event satisfies AxReadAll's
genuine `∀ v` shape, given graph agreement and the wire premise. -/
theorem wpLd8ForallvAx (GD : Gdexec) (i : Agent) (st : Stuckness)
    (Φ : Athread → IProp GF) (cpu : CPU) (va : Nat)
    (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hsync : (classify req.access_kind).akSync = false)
    (Hread0 : areadStep (AxOpsem.grow GD i) (AxSymLd.s0 cpu va req KK rs ib k)
      (afLd8DataIdent (AxSymLd.ea0 va req)) (AxSymLd.k0 cpu KK rs ib k))
    (x0 : List (BitVec 8)) (Hlen0 : x0.length = aidentN (afLd8DataIdent (AxSymLd.ea0 va req)))
    (Hflow0 : ⊢ ∀ na, naAtProgress GD i (AxSymLd.s0 cpu va req KK rs ib k).atK na ∗
        AxirisG.annotInterp (self := skelAxirisG γg Φp) na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF)
         (ls' : @AxirisG.logTsT GF (skelAxirisG γg Φp)),
         naSplittingWf (Axpol.lobp GD (i, (AxSymLd.s0 cpu va req KK rs ib k).atK)) na naUsed
           naUnused ∗
         @flowEqDyn hlc GF _ (skelAxirisG γg Φp) GD (i, (AxSymLd.s0 cpu va req KK rs ib k).atK)
           (Axpol.sPol GD (i, (AxSymLd.s0 cpu va req KK rs ib k).atK)) naUsed
           iprop(R ∗ ⌜graphValue GD (i, (AxSymLd.s0 cpu va req KK rs ib k).atK) = some x0⌝) ∗
         AxirisG.annotInterp (self := skelAxirisG γg Φp)
           (PartialMap.union (PartialMap.union
             {[(i, (AxSymLd.s0 cpu va req KK rs ib k).atK) := R]} naUnused) na) ∗
         AxirisG.localInterp (self := skelAxirisG γg Φp) GD i
           (AxSymLd.k0 cpu KK rs ib k x0).atK ls') :
    ⊢ graphAgree γg GD -∗
      (□ ∀ s', ⌜awire (AxSymLd.s0 cpu va req KK rs ib k) s'⌝ -∗
        @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i s' Φ) -∗
      (∀ v, ⌜v.length = aidentN (afLd8DataIdent (AxSymLd.ea0 va req))⌝ -∗
        @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i (AxSymLd.k0 cpu KK rs ib k v) Φ) -∗
      @AxWp.wp hlc GF _ (skelAxirisG γg Φp) _ st i (AxSymLd.s0 cpu va req KK rs ib k) Φ :=
  wpLd8ForallvOfGraphAgree γg Φp GD i st Φ cpu va req KK rs ib k Hdev Hlat Hsync
    (AxSymLd.ea0 va req) Hread0 x0 Hlen0 Hflow0

end main

/-! ## 2. `sym_wp_ld` instantiated -- degenerate SC surface -/

section degenerate
variable {GF : BundledGFunctors} (Goal : IProp GF)

def symldLoc : Type := Unit
def symldVal : Type := List (BitVec 8)
def symldProv : Type := Unit
def symldPt (_ : symldLoc) (_ : symldVal) : IProp GF := iprop(⌜True⌝)
def symldProvl (_ : symldLoc) (_ : symldProv) : IProp GF := iprop(⌜True⌝)
def symldValid (_ : symldProv) : Prop := True
def symldInstrLd (_ _ _ : symldLoc) : IProp GF := iprop(⌜True⌝)
def symldDataInstr (_ _ : symldLoc) : IProp GF := iprop(⌜True⌝)

instance symldProvlPersistent (l : symldLoc) (P : symldProv) :
    Persistent (symldProvl (GF := GF) l P) := by
  unfold symldProvl; infer_instance

instance symldDataInstrPersistent (d s : symldLoc) :
    Persistent (symldDataInstr (GF := GF) d s) := by
  unfold symldDataInstr; infer_instance

theorem symldProvlCarry (d s : symldLoc) (P : symldProv) :
    symldDataInstr (GF := GF) d s ⊢ symldProvl s P -∗ symldProvl d P := by
  unfold symldProvl
  iintro _ _
  ipureintro
  trivial

instance symldInstrLdPersistent (rd rs1 ea : symldLoc) :
    Persistent (symldInstrLd (GF := GF) rd rs1 ea) := by
  unfold symldInstrLd; infer_instance

theorem symldInstrLdCarries (rd rs1 ea : symldLoc) :
    symldInstrLd (GF := GF) rd rs1 ea ⊢ symldDataInstr rd ea := by
  unfold symldDataInstr
  iintro _
  ipureintro
  trivial

/-- THE DEGENERATE INSTANTIATION of `wp_ld_forallv`: the continuation is discharged only at
`x` (the collapsed shape, not the genuine `∀ v` content of `wpLd8ForallvAx`). -/
theorem symldWpLdForallv (rd rs1 ea : symldLoc) (base x : symldVal) (P : symldProv) :
    symldPt (GF := GF) rs1 base ⊢ symldProvl ea P -∗ symldInstrLd rd rs1 ea -∗
      (∀ v, symldPt rs1 base -∗ symldPt rd v -∗ ⌜symldValid P → v = x⌝ -∗ Goal) -∗
      Goal := by
  iintro Hrs1 _ _ Hcont
  ihave Hrdx : symldPt (GF := GF) rd x $$ []
  · unfold symldPt; ipureintro; trivial
  iapply Hcont $$ %x Hrs1 Hrdx
  ipureintro
  intro _; rfl

/-- `AxSymReg.sym_wp_ld` at the degenerate surface, by replaying its proof. -/
theorem symldSymWpLd (rd rs1 ea : symldLoc) (base x : symldVal) :
    symldPt (GF := GF) rs1 base ⊢ symPt symldPt symldProvl symldValid ea x -∗
      symldInstrLd rd rs1 ea -∗
      (symldPt rs1 base -∗ symPt symldPt symldProvl symldValid rd x -∗
        symPt symldPt symldProvl symldValid ea x -∗ Goal) -∗ Goal := by
  unfold symPt
  iintro Hrs1 Hea #Hinstr Hcont
  icases Hea with ⟨%vm, %P, Hvm, #HP, %Hi⟩
  ihave #Hcarry := symldInstrLdCarries (GF := GF) rd rs1 ea $$ Hinstr
  ihave #HPrd := symldProvlCarry (GF := GF) rd ea P $$ Hcarry HP
  iapply symldWpLdForallv Goal rd rs1 ea base x P $$ Hrs1 HP Hinstr
  iintro %v Hrs1 Hrd %Hj
  iapply Hcont $$ Hrs1 [Hrd] [Hvm]
  · iexists v, P
    iframe Hrd HPrd
    ipureintro
    exact Hj
  · iexists vm, P
    iframe Hvm HP
    ipureintro
    exact Hi

end degenerate

end Weak
