/-
THE UNION CLAIM'S KERNEL-EVENT STEPS AND DRAIN, SEALED -- the declarations of
Rocq `UnionOut.v` (pinned `1900b8a43`) that `Xv6/UnionOut.lean` did not port
but that the union laws reach (U4 seal wave, walk3.txt): thin wrappers over
`PipeOutWSeal`'s `pwclV_*` at the landed
`ucl ug := pwclV (ugnPipe ug) ulmG (ucparams ug) ∅ (uwa ug) uwild`.
(`union_era_split`, `union_led_*`, `union_birth_all` and `UnionLinks` are
lane U4's own, not here.)

Added (Rocq → Lean): `udrain_ret` → `udrainRet`, `ucl_drain`, `ucl_close`,
`ucl_open`, `ucl_step_byte` (same names).

DEVIATIONS from Rocq:
1. Rocq's section `Context (ug : union_gn)` is an explicit argument; the
   local notations `U`/`UB`/`UT`/`pg` are written out (`ulmG`,
   `ulm_byte_laws admUG admSOn`, `fileTaint ug.ugnFile.fgnCl`,
   `ugnPipe ug`); `gf` is `ug.ugnFile`.
2. THE KERNEL PREMISES (`GenOutHistSeal.lean` DEVIATION 1): `ucl_close`
   takes `hK3` and `ucl_open` takes `hK1`/`hK2`, in Rocq's exact shape;
   once `consEvOk` carries them they are its projections.
-/
import Xv6.UnionOut
import Xv6.PipeOutWSeal

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1024

section UnionOutSealSteps
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF]
  [EchoOutG GF] [FileAppG GF] [FileOutG GF] [PipeOutG GF]

/-- THE UNION'S DRAIN RECEIPT (Rocq `udrain_ret`): `gdrain_ret` at the union,
its writer's witness read as the file era's pin and boot lower bound. -/
noncomputable def udrainRet (ug : UnionGn) (k : Nat) (seg : List Obs) : IProp GF :=
  iprop(fileTaint (hlc := hlc) ug.ugnFile.fgnCl
    ∨ ∃ (s0 : Fstate) (vf : FileEra),
        ⌜lmGoodOut ulmG s0 seg⌝ ∗ ⌜fstateOk s0⌝ ∗ f0Typed ug.ugnFile s0
        ∗ fileEraPin ug.ugnFile k vf ∗ f0Lb vf s0)

theorem uwa_gwaTy (ug : UnionGn) :
    (uwa (hlc := hlc) (GF := GF) ug).gwaTy = f0Typed ug.ugnFile := rfl

/-- Rocq `ucl_drain`. -/
theorem ucl_drain (ug : UnionGn) (k : Nat) (h ho : List Obs) (CH : ConsHist) (seg : List Obs)
    (hsh : traceShape h true) (hk : obsBoots h = k) (hpre : ho <+: h)
    (hins : consIns seg = consIns (openSeg h)) (hwire : obsWire .uart0 seg <+: CH.chAcc)
    (hne : obsWire .uart0 seg ≠ []) :
    ⊢ ucl (hlc := hlc) (GF := GF) ug k ho CH -∗ ucl ug k ho CH ∗ udrainRet ug k seg := by
  iintro Hc
  unfold ucl
  ihave ⟨Hc, Hd⟩ := pwclV_drain (ugnPipe ug) ulmG (ucparams ug) ulmG_laws
    (ulm_byte_laws admUG admSOn) (∅ : Fstate) (uwa ug) uwild uwild_wild k h ho CH seg hsh hk hpre
    hins hwire hne $$ Hc
  isplitl [Hc]
  · iexact Hc
  · unfold udrainRet gdrainRet
    rw [ucparams_gcT, ucparams_gcW, uwa_gwaTy]
    unfold f0cw
    icases Hd with (#HT | ⟨%s0, %hgo, %hok, #Hty, ⟨%vf, #Hfp, #Hlb⟩⟩)
    · ileft; iexact HT
    · iright
      iexists s0, vf
      iframe Hty Hfp Hlb
      isplitr
      · ipureintro; exact hgo
      · ipureintro; exact hok

/-- Rocq `ucl_close`: THE KERNEL'S OWN EVENTS.  `hK3`: DEVIATION 2. -/
theorem ucl_close (ug : UnionGn) (k : Nat) (ho : List Obs) (H : ConsHist) (hok : consHistOk H)
    (hev : consEvOk H .evClose)
    (hK3 : ∀ a, H.chArm = some a → caEcho a = [echoOf (caByte a)] → caSent a = 1) :
    ⊢ ucl (hlc := hlc) (GF := GF) ug k ho H -∗ ucl ug k ho (consStep H .evClose) :=
  pwclV_close (ugnPipe ug) ulmG (ucparams ug) (∅ : Fstate) (uwa ug) uwild k ho H hok hev hK3

/-- Rocq `ucl_open`.  `hK1`/`hK2`: DEVIATION 2. -/
theorem ucl_open (ug : UnionGn) (k : Nat) (ho : List Obs) (H : ConsHist) (h : List Obs)
    (c : BitVec 8) (cs : List (BitVec 8)) (hok : consHistOk H) (hev : consEvOk H (.evOpen h c cs))
    (hK1 : ∃ f : Nat, flushLost h f
      ∧ H.chLog.length + 1 + f = (obsIns .uart0 (openSeg h)).length)
    (hK2 : cs = [] → consDropOk c H.chLog H.chDl)
    (hd : lmDiscInput ulmG (consIns (openSeg h))) (hb : obsBoots h = k) (hdh : lmDisc ulmG h)
    (hsh : traceShape h true) :
    ⊢ ucl (hlc := hlc) (GF := GF) ug k ho H -∗ ucl ug k h (consStep H (.evOpen h c cs)) :=
  pwclV_open (ugnPipe ug) ulmG (ucparams ug) (ulm_byte_laws admUG admSOn) (∅ : Fstate) (uwa ug)
    uwild uwild_wild k ho H h c cs hok hev hK1 hK2 hd hb hdh hsh

/-- Rocq `ucl_step_byte`. -/
theorem ucl_step_byte (ug : UnionGn) (k : Nat) (ho : List Obs) (CH : ConsHist) (b : BitVec 8)
    (hok : consHistOk CH) (hev : consEvOk CH (.evByte b)) :
    ⊢ ucl (hlc := hlc) (GF := GF) ug k ho CH ==∗ ucl ug k ho (consStep CH (.evByte b)) :=
  pwclV_step_byte (ugnPipe ug) ulmG (ucparams ug) (ulm_byte_laws admUG admSOn) (∅ : Fstate)
    (uwa ug) uwild ulmG_laws k ho CH b hok hev

end UnionOutSealSteps

end Xv6
