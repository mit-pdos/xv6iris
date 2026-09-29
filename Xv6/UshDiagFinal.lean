/-
**runcmd and fork1 at sh's own printer** (sh-main lane; Rocq
`UkShDiag.wp_kshr_runcmd_final`, `wp_kshr_fork1_final_at`, pinned
`1900b8a43`): sh-run's walks, generic in the diagnostic subtree's stack need
`Dg` and its leaf (`UshRunDefs.ushDiagLeaf`), instantiated at `ushDg` and
`UshDiagLeaf.ushDiagLeafHolds`.  Rocq proves them by one `exact` each; so
do these.  runcmd's and fork1's own contracts are sh-run's interfaces
`SH_RUNCMD` / `SH_FORK1` (lane sh-run, in flight), taken as parameters.

Deviations from Rocq: `UshDiagDefs` deviation 6 and sh-run's `SpecShRuncmd`
/ `SpecShFork1` deviations (the statements are theirs at `Dg := ushDg`);
Rocq's section hypothesis `Hpsok_free` is the explicit `hpsok`.
-/
import Xv6.UshDiagLeaf
import Xv6.SpecShRuncmd

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open LeanRV64D LeanRV64D.Functions
open Std (ExtTreeSet)

set_option linter.unusedSectionVars false

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CtokG GF] [UexecSG GF] [UprogSG GF]
  [GhostMapG GF Nat (BitVec 8) RegMapF] [GhostVarG GF Nat] [GhostMapG GF (Option Nat) UfdCell UfdMapF]
  [GhostVarG GF (ExtTreeSet GName compare)] [GhostVarG GF Int] [Xv6G GF]

/-- **Rocq `wp_kshr_runcmd_final`**: runcmd at sh's own printer. -/
theorem wp_kshr_runcmd_final (UL : UK_LEAVES) (HS : UK_SYS_P) (HF : USH_FPRINTF) (SP : SH_PANIC) (SR : SH_RUNCMD)
    (hpsok : ∀ k : Int, freeNum k → UprogSG.psok (GF := GF) k) (c : Ushcmd) (hc : ushSimple c) :
    ∀ (N : UkNames GF) [UknConst N] (h : CPU) (m : RegMap) (t szv : Nat) (ld : List FdState) (n : Nat),
    (⊢ N.pay (-1)) → m.get 10#5 = BitVec.ofNat 64 t →
    ⊢ shDeps (hlc := hlc) -∗ ushCode N.t -∗ uxsupAt (hlc := hlc) N.pay -∗
      □ (uKillCred (hlc := hlc) -∗ N.pay (-1)) -∗ ushJtab N.t -∗ ushCmd N.d t c -∗ usz N.s szv -∗
      ustd N.fd ld -∗ ucwdAny N.cwd -∗ uchAny N.ch -∗
      urun (hlc := hlc) N h m (BitVec.ofNat 64 User.Sh.Sym.«runcmd») (6 * ushHt c + (2 + (ushDg + n))) -∗
      wpLoop h :=
  SR.wp_shRuncmd ushDg (ushDiagLeafHolds UL HS HF SP) hpsok c hc

/-- **Rocq `wp_kshr_fork1_final_at`**: fork1 at sh's own printer's stack
need, at a named table view. -/
theorem wp_kshr_fork1_final_at (SF : SH_FORK1) :
  ∀ (N : UkNames GF) (P : GName → GName → GName → IProp GF) [Forkable P] (szv : Nat)
    (l v : List FdState) (D : RegMapF FdState) (h : CPU) (m : RegMap) (n cw : Nat)
    (Sc : ExtTreeSet GName compare) (Q : Int → IProp GF) (Rc Pex : IProp GF),
    (∀ x y : Int, Q x = Q y) →
    ⊢ ushCode N.t -∗ P N.t N.d N.s -∗ usz N.s szv -∗ ustdAt N.fd l v -∗ ucwd N.cwd cw -∗ uch N.ch Sc -∗
      ([∗map] fd ↦ st ∈ D, ufd N.fd fd st) -∗ Rc -∗ □ (uKillCred (hlc := hlc) -∗ Q (-1)) -∗ Pex -∗
      urun (hlc := hlc) N h m (BitVec.ofNat 64 User.Sh.Sym.«fork1») (2 + (ushDg + n)) -∗
      ((∀ (h' : CPU) (m' : RegMap) (r : BitVec 64), ⌜(m'.get 10#5).toNat = 0x1288⌝ -∗ ⌜r = -1#64⌝ -∗
          ushFork1Ans N Sc Q Rc r -∗ ustdAt N.fd l v -∗ Pex -∗
          urun (hlc := hlc) N h' m' (BitVec.ofNat 64 User.Sh.Sym.«panic») (ushDg + n) -∗ wpLoop h') ∗
        (∀ (h' : CPU) (m' : RegMap) (r : BitVec 64), ⌜r ≠ 0#64⌝ -∗ ⌜r ≠ -1#64⌝ -∗ ⌜ucalleeSaved m m'⌝ -∗
          ⌜m'.get 10#5 = r⌝ -∗ ushFork1Ans N Sc Q Rc r -∗
          P N.t N.d N.s -∗ usz N.s szv -∗ ustdAt N.fd l v -∗ ucwd N.cwd cw -∗
          ([∗map] fd ↦ st ∈ D, ufd N.fd fd st) -∗ Pex -∗
          urun (hlc := hlc) N h' m' (retPc (m.get 1#5)) (2 + (ushDg + n)) -∗ wpLoop h') ∗
        (∀ (N' : UkNames GF) (h' : CPU) (m' : RegMap) (γ' : GName), ⌜N'.pay = Q⌝ -∗ ⌜ucalleeSaved m m'⌝ -∗
          ⌜m'.get 10#5 = 0#64⌝ -∗ myPay γ' Q -∗ Rc -∗ ushCode N'.t -∗ P N'.t N'.d N'.s -∗ usz N'.s szv -∗
          ustdAt N'.fd l v -∗ ucwd N'.cwd cw -∗ uch N'.ch ∅ -∗ (∃ p : Int, ⌜p ≠ 1⌝ ∗ upid N'.pid p) -∗
          ([∗map] fd ↦ st ∈ D, ufd N'.fd fd st) -∗
          urun (hlc := hlc) N' h' m' (retPc (m.get 1#5)) (2 + (ushDg + n)) -∗ wpLoop h')) -∗
      wpLoop h :=
  SF.wp_shFork1At ushDg

end

end Xv6
