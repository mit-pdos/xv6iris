/-
Weak: **satisfiability certificates for `lock3sValue`** — two concrete, machine-checked
consistent 2-hart graphs on which EVERY premise of `AxLock3Thm.lock3sValue` is discharged, so its
premises are not vacuous.  Each conclusion is obtained by APPLYING `lock3sValue` (not by reading
`vB` off the row).

Rocq: `iris/AxLock3Cert.v` @ xxvzwolszwmp.

- `lock3sCertAB`: A acquires first, B reads-from A's release and A's write: the first conjunct
  gives `vB = b1`.
- `lock3sCertBA`: B acquires first from the image and loads `x` from the image (`b0`): the
  second conjunct gives `vB = bx0`.

**Fetches.** None (the graphs carry only RMW/store/fence/load labels; Stage C).

## Deviations from Rocq

1. NAMES: camelCase (map below).  Duplicated Rocq name, file-qualified: `AxLock3Cert.l2r` (also
   in AxLockN).  Rocq's `Local Notation B0/B1` ↦ `b0`/`b1`; the notations `A2 := 0`, `B2h := 1`
   ↦ reducible defs `a2`/`b2h`.
2. VOCABULARY: `vm_compute; reflexivity` ↦ `decide +kernel`; `z_pa` ↦ `zPa`; `mkgd` ↦
   `AxGraphWit.mkgd`; `gd_g`/`gx_gmo`/`gx_img` ↦ `.gdG`/`.gxGmo`/`.gxImg`; `grow` ↦
   `AxOpsem.grow`; `0%fin` ↦ `⟨0, _⟩`.
3. `lock3sValue` (Lean) takes the image premise `HimgL : GD.gdG.gxImg L = some b0` (one of the
   three `eq_refl`s of the Rocq call, together with `Hb0A`/`Hb0B`); discharged by `rfl` here.
4. `gAB_grfe` is proved through the boolean spec `grfeBSpec` (Rocq: unfolds `grfe` and uses
   `grb_b_spec`); same statement.

**Rocq → Lean name map.**  `Lpa2` `lpa2`, `xpa2` `xpa2`, `HLram2` `hLram2`, `Hxram2` `hxram2`,
`cpu2` `cpu2`, `L2r` `AxLock3Cert.l2r`, `x2r` `x2r`, `Hxy2` `hxy2`, `A2` `a2`, `B2h` `b2h`,
`HAB2` `hAB2`, `gAB` `gAB`, `gAB_cat` `gABCat`, `gAB_harts` `gABHarts`, `gAB_grfe` `gABGrfe`,
`lock3s_cert_AB` `lock3sCertAB`, `gBA` `gBA`, `gBA_cat` `gBACat`, `gBA_harts` `gBAHarts`,
`gBA_rd0` `gBARd0`, `gBA_imgx` `gBAImgx`, `lock3s_cert_BA` `lock3sCertBA`.

**Dropped:** nothing (the `Print Assumptions` audits are covered by the lint's axiom check).
-/
import Weak.AxLock3Thm
import Weak.AxGraphWit
import Weak.AxGraphDec

namespace Weak

open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D

/-! # 0. Concrete addresses (as in AxLock3Race) -/

def lpa2 : PAddr := zPa 0x80001000
def xpa2 : PAddr := zPa 0x80002000

theorem hLram2 : devAddr lpa2 = false := by decide +kernel
theorem hxram2 : devAddr xpa2 = false := by decide +kernel

def cpu2 : CPU := ⟨0, by decide⟩

def AxLock3Cert.l2r : Int := l3pLbase lpa2
def x2r : Int := l3pXbase xpa2

theorem hxy2 : x2r ≠ AxLock3Cert.l2r := by
  unfold x2r AxLock3Cert.l2r; decide +kernel

@[reducible] def a2 : Nat := 0
@[reducible] def b2h : Nat := 1

theorem hAB2 : a2 ≠ b2h := by decide

/-! # 1. Graph AB: A acquires first (from the image), writes `x := b1`, releases; B's acquire
reads A's release, B's load reads A's write.

gmo = [acqA; w_xA; relA; acqB; r_xB; relB]; write indices (t = 0 is the image): acqA=1, w_xA=2,
relA=3, acqB=4, relB=5.  So tA = 0, tB = 3 (relA), txB = 2 (w_xA), vB = b1. -/

def gAB : Gdexec :=
  AxGraphWit.mkgd [l3pWRow lpa2 xpa2 0 b0 b1, l3pRRow lpa2 xpa2 3 b0 2 b1]
    [(a2, 0), (a2, 1), (a2, 3), (b2h, 0), (b2h, 1), (b2h, 3)] []

theorem gABCat : rvwmoCatConsistent gAB :=
  catConsistentBSound _ (by decide +kernel)

theorem gABHarts : ∀ e : Geid, e ∈ gAB.gdG.gxGmo → e.1 = a2 ∨ e.1 = b2h := by
  intro e He
  simp only [gAB, AxGraphWit.mkgd, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem gABGrfe : grfe gAB.gdG (a2, 3) (b2h, 0) :=
  (grfeBSpec _ _ _).1 (by decide +kernel)

theorem lock3sCertAB :
    ∃ vB, AxOpsem.grow gAB b2h = l3pRRow lpa2 xpa2 3 b0 2 vB ∧ vB = b1 := by
  refine ⟨b1, rfl, ?_⟩
  have H := lock3sValue gAB AxLock3Cert.l2r x2r hxy2 lpa2 xpa2 hLram2 hxram2 cpu2 cpu2
    rfl rfl a2 b2h hAB2 0 b0 b1 rfl 3 b0 2 b1 rfl gABCat gABHarts rfl rfl rfl
  exact H.1 gABGrfe

/-! # 2. Graph BA: B acquires first (from the image), loads `x` from the image
(`imgw x = some b0`), releases; A acquires from B's release.

gmo = [acqB; r_xB; relB; acqA; w_xA; relA]; write indices: acqB=1, relB=2, acqA=3, w_xA=4,
relA=5.  So tB = 0, txB = 0 (image), tA = 2 (relB), vB = b0 (= the image byte bx0). -/

def gBA : Gdexec :=
  AxGraphWit.mkgd [l3pWRow lpa2 xpa2 2 b0 b1, l3pRRow lpa2 xpa2 0 b0 0 b0]
    [(b2h, 0), (b2h, 1), (b2h, 3), (a2, 0), (a2, 1), (a2, 3)] []

theorem gBACat : rvwmoCatConsistent gBA :=
  catConsistentBSound _ (by decide +kernel)

theorem gBAHarts : ∀ e : Geid, e ∈ gBA.gdG.gxGmo → e.1 = a2 ∨ e.1 = b2h := by
  intro e He
  simp only [gBA, AxGraphWit.mkgd, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem gBARd0 : greadsByte gBA.gdG (b2h, 0) AxLock3Cert.l2r 0 b0 :=
  (grbBSpec _ _ _ _ _).1 (by decide +kernel)

theorem gBAImgx : gBA.gdG.gxImg x2r = some b0 := rfl

theorem lock3sCertBA :
    ∃ vB bx0, AxOpsem.grow gBA b2h = l3pRRow lpa2 xpa2 0 b0 0 vB ∧
      gBA.gdG.gxImg x2r = some bx0 ∧ vB = bx0 := by
  refine ⟨b0, b0, rfl, gBAImgx, ?_⟩
  have H := lock3sValue gBA AxLock3Cert.l2r x2r hxy2 lpa2 xpa2 hLram2 hxram2 cpu2 cpu2
    rfl rfl a2 b2h hAB2 2 b0 b1 rfl 0 b0 0 b0 rfl gBACat gBAHarts rfl rfl rfl
  exact H.2 gBARd0 b0 gBAImgx

end Weak
