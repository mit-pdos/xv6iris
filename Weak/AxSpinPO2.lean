/-
Weak: **PHASE 5, stage 5: push_off's `noff == 0` ARM** — xv6's REAL `push_off + 0x2c … + 0x38`
(`jal mycpu`; `srli a5,s1,1`; `c.andi a5,1`; `c.sw a5,124(a0)` — `c->intena = old`; `c.j + 0x18`)
as a POSITIONAL CPS WPd at the joint instance Ixv6, interrupts off (`ctrlOkSW`), WARM TLB.
Composed with `AxSpinE8.wpdMycpu` at the row position `u` itself.

Rocq: `iris/AxSpinPO2.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

`wpdPoInt u`: for every `u` and every row matching `AxSpinPOr.poInt …` at `u` (5 items under
Stage C: mycpu's four events at `u .. u+3`; the intena store at `u + 4`), with `s1 =
sstatusRead m` for an `m` with SIE = 0 (what `AxSpinPO1.wpdPoHead` hands on):
  WPd (boundary at u, regs rs0) {{Ψ}}
  ⇐ (∀ rs' ib',
       ⌜regime ∧ PC = + 0x18 ∧ TLB kept ∧ a0 = mycpuRet tp ∧ sp kept ∧ every GPR but
        ra / s0 / a0 / a5 kept ∧ THE INTENA STORE'S ROW DATA = stBytes 4 0⌝
       -∗ WPd (boundary at u + 5, regs rs') {{Ψ}})
— intena := (sstatus >> 1) & 1 = SIE = 0 (`AxSpinPO1.ienaZero`), the plan's "push_off writes
intena := SIE = 0".
PREMISES (beyond AxSpinE8's style): mycpu's slot bundles, the intena field bundle (`fld4`: 4
bytes of hart `i`'s cpu struct) and `rowWle`; the value pin for mycpu's return (deviation 1).

GRAPH-VALUE PINNING (Q20', provisional Option V, `notes/weak-port-q20-offrow.md`; Rocq:
"TEMPORARY ASSUMPTION — ROW PINNING", owner decision 2026-10-03).  `poInt` fixes which row
positions are loads / stores and the data base addresses (mycpu's slots, the intena field);
mycpu's RETURN (to `push_off + 0x30`) is pinned by its ra reload's GRAPH VALUE (`Hval30`).  The
theorem proves nothing about a graph whose values differ; the follow-up ROW-INTEGRITY theorem is
to discharge the value pin.  Ownership is load-bearing for data values.

Kernel words (cross-checked against `Xv6/KernelImage.lean`, push_off = 0x80000c1e):
+0x2c 0x80000c4a `0x513000ef` (jal mycpu, imm 3346 → 0x8000195c), +0x30 0x80000c4e
`0x0014d793`, +0x34 `0x8b85`, +0x36 `0xdd7c`, +0x38 0x80000c56 `0xb7c5` (c.j → 0x80000c36 =
+0x18).  All as in `AxSpinPO` (its `Wq2c`/`q2c` carry the drifted immediate).

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20', AxSpinPOr,
   AxSpinPO1 / AxSpinPO3 (value pins), AxSpinE8 (Hval/Hret) entries):
   * the row shape is `poInt (paZ Pmra) (paZ Pms0) (paZ Pi)` (AxSpinPOr deviation 1: no fetch
     items); the parameters `p2c` (the fetch of + 0x2c) and `p30` (mycpu's return fetch) are
     DROPPED.
   * POSITIONS (a fetch consumes no row item): the `jal` at `u`, mycpu at `u` (Rocq `u + 1`),
     its continuation at `u + 4` (Rocq `u + 19`), the register-only `srli` / `c.andi` at
     `u + 4`, the intena store AT `u + 4` (Rocq `u + 22`, row data), the `c.j` at `u + 5` and
     the final continuation at `u + 5` (Rocq `u + 24`).
   * NEW length premise `u + 5 < row.length` (the `c.j` is register-only and needs a next row
     item, `XxReg`'s `k < LEN`; Rocq got its length from the window's trailing fetch items).
   * the `fpin T stv (ppo 0x30) p30` premise, the section context `stv` and the Sail premise
     `va_first_read` are DROPPED; NEW value pin (Q20') `Hval30 : graphValue (gtAdGd GT)
     (i, u + 2) = some (stBytes 8 (AxSpinPO.ppo 0x30))` (mycpu's ra reload — `wpdMycpu`'s
     `Hval` at `u`; its `Hret` is decided at the literal).
   * `sh_fetch_nw` (the intena store's "previous item is not a write") has no counterpart:
     `XxSt4` takes no such premise.
2. TYPES / SPELLING (as AxSpinPO1 deviation 3): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`;
   `eq_vec (_get_Mstatus_SIE m) 'b"1" = false` ↦ `(_get_Mstatus_SIE m == 1#1) = false`;
   the `let`s are inlined: `spb` ↦ `gprVal rs0 AxSpinE8.r2`, `tp` ↦ `gprVal rs0 AxSpinE8.r4`;
   `add_vec (sp1_of spb) (sign_extend' 64 imm_ra)` ↦ `AxSpinE8.sp1Of … + sign_extend (m := 64)
   AxSpinE8.immRa`; `mword_of_int 0 : mword 64` ↦ `0#64`; `Interface.Ret tt` ↦ `.pure ()`.
3. INSTANCES / SECTION (as AxSpinPO1 deviation 4): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `pi_pol`/`pi_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section
   variables are explicit arguments in AxSpinE6's order (+ `Htxm Htxp`).
4. TACTICS: `pcs`/`nz`/`zq` ↦ `decide`; `zsimp` ↦ the file-local macro `ax_spin_po2_zsimp`
   (= AxSpinE8's); `lia` ↦ `omega`.  The proof uses literal register indices (`15#5`, `10#5`)
   where Rocq uses `rc7` / `r10`.  The trailing `Print Assumptions` is not ported.

**Rocq → Lean name map.**  `i124` `i124`, `wpd_po_int` `wpdPoInt`.  The local instances
`pi_pol`, `pi_G` are inlined (deviation 3).  No Lean-only declarations (+ 1 local macro).

**Dropped:** none.  Rocq 2 definitions/lemmas + 2 local instances; Lean 2.
-/
import Weak.AxSpinPO1
import Weak.AxSpinPOd
import Weak.AxSpinPOd2
import Weak.AxSpinPOt3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `i124`: the offset of `cpus[i].intena`. -/
def i124 : BitVec 12 := 124#12

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_po2_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

section point
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]
variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Htxm : mycpuText σi T) (Htxp : pushOffText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxp HΨmid in
/-- Rocq `wpd_po_int` (deviation 1: Stage C positions; the value pin `Hval30` replaces the
`fpin` premise; new length premise `u + 5 < row.length`). -/
theorem wpdPoInt (u : Nat) (rs0 : RegFile) (ib0 : Ibch) (Pmra Pms0 Pi : BitVec 64)
    (m : BitVec 64) :
    -- the row
    RowSh u (AxOpsem.grow (gtAdGd GT) i) (poInt (paZ Pmra) (paZ Pms0) (paZ Pi)) →
    u + 5 < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pi) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinPO.ppo 0x2c → hitW rs0 (AxSpinPO.ppo 0) →
    hitW rs0 (pcm 0) →
    gprVal rs0 AxSpinPOr.r9 = sstatusRead m → (_get_Mstatus_SIE m == 1#1) = false →
    -- mycpu's slots and the intena field
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi →
    dj (paZ Pms0) 8 (paZ Pmra) 8 →
    -- the value pin (Q20': mycpu's ra reload; deviation 1)
    graphValue (gtAdGd GT) (i, u + 2) = some (stBytes 8 (AxSpinPO.ppo 0x30)) →
    ⊢ (∀ (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = AxSpinPO.ppo 0x18 ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, u + 4) = some (stBytes 4 0#64)⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', u + 5⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, u⟩ Ψ := by
  intro HR Hlen Hw8 Hnr_mra Hnr_ms0 Hwle Hc0 HPC0 Hhit0 HhitM Hs1 HSIE
    ⟨HdaS_mra, HdaL_mra, Hh_mra, Hpr_mra, Hnt_mra⟩ ⟨HdaS_ms0, HdaL_ms0, Hh_ms0, Hpr_ms0, Hnt_ms0⟩
    ⟨HdaS_i, _, Hh_i, Hpr_i, _⟩ Hdm Hval30
  iintro C
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, T2c, T30, T34, T36, T38⟩ :=
    Htxp
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS4 := XxSt4 L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have WM := wpdMycpu L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Ψ HΨmid
  -- ---- + 0x2c: jal ra,mycpu (row position u) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs0 (AxSpinPO.ppo 0x2c) false q2c (some (pcm 0))
      (some (1#5, BitVec.addInt (AxSpinPO.ppo 0x2c) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs0 (AxSpinPO.ppo 0x2c)
      false 3346#21 1#5 (by decide)
    rw [show AxSpinPO.ppo 0x2c + sign_extend (m := 64) 3346#21 = pcm 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinPO.ppo 0x2c) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinPO.ppo 0x2c) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs0 u (AxSpinPO.ppo 0x2c) false q2c (some (pcm 0))
    (some (1#5, BitVec.addInt (AxSpinPO.ppo 0x2c) (incr false)))
    (retxRefl cpu rs0 u ib0) Hc0 HPC0
    (hitWSvpn rs0 (AxSpinPO.ppo 0x2c) (AxSpinPO.ppo 0) (by decide) Hhit0)
    (tw4Q2c σi T satp0 _ T2c) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 3346#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pcm 0 := gbPc T satp0 _ _ _ _ _ _ HG1
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  have Esp1 : gprVal rs1 AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 := by
    rw [HF1]; ax_spin_po2_zsimp
  have Etp1 : gprVal rs1 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := by
    rw [HF1]; ax_spin_po2_zsimp
  have Evra : AxSpinE8.vaRa rs1 =
      AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa := by
    unfold AxSpinE8.vaRa; rw [Esp1]
  have Evs0 : AxSpinE8.vaS0 rs1 =
      AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0 := by
    unfold AxSpinE8.vaS0; rw [Esp1]
  -- ---- mycpu, at u ----
  have HRm : RowMycpu u (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) (paZ Pms0) :=
    rowMycpuOf u _ _ _ (rowShAppL u _ (mycSh (paZ Pmra) (paZ Pms0)) [.RS (paZ Pi) 4] HR)
      (by omega)
  iapply (WM u rs1 ib1 (AxSpinPO.ppo 0x30) Pmra Pms0 HRm Hw8 Hnr_mra Hnr_ms0
    (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1 (hitWAgree rs0 rs1 _ Htl1 HhitM)
    (by rw [Evra]; exact HdaS_mra) (by rw [Evra]; exact HdaL_mra)
    (by rw [Evra]; exact hitWAgree rs0 rs1 _ Htl1 Hh_mra)
    (by rw [Evs0]; exact HdaS_ms0) (by rw [Evs0]; exact HdaL_ms0)
    (by rw [Evs0]; exact hitWAgree rs0 rs1 _ Htl1 Hh_ms0)
    Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0 (by unfold dj at Hdm; omega) Hval30 (by decide))
  iintro %vmra %vms0 %rs2 %ib2 %HM - -
  obtain ⟨Hc2, HPC2, Htl2', Ha02, Hsp2, -, -, -, -, Hkeep2, -, -, -, -⟩ := HM
  have Htl2 : rs2 .tlb = rs0 .tlb := Htl2'.trans Htl1
  have Ea02 : gprVal rs2 10#5 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) := by
    rw [← Etp1]; exact Ha02
  have Es12 : gprVal rs2 9#5 = sstatusRead m := by
    rw [Hkeep2 9#5 (by decide) (by decide) (by decide) (by decide) (by decide), HF1]
    ax_spin_po2_zsimp
    exact Hs1
  -- ---- + 0x30: srli a5,s1,1 (u+4) ----
  iapply (XR _ rs2 (u + 4) (AxSpinPO.ppo 0x30) false q30 none
    (some (15#5, shift_bits_right (gprVal rs2 9#5)
      (Sail.BitVec.extractLsb (1#6) (Functions.log2_xlen -i 1) 0)))
    (retxRefl cpu rs2 (u + 4) ib2) Hc2 HPC2
    (hitWSvpn rs2 (AxSpinPO.ppo 0x30) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (tw4Q30 σi T satp0 _ T30) (AxSpinE8.owOkSome 15#5 _ (by decide))
    (rfFSrli _ _ _)
    (certSrli (ctrlOkSW T satp0) rs2 (AxSpinPO.ppo 0x30) false 9#5 15#5 1#6 (by decide))
    (by omega))
  iintro %rs3 %ib3 %HG3
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 (fun _ => rfl) HG3
  have HPC3 : rs3 .PC = AxSpinPO.ppo 0x34 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- ---- + 0x34: c.andi a5,1 (u+4) ----
  have Hc4 := certAndi (ctrlOkSW T satp0) rs3 (AxSpinPO.ppo 0x34) true 15#5 15#5
    (sign_extend (m := 12) (1#6)) (by decide)
  simp only [HF3] at Hc4
  ax_spin_po2_zsimp at Hc4
  iapply (XR _ rs3 (u + 4) (AxSpinPO.ppo 0x34) true q34 none _
    (retxRefl cpu rs3 (u + 4) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (AxSpinPO.ppo 0x34) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (tw8b85 σi T satp0 _ T34) (AxSpinE8.owOkSome 15#5 _ (by decide))
    (rfFAndi _ _ _) Hc4 (by omega))
  iintro %rs4 %ib4 %HG4
  have HF4 := stepRegs T satp0 _ rs3 _ _ _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = AxSpinPO.ppo 0x36 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- ---- + 0x36: c.sw a5,124(a0) — intena (u+4) ----
  iapply (XS4 _ rs4 (u + 4) (AxSpinPO.ppo 0x36) true i124 15#5 10#5
    (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i124) Pi
    (retxRefl cpu rs4 (u + 4) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (AxSpinPO.ppo 0x36) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (twDd7c σi T satp0 _ T36) (by rw [HF4]; ax_spin_po2_zsimp; rw [Ea02]) HdaS_i
    (hitWAgree rs0 rs4 _ Htl4 Hh_i) Hpr_i Hwle (by omega))
  iintro %rs5 %ib5 %HG5 %Hgd4
  have HF5 := stepRegs0 T satp0 _ rs4 _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = AxSpinPO.ppo 0x38 := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- + 0x38: c.j + 0x18 (u+5) ----
  have Hcj2 : CertC (ctrlOkSW T satp0) rs5 (AxSpinPO.ppo 0x38) true q38
      (some (AxSpinPO.ppo 0x18)) none := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs5 (AxSpinPO.ppo 0x38)
      true (sign_extend (m := 21) (2032#11 +++ 0b0#1)) AxSpinPO1.rz (by decide)
    rw [show AxSpinPO.ppo 0x38 + sign_extend (m := 64) (sign_extend (m := 21) (2032#11 +++ 0b0#1))
      = AxSpinPO.ppo 0x18 by decide, linkOwZero AxSpinPO1.rz _ (by decide)] at h
    exact h
  iapply (XR _ rs5 (u + 5) (AxSpinPO.ppo 0x38) true q38 (some (AxSpinPO.ppo 0x18)) none
    (retxRefl cpu rs5 (u + 5) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (AxSpinPO.ppo 0x38) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs5 _ Htl5 Hhit0))
    (twB7c5 σi T satp0 _ T38) trivial (AxSpinPOx.rfFJal _ _) Hcj2 (by omega))
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs5 _ _ _ rs' HF5 HGr
  iapply C $$ %rs' %ib'
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, gbPc T satp0 _ _ _ _ _ _ HGr,
    (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl5, ?_, ?_, ?_, ?_⟩
  · -- a0 = mycpuRet tp
    rw [HFr]
    ax_spin_po2_zsimp
    exact Ea02
  · -- sp kept
    rw [HFr]
    ax_spin_po2_zsimp
    exact Hsp2.trans Esp1
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr10 Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      rw [Hkeep2 r Hr1 Hr2 Hr8 Hr10 Hr15, HF1]
      simp (disch := assumption) only [AxSpinE8.updOther]
  · -- the intena store's row data: intena = SIE = 0
    rw [Hgd4, HF4]
    ax_spin_po2_zsimp
    rw [Es12]
    show some (stBytes 4 (iena (sstatusRead m))) = _
    rw [ienaZero m HSIE]

end point

end Weak
