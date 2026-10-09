/-
Weak: **PHASE 5, stage 2: THE CERTIFICATE `wpdMycpu`** — xv6's REAL `mycpu` (the 14
instructions at `KernelSyms.«mycpu»`) as a POSITIONAL CPS WPd at the joint instance Ixv6,
interrupts off (`ctrlOkSW`: S-mode, SIE = 0), WARM TLB.

Rocq: `iris/AxSpinE8.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

`RowMycpu k row pra ps0` — the piece of hart `i`'s row that mycpu occupies from position `k`.
Under O2 Stage C an instruction fetch is an ADMIN step with no row item, so the window holds
only mycpu's four memory events:
  k+0 / k+1   the SPILLS: plain 8-byte stores at `pra` (ra's slot) / `ps0` (s0's slot), data
              existential;
  k+2 / k+3   the RELOADS: plain 8-byte reads of the slots, values existential;
and the row continues past `k+3` (`k + 4 < row.length`: the caller's next memory event).
THE THEOREM (`wpdMycpu`), for every `k` and every row with `RowMycpu k`:
  WPd (boundary at k, regs rs0) {{Ψ}}
  ⇐ (∀ vra vs0 rs' ib',
       ⌜regime ∧ PC rs' = ret ∧ TLB kept ∧ a0 = mycpuRet (tp of rs0) ∧ sp restored ∧ ra / s0 =
        the RELOADED words ∧ every other GPR kept ∧ the spills' row data = ra0 / s00's bytes ∧
        the reloads' graph values = vra / vs0⌝
       -∗ (i,k+2) ↦ₐ ⌜reload bytes = ra0's bytes⌝ -∗ (i,k+3) ↦ₐ ⌜reload bytes = s00's bytes⌝
       -∗ WPd (boundary at k+4, regs rs') {{Ψ}})
— the continuation is at the EXACT position `k + 4`; the two reload annotations are Phase 1c's
private-slot facts (`RLfact`) to be read back at the caller's row end.

TEMPORARY ASSUMPTION — ROW PINNING (Rocq, owner decision 2026-10-03) ↦ GRAPH-VALUE PINNING
(Q20', provisional Option V, `notes/weak-port-q20-offrow.md`).  `RowMycpu` fixes which row
positions are spills / reloads and the slots' base addresses; the return address is pinned by
the reload's GRAPH VALUE `Hval : graphValue (gtAdGd GT) (i, k + 2) = some (stBytes 8 ret)`
(the row cannot pin control flow under Stage C; the reload's graph value does).  The theorem
proves nothing about a graph whose reload value differs.  The follow-up ROW-INTEGRITY theorem
is to discharge `Hval` from the `RLfact` readback (reload bytes = spill bytes = entry `ra`).

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C row `AxSpinE8`, Q-S2-1/2)

`RowMycpuP k row pra ps0` is `RowMycpu` on a PREFIX row: each of the four memory events that is
PRESENT (`k + j < row.length`) has its `mshape`; no length conjunct (`AxSpinE8.rowMycpuPOfFull`:
`RowMycpu → RowMycpuP`).  `wpdMycpuP` is the same script as `wpdMycpu` with one `by_cases` per
row position (`k`, `k+1`, `k+2`, `k+3`, `k+4` — the five boundaries where the row may end; the
other leaf calls at the same position reuse the bound); the end case is discharged by the
WINDOWED, RESOURCE-FREE hook (exact form, shared with the other P-form lanes):
  `HΨend : ∀ k', k ≤ k' → k' ≤ k + 4 → (grow (gtAdGd GT) i).length ≤ k' →
     ∀ pr : Pexv6, ⊢ wpdM … .MaybeStuck i ⟨pr, k'⟩ Ψ`
(every program state; the caller instantiates it by `AxSpinApA.wpdEndAnn` + `postLiftingTrue`).
mycpu has NO designated cut, so no end arm is proved here.  The `Hval` pin is GUARDED:
`k + 2 < LEN → graphValue (i, k + 2) = some (stBytes 8 ret)` (design §A "guarded pins").  The
continuation (unchanged) is reached only on rows with `k + 4 < LEN`.  `wpdMycpu` keeps its exact
statement and is now the corollary (hook vacuous under `k + 4 < LEN`; `Hval` unguarded).

## P1 GATE FORM (Lean-only; notes/weak-lb-thm2-pins.md §P1, Q-P1-2)

`wpdMycpuG L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxt Ψ HΨmid k rs0 ib0 Pra Ps0`
has EXACTLY `wpdMycpuP`'s premises and post except (no `ret` argument; `ret := gprVal rs0 r1`,
the entry `ra`, which the callers know from their `jal` — T2a's `jalrRets`):
  * the pin `k + 2 < LEN → graphValue (gtAdGd GT) (i, k + 2) = some (stBytes 8 ret)` is replaced
    by the GATE `Hgate : AxSpinT2i.Gate GT i (k + 2) (stBytes 8 (gprVal rs0 AxSpinE8.r1))`, i.e.
    `graphValue (gtAdGd GT) (i, k + 2) ≠ some (stBytes 8 (gprVal rs0 r1)) → LEN ≤ k + 3`
    (kr = k + 2 the ra reload, vw = ra's spill bytes);
  * `Hret : jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = gprVal rs0 AxSpinE8.r1`;
  * the post's `rs' .PC = gprVal rs0 AxSpinE8.r1`.
Same argument order as `wpdMycpuP` (gate in `Hval`'s slot; hook `HΨend` unchanged, windowed
`k .. k + 4`).  A caller passes its OWN gate (from its row family / ApB bridge), or
`AxSpinT2i.gateOfPin`/`gateOfPinG` of an old pin.  Proof: the gated core
`AxSpinE8.wpdMycpuGr` (`ret` generic, gate `Gate GT i (k + 2) (stBytes 8 ret)`): at the reload's
continuation `by_cases` on the reloaded value — equal ⇒ the P-form script (the value is now the
leaf's `Hgv`); else, when `stBytes 8 ret` is the spill (always at `wpdMycpuG`), the arm is
`AxSpinT2i.cutReloadG` with the leaf's `RLfact` annotation (refuted: `LEN ≤ k + 3` from the
gate, readback contradicts the value); for `wpdMycpuP`'s free `ret` ≠ entry ra the gate gives
`LEN ≤ k + 3` and the arm is the hook.  `wpdMycpuP` = core ∘ `AxSpinT2i.gateOfPinG` (statement
unchanged), `wpdMycpu` = `wpdMycpuP` as before.  HONESTY: `wpdMycpuG` has no return-address pin;
the s0 reload (k + 3) never had one (its value is only reported).

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20' entry):
   * `Row_mycpu k row pra ps0 pret nret` ↦ `RowMycpu k row pra ps0`: no fetch items, so the
     window is the four memory events at `k .. k+3` (Rocq spills `k+2`/`k+4`, reloads
     `k+13`/`k+15`, 14 fetch items, return fetch at `k+18`); the length conjunct is
     `k + 4 < row.length` (Rocq `k + 18 < length row`: the c.ret's continuation boundary needs
     a next row item — `AxSpinE6.XxRet`'s `k < LEN`).  `pret`/`nret` and the return-fetch
     conjunct are gone; `mshape`'s fetch arm is `False` (it ranges over `j < 4` only).
   * `wpdMycpu`: Rocq's return-page premises `Hinj` (only `ret` fetches from `pret`) and
     `Hstv` (the trap vector does not), the section context `stv` and the Sail premise
     `va_first_read` are DROPPED ("Stage C: no row item pins a fetch"; `AxSpinE6` deviation
     4).  NEW premises: `Hval : graphValue (gtAdGd GT) (i, k + 2) = some (stBytes 8 ret)` (the
     Stage C pin of the return address) and `Hret : jalrTgt 0#12 ret = ret` (`ret` is
     2-aligned: c.ret clears bit 0 of `ra`; Rocq obtained `PC = ret` from the fetch pin; `by
     decide` at a literal `ret`).
   * Positions: spills' row data at `(i, k)` / `(i, k + 1)` (Rocq `k+2`/`k+4`), reloads'
     graph values and annotations at `(i, k + 2)` / `(i, k + 3)` (Rocq `k+13`/`k+15`),
     continuation at `k + 4` (Rocq `k+18`).
   * `rf_fetch` is DROPPED (it describes the fetch positions; there are none, and its two uses
     fed the leaves' `Hnw`/`Hnr8`, dropped in `AxSpinE6` deviation 3).
2. KERNEL DRIFT (`AxSpinE7` deviation 1): the `addi a0,a0,…` immediate is `0xbc6#12` (Rocq
   `2692` = 0xa84); `AxSpinE8.mycpuRet` is stated with it.  `mycpu_ret`/`mycpu_a5` (Rocq
   `ProcGeom`, not in the Lean `Xv6/ProcGeom`) and `frame_cancel_16` (Rocq `KernelRvcDecode`,
   MISSING by design) are ported here as the file-qualified `AxSpinE8.mycpuRet`,
   `AxSpinE8.mycpuA5`, `AxSpinE8.frameCancel16` (only what this file uses).  `mycpuRet`'s
   `add_vec_int (mword_of_int mycpu) 14` is spelled `pcm 0x0e`.
3. TYPES / SPELLING (`AxSpinE6` deviation 1): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `Z.eqb (uint r) (uint rd)`
   ↦ `r = rd` in `AxSpinE8.upd`; `l !! k` ↦ `l[k]?`; `zero_extend' 5 'b"10"` ↦ `2#5`; `rS0` ↦
   `8#5`; `(i,k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; the `let`s `sp0`/`va_ra`/`va_s0` are
   inlined (`AxSpinE8.vaRa`/`vaS0` name the two VAs).
4. INSTANCES / SECTION (as `AxSpinE6` deviation 2): `[InvGS_gen hlc GF]` (any `hlc`); the
   local instances are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; the section variables
   are explicit arguments in `AxSpinE6`'s order.
5. TACTICS: Rocq `pcs` (closed bit-vector equations) ↦ `decide`; `nz` ↦ `decide`; `zsimp` ↦
   the file-local macro `ax_spin_e8_zsimp` (`simp (disch := decide) only [AxSpinE8.updSame,
   AxSpinE8.updOther, AxSpinE8.updZero]`); `vm_compute_uint`, `zq` are subsumed (not ported).
   The trailing `Print Assumptions` is not ported (the lint's axiom check covers it).

**Rocq → Lean name map.**  `upd` `AxSpinE8.upd`, `retx_refl` `retxRefl`, `gb_ctrl` `gbCtrl`,
`gb_pc` `gbPc`, `gb_tlb` `gbTlb`, `step_regs` `stepRegs`, `step_regs0` `stepRegs0`, `hitW_svpn`
`hitWSvpn`, `mshape` `mshape`, `Row_mycpu` `RowMycpu`, `row_w8` `rowW8`, `no_rmw8` `noRmw8`,
`r1`…`r15` `AxSpinE8.r1`…`AxSpinE8.r15` (abbrevs), `imm_ra` `AxSpinE8.immRa`, `imm_s0`
`AxSpinE8.immS0`, `sp1_of` `AxSpinE8.sp1Of`, `wpd_mycpu` `wpdMycpu` (none in the
duplicated-name table; the generic ones are file-qualified anyway); from other Rocq files
(deviation 2) `mycpu_a5` `AxSpinE8.mycpuA5`, `mycpu_ret` `AxSpinE8.mycpuRet`,
`frame_cancel_16` `AxSpinE8.frameCancel16`.  Lean-only (file-qualified): `AxSpinE8.updSame`,
`updOther`, `updZero`, `owOkSome`, `gprValZero`, `ldResStBytes8`, `vaRa`, `vaS0`,
`rowMycpuPOfFull`; stage-2 P-form (unqualified, grepped unique): `RowMycpuP`, `wpdMycpuP`;
P1: `wpdMycpuG`, `AxSpinE8.wpdMycpuGr`.

**Dropped:** `rf_fetch` (deviation 1).  Rocq 23 definitions/lemmas (+ 5 Ltac); Lean 22 + 3
ported from ProcGeom/KernelRvcDecode + 11 Lean-only (+ 1 macro).
-/
import Weak.AxSpinE6
import Weak.AxSpinE7b
import Weak.AxSpinE7c
import Weak.AxSpinE7d
import Weak.AxSpinE7e
import Weak.AxSpinE7f
import Weak.AxSpinE7g
import Weak.AxSpinT2i

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Register-file bookkeeping through `GoodB` -/

/-- Rocq `upd`. -/
def AxSpinE8.upd (F : BitVec 5 → BitVec 64) (rd : BitVec 5) (v : BitVec 64) (r : BitVec 5) :
    BitVec 64 :=
  if r.toNat = 0 then 0#64 else if r = rd then v else F r

theorem AxSpinE8.updSame (F : BitVec 5 → BitVec 64) (rd : BitVec 5) (v : BitVec 64) :
    rd.toNat ≠ 0 → AxSpinE8.upd F rd v rd = v := by
  intro h
  unfold AxSpinE8.upd
  rw [if_neg h, if_pos rfl]

theorem AxSpinE8.updOther (F : BitVec 5 → BitVec 64) (rd : BitVec 5) (v : BitVec 64)
    (r : BitVec 5) : r.toNat ≠ 0 → r ≠ rd → AxSpinE8.upd F rd v r = F r := by
  intro h1 h2
  unfold AxSpinE8.upd
  rw [if_neg h1, if_neg h2]

theorem AxSpinE8.updZero (F : BitVec 5 → BitVec 64) (rd : BitVec 5) (v : BitVec 64)
    (r : BitVec 5) : r.toNat = 0 → AxSpinE8.upd F rd v r = 0#64 := by
  intro h
  unfold AxSpinE8.upd
  rw [if_pos h]

theorem AxSpinE8.owOkSome (rd : BitVec 5) (v : BitVec 64) : rd.toNat ≠ 0 → owOk (some (rd, v)) :=
  id

/-- (Lean-only, Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_e8_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

theorem AxSpinE8.gprValZero (rs : RegFile) (r : BitVec 5) : r.toNat = 0 → gprVal rs r = 0#64 := by
  intro h
  unfold gprVal uxaXget
  rw [h]
  rfl

/-- Rocq `retx_refl`. -/
theorem retxRefl (cpu : CPU) (rs : RegFile) (k : Nat) (ib : Ibch) :
    RetX cpu rs k ⟨.PHart cpu (.pure ()) rs none ib, k⟩ :=
  ⟨ib, rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩

section gb
variable (T : PTree) (satp0 : BitVec 64)

/-- Rocq `gb_ctrl`. -/
theorem gbCtrl (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ot : Option (BitVec 64))
    (ow : Option (BitVec 5 × BitVec 64)) (rs' : RegFile) :
    GoodB T satp0 rs pc is_rvc ot ow rs' → ctrlOkSW T satp0 rs' := fun h => h.1.1

/-- Rocq `gb_pc`. -/
theorem gbPc (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ot : Option (BitVec 64))
    (ow : Option (BitVec 5 × BitVec 64)) (rs' : RegFile) :
    GoodB T satp0 rs pc is_rvc ot ow rs' → rs' .PC = tgtOf ot pc is_rvc := fun h => h.1.2.1

/-- Rocq `gb_tlb`. -/
theorem gbTlb (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ot : Option (BitVec 64))
    (ow : Option (BitVec 5 × BitVec 64)) (rs' : RegFile) :
    GoodB T satp0 rs pc is_rvc ot ow rs' → rs' .tlb = rs .tlb := fun h => h.2

/-- Rocq `step_regs`. -/
theorem stepRegs (F : BitVec 5 → BitVec 64) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool)
    (ot : Option (BitVec 64)) (rd : BitVec 5) (v : BitVec 64) (rs' : RegFile) :
    (∀ r, gprVal rs r = F r) → GoodB T satp0 rs pc is_rvc ot (some (rd, v)) rs' →
    ∀ r, gprVal rs' r = AxSpinE8.upd F rd v r := by
  intro HF HG r
  unfold AxSpinE8.upd
  by_cases E : r.toNat = 0
  · rw [if_pos E]
    exact AxSpinE8.gprValZero rs' r E
  · rw [if_neg E]
    have Hg := HG.1.2.2 r E
    simp only [gprPost] at Hg
    show uxaXget rs' r = _
    rw [Hg]
    by_cases h : r = rd
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      exact HF r

/-- Rocq `step_regs0`. -/
theorem stepRegs0 (F : BitVec 5 → BitVec 64) (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool)
    (ot : Option (BitVec 64)) (rs' : RegFile) :
    (∀ r, gprVal rs r = F r) → GoodB T satp0 rs pc is_rvc ot none rs' → ∀ r, gprVal rs' r = F r := by
  intro HF HG r
  rw [← HF r]
  by_cases E : r.toNat = 0
  · rw [AxSpinE8.gprValZero rs' r E, AxSpinE8.gprValZero rs r E]
  · exact HG.1.2.2 r E

end gb

/-- Rocq `hitW_svpn`. -/
theorem hitWSvpn (rs : RegFile) (a b : BitVec 64) :
    WeakKpt.svpnOf a = WeakKpt.svpnOf b → hitW rs b → hitW rs a := by
  intro h
  unfold hitW
  rw [h]
  exact id

/-! # 2. `RowMycpu` -/

/-- Rocq `mshape` (deviation 1: the four memory events; no fetch arm). -/
def mshape (pra ps0 : Int) (j : Nat) (lb : Lbl) : Prop :=
  match j with
  | 0 => ∃ vw cls, lb = .LStore false pra vw cls ∧ vw.length = 8
  | 1 => ∃ vw cls, lb = .LStore false ps0 vw cls ∧ vw.length = 8
  | 2 => ∃ aq, aident lb = .IRead aq pra 8
  | 3 => ∃ aq, aident lb = .IRead aq ps0 8
  | _ => False

/-- Rocq `Row_mycpu` (deviation 1: no fetch items, no `pret`/`nret`). -/
def RowMycpu (k : Nat) (row : List Lbl) (pra ps0 : Int) : Prop :=
  k + 4 < row.length ∧ ∀ j, j < 4 → ∃ lb, row[k + j]? = some lb ∧ mshape pra ps0 j lb

/-- (Lean-only, stage 2 P-form) `RowMycpu` on a PREFIX row: every one of mycpu's four
memory events that is PRESENT (`k + j < row.length`) has its shape; no length conjunct (the row
may end anywhere, the end case is `wpdMycpuP`'s hook). -/
def RowMycpuP (k : Nat) (row : List Lbl) (pra ps0 : Int) : Prop :=
  ∀ j, j < 4 → k + j < row.length → ∃ lb, row[k + j]? = some lb ∧ mshape pra ps0 j lb

/-- (Lean-only) a full mycpu window is a prefix window. -/
theorem AxSpinE8.rowMycpuPOfFull (k : Nat) (row : List Lbl) (pra ps0 : Int) :
    RowMycpu k row pra ps0 → RowMycpuP k row pra ps0 :=
  fun ⟨_, Hs⟩ j hj _ => Hs j hj

/-- Rocq `row_w8`: RV64 rows — every write is at most 8 bytes. -/
def rowW8 (row : List Lbl) : Prop :=
  ∀ (k : Nat) (lb : Lbl) (rl : Bool) (b : Int) (m : Nat),
    row[k]? = some lb → aidentWr (aident lb) = some (rl, b, m) → m ≤ 8

/-- Rocq `no_rmw8`: no fused RMW of 8 bytes at `pa`. -/
def noRmw8 (row : List Lbl) (pa : Int) : Prop :=
  ∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (n : Nat),
    row[k]? = some lb → aident lb = .IRmw aq rl pa n → n ≠ 8

/-! # 3. THE CERTIFICATE -/

/-- Rocq `r1`. -/
abbrev AxSpinE8.r1 : BitVec 5 := 1#5
/-- Rocq `r2`. -/
abbrev AxSpinE8.r2 : BitVec 5 := 2#5
/-- Rocq `r4`. -/
abbrev AxSpinE8.r4 : BitVec 5 := 4#5
/-- Rocq `r8`. -/
abbrev AxSpinE8.r8 : BitVec 5 := 8#5
/-- Rocq `r10`. -/
abbrev AxSpinE8.r10 : BitVec 5 := 10#5
/-- Rocq `r15`. -/
abbrev AxSpinE8.r15 : BitVec 5 := 15#5
/-- Rocq `imm_ra`. -/
def AxSpinE8.immRa : BitVec 12 := zero_extend (m := 12) (1#6 +++ 0b000#3)
/-- Rocq `imm_s0`. -/
def AxSpinE8.immS0 : BitVec 12 := zero_extend (m := 12) (0#6 +++ 0b000#3)
/-- Rocq `sp1_of`. -/
def AxSpinE8.sp1Of (sp0 : BitVec 64) : BitVec 64 :=
  sp0 + sign_extend (m := 64) (sign_extend (m := 12) (48#6))
/-- (Lean-only) Rocq's `let va_ra`. -/
def AxSpinE8.vaRa (rs0 : RegFile) : BitVec 64 :=
  AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa
/-- (Lean-only) Rocq's `let va_s0`. -/
def AxSpinE8.vaS0 (rs0 : RegFile) : BitVec 64 :=
  AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0

/-- Rocq `ProcGeom.mycpu_a5` (deviation 2). -/
def AxSpinE8.mycpuA5 (tp0 : BitVec 64) : BitVec 64 :=
  shift_bits_left
    (sign_extend (m := 64) (Sail.BitVec.extractLsb
      ((0#64 + tp0) + sign_extend (m := 64) (sign_extend (m := 12) (0#6))) 31 0))
    (Sail.BitVec.extractLsb (7#6) (Functions.log2_xlen -i 1) 0)

/-- Rocq `ProcGeom.mycpu_ret` (deviation 2: immediate `0xbc6`, `pcm 0x0e`). -/
def AxSpinE8.mycpuRet (tp0 : BitVec 64) : BitVec 64 :=
  ((pcm 0x0e + auipcOff 17#20) + sign_extend (m := 64) (0xbc6#12)) + AxSpinE8.mycpuA5 tp0

/-- Rocq `KernelRvcDecode.frame_cancel_16` (deviation 2). -/
theorem AxSpinE8.frameCancel16 (X : BitVec 64) :
    (X + sign_extend (m := 64) (sign_extend (m := 12) (48#6))) +
      sign_extend (m := 64) (sign_extend (m := 12) (16#6)) = X := by
  rw [BitVec.add_assoc,
    show sign_extend (m := 64) (sign_extend (m := 12) (48#6)) +
      sign_extend (m := 64) (sign_extend (m := 12) (16#6)) = 0#64 by decide]
  exact BitVec.add_zero X

/-- (Lean-only) an 8-byte plain load of the bytes an 8-byte store of `v` writes is `v`. -/
theorem AxSpinE8.ldResStBytes8 (v : BitVec 64) : ldRes false 8 (stBytes 8 v) = v := by
  unfold ldRes stBytes rrv AxDataX.wrb
  rw [wordOfBytesWbytes]
  unfold AxDataX.stData extend_value sign_extend
  simp only [Bool.false_eq_true, ↓reduceIte]
  ext j hj
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, hj]

section mycpu
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
variable (Htxt : mycpuText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- (Lean-only, P1) THE GATED CORE of `wpdMycpuG`/`wpdMycpuP` on a PREFIX row: the P-form script
with the return-address pin replaced by the GATE `AxSpinT2i.Gate GT i (k + 2) (stBytes 8 ret)`
(`ret` still a parameter).  At the reload's continuation `k + 3`: `by_cases` on the reloaded
value `vra = stBytes 8 ret` — equal ⇒ the P-form script; else the gate gives `LEN ≤ k + 3`, and
the arm is `AxSpinT2i.cutReloadG` with the reload's `RLfact` when `ret`'s bytes are the spill's
(`stBytes 8 ret = stBytes 8 (gprVal rs0 r1)`; always so at `wpdMycpuG`'s `ret`), otherwise the
row-end hook `HΨend` at `k + 3` (only reachable from `wpdMycpuP`'s free `ret`). -/
theorem AxSpinE8.wpdMycpuGr (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 : BitVec 64) :
    -- the row
    RowMycpuP k (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = pcm 0x00 → hitW rs0 (pcm 0x00) →
    -- the two stack slots
    dataAtS σi T (.Store .Data) (AxSpinE8.vaRa rs0) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaRa rs0) 8 Pra → hitW rs0 (AxSpinE8.vaRa rs0) →
    dataAtS σi T (.Store .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 → hitW rs0 (AxSpinE8.vaS0 rs0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (paZ Ps0 + 8 ≤ paZ Pra ∨ paZ Pra + 8 ≤ paZ Ps0) →
    -- the return address (P1: the reload GATE against `ret`'s bytes)
    AxSpinT2i.Gate GT i (k + 2) (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    -- the row-end hook (stage 2, design §B / Q-S2-2)
    (∀ k' : Nat, k ≤ k' → k' ≤ k + 4 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vra vs0 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 2) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 3) = some vs0⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 2)
          iprop(⌜RLfact GT i (paZ Pra) (k + 2) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 3)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 3) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 4⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hc0 HPC0 Hhit0 HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hslots Hgate Hret HΨend
  have Hsh := HR
  iintro C
  -- row end at k
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := XxSt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL := XxLd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XT := XxRet L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  let F0 : BitVec 5 → BitVec 64 := fun r => gprVal rs0 r
  have HF0 : ∀ r, gprVal rs0 r = F0 r := fun _ => rfl
  -- ---- 0x00: c.addi sp,-16 (row position k) ----
  iapply (XR _ rs0 k (pcm 0x00) true ins00 none (some (2#5, AxSpinE8.sp1Of (gprVal rs0 2#5)))
    (retxRefl cpu rs0 k ib0) Hc0 HPC0 Hhit0 (tok00 σi T satp0 Htxt)
    (AxSpinE8.owOkSome 2#5 _ (by decide)) rfFIns00
    (certAddi _ rs0 (pcm 0x00) true 2#5 2#5 _ (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pcm 0x02 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  -- ---- 0x02: c.sdsp ra,8(sp) (spill at k) ----
  iapply (XS _ rs1 k (pcm 0x02) true AxSpinE8.immRa 1#5 2#5 (AxSpinE8.vaRa rs0) Pra
    (retxRefl cpu rs1 k ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (pcm 0x02) (pcm 0x00) (by decide) (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (tok02 σi T satp0 Htxt) (by rw [HF1]; ax_spin_e8_zsimp; rfl) HdaS_ra
    (hitWAgree rs0 rs1 _ Htl1 Hh_ra) Hpr_ra Hw8 (by omega))
  iintro %rs2 %ib2 %HG2 %Hgd0
  have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = pcm 0x04 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  -- row end at k + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- 0x04: c.sdsp s0,0(sp) (spill at k+1) ----
  iapply (XS _ rs2 (k + 1) (pcm 0x04) true AxSpinE8.immS0 8#5 2#5 (AxSpinE8.vaS0 rs0) Ps0
    (retxRefl cpu rs2 (k + 1) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (pcm 0x04) (pcm 0x00) (by decide) (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (tok04 σi T satp0 Htxt) (by rw [HF2]; ax_spin_e8_zsimp; rfl) HdaS_s0
    (hitWAgree rs0 rs2 _ Htl2 Hh_s0) Hpr_s0 Hw8 (by omega))
  iintro %rs3 %ib3 %HG3 %Hgd1
  have HF3 := stepRegs0 T satp0 _ rs2 _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = pcm 0x06 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- row end at k + 2
  by_cases E2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- 0x06: c.addi4spn s0,sp,16 (k+2) ----
  have Hc4 := certAddi (ctrlOkSW T satp0) rs3 (pcm 0x06) true 2#5 8#5 (caddi4spnImm 4#8)
    (by decide)
  simp only [HF3] at Hc4
  ax_spin_e8_zsimp at Hc4
  iapply (XR _ rs3 (k + 2) (pcm 0x06) true ins06 _ _
    (retxRefl cpu rs3 (k + 2) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (pcm 0x06) (pcm 0x00) (by decide) (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (tok06 σi T satp0 Htxt) (AxSpinE8.owOkSome 8#5 _ (by decide)) rfFIns06 Hc4 (by omega))
  iintro %rs4 %ib4 %HG4
  have HF4 := stepRegs T satp0 _ rs3 _ _ _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = pcm 0x08 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- ---- 0x08: c.mv a5,tp ----
  have Hc5 := certAdd (ctrlOkSW T satp0) rs4 (pcm 0x08) true 4#5 0#5 15#5 (by decide)
  simp only [HF4] at Hc5
  ax_spin_e8_zsimp at Hc5
  iapply (XR _ rs4 (k + 2) (pcm 0x08) true ins08 _ _
    (retxRefl cpu rs4 (k + 2) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (pcm 0x08) (pcm 0x00) (by decide) (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (tok08 σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFIns08 Hc5 (by omega))
  iintro %rs5 %ib5 %HG5
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = pcm 0x0a := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- ---- 0x0a: c.addiw a5,0 (sext.w) ----
  have Hc6 := certAddiw (ctrlOkSW T satp0) rs5 (pcm 0x0a) true 15#5 15#5
    (sign_extend (m := 12) (0#6)) (by decide)
  simp only [HF5] at Hc6
  ax_spin_e8_zsimp at Hc6
  iapply (XR _ rs5 (k + 2) (pcm 0x0a) true ins0a _ _
    (retxRefl cpu rs5 (k + 2) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (pcm 0x0a) (pcm 0x00) (by decide) (hitWAgree rs0 rs5 _ Htl5 Hhit0))
    (tok0a σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFIns0a Hc6 (by omega))
  iintro %rs6 %ib6 %HG6
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = pcm 0x0c := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- ---- 0x0c: c.slli a5,7 ----
  have Hc7 := certSlli (ctrlOkSW T satp0) rs6 (pcm 0x0c) true 15#5 15#5 7#6 (by decide)
  simp only [HF6] at Hc7
  ax_spin_e8_zsimp at Hc7
  iapply (XR _ rs6 (k + 2) (pcm 0x0c) true ins0c _ _
    (retxRefl cpu rs6 (k + 2) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (pcm 0x0c) (pcm 0x00) (by decide) (hitWAgree rs0 rs6 _ Htl6 Hhit0))
    (tok0c σi T satp0 Htxt) (AxSpinE8.owOkSome 15#5 _ (by decide)) rfFIns0c Hc7 (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = pcm 0x0e := by rw [gbPc T satp0 _ _ _ _ _ _ HG7]; decide
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- ---- 0x0e: auipc a0,0x11 ----
  iapply (XR _ rs7 (k + 2) (pcm 0x0e) false ins0e _ _
    (retxRefl cpu rs7 (k + 2) ib7) (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (pcm 0x0e) (pcm 0x00) (by decide) (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (tok0e σi T satp0 Htxt) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFIns0e
    (certAuipc (ctrlOkSW T satp0) rs7 (pcm 0x0e) false 10#5 17#20 (by decide)) (by omega))
  iintro %rs8 %ib8 %HG8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = pcm 0x12 := by rw [gbPc T satp0 _ _ _ _ _ _ HG8]; decide
  have Htl8 : rs8 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  -- ---- 0x12: addi a0,a0,… (deviation 2: immediate 0xbc6) ----
  have Hc9 := certAddi (ctrlOkSW T satp0) rs8 (pcm 0x12) false 10#5 10#5 0xbc6#12 (by decide)
  simp only [HF8] at Hc9
  ax_spin_e8_zsimp at Hc9
  iapply (XR _ rs8 (k + 2) (pcm 0x12) false ins12 _ _
    (retxRefl cpu rs8 (k + 2) ib8) (gbCtrl T satp0 _ _ _ _ _ _ HG8) HPC8
    (hitWSvpn rs8 (pcm 0x12) (pcm 0x00) (by decide) (hitWAgree rs0 rs8 _ Htl8 Hhit0))
    (tok12 σi T satp0 Htxt) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFIns12 Hc9 (by omega))
  iintro %rs9 %ib9 %HG9
  have HF9 := stepRegs T satp0 _ rs8 _ _ _ _ _ rs9 HF8 HG9
  have HPC9 : rs9 .PC = pcm 0x16 := by rw [gbPc T satp0 _ _ _ _ _ _ HG9]; decide
  have Htl9 : rs9 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG9).trans Htl8
  -- ---- 0x16: c.add a0,a5 ----
  have Hc10 := certAdd (ctrlOkSW T satp0) rs9 (pcm 0x16) true 15#5 10#5 10#5 (by decide)
  simp only [HF9] at Hc10
  ax_spin_e8_zsimp at Hc10
  iapply (XR _ rs9 (k + 2) (pcm 0x16) true ins16 _ _
    (retxRefl cpu rs9 (k + 2) ib9) (gbCtrl T satp0 _ _ _ _ _ _ HG9) HPC9
    (hitWSvpn rs9 (pcm 0x16) (pcm 0x00) (by decide) (hitWAgree rs0 rs9 _ Htl9 Hhit0))
    (tok16 σi T satp0 Htxt) (AxSpinE8.owOkSome 10#5 _ (by decide)) rfFIns16 Hc10 (by omega))
  iintro %rs10 %ib10 %HG10
  have HF10 := stepRegs T satp0 _ rs9 _ _ _ _ _ rs10 HF9 HG10
  have HPC10 : rs10 .PC = pcm 0x18 := by rw [gbPc T satp0 _ _ _ _ _ _ HG10]; decide
  have Htl10 : rs10 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG10).trans Htl9
  -- ---- 0x18: c.ldsp ra,8(sp) — the RELOAD of ra's spill (k+2) ----
  obtain ⟨lb0, Hlb0, vwra, cls0, rfl, Hlvw0⟩ := Hsh 0 (by omega) (by omega)
  obtain ⟨lb1, Hlb1, vws0, cls1, rfl, Hlvw1⟩ := Hsh 1 (by omega) (by omega)
  obtain ⟨lb2, Hlb2, aq2, Hid2⟩ := Hsh 2 (by omega) (by omega)
  rw [Nat.add_zero] at Hlb0
  iapply (XL _ rs10 (k + 2) (pcm 0x18) true AxSpinE8.immRa 2#5 1#5 (AxSpinE8.vaRa rs0) Pra k
    vwra cls0 (retxRefl cpu rs10 (k + 2) ib10) (gbCtrl T satp0 _ _ _ _ _ _ HG10) HPC10
    (hitWSvpn rs10 (pcm 0x18) (pcm 0x00) (by decide) (hitWAgree rs0 rs10 _ Htl10 Hhit0))
    (tok18 σi T satp0 Htxt) (by decide) (by rw [HF10]; ax_spin_e8_zsimp; rfl) HdaL_ra
    (hitWAgree rs0 rs10 _ Htl10 Hh_ra) Hpr_ra Hnt_ra Hnr_ra Hlb0 Hlvw0 (by omega) ?_ (by omega))
  · intro k' lb' rl b m ⟨h1, h2⟩ Hl Hid
    obtain rfl : k' = k + 1 := by omega
    rw [Hlb1] at Hl
    cases Hl
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨-, rfl, rfl⟩ := Hid
    rw [Hlvw1]
    omega
  iintro %vra %rs11 %ib11 %Hlvra %HG11 %Hgv2 H2
  -- the ra spill's row data is the entry ra (needed by the reload cut's `RLfact`)
  have Hd0 : graphData (gtAdGd GT) (i, k) = some vwra := by
    rw [graphData, AxWp.growLookup _ _ _ _ Hlb0]
    rfl
  have Hra0 : vwra = stBytes 8 (gprVal rs0 AxSpinE8.r1) := by
    rw [Hd0, HF1] at Hgd0
    ax_spin_e8_zsimp at Hgd0
    exact Option.some.inj Hgd0
  subst Hra0
  -- P1 GATE at the reload's boundary k + 3: a wrong reloaded value ends the row there
  by_cases Hv : ¬ vra = stBytes 8 ret
  · iclear C
    by_cases Hs : stBytes 8 ret = stBytes 8 (gprVal rs0 AxSpinE8.r1)
    · -- `ret`'s bytes are the spill's: the reload CUT refutes the arm (RLfact read back)
      rw [Hs] at Hv Hgate
      iapply (AxSpinT2i.cutReloadG L GT nm Hcons i (k + 2) (paZ Pra)
        (stBytes 8 (gprVal rs0 AxSpinE8.r1)) vra Ψ ⟨lb2, Hlb2, aq2, Hid2⟩ Hlvw0 Hgv2 Hv Hgate
        _) $$ H2
    · have Hend := AxSpinT2i.lenOfGate Hgate Hgv2 Hv
      iclear H2
      iapply (HΨend _ (by omega) (by omega) (by omega) _)
  have Hvra : vra = stBytes 8 ret := Classical.byContradiction Hv
  have HF11 := stepRegs T satp0 _ rs10 _ _ _ _ _ rs11 HF10 HG11
  have HPC11 : rs11 .PC = pcm 0x1a := by rw [gbPc T satp0 _ _ _ _ _ _ HG11]; decide
  have Htl11 : rs11 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG11).trans Htl10
  -- row end at k + 2 + 1
  by_cases E3 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2 + 1
  · iclear C
    iclear H2
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- 0x1a: c.ldsp s0,0(sp) — the RELOAD of s0's spill (k+3) ----
  iapply (XL _ rs11 (k + 2 + 1) (pcm 0x1a) true AxSpinE8.immS0 2#5 8#5 (AxSpinE8.vaS0 rs0) Ps0
    (k + 1) vws0 cls1 (retxRefl cpu rs11 (k + 2 + 1) ib11) (gbCtrl T satp0 _ _ _ _ _ _ HG11)
    HPC11
    (hitWSvpn rs11 (pcm 0x1a) (pcm 0x00) (by decide) (hitWAgree rs0 rs11 _ Htl11 Hhit0))
    (tok1a σi T satp0 Htxt) (by decide) (by rw [HF11]; ax_spin_e8_zsimp; rfl) HdaL_s0
    (hitWAgree rs0 rs11 _ Htl11 Hh_s0) Hpr_s0 Hnt_s0 Hnr_s0 Hlb1 Hlvw1 (by omega) ?_ (by omega))
  · intro k' lb' rl b m ⟨h1, h2⟩ Hl Hid
    obtain rfl : k' = k + 2 := by omega
    rw [Hlb2] at Hl
    cases Hl
    rw [Hid2] at Hid
    simp only [aidentWr, reduceCtorEq] at Hid
  iintro %vs0 %rs12 %ib12 %Hlvs0 %HG12 %Hgv3 H3
  have HF12 := stepRegs T satp0 _ rs11 _ _ _ _ _ rs12 HF11 HG12
  have HPC12 : rs12 .PC = pcm 0x1c := by rw [gbPc T satp0 _ _ _ _ _ _ HG12]; decide
  have Htl12 : rs12 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG12).trans Htl11
  -- row end at k + 2 + 1 + 1
  by_cases E4 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2 + 1 + 1
  · iclear C
    iclear H2
    iclear H3
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- 0x1c: c.addi sp,16 (k+4) ----
  have Hc13 := certAddi (ctrlOkSW T satp0) rs12 (pcm 0x1c) true 2#5 2#5
    (sign_extend (m := 12) (16#6)) (by decide)
  simp only [HF12] at Hc13
  ax_spin_e8_zsimp at Hc13
  iapply (XR _ rs12 (k + 2 + 1 + 1) (pcm 0x1c) true ins1c _ _
    (retxRefl cpu rs12 (k + 2 + 1 + 1) ib12) (gbCtrl T satp0 _ _ _ _ _ _ HG12) HPC12
    (hitWSvpn rs12 (pcm 0x1c) (pcm 0x00) (by decide) (hitWAgree rs0 rs12 _ Htl12 Hhit0))
    (tok1c σi T satp0 Htxt) (AxSpinE8.owOkSome 2#5 _ (by decide)) rfFIns1c Hc13 (by omega))
  iintro %rs13 %ib13 %HG13
  have HF13 := stepRegs T satp0 _ rs12 _ _ _ _ _ rs13 HF12 HG13
  have HPC13 : rs13 .PC = pcm 0x1e := by rw [gbPc T satp0 _ _ _ _ _ _ HG13]; decide
  have Htl13 : rs13 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG13).trans Htl12
  -- ---- 0x1e: c.ret (k+4; Q20': no stuck branch, the target is the reloaded ra) ----
  iapply (XT _ rs13 (k + 2 + 1 + 1) (pcm 0x1e)
    (retxRefl cpu rs13 (k + 2 + 1 + 1) ib13) (gbCtrl T satp0 _ _ _ _ _ _ HG13) HPC13
    (hitWSvpn rs13 (pcm 0x1e) (pcm 0x00) (by decide) (hitWAgree rs0 rs13 _ Htl13 Hhit0))
    (tok1e σi T satp0 Htxt) rfFIns1e (by omega))
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs13 _ _ _ rs' HF13 HGr
  -- the spills' row data are the entry values of ra / s0
  have Hd1 : graphData (gtAdGd GT) (i, k + 1) = some vws0 := by
    rw [graphData, AxWp.growLookup _ _ _ _ Hlb1]
    rfl
  have Hs00 : vws0 = stBytes 8 (gprVal rs0 AxSpinE8.r8) := by
    rw [Hd1, HF2] at Hgd1
    ax_spin_e8_zsimp at Hgd1
    exact Option.some.inj Hgd1
  subst Hs00
  have Hgpr1 : gprVal rs13 1#5 = ldRes false 8 vra := by
    rw [HF13]
    ax_spin_e8_zsimp
  have Hgpr8 : gprVal rs13 8#5 = ldRes false 8 vs0 := by
    rw [HF13]
    ax_spin_e8_zsimp
  iapply C $$ %vra %vs0 %rs' %ib' [] H2 H3
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl13, ?_,
    ?_, Hlvra, Hlvs0, ((HFr 1#5).trans ((HF13 1#5).symm.trans Hgpr1)),
    ((HFr 8#5).trans ((HF13 8#5).symm.trans Hgpr8)), ?_, Hd0, Hd1, Hgv2, Hgv3⟩
  · -- PC = ret: the c.ret target is the reloaded ra (`Hvra`, the gate's equal arm)
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    show jalrTgt 0#12 (gprVal rs13 1#5) = ret
    rw [Hgpr1, Hvra, AxSpinE8.ldResStBytes8, Hret]
  · -- a0 = mycpuRet tp
    rw [HFr]
    ax_spin_e8_zsimp
    rfl
  · -- sp restored
    rw [HFr]
    ax_spin_e8_zsimp
    exact AxSpinE8.frameCancel16 _
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr10 Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n10 : r ≠ 10#5 := fun h => Hr10 (by rw [h]; rfl)
      have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]

include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- (Lean-only, P1) THE GATE FORM of mycpu on a PREFIX row: `wpdMycpuP` with the return-address
pin replaced by the reload GATE `AxSpinT2i.Gate GT i (k + 2) (stBytes 8 (gprVal rs0 r1))` (a row
that continues past the ra reload read ra's spill) and `ret := gprVal rs0 r1` (the entry `ra`;
Q-P1-2).  A wrong reload value at the row end `k + 3` is REFUTED by `AxSpinT2i.cutReloadG`. -/
theorem wpdMycpuG (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (Pra Ps0 : BitVec 64) :
    -- the row
    RowMycpuP k (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = pcm 0x00 → hitW rs0 (pcm 0x00) →
    -- the two stack slots
    dataAtS σi T (.Store .Data) (AxSpinE8.vaRa rs0) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaRa rs0) 8 Pra → hitW rs0 (AxSpinE8.vaRa rs0) →
    dataAtS σi T (.Store .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 → hitW rs0 (AxSpinE8.vaS0 rs0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (paZ Ps0 + 8 ≤ paZ Pra ∨ paZ Pra + 8 ≤ paZ Ps0) →
    -- the return address (P1: the reload GATE; `ret` is the entry ra, Q-P1-2)
    AxSpinT2i.Gate GT i (k + 2) (stBytes 8 (gprVal rs0 AxSpinE8.r1)) →
    jalrTgt 0#12 (gprVal rs0 AxSpinE8.r1) = gprVal rs0 AxSpinE8.r1 →
    -- the row-end hook (stage 2, design §B / Q-S2-2)
    (∀ k' : Nat, k ≤ k' → k' ≤ k + 4 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vra vs0 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = gprVal rs0 AxSpinE8.r1 ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 2) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 3) = some vs0⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 2)
          iprop(⌜RLfact GT i (paZ Pra) (k + 2) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 3)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 3) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 4⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ :=
  AxSpinE8.wpdMycpuGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxt Ψ HΨmid k rs0 ib0
    (gprVal rs0 AxSpinE8.r1) Pra Ps0

include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdMycpu` on a PREFIX row (`RowMycpuP`; the `Hval` pin
guarded by `k + 2 < LEN`): at each of mycpu's five row positions `k .. k + 4` a `by_cases` on
`LEN ≤ position`; the row-end case is the WINDOWED hook `HΨend` (resource-free, every program
state; mycpu has no designated cut).  The continuation is reached only when `k + 4 < LEN`.
P1: the corollary of the gated core `AxSpinE8.wpdMycpuGr` via `AxSpinT2i.gateOfPinG`. -/
theorem wpdMycpuP (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64) (Pra Ps0 : BitVec 64) :
    -- the row
    RowMycpuP k (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = pcm 0x00 → hitW rs0 (pcm 0x00) →
    -- the two stack slots
    dataAtS σi T (.Store .Data) (AxSpinE8.vaRa rs0) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaRa rs0) 8 Pra → hitW rs0 (AxSpinE8.vaRa rs0) →
    dataAtS σi T (.Store .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 → hitW rs0 (AxSpinE8.vaS0 rs0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (paZ Ps0 + 8 ≤ paZ Pra ∨ paZ Pra + 8 ≤ paZ Ps0) →
    -- the return address (Q20': the reload's graph value; deviation 1)
    (k + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 2) = some (stBytes 8 ret)) → jalrTgt 0#12 ret = ret →
    -- the row-end hook (stage 2, design §B / Q-S2-2)
    (∀ k' : Nat, k ≤ k' → k' ≤ k + 4 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vra vs0 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 2) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 3) = some vs0⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 2)
          iprop(⌜RLfact GT i (paZ Pra) (k + 2) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 3)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 3) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 4⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hc0 HPC0 Hhit0 HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hslots Hval Hret HΨend
  exact AxSpinE8.wpdMycpuGr L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxt Ψ HΨmid k rs0 ib0
    ret Pra Ps0 HR Hw8 Hnr_ra Hnr_s0 Hc0 HPC0 Hhit0 HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hslots (AxSpinT2i.gateOfPinG Hval) Hret HΨend

include HL Hcons hmode hasid hppn Hfix Htxt HΨmid in
/-- Rocq `wpd_mycpu` (deviation 1: Stage C positions, `Hval`/`Hret` replace the return-fetch
pin `Hinj`/`Hstv`/`va_first_read`).  Stage 2: the full-row corollary of `wpdMycpuP` (the hook
is vacuous: `k + 4 < LEN`). -/
theorem wpdMycpu (k : Nat) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64) (Pra Ps0 : BitVec 64) :
    -- the row
    RowMycpu k (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) (paZ Ps0) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = pcm 0x00 → hitW rs0 (pcm 0x00) →
    -- the two stack slots
    dataAtS σi T (.Store .Data) (AxSpinE8.vaRa rs0) 8 Pra →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaRa rs0) 8 Pra → hitW rs0 (AxSpinE8.vaRa rs0) →
    dataAtS σi T (.Store .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaS0 rs0) 8 Ps0 → hitW rs0 (AxSpinE8.vaS0 rs0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (paZ Ps0 + 8 ≤ paZ Pra ∨ paZ Pra + 8 ≤ paZ Ps0) →
    -- the return address (Q20': the reload's graph value; deviation 1)
    graphValue (gtAdGd GT) (i, k + 2) = some (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    ⊢ (∀ (vra vs0 : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 ∧
          vra.length = 8 ∧ vs0.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0 ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 2) = some vra ∧
          graphValue (gtAdGd GT) (i, k + 3) = some vs0⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 2)
          iprop(⌜RLfact GT i (paZ Pra) (k + 2) (stBytes 8 (gprVal rs0 AxSpinE8.r1))⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, k + 3)
          iprop(⌜RLfact GT i (paZ Ps0) (k + 3) (stBytes 8 (gprVal rs0 AxSpinE8.r8))⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 4⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hc0 HPC0 Hhit0 HdaS_ra HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hslots Hval Hret
  have Hlen := HR.1
  exact wpdMycpuP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxt Ψ HΨmid k rs0 ib0
    ret Pra Ps0 (AxSpinE8.rowMycpuPOfFull _ _ _ _ HR) Hw8 Hnr_ra Hnr_s0 Hc0 HPC0 Hhit0 HdaS_ra
    HdaL_ra Hh_ra HdaS_s0 HdaL_s0 Hh_s0 Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hslots (fun _ => Hval) Hret
    (fun _ _ h2 h3 => absurd h3 (by omega))

end mycpu

end Weak
