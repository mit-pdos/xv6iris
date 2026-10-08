/-
Weak: **PHASE 5, stage 5: pop_off's HEAD** — xv6's REAL `pop_off` from its entry to the
data-dependent branch `if(c->noff == 0 && …)` (`+ 0x00 … + 0x1e`: frame; ra / s0 spills;
`s0 := frame`; `jal mycpu`; `csrr a5,sstatus`; `andi a5,a5,2`; `bnez a5 → panic`;
`lw a5,120(a0)` (noff); `bge zero,a5 → panic`; `addiw a5,a5,-1`; `sw a5,120(a0)`; `bnez a5`)
as a POSITIONAL CPS WPd at the joint instance Ixv6, interrupts off (`ctrlOkSW`), WARM TLB.
Composed with `AxSpinE8.wpdMycpu` at the inner position `k + 2`.

Rocq: `iris/AxSpinPO5.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

THE TWO PANIC BRANCHES: `if(intr_get()) panic` is REFUTED AT REGISTER LEVEL — csrr reads the
boundary's mstatus (AxSpinPOm), SIE = 0 by the regime, so the bnez is not taken
(`popSstatusClearNeq'`); `if(c->noff < 1) panic` tests a LOADED value, so under Option V the
noff load's GRAPH VALUE decides it (`Hvge`); the continuation gets the gate fact
`¬ (0 ≥ noff)` as a pure fact about the loaded bytes.

`wpdPpHead k c`: for every `k`, every bit `c` (`c` = "noff − 1 ≠ 0", the arm of the last
bnez) and every row matching `AxSpinPOr.ppHead …` at `k` (8 items under Stage C: the spills at
`k`, `k + 1`; mycpu's four events at `k + 2 .. k + 5`; the noff load at `k + 6`; the noff
store at `k + 7`):
  WPd (boundary at k, regs rs0) {{Ψ}}
  ⇐ (∀ vn rs' ib',
       ⌜regime ∧ PC = (if c then + 0x28 else + 0x20) ∧ TLB kept ∧ a0 = mycpuRet tp ∧
        sp = sp0 − 16 ∧ a5 = noff − 1 ∧ every GPR but ra / s0 / a0 / a5 / sp kept ∧ the spills'
        row data ∧ the noff load's graph value = vn ∧ ¬ (0 ≥ noff) ∧ the noff store's row data
        = stBytes 4 (noff − 1) ∧ (noff − 1 ≠ 0) = c⌝
       -∗ WPd (boundary at k + 8, regs rs') {{Ψ}})

GRAPH-VALUE PINNING (Q20', provisional Option V, `notes/weak-port-q20-offrow.md` §C.2 item 4;
Rocq: "TEMPORARY ASSUMPTION — ROW PINNING", owner decision 2026-10-03).  `ppHead` fixes which
row positions are loads / stores and the data base addresses; mycpu's RETURN (to
`pop_off + 0x0c`) is pinned by its ra reload's GRAPH VALUE (`Hval0c`), the `bge`'s
fall-through by the noff load's GRAPH VALUE (`Hvge`), and the ARM of the last `bnez` by the
same value (`Hvc`).  The theorem proves nothing about a graph whose values differ; the
follow-up ROW-INTEGRITY theorem is to discharge the value pins.  Ownership is load-bearing for
data values.

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C row `AxSpinPO5/PO6`)

`wpdPpHeadP` is `wpdPpHead`'s script on a PREFIX row (`RowShP k row (ppHead …)`, AxSpinRowP) with
one `by_cases` per row position `k, k+1, k+2, k+6, k+7, k+8` (mycpu's `k+2 .. k+6` are handled
inside `AxSpinE8.wpdMycpuP`, fed from this hook).  Row ends:
* the WINDOWED, RESOURCE-FREE hook (as `wpdMycpuP`'s header, orchestrator ruling):
  `HΨend : ∀ k', k ≤ k' → k' ≤ k + 8 → k' ≠ k + 7 → LEN ≤ k' → ∀ pr, ⊢ wpdM … ⟨pr, k'⟩ Ψ`;
* the DESIGNATED CUT `ppN` (AxSpinT2f `cutPos .ppN = t2KPp q + 7`: the row ends right after the
  noff load, where `bge zero,a5,panic` would branch) is EXCLUDED from the hook; its arm is the
  premise `KppN : LEN = k + 7 → ∀ vn pr, graphValue (i, k + 6) = some vn →
  ⊢ ann4O … (k + 6) rlN -∗ wpdM … ⟨pr, k + 7⟩ Ψ` — resource-carrying (the noff annotation in
  hand), to be supplied by `AxSpinT2h` (refutation of the flipped gate by D4 readback: the noff
  read is push_off's `sw noff` = image + 1, `AxSpinT2g.noffPop`).
The pins `Hval0c` / `Hvge` are GUARDED by position (`k + 4 < LEN →`, `k + 7 < LEN →`; on a row
that continues past `k + 7` the `ppN` gate is `allocPre`'s gate conjunct); `Hvc` (selector
`ppArm`) is vacuous at an absent position and kept.

THE SWAP (AxSpinLd4P header): the noff load `lw a5,120(a0)` runs the OPTIONAL reload leaf
`AxSpinPO5.XxLd4O rlN`: `rlN = some (kw, vw, cls)` with `AxSpinPO5.rlOk4 row pa (k + 6) rlN`
(the row item `kw < k + 6` is the field's po-latest own store `.LStore false pa vw cls`, `vw` of
length 4, `nowr row kw (k + 6) pa 4` — exactly what push_off's post provides for its `sw noff`,
data `stBytes 4 (addiw1 …)`, AxSpinPO4) is `AxSpinLd4P.XxLd4R` and hands on the annotation
`annotOwn (i, k + 6) ⌜AxSpinLd4P.rlFact4 GT i pa (k + 6) vw⌝`; `rlN = none` is the old
value-agnostic `XxLd4` (annotation `True`).  The annotation `AxSpinPO5.ann4O … rlN` is CARRIED
to the continuation and to `KppN`.  The option is what keeps `wpdPpHead` a COROLLARY (it cannot
supply push_off's store): `wpdPpHead` = `wpdPpHeadP` at `rlN = none`, `RowSh ⇒ RowShP`, hook and
cut arm vacuous under `k + 8 < LEN`, pins unguarded.  HONESTY: nothing is weakened — the
P-form's extra premises are row facts (`rlOk4`) and the two continuations; the pins it keeps are
the stage-1 pins, guarded.

THE FRAME (TODO-S2 fix, 2026-10-08): `wpdPpHeadP` takes an iProp FRAME `F` carried from the caller
to the cut: the statement is `⊢ F -∗ (… -∗ F -∗ ann4O … -∗ WPd) -∗ WPd` and the cut arm is
`KppN : … ⊢ F -∗ ann4O … -∗ WPd` (`AxSpinT2h.cutPpNF` needs push_off's genesis annotation, a
resource, there; the hook sites drop `F`).  `wpdPpHead` is the corollary at `F := True`.

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20', AxSpinPOr,
   AxSpinPOx (XxPin Option V), AxSpinPO1 (wpdPoHead pins), AxSpinE8 (Hval/Hret) entries):
   * the row shape is `ppHead (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn)` (AxSpinPOr
     deviation 1: no fetch items); the parameters `a0c` (mycpu's return fetch), `a1a` (the
     bge fall-through fetch) and `pb` (the arm target's fetch) are DROPPED.
   * POSITIONS (AxSpinPOr Stage C windows; a fetch consumes no row item): the spills at `k`,
     `k + 1` (Rocq `k + 2 / 4`, row data); the register-only `c.addi4spn`, `jal` at `k + 2`;
     mycpu at `k + 2` (Rocq `k + 7`), its continuation at `k + 6` (Rocq `k + 25`); `csrr`,
     `c.andi`, the first `c.bnez` at `k + 6`; the noff load at `k + 6` (Rocq `k + 28`, graph
     value at `k + 6`, Rocq `k + 29`); `bge`, `addiw` at `k + 7`; the noff store at `k + 7`
     (Rocq `k + 32`, row data at `k + 7`, Rocq `k + 33`); the last `c.bnez` and the
     continuation at `k + 8` (Rocq `k + 35`).
   * Rocq's premise "row item `k + 35` is the PINNED fetch of the arm's target"
     (`∃ lb aq, row !! (k+35) = Some lb ∧ aident_rd … = Some (aq, pb, 2)`) is REPLACED by the
     length premise `k + 8 < row.length` (the boundary after the last `bnez` needs a next
     row item, `XxPin`'s `k < LEN`).
   * the three `fpin` premises, the section context `stv` and the Sail premise
     `va_first_read` are DROPPED; NEW value pins (Q20'):
     `Hval0c : graphValue (gtAdGd GT) (i, k + 4) = some (stBytes 8 (ppp 0x0c))` (mycpu's ra
     reload — `AxSpinE8.wpdMycpu`'s `Hval` at `k + 2`; its `Hret` is decided at the literal),
     `Hvge : ∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
       zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false` (the bge falls through: Rocq's "the
     panic arm is row-stuck at its next fetch" becomes a value pin, AxSpinPOx deviation 3) and
     `Hvc : ∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
       (addiwm1 (ldRes false 4 vn) != zero_reg) = c` (the noff value picks the arm).  The
     continuation's conjuncts `zopz0zKzJ_s … = false` and `(… != zero_reg) = c` are kept (now
     from the pins).  Consequently `ppp28_20` / `ppp3c1a` (Rocq's arm-exclusion facts) have no
     use in the Lean proof; they are ported as stated.
2. `popSstatusClearNeq'` is proved by `bv_decide` (after unfolding the S-view and the field
   accessors, as AxSpinPO1's `ienaZero`) instead of Rocq's `Z.testbit` argument.
3. TYPES / SPELLING (as AxSpinPO1 deviation 3): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `eq_vec a b` ↦ `a == b`;
   `neq_vec a b` ↦ `a != b`; `and_vec` ↦ `&&&`; `sstatus_read` ↦ `sstatusRead`;
   `subrange_vec_dec v 31 0` ↦ `Sail.BitVec.extractLsb v 31 0`; the `let`s are inlined:
   `spb` ↦ `AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)`, `tp` ↦ `gprVal rs0 AxSpinE8.r4`,
   `nxt` ↦ `if c then ppp 0x28 else ppp 0x20`; `imm_ra`/`imm_s0` ↦
   `AxSpinE8.immRa`/`immS0`; `Interface.Ret tt` ↦ `.pure ()`.
4. INSTANCES / SECTION (as AxSpinPO1 deviation 4): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `qh_pol`/`qh_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section
   variables are explicit arguments in AxSpinE6's order (+ `Htxm Htxq`).
5. TACTICS: `pcs`/`nz`/`zq` ↦ `decide`; `zsimp` ↦ the file-local macro `ax_spin_po5_zsimp`
   (= AxSpinE8's); `lia` ↦ `omega`.  Literal register indices (`8#5`, `15#5`, `0#5`) are used
   where Rocq writes `rS0` / `rc7` / `rz`.  The trailing `Print Assumptions` is not ported.
6. KERNEL (checked against `Xv6/KernelImage.lean`, pop_off = 0x80000c98): every word of
   `popOffText` matches; `jal mycpu` at `+ 0x08` is `p08 = JAL 3260` (AxSpinPO deviation 1;
   Rocq 3222), `ppp 0x08 + 3260 = pcm 0` is decided; the branch targets `+ 0x30` (first bnez),
   `+ 0x3c` (bge) and `+ 0x28` (last bnez) are as in Rocq.

**Rocq → Lean name map.**  `addiwm1` `addiwm1`, `pop_sstatus_clear_neq'`
`popSstatusClearNeq'`, `ppp_28_20` `ppp28_20`, `ppp_3c_1a` `ppp3c1a`, `wpd_pp_head`
`wpdPpHead`.  The local instances `qh_pol`, `qh_G` are inlined (deviation 4).  Lean-only
(stage 2): file-qualified `AxSpinPO5.rlOk4`, `AxSpinPO5.ann4O`, `AxSpinPO5.rowMycpuPOf`,
`AxSpinPO5.XxLd4O`; P-form (unqualified, grepped unique) `wpdPpHeadP` (+ 1 local macro).
Reused: `RowShP`/`rowShPOfSh`/`rowShPAppL`/`rowShPAppR` (AxSpinRowP), `wpdMycpuP`/`RowMycpuP`
(AxSpinE8), `mycItem` (AxSpinPOr), `AxSpinLd4P.XxLd4R`/`rlFact4` (AxSpinLd4P), `XxLd4` (AxSpinPOx).

**Dropped:** nothing (Rocq 5 definitions/lemmas + 2 local instances; Lean 5 + 5 stage-2).
-/
import Weak.AxSpinPO1
import Weak.AxSpinPOt2
import Weak.AxSpinPOt4
import Weak.AxSpinPOt5
import Weak.AxSpinPOd2
import Weak.AxSpinLd4P
import Weak.AxSpinRowP

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. Values and bit lemmas -/

/-- Rocq `addiwm1`: `addiw a5,a5,-1`'s result. -/
def addiwm1 (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (sign_extend (m := 12) (63#6))) 31 0)

/-- Rocq `pop_sstatus_clear_neq'` (deviation 2: by `bv_decide`): with SIE = 0 the
`andi a5,a5,2` of the S-view is zero, so `bnez a5,panic` is not taken. -/
theorem popSstatusClearNeq' (m : BitVec 64) :
    (_get_Mstatus_SIE m == 1#1) = false →
    ((sstatusRead m &&& sign_extend (m := 64) (sign_extend (m := 12) (2#6))) != zero_reg) =
      false := by
  intro hSIE
  rw [show sign_extend (m := 64) (sign_extend (m := 12) (2#6)) = 2#64 by decide,
    show (zero_reg : BitVec 64) = 0#64 by decide]
  unfold sstatusRead lower_mstatus
  simp only [Mk_Sstatus,
    _update_Sstatus_SIE, _update_Sstatus_SPIE, _update_Sstatus_SPP, _update_Sstatus_VS,
    _update_Sstatus_FS, _update_Sstatus_XS, _update_Sstatus_SUM, _update_Sstatus_MXR,
    _update_Sstatus_SPELP, _update_Sstatus_UXL, _update_Sstatus_SD,
    _get_Mstatus_SIE, _get_Mstatus_SPIE, _get_Mstatus_SPP, _get_Mstatus_VS,
    _get_Mstatus_FS, _get_Mstatus_XS, _get_Mstatus_SUM, _get_Mstatus_MXR,
    _get_Mstatus_SPELP, _get_Mstatus_UXL, _get_Mstatus_SD,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    BitVec.extractLsb, zeros] at hSIE ⊢
  bv_decide

/-- Rocq `ppp_28_20`. -/
theorem ppp28_20 : ppp 0x28 ≠ ppp 0x20 := by decide
/-- Rocq `ppp_3c_1a`. -/
theorem ppp3c1a : ppp 0x3c ≠ ppp 0x1a := by decide

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_po5_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-! # 2. Stage 2: the optional 4-byte RELOAD leaf (Lean-only) -/

/-- (Lean-only, stage 2) the reload premise of a 4-byte field load at `k`, OPTIONAL: `none` (no
reload claimed; the load runs `XxLd4`, value-agnostic) or `some (kw, vw, cls)` (the field's
po-latest own store is the row item `kw < k` writing `vw`, no write of the row to `[pa, pa + 4)`
strictly between — the premises of `AxSpinLd4P.XxLd4R`). -/
def AxSpinPO5.rlOk4 (row : List Lbl) (pa : Int) (k : Nat) :
    Option (Nat × List (BitVec 8) × WmClass) → Prop
  | none => True
  | some (kw, vw, cls) =>
    row[kw]? = some (.LStore false pa vw cls) ∧ vw.length = 4 ∧ kw < k ∧ nowr row kw k pa 4

/-- (Lean-only) a prefix mycpu window from a prefix `mycSh` match. -/
theorem AxSpinPO5.rowMycpuPOf (k : Nat) (row : List Lbl) (pra ps0 : Int) :
    RowShP k row (mycSh pra ps0) → RowMycpuP k row pra ps0 := by
  intro H j Hj Hk
  obtain ⟨it, Hit, Hm⟩ := mycItem pra ps0 j Hj
  obtain ⟨lb, Hlb, Hs⟩ := H j it Hit Hk
  exact ⟨lb, Hlb, Hm lb Hs⟩

section ld4o
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- (Lean-only, stage 2) the annotation the optional reload hands on: `True` for `none`, the
`AxSpinLd4P.rlFact4` annotation at `(i, k)` for `some (kw, vw, cls)`. -/
def AxSpinPO5.ann4O (GT : GdexecT) (i : Agent) (pa : Int) (k : Nat) :
    Option (Nat × List (BitVec 8) × WmClass) → IProp GF
  | none => iprop(True)
  | some (_, vw, _) =>
    AxAnnot.annotOwn (GF := GF) (i, k) iprop(⌜AxSpinLd4P.rlFact4 GT i pa k vw⌝)

variable (L : Xlay) (GT : GdexecT) (nm : Xv6N)
variable (HL : xlayOk L) (Hcons : rvwmoCatConsistent (gtAdGd GT))
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Hfix : textFixed (gtAdGd GT) i (imgS σi))
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- (Lean-only, stage 2) THE OPTIONAL RELOAD LEAF: `XxLd4`'s premises, then privacy and an
optional reload `rl` with `AxSpinPO5.rlOk4`; the continuation also receives `ann4O … rl`.
`none` is `XxLd4` (annotation `True`); `some` is `AxSpinLd4P.XxLd4R` (annotation `rlFact4`). -/
theorem AxSpinPO5.XxLd4O (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 4 pa → hitW rs va → ¬ L.xlText (paZ pa) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    (∀ j : Nat, j < 4 → priv L (paZ pa + (j : Int)) i) →
    ∀ rl : Option (Nat × List (BitVec 8) × WmClass),
    AxSpinPO5.rlOk4 (AxOpsem.grow (gtAdGd GT) i) (paZ pa) k rl →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 4⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 4 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        AxSpinPO5.ann4O (GF := GF) GT i (paZ pa) k rl -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle Hpriv rl Hrl
  rcases rl with _ | ⟨kw, vw, cls⟩
  · iintro C
    iapply (XxLd4 L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
      s rs k pc is_rvc imm rs1 rd va pa HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle)
    iintro %vs %rs' %ib' %H1 %H2 %H3
    iapply C $$ %vs %rs' %ib' %H1 %H2 %H3
    simp only [AxSpinPO5.ann4O]
    ipureintro
    trivial
  · obtain ⟨Hw, Hlen, Hkw, Hbw⟩ := Hrl
    iintro C
    iapply (AxSpinLd4P.XxLd4R L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
      s rs k pc is_rvc imm rs1 rd va pa HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle
      kw vw cls Hpriv Hw Hlen Hkw Hbw)
    iintro %vs %rs' %ib' %H1 %H2 %H3 Ha
    iapply C $$ %vs %rs' %ib' %H1 %H2 %H3
    simp only [AxSpinPO5.ann4O]
    iexact Ha

end ld4o

/-! # 3. THE HEAD -/

section pphead
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
variable (Htxm : mycpuText σi T) (Htxq : popOffText σi T)
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

set_option maxHeartbeats 3200000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxq HΨmid in
/-- (Lean-only, stage 2) THE P-FORM of `wpdPpHead` on a PREFIX row (`RowShP`; the pins
`Hval0c` / `Hvge` GUARDED by the position after them): one `by_cases` per row position
`k, k+1, k+2, k+6, k+7, k+8` (mycpu's `k+2 .. k+6` inside `wpdMycpuP`); the row-end case is the
WINDOWED hook `HΨend` on `[k, k+8]` EXCEPT the designated cut `ppN` at `k + 7`, whose arm is the
premise `KppN` (it receives the noff load's graph value and its annotation).  The noff load runs
the optional reload leaf `AxSpinPO5.XxLd4O rlN`; its annotation is handed to the continuation. -/
theorem wpdPpHeadP (k : Nat) (c : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Pmra Pms0 Pn : BitVec 64) (rlN : Option (Nat × List (BitVec 8) × WmClass))
    (F : IProp GF) :
    -- the row (prefix)
    RowShP k (AxOpsem.grow (gtAdGd GT) i)
      (ppHead (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn)) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0 → hitW rs0 (ppp 0) → hitW rs0 (pcm 0) →
    -- the slots and the noff field
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    dj (paZ Pms0) 8 (paZ Pmra) 8 →
    -- the value pins (guarded by position)
    (k + 4 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, k + 4) = some (stBytes 8 (ppp 0x0c))) →
    (k + 7 < (AxOpsem.grow (gtAdGd GT) i).length →
      ∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
        zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = c) →
    -- the noff load's (optional) reload premise
    AxSpinPO5.rlOk4 (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) (k + 6) rlN →
    -- the row-end hook (windowed; NOT at the designated cut `k + 7`)
    (∀ k' : Nat, k ≤ k' → k' ≤ k + 8 → k' ≠ k + 7 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    -- the designated cut ppN (row ends right after the noff load)
    ((AxOpsem.grow (gtAdGd GT) i).length = k + 7 →
      ∀ (vn : List (BitVec 8)) (pr : Pexv6), graphValue (gtAdGd GT) (i, k + 6) = some vn →
        ⊢ F -∗ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
          @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
            ⟨pr, k + 7⟩ Ψ) →
    ⊢ F -∗ (∀ (vn : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧
          rs' .PC = (if c then ppp 0x28 else ppp 0x20) ∧
          rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) ∧
          vn.length = 4 ∧ gprVal rs' AxSpinE8.r15 = addiwm1 (ldRes false 4 vn) ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 6) = some vn ∧
          zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false ∧
          graphData (gtAdGd GT) (i, k + 7) = some (stBytes 4 (addiwm1 (ldRes false 4 vn))) ∧
          (addiwm1 (ldRes false 4 vn) != zero_reg) = c⌝ -∗
        F -∗ AxSpinPO5.ann4O (GF := GF) GT i (paZ Pn) (k + 6) rlN -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 8⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hw8 Hnr_mra Hnr_ms0 Hwle Hnrn Hc0 HPC0 Hhit0 HhitM
    ⟨HdaS_ra, _, Hh_ra, Hpr_ra, _⟩ ⟨HdaS_s0, _, Hh_s0, Hpr_s0, _⟩
    ⟨HdaS_mra, HdaL_mra, Hh_mra, Hpr_mra, Hnt_mra⟩ ⟨HdaS_ms0, HdaL_ms0, Hh_ms0, Hpr_ms0, Hnt_ms0⟩
    ⟨HdaS_n, HdaL_n, Hh_n, Hpr_n, Hnt_n⟩ Hdm Hval0c Hvge Hvc HrlN HΨend KppN
  iintro HF C
  -- row end at k
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k
  · iclear C
    iclear HF
    iapply (HΨend _ (by omega) (by omega) (by omega) (by omega) _)
  obtain ⟨T00, T02, T04, T06, T08, T0c, T10, T12, T14, T16, T1a, T1c, T1e, -⟩ := Htxq
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS := XxSt L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XM := XxRegm L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL4 := AxSpinPO5.XxLd4O L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS4 := XxSt4 L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XP := XxPin L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have WM := wpdMycpuP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Ψ HΨmid
  -- ---- + 0x00: c.addi sp,-16 (row position k) ----
  iapply (XR _ rs0 k (ppp 0x00) true ins00 none
    (some (2#5, AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)))
    (retxRefl cpu rs0 k ib0) Hc0 HPC0
    (hitWSvpn rs0 (ppp 0x00) (ppp 0) (by decide) Hhit0)
    (tw1141 σi T satp0 _ T00) (AxSpinE8.owOkSome 2#5 _ (by decide)) rfFIns00
    (certAddi _ rs0 (ppp 0x00) true 2#5 2#5 _ (by decide)) (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = ppp 0x02 := by rw [gbPc T satp0 _ _ _ _ _ _ HG1]; decide
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  have Esp1 : gprVal rs1 AxSpinE8.r2 = AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) := by
    rw [HF1]; ax_spin_po5_zsimp
  -- ---- + 0x02: c.sdsp ra,8(sp) (spill at k) ----
  iapply (XS _ rs1 k (ppp 0x02) true AxSpinE8.immRa 1#5 2#5
    (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa) Pra
    (retxRefl cpu rs1 k ib1) (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1
    (hitWSvpn rs1 (ppp 0x02) (ppp 0) (by decide) (hitWAgree rs0 rs1 _ Htl1 Hhit0))
    (twE406 σi T satp0 _ T02) (by rw [Esp1]) HdaS_ra
    (hitWAgree rs0 rs1 _ Htl1 Hh_ra) Hpr_ra Hw8 (by omega))
  iintro %rs2 %ib2 %HG2 %Hgd0
  have HF2 := stepRegs0 T satp0 _ rs1 _ _ _ rs2 HF1 HG2
  have HPC2 : rs2 .PC = ppp 0x04 := by rw [gbPc T satp0 _ _ _ _ _ _ HG2]; decide
  have Htl2 : rs2 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG2).trans Htl1
  have Esp2 : gprVal rs2 AxSpinE8.r2 = AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) := by
    rw [HF2]; ax_spin_po5_zsimp
  -- row end at k + 1
  by_cases E1 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 1
  · iclear C
    iclear HF
    iapply (HΨend _ (by omega) (by omega) (by omega) (by omega) _)
  -- ---- + 0x04: c.sdsp s0,0(sp) (spill at k+1) ----
  iapply (XS _ rs2 (k + 1) (ppp 0x04) true AxSpinE8.immS0 8#5 2#5
    (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0) Ps0
    (retxRefl cpu rs2 (k + 1) ib2) (gbCtrl T satp0 _ _ _ _ _ _ HG2) HPC2
    (hitWSvpn rs2 (ppp 0x04) (ppp 0) (by decide) (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (twE022 σi T satp0 _ T04) (by rw [Esp2]) HdaS_s0
    (hitWAgree rs0 rs2 _ Htl2 Hh_s0) Hpr_s0 Hw8 (by omega))
  iintro %rs3 %ib3 %HG3 %Hgd1
  have HF3 := stepRegs0 T satp0 _ rs2 _ _ _ rs3 HF2 HG3
  have HPC3 : rs3 .PC = ppp 0x06 := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- row end at k + 2
  by_cases E2 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 2
  · iclear C
    iclear HF
    iapply (HΨend _ (by omega) (by omega) (by omega) (by omega) _)
  -- ---- + 0x06: c.addi4spn s0,sp,16 (k+2) ----
  have Hc4 := certAddi (ctrlOkSW T satp0) rs3 (ppp 0x06) true 2#5 8#5 (caddi4spnImm 4#8)
    (by decide)
  simp only [HF3] at Hc4
  ax_spin_po5_zsimp at Hc4
  iapply (XR _ rs3 (k + 2) (ppp 0x06) true ins06 _ _
    (retxRefl cpu rs3 (k + 2) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (ppp 0x06) (ppp 0) (by decide) (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (tw0800 σi T satp0 _ T06) (AxSpinE8.owOkSome 8#5 _ (by decide)) rfFIns06 Hc4 (by omega))
  iintro %rs4 %ib4 %HG4
  have HF4 := stepRegs T satp0 _ rs3 _ _ _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = ppp 0x08 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- ---- + 0x08: jal ra,mycpu (k+2) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs4 (ppp 0x08) false p08 (some (pcm 0))
      (some (1#5, BitVec.addInt (ppp 0x08) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs4 (ppp 0x08)
      false 3260#21 1#5 (by decide)
    rw [show ppp 0x08 + sign_extend (m := 64) 3260#21 = pcm 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (ppp 0x08) (incr false)) =
      some (1#5, BitVec.addInt (ppp 0x08) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs4 (k + 2) (ppp 0x08) false p08 (some (pcm 0))
    (some (1#5, BitVec.addInt (ppp 0x08) (incr false)))
    (retxRefl cpu rs4 (k + 2) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (ppp 0x08) (ppp 0) (by decide) (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (tw4P08 σi T satp0 _ T08) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 3260#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs5 %ib5 %HG5
  have HF5 := stepRegs T satp0 _ rs4 _ _ _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = pcm 0 := gbPc T satp0 _ _ _ _ _ _ HG5
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  have Esp5 : gprVal rs5 AxSpinE8.r2 = AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) := by
    rw [HF5]; ax_spin_po5_zsimp
  have Etp5 : gprVal rs5 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := by
    rw [HF5]; ax_spin_po5_zsimp
  have Evra : AxSpinE8.vaRa rs5 = AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
      sign_extend (m := 64) AxSpinE8.immRa := by
    unfold AxSpinE8.vaRa; rw [Esp5]
  have Evs0 : AxSpinE8.vaS0 rs5 = AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
      sign_extend (m := 64) AxSpinE8.immS0 := by
    unfold AxSpinE8.vaS0; rw [Esp5]
  -- ---- mycpu, at k+2 (its P-form; its row ends are our hook's) ----
  have HRm0 : RowShP (k + 2) (AxOpsem.grow (gtAdGd GT) i) (mycSh (paZ Pmra) (paZ Pms0)) :=
    rowShPAppR (s1 := [.RS (paZ Pra) 8, .RS (paZ Ps0) 8])
      (rowShPAppL (s1 := [.RS (paZ Pra) 8, .RS (paZ Ps0) 8] ++ mycSh (paZ Pmra) (paZ Pms0))
        (s2 := [.RL (paZ Pn) 4, .RS (paZ Pn) 4]) HR)
  have WM' := WM (k + 2) rs5 ib5 (ppp 0x0c) Pmra Pms0
    (AxSpinPO5.rowMycpuPOf (k + 2) _ _ _ HRm0) Hw8 Hnr_mra Hnr_ms0
    (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5 (hitWAgree rs0 rs5 _ Htl5 HhitM)
    (by rw [Evra]; exact HdaS_mra) (by rw [Evra]; exact HdaL_mra)
    (by rw [Evra]; exact hitWAgree rs0 rs5 _ Htl5 Hh_mra)
    (by rw [Evs0]; exact HdaS_ms0) (by rw [Evs0]; exact HdaL_ms0)
    (by rw [Evs0]; exact hitWAgree rs0 rs5 _ Htl5 Hh_ms0)
    Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0 (by unfold dj at Hdm; omega)
    (fun h => by rw [show k + 2 + 2 = k + 4 by omega]; exact Hval0c (by omega)) (by decide)
    (fun k' h1 h2 h3 pr => HΨend k' (by omega) (by omega) (by omega) h3 pr)
  rw [show k + 2 + 4 = k + 6 by omega] at WM'
  iapply WM'
  iintro %vmra %vms0 %rs6 %ib6 %HM - -
  obtain ⟨Hc6, HPC6, Htl6', Ha06, Hsp6, -, -, -, -, Hkeep6, -, -, -, -⟩ := HM
  have Htl6 : rs6 .tlb = rs0 .tlb := Htl6'.trans Htl5
  have Ea06 : gprVal rs6 10#5 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) := by
    rw [← Etp5]; exact Ha06
  -- row end at k + 6
  by_cases E6 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 6
  · iclear C
    iclear HF
    iapply (HΨend _ (by omega) (by omega) (by omega) (by omega) _)
  -- ---- + 0x0c: csrr a5,sstatus (k+6) ----
  have HSIE : (_get_Mstatus_SIE (rs6 .mstatus) == 1#1) = false := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, H, -⟩, -⟩ := Hc6
    exact H
  iapply (XM _ rs6 (k + 6) (ppp 0x0c) false p0c none
    (some (15#5, sstatusRead (rs6 .mstatus)))
    (retxRefl cpu rs6 (k + 6) ib6) Hc6 HPC6
    (hitWSvpn rs6 (ppp 0x0c) (ppp 0) (by decide) (hitWAgree rs0 rs6 _ Htl6 Hhit0))
    (tw4P0c σi T satp0 _ T0c) (AxSpinE8.owOkSome 15#5 _ (by decide))
    (CertBmP0c σi T satp0 dok0 .DKSt rs6 (ppp 0x0c) .CPend false) (by omega))
  iintro %rs7 %ib7 %HG7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 (fun _ => rfl) HG7
  have HPC7 : rs7 .PC = ppp 0x10 := by rw [gbPc T satp0 _ _ _ _ _ _ HG7]; decide
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- ---- + 0x10: c.andi a5,2 (k+6) ----
  have Hc8 := certAndi (ctrlOkSW T satp0) rs7 (ppp 0x10) true 15#5 15#5
    (sign_extend (m := 12) (2#6)) (by decide)
  simp only [HF7] at Hc8
  ax_spin_po5_zsimp at Hc8
  iapply (XR _ rs7 (k + 6) (ppp 0x10) true p10 _ _
    (retxRefl cpu rs7 (k + 6) ib7) (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (ppp 0x10) (ppp 0) (by decide) (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (tw8b89 σi T satp0 _ T10) (AxSpinE8.owOkSome 15#5 _ (by decide))
    (rfFAndi _ _ _) Hc8 (by omega))
  iintro %rs8 %ib8 %HG8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = ppp 0x12 := by rw [gbPc T satp0 _ _ _ _ _ _ HG8]; decide
  have Htl8 : rs8 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  -- ---- + 0x12: c.bnez a5,panic — REFUTED at register level (SIE = 0) (k+6) ----
  have Hc9 : CertC (ctrlOkSW T satp0) rs8 (ppp 0x12) true AxSpinPO.p12 none none := by
    have h := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs8 (ppp 0x12) true
      (sign_extend (m := 13) (15#8 +++ 0b0#1)) 0#5 15#5 .BNE (by decide)
    have Ea8 : gval 15#5 rs8 =
        sstatusRead (rs6 .mstatus) &&& sign_extend (m := 64) (sign_extend (m := 12) (2#6)) := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs8 15#5 = _
      rw [HF8]
      ax_spin_po5_zsimp
    have Ez : gval 0#5 rs8 = zero_reg := by
      unfold gval
      rw [if_pos (by decide)]
    have Eot : brOt .BNE 15#5 0#5 rs8
        (ppp 0x12 + sign_extend (m := 64) (sign_extend (m := 13) (15#8 +++ 0b0#1))) = none := by
      unfold brOt AxSymCtl2.bcond
      rw [Ea8, Ez, popSstatusClearNeq' _ HSIE]
      rfl
    rw [Eot] at h
    exact h
  iapply (XR _ rs8 (k + 6) (ppp 0x12) true AxSpinPO.p12 none none
    (retxRefl cpu rs8 (k + 6) ib8) (gbCtrl T satp0 _ _ _ _ _ _ HG8) HPC8
    (hitWSvpn rs8 (ppp 0x12) (ppp 0) (by decide) (hitWAgree rs0 rs8 _ Htl8 Hhit0))
    (twEf99 σi T satp0 _ T12) trivial (rfFBtype _ _ _ _) Hc9 (by omega))
  iintro %rs9 %ib9 %HG9
  have HF9 := stepRegs0 T satp0 _ rs8 _ _ _ rs9 HF8 HG9
  have HPC9 : rs9 .PC = ppp 0x14 := by rw [gbPc T satp0 _ _ _ _ _ _ HG9]; decide
  have Htl9 : rs9 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG9).trans Htl8
  have Ea09 : gprVal rs9 10#5 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) := by
    rw [HF9]; ax_spin_po5_zsimp; exact Ea06
  -- ---- + 0x14: lw a5,120(a0) — noff (k+6), the optional RELOAD leaf ----
  iapply (XL4 _ rs9 (k + 6) (ppp 0x14) true i120 10#5 15#5
    (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn
    (retxRefl cpu rs9 (k + 6) ib9) (gbCtrl T satp0 _ _ _ _ _ _ HG9) HPC9
    (hitWSvpn rs9 (ppp 0x14) (ppp 0) (by decide) (hitWAgree rs0 rs9 _ Htl9 Hhit0))
    (tw5d3c σi T satp0 _ T14) (by decide) (by rw [Ea09]) HdaL_n
    (hitWAgree rs0 rs9 _ Htl9 Hh_n) Hnt_n Hnrn (by omega) Hpr_n rlN HrlN)
  iintro %vn %rs10 %ib10 %Hlvn %HG10 %Hgv6 HaN
  have HF10 := stepRegs T satp0 _ rs9 _ _ _ _ _ rs10 HF9 HG10
  have HPC10 : rs10 .PC = ppp 0x16 := by rw [gbPc T satp0 _ _ _ _ _ _ HG10]; decide
  have Htl10 : rs10 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG10).trans Htl9
  -- row end at k + 7: THE DESIGNATED CUT ppN (the arm is the premise `KppN`)
  by_cases E7 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 7
  · iclear C
    iapply (KppN (by omega) vn _ Hgv6) $$ HF HaN
  -- ---- + 0x16: bge zero,a5,panic — the gate (guarded pin `Hvge`) (k+7) ----
  have Hge : zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false := Hvge (by omega) vn Hgv6
  have Hcg := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs10
    (ppp 0x16) false 38#13 15#5 0#5 .BGE (by decide)
  have Htg16 : tgtOf (brOt .BGE 0#5 15#5 rs10 (ppp 0x16 + sign_extend (m := 64) 38#13))
      (ppp 0x16) false = ppp 0x1a := by
    have Ea5 : gval 15#5 rs10 = ldRes false 4 vn := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs10 15#5 = _
      rw [HF10]
      ax_spin_po5_zsimp
    have Ez : gval 0#5 rs10 = zero_reg := by
      unfold gval
      rw [if_pos (by decide)]
    unfold tgtOf brOt AxSymCtl2.bcond
    rw [Ea5, Ez, Hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    decide
  iapply (XP _ rs10 (k + 7) (ppp 0x16) false p16 _ none (ppp 0x1a)
    (retxRefl cpu rs10 (k + 7) ib10) (gbCtrl T satp0 _ _ _ _ _ _ HG10) HPC10
    (hitWSvpn rs10 (ppp 0x16) (ppp 0) (by decide) (hitWAgree rs0 rs10 _ Htl10 Hhit0))
    (tw4P16 σi T satp0 _ T16) trivial (rfFBtype _ _ _ _) Hcg (by omega) Htg16)
  iintro %rs11 %ib11 %HGP
  obtain ⟨HG11, Htg11⟩ := HGP
  have HF11 := stepRegs0 T satp0 _ rs10 _ _ _ rs11 HF10 HG11
  have HPC11 : rs11 .PC = ppp 0x1a := by rw [gbPc T satp0 _ _ _ _ _ _ HG11]; exact Htg11
  have Htl11 : rs11 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG11).trans Htl10
  -- ---- + 0x1a: addiw a5,a5,-1 (k+7) ----
  have Hc12 : CertC (ctrlOkSW T satp0) rs11 (ppp 0x1a) true p1a none
      (some (15#5, addiwm1 (ldRes false 4 vn))) := by
    have h := certAddiw (ctrlOkSW T satp0) rs11 (ppp 0x1a) true 15#5 15#5
      (sign_extend (m := 12) (63#6)) (by decide)
    simp only [HF11] at h
    ax_spin_po5_zsimp at h
    exact h
  iapply (XR _ rs11 (k + 7) (ppp 0x1a) true p1a _ _
    (retxRefl cpu rs11 (k + 7) ib11) (gbCtrl T satp0 _ _ _ _ _ _ HG11) HPC11
    (hitWSvpn rs11 (ppp 0x1a) (ppp 0) (by decide) (hitWAgree rs0 rs11 _ Htl11 Hhit0))
    (tw37fd σi T satp0 _ T1a) (AxSpinE8.owOkSome 15#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addiw _ _ _)) Hc12 (by omega))
  iintro %rs12 %ib12 %HG12
  have HF12 := stepRegs T satp0 _ rs11 _ _ _ _ _ rs12 HF11 HG12
  have HPC12 : rs12 .PC = ppp 0x1c := by rw [gbPc T satp0 _ _ _ _ _ _ HG12]; decide
  have Htl12 : rs12 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG12).trans Htl11
  have Ea012 : gprVal rs12 10#5 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) := by
    rw [HF12]; ax_spin_po5_zsimp; exact Ea06
  -- ---- + 0x1c: sw a5,120(a0) — noff (k+7) ----
  iapply (XS4 _ rs12 (k + 7) (ppp 0x1c) true i120 15#5 10#5
    (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn
    (retxRefl cpu rs12 (k + 7) ib12) (gbCtrl T satp0 _ _ _ _ _ _ HG12) HPC12
    (hitWSvpn rs12 (ppp 0x1c) (ppp 0) (by decide) (hitWAgree rs0 rs12 _ Htl12 Hhit0))
    (twDd3c σi T satp0 _ T1c) (by rw [Ea012]) HdaS_n
    (hitWAgree rs0 rs12 _ Htl12 Hh_n) Hpr_n Hwle (by omega))
  iintro %rs13 %ib13 %HG13 %Hgd7
  have HF13 := stepRegs0 T satp0 _ rs12 _ _ _ rs13 HF12 HG13
  have HPC13 : rs13 .PC = ppp 0x1e := by rw [gbPc T satp0 _ _ _ _ _ _ HG13]; decide
  have Htl13 : rs13 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG13).trans Htl12
  -- row end at k + 8
  by_cases E8 : (AxOpsem.grow (gtAdGd GT) i).length ≤ k + 8
  · iclear C
    iclear HF
    iclear HaN
    iapply (HΨend _ (by omega) (by omega) (by omega) (by omega) _)
  -- ---- + 0x1e: c.bnez a5 — the noff load's VALUE picks the arm (k+8) ----
  have Hc : (addiwm1 (ldRes false 4 vn) != zero_reg) = c := Hvc vn Hgv6
  have Hcb := certBTYPE (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs13
    (ppp 0x1e) true (sign_extend (m := 13) (5#8 +++ 0b0#1)) 0#5 15#5 .BNE (by decide)
  have Htgt : tgtOf (brOt .BNE 15#5 0#5 rs13
      (ppp 0x1e + sign_extend (m := 64) (sign_extend (m := 13) (5#8 +++ 0b0#1))))
      (ppp 0x1e) true = (if c then ppp 0x28 else ppp 0x20) := by
    have Ea5 : gval 15#5 rs13 = addiwm1 (ldRes false 4 vn) := by
      unfold gval
      rw [if_neg (by decide)]
      show gprVal rs13 15#5 = _
      rw [HF13]
      ax_spin_po5_zsimp
    have Ez : gval 0#5 rs13 = zero_reg := by
      unfold gval
      rw [if_pos (by decide)]
    unfold tgtOf brOt AxSymCtl2.bcond
    rw [Ea5, Ez, Hc]
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> decide
  iapply (XP _ rs13 (k + 8) (ppp 0x1e) true p1e _ none
    (if c then ppp 0x28 else ppp 0x20)
    (retxRefl cpu rs13 (k + 8) ib13) (gbCtrl T satp0 _ _ _ _ _ _ HG13) HPC13
    (hitWSvpn rs13 (ppp 0x1e) (ppp 0) (by decide) (hitWAgree rs0 rs13 _ Htl13 Hhit0))
    (twE789 σi T satp0 _ T1e) trivial (rfFBtype _ _ _ _) Hcb (by omega) Htgt)
  iintro %rs' %ib' %HGP
  obtain ⟨HGr, Htg⟩ := HGP
  have HFr := stepRegs0 T satp0 _ rs13 _ _ _ rs' HF13 HGr
  iapply C $$ %vn %rs' %ib' [] HF HaN
  ipureintro
  refine ⟨gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl13, ?_,
    ?_, Hlvn, ?_, ?_, ?_, ?_, Hgv6, Hge, ?_, Hc⟩
  · -- PC = the arm's target
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    exact Htg
  · -- a0 = mycpuRet tp
    rw [HFr]
    ax_spin_po5_zsimp
    exact Ea06
  · -- sp = the frame
    rw [HFr]
    ax_spin_po5_zsimp
    exact Hsp6.trans Esp5
  · -- a5 = noff - 1
    rw [HFr]
    ax_spin_po5_zsimp
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr10 Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      rw [Hkeep6 r Hr1 Hr2 Hr8 Hr10 Hr15, HF5]
      simp (disch := assumption) only [AxSpinE8.updOther]
  · -- the two spills' row data
    rw [Hgd0, HF1]
    ax_spin_po5_zsimp
  · rw [Hgd1, HF2]
    ax_spin_po5_zsimp
  · -- the noff store's row data
    rw [Hgd7, HF12]
    ax_spin_po5_zsimp

include HL Hcons hmode hasid hppn Hfix Htxm Htxq HΨmid in
/-- Rocq `wpd_pp_head` (deviation 1: Stage C positions; value pins `Hval0c`/`Hvge`/`Hvc`
replace the `fpin` premises; the arm-fetch row premise becomes `k + 8 < row.length`).  Stage 2:
the full-row corollary of `wpdPpHeadP` (no reload claimed, `rlN = none`; the hook and the cut
arm are vacuous under `k + 8 < LEN`; the pins unguarded). -/
theorem wpdPpHead (k : Nat) (c : Bool) (rs0 : RegFile) (ib0 : Ibch)
    (Pra Ps0 Pmra Pms0 Pn : BitVec 64) :
    -- the row
    RowSh k (AxOpsem.grow (gtAdGd GT) i)
      (ppHead (paZ Pra) (paZ Ps0) (paZ Pmra) (paZ Pms0) (paZ Pn)) →
    k + 8 < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = ppp 0 → hitW rs0 (ppp 0) → hitW rs0 (pcm 0) →
    -- the slots and the noff field
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immRa) Pra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) + sign_extend (m := 64) AxSpinE8.immS0) Ps0 →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immRa) Pmra →
    AxSpinPO1.slot8 σi T L i rs0
      (AxSpinE8.sp1Of (AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2)) +
        sign_extend (m := 64) AxSpinE8.immS0) Pms0 →
    fld4 σi T L i rs0
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn →
    dj (paZ Pms0) 8 (paZ Pmra) 8 →
    -- the value pins (Q20': mycpu's ra reload and the noff load; deviation 1)
    graphValue (gtAdGd GT) (i, k + 4) = some (stBytes 8 (ppp 0x0c)) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
      zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false) →
    (∀ vn, graphValue (gtAdGd GT) (i, k + 6) = some vn →
      (addiwm1 (ldRes false 4 vn) != zero_reg) = c) →
    ⊢ (∀ (vn : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧
          rs' .PC = (if c then ppp 0x28 else ppp 0x20) ∧
          rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 = AxSpinE8.sp1Of (gprVal rs0 AxSpinE8.r2) ∧
          vn.length = 4 ∧ gprVal rs' AxSpinE8.r15 = addiwm1 (ldRes false 4 vn) ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 10 →
            r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphData (gtAdGd GT) (i, k) = some (stBytes 8 (gprVal rs0 AxSpinE8.r1)) ∧
          graphData (gtAdGd GT) (i, k + 1) = some (stBytes 8 (gprVal rs0 AxSpinE8.r8)) ∧
          graphValue (gtAdGd GT) (i, k + 6) = some vn ∧
          zopz0zKzJ_s zero_reg (ldRes false 4 vn) = false ∧
          graphData (gtAdGd GT) (i, k + 7) = some (stBytes 4 (addiwm1 (ldRes false 4 vn))) ∧
          (addiwm1 (ldRes false 4 vn) != zero_reg) = c⌝ -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 8⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, k⟩ Ψ := by
  intro HR Hlen Hw8 Hnr_mra Hnr_ms0 Hwle Hnrn Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bmra Bms0 Bn Hdm
    Hval0c Hvge Hvc
  iintro C
  iapply (wpdPpHeadP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxq Ψ HΨmid
    k c rs0 ib0 Pra Ps0 Pmra Pms0 Pn none iprop(True) (rowShPOfSh HR) Hw8 Hnr_mra Hnr_ms0 Hwle
    Hnrn Hc0 HPC0 Hhit0 HhitM Bra Bs0 Bmra Bms0 Bn Hdm (fun _ => Hval0c) (fun _ => Hvge) Hvc
    trivial (fun _ _ h2 _ h4 => absurd h4 (by omega)) (fun h => absurd h (by omega))) $$ [] [C]
  · ipureintro
    trivial
  · iintro %vn %rs' %ib' %H - -
    iapply C $$ %vn %rs' %ib' %H

end pphead

end Weak
