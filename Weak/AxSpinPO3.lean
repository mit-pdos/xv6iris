/-
Weak: **PHASE 5, stage 5: push_off's TAIL** — xv6's REAL `push_off` from `+ 0x18` to its
return (`jal mycpu; lw a5,120(a0); addiw a5,a5,1; sw a5,120(a0)`; the three callee-saved
reloads; `addi16sp`; `c.ret`) as a POSITIONAL CPS WPd at the joint instance Ixv6, interrupts
off (`ctrlOkSW`), WARM TLB.  Composed with `AxSpinE8.wpdMycpu` at the inner position `t`.

Rocq: `iris/AxSpinPO3.v` @ xxvzwolszwmp.

## The Rocq header, in substance (as restated under Stage C)

`wpdPoTail t`: for every `t` and every row matching `AxSpinPOr.poTail …` at `t` (9 items under
Stage C: mycpu's four events at `t .. t+3`; the `noff` load at `t+4`; the `noff` store at
`t+5`; the three reloads at `t+6 .. t+8`):
  WPd (boundary at t, regs rs0) {{Ψ}}
  ⇐ (∀ vn vra' vs0' vs1' rs' ib',
       ⌜regime ∧ PC = ret ∧ TLB kept ∧ a0 = mycpuRet tp ∧ sp = spb + 32 ∧ a5 = addiw1 (noff
        bytes) ∧ ra / s0 / s1 = the RELOADED words ∧ every other GPR kept ∧ the noff load's
        graph value = vn ∧ the noff store's row data = stBytes 4 (addiw1 …) ∧ the reloads'
        graph values = vra' / vs0' / vs1'⌝
       -∗ three reload annotations (reload bytes = the spills' row bytes)
       -∗ WPd (boundary at t + 9, regs rs') {{Ψ}})
where `spb` = the entry sp (push_off's frame), `tp` = the entry tp.  mycpu's own two reload
annotations are DROPPED (affine) — only push_off's reloads are handed on.
PREMISES: the three spills are given by the caller as ROW facts (position, label, "no write to
the slot between the spill and `t`", `nowr`); the cpu field `noff`: `dataAtS` both ways,
privacy (4 bytes of hart `i`'s), not text, `rowWle` (writes at the field ≤ 4 bytes) and
`noRmwn`; the slots pairwise `dj`.

GRAPH-VALUE PINNING (Q20', provisional Option V, `notes/weak-port-q20-offrow.md` §C.2 item 4;
Rocq: "TEMPORARY ASSUMPTION — ROW PINNING", owner decision 2026-10-03).  `poTail` fixes which
row positions are loads / stores and the data base addresses; the two RETURNS (mycpu's, to
`push_off + 0x1c`, and push_off's own, to `ret`) are pinned by the ra reloads' GRAPH VALUES
(`Hval1c`, `Hval`).  The theorem proves nothing about a graph whose reload values differ; the
follow-up ROW-INTEGRITY theorem is to discharge the value pins from the `RLfact` readback.
Ownership is load-bearing for data values (the reload annotations' "reload bytes = spill
bytes" come from hart `i`'s private ownership of the slots).

## Stage 2 P-FORM (Lean-only; notes/weak-lb-thm2-stage2.md §B, §C, Q-S2-1/2; as AxSpinE8)

`wpdPoTailP` is `wpdPoTail` on a PREFIX row: `RowShP t row (poTail …)` (AxSpinRowP), no length
premise, the pins `Hval1c` / `Hval` GUARDED (`t + 2 < LEN → …`, `t + 6 < LEN → …`), and the
WINDOWED, RESOURCE-FREE row-end hook (orchestrator ruling, exactly AxSpinE8's form)
  `HΨend : ∀ k', t ≤ k' → k' ≤ t + 9 → (grow (gtAdGd GT) i).length ≤ k' →
     ∀ pr : Pexv6, ⊢ wpdM … .MaybeStuck i ⟨pr, k'⟩ Ψ`.
Same script with one `by_cases` per row position (`t`, `t + 4` … `t + 9`; mycpu's
`[t, t + 4]` is `AxSpinE8.wpdMycpuP`'s, handed the sub-window of the hook); the end case is the
hook (annotations in hand are cleared — affine).  push_off has no designated cut.  The
continuation is reached only when `t + 9 < LEN`.  TWO additions to the continuation (the stage-2
pop_off arms need them):
* the noff load runs the CONDITIONAL GENESIS leaf `AxSpinPO3.xxLd4C` (below) instead of `XxLd4`;
  the continuation receives `∀ _ : AxSpinLd4P.noWrBefore row (t + 4) (paZ Pn) 4,
  (i, t + 4) ↦ₐ ⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (t + 4)⌝` (last wand);
* the pure post's FIRST conjunct is the `sw noff` row label with its data,
  `∃ cls, row[t + 5]? = some (.LStore false (paZ Pn) (stBytes 4 (addiw1 (ldRes false 4 vn))) cls)`
  (what `AxSpinLd4P.XxLd4R`'s `Hkw_lbl` takes); `.2` of the post is the old conjunction.
`wpdPoTail` keeps its exact statement and is now the corollary (`rowShPOfSh`; hook vacuous
under `t + 9 < LEN`; pins unguarded; label and annotation dropped).

`AxSpinPO3.xxLd4C` (Lean-only): `XxLd4`'s premises + the four bytes' `priv`; the continuation
gets the genesis annotation UNDER `noWrBefore` — by `by_cases` on `noWrBefore`: if it holds the
load runs `AxSpinLd4P.XxLd4G` (the annotation is handed on), otherwise plain `XxLd4` (the
conditional is vacuous).  HONESTY: no new premise; the conditional form is what keeps the old
lemmas corollaries (they cannot supply `noWrBefore`, a fact about row positions BEFORE the
window); the caller (ApA level) discharges it from its segment-write facts (`segWr`).  Also
Lean-only: `AxSpinPO3.rowMycpuPOf` (`RowShP k row (mycSh …) → RowMycpuP k row …`),
`AxSpinPO3.rowShPNowr` (`rowShNowr` on `RowShP`: absent positions carry no write).

## Deviations from Rocq

1. O2 STAGE C / Q20' (provisional Option V; protocol "Cross-file facts" Q20', AxSpinPOr,
   AxSpinPOx (XxPin Option V), AxSpinE8 (Hval/Hret), AxSpinHd8 entries):
   * the row shape is `poTail (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)`
     (AxSpinPOr deviation 1: no fetch items); the parameters `p18 p1c pret nret` and the
     premise `nret = 2 ∨ nret = 4` are DROPPED ("Stage C: no row item pins a fetch").
   * POSITIONS (AxSpinPOr Stage C windows): the `jal` at `t` (register-only; Rocq `t`),
     mycpu at `t` (Rocq `t + 1`), its continuation at `t + 4` (Rocq `t + 19`), the `noff`
     load at `t + 4` (Rocq `t + 20`, graph value), the `addiw` at `t + 5`, the `noff` store at
     `t + 5` (Rocq `t + 23`, row data), the reloads at `t + 6 / 7 / 8` (Rocq `t + 25 / 27 /
     29`, graph values and annotations), `addi16sp` and `c.ret` at `t + 9`, the continuation
     at `t + 9` (Rocq `t + 32`).  The spills' "no write between" premises keep Rocq's form
     `nowr row kra (t + 1) …` (under Stage C position `t` is mycpu's ra spill at `Pmra`, so
     the caller's premise also covers it — callers prove it from their enclosing window).
   * the two `fpin` premises (mycpu's return `fpin T stv (ppo 0x1c) p1c`, push_off's return
     `fpin T stv ret pret`), the section context `stv` and the Sail premise `va_first_read`
     are DROPPED; NEW value pins (Q20'): `Hval1c : graphValue (gtAdGd GT) (i, t + 2) = some
     (stBytes 8 (AxSpinPO.ppo 0x1c))` (mycpu's ra reload — `AxSpinE8.wpdMycpu`'s `Hval` at
     `k = t`; its `Hret` is decided at the literal), `Hval : graphValue (gtAdGd GT) (i, t + 6)
     = some (stBytes 8 ret)` (push_off's ra reload) and `Hret : jalrTgt 0#12 ret = ret`
     (c.ret clears bit 0; as AxSpinE8 / AxSpinHd8).
   * NEW premise `t + 9 < row.length`: the boundary after the c.ret needs a next row item
     (`AxSpinE6.XxRet`'s `k < LEN`); Rocq got `t + 33 ≤ length row` from the return-fetch item
     at `t + 32`, but the Stage C window ends at the last reload (AxSpinPOr lesson: "poTail /
     ppTail end at the last reload — the c.ret's `k < LEN` must come from the caller's window
     or a length premise").
   * the leaves' fetch-item premises (`sh_fetch_ne` / `sh_fetch_nw` uses) are gone with
     AxSpinPOx deviation 1 / AxSpinE6 deviation 3.
2. KERNEL DRIFT (AxSpinPO deviation 1): `jal mycpu` at `+ 0x18` is `q18 = JAL 3366` (Rocq
   3328); `ppo 0x18 + 3366 = pcm 0` is decided.
3. TYPES / SPELLING (as AxSpinE8 deviation 3): `uint P` ↦ `paZ P`; `gpr_val` ↦ `gprVal`;
   `register_lookup PC rs` ↦ `rs .PC`; `uint r ≠ n` ↦ `r.toNat ≠ n`; `l !! k` ↦ `l[k]?`;
   `(i,k) ↦ₐ P` ↦ `AxAnnot.annotOwn (i, k) P`; `WeakAxiomatic.LStore` ↦ `Lbl.LStore`;
   `wm_class` ↦ `WmClass`; the `let`s are inlined: `spb` ↦ `gprVal rs0 AxSpinE8.r2`, `tp` ↦
   `gprVal rs0 AxSpinE8.r4`, `va_mra`/`va_ms0` ↦ `AxSpinE8.vaRa rs0`/`AxSpinE8.vaS0 rs0`
   (definitionally Rocq's `sp1_of spb + imm_ra/imm_s0`); `caddi16sp_imm` ↦ `caddi16spImm`.
4. INSTANCES / SECTION (as AxSpinE8 deviation 4): `[InvGS_gen hlc GF]` (any `hlc`); the local
   instances `pt_pol`/`pt_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`; section
   variables are explicit arguments in AxSpinE6's order (+ `Htxm Htxp`).
5. TACTICS: `pcs`/`nz` ↦ `decide`; `zsimp` ↦ the file-local macro `ax_spin_po3_zsimp`
   (= AxSpinE8's); `lia` ↦ `omega`; `nowr_tac` ↦ AxSpinPOr's `ax_spin_por_nowr`; `zq`
   subsumed.  The trailing `Print Assumptions` is not ported.

**Rocq → Lean name map.**  `addiw1` `AxSpinPO3.addiw1`, `imm24` `AxSpinPO3.imm24`, `imm16`
`AxSpinPO3.imm16`, `imm8` `AxSpinPO3.imm8`, `rsp` `AxSpinPO3.rsp` (duplicated names:
file-qualified), `i120` `i120`, `wpd_po_tail` `wpdPoTail`.  The local instances `pt_pol`,
`pt_G` are inlined (deviation 4).  Lean-only (stage 2, grepped unique): `wpdPoTailP`,
`AxSpinPO3.xxLd4C`, `AxSpinPO3.rowMycpuPOf`, `AxSpinPO3.rowShPNowr` (+ 1 local macro).

**Dropped:** nothing (Rocq 7 definitions/lemmas + 2 local instances; Lean 7).
-/
import Weak.AxSpinPOx
import Weak.AxSpinPOt2
import Weak.AxSpinPOt3
import Weak.AxSpinPOd
import Weak.AxSpinRowP
import Weak.AxSpinLd4P

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `addiw1` (duplicated name: file-qualified): `addiw a5,a5,1`'s result. -/
def AxSpinPO3.addiw1 (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (sign_extend (m := 12) (1#6))) 31 0)
/-- Rocq `imm24` (duplicated name). -/
def AxSpinPO3.imm24 : BitVec 12 := zero_extend (m := 12) (3#6 +++ 0b000#3)
/-- Rocq `imm16` (duplicated name). -/
def AxSpinPO3.imm16 : BitVec 12 := zero_extend (m := 12) (2#6 +++ 0b000#3)
/-- Rocq `imm8` (duplicated name). -/
def AxSpinPO3.imm8 : BitVec 12 := zero_extend (m := 12) (1#6 +++ 0b000#3)
/-- Rocq `rsp` (duplicated name). -/
abbrev AxSpinPO3.rsp : BitVec 5 := 2#5
/-- Rocq `i120`: the offset of `cpus[i].noff`. -/
def i120 : BitVec 12 := 120#12

/-- (Rocq `zsimp`) evaluate the closed `upd` tests. -/
local macro "ax_spin_po3_zsimp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := decide) only [AxSpinE8.updSame, AxSpinE8.updOther, AxSpinE8.updZero]
    $[$loc]?)

/-! # Stage 2 helpers (Lean-only): prefix windows and the conditional genesis leaf -/

/-- (Lean-only, stage 2) a PREFIX mycpu item window is a `RowMycpuP` window. -/
theorem AxSpinPO3.rowMycpuPOf (k : Nat) (row : List Lbl) (pra ps0 : Int) :
    RowShP k row (mycSh pra ps0) → RowMycpuP k row pra ps0 := by
  intro H j Hj Hk
  obtain ⟨it, Hit, Hm⟩ := mycItem pra ps0 j Hj
  obtain ⟨lb, Hlb, Hs⟩ := H j it Hit Hk
  exact ⟨lb, Hlb, Hm lb Hs⟩

/-- (Lean-only, stage 2) `rowShNowr` on a PREFIX window: absent positions carry no write. -/
theorem AxSpinPO3.rowShPNowr (k : Nat) (row : List Lbl) (sh : List Ritem) (jw jr : Nat)
    (pa : Int) (w : Nat) :
    RowShP k row sh → jr ≤ sh.length →
    (∀ it ∈ (sh.take jr).drop (jw + 1), itDisj pa w it) →
    nowr row (k + jw) (k + jr) pa w := by
  intro H Hle HF k' lb rl b m Hk Hlb Hid
  have Hlt : k' < row.length := (List.getElem?_eq_some_iff.1 Hlb).1
  obtain ⟨it, Hit⟩ : ∃ it, sh[k' - k]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨lb', Hlb', Hs⟩ := H (k' - k) it Hit (by omega)
  rw [show k + (k' - k) = k' by omega, Hlb] at Hlb'
  cases Hlb'
  have Hj : ((sh.take jr).drop (jw + 1))[k' - k - (jw + 1)]? = some it := by
    rw [List.getElem?_drop, List.getElem?_take]
    rw [if_pos (by omega), show jw + 1 + (k' - k - (jw + 1)) = k' - k by omega]
    exact Hit
  have Hd : itDisj pa w it := HF it (List.mem_of_getElem? Hj)
  cases it with
  | RF n => obtain ⟨aq, b', E⟩ := Hs; rw [E] at Hid; cases Hid
  | RP pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid
  | RS pb n =>
    obtain ⟨vw, cls, rfl, Hl⟩ := Hs
    simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hid
    obtain ⟨_, rfl, rfl⟩ := Hid
    rw [Hl]
    exact Hd
  | RL pb n => obtain ⟨aq, E⟩ := Hs; rw [E] at Hid; cases Hid

section ld4c
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
variable (Ψ : Athread → IProp GF)
variable (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
  ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)

include HL Hcons hmode hasid hppn Hfix HΨmid in
/-- (Lean-only, stage 2) THE CONDITIONAL GENESIS LEAF: `XxLd4`'s premises plus the four bytes'
privacy; the continuation also receives the GENESIS annotation `AxSpinLd4P.genFact4` at `(i, k)`
UNDER the row condition "no own write to the field before `k`" (`AxSpinLd4P.noWrBefore`): when
that holds the load runs `AxSpinLd4P.XxLd4G`, otherwise the plain `XxLd4` (the conditional is
then vacuous).  The caller discharges the condition where it knows the row's earlier writes. -/
theorem AxSpinPO3.xxLd4C (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (va pa : BitVec 64) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) →
    rd.toNat ≠ 0 →
    va = gprVal rs rs1 + sign_extend (m := 64) imm →
    dataAtS σi T (.Load .Data) va 4 pa → hitW rs va → ¬ L.xlText (paZ pa) →
    noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ pa) 4 →
    k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length →
    (∀ j : Nat, j < 4 → priv L (paZ pa + (j : Int)) i) →
    ⊢ (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = 4⌝ -∗
        ⌜GoodB T satp0 rs pc is_rvc none (some (rd, ldRes false 4 vs)) rs'⌝ -∗
        ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗
        (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) k (paZ pa) 4,
          AxAnnot.annotOwn (GF := GF) (i, k) iprop(⌜AxSpinLd4P.genFact4 GT i (paZ pa) k⌝)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ := by
  intro HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle Hpriv
  iintro C
  by_cases Hnone : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) k (paZ pa) 4
  · iapply (AxSpinLd4P.XxLd4G L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
      s rs k pc is_rvc imm rs1 rd va pa HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle Hpriv
      Hnone)
    iintro %vs %rs' %ib' %Hvs %HGB %Hgv Hann
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv
    iintro %_
    iexact Hann
  · iapply (XxLd4 L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
      s rs k pc is_rvc imm rs1 rd va pa HRet Hc HPC Hhit Htx Hrd Hva Hda Hhv Hnt Hnr Hle)
    iintro %vs %rs' %ib' %Hvs %HGB %Hgv
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv
    iintro %h
    exact absurd h Hnone

end ld4c

section potail
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
/-- (Lean-only, stage 2) THE P-FORM of `wpdPoTail` on a PREFIX row (`RowShP`; the value pins
guarded by position): at each row position of the tail window a `by_cases` on
`LEN ≤ position`; the row-end case is the WINDOWED hook `HΨend` over `[t, t + 9]` (mycpu's
sub-window is handed on to `wpdMycpuP`).  The noff load runs the conditional genesis leaf
`AxSpinPO3.xxLd4C` (its `genFact4` annotation is handed on); the post additionally exposes the
`sw noff` row label with its data.  The continuation is reached only when `t + 9 < LEN`. -/
theorem wpdPoTailP (t : Nat) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 Ps1 Pmra Pms0 Pn : BitVec 64) (kra ks0 ks1 : Nat)
    (vra vs0 vs1 : List (BitVec 8)) (cra cs0 cs1 : WmClass) :
    -- the row
    RowShP t (AxOpsem.grow (gtAdGd GT) i)
      (poTail (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    -- the spills (caller's row facts)
    (AxOpsem.grow (gtAdGd GT) i)[kra]? = some (.LStore false (paZ Pra) vra cra) →
    vra.length = 8 → kra < t → nowr (AxOpsem.grow (gtAdGd GT) i) kra (t + 1) (paZ Pra) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks0]? = some (.LStore false (paZ Ps0) vs0 cs0) →
    vs0.length = 8 → ks0 < t → nowr (AxOpsem.grow (gtAdGd GT) i) ks0 (t + 1) (paZ Ps0) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks1]? = some (.LStore false (paZ Ps1) vs1 cs1) →
    vs1.length = 8 → ks1 < t → nowr (AxOpsem.grow (gtAdGd GT) i) ks1 (t + 1) (paZ Ps1) 8 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinPO.ppo 0x18 → hitW rs0 (AxSpinPO.ppo 0) →
    hitW rs0 (pcm 0) →
    -- push_off's slots (reloaded here)
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm24) 8
      Pra → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm24) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm16) 8
      Ps0 → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm16) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm8) 8
      Ps1 → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm8) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    -- mycpu's slots
    dataAtS σi T (.Store .Data) (AxSpinE8.vaRa rs0) 8 Pmra →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaRa rs0) 8 Pmra → hitW rs0 (AxSpinE8.vaRa rs0) →
    dataAtS σi T (.Store .Data) (AxSpinE8.vaS0 rs0) 8 Pms0 →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaS0 rs0) 8 Pms0 → hitW rs0 (AxSpinE8.vaS0 rs0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pmra + (j : Int)) i) → ¬ L.xlText (paZ Pmra) →
    (∀ j : Nat, j < 8 → priv L (paZ Pms0 + (j : Int)) i) → ¬ L.xlText (paZ Pms0) →
    -- the noff field
    dataAtS σi T (.Store .Data)
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) 4 Pn →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) 4 Pn →
    hitW rs0 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) →
    (∀ j : Nat, j < 4 → priv L (paZ Pn + (j : Int)) i) → ¬ L.xlText (paZ Pn) →
    -- disjointness
    dj (paZ Pms0) 8 (paZ Pmra) 8 →
    dj (paZ Pmra) 8 (paZ Pra) 8 → dj (paZ Pms0) 8 (paZ Pra) 8 → dj (paZ Pn) 4 (paZ Pra) 8 →
    dj (paZ Pmra) 8 (paZ Ps0) 8 → dj (paZ Pms0) 8 (paZ Ps0) 8 → dj (paZ Pn) 4 (paZ Ps0) 8 →
    dj (paZ Pmra) 8 (paZ Ps1) 8 → dj (paZ Pms0) 8 (paZ Ps1) 8 → dj (paZ Pn) 4 (paZ Ps1) 8 →
    -- the returns (Q20': the ra reloads' graph values; deviation 1)
    (t + 2 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, t + 2) = some (stBytes 8 (AxSpinPO.ppo 0x1c))) →
    (t + 6 < (AxOpsem.grow (gtAdGd GT) i).length →
      graphValue (gtAdGd GT) (i, t + 6) = some (stBytes 8 ret)) → jalrTgt 0#12 ret = ret →
    -- the row-end hook (stage 2, design §B / Q-S2-2; windowed)
    (∀ k' : Nat, t ≤ k' → k' ≤ t + 9 → (AxOpsem.grow (gtAdGd GT) i).length ≤ k' →
      ∀ pr : Pexv6,
        ⊢ @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨pr, k'⟩ Ψ) →
    ⊢ (∀ (vn vra' vs0' vs1' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜(∃ cls, (AxOpsem.grow (gtAdGd GT) i)[t + 5]? =
            some (.LStore false (paZ Pn) (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) cls)) ∧
          ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 =
            gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) (caddi16spImm 2#6) ∧
          vn.length = 4 ∧ gprVal rs' AxSpinE8.r15 = AxSpinPO3.addiw1 (ldRes false 4 vn) ∧
          vra'.length = 8 ∧ vs0'.length = 8 ∧ vs1'.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
          gprVal rs' AxSpinPOr.r9 = ldRes false 8 vs1' ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphValue (gtAdGd GT) (i, t + 4) = some vn ∧
          graphData (gtAdGd GT) (i, t + 5) =
            some (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) ∧
          graphValue (gtAdGd GT) (i, t + 6) = some vra' ∧
          graphValue (gtAdGd GT) (i, t + 7) = some vs0' ∧
          graphValue (gtAdGd GT) (i, t + 8) = some vs1'⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 6) iprop(⌜RLfact GT i (paZ Pra) (t + 6) vra⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 7) iprop(⌜RLfact GT i (paZ Ps0) (t + 7) vs0⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 8) iprop(⌜RLfact GT i (paZ Ps1) (t + 8) vs1⌝) -∗
        (∀ _ : AxSpinLd4P.noWrBefore (AxOpsem.grow (gtAdGd GT) i) (t + 4) (paZ Pn) 4,
          AxAnnot.annotOwn (GF := GF) (i, t + 4)
            iprop(⌜AxSpinLd4P.genFact4 GT i (paZ Pn) (t + 4)⌝)) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', t + 9⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, t⟩ Ψ := by
  intro HR Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_mra Hnr_ms0 Hwle Hnrn
    Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM HdaL_ra Hh_ra HdaL_s0 Hh_s0 HdaL_s1 Hh_s1
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1
    HdaS_mra HdaL_mra Hh_mra HdaS_ms0 HdaL_ms0 Hh_ms0 Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0
    HdaS_n HdaL_n Hh_n Hpr_n Hnt_n
    Hdm _Hd1 Hd2 Hd3 _Hd4 Hd5 Hd6 _Hd7 Hd8 Hd9 Hval1c Hval Hret HΨend
  iintro C
  -- row end at t
  by_cases E0 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, T18, T1c, T1e, T20, T22, T24, T26, T28, T2a, -, -, -, -,
    -⟩ := Htxp
  have XR := XxReg L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL := XxLd L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XS4 := XxSt4 L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XL4 := AxSpinPO3.xxLd4C L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have XT := XxRet L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid
  have WM := wpdMycpuP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Ψ HΨmid
  have Hlsh : (poTail (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)).length = 9 :=
    rfl
  -- ---- + 0x18: jal ra,mycpu (row position t) ----
  have Hcj : CertC (ctrlOkSW T satp0) rs0 (AxSpinPO.ppo 0x18) false q18 (some (pcm 0))
      (some (1#5, BitVec.addInt (AxSpinPO.ppo 0x18) (incr false))) := by
    have h := certJAL (ctrlOkSW T satp0) (AxSpinE6.ctlRegimeSW T satp0) rs0 (AxSpinPO.ppo 0x18)
      false 3366#21 1#5 (by decide)
    rw [show AxSpinPO.ppo 0x18 + sign_extend (m := 64) 3366#21 = pcm 0 by decide] at h
    rw [show linkOw 1#5 (BitVec.addInt (AxSpinPO.ppo 0x18) (incr false)) =
      some (1#5, BitVec.addInt (AxSpinPO.ppo 0x18) (incr false)) by
        unfold linkOw; rw [if_neg (by decide)]] at h
    exact h
  iapply (XR _ rs0 t (AxSpinPO.ppo 0x18) false q18 (some (pcm 0))
    (some (1#5, BitVec.addInt (AxSpinPO.ppo 0x18) (incr false)))
    (retxRefl cpu rs0 t ib0) Hc0 HPC0
    (hitWSvpn rs0 (AxSpinPO.ppo 0x18) (AxSpinPO.ppo 0) (by decide) Hhit0)
    (tw4Q18 σi T satp0 _ T18) (AxSpinE8.owOkSome 1#5 _ (by decide))
    (AxSpinPOx.rfFJal 3366#21 (.Regidx 1#5)) Hcj (by omega))
  iintro %rs1 %ib1 %HG1
  have HF1 := stepRegs T satp0 _ rs0 _ _ _ _ _ rs1 (fun _ => rfl) HG1
  have HPC1 : rs1 .PC = pcm 0 := gbPc T satp0 _ _ _ _ _ _ HG1
  have Htl1 : rs1 .tlb = rs0 .tlb := gbTlb T satp0 _ _ _ _ _ _ HG1
  have Esp1 : gprVal rs1 AxSpinE8.r2 = gprVal rs0 AxSpinE8.r2 := by
    rw [HF1]; ax_spin_po3_zsimp
  have Etp1 : gprVal rs1 AxSpinE8.r4 = gprVal rs0 AxSpinE8.r4 := by
    rw [HF1]; ax_spin_po3_zsimp
  have Evra : AxSpinE8.vaRa rs1 = AxSpinE8.vaRa rs0 := by
    unfold AxSpinE8.vaRa; rw [Esp1]
  have Evs0 : AxSpinE8.vaS0 rs1 = AxSpinE8.vaS0 rs0 := by
    unfold AxSpinE8.vaS0; rw [Esp1]
  -- ---- mycpu, at t ----
  have HRm : RowMycpuP t (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) (paZ Pms0) :=
    AxSpinPO3.rowMycpuPOf t _ _ _ (rowShPAppL (s1 := mycSh (paZ Pmra) (paZ Pms0))
      (s2 := [.RL (paZ Pn) 4, .RS (paZ Pn) 4, .RL (paZ Pra) 8, .RL (paZ Ps0) 8, .RL (paZ Ps1) 8])
      HR)
  iapply (WM t rs1 ib1 (AxSpinPO.ppo 0x1c) Pmra Pms0 HRm Hw8 Hnr_mra Hnr_ms0
    (gbCtrl T satp0 _ _ _ _ _ _ HG1) HPC1 (hitWAgree rs0 rs1 _ Htl1 HhitM)
    (by rw [Evra]; exact HdaS_mra) (by rw [Evra]; exact HdaL_mra)
    (by rw [Evra]; exact hitWAgree rs0 rs1 _ Htl1 Hh_mra)
    (by rw [Evs0]; exact HdaS_ms0) (by rw [Evs0]; exact HdaL_ms0)
    (by rw [Evs0]; exact hitWAgree rs0 rs1 _ Htl1 Hh_ms0)
    Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0 (by unfold dj at Hdm; omega) Hval1c (by decide)
    (fun k' h1 h2 h3 => HΨend k' h1 (by omega) h3))
  iintro %vmra %vms0 %rs2 %ib2 %HM - -
  obtain ⟨Hc2, HPC2, Htl2', Ha02, Hsp2, -, -, -, -, Hkeep2, -, -, -, -⟩ := HM
  have Htl2 : rs2 .tlb = rs0 .tlb := Htl2'.trans Htl1
  have Ea02 : gprVal rs2 10#5 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) := by
    rw [← Etp1]; exact Ha02
  have Esp2 : gprVal rs2 2#5 = gprVal rs0 AxSpinE8.r2 := by
    rw [← Esp1]; exact Hsp2
  -- row end at t + 4
  by_cases E4 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 4
  · iclear C
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x1c: lw a5,120(a0) — noff (t+4; conditional genesis leaf) ----
  iapply (XL4 _ rs2 (t + 4) (AxSpinPO.ppo 0x1c) true i120 10#5 15#5
    (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn
    (retxRefl cpu rs2 (t + 4) ib2) Hc2 HPC2
    (hitWSvpn rs2 (AxSpinPO.ppo 0x1c) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs2 _ Htl2 Hhit0))
    (tw5d3c σi T satp0 _ T1c) (by decide) (by rw [Ea02]) HdaL_n
    (hitWAgree rs0 rs2 _ Htl2 Hh_n) Hnt_n Hnrn (by omega) Hpr_n)
  iintro %vn %rs3 %ib3 %Hlvn %HG3 %Hgv4 Hgen
  have HF3 := stepRegs T satp0 _ rs2 _ _ _ _ _ rs3 (fun _ => rfl) HG3
  have HPC3 : rs3 .PC = AxSpinPO.ppo 0x1e := by rw [gbPc T satp0 _ _ _ _ _ _ HG3]; decide
  have Htl3 : rs3 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG3).trans Htl2
  -- row end at t + 5
  by_cases E5 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 5
  · iclear C
    iclear Hgen
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x1e: addiw a5,a5,1 (t+5) ----
  have Hc4 : CertC (ctrlOkSW T satp0) rs3 (AxSpinPO.ppo 0x1e) true q1e none
      (some (15#5, AxSpinPO3.addiw1 (ldRes false 4 vn))) := by
    have h := certAddiw (ctrlOkSW T satp0) rs3 (AxSpinPO.ppo 0x1e) true 15#5 15#5
      (sign_extend (m := 12) (1#6)) (by decide)
    simp only [HF3] at h
    ax_spin_po3_zsimp at h
    exact h
  iapply (XR _ rs3 (t + 5) (AxSpinPO.ppo 0x1e) true q1e _ _
    (retxRefl cpu rs3 (t + 5) ib3) (gbCtrl T satp0 _ _ _ _ _ _ HG3) HPC3
    (hitWSvpn rs3 (AxSpinPO.ppo 0x1e) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs3 _ Htl3 Hhit0))
    (tw2785 σi T satp0 _ T1e) (AxSpinE8.owOkSome 15#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addiw _ _ _)) Hc4 (by omega))
  iintro %rs4 %ib4 %HG4
  have HF4 := stepRegs T satp0 _ rs3 _ _ _ _ _ rs4 HF3 HG4
  have HPC4 : rs4 .PC = AxSpinPO.ppo 0x20 := by rw [gbPc T satp0 _ _ _ _ _ _ HG4]; decide
  have Htl4 : rs4 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG4).trans Htl3
  -- ---- + 0x20: sw a5,120(a0) — noff (t+5) ----
  iapply (XS4 _ rs4 (t + 5) (AxSpinPO.ppo 0x20) true i120 15#5 10#5
    (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) Pn
    (retxRefl cpu rs4 (t + 5) ib4) (gbCtrl T satp0 _ _ _ _ _ _ HG4) HPC4
    (hitWSvpn rs4 (AxSpinPO.ppo 0x20) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs4 _ Htl4 Hhit0))
    (twDd3c σi T satp0 _ T20) (by rw [HF4]; ax_spin_po3_zsimp; rw [Ea02]) HdaS_n
    (hitWAgree rs0 rs4 _ Htl4 Hh_n) Hpr_n Hwle (by omega))
  iintro %rs5 %ib5 %HG5 %Hgd5
  have Hgd5' : graphData (gtAdGd GT) (i, t + 5) =
      some (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) := by
    rw [Hgd5, HF4]
    ax_spin_po3_zsimp
  obtain ⟨lbn, Hlbn, vwn, clsn, rfl, -⟩ := HR 5 (.RS (paZ Pn) 4) rfl (by omega)
  have Hvwn : vwn = stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn)) := by
    have h := Hgd5'
    unfold graphData at h
    rw [AxWp.growLookup _ _ _ _ Hlbn] at h
    simpa only [Option.bind_some, lblData, Option.some.injEq] using h
  subst Hvwn
  have HF5 := stepRegs0 T satp0 _ rs4 _ _ _ rs5 HF4 HG5
  have HPC5 : rs5 .PC = AxSpinPO.ppo 0x22 := by rw [gbPc T satp0 _ _ _ _ _ _ HG5]; decide
  have Htl5 : rs5 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG5).trans Htl4
  -- row end at t + 6
  by_cases E6 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 6
  · iclear C
    iclear Hgen
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x22: ld ra,24(sp) — reload (t+6) ----
  iapply (XL _ rs5 (t + 6) (AxSpinPO.ppo 0x22) true AxSpinPO3.imm24 2#5 1#5
    (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm24) Pra kra vra cra
    (retxRefl cpu rs5 (t + 6) ib5) (gbCtrl T satp0 _ _ _ _ _ _ HG5) HPC5
    (hitWSvpn rs5 (AxSpinPO.ppo 0x22) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs5 _ Htl5 Hhit0))
    (tw60e2 σi T satp0 _ T22) (by decide) (by rw [HF5]; ax_spin_po3_zsimp; rw [Esp2])
    HdaL_ra (hitWAgree rs0 rs5 _ Htl5 Hh_ra) Hpr_ra Hnt_ra Hnr_ra Hkra Hlra (by omega) ?_
    (by omega))
  · have Hnw := nowrJoin _ kra t (t + 6) (paZ Pra) 8 (by omega) Hbw_ra
      (AxSpinPO3.rowShPNowr t _ _ 0 6 (paZ Pra) 8 HR (by rw [Hlsh]; omega) (by ax_spin_por_nowr))
    intro k' lb' rl b m Hk Hl Hid
    have := Hnw k' lb' rl b m Hk Hl Hid
    unfold dj at this
    omega
  iintro %vra' %rs6 %ib6 %Hlvra %HG6 %Hgv6 H6
  have HF6 := stepRegs T satp0 _ rs5 _ _ _ _ _ rs6 HF5 HG6
  have HPC6 : rs6 .PC = AxSpinPO.ppo 0x24 := by rw [gbPc T satp0 _ _ _ _ _ _ HG6]; decide
  have Htl6 : rs6 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG6).trans Htl5
  -- row end at t + 7
  by_cases E7 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 7
  · iclear C
    iclear Hgen
    iclear H6
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x24: ld s0,16(sp) — reload (t+7) ----
  iapply (XL _ rs6 (t + 7) (AxSpinPO.ppo 0x24) true AxSpinPO3.imm16 2#5 8#5
    (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm16) Ps0 ks0 vs0 cs0
    (retxRefl cpu rs6 (t + 7) ib6) (gbCtrl T satp0 _ _ _ _ _ _ HG6) HPC6
    (hitWSvpn rs6 (AxSpinPO.ppo 0x24) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs6 _ Htl6 Hhit0))
    (tw6442 σi T satp0 _ T24) (by decide) (by rw [HF6]; ax_spin_po3_zsimp; rw [Esp2])
    HdaL_s0 (hitWAgree rs0 rs6 _ Htl6 Hh_s0) Hpr_s0 Hnt_s0 Hnr_s0 Hks0 Hls0 (by omega) ?_
    (by omega))
  · have Hnw := nowrJoin _ ks0 t (t + 7) (paZ Ps0) 8 (by omega) Hbw_s0
      (AxSpinPO3.rowShPNowr t _ _ 0 7 (paZ Ps0) 8 HR (by rw [Hlsh]; omega) (by ax_spin_por_nowr))
    intro k' lb' rl b m Hk Hl Hid
    have := Hnw k' lb' rl b m Hk Hl Hid
    unfold dj at this
    omega
  iintro %vs0' %rs7 %ib7 %Hlvs0 %HG7 %Hgv7 H7
  have HF7 := stepRegs T satp0 _ rs6 _ _ _ _ _ rs7 HF6 HG7
  have HPC7 : rs7 .PC = AxSpinPO.ppo 0x26 := by rw [gbPc T satp0 _ _ _ _ _ _ HG7]; decide
  have Htl7 : rs7 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG7).trans Htl6
  -- row end at t + 8
  by_cases E8 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 8
  · iclear C
    iclear Hgen
    iclear H6
    iclear H7
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x26: ld s1,8(sp) — reload (t+8) ----
  iapply (XL _ rs7 (t + 8) (AxSpinPO.ppo 0x26) true AxSpinPO3.imm8 2#5 9#5
    (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm8) Ps1 ks1 vs1 cs1
    (retxRefl cpu rs7 (t + 8) ib7) (gbCtrl T satp0 _ _ _ _ _ _ HG7) HPC7
    (hitWSvpn rs7 (AxSpinPO.ppo 0x26) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs7 _ Htl7 Hhit0))
    (tw64a2 σi T satp0 _ T26) (by decide) (by rw [HF7]; ax_spin_po3_zsimp; rw [Esp2])
    HdaL_s1 (hitWAgree rs0 rs7 _ Htl7 Hh_s1) Hpr_s1 Hnt_s1 Hnr_s1 Hks1 Hls1 (by omega) ?_
    (by omega))
  · have Hnw := nowrJoin _ ks1 t (t + 8) (paZ Ps1) 8 (by omega) Hbw_s1
      (AxSpinPO3.rowShPNowr t _ _ 0 8 (paZ Ps1) 8 HR (by rw [Hlsh]; omega) (by ax_spin_por_nowr))
    intro k' lb' rl b m Hk Hl Hid
    have := Hnw k' lb' rl b m Hk Hl Hid
    unfold dj at this
    omega
  iintro %vs1' %rs8 %ib8 %Hlvs1 %HG8 %Hgv8 H8
  have HF8 := stepRegs T satp0 _ rs7 _ _ _ _ _ rs8 HF7 HG8
  have HPC8 : rs8 .PC = AxSpinPO.ppo 0x28 := by rw [gbPc T satp0 _ _ _ _ _ _ HG8]; decide
  have Htl8 : rs8 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG8).trans Htl7
  -- row end at t + 9
  by_cases E9 : (AxOpsem.grow (gtAdGd GT) i).length ≤ t + 9
  · iclear C
    iclear Hgen
    iclear H6
    iclear H7
    iclear H8
    iapply (HΨend _ (by omega) (by omega) (by omega) _)
  -- ---- + 0x28: c.addi16sp sp,32 (t+9) ----
  have Hc9 := certAddi (ctrlOkSW T satp0) rs8 (AxSpinPO.ppo 0x28) true 2#5 2#5
    (caddi16spImm 2#6) (by decide)
  simp only [HF8] at Hc9
  ax_spin_po3_zsimp at Hc9
  iapply (XR _ rs8 (t + 9) (AxSpinPO.ppo 0x28) true q28 _ _
    (retxRefl cpu rs8 (t + 9) ib8) (gbCtrl T satp0 _ _ _ _ _ _ HG8) HPC8
    (hitWSvpn rs8 (AxSpinPO.ppo 0x28) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs8 _ Htl8 Hhit0))
    (tw6105 σi T satp0 _ T28) (AxSpinE8.owOkSome 2#5 _ (by decide))
    (rfFOfRf0 _ (rf0Addi _ _ _)) Hc9 (by omega))
  iintro %rs9 %ib9 %HG9
  have HF9 := stepRegs T satp0 _ rs8 _ _ _ _ _ rs9 HF8 HG9
  have HPC9 : rs9 .PC = AxSpinPO.ppo 0x2a := by rw [gbPc T satp0 _ _ _ _ _ _ HG9]; decide
  have Htl9 : rs9 .tlb = rs0 .tlb := (gbTlb T satp0 _ _ _ _ _ _ HG9).trans Htl8
  -- ---- + 0x2a: c.ret (t+9; Q20': no stuck branch, the target is the reloaded ra) ----
  iapply (XT _ rs9 (t + 9) (AxSpinPO.ppo 0x2a)
    (retxRefl cpu rs9 (t + 9) ib9) (gbCtrl T satp0 _ _ _ _ _ _ HG9) HPC9
    (hitWSvpn rs9 (AxSpinPO.ppo 0x2a) (AxSpinPO.ppo 0) (by decide)
      (hitWAgree rs0 rs9 _ Htl9 Hhit0))
    (tw8082 σi T satp0 _ T2a) rfFIns1e (by omega))
  iintro %rs' %ib' %HGr
  have HFr := stepRegs0 T satp0 _ rs9 _ _ _ rs' HF9 HGr
  have Hvra : vra' = stBytes 8 ret := Option.some.inj (Hgv6.symm.trans (Hval (by omega)))
  have Hgpr1 : gprVal rs9 1#5 = ldRes false 8 vra' := by
    rw [HF9]
    ax_spin_po3_zsimp
  iapply C $$ %vn %vra' %vs0' %vs1' %rs' %ib' [] H6 H7 H8 Hgen
  ipureintro
  refine ⟨⟨clsn, Hlbn⟩, gbCtrl T satp0 _ _ _ _ _ _ HGr, ?_, (gbTlb T satp0 _ _ _ _ _ _ HGr).trans Htl9, ?_,
    ?_, Hlvn, ?_, Hlvra, Hlvs0, Hlvs1, ?_, ?_, ?_, ?_, Hgv4, Hgd5', Hgv6, Hgv7, Hgv8⟩
  · -- PC = ret: the c.ret target is the reloaded ra, pinned by `Hval`
    rw [gbPc T satp0 _ _ _ _ _ _ HGr]
    show jalrTgt 0#12 (gprVal rs9 1#5) = ret
    rw [Hgpr1, Hvra, AxSpinE8.ldResStBytes8, Hret]
  · -- a0 = mycpuRet tp
    rw [HFr]
    ax_spin_po3_zsimp
    exact Ea02
  · -- sp restored
    rw [HFr]
    ax_spin_po3_zsimp
    rw [Esp2]
  · -- a5 = addiw1 (noff)
    rw [HFr]
    ax_spin_po3_zsimp
  · rw [HFr]
    ax_spin_po3_zsimp
  · rw [HFr]
    ax_spin_po3_zsimp
  · rw [HFr]
    ax_spin_po3_zsimp
  · -- every other GPR kept
    intro r Hr1 Hr2 Hr8 Hr9 Hr10 Hr15
    rw [HFr]
    by_cases E0 : r.toNat = 0
    · rw [AxSpinE8.updZero _ _ _ _ E0, AxSpinE8.gprValZero rs0 r E0]
    · have n1 : r ≠ 1#5 := fun h => Hr1 (by rw [h]; rfl)
      have n2 : r ≠ 2#5 := fun h => Hr2 (by rw [h]; rfl)
      have n8 : r ≠ 8#5 := fun h => Hr8 (by rw [h]; rfl)
      have n9 : r ≠ 9#5 := fun h => Hr9 (by rw [h]; rfl)
      have n15 : r ≠ 15#5 := fun h => Hr15 (by rw [h]; rfl)
      simp (disch := assumption) only [AxSpinE8.updOther]
      rw [Hkeep2 r Hr1 Hr2 Hr8 Hr10 Hr15, HF1]
      simp (disch := assumption) only [AxSpinE8.updOther]


set_option maxHeartbeats 1600000 in
include HL Hcons hmode hasid hppn Hfix Htxm Htxp HΨmid in
/-- Rocq `wpd_po_tail` (deviation 1: Stage C positions; value pins `Hval1c`/`Hval`/`Hret`
replace the `fpin` premises; new length premise `t + 9 < row.length`).  Stage 2: the full-row
corollary of `wpdPoTailP` (hook vacuous under `t + 9 < LEN`; pins unguarded; the extra label
conjunct and the genesis annotation are dropped). -/
theorem wpdPoTail (t : Nat) (rs0 : RegFile) (ib0 : Ibch) (ret : BitVec 64)
    (Pra Ps0 Ps1 Pmra Pms0 Pn : BitVec 64) (kra ks0 ks1 : Nat)
    (vra vs0 vs1 : List (BitVec 8)) (cra cs0 cs1 : WmClass) :
    -- the row
    RowSh t (AxOpsem.grow (gtAdGd GT) i)
      (poTail (paZ Pra) (paZ Ps0) (paZ Ps1) (paZ Pmra) (paZ Pms0) (paZ Pn)) →
    t + 9 < (AxOpsem.grow (gtAdGd GT) i).length →
    rowW8 (AxOpsem.grow (gtAdGd GT) i) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pra) → noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps0) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Ps1) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pmra) →
    noRmw8 (AxOpsem.grow (gtAdGd GT) i) (paZ Pms0) →
    rowWle (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 → noRmwn (AxOpsem.grow (gtAdGd GT) i) (paZ Pn) 4 →
    -- the spills (caller's row facts)
    (AxOpsem.grow (gtAdGd GT) i)[kra]? = some (.LStore false (paZ Pra) vra cra) →
    vra.length = 8 → kra < t → nowr (AxOpsem.grow (gtAdGd GT) i) kra (t + 1) (paZ Pra) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks0]? = some (.LStore false (paZ Ps0) vs0 cs0) →
    vs0.length = 8 → ks0 < t → nowr (AxOpsem.grow (gtAdGd GT) i) ks0 (t + 1) (paZ Ps0) 8 →
    (AxOpsem.grow (gtAdGd GT) i)[ks1]? = some (.LStore false (paZ Ps1) vs1 cs1) →
    vs1.length = 8 → ks1 < t → nowr (AxOpsem.grow (gtAdGd GT) i) ks1 (t + 1) (paZ Ps1) 8 →
    -- the entry state
    ctrlOkSW T satp0 rs0 → rs0 .PC = AxSpinPO.ppo 0x18 → hitW rs0 (AxSpinPO.ppo 0) →
    hitW rs0 (pcm 0) →
    -- push_off's slots (reloaded here)
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm24) 8
      Pra → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm24) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm16) 8
      Ps0 → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm16) →
    dataAtS σi T (.Load .Data) (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm8) 8
      Ps1 → hitW rs0 (gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) AxSpinPO3.imm8) →
    (∀ j : Nat, j < 8 → priv L (paZ Pra + (j : Int)) i) → ¬ L.xlText (paZ Pra) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps0 + (j : Int)) i) → ¬ L.xlText (paZ Ps0) →
    (∀ j : Nat, j < 8 → priv L (paZ Ps1 + (j : Int)) i) → ¬ L.xlText (paZ Ps1) →
    -- mycpu's slots
    dataAtS σi T (.Store .Data) (AxSpinE8.vaRa rs0) 8 Pmra →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaRa rs0) 8 Pmra → hitW rs0 (AxSpinE8.vaRa rs0) →
    dataAtS σi T (.Store .Data) (AxSpinE8.vaS0 rs0) 8 Pms0 →
    dataAtS σi T (.Load .Data) (AxSpinE8.vaS0 rs0) 8 Pms0 → hitW rs0 (AxSpinE8.vaS0 rs0) →
    (∀ j : Nat, j < 8 → priv L (paZ Pmra + (j : Int)) i) → ¬ L.xlText (paZ Pmra) →
    (∀ j : Nat, j < 8 → priv L (paZ Pms0 + (j : Int)) i) → ¬ L.xlText (paZ Pms0) →
    -- the noff field
    dataAtS σi T (.Store .Data)
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) 4 Pn →
    dataAtS σi T (.Load .Data)
      (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) 4 Pn →
    hitW rs0 (AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) + sign_extend (m := 64) i120) →
    (∀ j : Nat, j < 4 → priv L (paZ Pn + (j : Int)) i) → ¬ L.xlText (paZ Pn) →
    -- disjointness
    dj (paZ Pms0) 8 (paZ Pmra) 8 →
    dj (paZ Pmra) 8 (paZ Pra) 8 → dj (paZ Pms0) 8 (paZ Pra) 8 → dj (paZ Pn) 4 (paZ Pra) 8 →
    dj (paZ Pmra) 8 (paZ Ps0) 8 → dj (paZ Pms0) 8 (paZ Ps0) 8 → dj (paZ Pn) 4 (paZ Ps0) 8 →
    dj (paZ Pmra) 8 (paZ Ps1) 8 → dj (paZ Pms0) 8 (paZ Ps1) 8 → dj (paZ Pn) 4 (paZ Ps1) 8 →
    -- the returns (Q20': the ra reloads' graph values; deviation 1)
    graphValue (gtAdGd GT) (i, t + 2) = some (stBytes 8 (AxSpinPO.ppo 0x1c)) →
    graphValue (gtAdGd GT) (i, t + 6) = some (stBytes 8 ret) → jalrTgt 0#12 ret = ret →
    ⊢ (∀ (vn vra' vs0' vs1' : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch),
        ⌜ctrlOkSW T satp0 rs' ∧ rs' .PC = ret ∧ rs' .tlb = rs0 .tlb ∧
          gprVal rs' AxSpinE8.r10 = AxSpinE8.mycpuRet (gprVal rs0 AxSpinE8.r4) ∧
          gprVal rs' AxSpinE8.r2 =
            gprVal rs0 AxSpinE8.r2 + sign_extend (m := 64) (caddi16spImm 2#6) ∧
          vn.length = 4 ∧ gprVal rs' AxSpinE8.r15 = AxSpinPO3.addiw1 (ldRes false 4 vn) ∧
          vra'.length = 8 ∧ vs0'.length = 8 ∧ vs1'.length = 8 ∧
          gprVal rs' AxSpinE8.r1 = ldRes false 8 vra' ∧ gprVal rs' AxSpinE8.r8 = ldRes false 8 vs0' ∧
          gprVal rs' AxSpinPOr.r9 = ldRes false 8 vs1' ∧
          (∀ r : BitVec 5, r.toNat ≠ 1 → r.toNat ≠ 2 → r.toNat ≠ 8 → r.toNat ≠ 9 →
            r.toNat ≠ 10 → r.toNat ≠ 15 → gprVal rs' r = gprVal rs0 r) ∧
          graphValue (gtAdGd GT) (i, t + 4) = some vn ∧
          graphData (gtAdGd GT) (i, t + 5) =
            some (stBytes 4 (AxSpinPO3.addiw1 (ldRes false 4 vn))) ∧
          graphValue (gtAdGd GT) (i, t + 6) = some vra' ∧
          graphValue (gtAdGd GT) (i, t + 7) = some vs0' ∧
          graphValue (gtAdGd GT) (i, t + 8) = some vs1'⌝ -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 6) iprop(⌜RLfact GT i (paZ Pra) (t + 6) vra⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 7) iprop(⌜RLfact GT i (paZ Ps0) (t + 7) vs0⌝) -∗
        AxAnnot.annotOwn (GF := GF) (i, t + 8) iprop(⌜RLfact GT i (paZ Ps1) (t + 8) vs1⌝) -∗
        @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
          ⟨.PHart cpu (.pure ()) rs' none ib', t + 9⟩ Ψ) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs0 none ib0, t⟩ Ψ := by
  intro HR Hlen Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_mra Hnr_ms0 Hwle Hnrn
    Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM HdaL_ra Hh_ra HdaL_s0 Hh_s0 HdaL_s1 Hh_s1
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1
    HdaS_mra HdaL_mra Hh_mra HdaS_ms0 HdaL_ms0 Hh_ms0 Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0
    HdaS_n HdaL_n Hh_n Hpr_n Hnt_n
    Hdm Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hval1c Hval Hret
  iintro C
  iapply (wpdPoTailP L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Htxm Htxp Ψ HΨmid
    t rs0 ib0 ret Pra Ps0 Ps1 Pmra Pms0 Pn kra ks0 ks1 vra vs0 vs1 cra cs0 cs1
    (rowShPOfSh HR) Hw8 Hnr_ra Hnr_s0 Hnr_s1 Hnr_mra Hnr_ms0 Hwle Hnrn
    Hkra Hlra Hlt_ra Hbw_ra Hks0 Hls0 Hlt_s0 Hbw_s0 Hks1 Hls1 Hlt_s1 Hbw_s1
    Hc0 HPC0 Hhit0 HhitM HdaL_ra Hh_ra HdaL_s0 Hh_s0 HdaL_s1 Hh_s1
    Hpr_ra Hnt_ra Hpr_s0 Hnt_s0 Hpr_s1 Hnt_s1
    HdaS_mra HdaL_mra Hh_mra HdaS_ms0 HdaL_ms0 Hh_ms0 Hpr_mra Hnt_mra Hpr_ms0 Hnt_ms0
    HdaS_n HdaL_n Hh_n Hpr_n Hnt_n
    Hdm Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 (fun _ => Hval1c) (fun _ => Hval) Hret
    (fun _ _ h2 h3 => absurd h3 (by omega)))
  iintro %vn %vra' %vs0' %vs1' %rs' %ib' %Hf H6 H7 H8 -
  iapply C $$ %vn %vra' %vs0' %vs1' %rs' %ib' %Hf.2 H6 H7 H8

end potail

end Weak
