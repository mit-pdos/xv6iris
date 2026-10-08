/-
Weak: **SURFACE v3** — the conditional register surface (`AxSymMem3`'s `curC` shape) with an
AFFINE condition, the release-pending flag threaded across instructions as a per-hart ghost,
and the S-mode store / `fence rw,w` / `amoswap.w` WPd leaves over it (AxSL tier).

Rocq: `iris/AxCondM3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Surface v2 (Rocq `AxLeafS4`) with
(1) an AFFINE condition: no `Cond_pers`; the gate law RETURNS the condition (`CondGate3`) —
    what an annotation-backed `Cond` can satisfy (AxCondM §2); `AxCondM.condP` satisfies it
    outright (`AxCondM.condPGate3`);
(2) the RELEASE-PENDING FLAG as a per-hart ghost: the PC ghost carries `(pc, r)`, `r` = the
    release flag the NEXT instruction's certificate starts from.  Every leaf starts its
    certificate at the ghost's `r` and leaves the ghost at the certificate's EXIT flag
    (`XFenceSW`: armed; `XStoreS` / `XAmoswapSP`: cleared — as `AxClsStep.relpUpd`).
    `pcIs3 pc` exposes it only through `Armed`: at an armed pc the flag IS set.  `instr3` adds
    the text facts that keep `Armed` honest for sequential leaves: the word before an armed pc
    is `fence rw,w`, a `sw zero` is only at an armed pc, a store's base is not `tp`.  Its
    compressed arm is satisfiable (a 2-byte text word, successor never armed).  At a store leaf
    at an armed pc the certificate's class is `wcls akPlain true = WCrel` (`wclsArmed`),
    handed to the protocol rule;
(3) the AMO's read value EXACT: `wpAmoswapC3` uses the pinned bridge (`XAmoswapSP` +
    `amoOutPin`); the protocol's AMO rule gives a write-flow output indexed by the event's own
    read value (`OutOfV`).
LEAVES: `wpStoreC3` (sd / sw, any width the X leaf takes), `wpFenceC3`, `wpAmoswapC3`.
PREMISES (section): the bridge instance premises, the data-region facts, `CondGate3`,
`Hagree` (graph agreement; `AxCondM.hagreeGa2`).

## Deviations from Rocq

1. Q7 (as AxLeafS2 deviation 2): `XStoreS` / `XFenceSW` / `XAmoswapSP` take
   `sfAnnB 32 w = false` for the instruction word, so `insAt3 pc ins` carries it:
   `∃ w32, textAt4S σi T pc w32 ∧ sfAnnB 32 w32 = false ∧ decodes3 w32 ins` (Rocq: no sfence
   conjunct).  Every instance is a concrete non-sfence word (decided).
2. TYPES / SPELLING as AxSymMem3 deviation 2 and AxLeafS2 deviation 3: `regfile` ↦ `RegMap`,
   `rget m r` ↦ `rget cid m r` (explicit SC hart `cid`, Rocq's `CpuId`; Rocq's `GenId` is not
   needed), `<[Regidx rd := regval_into_reg v]> m` ↦ `m.set rd v`, `Rtp` ↦ `4#5`, `csp_rs1` ↦
   `2#5`, `register_lookup PC rs` ↦ `rs .PC`, `add_vec_int pc 4` ↦ `pc + 4#64`, `uint pa` ↦
   `paZ pa`, `Z.to_nat wd` ↦ `wd : Nat` (`(1 ≤ wd ≤ 8)%Z` ↦ `1 ≤ wd ∧ wd ≤ 8`), `zero_reg` ↦
   `0#64`, `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`, `mstate`'s `sregs` ↦
   `ExecSt.regs`, `ghost_var γ (1/2)` ↦ `ghost_var γ (.own (1 : Qp).half)`, `WPd s @
   MaybeStuck; i {{ Φ0 }}` ↦ `wpd .MaybeStuck i s Φ0`; `invGS_gen HasNoLc` ↦ any `hlc`.
   The leaf statements' `let pa := …` are inlined.  Section variables are explicit arguments
   of each declaration that uses them; the iProp-valued Rocq premises (`Cond_gate3`,
   `amo_rule3`, the store rule `Hrule`) are `⊢` entailments; `Hagree` is
   `⊢ gconstInterp GD -∗ gconstInterp GD' -∗ ⌜GD = GD'⌝` (AxCondM2 deviation 3).
3. WpAmo's `amoswap_stored` / `amoswap_loaded` (WpAmo is an SC file with no Lean port; the
   Lean SC tree spells them inline) are defined here, file-qualified:
   `AxCondM3.amoswapStored v := amoStv 4 v`, `AxCondM3.amoswapLoaded w := sign_extend w`.
4. `wp_next` ↦ `wpNext` with the continuation indexed by the resuming hart (AxSymMem3
   deviation 2); inside it `goal3` is at the ambient SC hart `cid` (as in Rocq, where the
   section's `CpuId` is fixed inside the section).

**Rocq → Lean name map.**  `fence_rw_w_ins` `fenceRwWIns`, `is_swz` `isSwz`, `cur3` `cur3`,
`Goal3` `goal3`, `sie_cap3` `sieCap3`, `pc_is3` `pcIs3`, `decodes3` `decodes3`, `ins_at3`
`insAt3`, `base_ok3` `baseOk3`, `instr3` `instr3`, `instr3_nrvc` `instr3Nrvc`, `is_dmem3`
`isDmem3`, `gate_at3` `gateAt3`, `dk3` `dk3`, `dk3_nosplit` `dk3Nosplit`, `Hmid3` `Hmid3`,
`Hb3` `Hb3`, `good_retx3` `goodRetx3`, `gpr_val_rel3` `gprValRel3`, `cur3_keep` `cur3Keep`,
`cur3_upd` `cur3Upd`, `gate_of3` `gateOf3`, `wp_store_c3` `wpStoreC3`, `wp_fence_c3`
`wpFenceC3`, `amo_ldv_loaded` `amoLdvLoaded`, `wp_amoswap_c3` `wpAmoswapC3`,
`fence_then_armed` `fenceThenArmed`.  Section parameters: `Cond_gate3` `CondGate3`,
`HnoSplit_reg` `HnoSplitReg`, `amo_res` `amoRes`, `amo_rule3` `amoRule3`, others unchanged.
None is in the duplicated-name table.  Lean-only (file-qualified): `AxCondM3.amoswapStored`,
`AxCondM3.amoswapLoaded` (deviation 3).

**Dropped:** nothing (Rocq 27 definitions/lemmas; Lean 27 + 2).  **Not ported:** the Ltac
`open_goal3` (inlined), the section notations `img` / `CK` (written out) and the
`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCondM2
import Weak.AxSymMem3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `fence_rw_w_ins`. -/
def fenceRwWIns : instruction :=
  .FENCE (0#4, 3#4, 1#4, regidx.Regidx 0#5, regidx.Regidx 0#5)

/-- Rocq `is_swz`: a `sw zero, imm(rs1)`. -/
def isSwz (ins : instruction) : Prop :=
  ∃ (imm : BitVec 12) (rs1 : BitVec 5), ins = .STORE (imm, .Regidx 0#5, .Regidx rs1, 4)

/-- (Lean-only; WpAmo's `amoswap_stored`) the word an `amoswap.w` stores. -/
def AxCondM3.amoswapStored (v : BitVec 64) : BitVec 32 := amoStv 4 v

/-- (Lean-only; WpAmo's `amoswap_loaded`) the value an `amoswap.w` writes to `rd`. -/
def AxCondM3.amoswapLoaded (w : BitVec 32) : BitVec 64 := sign_extend (m := 64) w

section surf3
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat]
variable (i : Agent) (cid cpu : CPU) (γm γp γn : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)

/- the pcs at which the release flag is set (e.g. release's `sw`) -/
variable (Armed : BitVec 64 → Prop)

/-! ## The surface -/

def cur3 (m : RegMap) (pc : BitVec 64) (s : Athread) (C : Prop) : Prop :=
  ∃ rs k, RetX cpu rs k s ∧ ctrlOkSW T satp0 rs ∧ rs .PC = pc ∧
    phys5 rs 4#5 = rget cid m 4#5 ∧ phys5 rs 2#5 = rget cid m 2#5 ∧
    (C → gprRel cid m rs)

variable (Cond : Prop → IProp GF)

def goal3 : IProp GF :=
  iprop(∀ (s : Athread) (m : RegMap) (n : Nat) (pc : BitVec 64) (r : Bool) (C : Prop),
    ⌜cur3 cid cpu T satp0 m pc s C⌝ -∗
    ghost_var γm (.own (1 : Qp).half) m -∗ ghost_var γn (.own (1 : Qp).half) n -∗
    ghost_var γp (.own (1 : Qp).half) (pc, r) -∗ Cond C -∗
    wpd .MaybeStuck i s (Φ0 (GF := GF)))

def sieCap3 (_cid0 : CPU) (m : RegMap) (n : Nat) (b : Bool) (_p : BitVec 64) : IProp GF :=
  iprop(⌜b = false⌝ ∗ ghost_var γm (.own (1 : Qp).half) m ∗ ghost_var γn (.own (1 : Qp).half) n)

def pcIs3 (pc : BitVec 64) : IProp GF :=
  iprop(∃ r : Bool, ghost_var γp (.own (1 : Qp).half) (pc, r) ∗ ⌜Armed pc → r = true⌝)

def decodes3 (w32 : BitVec 32) (ins : instruction) : Prop :=
  ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w32) t

def insAt3 (pc : BitVec 64) (ins : instruction) : Prop :=
  ∃ w32, textAt4S σi T pc w32 ∧ sfAnnB 32 w32 = false ∧ decodes3 σi T satp0 w32 ins

def baseOk3 (ins : instruction) : Prop :=
  ∀ (imm : BitVec 12) (rs2 rs1 : BitVec 5) (wd : Nat),
    ins = .STORE (imm, .Regidx rs2, .Regidx rs1, wd) → regidx.Regidx rs1 ≠ regidx.Regidx 4#5

/-- The instruction fact: a 4-byte word decoding to `ins` (whose successor is armed only if
`ins` is the fence), or — for a COMPRESSED instruction — a 2-byte text word whose successor is
never armed; plus "`sw zero` only at an armed pc" and "a store's base is not tp". -/
def instr3 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(⌜((is_rvc = false ∧ insAt3 σi T satp0 pc ins ∧ (Armed (pc + 4#64) → ins = fenceRwWIns)) ∨
      (is_rvc = true ∧ (∃ w16, textAtS σi T pc w16) ∧ ¬ Armed (pc + 2#64))) ∧
     (isSwz ins → Armed pc) ∧ baseOk3 ins⌝)

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
theorem instr3Nrvc (pc : BitVec 64) (ins : instruction) :
    instr3 (GF := GF) σi T satp0 Armed pc false ins ⊢
      ⌜insAt3 σi T satp0 pc ins ∧ (Armed (pc + 4#64) → ins = fenceRwWIns) ∧
        (isSwz ins → Armed pc) ∧ baseOk3 ins⌝ := by
  unfold instr3
  refine pure_mono ?_
  rintro ⟨H | ⟨h, _⟩, h3, h4⟩
  · exact ⟨H.2.1, H.2.2, h3, h4⟩
  · exact nomatch h

def isDmem3 (ins : instruction) : Prop :=
  match ins with
  | .LOAD _ | .STORE _ | .AMO _ => True
  | _ => False

def gateAt3 (s : Athread) : Prop :=
  ∃ rs k ins, RetX cpu rs k s ∧ insAt3 σi T satp0 (rs .PC) ins ∧ isDmem3 ins

/- THE GATE LAW, affine form (premise; `AxCondM.condPGate3` at `condP`) -/
variable (CondGate3 : ∀ s C, gateAt3 cpu σi T satp0 s →
  ⊢ Cond C -∗ (⌜C⌝ -∗ Cond C -∗ wpd .MaybeStuck i s (Φ0 (GF := GF))) -∗
    wpd .MaybeStuck i s (Φ0 (GF := GF)))

/- bridge instance premises -/
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hagree : ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)

/- data regions -/
variable (dreg damo : Int → Nat → Prop)
variable (Hdmap : ∀ (acc : MemoryAccessType mem_payload) (va : BitVec 64) (w : Nat),
  dreg (paZ va) w ∨ damo (paZ va) w → dataAtS σi T acc va w va)
variable (HnoSplitReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ damo base n⌝)

def dk3 (a : Int) (n : Nat) : Int → Nat → Prop := fun a' n' => a' = a ∧ n' = n

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
include HnoSplitReg in
theorem dk3Nosplit (a : Int) (n : Nat) : damo a n → ∀ GD, rvwmoCatConsistent GD →
    AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n' : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n' →
        ¬ dk3 a n base n'⌝ := by
  intro Hd GD Hc
  refine (HnoSplitReg GD Hc).trans (pure_mono ?_)
  intro Hns k lb aq base n' Hlb Hid ⟨e1, e2⟩
  subst e1 e2
  exact Hns k lb aq _ _ Hlb Hid Hd

/-! ## Common steps -/

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
theorem Hmid3 : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
    ⊢ postLifting (Φ0 (GF := GF)) i s :=
  fun _ s _ _ _ => postLiftingΦ0 i s

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
theorem Hb3 (rs : RegFile) (k : Nat) : ∀ GD s1, G GD → RetX cpu rs k s1 →
    s1.atK = (AxOpsem.grow GD i).length → ⊢ postLifting (Φ0 (GF := GF)) i s1 :=
  fun _ s1 _ _ _ => postLiftingΦ0 i s1

theorem goodRetx3 (rs' : RegFile) (t' : ExecSt) (ib' : Ibch) (k' : Nat) :
    regsAgree AxRunClose.pinReg rs' t'.regs →
    RetX cpu t'.regs k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
  fun Hag => ⟨ib', rfl, rfl, rfl, rfl, rfl, Hag⟩

theorem gprValRel3 (m : RegMap) (rs : RegFile) (r : BitVec 5) :
    gprRel cid m rs → gprVal rs r = rget cid m r := fun Hr => Hr r

theorem cur3Keep (m : RegMap) (pc : BitVec 64) (rs : RegFile) (t' : ExecSt) (rs' : RegFile)
    (ib' : Ibch) (k' : Nat) (C : Prop) :
    ctrlOkSW T satp0 t'.regs → t'.regs .PC = pc + 4#64 →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget t'.regs r = uxaXget rs r) →
    regsAgree AxRunClose.pinReg rs' t'.regs →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 → (C → gprRel cid m rs) →
    cur3 cid cpu T satp0 m (pc + 4#64) ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ C := by
  intro Hc HPC Hg Hag Htp Hsp Hrel
  have Hsame : ∀ r, phys5 t'.regs r = phys5 rs r := by
    intro r
    show uxaXget t'.regs r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hg r h0
  refine ⟨t'.regs, k', goodRetx3 cpu rs' t' ib' k' Hag, Hc, HPC, by rw [Hsame]; exact Htp,
    by rw [Hsame]; exact Hsp, ?_⟩
  intro HCC r
  exact (Hsame r).trans (Hrel HCC r)

theorem cur3Upd (m : RegMap) (pc : BitVec 64) (rs : RegFile) (t' : ExecSt) (rs' : RegFile)
    (ib' : Ibch) (k' : Nat) (rd : BitVec 5) (val v : BitVec 64) (C C' : Prop) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ctrlOkSW T satp0 t'.regs → t'.regs .PC = pc + 4#64 →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget t'.regs r = gprPost (some (rd, val)) rs r) →
    regsAgree AxRunClose.pinReg rs' t'.regs →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 → (C → gprRel cid m rs) →
    (C' → C ∧ val = v) →
    cur3 cid cpu T satp0 (m.set rd v) (pc + 4#64) ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ C' := by
  intro Hrd Hrdok Hc HPC Hg Hag Htp Hsp Hrel HC'
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget t'.regs r = if r = rd then val else uxaXget rs r := fun r Hr => Hg r Hr
  have Hne_tp : (4#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.2 (uint5Inj _ _ E).symm
  have Hne_sp : (2#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.1 (uint5Inj _ _ E).symm
  refine ⟨t'.regs, k', goodRetx3 cpu rs' t' ib' k' Hag, Hc, HPC, ?_, ?_, ?_⟩
  · rw [phys5UpdNe rs t'.regs rd 4#5 _ Hg' Hne_tp, Htp, rget_tp, rget_tp]
  · rw [phys5UpdNe rs t'.regs rd 2#5 _ Hg' Hne_sp, Hsp,
      rget_ne cid _ 2#5 (by decide) (by decide), rget_ne cid _ 2#5 (by decide) (by decide),
      RegMap.set_other _ _ _ _ (fun e => Hrdok.2.1 e.symm)]
  · intro HCC'
    obtain ⟨HCC, rfl⟩ := HC' HCC'
    exact gprRelUpd cid m rs t'.regs rd val (Hrel HCC) Hrd Hrdok.2.2 Hg'

theorem gateOf3 (m : RegMap) (pc : BitVec 64) (s : Athread) (C : Prop) (ins : instruction) :
    cur3 cid cpu T satp0 m pc s C → insAt3 σi T satp0 pc ins → isDmem3 ins →
    gateAt3 cpu σi T satp0 s := by
  rintro ⟨rs, k, HRet, _, HPC, _⟩ Hins Hd
  exact ⟨rs, k, ins, HRet, by rw [HPC]; exact Hins, Hd⟩

/-! ## The leaves -/

include hmode hasid hppn CondGate3 Htext Hflow Hloc HG Hdmap in
/-- Rocq `wp_store_c3`: a STORE; the protocol rule is handed the certificate's store CLASS
(`wcls akPlain r`, `r` = the ghost flag) and, at an armed pc, that it is `WCrel`. -/
theorem wpStoreC3 (pc : BitVec 64) (rs2 rs1 : BitVec 5) (imm : BitVec 12) (wd : Nat)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) (Pre Post : IProp GF) :
    vmemWidth wd → 1 ≤ wd ∧ wd ≤ 8 →
    (∀ c : WmClass, ⊢ ⌜Armed pc → c = .WCrel⌝ -∗ Pre -∗
      ⌜dreg (paZ (rget cid m rs1 + sign_extend (m := 64) imm)) wd⌝ ∗
      FstM rvwmoCatConsistent (dk3 (paZ (rget cid m rs1 + sign_extend (m := 64) imm)) wd) i
        (fun _ data => iprop(⌜data = stBytes wd (rget cid m rs2) ∧
          (rs2.toNat = 0 → data = stBytes wd 0#64)⌝ -∗ Post))) →
    ⊢ sieCap3 (GF := GF) γm γn cid m n b p -∗ pcIs3 (GF := GF) γp Armed pc -∗
      instr3 (GF := GF) σi T satp0 Armed pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, wd)) -∗
      Pre -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCap3 γm γn cpu' m n b p -∗ pcIs3 γp Armed (pc + 4#64) -∗ Post -∗
        goal3 i cid cpu γm γp γn T satp0 Cond)) -∗
      goal3 i cid cpu γm γp γn T satp0 Cond := by
  intro Hvw Hw Hrule
  generalize Hpa0 : rget cid m rs1 + sign_extend (m := 64) imm = pa at Hrule
  unfold sieCap3 pcIs3
  iintro ⟨%Hb, Hm, Hn⟩ ⟨%r0, Hp, %Har⟩ Hi Hpre Hcont
  subst Hb
  ihave %Hi := instr3Nrvc σi T satp0 Armed pc _ $$ Hi
  obtain ⟨Hins, Hnf, _, _⟩ := Hi
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal3
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  iapply (CondGate3 s C (gateOf3 cid cpu σi T satp0 m pc s C _ Hcur Hins trivial)) $$ HC
  iintro %HCC HC
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  have Hr := Hrel HCC
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hpr := Hrule (wcls AxDataX.akPlain r0) $$
    %(fun Ha => by rw [Har Ha]; exact wclsArmed _ rfl) Hpre
  icases Hpr with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + sign_extend (m := 64) imm := by
    rw [gprValRel3 cid m rs rs1 Hr, Hpa0]
  have HF : FstM rvwmoCatConsistent (dk3 (paZ pa) wd) i
        (fun _ data => iprop(⌜data = stBytes wd (rget cid m rs2) ∧
          (rs2.toNat = 0 → data = stBytes wd 0#64)⌝ -∗ Post)) ⊢
      Fst (dk3 (paZ pa) wd) i
        (fun _ data => iprop(⌜data = stBytes wd (rget cid m rs2) ∧
          (rs2.toNat = 0 → data = stBytes wd 0#64)⌝ -∗ Post)) := .rfl
  ihave F := HF $$ F
  iapply (XStoreS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (Hmid3 i G) (dk3 (paZ pa) wd) _ s rs k pc w32 imm rs2 rs1 wd pa pa r0 HRet Hctrl HPC Htx
    Hsf Hdec Hvw Hw Hva (Hdmap _ pa wd (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb3 i cpu G rs k)) $$ F
  iintro %t' %rs' %ib' %k' %HG' %Hag Hpt
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  icases Hpt with ⟨%kd, Hpt⟩
  have Hdat : stBytes wd (gprVal rs rs2) = stBytes wd (rget cid m rs2) ∧
      (rs2.toNat = 0 → stBytes wd (gprVal rs rs2) = stBytes wd 0#64) :=
    ⟨by rw [gprValRel3 cid m rs rs2 Hr],
     fun H0 => by
      show stBytes wd (uxaXget rs rs2) = _
      rw [AxReuseProbe2.uxaXgetZero rs rs2 H0]⟩
  ispecialize Hpt $$ %Hdat
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 4#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur3Keep cid cpu T satp0 m pc rs t' rs' ib' k' C Hc' (by rw [HPC']; rfl) Hg' Hag
    Htp Hspx Hrel
  iapply Hcont $$ [Hm Hn] [Hp] Hpt %_ %m %n %(pc + 4#64) %false %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · iexact Hn
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      have h := Hnf Ha
      unfold fenceRwWIns at h
      cases h

include hmode hasid hppn Htext Hflow Hloc HG in
/-- Rocq `wp_fence_c3`: `fence rw,w` — the flag becomes ARMED (the certificate's exit flag). -/
theorem wpFenceC3 (pc : BitVec 64) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    ⊢ sieCap3 (GF := GF) γm γn cid m n b p -∗
      pcIs3 (GF := GF) γp Armed pc -∗
      instr3 (GF := GF) σi T satp0 Armed pc false fenceRwWIns -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCap3 γm γn cpu' m n b p -∗
        pcIs3 γp Armed (pc + 4#64) -∗
        goal3 i cid cpu γm γp γn T satp0 Cond)) -∗
      goal3 i cid cpu γm γp γn T satp0 Cond := by
  unfold sieCap3 pcIs3
  iintro ⟨%Hb, Hm, Hn⟩ ⟨%r0, Hp, %_⟩ Hi Hcont
  subst Hb
  ihave %Hi := instr3Nrvc σi T satp0 Armed pc _ $$ Hi
  obtain ⟨Hins, _, _, _⟩ := Hi
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal3
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  iapply (XFenceSW σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0 (Hmid3 i G)
    s rs k pc w32 r0 HRet Hctrl HPC Htx Hsf Hdec (Hb3 i cpu G rs k))
  iintro %t' %rs' %ib' %k' %HG' %Hag %_
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 4#64, true) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur3Keep cid cpu T satp0 m pc rs t' rs' ib' k' C Hc' (by rw [HPC']; rfl) Hg' Hag
    Htp Hspx Hrel
  iapply Hcont $$ [Hm Hn] [Hp] %_ %m %n %(pc + 4#64) %true %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · iexact Hn
  · iexists true
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      exact fun _ => rfl

/- `amoswap.w{.aq} rd, rs2, (rs1)`: rd := the EXACT read value; the protocol's output at the
event's own read value (`OutOfV`) -/
variable (amoRes : PAddr → BitVec 32 → (BitVec 32 → IProp GF) → IProp GF)
variable (amoRule3 : ∀ pa wnew Post, ⊢ amoRes pa wnew Post -∗ ⌜damo (paZ pa) 4⌝ ∗
  FstM rvwmoCatConsistent (dk3 (paZ pa) 4) i
    (OutOfV i (fun _ ov data => iprop(⌜data = AxDataX.wrb 4 wnew⌝ -∗
      ∀ rvs, ⌜ov = some rvs⌝ -∗ Post (rrv 4 rvs)))))

theorem amoLdvLoaded (vs : List (BitVec 8)) :
    amoLdv 4 vs = AxCondM3.amoswapLoaded (rrv 4 vs) := rfl

include hmode hasid hppn CondGate3 Htext Hflow Hloc HG Hagree Hdmap HnoSplitReg amoRule3 in
/-- Rocq `wp_amoswap_c3`. -/
theorem wpAmoswapC3 (pc : BitVec 64) (aq : Bool) (rd rs2 rs1 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) (Post : BitVec 32 → IProp GF) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ sieCap3 (GF := GF) γm γn cid m n b p -∗
      pcIs3 (GF := GF) γp Armed pc -∗
      instr3 (GF := GF) σi T satp0 Armed pc false
        (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)) -∗
      amoRes (rget cid m rs1 + zeros (n := 64)) (AxCondM3.amoswapStored (rget cid m rs2)) Post -∗
      (∀ w : BitVec 32,
        wpNext b p cid (fun cpu' => iprop(
          sieCap3 γm γn cpu' (m.set rd (AxCondM3.amoswapLoaded w)) n b p -∗
          pcIs3 γp Armed (pc + 4#64) -∗
          Post w -∗
          goal3 i cid cpu γm γp γn T satp0 Cond))) -∗
      goal3 i cid cpu γm γp γn T satp0 Cond := by
  intro Hrd Hrdok
  generalize Hpa0 : rget cid m rs1 + zeros (n := 64) = pa
  unfold sieCap3 pcIs3
  iintro ⟨%Hb, Hm, Hn⟩ ⟨%r0, Hp, %_⟩ Hi Hres Hcont
  subst Hb
  ihave %Hi := instr3Nrvc σi T satp0 Armed pc _ $$ Hi
  obtain ⟨Hins, Hnf, _, _⟩ := Hi
  unfold goal3
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  iapply (CondGate3 s C (gateOf3 cid cpu σi T satp0 m pc s C _ Hcur Hins trivial)) $$ HC
  iintro %HCC HC
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  have Hr := Hrel HCC
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hpr := amoRule3 _ _ _ $$ Hres
  icases Hpr with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + zeros (n := 64) := by
    rw [gprValRel3 cid m rs rs1 Hr, Hpa0]
  iapply (XAmoswapSP σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0 (Hmid3 i G)
    (dk3 (paZ pa) 4) _ Hagree (dk3Nosplit i damo HnoSplitReg _ _ Hdr)
    s rs k pc w32 aq rs2 rs1 rd pa pa HRet Hctrl HPC Htx Hsf Hdec Hrd
    Hva (Hdmap _ pa 4 (Or.inr Hdr)) ⟨rfl, rfl⟩ (Hb3 i cpu G rs k)) $$ F
  iintro %vs %t' %rs' %ib' %k' %Hlen %HG' %Hag ⟨%kd, Ho, #Hpin⟩
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  ihave Ho := amoOutPin i Hagree _ kd vs _ $$ Hpin Ho
  have Hst : AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)) =
      AxDataX.wrb 4 (AxCondM3.amoswapStored (rget cid m rs2)) := by
    rw [gprValRel3 cid m rs rs2 Hr]
    rfl
  ispecialize Ho $$ %Hst %vs %rfl
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd (AxCondM3.amoswapLoaded (rrv 4 vs))) γm m m $$ Hm Hm'
    with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 4#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  ihave Hcont := Hcont $$ %(rrv 4 vs)
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  have Hcur' := cur3Upd cid cpu T satp0 m pc rs t' rs' ib' k' rd (amoLdv 4 vs)
    (AxCondM3.amoswapLoaded (rrv 4 vs)) C C Hrd Hrdok Hc' (by rw [HPC']; rfl) Hg' Hag Htp Hspx
    Hrel (fun HC0 => ⟨HC0, amoLdvLoaded vs⟩)
  iapply Hcont $$ [Hm Hn] [Hp] Ho %_ %(m.set rd (AxCondM3.amoswapLoaded (rrv 4 vs))) %n
    %(pc + 4#64) %false %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · iexact Hn
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      have h := Hnf Ha
      unfold fenceRwWIns at h
      cases h

/-- Rocq `fence_then_armed`: THE TWO-INSTRUCTION FACT (`fence rw,w; sw` ⇒ the `sw` is
`WCrel`): from the fence leaf's post the flag is set at `pc + 4`; the store leaf there (armed)
hands the rule the class `WCrel`. -/
theorem fenceThenArmed (pc : BitVec 64) (r : Bool) :
    Armed (pc + 4#64) → (Armed (pc + 4#64) → r = true) → wcls AxDataX.akPlain r = .WCrel := by
  intro Ha Hra
  rw [Hra Ha]
  exact wclsArmed _ rfl

end surf3

end Weak
