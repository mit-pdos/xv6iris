/-
Weak: **S-mode lock leaves, part 4: the SC LEAF SHAPES on a REVISED conditional surface**
(surface v2: the `AxSymMem3` surface with the X engine review's findings addressed),
instantiated with the real X leaves of `AxLeafS2` at the data regime `ctrlOkSW`.

Rocq: `iris/AxLeafS4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE SURFACE (v2).  As AxSymMem3: the SC map `m` is a ghost mirror of the physical registers,
related CONDITIONALLY (`C → gprRel cid m rs`) with sp / tp exact; the goal carries `Cond C`.
Changes: (1) CAPACITY RESTORED: `sieCap2 m n b p` mirrors the stack capacity `n` in a third
ghost variable `γn`; `goal2` quantifies it, so push/pop leaves can move it and every leaf here
keeps it.  (2) `Cond` LAWS THAT EXCLUDE `Cond := False`: `CondIntro` (`⌜C⌝ ⊢ Cond C`) and the
READBACK law `CondRb` (row end: `Cond C` lets the post learn `C`).  The law set is satisfiable
by a non-False model (`CondLawsModel`: `Cond := ⌜·⌝`) and `Cond := False` violates `CondIntro`
(`CondFalseNotIntro`).  (3) THE PC is kept EXACT (a conditional PC makes every later leaf
unprovable); c.ret must LEARN `C` at its control transfer (the "ctrl gate"); the same holds for
the BASE REGISTER of a load / store / AMO (the "addr gate", RVWMO ppo rule 9).  Both are the ONE
law `CondGate`: at a boundary whose instruction is a data access, `Cond C` may be turned into
`⌜C⌝` for the WPd.  It is a PREMISE (an adequacy-side fact), used only at data-access
boundaries (`gateAt`).
LEAVES (statements = the SC leaves' with `WP Loop` := `goal2`, `sie_cap_gpr` := `sieCap2`,
`pc_is` := `pcIs2`, `instr` := `instr2`, `↦₈` / `↦₄` := the protocol's owned words `wpt8` /
`wpt4`): `wpLdC`, `wpLwC`, `wpSdC`, `wpSwC`, `wpFenceC`, `wpAmoswapC` (the generic AMO shape:
∀ w, rd := `amoswapLoaded w`, the protocol post `Post w`).
PREMISED (section variables): the protocol rules `ld8Rule` / `ld4Rule` / `st8Rule` / `st4Rule` /
`amoRule` (the WPd lock protocol, D2), the identity direct map of the data regions (`Hdmap`),
the region side conditions, the bridge's instance premises, `CondGate`, and `amoRdFlow` — the
AMO's read value must reach the WRITE flow's output (the bridge's RMW arm hands the flow output
only the WRITTEN bytes).

## Deviations from Rocq

1. O2 STAGE C (as `AxSymMem3` deviation 1): there is no `ax_text`, so the section premise
   `Hdreg` (`dreg a n ∨ damo a n → ¬ ax_text a`) is DROPPED, and so is `dk_ntext` (its only
   user; its conclusion fed `X_load_S`'s `Hntext`, which `AxLeafS2.XLoadS` no longer takes;
   no downstream weak file uses it).
2. Q7 (as `AxLeafS2` deviation 2): every X leaf takes `sfAnnB 32 w = false` after the text
   fact, so `insAt pc ins` is `∃ w32, textAt4S σi T pc w32 ∧ sfAnnB 32 w32 = false ∧
   decodes w32 ins` (Rocq: no sfAnnB conjunct).
3. SPELLING as AxSymMem3 / AxLeafS2: `regfile` ↦ `RegMap`, `rget m r` ↦ `rget cid m r` (explicit
   SC hart `cid`, Rocq's section `CpuId`); `<[Regidx rd := regval_into_reg v]> m` ↦
   `m.set rd v`; `Rtp` ↦ `4#5`, `csp_rs1` ↦ `2#5`; `IntrDefs.rd_ok` ↦ `MachCSL.rdOk` (three
   conjuncts: `rd ≠ 0`, `≠ sp`, `≠ tp`); `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`; `uint pa` ↦ `paZ pa`;
   `data_at_S … va w va` with `w : Z`, `Z.to_nat w` ↦ `w : Nat`; `add_vec x (sign_extend' 64
   imm)` ↦ `x + sign_extend (m := 64) imm`; `zeros' 64` ↦ `zeros (n := 64)`;
   `add_vec_int pc 4` ↦ `pc + 4#64`; `register_lookup PC rs` ↦ `rs .PC`;
   `gpr r t` ↦ `uxaXget t r`, `gpr_post` ↦ `gprPost`; `regs_agree seip_reg` ↦
   `regsAgree AxRunClose.pinReg`; `Interface.Ret tt` ↦ `.pure ()`; `wp_next` ↦ `wpNext`
   (continuation indexed by the resuming hart; `goal2` stays at the section hart `cid`, as in
   Rocq, where the section constant does not take the bound `CpuId`); `ghost_var γ (1/2)` ↦
   `ghost_var γ (.own (1 : Qp).half)`; `WPd s @ MaybeStuck; i {{ Φ0 }}` ↦
   `wpd .MaybeStuck i s Φ0`; `iProp` wand statements are `⊢ … -∗ …`.  The `let`s of the leaf
   statements (`pa`, `storeval`) are inlined.
4. WpAmo's `amoswap_stored` / `amoswap_loaded` and RiscvExtras' `trunc32` have no Lean
   counterpart: they are defined here, file-qualified (`AxLeafS4.amoswapStored` = `amoStv 4`,
   `AxLeafS4.amoswapLoaded w` = `sign_extend (m := 64) w`, `AxLeafS4.trunc32` = the low 32 bits).
5. `Cond_pers` is an instance binder `[∀ C, Persistent (Cond C)]`; the laws are `⊢`
   entailments.  `Cond_laws_model`'s first conjunct (`∀ C, Persistent (CondP C)`; Lean's
   `Persistent` is not a `Prop`) is stated by its content `CondP C ⊢ <pers> CondP C`; the
   instance itself is `AxLeafS4.condPPers`.
6. The Ltac `open_goal` is inlined in each leaf.

**Rocq → Lean name map.**  `cur2` `cur2`, `Goal2` `goal2`, `sie_cap2` `sieCap2`, `pc_is2`
`pcIs2`, `decodes` `decodes`, `ins_at` `insAt`, `instr2` `instr2`, `is_dmem` `isDmem`, `gate_at`
`gateAt`, `dk` `AxLeafS4.dk` (duplicated name), `dk_normw` `dkNormw`, `dk_nosplit` `dkNosplit`,
`Hmid0` `AxLeafS4.Hmid0` (duplicated name), `Hb0` `Hb0`, `good_retx` `goodRetx`, `gpr_val_rel`
`gprValRel`, `cur2_keep` `cur2Keep`, `cur2_upd` `cur2Upd`, `gate_of` `gateOf`, `wp_ld_c`
`wpLdC`, `wp_lw_c` `wpLwC`, `wp_sd_c` `wpSdC`, `wp_sw_c` `wpSwC`, `wp_fence_c` `wpFenceC`,
`wp_amoswap_c` `wpAmoswapC`, `Cond_false_not_intro` `CondFalseNotIntro`, `CondP`
`AxLeafS4.CondP` (duplicated name), `Cond_laws_model` `CondLawsModel`.  Section parameters:
`Cond_and` `CondAnd`, `Cond_mono` `CondMono`, `Cond_intro` `CondIntro`, `Cond_rb` `CondRb`,
`Cond_gate` `CondGate`, `HnoRmw_reg` `HnoRmwReg`, `HnoSplit_reg` `HnoSplitReg`, `ld8_rule`
`ld8Rule`, `ld4_rule` `ld4Rule`, `st8_rule` `st8Rule`, `st4_rule` `st4Rule`, `amo_res` `amoRes`,
`AmoOut` `AmoOut`, `amo_rule` `amoRule`, `amo_rd_flow` `amoRdFlow`.  Lean-only (file-qualified):
`AxLeafS4.amoswapStored`, `AxLeafS4.amoswapLoaded`, `AxLeafS4.trunc32` (deviation 4),
instance `AxLeafS4.condPPers` (deviation 5).

**Dropped:** `dk_ntext` (deviation 1), the Ltac `open_goal` (deviation 6) and the
`Print Assumptions` lines (the lint's axiom check covers them).  Rocq 29 definitions/lemmas;
Lean 28 ported + 4 Lean-only.
-/
import Weak.AxLeafS2
import Weak.AxSymMem3

namespace Weak

open Iris Iris.BI Iris.ProofMode MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 0. Value vocabulary (Lean-only; deviation 4) -/

/-- Rocq `WpAmo.amoswap_stored`: the word an `amoswap.w` stores (rs2's low word). -/
def AxLeafS4.amoswapStored (v : BitVec 64) : BitVec 32 := amoStv 4 v

/-- Rocq `WpAmo.amoswap_loaded`: the value an `amoswap.w` writes to rd. -/
def AxLeafS4.amoswapLoaded (w : BitVec 32) : BitVec 64 := sign_extend (m := 64) w

/-- Rocq `RiscvExtras.trunc32`: the low 32 bits (the value a 4-byte store commits). -/
def AxLeafS4.trunc32 (w : BitVec 64) : BitVec 32 := BitVec.setWidth 32 w

/-! # 1. The surface -/

section surf2
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] [GhostVarG GF Nat]
variable (i : Agent) (cid cpu : CPU) (γm γp γn : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)

/- the annotation-backed condition and its laws -/
variable (Cond : Prop → IProp GF) [∀ C, Persistent (Cond C)]
variable (CondAnd : ∀ C1 C2, ⊢ Cond C1 -∗ Cond C2 -∗ Cond (C1 ∧ C2))
variable (CondMono : ∀ C1 C2 : Prop, (C1 → C2) → ⊢ Cond C1 -∗ Cond C2)
variable (CondIntro : ∀ C : Prop, iprop(⌜C⌝) ⊢ Cond C)
variable (CondRb : ∀ C (Φ : Athread → IProp GF) s,
  ⊢ Cond C -∗ postLifting (fun s' => iprop(⌜C⌝ -∗ Φ s')) i s -∗ postLifting Φ i s)

/-- Rocq `cur2`. -/
def cur2 (m : RegMap) (pc : BitVec 64) (s : Athread) (C : Prop) : Prop :=
  ∃ rs k, RetX cpu rs k s ∧ ctrlOkSW T satp0 rs ∧ rs .PC = pc ∧
    phys5 rs 4#5 = rget cid m 4#5 ∧ phys5 rs 2#5 = rget cid m 2#5 ∧
    (C → gprRel cid m rs)

/-- Rocq `Goal2`. -/
def goal2 : IProp GF :=
  iprop(∀ s m (n : Nat) pc C, ⌜cur2 cid cpu T satp0 m pc s C⌝ -∗ ghost_var γm (.own (1 : Qp).half) m -∗
    ghost_var γn (.own (1 : Qp).half) n -∗ ghost_var γp (.own (1 : Qp).half) pc -∗ Cond C -∗
    wpd .MaybeStuck i s (Φ0 (GF := GF)))

/-- Rocq `sie_cap2`. -/
def sieCap2 (_cid0 : CPU) (m : RegMap) (n : Nat) (b : Bool) (_p : BitVec 64) : IProp GF :=
  iprop(⌜b = false⌝ ∗ ghost_var γm (.own (1 : Qp).half) m ∗ ghost_var γn (.own (1 : Qp).half) n)

/-- Rocq `pc_is2`. -/
def pcIs2 (pc : BitVec 64) : IProp GF := ghost_var γp (.own (1 : Qp).half) pc

/-- Rocq `decodes`. -/
def decodes (w32 : BitVec 32) (ins : instruction) : Prop :=
  ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
    EvA (imgS σi) (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w32) t

/-- Rocq `ins_at` (+ the Q7 conjunct, deviation 2). -/
def insAt (pc : BitVec 64) (ins : instruction) : Prop :=
  ∃ w32, textAt4S σi T pc w32 ∧ sfAnnB 32 w32 = false ∧ decodes σi T satp0 w32 ins

/-- Rocq `instr2`. -/
def instr2 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(⌜is_rvc = false ∧ insAt σi T satp0 pc ins⌝)

/-- Rocq `is_dmem`. -/
def isDmem (ins : instruction) : Prop :=
  match ins with
  | .LOAD _ | .STORE _ | .AMO _ => True
  | _ => False

/-- Rocq `gate_at`. -/
def gateAt (s : Athread) : Prop :=
  ∃ rs k ins, RetX cpu rs k s ∧ insAt σi T satp0 (rs .PC) ins ∧ isDmem ins

/- THE GATE LAW (premise): at a data-access boundary the WPd may assume the conditions it
holds (RVWMO ppo rule 9). -/
variable (CondGate : ∀ s C, gateAt cpu σi T satp0 s →
  ⊢ Cond C -∗ (⌜C⌝ -∗ wpd .MaybeStuck i s (Φ0 (GF := GF))) -∗ wpd .MaybeStuck i s (Φ0 (GF := GF)))

/- the bridge's instance premises -/
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

/- data regions: plain (loads / stores) and AMO targets; identity direct map with A/D preset
(Rocq `Hdreg` dropped: deviation 1) -/
variable (dreg damo : Int → Nat → Prop)
variable (Hdmap : ∀ (acc : MemoryAccessType mem_payload) (va : BitVec 64) (w : Nat),
  dreg (paZ va) w ∨ damo (paZ va) w → dataAtS σi T acc va w va)
variable (HnoRmwReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dreg base n⌝)
variable (HnoSplitReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ damo base n⌝)

/-- Rocq `dk`. -/
def AxLeafS4.dk (a : Int) (n : Nat) : Int → Nat → Prop := fun a' n' => a' = a ∧ n' = n

include HnoRmwReg in
/-- Rocq `dk_normw`. -/
theorem dkNormw (a : Int) (n : Nat) : dreg a n → ∀ GD, rvwmoCatConsistent GD →
    AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n' : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n' →
        ¬ AxLeafS4.dk a n base n'⌝ := by
  intro Hd GD Hc
  refine (HnoRmwReg GD Hc).trans (pure_mono ?_)
  intro Hnr k lb aq rl base n' Hlb Hid ⟨e1, e2⟩
  subst e1 e2
  exact Hnr k lb aq rl _ _ Hlb Hid Hd

include HnoSplitReg in
/-- Rocq `dk_nosplit`. -/
theorem dkNosplit (a : Int) (n : Nat) : damo a n → ∀ GD, rvwmoCatConsistent GD →
    AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n' : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n' →
        ¬ AxLeafS4.dk a n base n'⌝ := by
  intro Hd GD Hc
  refine (HnoSplitReg GD Hc).trans (pure_mono ?_)
  intro Hns k lb aq base n' Hlb Hid ⟨e1, e2⟩
  subst e1 e2
  exact Hns k lb aq _ _ Hlb Hid Hd

/- the protocol's owned words and rules (PREMISES: the WPd lock protocol of D2) -/
variable (wpt8 : PAddr → DFrac → BitVec 64 → IProp GF) (wpt4 : PAddr → DFrac → BitVec 32 → IProp GF)
variable (ld8Rule : ∀ pa dq v, ⊢ wpt8 pa dq v -∗ ⌜dreg (paZ pa) 8⌝ ∗
  Fld (AxLeafS4.dk (paZ pa) 8) i (fun _ vs => iprop(wpt8 pa dq v ∗ Cond (ldRes false 8 vs = v))))
variable (ld4Rule : ∀ pa dq v, ⊢ wpt4 pa dq v -∗ ⌜dreg (paZ pa) 4⌝ ∗
  Fld (AxLeafS4.dk (paZ pa) 4) i
    (fun _ vs => iprop(wpt4 pa dq v ∗ Cond (ldRes false 4 vs = sign_extend (m := 64) v))))
variable (st8Rule : ∀ pa vold vnew, ⊢ wpt8 pa (.own 1) vold -∗ ⌜dreg (paZ pa) 8⌝ ∗
  Fst (AxLeafS4.dk (paZ pa) 8) i
    (fun _ data => iprop(⌜data = stBytes 8 vnew⌝ -∗ wpt8 pa (.own 1) vnew)))
variable (st4Rule : ∀ pa vold vnew, ⊢ wpt4 pa (.own 1) vold -∗ ⌜dreg (paZ pa) 4⌝ ∗
  Fst (AxLeafS4.dk (paZ pa) 4) i
    (fun _ data => iprop(⌜data = stBytes 4 vnew⌝ -∗ wpt4 pa (.own 1) (AxLeafS4.trunc32 vnew))))
/- the AMO: the protocol resource `amoRes pa wnew Post` yields the write flow; its output
`AmoOut` must be READ BACK against the exclusive read's bytes (`amoRdFlow`) -/
variable (amoRes : PAddr → BitVec 32 → (BitVec 32 → IProp GF) → IProp GF)
  (AmoOut : Nat → PAddr → BitVec 32 → (BitVec 32 → IProp GF) → IProp GF)
variable (amoRule : ∀ pa wnew Post, ⊢ amoRes pa wnew Post -∗ ⌜damo (paZ pa) 4⌝ ∗
  Fst (AxLeafS4.dk (paZ pa) 4) i
    (fun k data => iprop(⌜data = AxDataX.wrb 4 wnew⌝ -∗ AmoOut k pa wnew Post)))
variable (amoRdFlow : ∀ k pa wnew Post (rvs : List (BitVec 8)), rvs.length = 4 →
  ⊢ AmoOut k pa wnew Post -∗
    ∃ w : BitVec 32, Cond (amoLdv 4 rvs = AxLeafS4.amoswapLoaded w) ∗ Post w)

/-! # 2. Common steps -/

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)]
  [GhostVarG GF Nat] in
/-- Rocq `Hmid0`. -/
theorem AxLeafS4.Hmid0 [InvGS_gen hlc GF] [AxirisG GF] : ∀ GD s, G GD → midState s →
    s.atK = (AxOpsem.grow GD i).length → ⊢ postLifting (Φ0 (GF := GF)) i s :=
  fun _ _ _ _ _ => postLiftingΦ0 i _

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)]
  [GhostVarG GF Nat] in
/-- Rocq `Hb0`. -/
theorem Hb0 [InvGS_gen hlc GF] [AxirisG GF] (rs : RegFile) (k : Nat) : ∀ GD s1, G GD →
    RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
    ⊢ postLifting (Φ0 (GF := GF)) i s1 :=
  fun _ _ _ _ _ => postLiftingΦ0 i _

/-- Rocq `good_retx`. -/
theorem goodRetx (rs' : RegFile) (t' : ExecSt) (ib' : Ibch) (k' : Nat) :
    regsAgree AxRunClose.pinReg rs' t'.regs →
    RetX cpu t'.regs k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
  fun Hag => ⟨ib', rfl, rfl, rfl, rfl, rfl, Hag⟩

/-- Rocq `gpr_val_rel`. -/
theorem gprValRel (m : RegMap) (rs : RegFile) (r : BitVec 5) :
    gprRel cid m rs → gprVal rs r = rget cid m r := fun Hr => Hr r

/-- Rocq `cur2_keep`: the post-state of a non-writing leaf. -/
theorem cur2Keep (m : RegMap) (pc : BitVec 64) (rs : RegFile) (t' : ExecSt) (rs' : RegFile)
    (ib' : Ibch) (k' : Nat) (C : Prop) :
    ctrlOkSW T satp0 t'.regs → t'.regs .PC = pc + 4#64 →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget t'.regs r = uxaXget rs r) →
    regsAgree AxRunClose.pinReg rs' t'.regs →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 → (C → gprRel cid m rs) →
    cur2 cid cpu T satp0 m (pc + 4#64) ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ C := by
  intro Hc HPC Hg Hag Htp Hsp Hrel
  have Hsame : ∀ r, phys5 t'.regs r = phys5 rs r := by
    intro r
    show uxaXget t'.regs r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hg r h0
  refine ⟨t'.regs, k', goodRetx cpu rs' t' ib' k' Hag, Hc, HPC, ?_, ?_, ?_⟩
  · rw [Hsame]; exact Htp
  · rw [Hsame]; exact Hsp
  · intro HCC r
    rw [← Hrel HCC r]
    exact Hsame r

/-- Rocq `cur2_upd`: the post-state of a leaf writing `rd := val`, logically `v` under `C'`. -/
theorem cur2Upd (m : RegMap) (pc : BitVec 64) (rs : RegFile) (t' : ExecSt) (rs' : RegFile)
    (ib' : Ibch) (k' : Nat) (rd : BitVec 5) (val v : BitVec 64) (C C' : Prop) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ctrlOkSW T satp0 t'.regs → t'.regs .PC = pc + 4#64 →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget t'.regs r = gprPost (some (rd, val)) rs r) →
    regsAgree AxRunClose.pinReg rs' t'.regs →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 → (C → gprRel cid m rs) →
    (C' → C ∧ val = v) →
    cur2 cid cpu T satp0 (m.set rd v) (pc + 4#64) ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ C' := by
  intro Hrd Hrdok Hc HPC Hg Hag Htp Hsp Hrel HC'
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget t'.regs r = if r = rd then val else uxaXget rs r := fun r Hr => Hg r Hr
  have Hne_tp : (4#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.2 (uint5Inj _ _ E).symm
  have Hne_sp : (2#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.1 (uint5Inj _ _ E).symm
  refine ⟨t'.regs, k', goodRetx cpu rs' t' ib' k' Hag, Hc, HPC, ?_, ?_, ?_⟩
  · rw [phys5UpdNe rs t'.regs rd 4#5 _ Hg' Hne_tp, Htp, rget_tp, rget_tp]
  · rw [phys5UpdNe rs t'.regs rd 2#5 _ Hg' Hne_sp, Hsp,
      rget_ne cid _ 2#5 (by decide) (by decide), rget_ne cid _ 2#5 (by decide) (by decide),
      RegMap.set_other _ _ _ _ (fun e => Hrdok.2.1 e.symm)]
  · intro HCC'
    obtain ⟨HCC, rfl⟩ := HC' HCC'
    exact gprRelUpd cid m rs t'.regs rd val (Hrel HCC) Hrd Hrdok.2.2 Hg'

/-- Rocq `gate_of`. -/
theorem gateOf (m : RegMap) (pc : BitVec 64) (s : Athread) (C : Prop) (ins : instruction) :
    cur2 cid cpu T satp0 m pc s C → insAt σi T satp0 pc ins → isDmem ins →
    gateAt cpu σi T satp0 s := by
  rintro ⟨rs, k, HRet, _, HPC, _⟩ Hins Hd
  exact ⟨rs, k, ins, HRet, HPC ▸ Hins, Hd⟩

/-! # 3. The leaves -/

include hmode hasid hppn CondAnd CondGate Htext Hflow Hloc HG Hdmap HnoRmwReg ld8Rule in
/-- Rocq `wp_ld_c`. -/
theorem wpLdC (pc : BitVec 64) (rd rs1 : BitVec 5) (imm : BitVec 12)
    (m : RegMap) (n : Nat) (v : BitVec 64) (b : Bool) (p : BitVec 64) {dqm : DFrac} :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ sieCap2 (GF := GF) γm γn cid m n b p -∗ pcIs2 (GF := GF) γp pc -∗
      instr2 (GF := GF) σi T satp0 pc false (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) -∗
      wpt8 (rget cid m rs1 + sign_extend (m := 64) imm) dqm v -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCap2 γm γn cpu' (m.set rd v) n b p -∗
        pcIs2 γp (pc + 4#64) -∗ wpt8 (rget cid m rs1 + sign_extend (m := 64) imm) dqm v -∗
        goal2 i cid cpu γm γp γn T satp0 Cond)) -∗
      goal2 i cid cpu γm γp γn T satp0 Cond := by
  intro Hrd Hrdok
  generalize Hpa0 : rget cid m rs1 + sign_extend (m := 64) imm = pa
  unfold sieCap2 pcIs2 instr2
  iintro ⟨%Hb, Hm, Hn⟩ Hp %Hins Hpt Hcont
  subst Hb
  obtain ⟨_, Hins⟩ := Hins
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal2
  iintro %s %m' %n' %pc' %C %Hcur Hm' Hn' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2 h3
  iapply (CondGate s C (gateOf cid cpu σi T satp0 m pc s C _ Hcur Hins trivial)) $$ HC
  iintro %HCC
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  have Hr := Hrel HCC
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hld := ld8Rule pa dqm v $$ Hpt
  icases Hld with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + sign_extend (m := 64) imm := by
    rw [← Hpa0, gprValRel cid m rs rs1 Hr]
  iapply (XLoadS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (AxLeafS4.Hmid0 i G) (AxLeafS4.dk (paZ pa) 8)
    (fun _ vs => iprop(wpt8 pa dqm v ∗ Cond (ldRes false 8 vs = v)))
    (dkNormw i dreg HnoRmwReg _ _ Hdr) s rs k pc w32 imm rs1 rd false 8 pa pa HRet Hctrl HPC
    Htx Hsf Hdec Hrd (Or.inr (Or.inr (Or.inr rfl))) ⟨by decide, by decide⟩ Hva
    (Hdmap _ pa 8 (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb0 i cpu G rs k)) $$ F
  iintro %vs %t' %rs' %ib' %k' %_ %Hgood %Hag Hout
  obtain ⟨Hc', HPC', Hg'⟩ := Hgood
  icases Hout with ⟨%kd, Hpt, #Hce⟩
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd v) γm m m $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 4#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur2Upd cid cpu T satp0 m pc rs t' rs' ib' k' rd (ldRes false 8 vs) v C
    (C ∧ ldRes false 8 vs = v) Hrd Hrdok Hc' (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hrel
    (fun h => h)
  ihave Hc2 := CondAnd _ _ $$ HC Hce
  iapply Hcont $$ [Hm Hn] Hp Hpt %_ %(m.set rd v) %n %(pc + 4#64) %(C ∧ ldRes false 8 vs = v)
    %Hcur' Hm' Hn' Hp' Hc2
  isplitr
  · ipureintro; rfl
  · isplitl [Hm]
    · iexact Hm
    · iexact Hn

include hmode hasid hppn CondAnd CondGate Htext Hflow Hloc HG Hdmap HnoRmwReg ld4Rule in
/-- Rocq `wp_lw_c`. -/
theorem wpLwC (pc : BitVec 64) (rd rs1 : BitVec 5) (imm : BitVec 12)
    (m : RegMap) (n : Nat) (v : BitVec 32) (b : Bool) (p : BitVec 64) {dqm : DFrac} :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ sieCap2 (GF := GF) γm γn cid m n b p -∗ pcIs2 (GF := GF) γp pc -∗
      instr2 (GF := GF) σi T satp0 pc false (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4)) -∗
      wpt4 (rget cid m rs1 + sign_extend (m := 64) imm) dqm v -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCap2 γm γn cpu' (m.set rd (sign_extend (m := 64) v)) n b p -∗
        pcIs2 γp (pc + 4#64) -∗ wpt4 (rget cid m rs1 + sign_extend (m := 64) imm) dqm v -∗
        goal2 i cid cpu γm γp γn T satp0 Cond)) -∗
      goal2 i cid cpu γm γp γn T satp0 Cond := by
  intro Hrd Hrdok
  generalize Hpa0 : rget cid m rs1 + sign_extend (m := 64) imm = pa
  unfold sieCap2 pcIs2 instr2
  iintro ⟨%Hb, Hm, Hn⟩ Hp %Hins Hpt Hcont
  subst Hb
  obtain ⟨_, Hins⟩ := Hins
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal2
  iintro %s %m' %n' %pc' %C %Hcur Hm' Hn' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2 h3
  iapply (CondGate s C (gateOf cid cpu σi T satp0 m pc s C _ Hcur Hins trivial)) $$ HC
  iintro %HCC
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  have Hr := Hrel HCC
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hld := ld4Rule pa dqm v $$ Hpt
  icases Hld with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + sign_extend (m := 64) imm := by
    rw [← Hpa0, gprValRel cid m rs rs1 Hr]
  iapply (XLoadS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (AxLeafS4.Hmid0 i G) (AxLeafS4.dk (paZ pa) 4)
    (fun _ vs => iprop(wpt4 pa dqm v ∗ Cond (ldRes false 4 vs = sign_extend (m := 64) v)))
    (dkNormw i dreg HnoRmwReg _ _ Hdr) s rs k pc w32 imm rs1 rd false 4 pa pa HRet Hctrl HPC
    Htx Hsf Hdec Hrd (Or.inr (Or.inr (Or.inl rfl))) ⟨by decide, by decide⟩ Hva
    (Hdmap _ pa 4 (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb0 i cpu G rs k)) $$ F
  iintro %vs %t' %rs' %ib' %k' %_ %Hgood %Hag Hout
  obtain ⟨Hc', HPC', Hg'⟩ := Hgood
  icases Hout with ⟨%kd, Hpt, #Hce⟩
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd (sign_extend (m := 64) v)) γm m m $$ Hm Hm'
    with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 4#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur2Upd cid cpu T satp0 m pc rs t' rs' ib' k' rd (ldRes false 4 vs)
    (sign_extend (m := 64) v) C (C ∧ ldRes false 4 vs = sign_extend (m := 64) v) Hrd Hrdok Hc'
    (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hrel (fun h => h)
  ihave Hc2 := CondAnd _ _ $$ HC Hce
  iapply Hcont $$ [Hm Hn] Hp Hpt %_ %(m.set rd (sign_extend (m := 64) v)) %n %(pc + 4#64)
    %(C ∧ ldRes false 4 vs = sign_extend (m := 64) v) %Hcur' Hm' Hn' Hp' Hc2
  isplitr
  · ipureintro; rfl
  · isplitl [Hm]
    · iexact Hm
    · iexact Hn

include hmode hasid hppn CondGate Htext Hflow Hloc HG Hdmap st8Rule in
/-- Rocq `wp_sd_c`. -/
theorem wpSdC (pc : BitVec 64) (rs2 rs1 : BitVec 5) (imm : BitVec 12)
    (m : RegMap) (n : Nat) (vold : BitVec 64) (b : Bool) (p : BitVec 64) :
    ⊢ sieCap2 (GF := GF) γm γn cid m n b p -∗ pcIs2 (GF := GF) γp pc -∗
      instr2 (GF := GF) σi T satp0 pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) -∗
      wpt8 (rget cid m rs1 + sign_extend (m := 64) imm) (.own 1) vold -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCap2 γm γn cpu' m n b p -∗
        pcIs2 γp (pc + 4#64) -∗
        wpt8 (rget cid m rs1 + sign_extend (m := 64) imm) (.own 1) (rget cid m rs2) -∗
        goal2 i cid cpu γm γp γn T satp0 Cond)) -∗
      goal2 i cid cpu γm γp γn T satp0 Cond := by
  generalize Hpa0 : rget cid m rs1 + sign_extend (m := 64) imm = pa
  unfold sieCap2 pcIs2 instr2
  iintro ⟨%Hb, Hm, Hn⟩ Hp %Hins Hpt Hcont
  subst Hb
  obtain ⟨_, Hins⟩ := Hins
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal2
  iintro %s %m' %n' %pc' %C %Hcur Hm' Hn' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2 h3
  iapply (CondGate s C (gateOf cid cpu σi T satp0 m pc s C _ Hcur Hins trivial)) $$ HC
  iintro %HCC
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  have Hr := Hrel HCC
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hst := st8Rule pa vold (rget cid m rs2) $$ Hpt
  icases Hst with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + sign_extend (m := 64) imm := by
    rw [← Hpa0, gprValRel cid m rs rs1 Hr]
  iapply (XStoreS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (AxLeafS4.Hmid0 i G) (AxLeafS4.dk (paZ pa) 8)
    (fun _ data => iprop(⌜data = stBytes 8 (rget cid m rs2)⌝ -∗
      wpt8 pa (.own 1) (rget cid m rs2)))
    s rs k pc w32 imm rs2 rs1 8 pa pa false HRet Hctrl HPC Htx Hsf Hdec
    (Or.inr (Or.inr (Or.inr rfl))) ⟨by decide, by decide⟩ Hva
    (Hdmap _ pa 8 (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb0 i cpu G rs k)) $$ F
  iintro %t' %rs' %ib' %k' %Hgood %Hag Hout
  obtain ⟨Hc', HPC', Hg'⟩ := Hgood
  icases Hout with ⟨%kd, Hpt⟩
  ihave Hpt := Hpt $$ %(by rw [gprValRel cid m rs rs2 Hr])
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 4#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur2Keep cid cpu T satp0 m pc rs t' rs' ib' k' C Hc' (by rw [HPC']; rfl) Hg' Hag
    Htp Hspx Hrel
  iapply Hcont $$ [Hm Hn] Hp Hpt %_ %m %n %(pc + 4#64) %C %Hcur' Hm' Hn' Hp' HC
  isplitr
  · ipureintro; rfl
  · isplitl [Hm]
    · iexact Hm
    · iexact Hn

include hmode hasid hppn CondGate Htext Hflow Hloc HG Hdmap st4Rule in
/-- Rocq `wp_sw_c`. -/
theorem wpSwC (pc : BitVec 64) (rs2 rs1 : BitVec 5) (imm : BitVec 12)
    (m : RegMap) (n : Nat) (vold : BitVec 32) (b : Bool) (p : BitVec 64) :
    ⊢ sieCap2 (GF := GF) γm γn cid m n b p -∗ pcIs2 (GF := GF) γp pc -∗
      instr2 (GF := GF) σi T satp0 pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, 4)) -∗
      wpt4 (rget cid m rs1 + sign_extend (m := 64) imm) (.own 1) vold -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCap2 γm γn cpu' m n b p -∗
        pcIs2 γp (pc + 4#64) -∗
        wpt4 (rget cid m rs1 + sign_extend (m := 64) imm) (.own 1)
          (AxLeafS4.trunc32 (rget cid m rs2)) -∗
        goal2 i cid cpu γm γp γn T satp0 Cond)) -∗
      goal2 i cid cpu γm γp γn T satp0 Cond := by
  generalize Hpa0 : rget cid m rs1 + sign_extend (m := 64) imm = pa
  unfold sieCap2 pcIs2 instr2
  iintro ⟨%Hb, Hm, Hn⟩ Hp %Hins Hpt Hcont
  subst Hb
  obtain ⟨_, Hins⟩ := Hins
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal2
  iintro %s %m' %n' %pc' %C %Hcur Hm' Hn' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2 h3
  iapply (CondGate s C (gateOf cid cpu σi T satp0 m pc s C _ Hcur Hins trivial)) $$ HC
  iintro %HCC
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  have Hr := Hrel HCC
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hst := st4Rule pa vold (rget cid m rs2) $$ Hpt
  icases Hst with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + sign_extend (m := 64) imm := by
    rw [← Hpa0, gprValRel cid m rs rs1 Hr]
  iapply (XStoreS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (AxLeafS4.Hmid0 i G) (AxLeafS4.dk (paZ pa) 4)
    (fun _ data => iprop(⌜data = stBytes 4 (rget cid m rs2)⌝ -∗
      wpt4 pa (.own 1) (AxLeafS4.trunc32 (rget cid m rs2))))
    s rs k pc w32 imm rs2 rs1 4 pa pa false HRet Hctrl HPC Htx Hsf Hdec
    (Or.inr (Or.inr (Or.inl rfl))) ⟨by decide, by decide⟩ Hva
    (Hdmap _ pa 4 (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb0 i cpu G rs k)) $$ F
  iintro %t' %rs' %ib' %k' %Hgood %Hag Hout
  obtain ⟨Hc', HPC', Hg'⟩ := Hgood
  icases Hout with ⟨%kd, Hpt⟩
  ihave Hpt := Hpt $$ %(by rw [gprValRel cid m rs rs2 Hr])
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 4#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur2Keep cid cpu T satp0 m pc rs t' rs' ib' k' C Hc' (by rw [HPC']; rfl) Hg' Hag
    Htp Hspx Hrel
  iapply Hcont $$ [Hm Hn] Hp Hpt %_ %m %n %(pc + 4#64) %C %Hcur' Hm' Hn' Hp' HC
  isplitr
  · ipureintro; rfl
  · isplitl [Hm]
    · iexact Hm
    · iexact Hn

include hmode hasid hppn Htext Hflow Hloc HG in
/-- Rocq `wp_fence_c`. -/
theorem wpFenceC (pc : BitVec 64) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    ⊢ sieCap2 (GF := GF) γm γn cid m n b p -∗
      pcIs2 (GF := GF) γp pc -∗
      instr2 (GF := GF) σi T satp0 pc false
        (.FENCE (0#4, 3#4, 1#4, .Regidx 0#5, .Regidx 0#5)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCap2 γm γn cpu' m n b p -∗
        pcIs2 γp (pc + 4#64) -∗
        goal2 i cid cpu γm γp γn T satp0 Cond)) -∗
      goal2 i cid cpu γm γp γn T satp0 Cond := by
  unfold sieCap2 pcIs2 instr2
  iintro ⟨%Hb, Hm, Hn⟩ Hp %Hins Hcont
  subst Hb
  obtain ⟨_, Hins⟩ := Hins
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal2
  iintro %s %m' %n' %pc' %C %Hcur Hm' Hn' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2 h3
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  iapply (XFenceSW σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (AxLeafS4.Hmid0 i G) s rs k pc w32 false HRet Hctrl HPC Htx Hsf Hdec (Hb0 i cpu G rs k))
  iintro %t' %rs' %ib' %k' %Hgood %Hag %_
  obtain ⟨Hc', HPC', Hg'⟩ := Hgood
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 4#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur2Keep cid cpu T satp0 m pc rs t' rs' ib' k' C Hc' (by rw [HPC']; rfl) Hg' Hag
    Htp Hspx Hrel
  iapply Hcont $$ [Hm Hn] Hp %_ %m %n %(pc + 4#64) %C %Hcur' Hm' Hn' Hp' HC
  isplitr
  · ipureintro; rfl
  · isplitl [Hm]
    · iexact Hm
    · iexact Hn

include hmode hasid hppn CondAnd CondGate Htext Hflow Hloc HG Hdmap HnoSplitReg amoRule
  amoRdFlow in
/-- Rocq `wp_amoswap_c`. -/
theorem wpAmoswapC (pc : BitVec 64) (rd rs2 rs1 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) (Post : BitVec 32 → IProp GF) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ sieCap2 (GF := GF) γm γn cid m n b p -∗
      pcIs2 (GF := GF) γp pc -∗
      instr2 (GF := GF) σi T satp0 pc false
        (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)) -∗
      amoRes (rget cid m rs1 + zeros (n := 64)) (AxLeafS4.amoswapStored (rget cid m rs2)) Post -∗
      (∀ w : BitVec 32,
        wpNext b p cid (fun cpu' => iprop(
          sieCap2 γm γn cpu' (m.set rd (AxLeafS4.amoswapLoaded w)) n b p -∗
          pcIs2 γp (pc + 4#64) -∗
          Post w -∗
          goal2 i cid cpu γm γp γn T satp0 Cond))) -∗
      goal2 i cid cpu γm γp γn T satp0 Cond := by
  intro Hrd Hrdok
  generalize Hpa0 : rget cid m rs1 + zeros (n := 64) = pa
  unfold sieCap2 pcIs2 instr2
  iintro ⟨%Hb, Hm, Hn⟩ Hp %Hins Hres Hcont
  subst Hb
  obtain ⟨_, Hins⟩ := Hins
  unfold goal2
  iintro %s %m' %n' %pc' %C %Hcur Hm' Hn' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2 h3
  iapply (CondGate s C (gateOf cid cpu σi T satp0 m pc s C _ Hcur Hins trivial)) $$ HC
  iintro %HCC
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  have Hr := Hrel HCC
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hamo := amoRule pa (AxLeafS4.amoswapStored (rget cid m rs2)) Post $$ Hres
  icases Hamo with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + zeros (n := 64) := by
    rw [← Hpa0, gprValRel cid m rs rs1 Hr]
  iapply (XAmoswapS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (AxLeafS4.Hmid0 i G) (AxLeafS4.dk (paZ pa) 4)
    (fun k data => iprop(⌜data = AxDataX.wrb 4 (AxLeafS4.amoswapStored (rget cid m rs2))⌝ -∗
      AmoOut k pa (AxLeafS4.amoswapStored (rget cid m rs2)) Post))
    (dkNosplit i damo HnoSplitReg _ _ Hdr) s rs k pc w32 true rs2 rs1 rd pa pa HRet Hctrl HPC
    Htx Hsf Hdec Hrd Hva (Hdmap _ pa 4 (Or.inr Hdr)) ⟨rfl, rfl⟩ (Hb0 i cpu G rs k)) $$ F
  iintro %vs %t' %rs' %ib' %k' %Hlen %Hgood %Hag Hout
  obtain ⟨Hc', HPC', Hg'⟩ := Hgood
  icases Hout with ⟨%kd, Ho⟩
  ihave Ho := Ho $$ %(by rw [gprValRel cid m rs rs2 Hr]; rfl)
  ihave Hrf := amoRdFlow kd pa _ Post vs Hlen $$ Ho
  icases Hrf with ⟨%w, #Hce, HP⟩
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd (AxLeafS4.amoswapLoaded w)) γm m m $$ Hm Hm'
    with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 4#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  ihave Hcont := Hcont $$ %w
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  have Hcur' := cur2Upd cid cpu T satp0 m pc rs t' rs' ib' k' rd (amoLdv 4 vs)
    (AxLeafS4.amoswapLoaded w) C (C ∧ amoLdv 4 vs = AxLeafS4.amoswapLoaded w) Hrd Hrdok Hc'
    (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hrel (fun h => h)
  ihave Hc2 := CondAnd _ _ $$ HC Hce
  iapply Hcont $$ [Hm Hn] Hp HP %_ %(m.set rd (AxLeafS4.amoswapLoaded w)) %n %(pc + 4#64)
    %(C ∧ amoLdv 4 vs = AxLeafS4.amoswapLoaded w) %Hcur' Hm' Hn' Hp' Hc2
  isplitr
  · ipureintro; rfl
  · isplitl [Hm]
    · iexact Hm
    · iexact Hn

end surf2

/-! # 4. The `Cond` laws exclude `Cond := False` and are satisfiable -/

section condLaws
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Rocq `Cond_false_not_intro`. -/
theorem CondFalseNotIntro :
    ¬ (∀ C : Prop, (iprop(⌜C⌝) : IProp GF) ⊢ (fun _ : Prop => (iprop(False) : IProp GF)) C) := by
  intro Hi
  exact Iris.pure_soundness (PROP := IProp GF) (φ := False)
    ((pure_intro trivial).trans ((Hi True).trans false_elim))

/-- Rocq `CondP`. -/
def AxLeafS4.CondP (C : Prop) : IProp GF := iprop(⌜C⌝)

/-- (Lean-only) Rocq's `apply _` on `Persistent (CondP C)`. -/
instance AxLeafS4.condPPers (C : Prop) : Persistent (AxLeafS4.CondP (GF := GF) C) := by
  unfold AxLeafS4.CondP; infer_instance

/-- Rocq `Cond_laws_model`. -/
theorem CondLawsModel (i : Agent) :
    (∀ C, AxLeafS4.CondP (GF := GF) C ⊢ <pers> AxLeafS4.CondP C) ∧
    (∀ C1 C2, ⊢ AxLeafS4.CondP (GF := GF) C1 -∗ AxLeafS4.CondP C2 -∗ AxLeafS4.CondP (C1 ∧ C2)) ∧
    (∀ C1 C2 : Prop, (C1 → C2) → ⊢ AxLeafS4.CondP (GF := GF) C1 -∗ AxLeafS4.CondP C2) ∧
    (∀ C : Prop, (iprop(⌜C⌝) : IProp GF) ⊢ AxLeafS4.CondP C) ∧
    (∀ C (Φ : Athread → IProp GF) s, ⊢ AxLeafS4.CondP C -∗
      postLifting (fun s' => iprop(⌜C⌝ -∗ Φ s')) i s -∗ postLifting Φ i s) := by
  refine ⟨fun C => (AxLeafS4.condPPers C).persistent, ?_, ?_, fun _ => .rfl, ?_⟩
  · intro C1 C2
    unfold AxLeafS4.CondP
    iintro %H1 %H2
    ipureintro
    exact ⟨H1, H2⟩
  · intro C1 C2 Himp
    unfold AxLeafS4.CondP
    iintro %H1
    ipureintro
    exact Himp H1
  · intro C Φ s
    unfold AxLeafS4.CondP postLifting
    iintro %HC H %na Hna
    imod H $$ %na Hna with ⟨Hna, H⟩
    imodintro
    iframe Hna
    iintro Hm
    ihave H := H $$ Hm
    inext
    imod H
    imodintro
    iapply H
    ipureintro
    exact HC

end condLaws

end Weak
