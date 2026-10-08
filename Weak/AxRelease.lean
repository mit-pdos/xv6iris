/-
Weak: **SURFACE v4** — surface v3 (`AxCondM3`) plus a STATIC EXACT-REGISTER MAP, and the
three lock-word leaves of xv6's `release` (sd / fence / sw) WITHOUT the address gate
`CondGate3`, plus the compressed frame / register leaves (AxSL tier).

Rocq: `iris/AxRelease.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE SURFACE.  `cur4 m pc s C` = `AxCondM3.cur3` plus
  `∀ r, Ex pc r → phys5 rs r = rget m r`       (UNCONDITIONAL)
where `Ex : pc → reg → Prop` is a section parameter: a static "exact-register" annotation of
the text (a dataflow fact: which registers' logical values are KNOWN without any
annotation-backed condition at that pc).  sp / tp stay exact as in v3.  The instruction fact
`instr4` adds two TEXT facts about `Ex` at each pc:
  `exBase` — a load / store / AMO's base (and the AMO's data) register is exact (`exactAt` =
             sp or `Ex pc`);
  `exOk`   — the exact set at the sequential successor is justified (`exSrc`: an untouched
             register exact here, or the written `rd` with an exact value — the AMO's rd (its
             read value is pinned: AxCondM2), c.mv / addi of an exact source; a LOAD's rd is
             NEVER exact: its value is demonic).
`instr4`'s compressed arm carries the REAL 2-byte decode fact (`AxSymMem2.textOkM`: text
word, compressed decode, ExecuteAs) — so the compressed WPd leaves (over AxRelease2) can be
built over it.  `cap4` = v3's cap plus a FREE-STACK resource `SF (m sp) n` (a section
parameter; AxRelease2 (Rocq) instantiates it with the release interface's `stack_own` so the
push / pop leaves can hand out / take back slots).

LEAVES (all over the real X bridges, no premised certificate): 4-byte `wpStoreC4` /
`wpFenceC4` / `wpAmoswapC4` (AxLeafS2 / AxCondM2); compressed `wpCmvC4` / `wpCaddi4spnC4` /
`wpCaddiSpPushC4` / `wpCaddi16spPopC4` (engine `wpGprWriteC4` over
`AxSpineOk5.XGprWriteHoldsT` at `SpineOkTSW`) and `wpCsdspC4` / `wpCldspC4` (over
AxRelease2's 2-byte bridge `XStoreS2` / `XLoadS2`); the stack words' protocol rules `stRule`
/ `ldRule` and `SFPush` / `SFPop` are section premises of the frame leaves.  THE GATE IS GONE
from `wpStoreC4` / `wpFenceC4` / `wpAmoswapC4`: a data access whose base register is exact
needs no `Cond C ⇒ ⌜C⌝`.  Where the gate went (Rocq AxRelease4): the exactness of s1 at
release+0x12 / +0x1a is an obligation of whoever establishes `goal4` at release+0x10 — the
callee slot (holding's return); holding RELOADS s1 from its frame (holding+0x26 `c.ldsp s1`),
so at the WPd level s1 is exact there only through a ctrl gate at holding's `c.ret`.

KERNEL CROSS-CHECK (Xv6/KernelImage.lean): this file states no kernel word (all leaves are
generic in pc / registers / immediates; the only fixed instruction is AxCondM3's
`fenceRwWIns` = `fence rw,w`, word 0x0310000f at release+0x16 = 0x80000cf6).  The header's
offsets agree with the Lean image: release = 0x80000ce0, +0x10 `beqz a0` (0x80000cf0), +0x12
`sd zero,16(s1)`, +0x16 `fence rw,w`, +0x1a `sw zero,0(s1)`; holding = 0x80000bf2, +0x26
`ld s1,8(sp)` (0x80000c18, a c.ldsp).

## Deviations from Rocq

1. O2 STAGE C (as AxSymMem3 deviation 1 / AxRelease2 deviation 1): `ldRule` deposits only
   `⌜dreg (paZ pa) 8⌝` (Rocq: `∧ ¬ ax_text (uint pa)`; there is no `ax_text`), and
   `wpCldspC4`'s local fact `Hnt` (`0 < n ∧ ¬ ax_text a`, fed to `X_load_S2`'s dropped
   `Hntext`) is gone.  `wpGprWriteC4` no longer uses `Hloc` (`XGprWriteHoldsT` takes only
   `Hsp Htext Hflow`).
2. Q7 (as AxCondM3 deviation 1): `insAt3` carries `sfAnnB 32 w32 = false`.
3. TYPES / SPELLING as AxCondM3 deviation 2 and AxSymMem3 deviation 2: `regfile` ↦ `RegMap`,
   `rget m r` ↦ `rget cid m r` (explicit SC hart `cid`), `m !!! Regidx csp_rs1` ↦ `m 2#5`,
   `<[Regidx rd := regval_into_reg v]> m` ↦ `m.set rd v`, `Rtp` ↦ `4#5`, `csp_rs1` ↦ `2#5`,
   `uint r = 0` ↦ `r.toNat = 0`, `register_lookup PC rs` ↦ `rs .PC`, `uint pa` ↦ `paZ pa`,
   `Z.to_nat wd` ↦ `wd : Nat`, `zero_reg` ↦ `0#64`, `add_vec_int pc (if is_rvc then 2 else
   4)` ↦ `pc + instrLen is_rvc` (`pc + 4#64` / `pc + 2#64` at a fixed width),
   `concat_vec uimm ('b"000")` ↦ `uimm +++ 0b000#3`, `ghost_var γ (1/2)` ↦
   `ghost_var γ (.own (1 : Qp).half)`, `WPd s @ MaybeStuck; i {{ Φ0 }}` ↦
   `wpd .MaybeStuck i s Φ0`.  `Regidx a = Regidx b` / `≠` between plain registers is stated
   on the 5-bit indices (`a = b`, `a ≠ b`) in `exactAt`, `rgetInsNe`/`rgetInsEq`,
   `cur4Write`, `rdOkSpNe`, `sfKeep` and `wpGprWriteC4` (`Regidx` is injective); `srcOk`
   keeps Rocq's `Regidx` form (as AxCondM3's `baseOk3`).  The statements' `let`s are inlined.
   Section variables are explicit arguments of each declaration that uses them; the
   iProp-valued Rocq premises (`Hrule`, `amo_rule3`, `ld_rule`, `st_rule`, `Cond_and`,
   `SF_push`, `SF_pop`) are entailments.
4. Lean's `rget` reads x0 as zero (Rocq's does not special-case x0), so `rgetInsNe` /
   `rgetInsEq` are proved through `AxReuseProbe2.rgetUpd`, and `rgetInsEq` takes
   `rd.toNat ≠ 0` (every use has it).
5. The engine `wpGprWriteC4`'s SC certificate premise is AxSymMem3's form (`s_pc.gpr rsa =
   rget cid m' rsa` for Rocq's `(if uint rsa = 0 then zero_reg else …) = rget m' rsa`;
   `exec (execute base) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd (wval m'))`).
6. The derived leaves (`wpCmvC4` …) do not destructure `cap4`'s `b = false` (Rocq: `subst b`
   + `wp_next_off` twice): they hand `cap4` to the engine whole and re-shape the continuation
   by `wpNext_mono`.  `rdOk` is MachCSL's (three conjuncts; Rocq's `rd_ok` has the last two).
7. Rocq's `sext9_12_64` (KernelRvcDecode, SC) is the Lean-only `AxRelease.sext91264`.
   `pa_stk` is `Weak.paStk` (WkStackOwn).

**Rocq → Lean name map.**  `exact_at` `exactAt`, `ex_base` `exBase`, `ex_src` `exSrc`,
`ex_ok` `exOk`, `src_ok` `AxRelease.srcOk` (duplicated name), `cur4` `cur4`, `Goal4` `goal4`,
`cap4` `cap4`, `pc_is4` `pcIs4`, `instr4` `instr4`, `instr4_nrvc` `instr4Nrvc`, `dk4_nosplit`
`dk4Nosplit`, `exact_phys` `exactPhys`, `cur4_keep` `cur4Keep`, `rget_ins_ne` `rgetInsNe`,
`rget_ins_eq` `rgetInsEq`, `cur4_upd` `cur4Upd`, `wp_store_c4` `wpStoreC4`, `wp_fence_c4`
`wpFenceC4`, `wp_amoswap_c4` `wpAmoswapC4`, `cur4_write` `cur4Write`, `wp_gpr_write_c4`
`wpGprWriteC4`, `rd_ok_sp_ne` `rdOkSpNe`, `sf_keep` `sfKeep`, `wp_cmv_c4` `wpCmvC4`,
`wp_caddi4spn_c4` `wpCaddi4spnC4`, `uint_csp_ne0` `uintCspNe0`, `sp_write_WE` `spWriteWE`,
`sp_write_cert` `spWriteCert`, `sp_write_ex` `spWriteEx`, `wp_caddi_sp_push_c4`
`wpCaddiSpPushC4`, `wp_caddi16sp_pop_c4` `wpCaddi16spPopC4`, `sp_pa` `spPa`, `wp_csdsp_c4`
`wpCsdspC4`, `wp_cldsp_c4` `wpCldspC4`.  Section parameters: `amo_res` `amoRes`, `amo_rule3`
`amoRule3`, `stack_own` `stackOwn`, `SF_push` `SFPush`, `SF_pop` `SFPop`, `ld_rule` `ldRule`,
`st_rule` `stRule`, `Cond_and` `CondAnd`, `HnoRmw_reg` `HnoRmwReg`, `HnoSplit_reg`
`HnoSplitReg`, others unchanged.  Lean-only (file-qualified): `AxRelease.sext91264`.

**Dropped:** nothing (Rocq 35 definitions/lemmas; Lean 35 + 1).  **Not ported:** the Ltac
`open_goal4` (inlined), the section notations `img` / `CK` (written out) and the
`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCondM3
import Weak.AxRelease2
import Weak.AxSpineOk5
import Weak.WkStackOwn

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! ## The exact-register text annotation -/

/-- Rocq `exact_at`: sp, or exact by the annotation. -/
def exactAt (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (r : BitVec 5) : Prop :=
  r = 2#5 ∨ Ex pc r

/-- Rocq `ex_base`: a data access's base (and an AMO's / a store's data) register is exact. -/
def exBase (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) : Prop :=
  match ins with
  | .STORE (_, .Regidx s2, .Regidx b, _) =>
      exactAt Ex pc b ∧ (exactAt Ex pc s2 ∨ (is_rvc = false ∧ s2.toNat = 0))
  | .LOAD (_, .Regidx b, _, _, _) => exactAt Ex pc b
  | .AMO (_, _, _, .Regidx s2, .Regidx b, _, _) => exactAt Ex pc b ∧ exactAt Ex pc s2
  | _ => True

/-- Rocq `ex_src`: why register `r` may be exact after `ins`. -/
def exSrc (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (ins : instruction)
    (r : BitVec 5) : Prop :=
  match ins with
  | .STORE _ => Ex pc r
  | .FENCE _ => Ex pc r
  | .AMO (_, _, _, _, _, _, .Regidx d) => Ex pc r ∨ r = d
  | .LOAD (_, _, .Regidx d, _, _) => Ex pc r ∧ r ≠ d
  | .RTYPE (.Regidx s2, .Regidx s1, .Regidx d, .ADD) =>
      (Ex pc r ∧ r ≠ d) ∨ (r = d ∧ s1.toNat = 0 ∧ exactAt Ex pc s2)
  | .ITYPE (_, .Regidx s1, .Regidx d, .ADDI) => (Ex pc r ∧ r ≠ d) ∨ (r = d ∧ exactAt Ex pc s1)
  | .JAL _ => True
  | .JALR _ => True
  | .BTYPE _ => True
  | _ => False

/-- Rocq `ex_ok`: the exact set at the sequential successor is justified. -/
def exOk (Ex : BitVec 64 → BitVec 5 → Prop) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) : Prop :=
  ∀ r, Ex (pc + instrLen is_rvc) r → exSrc Ex pc ins r

/-- Rocq `src_ok`: the source registers a leaf reads through `rget` are not tp. -/
def AxRelease.srcOk (ins : instruction) : Prop :=
  match ins with
  | .STORE (_, .Regidx s2, _, _) => regidx.Regidx s2 ≠ regidx.Regidx 4#5
  | .RTYPE (.Regidx s2, _, _, _) => regidx.Regidx s2 ≠ regidx.Regidx 4#5
  | _ => True

/-- (Lean-only; Rocq `sext9_12_64`) a 9-bit zero-extended offset sign-extends as it
zero-extends. -/
theorem AxRelease.sext91264 (uimm : BitVec 6) :
    sign_extend (m := 64) (zero_extend (m := 12) (uimm +++ 0b000#3)) =
      zero_extend (m := 64) (uimm +++ 0b000#3) := by
  simp only [sign_extend, zero_extend, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend]
  bv_decide

section surf4
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat]
variable (i : Agent) (cid cpu : CPU) (γm γp γn : GName)
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)

variable (Armed : BitVec 64 → Prop)
variable (Ex : BitVec 64 → BitVec 5 → Prop)
variable (SF : BitVec 64 → Nat → IProp GF)

/-! ## The surface -/

def cur4 (m : RegMap) (pc : BitVec 64) (s : Athread) (C : Prop) : Prop :=
  ∃ rs k, RetX cpu rs k s ∧ ctrlOkSW T satp0 rs ∧ rs .PC = pc ∧
    phys5 rs 4#5 = rget cid m 4#5 ∧ phys5 rs 2#5 = rget cid m 2#5 ∧
    (∀ r, Ex pc r → phys5 rs r = rget cid m r) ∧
    (C → gprRel cid m rs)

variable (Cond : Prop → IProp GF)

def goal4 : IProp GF :=
  iprop(∀ (s : Athread) (m : RegMap) (n : Nat) (pc : BitVec 64) (r : Bool) (C : Prop),
    ⌜cur4 cid cpu T satp0 Ex m pc s C⌝ -∗
    ghost_var γm (.own (1 : Qp).half) m -∗ ghost_var γn (.own (1 : Qp).half) n -∗
    ghost_var γp (.own (1 : Qp).half) (pc, r) -∗ Cond C -∗
    wpd .MaybeStuck i s (Φ0 (GF := GF)))

def cap4 (_cid0 : CPU) (m : RegMap) (n : Nat) (b : Bool) (_p : BitVec 64) : IProp GF :=
  iprop(⌜b = false⌝ ∗ ghost_var γm (.own (1 : Qp).half) m ∗
    ghost_var γn (.own (1 : Qp).half) n ∗ SF (m 2#5) n)

def pcIs4 (pc : BitVec 64) : IProp GF :=
  iprop(∃ r : Bool, ghost_var γp (.own (1 : Qp).half) (pc, r) ∗ ⌜Armed pc → r = true⌝)

/-- The instruction fact: v3's, a REAL compressed arm, and the two exact-map text facts. -/
def instr4 (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(⌜((is_rvc = false ∧ insAt3 σi T satp0 pc ins ∧ (Armed (pc + 4#64) → ins = fenceRwWIns)) ∨
      (is_rvc = true ∧ textOkM (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) pc true ins ∧
        (isDmem3 ins ∨ rf0 (execute ins)) ∧ ¬ Armed (pc + 2#64))) ∧
     (isSwz ins → Armed pc) ∧ (baseOk3 ins ∧ AxRelease.srcOk ins) ∧ exBase Ex pc is_rvc ins ∧
     exOk Ex pc is_rvc ins⌝)

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
theorem instr4Nrvc (pc : BitVec 64) (ins : instruction) :
    instr4 (GF := GF) σi T satp0 Armed Ex pc false ins ⊢
      ⌜insAt3 σi T satp0 pc ins ∧ (Armed (pc + 4#64) → ins = fenceRwWIns) ∧
        (isSwz ins → Armed pc) ∧ (baseOk3 ins ∧ AxRelease.srcOk ins) ∧
        exBase Ex pc false ins ∧ exOk Ex pc false ins⌝ := by
  unfold instr4
  refine pure_mono ?_
  rintro ⟨H | ⟨h, _⟩, h3, h4, h5, h6⟩
  · exact ⟨H.2.1, H.2.2, h3, h4, h5, h6⟩
  · exact nomatch h

/- bridge instance premises (as AxCondM3) — NO gate -/
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

variable (dreg damo : Int → Nat → Prop)
variable (Hdmap : ∀ (acc : MemoryAccessType mem_payload) (va : BitVec 64) (w : Nat),
  dreg (paZ va) w ∨ damo (paZ va) w → dataAtS σi T acc va w va)
variable (HnoSplitReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ damo base n⌝)

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
include HnoSplitReg in
theorem dk4Nosplit (a : Int) (n : Nat) : damo a n → ∀ GD, rvwmoCatConsistent GD →
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

theorem exactPhys (m : RegMap) (pc : BitVec 64) (rs : RegFile) (r : BitVec 5) :
    phys5 rs 2#5 = rget cid m 2#5 → (∀ r, Ex pc r → phys5 rs r = rget cid m r) →
    exactAt Ex pc r → phys5 rs r = rget cid m r := by
  rintro Hsp Hex (rfl | E)
  · exact Hsp
  · exact Hex r E

theorem cur4Keep (m : RegMap) (pc : BitVec 64) (rs : RegFile) (t' : ExecSt) (rs' : RegFile)
    (ib' : Ibch) (k' : Nat) (C : Prop) (is_rvc : Bool) (ins : instruction) :
    ctrlOkSW T satp0 t'.regs → t'.regs .PC = pc + instrLen is_rvc →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget t'.regs r = uxaXget rs r) →
    regsAgree AxRunClose.pinReg rs' t'.regs →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 →
    (∀ r, Ex pc r → phys5 rs r = rget cid m r) →
    exOk Ex pc is_rvc ins → (∀ r, exSrc Ex pc ins r → Ex pc r) →
    (C → gprRel cid m rs) →
    cur4 cid cpu T satp0 Ex m (pc + instrLen is_rvc)
      ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ C := by
  intro Hc HPC Hg Hag Htp Hsp Hex Hok Hsrc Hrel
  have Hsame : ∀ r, phys5 t'.regs r = phys5 rs r := by
    intro r
    show uxaXget t'.regs r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hg r h0
  refine ⟨t'.regs, k', goodRetx3 cpu rs' t' ib' k' Hag, Hc, HPC, by rw [Hsame]; exact Htp,
    by rw [Hsame]; exact Hsp, ?_, ?_⟩
  · intro r Hr
    rw [Hsame]
    exact Hex r (Hsrc r (Hok r Hr))
  · intro HCC r
    exact (Hsame r).trans (Hrel HCC r)

theorem rgetInsNe (m : RegMap) (rd r : BitVec 5) (v : BitVec 64) :
    r ≠ 4#5 → r ≠ rd → rget cid (m.set rd v) r = rget cid m r := by
  intro Ht Hd
  by_cases h0 : r = 0#5
  · subst h0
    rw [rget_zero, rget_zero]
  · rw [rget_ne cid _ r h0 Ht, rget_ne cid _ r h0 Ht, RegMap.set_other _ _ _ _ Hd]

theorem rgetInsEq (m : RegMap) (rd : BitVec 5) (v : BitVec 64) :
    rd ≠ 4#5 → rd.toNat ≠ 0 → rget cid (m.set rd v) rd = v := by
  intro Ht H0
  rw [rgetUpd cid m rd rd v Ht H0, if_pos rfl]

/-- A register write of `rd` (the v3 `cur3Upd` plus the exact map): `Hex'` says which
registers are exact at the successor. -/
theorem cur4Upd (m : RegMap) (pc : BitVec 64) (rs : RegFile) (t' : ExecSt) (rs' : RegFile)
    (ib' : Ibch) (k' : Nat) (rd : BitVec 5) (val v : BitVec 64) (C C' : Prop)
    (is_rvc : Bool) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ctrlOkSW T satp0 t'.regs → t'.regs .PC = pc + instrLen is_rvc →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget t'.regs r = gprPost (some (rd, val)) rs r) →
    regsAgree AxRunClose.pinReg rs' t'.regs →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 →
    (∀ r, Ex pc r → phys5 rs r = rget cid m r) →
    (∀ r, Ex (pc + instrLen is_rvc) r → (Ex pc r ∧ r ≠ rd) ∨ (r = rd ∧ val = v)) →
    (C → gprRel cid m rs) →
    (C' → C ∧ val = v) →
    cur4 cid cpu T satp0 Ex (m.set rd v) (pc + instrLen is_rvc)
      ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ C' := by
  intro Hrd Hrdok Hc HPC Hg Hag Htp Hsp Hex Hex' Hrel HC'
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget t'.regs r = if r = rd then val else uxaXget rs r := fun r Hr => Hg r Hr
  have Hne_tp : (4#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.2 (uint5Inj _ _ E).symm
  have Hne_sp : (2#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.1 (uint5Inj _ _ E).symm
  refine ⟨t'.regs, k', goodRetx3 cpu rs' t' ib' k' Hag, Hc, HPC, ?_, ?_, ?_, ?_⟩
  · rw [phys5UpdNe rs t'.regs rd 4#5 _ Hg' Hne_tp, Htp, rget_tp, rget_tp]
  · rw [phys5UpdNe rs t'.regs rd 2#5 _ Hg' Hne_sp, Hsp,
      rget_ne cid _ 2#5 (by decide) (by decide), rget_ne cid _ 2#5 (by decide) (by decide),
      RegMap.set_other _ _ _ _ (fun e => Hrdok.2.1 e.symm)]
  · intro r Hr
    rcases Hex' r Hr with ⟨Hr0, Hne⟩ | ⟨rfl, Hv⟩
    · have Hne' : r.toNat ≠ rd.toNat := fun E => Hne (uint5Inj _ _ E)
      rw [phys5UpdNe rs t'.regs rd r _ Hg' Hne', Hex r Hr0,
        rgetUpd cid m rd r v Hrdok.2.2 Hrd, if_neg Hne]
    · rw [rgetInsEq cid m r v Hrdok.2.2 Hrd]
      show uxaXget t'.regs r = v
      rw [Hg' r Hrd, if_pos rfl, Hv]
  · intro HCC'
    obtain ⟨HCC, rfl⟩ := HC' HCC'
    exact gprRelUpd cid m rs t'.regs rd val (Hrel HCC) Hrd Hrdok.2.2 Hg'

/-! ## The leaves — NO gate -/

include hmode hasid hppn Htext Hflow Hloc HG Hdmap in
/-- Rocq `wp_store_c4`: a STORE whose base register is exact.  The rule gets the data fact
"the bytes are rs2's when rs2 is exact, zero when rs2 = x0". -/
theorem wpStoreC4 (pc : BitVec 64) (rs2 rs1 : BitVec 5) (imm : BitVec 12) (wd : Nat)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) (Pre Post : IProp GF) :
    vmemWidth wd → 1 ≤ wd ∧ wd ≤ 8 →
    (∀ c : WmClass, ⊢ ⌜Armed pc → c = .WCrel⌝ -∗ Pre -∗
      ⌜dreg (paZ (rget cid m rs1 + sign_extend (m := 64) imm)) wd⌝ ∗
      FstM rvwmoCatConsistent (dk3 (paZ (rget cid m rs1 + sign_extend (m := 64) imm)) wd) i
        (fun _ data => iprop(⌜(exactAt Ex pc rs2 → data = stBytes wd (rget cid m rs2)) ∧
          (rs2.toNat = 0 → data = stBytes wd 0#64)⌝ -∗ Post))) →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc false (.STORE (imm, .Regidx rs2, .Regidx rs1, wd)) -∗
      Pre -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗ pcIs4 γp Armed (pc + 4#64) -∗ Post -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hvw Hw Hrule
  generalize Hpa0 : rget cid m rs1 + sign_extend (m := 64) imm = pa at Hrule
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %Har⟩ Hi Hpre Hcont
  subst Hb
  ihave %Hi := instr4Nrvc σi T satp0 Armed Ex pc _ $$ Hi
  obtain ⟨Hins, Hnf, _, _, Hexb, Hexo⟩ := Hi
  obtain ⟨Hexb1, Hexb2⟩ := Hexb
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hpr := Hrule (wcls AxDataX.akPlain r0) $$
    %(fun Ha => by rw [Har Ha]; exact wclsArmed _ rfl) Hpre
  icases Hpr with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + sign_extend (m := 64) imm := by
    rw [← Hpa0, show gprVal rs rs1 = rget cid m rs1 from
      exactPhys cid Ex m pc rs rs1 Hspx Hex Hexb1]
  have HF : FstM rvwmoCatConsistent (dk3 (paZ pa) wd) i
        (fun _ data => iprop(⌜(exactAt Ex pc rs2 → data = stBytes wd (rget cid m rs2)) ∧
          (rs2.toNat = 0 → data = stBytes wd 0#64)⌝ -∗ Post)) ⊢
      Fst (dk3 (paZ pa) wd) i
        (fun _ data => iprop(⌜(exactAt Ex pc rs2 → data = stBytes wd (rget cid m rs2)) ∧
          (rs2.toNat = 0 → data = stBytes wd 0#64)⌝ -∗ Post)) := .rfl
  ihave F := HF $$ F
  iapply (XStoreS σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0
    (Hmid3 i G) (dk3 (paZ pa) wd) _ s rs k pc w32 imm rs2 rs1 wd pa pa r0 HRet Hctrl HPC Htx
    Hsf Hdec Hvw Hw Hva (Hdmap _ pa wd (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb3 i cpu G rs k)) $$ F
  iintro %t' %rs' %ib' %k' %HG' %Hag Hpt
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  icases Hpt with ⟨%kd, Hpt⟩
  have Hdat : (exactAt Ex pc rs2 → stBytes wd (gprVal rs rs2) = stBytes wd (rget cid m rs2)) ∧
      (rs2.toNat = 0 → stBytes wd (gprVal rs rs2) = stBytes wd 0#64) :=
    ⟨fun He => by
      rw [show gprVal rs rs2 = rget cid m rs2 from exactPhys cid Ex m pc rs rs2 Hspx Hex He],
     fun H0 => by
      show stBytes wd (uxaXget rs rs2) = _
      rw [AxReuseProbe2.uxaXgetZero rs rs2 H0]⟩
  ispecialize Hpt $$ %Hdat
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 4#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur4Keep cid cpu T satp0 Ex m pc rs t' rs' ib' k' C false _ Hc'
    (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hex Hexo (fun _ H => H) Hrel
  iapply Hcont $$ [Hm Hn HS] [Hp] Hpt %_ %m %n %(pc + 4#64) %false %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      have h := Hnf Ha
      unfold fenceRwWIns at h
      cases h

include hmode hasid hppn Htext Hflow Hloc HG in
/-- Rocq `wp_fence_c4`: `fence rw,w` arms the flag. -/
theorem wpFenceC4 (pc : BitVec 64) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗
      pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc false fenceRwWIns -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗
        pcIs4 γp Armed (pc + 4#64) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %_⟩ Hi Hcont
  subst Hb
  ihave %Hi := instr4Nrvc σi T satp0 Armed Ex pc _ $$ Hi
  obtain ⟨Hins, _, _, _, _, Hexo⟩ := Hi
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  iapply (XFenceSW σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0 (Hmid3 i G)
    s rs k pc w32 r0 HRet Hctrl HPC Htx Hsf Hdec (Hb3 i cpu G rs k))
  iintro %t' %rs' %ib' %k' %HG' %Hag %_
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 4#64, true) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur4Keep cid cpu T satp0 Ex m pc rs t' rs' ib' k' C false _ Hc'
    (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hex Hexo (fun _ H => H) Hrel
  iapply Hcont $$ [Hm Hn HS] [Hp] %_ %m %n %(pc + 4#64) %true %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists true
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      exact fun _ => rfl

/- `amoswap.w{.aq} rd, rs2, (rs1)` with exact rs1 / rs2: rd := the EXACT read value, and rd
becomes EXACT -/
variable (amoRes : PAddr → BitVec 32 → (BitVec 32 → IProp GF) → IProp GF)
variable (amoRule3 : ∀ pa wnew Post, ⊢ amoRes pa wnew Post -∗ ⌜damo (paZ pa) 4⌝ ∗
  FstM rvwmoCatConsistent (dk3 (paZ pa) 4) i
    (OutOfV i (fun _ ov data => iprop(⌜data = AxDataX.wrb 4 wnew⌝ -∗
      ∀ rvs, ⌜ov = some rvs⌝ -∗ Post (rrv 4 rvs)))))

include hmode hasid hppn Htext Hflow Hloc HG Hagree Hdmap HnoSplitReg amoRule3 in
/-- Rocq `wp_amoswap_c4`. -/
theorem wpAmoswapC4 (pc : BitVec 64) (aq : Bool) (rd rs2 rs1 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) (Post : BitVec 32 → IProp GF) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗
      pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc false
        (.AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd)) -∗
      amoRes (rget cid m rs1 + zeros (n := 64)) (AxCondM3.amoswapStored (rget cid m rs2)) Post -∗
      (∀ w : BitVec 32,
        wpNext b p cid (fun cpu' => iprop(
          cap4 γm γn SF cpu' (m.set rd (AxCondM3.amoswapLoaded w)) n b p -∗
          pcIs4 γp Armed (pc + 4#64) -∗
          Post w -∗
          goal4 i cid cpu γm γp γn T satp0 Ex Cond))) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hrd Hrdok
  generalize Hpa0 : rget cid m rs1 + zeros (n := 64) = pa
  unfold cap4 pcIs4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %_⟩ Hi Hres Hcont
  subst Hb
  ihave %Hi := instr4Nrvc σi T satp0 Armed Ex pc _ $$ Hi
  obtain ⟨Hins, Hnf, _, _, Hexb, Hexo⟩ := Hi
  obtain ⟨Hex1, Hex2⟩ := Hexb
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  obtain ⟨w32, Htx, Hsf, Hdec⟩ := Hins
  ihave Hpr := amoRule3 _ _ _ $$ Hres
  icases Hpr with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs rs1 + zeros (n := 64) := by
    rw [← Hpa0, show gprVal rs rs1 = rget cid m rs1 from
      exactPhys cid Ex m pc rs rs1 Hspx Hex Hex1]
  iapply (XAmoswapSP σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0 (Hmid3 i G)
    (dk3 (paZ pa) 4) _ Hagree (dk4Nosplit i damo HnoSplitReg _ _ Hdr)
    s rs k pc w32 aq rs2 rs1 rd pa pa HRet Hctrl HPC Htx Hsf Hdec Hrd
    Hva (Hdmap _ pa 4 (Or.inr Hdr)) ⟨rfl, rfl⟩ (Hb3 i cpu G rs k)) $$ F
  iintro %vs %t' %rs' %ib' %k' %Hlen %HG' %Hag ⟨%kd, Ho, #Hpin⟩
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  ihave Ho := amoOutPin i Hagree _ kd vs _ $$ Hpin Ho
  have Hst : AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)) =
      AxDataX.wrb 4 (AxCondM3.amoswapStored (rget cid m rs2)) := by
    rw [show gprVal rs rs2 = rget cid m rs2 from exactPhys cid Ex m pc rs rs2 Hspx Hex Hex2]
    rfl
  ispecialize Ho $$ %Hst %vs %rfl
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd (AxCondM3.amoswapLoaded (rrv 4 vs))) γm m m $$ Hm Hm'
    with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 4#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  ihave Hcont := Hcont $$ %(rrv 4 vs)
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  have Hsp_eq : (m.set rd (AxCondM3.amoswapLoaded (rrv 4 vs))) 2#5 = m 2#5 :=
    RegMap.set_other _ _ _ _ (fun e => Hrdok.2.1 e.symm)
  have HSe : SF (m 2#5) n ⊢ SF ((m.set rd (AxCondM3.amoswapLoaded (rrv 4 vs))) 2#5) n := by
    rw [Hsp_eq]
    try exact .rfl
  ihave HS := HSe $$ HS
  have Hex' : ∀ r, Ex (pc + instrLen false) r → (Ex pc r ∧ r ≠ rd) ∨
      (r = rd ∧ amoLdv 4 vs = AxCondM3.amoswapLoaded (rrv 4 vs)) := by
    intro r Hr
    have h : Ex pc r ∨ r = rd := Hexo r Hr
    rcases h with He | Ed
    · by_cases E : r = rd
      · exact Or.inr ⟨E, amoLdvLoaded vs⟩
      · exact Or.inl ⟨He, E⟩
    · exact Or.inr ⟨Ed, amoLdvLoaded vs⟩
  have Hcur' := cur4Upd cid cpu T satp0 Ex m pc rs t' rs' ib' k' rd (amoLdv 4 vs)
    (AxCondM3.amoswapLoaded (rrv 4 vs)) C C false Hrd Hrdok Hc' (by rw [HPC']; rfl) Hg' Hag
    Htp Hspx Hex Hex' Hrel (fun HC0 => ⟨HC0, amoLdvLoaded vs⟩)
  iapply Hcont $$ [Hm Hn HS] [Hp] Ho %_ %(m.set rd (AxCondM3.amoswapLoaded (rrv 4 vs))) %n
    %(pc + 4#64) %false %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      have h := Hnf Ha
      unfold fenceRwWIns at h
      cases h

/-! ## The COMPRESSED leaves (frame / register), over AxRelease2's 2-byte X bridge and
`AxSpineOk5.XGprWriteHoldsT` -/

theorem cur4Write (m : RegMap) (pc pc' : BitVec 64) (rs rs' : RegFile) (k' : Nat) (s' : Athread)
    (rd : BitVec 5) (val v : BitVec 64) (C C' : Prop) :
    RetX cpu rs' k' s' → ctrlOkSW T satp0 rs' → rs' .PC = pc' →
    rd.toNat ≠ 0 → rd ≠ 4#5 →
    (∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = if r = rd then val else uxaXget rs r) →
    phys5 rs 4#5 = rget cid m 4#5 → phys5 rs 2#5 = rget cid m 2#5 →
    (∀ r, Ex pc r → phys5 rs r = rget cid m r) →
    (rd = 2#5 → val = v) →
    (∀ r, Ex pc' r → (Ex pc r ∧ r ≠ rd) ∨ (r = rd ∧ val = v)) →
    (C → gprRel cid m rs) → (C' → C ∧ val = v) →
    cur4 cid cpu T satp0 Ex (m.set rd v) pc' s' C' := by
  intro HRet' Hc' HPC' Hrd Hrdtp Hg' Htp Hsp Hex Hsprd Hex' Hrel HC'
  have Hne_tp : (4#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdtp (uint5Inj _ _ E).symm
  have Hphys_rd : phys5 rs' rd = val := by
    show uxaXget rs' rd = val
    rw [Hg' rd Hrd, if_pos rfl]
  refine ⟨rs', k', HRet', Hc', HPC', ?_, ?_, ?_, ?_⟩
  · rw [phys5UpdNe rs rs' rd 4#5 _ Hg' Hne_tp, Htp, rget_tp, rget_tp]
  · by_cases E : rd = 2#5
    · subst E
      rw [rgetInsEq cid m 2#5 v (by decide) (by decide), Hphys_rd]
      exact Hsprd rfl
    · rw [phys5UpdNe rs rs' rd 2#5 _ Hg' (uintNeOfRegidx _ _ (fun h => E (by injection h with h; exact h.symm))),
        Hsp, rgetInsNe cid m rd 2#5 v (by decide) (fun h => E h.symm)]
  · intro r Hr
    rcases Hex' r Hr with ⟨Hr0, Hne⟩ | ⟨rfl, Hv⟩
    · have Hne' : r.toNat ≠ rd.toNat := fun E => Hne (uint5Inj _ _ E)
      rw [phys5UpdNe rs rs' rd r _ Hg' Hne', Hex r Hr0, rgetUpd cid m rd r v Hrdtp Hrd,
        if_neg Hne]
    · rw [rgetInsEq cid m r v Hrdtp Hrd, Hphys_rd, Hv]
  · intro HCC'
    obtain ⟨HCC, Hv⟩ := HC' HCC'
    subst Hv
    exact gprRelUpd cid m rs rs' rd val (Hrel HCC) Hrd Hrdtp Hg'

include hmode hasid hppn Htext Hflow in
/-- Rocq `wp_gpr_write_c4`: the compressed register-write ENGINE (AxSymMem3's `wpGprWriteC`
on v4): the written value depends only on EXACT registers. -/
theorem wpGprWriteC4 (pc : BitVec 64) (rd rsa rsb : BitVec 5) (base : instruction)
    (wval : RegMap → BitVec 64) (m : RegMap) (n n2 : Nat) (b : Bool) (p : BitVec 64)
    (Pre Post : IProp GF) :
    (∀ m1 m2 : RegMap, (∀ r, rget cid m1 r = rget cid m2 r) → wval m1 = wval m2) →
    ¬ isDmem3 base → rd.toNat ≠ 0 → rd ≠ 4#5 →
    (∀ r, Ex (pc + 2#64) r → (Ex pc r ∧ r ≠ rd) ∨
      (r = rd ∧ ∀ m1 : RegMap, (∀ r', exactAt Ex pc r' → rget cid m1 r' = rget cid m r') →
        wval m1 = wval m)) →
    (rd = 2#5 →
      ∀ m1 : RegMap, (∀ r', exactAt Ex pc r' → rget cid m1 r' = rget cid m r') →
        wval m1 = wval m) →
    (∀ (m' : RegMap) (s_pc : ExecSt),
       s_pc.regs .nextPC = pc + 2#64 →
       s_pc.gpr rsa = rget cid m' rsa →
       s_pc.gpr rsb = rget cid m' rsb →
       exec (execute base) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd (wval m'))) →
    (SF (m 2#5) n ∗ Pre ⊢ SF ((m.set rd (wval m)) 2#5) n2 ∗ Post) →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc true base -∗ Pre -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' (m.set rd (wval m)) n2 b p -∗ pcIs4 γp Armed (pc + 2#64) -∗ Post -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hwv Hnm Hrd Hrdtp Hex' HspE Hbexec HSF
  have HSFw : ⊢ SF (m 2#5) n -∗ Pre -∗ iprop(SF ((m.set rd (wval m)) 2#5) n2 ∗ Post) := by
    iintro HS Hpre
    iapply (entails_wand HSF)
    isplitl [HS]
    · iexact HS
    · iexact Hpre
  unfold cap4 pcIs4 instr4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %Har⟩ %Htx Hpre Hcont
  subst Hb
  obtain ⟨Harm, -, -, -, -⟩ := Htx
  rcases Harm with ⟨⟨⟩, -⟩ | ⟨-, Htm, Hrf, HnA⟩
  have Htd : textOkD (imgS σi) (ctrlOkSW T satp0) (textAtS σi T) pc true base := by
    obtain ⟨Hc, h, i0, Ha, Hd, He⟩ := Htm
    exact ⟨Hc, h, i0, Ha, Hd, He, Hrf.resolve_left Hnm⟩
  ihave HSP := HSFw $$ HS Hpre
  icases HSP with ⟨HS, Hpost⟩
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  have Htp' : phys5 rs 4#5 = hartId cid := Htp.trans (rget_tp cid m)
  have Hrelp := gprRelMphys cid rs Htp'
  have Hsrc : ∀ (s_pc : ExecSt) (r : BitVec 5), gprAgree s_pc.regs rs →
      s_pc.gpr r = rget cid (mphys rs) r := by
    intro s_pc r Hag
    rw [← Hrelp r]
    show uxaXget s_pc.regs r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hag r h0
  have HXi := XGprWriteHoldsT (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) Htext Hflow s rs k pc true base rd
    (wval (mphys rs)) HRet Hctrl HPC Htd Hrd
    (fun s_pc Hnpc Hag => Hbexec (mphys rs) s_pc Hnpc (Hsrc s_pc rsa Hag) (Hsrc s_pc rsb Hag))
  iapply HXi
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hgpr
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd (wval m)) γm m m $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves n2 γn n n $$ Hn Hn' with ⟨Hn, Hn'⟩
  imod ghost_var_update_halves (pc + 2#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have HWE : (∀ m1 : RegMap, (∀ r', exactAt Ex pc r' → rget cid m1 r' = rget cid m r') →
      wval m1 = wval m) → wval (mphys rs) = wval m := fun HW =>
    HW _ (fun r' Her => (Hrelp r').symm.trans (exactPhys cid Ex m pc rs r' Hspx Hex Her))
  have Hcur' := cur4Write cid cpu T satp0 Ex m pc (pc + 2#64) rs rs' k' s' rd (wval (mphys rs))
    (wval m) C C HRet' Hctrl' HPC' Hrd Hrdtp Hgpr Htp Hspx Hex (fun E => HWE (HspE E))
    (fun r Hr => by
      rcases Hex' r Hr with H1 | ⟨H2, H3⟩
      · exact Or.inl H1
      · exact Or.inr ⟨H2, HWE H3⟩)
    Hrel (fun HCC => ⟨HCC, Hwv _ _ (fun r => (Hrelp r).symm.trans (Hrel HCC r))⟩)
  iapply Hcont $$ [Hm Hn HS] [Hp] Hpost %_ %(m.set rd (wval m)) %n2 %(pc + 2#64) %false %C
    %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      exact absurd Ha HnA

theorem rdOkSpNe (rd : BitVec 5) : MachCSL.rdOk rd → rd ≠ 2#5 := fun h => h.2.1

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap]
  [GhostVarG GF (BitVec 64 × Bool)] [GhostVarG GF Nat] in
theorem sfKeep (m : RegMap) (rd : BitVec 5) (v : BitVec 64) (n : Nat) :
    rd ≠ 2#5 →
    SF (m 2#5) n ∗ emp ⊢ SF ((m.set rd v) 2#5) n ∗ emp := by
  intro Hne
  rw [RegMap.set_other _ _ _ _ (fun e => Hne e.symm)]
  try exact .rfl

include hmode hasid hppn Htext Hflow in
/-- Rocq `wp_cmv_c4`: `c.mv rd, rs2`. -/
theorem wpCmvC4 (pc : BitVec 64) (rd rs2 : BitVec 5) (m : RegMap) (n : Nat) (b : Bool)
    (p : BitVec 64) :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc true (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIs4 γp Armed (pc + 2#64) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hrd Hrdok
  have Hwv : ∀ m1 m2 : RegMap, (∀ r, rget cid m1 r = rget cid m2 r) →
      (fun m => 0#64 + rget cid m rs2) m1 = (fun m => 0#64 + rget cid m rs2) m2 := by
    intro m1 m2 Hm12
    show 0#64 + rget cid m1 rs2 = 0#64 + rget cid m2 rs2
    rw [Hm12]
  have Hbexec : ∀ (m' : RegMap) (s_pc : ExecSt), s_pc.regs .nextPC = pc + 2#64 →
      s_pc.gpr rs2 = rget cid m' rs2 → s_pc.gpr rs2 = rget cid m' rs2 →
      exec (execute (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD))) s_pc =
        some (RETIRE_SUCCESS, s_pc.setGpr rd ((fun m => 0#64 + rget cid m rs2) m')) := by
    intro m' s_pc _ Hva _
    show exec (execute_RTYPE (.Regidx rs2) (.Regidx 0#5) (.Regidx rd) .ADD) s_pc = _
    rw [execExecuteRTYPEADDGpr rs2 0#5 rd s_pc]
    unfold gprRdVal
    rw [Hva]
    rfl
  unfold instr4
  iintro Hc Hp %Hi Hk
  have Hexo := Hi.2.2.2.2
  have Hex' : ∀ r, Ex (pc + 2#64) r → (Ex pc r ∧ r ≠ rd) ∨
      (r = rd ∧ ∀ m1 : RegMap, (∀ r', exactAt Ex pc r' → rget cid m1 r' = rget cid m r') →
        (fun m => 0#64 + rget cid m rs2) m1 = (fun m => 0#64 + rget cid m rs2) m) := by
    intro r Hr
    have h : (Ex pc r ∧ r ≠ rd) ∨
        (r = rd ∧ (zero_extend (m := 5) 0b00#2 : BitVec 5).toNat = 0 ∧ exactAt Ex pc rs2) :=
      Hexo r Hr
    rcases h with H1 | ⟨H2, -, H3⟩
    · exact Or.inl H1
    · refine Or.inr ⟨H2, fun m1 Hm1 => ?_⟩
      show 0#64 + rget cid m1 rs2 = 0#64 + rget cid m rs2
      rw [Hm1 rs2 H3]
  iapply (wpGprWriteC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Armed Ex SF Cond Htext
    Hflow pc rd rs2 rs2 (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD))
    (fun m => 0#64 + rget cid m rs2) m n n b p iprop(emp) iprop(emp) Hwv (fun h => h) Hrd
    Hrdok.2.2 Hex' (fun E => absurd E (rdOkSpNe rd Hrdok)) Hbexec
    (sfKeep SF m rd _ n (rdOkSpNe rd Hrdok))) $$ Hc Hp [] [] [Hk]
  · unfold instr4
    ipureintro
    exact Hi
  · iempintro
  · iapply (wpNext_mono b p cid _ _) $$ Hk
    iintro %c Hk Hc Hp -
    iapply Hk $$ Hc Hp

include hmode hasid hppn Htext Hflow in
/-- Rocq `wp_caddi4spn_c4`: `c.addi4spn rd', sp, nzimm`. -/
theorem wpCaddi4spnC4 (pc : BitVec 64) (rdc : cregidx) (nzimm : BitVec 8) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    creg2reg_idx rdc = .Regidx rd → rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc true
        (.ITYPE (caddi4spnImm nzimm, sp, .Regidx rd, .ADDI)) -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' (m.set rd (m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm))) n b p -∗
        pcIs4 γp Armed (pc + 2#64) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro _ Hrd Hrdok
  have Hwv : ∀ m1 m2 : RegMap, (∀ r, rget cid m1 r = rget cid m2 r) →
      (fun m : RegMap => m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm)) m1 =
        (fun m : RegMap => m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm)) m2 := by
    intro m1 m2 Hm12
    show m1 2#5 + _ = m2 2#5 + _
    rw [← rget_ne cid m1 2#5 (by decide) (by decide), ← rget_ne cid m2 2#5 (by decide) (by decide),
      Hm12]
  have Hbexec : ∀ (m' : RegMap) (s_pc : ExecSt), s_pc.regs .nextPC = pc + 2#64 →
      s_pc.gpr 2#5 = rget cid m' 2#5 → s_pc.gpr 2#5 = rget cid m' 2#5 →
      exec (execute (.ITYPE (caddi4spnImm nzimm, sp, .Regidx rd, .ADDI))) s_pc =
        some (RETIRE_SUCCESS, s_pc.setGpr rd
          ((fun m : RegMap => m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm)) m')) := by
    intro m' s_pc _ Hva _
    show exec (execute (.ITYPE (caddi4spnImm nzimm, .Regidx 2#5, .Regidx rd, .ADDI))) s_pc = _
    rw [execExecuteITYPEADDIGpr 2#5 rd (caddi4spnImm nzimm) s_pc]
    unfold gprAddiVal
    rw [Hva, rget_ne cid m' 2#5 (by decide) (by decide)]
  unfold instr4
  iintro Hc Hp %Hi Hk
  have Hexo := Hi.2.2.2.2
  have Hex' : ∀ r, Ex (pc + 2#64) r → (Ex pc r ∧ r ≠ rd) ∨
      (r = rd ∧ ∀ m1 : RegMap, (∀ r', exactAt Ex pc r' → rget cid m1 r' = rget cid m r') →
        (fun m : RegMap => m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm)) m1 =
          (fun m : RegMap => m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm)) m) := by
    intro r Hr
    have h : (Ex pc r ∧ r ≠ rd) ∨ (r = rd ∧ exactAt Ex pc 2#5) := Hexo r Hr
    rcases h with H1 | ⟨H2, H3⟩
    · exact Or.inl H1
    · refine Or.inr ⟨H2, fun m1 Hm1 => ?_⟩
      show m1 2#5 + _ = m 2#5 + _
      rw [← rget_ne cid m1 2#5 (by decide) (by decide), ← rget_ne cid m 2#5 (by decide) (by decide),
        Hm1 2#5 H3]
  iapply (wpGprWriteC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Armed Ex SF Cond Htext
    Hflow pc rd 2#5 2#5 (.ITYPE (caddi4spnImm nzimm, sp, .Regidx rd, .ADDI))
    (fun m : RegMap => m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm)) m n n b p
    iprop(emp) iprop(emp) Hwv (fun h => h) Hrd Hrdok.2.2 Hex'
    (fun E => absurd E (rdOkSpNe rd Hrdok)) Hbexec
    (sfKeep SF m rd _ n (rdOkSpNe rd Hrdok))) $$ Hc Hp [] [] [Hk]
  · unfold instr4
    ipureintro
    exact Hi
  · iempintro
  · iapply (wpNext_mono b p cid _ _) $$ Hk
    iintro %c Hk Hc Hp -
    iapply Hk $$ Hc Hp

/- the free-stack resource's two laws (section premises; instantiated from `stack_own_slots`
in Rocq AxRelease3) -/
variable (stackOwn : PAddr → Nat → IProp GF)
variable (SFPush : ∀ sp0 n k, k ≤ n → SF sp0 n ⊢ stackOwn sp0 k ∗ SF (paStk sp0 k) (n - k))
variable (SFPop : ∀ sp1 n k, SF (paStk sp1 k) n ∗ stackOwn sp1 k ⊢ SF sp1 (n + k))

theorem uintCspNe0 : (2#5 : BitVec 5).toNat ≠ 0 := by decide

theorem spWriteWE (pc : BitVec 64) (m : RegMap) (imm : BitVec 12) :
    ∀ m1 : RegMap, (∀ r', exactAt Ex pc r' → rget cid m1 r' = rget cid m r') →
      (fun m0 : RegMap => m0 2#5 + sign_extend (m := 64) imm) m1 =
        (fun m0 : RegMap => m0 2#5 + sign_extend (m := 64) imm) m := by
  intro m1 Hm1
  show m1 2#5 + _ = m 2#5 + _
  rw [← rget_ne cid m1 2#5 (by decide) (by decide), ← rget_ne cid m 2#5 (by decide) (by decide),
    Hm1 2#5 (Or.inl rfl)]

theorem spWriteCert (pc : BitVec 64) (imm : BitVec 12) :
    ∀ (m' : RegMap) (s_pc : ExecSt),
      s_pc.regs .nextPC = pc + 2#64 →
      s_pc.gpr 2#5 = rget cid m' 2#5 →
      s_pc.gpr 2#5 = rget cid m' 2#5 →
      exec (execute (.ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI))) s_pc =
        some (RETIRE_SUCCESS, s_pc.setGpr 2#5
          ((fun m0 : RegMap => m0 2#5 + sign_extend (m := 64) imm) m')) := by
  intro m' s_pc _ Hva _
  rw [execExecuteITYPEADDIGpr 2#5 2#5 imm s_pc]
  unfold gprAddiVal
  rw [Hva, rget_ne cid m' 2#5 (by decide) (by decide)]

theorem spWriteEx (pc : BitVec 64) (m : RegMap) (imm : BitVec 12) :
    exOk Ex pc true (.ITYPE (imm, .Regidx 2#5, .Regidx 2#5, .ADDI)) →
    ∀ r, Ex (pc + 2#64) r → (Ex pc r ∧ r ≠ 2#5) ∨
      (r = 2#5 ∧ ∀ m1 : RegMap, (∀ r', exactAt Ex pc r' → rget cid m1 r' = rget cid m r') →
        (fun m0 : RegMap => m0 2#5 + sign_extend (m := 64) imm) m1 =
          (fun m0 : RegMap => m0 2#5 + sign_extend (m := 64) imm) m) := by
  intro Hexo r Hr
  have h : (Ex pc r ∧ r ≠ 2#5) ∨ (r = 2#5 ∧ exactAt Ex pc 2#5) := Hexo r Hr
  rcases h with H1 | ⟨H2, -⟩
  · exact Or.inl H1
  · exact Or.inr ⟨H2, spWriteWE cid Ex pc m imm⟩

include hmode hasid hppn Htext Hflow SFPush in
/-- Rocq `wp_caddi_sp_push_c4`: `c.addi sp, -imm` (the frame PUSH): `k` slots move from the
free stack to the caller-visible `stackOwn sp0 k`. -/
theorem wpCaddiSpPushC4 (pc : BitVec 64) (imm : BitVec 6) (m : RegMap) (n k : Nat) (b : Bool)
    (p : BitVec 64) :
    k ≤ n →
    m 2#5 + sign_extend (m := 64) (sign_extend (m := 12) imm) = paStk (m 2#5) k →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc true
        (.ITYPE (sign_extend (m := 12) imm, .Regidx 2#5, .Regidx 2#5, .ADDI)) -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu'
          (m.set 2#5 (m 2#5 + sign_extend (m := 64) (sign_extend (m := 12) imm))) (n - k) b p -∗
        stackOwn (m 2#5) k -∗ pcIs4 γp Armed (pc + 2#64) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hkn Hw
  have HSF : SF (m 2#5) n ∗ iprop(emp) ⊢
      SF ((m.set 2#5 ((fun m0 : RegMap => m0 2#5 + sign_extend (m := 64)
        (sign_extend (m := 12) imm)) m)) 2#5) (n - k) ∗ stackOwn (m 2#5) k := by
    dsimp only
    rw [RegMap.set_same, Hw]
    iintro ⟨HS, -⟩
    ihave HS := SFPush (m 2#5) n k Hkn $$ HS
    icases HS with ⟨Ho, HS⟩
    isplitl [HS]
    · iexact HS
    · iexact Ho
  unfold instr4
  iintro Hc Hp %Hi Hk
  have Hexo := Hi.2.2.2.2
  iapply (wpGprWriteC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Armed Ex SF Cond Htext
    Hflow pc 2#5 2#5 2#5 (.ITYPE (sign_extend (m := 12) imm, .Regidx 2#5, .Regidx 2#5, .ADDI))
    (fun m0 : RegMap => m0 2#5 + sign_extend (m := 64) (sign_extend (m := 12) imm)) m n (n - k)
    b p iprop(emp) (stackOwn (m 2#5) k)
    (fun m1 m2 Hm12 => by
      show m1 2#5 + _ = m2 2#5 + _
      rw [← rget_ne cid m1 2#5 (by decide) (by decide),
        ← rget_ne cid m2 2#5 (by decide) (by decide), Hm12])
    (fun h => h) uintCspNe0 (by decide) (spWriteEx cid Ex pc m _ Hexo)
    (fun _ => spWriteWE cid Ex pc m _) (spWriteCert cid pc _) HSF) $$ Hc Hp [] [] [Hk]
  · unfold instr4
    ipureintro
    exact Hi
  · iempintro
  · iapply (wpNext_mono b p cid _ _) $$ Hk
    iintro %c Hk Hc Hp Hs
    iapply Hk $$ Hc Hs Hp

include hmode hasid hppn Htext Hflow SFPop in
/-- Rocq `wp_caddi16sp_pop_c4`: `c.addi16sp sp, imm` (the frame POP): `k` slots return to the
free stack. -/
theorem wpCaddi16spPopC4 (pc : BitVec 64) (imm6 : BitVec 6) (m : RegMap) (n k : Nat) (b : Bool)
    (p : BitVec 64) :
    m 2#5 = paStk (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) k →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc true (.ITYPE (caddi16spImm imm6, sp, sp, .ADDI)) -∗
      stackOwn (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) k -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu'
          (m.set 2#5 (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6))) (n + k) b p -∗
        pcIs4 γp Armed (pc + 2#64) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hw
  have HSe : SF (m 2#5) n ⊢
      SF (paStk (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) k) n := by
    rw [← Hw]
    try exact .rfl
  have HSF : SF (m 2#5) n ∗ stackOwn (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) k ⊢
      SF ((m.set 2#5 ((fun m0 : RegMap => m0 2#5 + sign_extend (m := 64)
        (caddi16spImm imm6)) m)) 2#5) (n + k) ∗ iprop(emp) := by
    dsimp only
    rw [RegMap.set_same]
    iintro ⟨HS, Hs⟩
    ihave HS := HSe $$ HS
    isplitl
    · iapply SFPop
      isplitl [HS]
      · iexact HS
      · iexact Hs
    · iempintro
  unfold instr4
  iintro Hc Hp %Hi Hs Hk
  have Hexo := Hi.2.2.2.2
  iapply (wpGprWriteC4 i cid cpu γm γp γn σi T satp0 hmode hasid hppn Armed Ex SF Cond Htext
    Hflow pc 2#5 2#5 2#5 (.ITYPE (caddi16spImm imm6, sp, sp, .ADDI))
    (fun m0 : RegMap => m0 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) m n (n + k)
    b p (stackOwn (m 2#5 + sign_extend (m := 64) (caddi16spImm imm6)) k) iprop(emp)
    (fun m1 m2 Hm12 => by
      show m1 2#5 + _ = m2 2#5 + _
      rw [← rget_ne cid m1 2#5 (by decide) (by decide),
        ← rget_ne cid m2 2#5 (by decide) (by decide), Hm12])
    (fun h => h) uintCspNe0 (by decide) (spWriteEx cid Ex pc m _ Hexo)
    (fun _ => spWriteWE cid Ex pc m _) (spWriteCert cid pc _) HSF) $$ Hc Hp [] Hs [Hk]
  · unfold instr4
    ipureintro
    exact Hi
  · iapply (wpNext_mono b p cid _ _) $$ Hk
    iintro %c Hk Hc Hp -
    iapply Hk $$ Hc Hp

/- the stack words: an EXACT physical owned word and its protocol rules (the owned read
deposits "the value read is the owned one", returned as `Cond`; the owned write) -/
variable (wpt : PAddr → DFrac → BitVec 64 → IProp GF)
variable (ldRule : ∀ pa dq v, ⊢ wpt pa dq v -∗
  ⌜dreg (paZ pa) 8⌝ ∗
  Fld (dk3 (paZ pa) 8) i (fun _ vs => iprop(wpt pa dq v ∗ Cond (ldRes false 8 vs = v))))
variable (stRule : ∀ pa vold vnew, ⊢ wpt pa (.own 1) vold -∗
  ⌜dreg (paZ pa) 8⌝ ∗
  Fst (dk3 (paZ pa) 8) i (fun _ data => iprop(⌜data = stBytes 8 vnew⌝ -∗ wpt pa (.own 1) vnew)))
variable (CondAnd : ∀ C1 C2, ⊢ Cond C1 -∗ Cond C2 -∗ Cond (C1 ∧ C2))
variable (HnoRmwReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dreg base n⌝)

theorem spPa (m : RegMap) (rs : RegFile) (uimm : BitVec 6) :
    phys5 rs 2#5 = rget cid m 2#5 →
    m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) =
      gprVal rs 2#5 + sign_extend (m := 64) (zero_extend (m := 12) (uimm +++ 0b000#3)) := by
  intro Hsp
  rw [AxRelease.sext91264, show gprVal rs 2#5 = m 2#5 from
    Hsp.trans (rget_ne cid m 2#5 (by decide) (by decide))]

include hmode hasid hppn Htext Hflow Hloc HG Hdmap stRule in
/-- Rocq `wp_csdsp_c4`: `c.sdsp rs2, uimm(sp)` — rs2 exact (text fact). -/
theorem wpCsdspC4 (pc : BitVec 64) (uimm : BitVec 6) (rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (vold : BitVec 64) (b : Bool) (p : BitVec 64) :
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc true
        (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), .Regidx rs2, sp, 8)) -∗
      wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) vold -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' m n b p -∗ pcIs4 γp Armed (pc + 2#64) -∗
        wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) (rget cid m rs2) -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  generalize Hpa0 : m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = pa
  unfold cap4 pcIs4 instr4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %Har⟩ %Hi Hpt Hcont
  subst Hb
  obtain ⟨Harm, -, -, Hexb, Hexo⟩ := Hi
  rcases Harm with ⟨⟨⟩, -⟩ | ⟨-, Htm, -, HnA⟩
  have Hexb' : exactAt Ex pc 2#5 ∧ (exactAt Ex pc rs2 ∨ (true = false ∧ rs2.toNat = 0)) := Hexb
  rcases Hexb'.2 with Hex2 | ⟨⟨⟩, -⟩
  obtain ⟨-, h, i0, Hat, Hdec, Hexp⟩ := Htm
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  ihave Hst := stRule pa vold (rget cid m rs2) $$ Hpt
  icases Hst with ⟨%Hdr, F⟩
  have Hva : pa = gprVal rs 2#5 + sign_extend (m := 64) (zero_extend (m := 12) (uimm +++ 0b000#3)) := by
    rw [← Hpa0]
    exact spPa cid m rs uimm Hspx
  iapply (XStoreS2 σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0 (Hmid3 i G)
    (dk3 (paZ pa) 8) _ s rs k pc h i0 (zero_extend (m := 12) (uimm +++ 0b000#3)) rs2 2#5 8 pa pa
    r0 HRet Hctrl HPC Hat Hdec Hexp (Or.inr (Or.inr (Or.inr rfl))) ⟨by decide, by decide⟩ Hva
    (Hdmap _ pa 8 (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb3 i cpu G rs k)) $$ F
  iintro %t' %rs' %ib' %k' %HG' %Hag Hpt
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  icases Hpt with ⟨%kd, Hpt⟩
  have Hdat : stBytes 8 (gprVal rs rs2) = stBytes 8 (rget cid m rs2) := by
    rw [show gprVal rs rs2 = rget cid m rs2 from exactPhys cid Ex m pc rs rs2 Hspx Hex Hex2]
  ispecialize Hpt $$ %Hdat
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 2#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hcur' := cur4Keep cid cpu T satp0 Ex m pc rs t' rs' ib' k' C true _ Hc'
    (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hex Hexo (fun _ H => H) Hrel
  iapply Hcont $$ [Hm Hn HS] [Hp] Hpt %_ %m %n %(pc + 2#64) %false %C %Hcur' Hm' Hn' Hp' HC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      exact absurd Ha HnA

include hmode hasid hppn Htext Hflow Hloc HG Hdmap ldRule CondAnd HnoRmwReg in
/-- Rocq `wp_cldsp_c4`: `c.ldsp rd, uimm(sp)` — rd leaves the exact set; its value is known
under `C ∧ (loaded = v)`. -/
theorem wpCldspC4 (pc : BitVec 64) (uimm : BitVec 6) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (v : BitVec 64) (b : Bool) (p : BitVec 64) {dqm : DFrac} :
    rd.toNat ≠ 0 → MachCSL.rdOk rd →
    ⊢ cap4 (GF := GF) γm γn SF cid m n b p -∗ pcIs4 (GF := GF) γp Armed pc -∗
      instr4 (GF := GF) σi T satp0 Armed Ex pc true
        (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), sp, .Regidx rd, false, 8)) -∗
      wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) dqm v -∗
      wpNext b p cid (fun cpu' => iprop(
        cap4 γm γn SF cpu' (m.set rd v) n b p -∗ pcIs4 γp Armed (pc + 2#64) -∗
        wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) dqm v -∗
        goal4 i cid cpu γm γp γn T satp0 Ex Cond)) -∗
      goal4 i cid cpu γm γp γn T satp0 Ex Cond := by
  intro Hrd Hrdok
  generalize Hpa0 : m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = pa
  unfold cap4 pcIs4 instr4
  iintro ⟨%Hb, Hm, Hn, HS⟩ ⟨%r0, Hp, %Har⟩ %Hi Hpt Hcont
  subst Hb
  obtain ⟨Harm, -, -, -, Hexo⟩ := Hi
  rcases Harm with ⟨⟨⟩, -⟩ | ⟨-, Htm, -, HnA⟩
  obtain ⟨-, h, i0, Hat, Hdec, Hexp⟩ := Htm
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goal4
  iintro %s %m' %n' %pc' %r' %C %Hcur Hm' Hn' Hp' HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hn Hn'
  ihave %h3 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  injection h3 with h3a h3b
  subst h3a h3b
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hex, Hrel⟩ := Hcur
  ihave Hld := ldRule pa dqm v $$ Hpt
  icases Hld with ⟨%Hdr, F⟩
  have Hnr : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n →
        ¬ dk3 (paZ pa) 8 base n⌝ := by
    intro GD Hc
    refine (HnoRmwReg GD Hc).trans (pure_mono ?_)
    intro Hnr k0 lb aq rl base n0 Hlb Hid ⟨e1, e2⟩
    subst e1 e2
    exact Hnr k0 lb aq rl _ _ Hlb Hid Hdr
  have Hva : pa = gprVal rs 2#5 + sign_extend (m := 64) (zero_extend (m := 12) (uimm +++ 0b000#3)) := by
    rw [← Hpa0]
    exact spPa cid m rs uimm Hspx
  iapply (XLoadS2 σi T satp0 hmode hasid hppn i cpu Htext Hflow Hloc G HG Φ0 (Hmid3 i G)
    (dk3 (paZ pa) 8) _ Hnr s rs k pc h i0 (zero_extend (m := 12) (uimm +++ 0b000#3)) 2#5 rd
    false 8 pa pa HRet Hctrl HPC Hat Hdec Hexp Hrd (Or.inr (Or.inr (Or.inr rfl)))
    ⟨by decide, by decide⟩ Hva (Hdmap _ pa 8 (Or.inl Hdr)) ⟨rfl, rfl⟩ (Hb3 i cpu G rs k)) $$ F
  iintro %vs %t' %rs' %ib' %k' %Hlen %HG' %Hag Hout
  obtain ⟨Hc', HPC', Hg'⟩ := HG'
  icases Hout with ⟨%kd, Hpt, HCv⟩
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd v) γm m m $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 2#64, false) γp (pc, r0) (pc, r0) $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have HSe : SF (m 2#5) n ⊢ SF ((m.set rd v) 2#5) n := by
    rw [RegMap.set_other _ _ _ _ (fun e => rdOkSpNe rd Hrdok e.symm)]
    try exact .rfl
  ihave HS := HSe $$ HS
  have Hcur' := cur4Upd cid cpu T satp0 Ex m pc rs t' rs' ib' k' rd (ldRes false 8 vs) v C
    (C ∧ ldRes false 8 vs = v) true Hrd Hrdok Hc' (by rw [HPC']; rfl) Hg' Hag Htp Hspx Hex
    (fun r Hr => Or.inl (Hexo r Hr)) Hrel (fun h => h)
  ihave HCC := CondAnd _ _ $$ HC HCv
  iapply Hcont $$ [Hm Hn HS] [Hp] Hpt %_ %(m.set rd v) %n %(pc + 2#64) %false
    %(C ∧ ldRes false 8 vs = v) %Hcur' Hm' Hn' Hp' HCC
  · isplitr
    · ipureintro; rfl
    · isplitl [Hm]
      · iexact Hm
      · isplitl [Hn]
        · iexact Hn
        · iexact HS
  · iexists false
    isplitl [Hp]
    · iexact Hp
    · ipureintro
      intro Ha
      exact absurd Ha HnA

end surf4

end Weak
