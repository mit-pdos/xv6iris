/-
Weak: the CONDITIONAL register/memory surface and the SC leaf statements over it — the ALU
engine `wpGprWriteC` (over `XGprWrite`), `wpCmvC` / `wpCaddiwC` / `wpCaddi4spnC`, and the memory
leaves `wpCldspC` / `wpCsdspC` (over `AxSymMem2.XMemHolds`), all with the SC statements of
`AxReuseProbe2`'s surface unchanged.

Rocq: `iris/AxSymMem3.v` @ xxvzwolszwmp (an archive file ported because live files import it).

## The Rocq header, in substance

THE SURFACE.  A WPd read is demonic (∀ v, pinned to `graphValue`, never learned by the thread),
so after `c.ldsp rd` the thread's PHYSICAL register holds an unknown `ext vs` while the SC post
says `rd := v` (the owned value).  So the SC map `m` in the ghost mirror (AxReuseProbe2's
surface) becomes a LOGICAL map related to the physical registers CONDITIONALLY:
`curC m pc s C` := Ret boundary at `rs`, control ok, PC, sp and tp EXACT (unconditional),
`C → gprRel m rs` (conditional); the goal carries `Cond C` ("C is backed by annotations",
AxSymReg's provenance condition, one for the whole register file).  Memory gets the same
wrapper `wptC pa dq v := ∃ v' C, wpt pa dq v' ∗ Cond C ∗ ⌜C → v' = v⌝`.  `Cond` is ABSTRACT
(a persistent predicate with ∧/mono laws, section parameters).

ALU LEAVES ON CONDITIONAL SOURCES.  The engine takes the SC certificate for EVERY map `m'` and
applies it at the physical map `mphys rs`; `wval` must respect `rget`-equality.  Under `C` the
physical and logical results agree, so `C → gprRel` is preserved.

PREMISES (section parameters): the S-mode spine `SpineOkT` and the fetch-side `Htext`/`Hflow`;
the data region `dreg` (not an AMO target: `HnoRmwReg`); the per-family DATA certificates
`HxCldsp`/`HxCsdsp` (`ExecD` for c.ldsp / c.sdsp; see AxSymMem4 for their non-vacuity); the
PROTOCOL rules `ldRule`/`stRule` (owned read with deposit `ext8 vs = v'`, owned write); the
`Cond` laws.

## Deviations from Rocq

1. O2 STAGE C (as `AxSymMem` / `AxSymMem2` deviation 1): the section premise `Hloc` is DROPPED,
   and so is every `¬ ax_text` (there is no `ax_text`): `ldRule`/`stRule` deposit only
   `⌜dreg (za pa) 8⌝`; `pin_ok` (whose conclusion was `0 < n ∧ ¬ ax_text a`, used only for
   `X_mem_holds`'s dropped `Hntext` premise) is DROPPED.
2. Types/spelling as `AxReuseProbe2` (deviations 1-5): `phys5 rs r` is `uxaXget rs r` (an
   `abbrev`); `regfile` ↦ `RegMap`, `rget m r` ↦ `rget cid m r` (explicit SC hart `cid`, Rocq's
   implicit `CpuId`); `m !!! Regidx r` ↦ `m r`; `<[Regidx rd := v]> m` ↦ `m.set rd v`;
   `cid_word_of cpu_id` ↦ `hartId cid`; `csp_rs1` ↦ `2#5`, `Rtp` ↦ `4#5`; `IntrDefs.rd_ok` ↦
   `MachCSL.rdOk`; `wp_next` ↦ `wpNext` (continuation indexed by the resuming hart);
   `Z.eqb (uint r0) (uint rd)` ↦ `r0 = rd`; `add_vec_int pc 2` ↦ `pc + 2#64`;
   `concat_vec uimm ('b"000")` ↦ `uimm +++ 0b000#3`; `Arch.pa` ↦ `PAddr`; `dfrac` ↦ `DFrac`.
   The `let`s of the leaf statements (`imm`, `pa`, `wval`, `storeval`) are inlined.
3. `Cond_pers` is an instance binder `[∀ C, Persistent (Cond C)]`; `Cond_and`/`Cond_mono` are
   `⊢` entailments.  `wp_caddi4spn_c`'s `creg2reg_idx rdc = Regidx rd` premise is kept (unused,
   as in Rocq).
4. `X_mem_holds` is `AxSymMem2.XMemHolds` (premises `Hsp Htext Hflow HnoRmw G HG Φ Hmid Out`).
5. §3's REPLAY `wp_cpuid_c` (owner ruling Q17) is ported against the LEAN cpuid interface,
   `AxReuseProbe.AbsCpuid` (the Lean SC proof text `AxReuseProbe.wp_cpuid`), not Rocq's
   `AxReuseProbe.AbsCpuid.wp_cpuid_sconf` (which the Lean tree does not have).  `wpCpuidC c k
   hsie hK : AxReuseProbe.wp_cpuid_body Goal kctx pcIs c k hsie hK` at `Goal c := goalC` at SC
   hart `c` (hart-indexed, as the probe found), `kctx c k := AxSymMem3.kctxC γm kt c k`
   (`sieCapC` of `k.regs`/`k.avail`/`k.sie`/`k.proc`, plus the kernel text `kt`), `pcIs _ :=
   pcIsC`, `instr := instrC`.  Section premises, adapted: `kt` (persistent) as in Rocq;
   Rocq's `stack_own` + `stack_own_2_elim/intro` ↦ the one abstract `frame2C` (the Lean frame
   macros hide the stack cells, AxReuseProbe finding (3)); Rocq's push / two c.sdsp / two
   c.ldsp / pop / c.ret leaves ↦ the two Lean frame macros `wpPrologue2C` / `wpEpilogue2C`
   (premises, statements = AxReuseProbe's `wp_prologue2`/`wp_epilogue2` at this surface; so
   `wpCldspC`/`wpCsdspC` are not fed to the replay: the Lean proof text has no c.sdsp/c.ldsp
   step of its own); the ten `ci_*` ↦ `textInstrC` (AxReuseProbe's `textInstr` at `instrC`).
   The two ALU leaves the Lean text applies, `wp_s_add` (c.mv a0,tp) and `wp_s_addiw`
   (sext.w), are PROVED (`AxSymMem3.wpSAddC`/`wpSAddiwC`, any length/sources, via the engine
   `AxSymMem3.wpGprWriteK`) — but from `AxSymMem3.XGprWriteL`, the lifting premise X with the
   step's later exposed (`▷` before the continuation), because the Lean SC leaves carry `▷`
   before their continuation and `goalC` (a WPd) cannot absorb it; `XGprWriteL` implies
   `XGprWrite` (`AxSymMem3.xGprWriteOfL`).  Rocq's `wp_caddi4spn_c`/`wp_cmv_c`/`wp_caddiw_c`
   stay proved (above) at Rocq's `sieCapC m n b p` surface.
6. Performance (Lean-only): `wpCldspC` keeps the load's flow resource at type `Fld …` in the
   proof-mode context and converts XMemHolds' first premise outside proof mode
   (`AxSymMem3.fldToDRes`): a context hypothesis of type `DResM … true … .DPend` made every
   later proof-mode step cost minutes of kernel time (cross-file fact KERNEL BLOW-UP).  The
   module now elaborates in ~3 s.

**Rocq → Lean name map.**  `phys5` `phys5`, `mphys` `mphys`, `gpr_rel_mphys` `gprRelMphys`,
`gpr_rel_rget` `gprRelRget`, `phys5_gpr_rel` `phys5GprRel`, `uint_csp` `uintCsp`, `uint_tp`
`uintTp`, `csp_ne_tp` `cspNeTp`, `phys5_upd_ne` `phys5UpdNe`, `uint_ne_of_regidx`
`uintNeOfRegidx`, `cur_c` `curC`, `Goal_c` `goalC`, `sie_cap_c` `sieCapC`, `pc_is_c` `pcIsC`,
`is_mem` `AxSymMem3.isMem` (duplicated name), `instr_c` `instrC`, `instr_c_d` `instrCD`,
`wp_gpr_write_c` `wpGprWriteC`, `wp_cmv_c` `wpCmvC`, `wp_caddiw_c` `wpCaddiwC`, `pin`
`AxSymMem3.pin` (duplicated name), `wpt_c` `wptC`, `pin_normw` `pinNormw`, `sp_phys` `spPhys`,
`wp_cldsp_c` `wpCldspC`, `wp_csdsp_c` `wpCsdspC`, `wp_caddi4spn_c` `wpCaddi4spnC`, `wp_cpuid_c` `wpCpuidC`.  Section
parameters: `Cond_and` `CondAnd`, `Cond_mono` `CondMono`, `HnoRmw_reg` `HnoRmwReg`, `ld_rule`
`ldRule`, `st_rule` `stRule`, `Hx_cldsp` `HxCldsp`, `Hx_csdsp` `HxCsdsp`, `kt` `kt`; for the replay (deviation 5)
`stack_own`/`stack_own_2_elim`/`stack_own_2_intro` ↦ `frame2C`, `wp_caddi_sp_push_s_sconf_c` +
`wp_caddi_sp_pop_s_sconf_c` + `wp_cret_s_sconf_c` ↦ `wpPrologue2C`/`wpEpilogue2C`, `ci_*` ↦
`textInstrC`, new `HXL`.  Lean-only helpers (file-qualified): `AxSymMem3.gprAfterWrLoad`,
`fldToDRes`, `XGprWriteL`, `xGprWriteOfL`, `kctxC`, `wpNextSelf`, `wpGprWriteK`, `wpSAddC`,
`wpSAddiwC`, `kctxCKt`.

**Dropped:** `pin_ok` (deviation 1).  Rocq 29 definitions/lemmas, Lean 28 (+ 10 Lean-only
helpers).  **Not ported:** the `Print Assumptions`/`Check` lines (the lint's axiom check covers
them).
-/
import Weak.AxSymMem2
import Weak.ExecSC
import Weak.AxReuseProbe

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 0. The physical register file -/

/-- The physical value of GPR `r` (`x0` reads zero). -/
abbrev phys5 (rs : RegFile) (r : BitVec 5) : BitVec 64 := uxaXget rs r

/-- The physical register file as an SC map. -/
def mphys (rs : RegFile) : RegMap := fun r => phys5 rs r

theorem gprRelMphys (cid : CPU) (rs : RegFile) :
    phys5 rs 4#5 = hartId cid → gprRel cid (mphys rs) rs := by
  intro Htp r
  by_cases h4 : r = 4#5
  · subst h4
    rw [rget_tp]
    exact Htp
  · by_cases h0 : r = 0#5
    · subst h0
      rw [rget_zero]
      rfl
    · rw [rget_ne cid _ r h0 h4]
      rfl

theorem gprRelRget (cid : CPU) (m1 m2 : RegMap) (rs : RegFile) :
    gprRel cid m1 rs → gprRel cid m2 rs → ∀ r, rget cid m1 r = rget cid m2 r := by
  intro H1 H2 r
  rw [← H1 r, ← H2 r]

theorem phys5GprRel (cid : CPU) (m : RegMap) (rs : RegFile) (r : BitVec 5) :
    gprRel cid m rs → phys5 rs r = rget cid m r := fun H => H r

theorem uintCsp : (2#5 : BitVec 5).toNat = 2 := rfl

theorem uintTp : (4#5 : BitVec 5).toNat = 4 := rfl

theorem cspNeTp : regidx.Regidx 2#5 ≠ regidx.Regidx 4#5 := by
  intro h
  injection h with h
  exact absurd (congrArg BitVec.toNat h) (by decide)

/-- Physical GPR `r` after an update of `rd` only (X's post form). -/
theorem phys5UpdNe (rs rs' : RegFile) (rd r : BitVec 5) (v : BitVec 64) :
    (∀ r0 : BitVec 5, r0.toNat ≠ 0 →
      uxaXget rs' r0 = if r0 = rd then v else uxaXget rs r0) →
    r.toNat ≠ rd.toNat → phys5 rs' r = phys5 rs r := by
  intro H Hne
  by_cases h0 : r.toNat = 0
  · show uxaXget rs' r = uxaXget rs r
    rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
  · show uxaXget rs' r = uxaXget rs r
    rw [H r h0, if_neg (fun (e : r = rd) => Hne (by rw [e]))]

theorem uintNeOfRegidx (a b : BitVec 5) : regidx.Regidx a ≠ regidx.Regidx b → a.toNat ≠ b.toNat :=
  fun H E => H (by rw [uint5Inj a b E])

/-! # The surface -/

section surf
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)]
variable (i : Agent) (cid cpu : CPU) (γm γp : GName)
variable (img : Image) (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
/- the abstract annotation-backed condition -/
variable (Cond : Prop → IProp GF) [∀ C, Persistent (Cond C)]
variable (CondAnd : ∀ C1 C2, ⊢ Cond C1 -∗ Cond C2 -∗ Cond (C1 ∧ C2))
variable (CondMono : ∀ C1 C2 : Prop, (C1 → C2) → ⊢ Cond C1 -∗ Cond C2)

def curC (m : RegMap) (pc : BitVec 64) (s : Athread) (C : Prop) : Prop :=
  ∃ rs k, RetX cpu rs k s ∧ ctrlOk rs ∧ rs .PC = pc ∧
    phys5 rs 4#5 = rget cid m 4#5 ∧ phys5 rs 2#5 = rget cid m 2#5 ∧
    (C → gprRel cid m rs)

/-- `WP Loop` ↦ `goalC`. -/
def goalC : IProp GF :=
  iprop(∀ s m pc C, ⌜curC cid cpu ctrlOk m pc s C⌝ -∗ ghost_var γm (.own (1 : Qp).half) m -∗
    ghost_var γp (.own (1 : Qp).half) pc -∗ Cond C -∗ wpd .MaybeStuck i s (Φ0 (GF := GF)))

def sieCapC (_cid0 : CPU) (m : RegMap) (_n : Nat) (b : Bool) (_p : BitVec 64) : IProp GF :=
  iprop(⌜b = false⌝ ∗ ghost_var γm (.own (1 : Qp).half) m)

def pcIsC (pc : BitVec 64) : IProp GF := ghost_var γp (.own (1 : Qp).half) pc

def AxSymMem3.isMem (ins : instruction) : Prop :=
  match ins with
  | .LOAD _ | .STORE _ => True
  | _ => False

def instrC (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : IProp GF :=
  iprop(⌜textOkM img ctrlOk textAt pc is_rvc ins ∧ (AxSymMem3.isMem ins ∨ rf0 (execute ins))⌝)

theorem instrCD (pc : BitVec 64) (c : Bool) (ins : instruction) :
    ¬ AxSymMem3.isMem ins →
    textOkM img ctrlOk textAt pc c ins ∧ (AxSymMem3.isMem ins ∨ rf0 (execute ins)) →
    textOkD img ctrlOk textAt pc c ins := by
  rintro Hnm ⟨⟨Hc, h, i0, Ha, Hd, He⟩, Hm | Hr⟩
  · exact absurd Hm Hnm
  · exact ⟨Hc, h, i0, Ha, Hd, He, Hr⟩

/-! # 1. The ALU engine over the conditional surface -/

variable (HX : XGprWrite (GF := GF) i cpu ctrlOk (textOkD img ctrlOk textAt))

include HX in
theorem wpGprWriteC (pc : BitVec 64) (rd rsa rsb : BitVec 5) (base : instruction)
    (wval : RegMap → BitVec 64) (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    (∀ m1 m2 : RegMap, (∀ r, rget cid m1 r = rget cid m2 r) → wval m1 = wval m2) →
    ¬ AxSymMem3.isMem base →
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    (∀ (m' : RegMap) (s_pc : ExecSt),
       s_pc.regs .nextPC = pc + 2#64 →
       s_pc.gpr rsa = rget cid m' rsa →
       s_pc.gpr rsb = rget cid m' rsb →
       exec (execute base) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd (wval m'))) →
    ⊢ sieCapC (GF := GF) γm cid m n b p -∗
      pcIsC (GF := GF) γp pc -∗
      instrC (GF := GF) img ctrlOk textAt pc true base -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapC γm cpu' (m.set rd (wval m)) n b p -∗
        pcIsC γp (pc + 2#64) -∗
        goalC i cid cpu γm γp ctrlOk Cond)) -∗
      goalC i cid cpu γm γp ctrlOk Cond := by
  intro Hwv Hnm Hrd Hrdok Hbexec
  unfold sieCapC pcIsC instrC
  iintro ⟨%Hb, Hm⟩ Hp %Htext Hcont
  subst Hb
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goalC
  iintro %s %m' %pc' %C %Hcur Hm' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hsp, Hrel⟩ := Hcur
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
  have HXi := HX s rs k pc true base rd (wval (mphys rs)) HRet Hctrl HPC
    (instrCD img ctrlOk textAt pc true base Hnm Htext) Hrd
    (fun s_pc Hnpc Hag => Hbexec (mphys rs) s_pc Hnpc (Hsrc s_pc rsa Hag) (Hsrc s_pc rsb Hag))
  iapply HXi
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hgpr
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd (wval m)) γm m m $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 2#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hne_tp : (4#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.2 (uint5Inj _ _ E).symm
  have Hne_sp : (2#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.1 (uint5Inj _ _ E).symm
  have Hcur' : curC cid cpu ctrlOk (m.set rd (wval m)) (pc + 2#64) s' C := by
    refine ⟨rs', k', HRet', Hctrl', HPC', ?_, ?_, ?_⟩
    · rw [phys5UpdNe rs rs' rd 4#5 _ Hgpr Hne_tp, Htp, rget_tp, rget_tp]
    · rw [phys5UpdNe rs rs' rd 2#5 _ Hgpr Hne_sp, Hsp,
        rget_ne cid _ 2#5 (by decide) (by decide), rget_ne cid _ 2#5 (by decide) (by decide),
        RegMap.set_other _ _ _ _ (fun e => Hrdok.2.1 e.symm)]
    · intro HCC
      have Hw : wval (mphys rs) = wval m :=
        Hwv _ _ (fun r => (Hrelp r).symm.trans (Hrel HCC r))
      rw [← Hw]
      exact gprRelUpd cid m rs rs' rd (wval (mphys rs)) (Hrel HCC) Hrd Hrdok.2.2 Hgpr
  iapply Hcont $$ [Hm] Hp %s' %(m.set rd (wval m)) %(pc + 2#64) %C %Hcur' Hm' Hp' HC
  isplitr
  · ipureintro; rfl
  · iexact Hm

include HX in
/-- The REAL SC leaves, statements unchanged; scripts = AxReuseProbe2's with the
certificate's map generalised. -/
theorem wpCmvC (pc : BitVec 64) (rd rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapC (GF := GF) γm cid m n b p -∗
      pcIsC (GF := GF) γp pc -∗
      instrC (GF := GF) img ctrlOk textAt pc true (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapC γm cpu' (m.set rd (0#64 + rget cid m rs2)) n b p -∗
        pcIsC γp (pc + 2#64) -∗
        goalC i cid cpu γm γp ctrlOk Cond)) -∗
      goalC i cid cpu γm γp ctrlOk Cond := by
  intro Hrd Hrdok
  refine wpGprWriteC i cid cpu γm γp img ctrlOk textAt Cond HX pc rd rs2 rs2
    (.RTYPE (.Regidx rs2, zreg, .Regidx rd, .ADD)) (fun m => 0#64 + rget cid m rs2) m n b p
    ?_ (fun h => h) Hrd Hrdok ?_
  · intro m1 m2 Hm12
    show 0#64 + rget cid m1 rs2 = 0#64 + rget cid m2 rs2
    rw [Hm12]
  · intro m' s_pc _ Hva _
    show exec (execute_RTYPE (.Regidx rs2) (.Regidx 0#5) (.Regidx rd) .ADD) s_pc = _
    rw [execExecuteRTYPEADDGpr rs2 0#5 rd s_pc]
    unfold gprRdVal
    rw [Hva]
    rfl

include HX in
theorem wpCaddiwC (pc : BitVec 64) (rd : BitVec 5) (imm : BitVec 6)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapC (GF := GF) γm cid m n b p -∗
      pcIsC (GF := GF) γp pc -∗
      instrC (GF := GF) img ctrlOk textAt pc true
        (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapC γm cpu' (m.set rd (sign_extend (m := 64) (Sail.BitVec.extractLsb
          (rget cid m rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0))) n b p -∗
        pcIsC γp (pc + 2#64) -∗
        goalC i cid cpu γm γp ctrlOk Cond)) -∗
      goalC i cid cpu γm γp ctrlOk Cond := by
  intro Hrd Hrdok
  refine wpGprWriteC i cid cpu γm γp img ctrlOk textAt Cond HX pc rd rd rd
    (.ADDIW (sign_extend (m := 12) imm, .Regidx rd, .Regidx rd))
    (fun m => sign_extend (m := 64) (Sail.BitVec.extractLsb
      (rget cid m rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0)) m n b p
    ?_ (fun h => h) Hrd Hrdok ?_
  · intro m1 m2 Hm12
    show sign_extend (m := 64) (Sail.BitVec.extractLsb
        (rget cid m1 rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0) =
      sign_extend (m := 64) (Sail.BitVec.extractLsb
        (rget cid m2 rd + sign_extend (m := 64) (sign_extend (m := 12) imm)) 31 0)
    rw [Hm12]
  · intro m' s_pc _ Hva _
    rw [execExecuteADDIWGpr rd rd (sign_extend (m := 12) imm) s_pc]
    unfold gprAddiwVal
    rw [Hva]

/-! # 3 (first half). c.addi4spn -/

include HX in
theorem wpCaddi4spnC (pc : BitVec 64) (rdc : cregidx) (nzimm : BitVec 8) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (b : Bool) (p : BitVec 64) :
    creg2reg_idx rdc = .Regidx rd →
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapC (GF := GF) γm cid m n b p -∗
      pcIsC (GF := GF) γp pc -∗
      instrC (GF := GF) img ctrlOk textAt pc true (.ITYPE (caddi4spnImm nzimm, sp, .Regidx rd, .ADDI)) -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapC γm cpu' (m.set rd (m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm))) n b p -∗
        pcIsC γp (pc + 2#64) -∗
        goalC i cid cpu γm γp ctrlOk Cond)) -∗
      goalC i cid cpu γm γp ctrlOk Cond := by
  intro _ Hrd Hrdok
  refine wpGprWriteC i cid cpu γm γp img ctrlOk textAt Cond HX pc rd 2#5 2#5
    (.ITYPE (caddi4spnImm nzimm, sp, .Regidx rd, .ADDI))
    (fun m => m 2#5 + sign_extend (m := 64) (caddi4spnImm nzimm)) m n b p
    ?_ (fun h => h) Hrd Hrdok ?_
  · intro m1 m2 Hm12
    show m1 2#5 + _ = m2 2#5 + _
    rw [← rget_ne cid m1 2#5 (by decide) (by decide), ← rget_ne cid m2 2#5 (by decide) (by decide),
      Hm12]
  · intro m' s_pc _ Hva _
    show exec (execute (.ITYPE (caddi4spnImm nzimm, .Regidx 2#5, .Regidx rd, .ADDI))) s_pc = _
    rw [execExecuteITYPEADDIGpr 2#5 rd (caddi4spnImm nzimm) s_pc]
    unfold gprAddiVal
    rw [Hva, rget_ne cid m' 2#5 (by decide) (by decide)]

/-! # 2. The memory leaves over `XMem` -/

variable (Hsp : SpineOkT img ctrlOk textAt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

/- the data region, its address map, the regime's byte conversions -/
variable (dreg : Int → Nat → Prop) (za : PAddr → Int)
variable (ext8 : List (BitVec 8) → BitVec 64) (bytes8 : BitVec 64 → List (BitVec 8))
variable (HnoRmwReg : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dreg base n⌝)

def AxSymMem3.pin (a : Int) : Int → Nat → Prop := fun a' n => a' = a ∧ n = 8

/- the PHYSICAL owned word and its conditional wrapper -/
variable (wpt : PAddr → DFrac → BitVec 64 → IProp GF)

def wptC (pa : PAddr) (dq : DFrac) (v : BitVec 64) : IProp GF :=
  iprop(∃ (v' : BitVec 64) (C : Prop), wpt pa dq v' ∗ Cond C ∗ ⌜C → v' = v⌝)

/- PROTOCOL RULES -/
variable (ldRule : ∀ pa dq v', ⊢ wpt pa dq v' -∗
  ⌜dreg (za pa) 8⌝ ∗
  Fld (AxSymMem3.pin (za pa)) i (fun _ vs => iprop(wpt pa dq v' ∗ Cond (ext8 vs = v'))))
variable (stRule : ∀ pa vold vnew, ⊢ wpt pa (.own 1) vold -∗
  ⌜dreg (za pa) 8⌝ ∗
  Fst (AxSymMem3.pin (za pa)) i (fun _ data => iprop(⌜data = bytes8 vnew⌝ -∗ wpt pa (.own 1) vnew)))

/- THE REGIME'S DATA CERTIFICATES for the two families -/
variable (HxCldsp : ∀ (rs : RegFile) (pc : BitVec 64) (uimm : BitVec 6) (rd : BitVec 5),
  ctrlOk rs → rd.toNat ≠ 0 → MachCSL.rdOk rd →
  dreg (za (phys5 rs 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3))) 8 →
  ExecD img (AxSymMem3.pin (za (phys5 rs 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)))) true
    ctrlOk rs pc (wrLoad rd ext8) (fun d => ∃ vs, d = .DDone vs)
    (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), sp, .Regidx rd, false, 8)))
variable (HxCsdsp : ∀ (rs : RegFile) (pc : BitVec 64) (uimm : BitVec 6) (rs2 : BitVec 5),
  ctrlOk rs →
  dreg (za (phys5 rs 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3))) 8 →
  ExecD img (AxSymMem3.pin (za (phys5 rs 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)))) false
    ctrlOk rs pc wrStore (fun d => d = .DDone (bytes8 (phys5 rs rs2)))
    (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), .Regidx rs2, sp, 8)))

include HnoRmwReg in
theorem pinNormw (pa : PAddr) : dreg (za pa) 8 → ∀ GD, rvwmoCatConsistent GD →
    AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n →
        ¬ AxSymMem3.pin (za pa) base n⌝ := by
  intro Hd GD Hc
  refine (HnoRmwReg GD Hc).trans (pure_mono ?_)
  intro Hnr k lb aq rl base n Hlb Hid ⟨e1, e2⟩
  subst e1 e2
  exact Hnr k lb aq rl _ _ Hlb Hid Hd

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] in
theorem spPhys (m : RegMap) (rs : RegFile) :
    phys5 rs 2#5 = rget cid m 2#5 → phys5 rs 2#5 = m 2#5 := by
  intro Hh
  rw [Hh, rget_ne cid m 2#5 (by decide) (by decide)]

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] in
/-- (Lean-only) `gprAfter` of a completed load. -/
theorem AxSymMem3.gprAfterWrLoad (rd : BitVec 5) (ext : List (BitVec 8) → BitVec 64)
    (vs : List (BitVec 8)) (rs : RegFile) (r : BitVec 5) :
    gprAfter (wrLoad rd ext) (.DDone vs) rs r = if r = rd then ext vs else uxaXget rs r := rfl

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] in
/-- (Lean-only) A load's flow resource IS its pending data resource (stated outside proof
mode: see the KERNEL BLOW-UP note). -/
theorem AxSymMem3.fldToDRes (dok : Int → Nat → Prop) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    Fld dok i Out ⊢ DResM rvwmoCatConsistent dok true i Out .DPend := .rfl

include Hsp Htext Hflow HnoRmwReg ldRule HxCldsp CondAnd in
theorem wpCldspC (pc : BitVec 64) (uimm : BitVec 6) (rd : BitVec 5)
    (m : RegMap) (n : Nat) (v : BitVec 64) (b : Bool) (p : BitVec 64) {dqm : DFrac} :
    rd.toNat ≠ 0 →
    MachCSL.rdOk rd →
    ⊢ sieCapC (GF := GF) γm cid m n b p -∗
      pcIsC (GF := GF) γp pc -∗
      instrC (GF := GF) img ctrlOk textAt pc true
        (.LOAD (zero_extend (m := 12) (uimm +++ 0b000#3), sp, .Regidx rd, false, 8)) -∗
      wptC Cond wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) dqm v -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapC γm cpu' (m.set rd v) n b p -∗
        pcIsC γp (pc + 2#64) -∗
        wptC Cond wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) dqm v -∗
        goalC i cid cpu γm γp ctrlOk Cond)) -∗
      goalC i cid cpu γm γp ctrlOk Cond := by
  intro Hrd Hrdok
  generalize Hpa0 : m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = pa
  unfold sieCapC pcIsC instrC wptC
  iintro ⟨%Hb, Hm⟩ Hp %Htx Hpt Hcont
  subst Hb
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goalC
  iintro %s %m' %pc' %C %Hcur Hm' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  icases Hpt with ⟨%v', %Cm, Hpt, #HCm, %Hv'⟩
  ihave Hld := ldRule pa dqm v' $$ Hpt
  icases Hld with ⟨%Hdr, F⟩
  have Hpa : phys5 rs 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = pa := by
    rw [spPhys cid m rs Hspx, Hpa0]
  have Hx := HxCldsp rs pc uimm rd Hctrl Hrd Hrdok
  rw [Hpa] at Hx
  have HXm := XMemHolds img (AxSymMem3.pin (za pa)) true i cpu ctrlOk textAt Hsp Htext Hflow
    (pinNormw i dreg za HnoRmwReg pa Hdr) (fun _ => True) (fun _ _ => pure_intro trivial)
    Φ0 (fun _ _ _ _ _ => postLiftingΦ0 i _)
    (fun _ vs => iprop(wpt pa dqm v' ∗ Cond (ext8 vs = v')))
    s rs k pc _ (wrLoad rd ext8) (fun d => ∃ vs, d = .DDone vs) HRet Hctrl HPC Htx.1
    (wrLoadRd0 rd ext8 Hrd) (Hx Hdr) (fun _ _ _ _ _ => postLiftingΦ0 i _)
  -- KERNEL BLOW-UP guard: never put a `DResM … true … .DPend`-typed hypothesis in the
  -- proof-mode context; restate XMemHolds' first premise at `Fld` outside proof mode.
  have HXm' := entails_wand ((AxSymMem3.fldToDRes _ i _).trans (wand_entails HXm))
  iapply HXm' $$ F
  iintro %s' %rs' %k' %d %_ %Hdp %HRet' %Hctrl' %HPC' %Hgpr Hout
  obtain ⟨vs, rfl⟩ := Hdp
  have HO : DResM rvwmoCatConsistent (AxSymMem3.pin (za pa)) true i
        (fun _ vs => iprop(wpt pa dqm v' ∗ Cond (ext8 vs = v'))) (.DDone vs) ⊢
      ∃ kd, iprop(wpt pa dqm v' ∗ Cond (ext8 vs = v')) := .rfl
  ihave Hout := HO $$ Hout
  icases Hout with ⟨%kd, Hpt, #Hce⟩
  iapply bupdWpd
  imod ghost_var_update_halves (m.set rd v) γm m m $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + 2#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget rs' r = if r = rd then ext8 vs else uxaXget rs r :=
    fun r Hr => (Hgpr r Hr).trans (AxSymMem3.gprAfterWrLoad rd ext8 vs rs r)
  have Hne_tp : (4#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.2 (uint5Inj _ _ E).symm
  have Hne_sp : (2#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.1 (uint5Inj _ _ E).symm
  have Hcur' : curC cid cpu ctrlOk (m.set rd v) (pc + 2#64) s' (C ∧ Cm ∧ ext8 vs = v') := by
    refine ⟨rs', k', HRet', Hctrl', by rw [HPC']; rfl, ?_, ?_, ?_⟩
    · rw [phys5UpdNe rs rs' rd 4#5 _ Hg' Hne_tp, Htp, rget_tp, rget_tp]
    · rw [phys5UpdNe rs rs' rd 2#5 _ Hg' Hne_sp, Hspx,
        rget_ne cid _ 2#5 (by decide) (by decide), rget_ne cid _ 2#5 (by decide) (by decide),
        RegMap.set_other _ _ _ _ (fun e => Hrdok.2.1 e.symm)]
    · rintro ⟨HCC, HCm', He⟩
      refine gprRelUpd cid m rs rs' rd v (Hrel HCC) Hrd Hrdok.2.2 ?_
      intro r Hr
      rw [Hg' r Hr, He, Hv' HCm']
  ihave Hc2 := CondAnd _ _ $$ HCm Hce
  ihave Hc3 := CondAnd _ _ $$ HC Hc2
  iapply Hcont $$ [Hm] Hp [Hpt] %s' %(m.set rd v) %(pc + 2#64) %(C ∧ Cm ∧ ext8 vs = v') %Hcur'
    Hm' Hp' Hc3
  · isplitr
    · ipureintro; rfl
    · iexact Hm
  · iexists v', Cm
    isplitl [Hpt]
    · iexact Hpt
    · isplitl
      · iexact HCm
      · ipureintro; exact Hv'

include Hsp Htext Hflow HnoRmwReg stRule HxCsdsp in
theorem wpCsdspC (pc : BitVec 64) (uimm : BitVec 6) (rs2 : BitVec 5)
    (m : RegMap) (n : Nat) (vold : BitVec 64) (b : Bool) (p : BitVec 64) :
    ⊢ sieCapC (GF := GF) γm cid m n b p -∗
      pcIsC (GF := GF) γp pc -∗
      instrC (GF := GF) img ctrlOk textAt pc true
        (.STORE (zero_extend (m := 12) (uimm +++ 0b000#3), .Regidx rs2, sp, 8)) -∗
      wptC Cond wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) vold -∗
      wpNext b p cid (fun cpu' => iprop(
        sieCapC γm cpu' m n b p -∗
        pcIsC γp (pc + 2#64) -∗
        wptC Cond wpt (m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3)) (.own 1) (rget cid m rs2) -∗
        goalC i cid cpu γm γp ctrlOk Cond)) -∗
      goalC i cid cpu γm γp ctrlOk Cond := by
  generalize Hpa0 : m 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = pa
  unfold sieCapC pcIsC instrC wptC
  iintro ⟨%Hb, Hm⟩ Hp %Htx Hpt Hcont
  subst Hb
  ihave Hcont := wpNext_off p cid _ $$ Hcont
  unfold goalC
  iintro %s %m' %pc' %C %Hcur Hm' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  obtain ⟨rs, k, HRet, Hctrl, HPC, Htp, Hspx, Hrel⟩ := Hcur
  icases Hpt with ⟨%v', %Cm, Hpt, _, _⟩
  ihave Hst := stRule pa v' (phys5 rs rs2) $$ Hpt
  icases Hst with ⟨%Hdr, F⟩
  have Hpa : phys5 rs 2#5 + zero_extend (m := 64) (uimm +++ 0b000#3) = pa := by
    rw [spPhys cid m rs Hspx, Hpa0]
  have Hx := HxCsdsp rs pc uimm rs2 Hctrl
  rw [Hpa] at Hx
  have HF : Fst (AxSymMem3.pin (za pa)) i
        (fun _ data => iprop(⌜data = bytes8 (phys5 rs rs2)⌝ -∗ wpt pa (.own 1) (phys5 rs rs2))) ⊢
      DResM rvwmoCatConsistent (AxSymMem3.pin (za pa)) false i
        (fun _ data => iprop(⌜data = bytes8 (phys5 rs rs2)⌝ -∗ wpt pa (.own 1) (phys5 rs rs2)))
        .DPend := .rfl
  ihave F := HF $$ F
  have HXm := XMemHolds img (AxSymMem3.pin (za pa)) false i cpu ctrlOk textAt Hsp Htext Hflow
    (pinNormw i dreg za HnoRmwReg pa Hdr) (fun _ => True) (fun _ _ => pure_intro trivial)
    Φ0 (fun _ _ _ _ _ => postLiftingΦ0 i _)
    (fun _ data => iprop(⌜data = bytes8 (phys5 rs rs2)⌝ -∗ wpt pa (.own 1) (phys5 rs rs2)))
    s rs k pc _ wrStore (fun d => d = .DDone (bytes8 (phys5 rs rs2))) HRet Hctrl HPC Htx.1
    wrStoreRd0 (Hx Hdr) (fun _ _ _ _ _ => postLiftingΦ0 i _)
  iapply HXm $$ F
  iintro %s' %rs' %k' %d %_ %Hdp %HRet' %Hctrl' %HPC' %Hgpr Hout
  subst Hdp
  have HO : DResM rvwmoCatConsistent (AxSymMem3.pin (za pa)) false i
        (fun _ data => iprop(⌜data = bytes8 (phys5 rs rs2)⌝ -∗ wpt pa (.own 1) (phys5 rs rs2)))
        (.DDone (bytes8 (phys5 rs rs2))) ⊢
      ∃ kd, iprop(⌜bytes8 (phys5 rs rs2) = bytes8 (phys5 rs rs2)⌝ -∗
        wpt pa (.own 1) (phys5 rs rs2)) := .rfl
  ihave Hout := HO $$ Hout
  icases Hout with ⟨%kd, Hpt⟩
  ispecialize Hpt $$ %rfl
  iapply bupdWpd
  imod ghost_var_update_halves (pc + 2#64) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hsame : ∀ r, phys5 rs' r = phys5 rs r := by
    intro r
    show uxaXget rs' r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hgpr r h0
  have Hcur' : curC cid cpu ctrlOk m (pc + 2#64) s' C := by
    refine ⟨rs', k', HRet', Hctrl', by rw [HPC']; rfl, by rw [Hsame]; exact Htp,
      by rw [Hsame]; exact Hspx, ?_⟩
    intro HCC r
    exact (Hsame r).trans (Hrel HCC r)
  iapply Hcont $$ [Hm] Hp [Hpt] %s' %m %(pc + 2#64) %C %Hcur' Hm' Hp' HC
  · isplitr
    · ipureintro; rfl
    · iexact Hm
  · iexists (phys5 rs rs2), C
    isplitl [Hpt]
    · iexact Hpt
    · isplitl
      · iexact HC
      · ipureintro; exact fun HCC => Hrel HCC rs2

/-! # 3 (second half). The cpuid REPLAY over the Lean interface (owner ruling Q17)

`AxReuseProbe.AbsCpuid` (the Lean SC proof text of `cpuid`) instantiated at this surface:
`Goal c` := `goalC` at SC hart `c`, `kctx c k` := `sieCapC` of `k`'s fields with the kernel
text `kt`, `pcIs` := `pcIsC`, `instr` := `instrC`.  The two ALU leaves (`wp_s_add`,
`wp_s_addiw`) are PROVED here, from the later-carrying lifting premise `XGprWriteL`; the
frame macros (`wp_prologue2` / `wp_epilogue2`, whose stack cells live in `frame2`), the
`frame2` resource and the text lemma are section premises (as Rocq's push/pop/ret/stack-split
leaves and `ci_*` were). -/

/-- (Lean-only) `XGprWrite` with the instruction step's later exposed on the continuation
(the Lean SC leaves carry `▷` before their continuation). -/
def AxSymMem3.XGprWriteL (i : Agent) (cpu : CPU) (ctrlOk : RegFile → Prop)
    (textOk : BitVec 64 → Bool → instruction → Prop) : Prop :=
  ∀ (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (rd : BitVec 5) (wval : BitVec 64),
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc is_rvc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ⊢ ▷ (∀ s' rs' k',
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = pc + instrLen is_rvc⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs r⌝ -∗
         wpd .MaybeStuck i s' (Φ0 (GF := GF))) -∗
       wpd .MaybeStuck i s (Φ0 (GF := GF))

omit [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] in
/-- (Lean-only) `XGprWriteL` is a strengthening of `XGprWrite`. -/
theorem AxSymMem3.xGprWriteOfL (textOk : BitVec 64 → Bool → instruction → Prop) :
    AxSymMem3.XGprWriteL (GF := GF) i cpu ctrlOk textOk → XGprWrite (GF := GF) i cpu ctrlOk textOk := by
  intro HL s rs k pc is_rvc ins rd wval h1 h2 h3 h4 h5 h6
  have H := HL s rs k pc is_rvc ins rd wval h1 h2 h3 h4 h5 h6
  iintro Hk
  iapply H
  inext
  iexact Hk

/-- (Lean-only) The SC context at this surface: the GPR mirror of `k` and the kernel text. -/
def AxSymMem3.kctxC (kt : IProp GF) (c : CPU) (k : KCtx) : IProp GF :=
  iprop(sieCapC γm c k.regs k.avail k.sie k.proc ∗ kt)

omit [InvGS_gen hlc GF] [AxirisG GF] [Axpol] [GhostVarG GF RegMap] [GhostVarG GF (BitVec 64)] in
/-- (Lean-only) The resuming hart may be the current one, whatever the interrupt state. -/
theorem AxSymMem3.wpNextSelf (sie : Bool) (p : BitVec 64) (c : CPU) (K : CPU → IProp GF) :
    wpNext sie p c K ⊢ K c := by
  unfold wpNext
  iintro H
  iapply H $$ %c %(fun _ => rfl)

variable (kt : IProp GF) [Persistent kt]
variable (HXL : AxSymMem3.XGprWriteL (GF := GF) i cpu ctrlOk (textOkD img ctrlOk textAt))

include HXL in
/-- (Lean-only) The ALU engine at the `kctx` shape, any length, SC hart `c`. -/
theorem AxSymMem3.wpGprWriteK (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool)
    (rd rsa rsb : BitVec 5) (base : instruction) (wval : RegMap → BitVec 64) :
    (∀ m1 m2 : RegMap, (∀ r, rget c m1 r = rget c m2 r) → wval m1 = wval m2) →
    ¬ AxSymMem3.isMem base →
    MachCSL.rdOk rd →
    (∀ (m' : RegMap) (s_pc : ExecSt),
       s_pc.regs .nextPC = pc + instrLen is_rvc →
       s_pc.gpr rsa = rget c m' rsa →
       s_pc.gpr rsb = rget c m' rsb →
       exec (execute base) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd (wval m'))) →
    instrC (GF := GF) img ctrlOk textAt pc is_rvc base ∗ AxSymMem3.kctxC γm kt c k ∗
      pcIsC (GF := GF) γp pc ∗
      ▷ (AxSymMem3.kctxC γm kt c (k.setReg rd (wval k.regs)) -∗
        pcIsC γp (pc + instrLen is_rvc) -∗ goalC i c cpu γm γp ctrlOk Cond) ⊢
      goalC i c cpu γm γp ctrlOk Cond := by
  intro Hwv Hnm Hrdok Hbexec
  have Hrd : rd.toNat ≠ 0 := fun E => Hrdok.1 (BitVec.eq_of_toNat_eq (by rw [E]; rfl))
  unfold AxSymMem3.kctxC sieCapC pcIsC instrC
  dsimp only [KCtx.setReg]
  iintro ⟨%Htext, ⟨⟨%Hb, Hm⟩, #Hkt⟩, Hp, Hcont⟩
  unfold goalC
  iintro %s %m' %pc' %C %Hcur Hm' Hp' #HC
  ihave %h1 := ghost_var_agree _ _ _ _ _ $$ Hm Hm'
  ihave %h2 := ghost_var_agree _ _ _ _ _ $$ Hp Hp'
  subst h1 h2
  obtain ⟨rs, kk, HRet, Hctrl, HPC, Htp, Hsp, Hrel⟩ := Hcur
  have Htp' : phys5 rs 4#5 = hartId c := Htp.trans (rget_tp c k.regs)
  have Hrelp := gprRelMphys c rs Htp'
  have Hsrc : ∀ (s_pc : ExecSt) (r : BitVec 5), gprAgree s_pc.regs rs →
      s_pc.gpr r = rget c (mphys rs) r := by
    intro s_pc r Hag
    rw [← Hrelp r]
    show uxaXget s_pc.regs r = uxaXget rs r
    by_cases h0 : r.toNat = 0
    · rw [AxReuseProbe2.uxaXgetZero _ r h0, AxReuseProbe2.uxaXgetZero _ r h0]
    · exact Hag r h0
  have HXi := HXL s rs kk pc is_rvc base rd (wval (mphys rs)) HRet Hctrl HPC
    (instrCD img ctrlOk textAt pc is_rvc base Hnm Htext) Hrd
    (fun s_pc Hnpc Hag => Hbexec (mphys rs) s_pc Hnpc (Hsrc s_pc rsa Hag) (Hsrc s_pc rsb Hag))
  iapply HXi
  inext
  iintro %s' %rs' %k' %HRet' %Hctrl' %HPC' %Hgpr
  iapply bupdWpd
  imod ghost_var_update_halves (k.regs.set rd (wval k.regs)) γm k.regs k.regs $$ Hm Hm' with ⟨Hm, Hm'⟩
  imod ghost_var_update_halves (pc + instrLen is_rvc) γp pc pc $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  have Hne_tp : (4#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.2 (uint5Inj _ _ E).symm
  have Hne_sp : (2#5 : BitVec 5).toNat ≠ rd.toNat :=
    fun E => Hrdok.2.1 (uint5Inj _ _ E).symm
  have Hcur' : curC c cpu ctrlOk (k.regs.set rd (wval k.regs)) (pc + instrLen is_rvc) s' C := by
    refine ⟨rs', k', HRet', Hctrl', HPC', ?_, ?_, ?_⟩
    · rw [phys5UpdNe rs rs' rd 4#5 _ Hgpr Hne_tp, Htp, rget_tp, rget_tp]
    · rw [phys5UpdNe rs rs' rd 2#5 _ Hgpr Hne_sp, Hsp,
        rget_ne c _ 2#5 (by decide) (by decide), rget_ne c _ 2#5 (by decide) (by decide),
        RegMap.set_other _ _ _ _ (fun e => Hrdok.2.1 e.symm)]
    · intro HCC
      have Hw : wval (mphys rs) = wval k.regs :=
        Hwv _ _ (fun r => (Hrelp r).symm.trans (Hrel HCC r))
      rw [← Hw]
      exact gprRelUpd c k.regs rs rs' rd (wval (mphys rs)) (Hrel HCC) Hrd Hrdok.2.2 Hgpr
  iapply Hcont $$ [Hm] Hp %s' %(k.regs.set rd (wval k.regs)) %(pc + instrLen is_rvc) %C %Hcur'
    Hm' Hp' HC
  isplitl
  · isplitr
    · ipureintro; exact Hb
    · iexact Hm
  · iexact Hkt

include HXL in
/-- The interface's `wp_s_add` at this surface (any length, any sources). -/
theorem AxSymMem3.wpSAddC (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool)
    (rd rs1 rs2 : BitVec 5) (_hrd : MachCSL.rdOk rd) :
    instrC (GF := GF) img ctrlOk textAt pc is_rvc
        (instruction.RTYPE (regidx.Regidx rs2, regidx.Regidx rs1, regidx.Regidx rd, rop.ADD)) ∗
      AxSymMem3.kctxC γm kt c k ∗ pcIsC (GF := GF) γp pc ∗
      ▷ wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxSymMem3.kctxC γm kt cpu' (k.setReg rd (k.rget cpu' rs1 + k.rget cpu' rs2)) -∗
        pcIsC γp (pc + instrLen is_rvc) -∗ goalC i cpu' cpu γm γp ctrlOk Cond)) ⊢
      goalC i c cpu γm γp ctrlOk Cond := by
  refine (sep_mono_right (sep_mono_right (sep_mono_right
    (later_mono (AxSymMem3.wpNextSelf k.sie k.proc c _))))).trans ?_
  refine AxSymMem3.wpGprWriteK i cpu γm γp img ctrlOk textAt Cond kt HXL c k pc is_rvc rd rs1 rs2
    _ (fun m => rget c m rs1 + rget c m rs2) ?_ (fun h => h) _hrd ?_
  · intro m1 m2 Hm12
    simp only [Hm12]
  · intro m' s_pc _ Hva Hvb
    show exec (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .ADD) s_pc = _
    rw [execExecuteRTYPEADDGpr rs2 rs1 rd s_pc]
    unfold gprRdVal
    rw [Hva, Hvb]

include HXL in
/-- The interface's `wp_s_addiw` at this surface (any length). -/
theorem AxSymMem3.wpSAddiwC (c : CPU) (k : KCtx) (pc : BitVec 64) (is_rvc : Bool)
    (imm : BitVec 12) (rd rs1 : BitVec 5) (_hrd : MachCSL.rdOk rd) :
    instrC (GF := GF) img ctrlOk textAt pc is_rvc
        (instruction.ADDIW (imm, regidx.Regidx rs1, regidx.Regidx rd)) ∗
      AxSymMem3.kctxC γm kt c k ∗ pcIsC (GF := GF) γp pc ∗
      ▷ wpNext k.sie k.proc c (fun cpu' =>
        iprop(AxSymMem3.kctxC γm kt cpu' (k.setReg rd (BitVec.signExtend 64
          (BitVec.extractLsb' 0 32 (k.rget cpu' rs1 + BitVec.signExtend 64 imm)))) -∗
        pcIsC γp (pc + instrLen is_rvc) -∗ goalC i cpu' cpu γm γp ctrlOk Cond)) ⊢
      goalC i c cpu γm γp ctrlOk Cond := by
  refine (sep_mono_right (sep_mono_right (sep_mono_right
    (later_mono (AxSymMem3.wpNextSelf k.sie k.proc c _))))).trans ?_
  refine AxSymMem3.wpGprWriteK i cpu γm γp img ctrlOk textAt Cond kt HXL c k pc is_rvc rd rs1 rs1
    _ (fun m => BitVec.signExtend 64
      (BitVec.extractLsb' 0 32 (rget c m rs1 + BitVec.signExtend 64 imm))) ?_ (fun h => h) _hrd ?_
  · intro m1 m2 Hm12
    simp only [Hm12]
  · intro m' s_pc _ Hva _
    rw [execExecuteADDIWGpr rs1 rd imm s_pc]
    unfold gprAddiwVal
    rw [Hva]
    rfl

/- the leaves NOT provided here (premises over the same surface): the frame macros, the frame
resource, the text lemma -/
variable (frame2C : BitVec 64 → BitVec 64 → BitVec 64 → IProp GF)
variable (textInstrC : ∀ (pc : BitVec 64) (rvc : Bool) (ins i₀ : instruction),
    Xv6.textDecodeWith drefM pc = some (rvc, ins, i₀) →
    Xv6.textDecodeWith drefS pc = some (rvc, ins, i₀) →
    kt ⊢ instrC (GF := GF) img ctrlOk textAt pc rvc ins)
variable (wpPrologue2C : ∀ (c : CPU) (k : KCtx) (_hsie : k.sie = false) (pc : BitVec 64)
    (_hK : 2 ≤ k.avail),
    instrC (GF := GF) img ctrlOk textAt pc true
      (instruction.ITYPE (4080#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instrC (GF := GF) img ctrlOk textAt (pc + 2#64) true
      (instruction.STORE (8#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 8)) ∗
    instrC (GF := GF) img ctrlOk textAt (pc + 4#64) true
      (instruction.STORE (0#12, regidx.Regidx 8#5, regidx.Regidx 2#5, 8)) ∗
    instrC (GF := GF) img ctrlOk textAt (pc + 6#64) true
      (instruction.ITYPE (16#12, regidx.Regidx 2#5, regidx.Regidx 8#5, iop.ADDI)) ∗
    AxSymMem3.kctxC γm kt c k ∗ pcIsC (GF := GF) γp pc ∗
    ▷ (AxSymMem3.kctxC γm kt c ((k.pushed 2).withRegs
          ((k.regs.set 2#5 (k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64)).set 8#5 (k.regs 2#5))) -∗
        pcIsC γp (pc + 8#64) -∗
        frame2C (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) -∗ goalC i c cpu γm γp ctrlOk Cond)
    ⊢ goalC i c cpu γm γp ctrlOk Cond)
variable (wpEpilogue2C : ∀ (c : CPU) (k : KCtx) (_hsie : k.sie = false) (pc : BitVec 64)
    (_hK : 2 ≤ k.avail) (R : RegMap) (_hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFF0#64)
    (ra s0 : BitVec 64),
    instrC (GF := GF) img ctrlOk textAt pc true
      (instruction.LOAD (8#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 8)) ∗
    instrC (GF := GF) img ctrlOk textAt (pc + 2#64) true
      (instruction.LOAD (0#12, regidx.Regidx 2#5, regidx.Regidx 8#5, false, 8)) ∗
    instrC (GF := GF) img ctrlOk textAt (pc + 4#64) true
      (instruction.ITYPE (16#12, regidx.Regidx 2#5, regidx.Regidx 2#5, iop.ADDI)) ∗
    instrC (GF := GF) img ctrlOk textAt (pc + 6#64) true
      (instruction.JALR (0#12, regidx.Regidx 1#5, regidx.Regidx 0#5)) ∗
    AxSymMem3.kctxC γm kt c ((k.pushed 2).withRegs R) ∗ pcIsC (GF := GF) γp pc ∗
      frame2C (k.regs 2#5) ra s0 ∗
    ▷ (AxSymMem3.kctxC γm kt c (k.withRegs (((R.set 1#5 ra).set 8#5 s0).set 2#5 (k.regs 2#5))) -∗
        pcIsC γp (jumpPc ra) -∗ goalC i c cpu γm γp ctrlOk Cond)
    ⊢ goalC i c cpu γm γp ctrlOk Cond)

omit [AxirisG GF] [Axpol] [GhostVarG GF (BitVec 64)] in
/-- (Lean-only) The kernel text sits in the context. -/
theorem AxSymMem3.kctxCKt (c : CPU) (k : KCtx) :
    AxSymMem3.kctxC γm kt c k ⊢ kt ∗ AxSymMem3.kctxC γm kt c k := by
  unfold AxSymMem3.kctxC
  iintro ⟨Hs, #Hkt⟩
  isplitl []
  · iexact Hkt
  · isplitl
    · iexact Hs
    · iexact Hkt

include HXL textInstrC wpPrologue2C wpEpilogue2C in
/-- **THE REPLAY** (Rocq `wp_cpuid_c`): the Lean SC proof text of `cpuid`
(`AxReuseProbe.wp_cpuid`) at the WPd surface; the two ALU leaves are the ones PROVED above. -/
theorem wpCpuidC (c : CPU) (k : KCtx) (hsie : k.sie = false) (hK : 2 ≤ k.avail) :
    AxReuseProbe.wp_cpuid_body (fun c => goalC i c cpu γm γp ctrlOk Cond)
      (AxSymMem3.kctxC γm kt) (fun _ => pcIsC (GF := GF) γp) c k hsie hK :=
  AxReuseProbe.wp_cpuid (fun c => goalC i c cpu γm γp ctrlOk Cond) (AxSymMem3.kctxC γm kt)
    (fun _ => pcIsC (GF := GF) γp) (instrC (GF := GF) img ctrlOk textAt) kt frame2C
    (AxSymMem3.kctxCKt γm kt) textInstrC wpPrologue2C
    (AxSymMem3.wpSAddC i cpu γm γp img ctrlOk textAt Cond kt HXL)
    (AxSymMem3.wpSAddiwC i cpu γm γp img ctrlOk textAt Cond kt HXL)
    wpEpilogue2C c k hsie hK

end surf

end Weak
