/-
Weak: **the two-hart emission witness** (route B).

Rocq: `iris/WeakRvwmoConfWit2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4d.4.  The companion of
`WeakRvwmoConfWit`, which witnessed `hartConf` at ONE nonempty row (the `sw &started` of `main`).
A single-hart witness cannot see the only thing the conformance bundle exists for: TWO harts whose
rows are tied by a read-from edge.

(1) §1 THE LOAD BLOCK.  Hart 1's spin load -- `lw a5,0(a4)` at `main+0x16`, the
    `while (__atomic_load_n(&started, …) == 0)` of xv6's `main`, the READ side of the handshake
    `WeakEvStarted` certifies from the write side.  Its residual monad is BUILT HERE, exactly the
    way `WeakEvStarted` §5 builds the store's: the cold-boot register file with `a4 = &started`
    and the PC at `main+0x16`, two unevaluated silent stretches (`esil`) with the footprint
    COLLECTED (not guessed), and the load node's request read off by the total projection
    `ereadReqAt` and inverted by `WeakEvLift.ereadReqAtInv`.  The width (4), the address
    (`&started`) and the access kind (plain -- the acquire is the SEPARATE `fence r,rw` at
    `main+0x18`) are the real machine's.  The block is PARAMETRIC in the value read.
(2) §3 THE MESSAGE-PASSING GRAPH `mpw`: hart 0's row is `WeakRvwmoConfWit`'s store, hart 1's row
    is the load, and the load's per-byte `ts` names hart 0's store (write index 1).  It is
    `rvwmoMinusDepsConsistent` and a `gdexecQconf` bundle with BOTH rows nonempty.
(3) §4 THE EARLY-READ VARIANT `mpw'`: the load reads the ERA IMAGE (`ts = 0`) and gmo puts the
    load first.  Also consistent, also qconf: the emission constrains the VALUE not at all.
(4) §5 THE SUPPLY: `WeakRvwmoSupply.supplyOfQconf` at the two-event candidate.

§6 of the Rocq file (a prose record of what a genuine LB-cycle witness would still cost) is a
comment only; its verdict carries over: the single missing mechanism is an `esil` → `admRun`
bridge at the `pstepEv` tier.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below), `WeakEvStarted`'s and `WeakRvwmoConfWit`'s
   vocabulary (`regstate` ↦ `RegFile`, `oib32` ↦ `Ibch`, `dev_state` ↦ `Efab`, `agent` ↦ `Nat`,
   `gset register` ↦ `List Register`, `bv_unsigned w` ↦ `w.toNat`, `seq 0 2` ↦
   `List.range' 0 2`, `is_Some o` ↦ `o.isSome = true`).  Duplicated Rocq names are
   file-qualified (`notes/weak-port-dupnames.json`): `WeakRvwmoConfWit2.ldP0/ldP1/ldVs/ldRow/
   mpw/mpRows`.  The section `G2`'s notation `G` is a `local notation` for
   `Gexec.mk im [[r0], [r1]] mo`.
2. THE CONCRETE STATE (`WeakEvStarted` deviation 7, same recipe): `ColdBoot.cold_regs` ↦
   `bootLand ⟨0, _⟩ WeakEvStarted.regs0`; the Lean kernel image has `main+0x16 = 0x80000ee4`
   `c.lw a5,0(a4)` (`0x431c`).  Since that pc is ≡ 0 mod 4, the Lean model fetches a FOUR-byte
   window there (Rocq: one 2-byte read), so `ldWf : BitVec 32` and `ldWord` is the real window
   `0x000f431c` (the compressed load plus the low half of the following `fence r,rw`), checked
   against the image by the Lean-only `WeakRvwmoConfWit2.ldWordKw`.  `ld_Dl` is the collector
   APPLICATION (unevaluated) and `ldD` its deduplicated 21-register readback (first-occurrence
   order), checked both ways by the Lean-only `WeakRvwmoConfWit2.ldDCovers` /
   `WeakRvwmoConfWit2.ldDExact`.  `ldReql` is an `Option.get` (Lean-only proof argument
   `WeakRvwmoConfWit2.ldX2IsRead`).  THE MEASUREMENT MATCHES ROCQ: 106 and 97 silent nodes.
   `ldLoadPlain` is `classify … = ⟨false, false, false⟩` (`akIfetch, akLatest, akSync`; Rocq's
   `AkInfo false false false`); `ldLoadPa` is stated at `@Eq PAddr`.
3. THE STEP: Lean's `pstepEv` is the fabric-`Efab` instance (the hart's own node arm, plain-RAM
   read disjunct, `WeakEvInst.pnodeStep`); `ldPstep` takes the `.Ok (w, none)` resume.
4. O2 / STAGE C (owner ruling Q-C1, `notes/weak-port-o2-stageC.md` item 17): the fetch is an
   ADMINISTRATIVE label pinned to the boot image (`WeakRvwmoSupply` deviation 2).  Both
   emissions here start AT their memory node (`ARnil`, as in Rocq), so they carry no fetch item
   and the extra `gdexecQconf` slot `emFetchImg` holds vacuously: Lean-only
   `WeakRvwmoConfWit2.ldEmFetchImg` / `WeakRvwmoConfWit2.evEmFetchImg`.  (The fetch that
   precedes the load, `ldX1`'s 4-byte window, IS the image's: `WeakRvwmoConfWit2.ldWordKw`.)
   `mpSupply` concludes at the PINNED LTS `pstepPin mpCand.cdImg pstepEv` (Rocq: `pstep_ev`);
   `supplyOfQconf`'s third premise is discharged with the emission's `emFetchImg`.  Stage B's
   `mpCandFetchInert`, `hemitOneFetch`, `admRunReadNode`, `pstepReadNodeNoFetch` are DELETED.
5. §7's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).

**Rocq → Lean name map.**  `ld_pc` `ldPc`, `ld_word` `ldWord`, `ld_wf` `ldWf`, `ld_rs0` `ldRs0`,
`ld_c1` `ldC1`, `ld_Dl` `ldDl`, `ld_D` `ldD`, `ld_x0..2` `ldX0..2`, `ld_reql` `ldReql`,
`ld_len1/2` `ldLen1/2`, `ld_load_req` `ldLoadReq`, `ld_load_pa` `ldLoadPa`, `ld_load_plain`
`ldLoadPlain`, `ld_load_ram` `ldLoadRam`, `ld_same_flag` `ldSameFlag`, `ld_p0`
`WeakRvwmoConfWit2.ldP0`, `ld_p1` `WeakRvwmoConfWit2.ldP1`, `ld_ts` `ldTs`, `ld_vs`
`WeakRvwmoConfWit2.ldVs`, `ld_tvs` `ldTvs`, `ld_wl` `ldWl`, `ld_row` `WeakRvwmoConfWit2.ldRow`,
`ld_em` `ldEm`, `ld_pstep` `ldPstep`, `ld_realizes` `ldRealizes`, `ld_hart_conf` `ldHartConf`,
`ld_em_devfree` `ldEmDevfree`, `row_deps_single` `rowDepsSingle`, `ev_row_deps_empty`
`evRowDepsEmpty`, `ld_row_deps_empty` `ldRowDepsEmpty`, `lb_shape_ok` `lbShapeOk`, `g2_lbl`
`g2Lbl`, `g2_lbl0/1` `g2Lbl0/1`, `g2_pos0` `g2Pos0`, `g2_nogpo` `g2Nogpo`, `g2_noppo` `g2Noppo`,
`g2_ppo_gmo` `g2PpoGmo`, `g2_gwf` `g2Gwf`, `mp_img` `mpImg`, `mp_img_byte` `mpImgByte`, `mpw`
`WeakRvwmoConfWit2.mpw`, `mpwd` `mpwd`, `mpw_gwrites` `mpwGwrites`, `mpw_gwix0` `mpwGwix0`,
`mpw_write_at1` `mpwWriteAt1`, `mpw_wr` `mpwWr`, `mpw_rd` `mpwRd`, `mpw_gvis0` `mpwGvis0`,
`mpw_consistent` `mpwConsistent`, `mpw_deps_consistent` `mpwDepsConsistent`, `mp_boot`
`mpBoot`, `mpw_qconf` `mpwQconf`, `mpw'` `mpw'`, `mpwd'` `mpwd'`, `mpw'_gwrites`
`mpw'Gwrites`, `mpw'_gwix0` `mpw'Gwix0`, `mpw'_wr` `mpw'Wr`, `mpw'_rd` `mpw'Rd`, `mpw'_novis`
`mpw'Novis`, `mpw'_consistent` `mpw'Consistent`, `mpw'_deps_consistent` `mpw'DepsConsistent`,
`mpw'_qconf` `mpw'Qconf`, `mp_st` `mpSt`, `mp_ld` `mpLd`, `mp_cand` `mpCand`, `mp_rows`
`WeakRvwmoConfWit2.mpRows`, `mp_cand_rows` `mpCandRows`, `mp_supply` `mpSupply`.
Lean-only (file-qualified): `WeakRvwmoConfWit2.ldWordKw`, `WeakRvwmoConfWit2.ldDCovers`,
`WeakRvwmoConfWit2.ldDExact`, `WeakRvwmoConfWit2.ldX2IsRead` (deviation 2),
`WeakRvwmoConfWit2.ldEmFetchImg`, `WeakRvwmoConfWit2.evEmFetchImg` (deviation 4);
`WeakRvwmoConfWit2.ldVsLookup`, `WeakRvwmoConfWit2.ldTsLookup`,
`WeakRvwmoConfWit2.wbytesLookupInv` (the byte inversions Rocq does by `destruct j`).

**Dropped:** nothing (Rocq 72 declarations; Lean 72 + 9 Lean-only).

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** `lbShapeOk`'s `LIo` arm is `True` (`gwf`'s flip).
-/
import Weak.WeakRvwmoConfWit
import Weak.KernelSitesDef

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! ## 1. THE LOAD BLOCK — `lw a5,0(a4)` at `main+0x16` -/

def ldPc : BitVec 64 := BitVec.ofNat 64 (KernelSyms.«main» + 0x16)

/-- The four-byte fetch window at `main+0x16` (deviation 2): `c.lw a5,0(a4)` (`0x431c`) and the
low half of the next instruction. -/
def ldWord : Nat := 0x000f431c
def ldWf : BitVec 32 := BitVec.ofNat 32 ldWord

/-- Lean-only: the window IS the kernel image's at `main+0x16`. -/
theorem WeakRvwmoConfWit2.ldWordKw : kw ((KernelSyms.«main» : Int) + 0x16) = ldWord := by
  decide +kernel

/-- The cold-boot file with the ADDRESS register `a4` at `&started` and the PC at the load. -/
def ldRs0 : RegFile :=
  (((bootLand ⟨0, by decide⟩ WeakEvStarted.regs0).set .x14 evFlag).set .PC ldPc).set .nextPC ldPc

noncomputable def ldC1 : RegFile × SailM Unit := erunAny 400 ldRs0 (riscvStep false)

/-- THE FOOTPRINT, collected (the collector application, unevaluated). -/
noncomputable def ldDl : List Register :=
  erunRegs 400 ldRs0 (riscvStep false) ++
    erunRegs 600 ldC1.1 (ereadResume ldWf.toNat ldC1.2)

/-- … deduplicated (read back once, first-occurrence order). -/
def ldD : List Register :=
  [.cur_privilege, .mcountinhibit, .minstretcfg, .minstret_increment, .hart_state, .misa, .mideleg,
   .mip, .sig_meip, .sig_seip, .mie, .mstatus, .PC, .pma_regions, .pmpcfg_n, .pmpaddr_n,
   .htif_tohost_base, .elp, .nextPC, .x14, .mseccfg]

theorem WeakRvwmoConfWit2.ldDCovers : ldDl.all (fun r => decide (r ∈ ldD)) = true := by
  decide +kernel

theorem WeakRvwmoConfWit2.ldDExact : ldD.all (fun r => decide (r ∈ ldDl)) = true := by
  decide +kernel

/-- THE TWO CURSORS, unevaluated compositions: `ldX1` at the FETCH node, `ldX2` at the DATA LOAD
node. -/
noncomputable def ldX0 : ecur := (ldRs0, riscvStep false)
noncomputable def ldX1 : ecur := esil 400 ldD ldX0
noncomputable def ldX2 : ecur := esil 600 ldD (ecurRead ldWf.toNat ldX1)

theorem WeakRvwmoConfWit2.ldX2IsRead : (ereadReqAt 4 64 ldX2.2).isSome = true := by
  decide +kernel

noncomputable def ldReql : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 4 64 ldX2.2).get WeakRvwmoConfWit2.ldX2IsRead

/-- THE MEASUREMENT.  106 silent nodes to the fetch, 97 more to the load. -/
theorem ldLen1 : ecount 400 ldD ldX0 = 106 := by decide +kernel
theorem ldLen2 : ecount 600 ldD (ecurRead ldWf.toNat ldX1) = 97 := by decide +kernel

/-- THE LOAD NODE: width 4 at `&started`, PLAIN. -/
theorem ldLoadReq : ereadReqAt 4 64 ldX2.2 = some ldReql := (Option.some_get _).symm
theorem ldLoadPa : ldReql.pa = evFlag := (by decide +kernel : @Eq PAddr ldReql.pa evFlag)
theorem ldLoadPlain : classify ldReql.access_kind = ⟨false, false, false⟩ := by decide +kernel
theorem ldLoadRam : devAddr ldReql.pa = false := by decide +kernel

/-- … and it IS the same byte the store witness writes. -/
theorem ldSameFlag : paZ ldReql.pa = paZ evFlag := by rw [ldLoadPa]

/-! ### 1.1 The block -/

/-- The hart, sitting at the load node. -/
noncomputable def WeakRvwmoConfWit2.ldP0 (cpu : CPU) (rs : RegFile) (ib : Ibch) : Pexv6 :=
  .PHart cpu ldX2.2 rs none ib

/-- … and where it lands, PER VALUE READ. -/
noncomputable def WeakRvwmoConfWit2.ldP1 (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch) :
    Pexv6 :=
  .PHart cpu (ereadResume w.toNat ldX2.2) rs none ib

def ldTs (t : Nat) : List Nat := [t, t, t, t]

def WeakRvwmoConfWit2.ldVs (w : BitVec 32) : List (BitVec 8) :=
  [nthByte (n := 4) w 0, nthByte (n := 4) w 1, nthByte (n := 4) w 2, nthByte (n := 4) w 3]

def ldTvs (t : Nat) (w : BitVec 32) : List (Nat × BitVec 8) :=
  [(t, nthByte (n := 4) w 0), (t, nthByte (n := 4) w 1), (t, nthByte (n := 4) w 2),
   (t, nthByte (n := 4) w 3)]

/-- THE WLABEL the step emits: a plain, non-latest load of four bytes at `&started`, with the
EMPTY address-operand list. -/
def ldWl (t : Nat) (w : BitVec 32) : Wlabel :=
  .LLoad false false (paZ evFlag) (ldTvs t w) []

/-- THE ROW: its axiomatic image, ONE graph label. -/
def WeakRvwmoConfWit2.ldRow (t : Nat) (w : BitVec 32) : List Lbl :=
  [.LLoad false (paZ evFlag) (ldTs t) (WeakRvwmoConfWit2.ldVs w)]

noncomputable def ldEm (t : Nat) (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch) :
    Hemission :=
  ⟨[(ldWl t w, some 0)], WeakRvwmoConfWit2.ldP1 w cpu rs ib⟩

theorem ldPstep (t : Nat) (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d0 : Efab) :
    pstepEv (WeakRvwmoConfWit2.ldP0 cpu rs ib) d0 (ldWl t w)
      (WeakRvwmoConfWit2.ldP1 w cpu rs ib) d0 := by
  obtain ⟨K, Hm, Hres⟩ := ereadReqAtInv 4 64 ldX2.2 ldReql ldLoadReq
  simp only [pstepEv, WeakRvwmoConfWit2.ldP0, WeakRvwmoConfWit2.ldP1]
  rw [Hres w, Hm]
  refine ⟨by trivial, none, none, none, by trivial, by trivial, Or.inl ⟨?_, rfl⟩⟩
  simp only [pstepNode, pnodeStep, ldLoadRam, Bool.false_eq_true, if_false]
  refine Or.inr ⟨by rw [ldLoadPlain], Or.inl ⟨by rw [ldLoadPlain], w, ldTvs t w, rfl, ?_, ?_,
    by trivial, by trivial, by trivial, by trivial, by trivial, by trivial⟩⟩
  · intro j hj
    rcases j with _ | _ | _ | _ | j
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  · rw [ldLoadPlain, ldLoadPa]
    rfl

theorem ldRealizes (t : Nat) (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch)
    (ws : Wstate) :
    hlblRealizes (WeakRvwmoConfWit2.ldP0 cpu rs ib) ws
      (.LLoad false (paZ evFlag) (ldTs t) (WeakRvwmoConfWit2.ldVs w)) (ldWl t w) :=
  ⟨trivial, rfl, rfl, rfl⟩

/-- THE WITNESS: hart 1's spin load IS an emittable row, at every value. -/
theorem ldHartConf (i t : Nat) (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch)
    (d0 : Efab) :
    hartConf i (WeakRvwmoConfWit2.ldRow t w) (WeakRvwmoConfWit2.ldP0 cpu rs ib) (fun _ => d0)
      (ldEm t w cpu rs ib) :=
  hemit.HEone (dv := fun _ => d0) 0 wsInit
    (.LLoad false (paZ evFlag) (ldTs t) (WeakRvwmoConfWit2.ldVs w)) []
    (WeakRvwmoConfWit2.ldP0 cpu rs ib) [] (WeakRvwmoConfWit2.ldP0 cpu rs ib) d0 (ldWl t w)
    (WeakRvwmoConfWit2.ldP1 w cpu rs ib) [] (WeakRvwmoConfWit2.ldP1 w cpu rs ib)
    (.ARnil _ _) (ldRealizes t w cpu rs ib wsInit) (ldPstep t w cpu rs ib d0) (.HEnil _ _ _)

theorem ldEmDevfree (t : Nat) (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch) :
    emDevfree (ldEm t w cpu rs ib) := by
  simp [emDevfree, emLabels, ldEm, ldWl]

/-- (Lean-only, deviation 4) the emission has no fetch item, so its fetches are pinned to any
image vacuously. -/
theorem WeakRvwmoConfWit2.ldEmFetchImg (im : Image) (t : Nat) (w : BitVec 32) (cpu : CPU)
    (rs : RegFile) (ib : Ibch) : emFetchImg im (ldEm t w cpu rs ib) := by
  intro l hl
  simp only [emLabels, ldEm, List.map_cons, List.map_nil, List.mem_singleton] at hl
  subst hl
  trivial

/-- (Lean-only, deviation 4) … and so has the store witness's. -/
theorem WeakRvwmoConfWit2.evEmFetchImg (im : Image) (cpu : CPU) (rs : RegFile) (ib : Ibch) :
    emFetchImg im (evEm cpu rs ib) := by
  intro l hl
  simp only [emLabels, evEm, List.map_cons, List.map_nil, List.mem_singleton] at hl
  subst hl
  trivial

/-! ## 2. THE ROW-DEPS OF A ONE-EVENT EMISSION ARE EMPTY -/

theorem rowDepsSingle (it : Eitem) (jk : Nat × Nat) :
    it.2 = some 0 → jk ∈ rowDeps [it] → False := by
  intro hit hjk
  have hlt := rowDepsLt _ _ hjk
  obtain ⟨it', hin, htg, _⟩ := rowDepsTgt _ _ hjk
  rw [List.mem_singleton] at hin
  subst hin
  rw [hit] at htg
  have := Option.some.inj htg
  omega

theorem evRowDepsEmpty (cpu : CPU) (rs : RegFile) (ib : Ibch) (jk : Nat × Nat) :
    jk ∈ rowDeps (evEm cpu rs ib).emItems → False :=
  rowDepsSingle (evWl ib, some 0) jk rfl

theorem ldRowDepsEmpty (t : Nat) (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch)
    (jk : Nat × Nat) : jk ∈ rowDeps (ldEm t w cpu rs ib).emItems → False :=
  rowDepsSingle (ldWl t w, some 0) jk rfl

/-! ## 3. THE TWO-HART GRAPH -/

def lbShapeOk (l : Lbl) : Prop :=
  match l with
  | .LLoad _ _ ts vs => vs.length = ts.length
  | .LStore _ _ vs _ => vs ≠ []
  | .LFence _ _ _ _ => True
  | .LRmw _ _ _ ts rvs wvs _ => wvs ≠ [] ∧ wvs.length = ts.length ∧ rvs.length = ts.length
  | .LIo .. => True

section G2

variable (im : Image) (r0 r1 : Lbl) (mo : List Geid)

local notation "G" => Gexec.mk im [[r0], [r1]] mo

theorem g2Lbl (e : Geid) (l : Lbl) :
    gxLbl G e = some l → (e = (0, 0) ∧ l = r0) ∨ (e = (1, 0) ∧ l = r1) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | k <;> simp [gxLbl] at hl <;> subst hl <;> simp

theorem g2Lbl0 : gxLbl G (0, 0) = some r0 := rfl
theorem g2Lbl1 : gxLbl G (1, 0) = some r1 := rfl

theorem g2Pos0 (e : Geid) : (gxLbl G e).isSome = true → e.2 = 0 := by
  intro h
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
  rcases g2Lbl im r0 r1 mo e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl

theorem g2Nogpo (e1 e2 : Geid) : ¬ WeakRvwmoGraph.gpo G e1 e2 := by
  rintro ⟨_, hlt, h1, h2⟩
  rw [g2Pos0 im r0 r1 mo e1 h1, g2Pos0 im r0 r1 mo e2 h2] at hlt
  omega

theorem g2Noppo (e1 e2 : Geid) : ¬ gppo G e1 e2 := by
  rintro (hpl | hf | ha | hr)
  · exact g2Nogpo im r0 r1 mo e1 e2 hpl.1
  · obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, _, h2, _⟩, _, h2r⟩ := hf
    have hs2 : (gxLbl G e2).isSome = true := by
      rcases h2r with ⟨⟨l, hl, _⟩, _⟩ | ⟨⟨l, hl, _⟩, _⟩ <;> rw [hl] <;> rfl
    rw [g2Pos0 im r0 r1 mo e2 hs2] at h2
    omega
  · exact g2Nogpo im r0 r1 mo e1 e2 ha.1
  · exact g2Nogpo im r0 r1 mo e1 e2 hr.1

theorem g2PpoGmo : gppoGmo G := fun e1 e2 h => absurd h (g2Noppo im r0 r1 mo e1 e2)

theorem g2Gwf :
    mo.Nodup →
    (∀ e : Geid, e ∈ mo ↔ (e = (0, 0) ∨ e = (1, 0))) →
    lbIsMem r0 = true → lbIsMem r1 = true →
    lbShapeOk r0 → lbShapeOk r1 →
    gwf G := by
  intro hnd hmo hm0 hm1 hs0 hs1
  refine ⟨hnd, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      rcases (hmo e).1 he with rfl | rfl
      · exact ⟨r0, rfl, hm0⟩
      · exact ⟨r1, rfl, hm1⟩
    · rintro ⟨l, hl, _⟩
      apply (hmo e).2
      rcases g2Lbl im r0 r1 mo e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp at hp <;> subst hp <;>
      rcases k with _ | k <;> simp at hk <;> subst hk
    · exact hs0
    · exact hs1

end G2

/-! ### 3.1 The era image: the flag word CLEAR -/

def mpImg : Image := fun a =>
  if paZ evFlag ≤ a ∧ a < paZ evFlag + 4 then some (nthByte (n := 4) lockZero (a - paZ evFlag).toNat)
  else none

theorem mpImgByte (j : Nat) :
    j < 4 → mpImg (accAddr (paZ evFlag) j) = some (nthByte (n := 4) lockZero j) := by
  intro hj
  unfold mpImg accAddr
  rw [if_pos (by omega), show (paZ evFlag + (j : Int) - paZ evFlag).toNat = j by omega]

/-- (Lean-only shape) the four bytes of a word, by index. -/
theorem WeakRvwmoConfWit2.ldVsLookup (w : BitVec 32) (j : Nat) (v : BitVec 8) :
    (WeakRvwmoConfWit2.ldVs w)[j]? = some v → j < 4 ∧ v = nthByte (n := 4) w j := by
  intro h
  rcases j with _ | _ | _ | _ | j <;> simp [WeakRvwmoConfWit2.ldVs] at h <;>
    first | exact ⟨by omega, h.symm⟩

theorem WeakRvwmoConfWit2.ldTsLookup (t j t' : Nat) : (ldTs t)[j]? = some t' → t' = t := by
  intro h
  rcases j with _ | _ | _ | _ | j <;> simp [ldTs] at h <;> exact h.symm

theorem WeakRvwmoConfWit2.wbytesLookupInv (w : BitVec 32) (j : Nat) (v : BitVec 8) :
    (WeakInterpProj.wbytes 4 w)[j]? = some v → j < 4 ∧ v = nthByte (n := 4) w j := by
  intro h
  have hj : j < 4 := by
    have := (List.getElem?_eq_some_iff.1 h).1
    rwa [wbytesLength] at this
  refine ⟨hj, ?_⟩
  rw [wbytesLookup 4 (m := 4) w j hj] at h
  exact (Option.some.inj h).symm

/-! ### 3.2 `mpw`: the load reads hart 0's store -/

def WeakRvwmoConfWit2.mpw : Gexec :=
  ⟨mpImg, [evRow, WeakRvwmoConfWit2.ldRow 1 lockOne], [(0, 0), (1, 0)]⟩

def mpwd : Gdexec := ⟨WeakRvwmoConfWit2.mpw, [], []⟩

theorem mpwGwrites : gwrites WeakRvwmoConfWit2.mpw = [(0, 0)] := by decide
theorem mpwGwix0 : gwix WeakRvwmoConfWit2.mpw (0, 0) = 1 := by decide
theorem mpwWriteAt1 : gwriteAt WeakRvwmoConfWit2.mpw 1 = some (0, 0) := by decide

theorem mpwWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte WeakRvwmoConfWit2.mpw e a v →
    e = (0, 0) ∧ ∃ j : Nat, j < 4 ∧ a = accAddr (paZ evFlag) j ∧
      v = nthByte (n := 4) lockOne j := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases g2Lbl mpImg _ _ _ e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    obtain ⟨hj, rfl⟩ := WeakRvwmoConfWit2.wbytesLookupInv lockOne j v hv
    exact ⟨rfl, j, hj, ha.symm, rfl⟩
  · simp [lbWr] at hwr

theorem mpwRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte WeakRvwmoConfWit2.mpw e a t v →
    e = (1, 0) ∧ t = 1 ∧ ∃ j : Nat, j < 4 ∧ a = accAddr (paZ evFlag) j ∧
      v = nthByte (n := 4) lockOne j := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases g2Lbl mpImg _ _ _ e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    obtain ⟨hj, rfl⟩ := WeakRvwmoConfWit2.ldVsLookup lockOne j v hv
    exact ⟨rfl, WeakRvwmoConfWit2.ldTsLookup 1 j t ht, j, hj, ha.symm, rfl⟩

theorem mpwGvis0 : gvisible WeakRvwmoConfWit2.mpw (0, 0) (1, 0) :=
  Or.inl ⟨by decide, by decide, by decide⟩

theorem mpwConsistent : rvwmoMinusConsistent WeakRvwmoConfWit2.mpw := by
  refine ⟨?_, g2PpoGmo mpImg _ _ _, ?_, ?_⟩
  · refine g2Gwf mpImg (.LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain)
      (.LLoad false (paZ evFlag) (ldTs 1) (WeakRvwmoConfWit2.ldVs lockOne)) _ (by decide) ?_ rfl rfl
      (wbytesNonnil 4 lockOne (by decide)) rfl
    intro e
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  · intro e a t v hrd
    obtain ⟨rfl, rfl, j, hj, rfl, rfl⟩ := mpwRd e a t v hrd
    refine ⟨⟨(0, 0), mpwWriteAt1, ⟨_, paZ evFlag, WeakInterpProj.wbytes 4 lockOne, j, rfl, rfl,
      wbytesLookup 4 (m := 4) lockOne j hj, rfl⟩, mpwGvis0⟩, ?_⟩
    intro w' v' hw' _
    obtain ⟨rfl, _⟩ := mpwWr w' _ v' hw'
    rw [mpwGwix0]
    exact Nat.le_refl _
  · intro e a t v hrd hw
    obtain ⟨rfl, _⟩ := mpwRd e a t v hrd
    obtain ⟨l, hl, hlw⟩ := hw
    have hl0 : gxLbl WeakRvwmoConfWit2.mpw (1, 0) =
        some (.LLoad false (paZ evFlag) (ldTs 1) (WeakRvwmoConfWit2.ldVs lockOne)) := rfl
    rw [hl0] at hl
    cases hl
    simp [lbIsW] at hlw

theorem mpwDepsConsistent : rvwmoMinusDepsConsistent mpwd :=
  ⟨mpwConsistent, fun _ h => by simp [mpwd] at h, fun _ h => by simp [mpwd] at h⟩

/-! ### 3.3 THE CONFORMANCE BUNDLE — the first with TWO nonempty rows -/

noncomputable def mpBoot (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (ib0 ib1 : Ibch) :
    Nat → Pexv6 := fun i =>
  match i with
  | 0 => evP0 cpu0 rs0 ib0
  | 1 => WeakRvwmoConfWit2.ldP0 cpu1 rs1 ib1
  | _ => .PDisk none

theorem mpwQconf (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (ib0 ib1 : Ibch) (d0 : Efab) :
    gdexecQconf (mpBoot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mpImg 2 mpwd := by
  refine ⟨rfl, by decide, ?_⟩
  intro i row hrow
  rcases i with _ | _ | i
  · obtain rfl : evRow = row := Option.some.inj hrow
    exact ⟨evEm cpu0 rs0 ib0, evHartConf _ _ _ _ _, evEmDevfree _ _ _,
      WeakRvwmoConfWit2.evEmFetchImg _ _ _ _,
      fun jk hjk => (evRowDepsEmpty cpu0 rs0 ib0 jk hjk).elim⟩
  · obtain rfl : WeakRvwmoConfWit2.ldRow 1 lockOne = row := Option.some.inj hrow
    exact ⟨ldEm 1 lockOne cpu1 rs1 ib1, ldHartConf _ _ _ _ _ _ _, ldEmDevfree _ _ _ _ _,
      WeakRvwmoConfWit2.ldEmFetchImg _ _ _ _ _ _,
      fun jk hjk => (ldRowDepsEmpty 1 lockOne cpu1 rs1 ib1 jk hjk).elim⟩
  · simp [mpwd, WeakRvwmoConfWit2.mpw] at hrow

/-! ## 4. THE EARLY-READ VARIANT: the load sees the era image -/

def mpw' : Gexec :=
  ⟨mpImg, [evRow, WeakRvwmoConfWit2.ldRow 0 lockZero], [(1, 0), (0, 0)]⟩

def mpwd' : Gdexec := ⟨mpw', [], []⟩

theorem mpw'Gwrites : gwrites mpw' = [(0, 0)] := by decide
theorem mpw'Gwix0 : gwix mpw' (0, 0) = 1 := by decide

theorem mpw'Wr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte mpw' e a v →
    e = (0, 0) ∧ ∃ j : Nat, j < 4 ∧ a = accAddr (paZ evFlag) j ∧
      v = nthByte (n := 4) lockOne j := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases g2Lbl mpImg _ _ _ e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    obtain ⟨hj, rfl⟩ := WeakRvwmoConfWit2.wbytesLookupInv lockOne j v hv
    exact ⟨rfl, j, hj, ha.symm, rfl⟩
  · simp [lbWr] at hwr

theorem mpw'Rd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte mpw' e a t v →
    e = (1, 0) ∧ t = 0 ∧ ∃ j : Nat, j < 4 ∧ a = accAddr (paZ evFlag) j ∧
      v = nthByte (n := 4) lockZero j := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases g2Lbl mpImg _ _ _ e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    obtain ⟨hj, rfl⟩ := WeakRvwmoConfWit2.ldVsLookup lockZero j v hv
    exact ⟨rfl, WeakRvwmoConfWit2.ldTsLookup 0 j t ht, j, hj, ha.symm, rfl⟩

/-- THE POINT of the variant: the store is NOT visible to the load — it is gmo-LATER and
cross-hart. -/
theorem mpw'Novis : ¬ gvisible mpw' (0, 0) (1, 0) := by
  rintro (⟨_, _, hlt⟩ | ⟨h, _⟩)
  · revert hlt
    decide
  · cases h

theorem mpw'Consistent : rvwmoMinusConsistent mpw' := by
  refine ⟨?_, g2PpoGmo mpImg _ _ _, ?_, ?_⟩
  · refine g2Gwf mpImg (.LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain)
      (.LLoad false (paZ evFlag) (ldTs 0) (WeakRvwmoConfWit2.ldVs lockZero)) _ (by decide) ?_ rfl
      rfl (wbytesNonnil 4 lockOne (by decide)) rfl
    intro e
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Or.comm
  · intro e a t v hrd
    obtain ⟨rfl, rfl, j, hj, rfl, rfl⟩ := mpw'Rd e a t v hrd
    refine ⟨mpImgByte j hj, ?_⟩
    intro w' v' hw' hvis
    obtain ⟨rfl, _⟩ := mpw'Wr w' _ v' hw'
    exact absurd hvis mpw'Novis
  · intro e a t v hrd hw
    obtain ⟨rfl, _⟩ := mpw'Rd e a t v hrd
    obtain ⟨l, hl, hlw⟩ := hw
    have hl0 : gxLbl mpw' (1, 0) =
        some (.LLoad false (paZ evFlag) (ldTs 0) (WeakRvwmoConfWit2.ldVs lockZero)) := rfl
    rw [hl0] at hl
    cases hl
    simp [lbIsW] at hlw

theorem mpw'DepsConsistent : rvwmoMinusDepsConsistent mpwd' :=
  ⟨mpw'Consistent, fun _ h => by simp [mpwd'] at h, fun _ h => by simp [mpwd'] at h⟩

theorem mpw'Qconf (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (ib0 ib1 : Ibch) (d0 : Efab) :
    gdexecQconf (mpBoot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mpImg 2 mpwd' := by
  refine ⟨rfl, by decide, ?_⟩
  intro i row hrow
  rcases i with _ | _ | i
  · obtain rfl : evRow = row := Option.some.inj hrow
    exact ⟨evEm cpu0 rs0 ib0, evHartConf _ _ _ _ _, evEmDevfree _ _ _,
      WeakRvwmoConfWit2.evEmFetchImg _ _ _ _,
      fun jk hjk => (evRowDepsEmpty cpu0 rs0 ib0 jk hjk).elim⟩
  · obtain rfl : WeakRvwmoConfWit2.ldRow 0 lockZero = row := Option.some.inj hrow
    exact ⟨ldEm 0 lockZero cpu1 rs1 ib1, ldHartConf _ _ _ _ _ _ _, ldEmDevfree _ _ _ _ _,
      WeakRvwmoConfWit2.ldEmFetchImg _ _ _ _ _ _,
      fun jk hjk => (ldRowDepsEmpty 0 lockZero cpu1 rs1 ib1 jk hjk).elim⟩
  · simp [mpwd', mpw'] at hrow

/-! ## 5. THE SUPPLY — `execProgOk'` for the two-hart candidate -/

def mpSt : Estep :=
  ⟨0, .LStore false (paZ evFlag) (WeakInterpProj.wbytes 4 lockOne) .WCplain⟩
def mpLd : Estep :=
  ⟨1, .LLoad false (paZ evFlag) (ldTs 1) (WeakRvwmoConfWit2.ldVs lockOne)⟩

def mpCand : Cand := ⟨mpImg, [mpSt, mpLd]⟩

def WeakRvwmoConfWit2.mpRows : Nat → List Lbl := fun i =>
  match i with
  | 0 => evRow
  | 1 => WeakRvwmoConfWit2.ldRow 1 lockOne
  | _ => []

theorem mpCandRows (i : Nat) :
    (mpCand.cdTr.filter (fun s => decide (s.esAg = i))).map (fun s => s.esLb) =
      WeakRvwmoConfWit2.mpRows i := by
  rcases i with _ | _ | i
  · rfl
  · rfl
  · simp [mpCand, mpSt, mpLd, WeakRvwmoConfWit2.mpRows]

theorem mpSupply (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (ib0 ib1 : Ibch) (d0 : Efab) :
    ∃ pst : Nat → List Pexv6,
      pst 0 = (List.range' 0 2).map (mpBoot cpu0 cpu1 rs0 rs1 ib0 ib1) ∧
      execProgOk' (pstepPin mpCand.cdImg pstepEv) pclsEv pst (fun _ => d0) (candExec mpCand) := by
  refine supplyOfQconf mpCand (mpBoot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 WeakRvwmoConfWit2.mpRows 2
    mpCandRows ?_ ?_
  · intro i hi
    rcases i with _ | _ | i
    · omega
    · omega
    · rfl
  · intro i hi
    rcases i with _ | _ | i
    · exact ⟨evEm cpu0 rs0 ib0, evHartConf _ _ _ _ _, WeakRvwmoConfWit2.evEmFetchImg _ _ _ _⟩
    · exact ⟨ldEm 1 lockOne cpu1 rs1 ib1, ldHartConf _ _ _ _ _ _ _,
        WeakRvwmoConfWit2.ldEmFetchImg _ _ _ _ _ _⟩
    · omega

end Weak
