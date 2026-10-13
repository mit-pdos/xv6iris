/-
Weak: **THE `racyD`-CYCLE WITNESS, AND THE WALK RUN ON IT** (route B).

Rocq: `iris/WeakRvwmoCycWit.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Design `claude-notes/design/weak-memory-route-b.md` §4e/§4f.  `WeakRvwmoWalk` reduces (R-2)
`walkSupply` to a per-state certification policy; a reduction is only worth its statement if it
is INHABITED at the shape the consumer meets — an `racyD`-CYCLE graph.  This file builds one and
RUNS THE WALK ON IT.

REAL (the kernel's own): the access kinds, widths, `va`/`translation`/`tag` of both requests are
`WeakEvStarted.evReqw` (the `sw &started` of `main`) and `WeakRvwmoConfWit2.ldReql` (the
`lw a5,0(a4)` at `main+0x16`) with ONLY the physical address changed; the stored value
`lockOne`; one address IS `&started`; every step relation, projection and consistency lemma is
the tree's.  HAND-BUILT: the three-node monad fragment `cyM` (a `memRead` whose continuation
ignores the value, an `instrAnnounce`, a `memWrite`) — no xv6 path has the LB shape, and the
real code's load is followed by ~117 administrative nodes and a FETCH before its next memory
event (`WeakRvwmoAdm` §3; under Stage C that fetch is literally one more ADMINISTRATIVE node,
an `LIFetch` admin label pinned to the boot image, not a graph event); bridging that stretch is
`admRun`'s job.  The second address is `&started + 8`.

  §1  the hand-built block: the fragment, its steps and projections; §1.6 the node is PINNED
      (no admin step moves `cyM`) and the substitution RE-CONVERGES (`cyBlkSubst`).
  §2  `cyHartConf` — a two-event row (load, store) with EMPTY `rowDeps` (the announce resets
      the dataflow's `dsLd`).
  §3  THE GRAPH `cyg`: LB, gmo `[sw B; lw B; sw A; lw A]`, consistent, `gdexecQconf`, and a real
      `racyD` CYCLE (`cygCycle`); the era image holds ZERO so the substituted read really
      returns DIFFERENT values (`cygValuesDiffer`).
  §4  THE WALK, RUN: four certified steps, two `segStep`s, two `wlkStep`s, and `cygWalk` —
      `walkSupply`'s conclusion at `cyg`.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below), as `WeakRvwmoWalk` deviation 1 (`regstate` ↦
   `RegFile`, `oib32` ↦ `Ibch`, `dev_state` ↦ `Efab` — `DevStates` at the `pnodeStep` tier —,
   `agent` ↦ `Nat`, `wreg` ↦ `Nat`, `M unit` ↦ `SailM Unit`, `Arch.pa` ↦ `PAddr`, `pa_z` ↦
   `paZ`, `EStep`/`WMsg`/`CSt`/`SegOut`/`Cand`/`GExec` ↦ anonymous constructors, `tvs.*1/.*2` ↦
   `tvs.map Prod.fst/snd`, `is_Some o` ↦ `o.isSome = true`, `seq 0 2` ↦ `List.range' 0 2`,
   `Interface.WriteReq.make … ev_reqw` ↦ the structure update `{ evReqw with pa := a }`,
   `bv_to_bvn (Z_to_bv 32 0)` ↦ `0#32` announced at width 32).  The Rocq `Section walkrun`
   context (`cpu0 cpu1 rs0 rs1 d0`) and its notation `boot` are explicit parameters
   (`cyBoot cpu0 cpu1 rs0 rs1`); defs/theorems take only the ones they use.
2. KERNEL DRIFT: the Lean image's `started` is `0x8000a400`, so `zAVal`/`zBVal` read
   `2147525632`/`2147525640` (Rocq `2147525168`/`2147525176`).
3. THE MONAD: Lean's `pnodeStep` carries the barrier output `obar`; `cyMStepInv` also concludes
   `obar = none`, and `cyMAdmStep` is over `pstepHw`'s three arms (with `obar`).  The read node's
   continuation receives a `Result`; `cyM2 = .pure ()` (Lean's boundary node; the emission ends
   there as in Rocq).  `cyPstepLd`/`cyPstepLd'` are proved from the arbitrary-state
   `cyPstepLdAny` (Rocq re-runs the same script three times).
4. O2 / STAGE C (`notes/weak-port-o2-stageC.md`): the program LTS of a cycle state is PINNED, so
   `cwProg0..4` are `execProgOk'` at `pstepPin cwCk.cdImg pstepEv` (Rocq: `pstep_ev`), via the
   pinned `execProgOk'Snoc` (the only admin label, `LInstr`, is pinned trivially);
   `gdexecQconf`'s `emFetchImg` slot is discharged by the Lean-only
   `WeakRvwmoCycWit.cyEmFetchImg` (no fetch item).  `cyBlkSubst` keeps Rocq's plain `cblk`;
   it is the instance at `lbAdmin true` of the Lean-only generic
   `WeakRvwmoCycWit.cyBlkSubstG` (any admin sub-alphabet), whose other instance
   `WeakRvwmoCycWit.cyBlkSubstPin` is the PINNED block (`WeakRvwmoCert2.cblkPin im`, `∀ im`) —
   the shape `WeakRvwmoWalk`'s `wwitNd` now asks for.
5. `cyRowDepsEmpty`'s `vm_compute` is `rfl`; the closed computations (`cwLb0Ts`, `cwLb2Eq`'s
   two halves, `cwBytes2`, `cygValuesDiffer`) are `decide +kernel`.
6. §5's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).

**Rocq → Lean name map.**  `cy_A` `cyA`, `cy_B` `cyB`, `cy_wreq` `cyWreq`, `cy_rreq` `cyRreq`,
`cy_wreq_plain` `cyWreqPlain`, `cy_rreq_plain` `cyRreqPlain`, `cy_wreq_val` `cyWreqVal`,
`cy_A_ram` `cyARam`, `cy_B_ram` `cyBRam`, `zA` `zA`, `zB` `zB`, `zA_val` `zAVal`, `zB_val`
`zBVal`, `cy_ob` `cyOb`, `cy_ib1` `cyIb1`, `cy_m2` `cyM2`, `cy_m1` `cyM1`, `cy_ma` `cyMa`, `cy_m`
`cyM`, `cy_p0` `cyP0`, `cy_pa` `cyPa`, `cy_p1` `cyP1`, `cy_p2` `cyP2`, `cy_bytes` `cyBytes`,
`cy_bytes_ne` `cyBytesNe`, `cy_bytes_nth` `cyBytesNth`, `cy_tvs` `cyTvs`, `cy_wl_ld` `cyWlLd`,
`cy_wl_ld'` `cyWlLd'`, `cy_wl_ld_eq` `cyWlLdEq`, `cy_wl_st` `cyWlSt`, `cy_tvs_fst` `cyTvsFst`,
`cy_tvs_snd` `cyTvsSnd`, `cy_tvs_len` `cyTvsLen`, `cy_pstep_ld` `cyPstepLd`, `cy_pstep_ld'`
`cyPstepLd'`, `cy_node_vindep` `cyNodeVindep`, `cy_pstep_ann` `cyPstepAnn`, `cy_pstep_st`
`cyPstepSt`, `cy_realizes_ld` `cyRealizesLd`, `cy_realizes_ld'` `cyRealizesLd'`,
`cy_realizes_st` `cyRealizesSt`, `cy_realizes_ld_any` `cyRealizesLdAny`, `cy_m_step_inv`
`cyMStepInv`, `cy_m_adm_step` `cyMAdmStep`, `cy_m_adm_fix` `cyMAdmFix`, `cy_pstep_ld_any`
`cyPstepLdAny`, `cy_blk_subst` `cyBlkSubst`, `cy_row` `cyRow`, `cy_em` `cyEm`,
`cy_relp_after_load` `cyRelpAfterLoad`, `cy_hart_conf` `cyHartConf`, `cy_em_devfree`
`cyEmDevfree`, `cy_row_deps_empty` `cyRowDepsEmpty`, `cy_ts2` `cyTs2`, `cy_ts1` `cyTs1`,
`cy_img` `cyImg`, `cyg` `cyg`, `cygd` `cygd`, `cyg_lbl` `cygLbl`, `cyg_pos` `cygPos`,
`cy_bytes_len` `cyBytesLen`, `cy_ranges_disj` `cyRangesDisj`, `cyg_wr` `cygWr`, `cyg_rd`
`cygRd`, `cyg_gwrites` `cygGwrites`, `cyg_at1/2` `cygAt1/2`, `cyg_wix1/2` `cygWix1/2`,
`cyg_gmo_20` `cygGmo20`, `cyg_gmo_01` `cygGmo01`, `cyg_gwf` `cygGwf`, `cyg_acc` `cygAcc`,
`cyg_noppo` `cygNoppo`, `cyg_consistent` `cygConsistent`, `cyg_deps_consistent`
`cygDepsConsistent`, `cy_boot` `cyBoot`, `cyg_qconf` `cygQconf`, `cyg_gpow0/1` `cygGpow0/1`,
`cyg_grf0/1` `cygGrf0/1`, `cyg_cycle` `cygCycle`, `cyg_segments` `cygSegments`, `boot` (a
notation) ↦ `cyBoot cpu0 cpu1 rs0 rs1`, `cw_c0..4` `cwC0..4`, `cw_lb0..3` `cwLb0..3`, `cw_log0`
`cwLog0`, `cw_log2` `cwLog2`, `cw_lb0_tvs` `cwLb0Tvs`, `cw_tvs0_len` `cwTvs0Len`, `cw_lb0_ts`
`cwLb0Ts`, `cw_lb2_eq` `cwLb2Eq`, `cw_c0..4_cons` `cwC0..4Cons`, `cw_bytes0` `cwBytes0`,
`cw_bytes2` `cwBytes2`, `cw_relp0` `cwRelp0`, `cw_relp0_1` `cwRelp0_1`, `cw_relp1` `cwRelp1`,
`cw_relp3` `cwRelp3`, `cw_pst0..4` `cwPst0..4`, `cw_dv0..4` `cwDv0..4`, `cw_prog0..4`
`cwProg0..4`, `cw_S0/2/4` `cwS0/2/4`, `cyg_values_differ` `cygValuesDiffer`, `cw_lb0_ne_row`
`cwLb0NeRow`, `cw_o0/1` `cwO0/1`, `cw_S0/2/4_ok` `cwS0/2/4Ok`, `cw_seg0/1` `cwSeg0/1`,
`cw_gmsg1/2` `cwGmsg1/2`, `cw_step0/1` `cwStep0/1`, `cw_inv0/2/4` `cwInv0/2/4`, `cw_pfx2/4`
`cwPfx2/4`, `cw_log4` `cwLog4`, `cyg_walk` `cygWalk`.

**File-qualified names:** none of this file's Rocq names is in `notes/weak-port-dupnames.json`;
Lean-only: `WeakRvwmoCycWit.cyRreqPa`, `WeakRvwmoCycWit.cyWreqPa` (the address projections,
`rfl`), `WeakRvwmoCycWit.cyBlkSubstG`, `WeakRvwmoCycWit.cyBlkSubstPin`,
`WeakRvwmoCycWit.cyEmFetchImg` (deviation 4).

**Dropped:** nothing (Rocq 149 declarations + the notation `boot`; Lean 149 + 5 Lean-only).
-/
import Weak.WeakRvwmoWalk
import Weak.WeakRvwmoConfWit2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. THE HAND-BUILT TWO-EVENT BLOCK -/

/-! ## 1.1 The two addresses, and the requests -/

def cyA : PAddr := evFlag
def cyB : PAddr := BitVec.ofNat 64 (KernelSyms.«started» + 8)

/-- Every field of the REAL `sw &started` request but the address. -/
noncomputable def cyWreq (a : PAddr) : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  { evReqw with pa := a }

/-- Every field of the REAL `lw a5,0(a4)` request but the address. -/
noncomputable def cyRreq (a : PAddr) : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  { ldReql with pa := a }

theorem WeakRvwmoCycWit.cyWreqPa (a : PAddr) : (cyWreq a).pa = a := rfl
theorem WeakRvwmoCycWit.cyRreqPa (a : PAddr) : (cyRreq a).pa = a := rfl

theorem cyWreqPlain (a : PAddr) :
    classify (cyWreq a).access_kind = ⟨false, false, false⟩ := evStorePlain

theorem cyRreqPlain (a : PAddr) :
    classify (cyRreq a).access_kind = ⟨false, false, false⟩ := ldLoadPlain

theorem cyWreqVal (a : PAddr) : (cyWreq a).value = some lockOne := evStoreVal

theorem cyARam : devAddr cyA = false := by
  unfold cyA
  rw [← evStorePa]
  exact evStoreRam

theorem cyBRam : devAddr cyB = false := by decide +kernel

def zA : Int := paZ cyA
def zB : Int := paZ cyB

theorem zAVal : zA = 2147525632 := by decide +kernel
theorem zBVal : zB = 2147525640 := by decide +kernel

/-! ## 1.2 The node fragment

A `memRead` whose continuation IGNORES the value, an `instrAnnounce` (the instruction BOUNDARY
that resets the dataflow's `dsLd`, so `rowDeps` carries no `(0,1)` edge — an ADMINISTRATIVE
node, living in the second block's `admRun`), and a `memWrite`. -/

def cyOb : BitVec 32 := 0#32
def cyIb1 : Ibch := ibAnn (ibOfBvn cyOb)

def cyM2 : SailM Unit := .pure ()

noncomputable def cyM1 (aS : PAddr) : SailM Unit :=
  .impure (.ok (.memWrite 4 64 (cyWreq aS))) (fun _ => cyM2)

noncomputable def cyMa (aS : PAddr) : SailM Unit :=
  .impure (.ok (.instrAnnounce 32 cyOb)) (fun _ => cyM1 aS)

noncomputable def cyM (aL aS : PAddr) : SailM Unit :=
  .impure (.ok (.memRead 4 64 (cyRreq aL))) (fun _ => cyMa aS)

noncomputable def cyP0 (aL aS : PAddr) (cpu : CPU) (rs : RegFile) : Pexv6 :=
  .PHart cpu (cyM aL aS) rs none ibNone
noncomputable def cyPa (aS : PAddr) (cpu : CPU) (rs : RegFile) : Pexv6 :=
  .PHart cpu (cyMa aS) rs none ibNone
noncomputable def cyP1 (aS : PAddr) (cpu : CPU) (rs : RegFile) : Pexv6 :=
  .PHart cpu (cyM1 aS) rs none cyIb1
def cyP2 (cpu : CPU) (rs : RegFile) : Pexv6 :=
  .PHart cpu cyM2 rs none cyIb1

/-! ## 1.3 The bytes, and the three labels -/

def cyBytes : List (BitVec 8) := WeakInterpProj.wbytes 4 lockOne

theorem cyBytesLen : cyBytes.length = 4 := wbytesLength 4 lockOne

theorem cyBytesNe : cyBytes ≠ [] := wbytesNonnil 4 lockOne (by decide)

theorem cyBytesNth (j : Nat) : j < 4 → cyBytes[j]? = some (nthByte (n := 4) lockOne j) :=
  wbytesLookup 4 (m := 4) lockOne j

/-- The read's per-byte answer list, at a chosen source index. -/
def cyTvs (ts : List Nat) : List (Nat × BitVec 8) := List.zip ts cyBytes

def cyWlLd (a : PAddr) (ts : List Nat) : Wlabel :=
  .LLoad false false (paZ a) (cyTvs ts) []

/-- THE LOAD'S wlabel AT ARBITRARY ANSWERS (the substituted read answers with the image's
bytes). -/
def cyWlLd' (a : PAddr) (tvs : List (Nat × BitVec 8)) : Wlabel :=
  .LLoad false false (paZ a) tvs []

theorem cyWlLdEq (a : PAddr) (ts : List Nat) : cyWlLd a ts = cyWlLd' a (cyTvs ts) := rfl

def cyWlSt (a : PAddr) : Wlabel :=
  .LStore false (paZ a) (WeakInterpProj.wbytes 4 lockOne)
    (depsAsrc (depsOfIb cyIb1.ibBits)) (depsVsrc (depsOfIb cyIb1.ibBits))

theorem cyTvsFst (ts : List Nat) : ts.length = 4 → (cyTvs ts).map Prod.fst = ts := by
  intro hl
  unfold cyTvs
  exact List.map_fst_zip (by rw [hl, cyBytesLen]; exact Nat.le_refl _)

theorem cyTvsSnd (ts : List Nat) : ts.length = 4 → (cyTvs ts).map Prod.snd = cyBytes := by
  intro hl
  unfold cyTvs
  exact List.map_snd_zip (by rw [hl, cyBytesLen]; exact Nat.le_refl _)

theorem cyTvsLen (ts : List Nat) : ts.length = 4 → (cyTvs ts).length = 4 := by
  intro hl
  unfold cyTvs
  rw [List.length_zip, hl, cyBytesLen]
  rfl

/-! ## 1.4 The three steps -/

/-- The load step at an ARBITRARY register file and channel. -/
theorem cyPstepLdAny (aL aS : PAddr) (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab)
    (tvs : List (Nat × BitVec 8)) :
    devAddr aL = false → tvs.length = 4 →
    pstepEv (.PHart cpu (cyM aL aS) rs none ib) d (cyWlLd' aL tvs)
      (.PHart cpu (cyMa aS) rs none ib) d := by
  intro hram hlen
  obtain ⟨w, hw⟩ := bvOfBytes 4 (tvs.map Prod.snd) (by rw [List.length_map, hlen])
  refine ⟨rfl, none, none, none, rfl, rfl, Or.inl ⟨?_, rfl⟩⟩
  simp only [pstepNode, pnodeStep, cyM, WeakRvwmoCycWit.cyRreqPa, hram, Bool.false_eq_true,
    if_false]
  refine Or.inr ⟨by rw [cyRreqPlain], Or.inl ⟨by rw [cyRreqPlain], w, tvs, hlen, hw, ?_,
    trivial, trivial, trivial, trivial, trivial, trivial⟩⟩
  rw [cyRreqPlain]
  rfl

theorem cyPstepLd' (aL aS : PAddr) (cpu : CPU) (rs : RegFile) (d : Efab)
    (tvs : List (Nat × BitVec 8)) :
    devAddr aL = false → tvs.length = 4 →
    pstepEv (cyP0 aL aS cpu rs) d (cyWlLd' aL tvs) (cyPa aS cpu rs) d :=
  cyPstepLdAny aL aS cpu rs ibNone d tvs

theorem cyPstepLd (aL aS : PAddr) (cpu : CPU) (rs : RegFile) (d : Efab) (ts : List Nat) :
    devAddr aL = false → ts.length = 4 →
    pstepEv (cyP0 aL aS cpu rs) d (cyWlLd aL ts) (cyPa aS cpu rs) d :=
  fun hram hts => cyPstepLd' aL aS cpu rs d (cyTvs ts) hram (cyTvsLen ts hts)

/-- THE VALUE-INDEPENDENCE, STATED: two answer lists of the read's own width, the SAME
successor node. -/
theorem cyNodeVindep (aL aS : PAddr) (cpu : CPU) (rs : RegFile) (d : Efab)
    (tvs tvs2 : List (Nat × BitVec 8)) :
    devAddr aL = false → tvs.length = 4 → tvs2.length = 4 →
    pstepEv (cyP0 aL aS cpu rs) d (cyWlLd' aL tvs) (cyPa aS cpu rs) d ∧
    pstepEv (cyP0 aL aS cpu rs) d (cyWlLd' aL tvs2) (cyPa aS cpu rs) d :=
  fun hram h1 h2 => ⟨cyPstepLd' aL aS cpu rs d tvs hram h1, cyPstepLd' aL aS cpu rs d tvs2 hram h2⟩

theorem cyPstepAnn (aS : PAddr) (cpu : CPU) (rs : RegFile) (d : Efab) :
    pstepEv (cyPa aS cpu rs) d .LInstr (cyP1 aS cpu rs) d :=
  ⟨rfl, none, some cyIb1, none, rfl, rfl,
    Or.inl ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩

theorem cyPstepSt (aS : PAddr) (cpu : CPU) (rs : RegFile) (d : Efab) :
    devAddr aS = false →
    pstepEv (cyP1 aS cpu rs) d (cyWlSt aS) (cyP2 cpu rs) d := by
  intro hram
  refine ⟨rfl, none, none, none, rfl, rfl, Or.inl ⟨?_, rfl⟩⟩
  simp only [pstepNode, pnodeStep, cyM1, WeakRvwmoCycWit.cyWreqPa, hram, Bool.false_eq_true,
    if_false, cyWreqVal]
  refine ⟨by decide, Or.inl ⟨by rw [cyWreqPlain], ?_, trivial, trivial, trivial, trivial, trivial,
    trivial⟩⟩
  rw [cyWreqPlain]
  rfl

/-! ## 1.5 The two projections -/

theorem cyRealizesLd (aL aS : PAddr) (cpu : CPU) (rs : RegFile) (ws : Wstate) (ts : List Nat) :
    ts.length = 4 →
    hlblRealizes (cyP0 aL aS cpu rs) ws (.LLoad false (paZ aL) ts cyBytes) (cyWlLd aL ts) := by
  intro hts
  refine ⟨trivial, rfl, rfl, ?_⟩
  show some (Lbl.LLoad false (paZ aL) ((cyTvs ts).map Prod.fst) ((cyTvs ts).map Prod.snd)) = _
  rw [cyTvsFst ts hts, cyTvsSnd ts hts]

theorem cyRealizesLd' (aL aS : PAddr) (cpu : CPU) (rs : RegFile) (ws : Wstate)
    (tvs : List (Nat × BitVec 8)) :
    hlblRealizes (cyP0 aL aS cpu rs) ws
      (.LLoad false (paZ aL) (tvs.map Prod.fst) (tvs.map Prod.snd)) (cyWlLd' aL tvs) :=
  ⟨trivial, rfl, rfl, rfl⟩

theorem cyRealizesSt (aS : PAddr) (cpu : CPU) (rs : RegFile) (ws : Wstate) :
    ws.wRelp = false →
    hlblRealizes (cyP1 aS cpu rs) ws (.LStore false (paZ aS) cyBytes .WCplain) (cyWlSt aS) := by
  intro hrel
  refine ⟨trivial, trivial, trivial, ?_⟩
  show some (Lbl.LStore false (paZ aS) cyBytes
    (wmClassOf (classify (cyWreq aS).access_kind) ws)) = _
  rw [cyWreqPlain]
  simp only [wmClassOf, hrel, Bool.false_or, Bool.false_eq_true, if_false]

/-! ## 1.6 THE NODE IS PINNED, AND THE SUBSTITUTION RE-CONVERGES -/

/-- The projection of a load's wlabel does not consult the process. -/
theorem cyRealizesLdAny (p : Pexv6) (ws : Wstate) (aL : PAddr) (tvs : List (Nat × BitVec 8)) :
    hlblRealizes p ws
      (.LLoad false (paZ aL) (tvs.map Prod.fst) (tvs.map Prod.snd)) (cyWlLd' aL tvs) :=
  ⟨trivial, rfl, rfl, rfl⟩

/-- (1) Every step out of `cyM` is the plain load, landing at `cyMa`. -/
theorem cyMStepInv (aL aS : PAddr) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m' : SailM Unit) (ors : Option RegFile) (fn' : Ofence) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    devAddr aL = false →
    pnodeStep (cyM aL aS) rs ib d l m' ors fn' d' oib obar →
    ∃ tvs : List (Nat × BitVec 8),
      tvs.length = 4 ∧ l = cyWlLd' aL tvs ∧
      m' = cyMa aS ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none := by
  intro hram hst
  simp only [pnodeStep, cyM, WeakRvwmoCycWit.cyRreqPa, hram, Bool.false_eq_true, if_false,
    cyRreqPlain] at hst
  rcases hst with ⟨hc, _⟩ | ⟨_, ⟨_, w, tvs, hlen, _, hl, hm, ho, hf, hd, hoib, hobar⟩ | ⟨hc, _⟩⟩
  · exact absurd hc (by decide)
  · exact ⟨tvs, hlen, hl, hm, ho, hf, hd, hoib, hobar⟩
  · exact absurd hc (by decide)

/-- (2) NO ADMINISTRATIVE STEP MOVES `cyM`. -/
theorem cyMAdmStep (aL aS : PAddr) (cpu : CPU) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (d : Efab) (l : Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool)
    (m1 : SailM Unit) (ors : Option RegFile) (fn1 : Ofence) (d1 : Efab) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    devAddr aL = false →
    lbAdmin true l →
    pstepHw cpu (cyM aL aS) rs fn ib d l rds wrs ann m1 ors fn1 d1 oib obar →
    m1 = cyM aL aS := by
  intro hram hadm hst
  rcases hst with ⟨rfl, ⟨hn, _⟩, _⟩ | ⟨pr, pw, sr, sw, rfl, ⟨hn, _⟩, _⟩ | ⟨hp, _⟩
  · obtain ⟨tvs, _, rfl, _⟩ := cyMStepInv aL aS rs ib d.efDev l m1 ors fn1 d1.efDev oib obar hram hn
    exact absurd hadm id
  · obtain ⟨rfl, _⟩ := hn
    exact absurd hadm id
  · obtain ⟨_, _, _, _, _, rfl, _⟩ := hp
    rfl

theorem cyMAdmFix (aL aS : PAddr) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (wrs : List Register) (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (d : Efab) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    devAddr aL = false →
    phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
    (∀ l0, l0 ∈ ls → lbAdmin true l0) →
    m = cyM aL aS → m' = cyM aL aS := by
  intro hram hrun
  induction hrun with
  | nil => intro _ hm; exact hm
  | more hstep _ ih =>
    intro hadm hm
    subst hm
    exact ih (fun l0 hl0 => hadm l0 (List.mem_cons_of_mem _ hl0))
      (cyMAdmStep aL aS cpu _ _ _ _ _ _ _ _ _ _ _ _ _ _ hram
        (hadm _ (List.mem_cons.2 (Or.inl rfl))) hstep)

/-- (3) THE SUBSTITUTION RE-CONVERGES AT ONCE, over any administrative sub-alphabet `A`
(Lean-only generalization, deviation 4). -/
theorem WeakRvwmoCycWit.cyBlkSubstG (A : Wlabel → Prop) (hA : ∀ l, A l → lbAdmin true l)
    (aL aS : PAddr) (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence)
    (ib' : Ibch) (tvs2 : List (Nat × BitVec 8)) :
    devAddr aL = false →
    tvs2.length = ts.length →
    WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base ts vs) l rds wrs (cyM aL aS) rs fn ib
      m' rs' fn' ib' →
    ∃ (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register),
      WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        l2 rds2 wrs2 (cyM aL aS) rs fn ib m' rs' fn' ib' := by
  intro hram hlen2 hblk
  obtain ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA', hre, hB,
    -, -⟩ := hblk
  have hma : ma = cyM aL aS :=
    cyMAdmFix aL aS cpu ls rdsA wrsA annA _ rs fn ib d0 ma rsa fna iba da hram hA'
      (fun l0 h => hA l0 (hadm l0 h)) rfl
  subst hma
  have hst := pevrunSingleInv l _ _ _ _
    (phrunPevrun cpu [l] rdsB wrsB annB _ rsa fna iba da m' rs' fn' ib' d0 hB)
  obtain ⟨tvs, hf, -, hshape⟩ := hlblRealizesLoadShape _ ws aq base ts vs l hre
  obtain ⟨-, ors, oib, obar, hrs, hib, hhart⟩ := hst
  have hnotd : ∀ kd ba bs sa sv, l ≠ .LDev kd ba bs sa sv := by
    rintro kd ba bs sa sv rfl
    rcases hshape with h | ⟨_, h⟩ <;> cases h
  rcases hhart with ⟨hnode, hd⟩ | hplic
  · cases fna with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, _⟩ := hnode
      rcases hshape with h | ⟨_, h⟩ <;> cases h
    | none =>
      obtain ⟨tvs0, hlen0, hl0, hm', hors, hfn', hd', hoib, -⟩ :=
        cyMStepInv aL aS rsa iba da.efDev l m' ors fn' d0.efDev oib obar hram hnode
      subst hm' hors hfn' hoib hrs hib
      have hdd : d0 = da := by rw [hd, hd']
      subst hdd
      rcases hshape with hl | ⟨_, hl⟩
      · rw [hl] at hl0
        simp only [cyWlLd', Wlabel.LLoad.injEq] at hl0
        obtain ⟨rfl, -, rfl, rfl, -⟩ := hl0
        have hlen2' : tvs2.length = 4 := by rw [hlen2, ← hf, List.length_map, hlen0]
        obtain ⟨rdsB2, wrsB2, annB2, hB2⟩ :=
          pevrunPhrun [cyWlLd' aL tvs2] _ d0 _ d0
            (pevrun.more (cyPstepLdAny aL aS cpu rs' ib' d0 tvs2 hram hlen2') (pevrun.nil _ _))
            cpu (cyM aL aS) rs' none ib' (cyMa aS) rs' none ib' rfl rfl
        exact ⟨cyWlLd' aL tvs2, rdsA ++ rdsB2, wrsA ++ wrsB2, ls, cyM aL aS, rs', none, ib', d0,
          rdsA, wrsA, annA, rdsB2, wrsB2, annB2, hadm, hA', cyRealizesLdAny _ ws aL tvs2, hB2,
          rfl, rfl⟩
      · rw [hl] at hl0
        cases hl0
  · obtain ⟨_, _, _, _, hl, _⟩ := hplic
    exact absurd hl (hnotd _ _ _ _ _)

/-- `cblk`'s instance (Rocq's statement). -/
theorem cyBlkSubst (aL aS : PAddr) (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool)
    (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel) (rds : List Nat)
    (wrs : List Register) (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit)
    (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (tvs2 : List (Nat × BitVec 8)) :
    devAddr aL = false →
    tvs2.length = ts.length →
    cblk cpu d0 ws (.LLoad aq base ts vs) l rds wrs (cyM aL aS) rs fn ib m' rs' fn' ib' →
    ∃ (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register),
      cblk cpu d0 ws (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) l2 rds2 wrs2
        (cyM aL aS) rs fn ib m' rs' fn' ib' :=
  WeakRvwmoCycWit.cyBlkSubstG (lbAdmin true) (fun _ h => h) aL aS cpu d0 ws aq base ts vs l rds
    wrs rs fn ib m' rs' fn' ib' tvs2

/-- (Lean-only, deviation 4) … and the PINNED block's, at any image. -/
theorem WeakRvwmoCycWit.cyBlkSubstPin (im : Image) (aL aS : PAddr) (cpu : CPU) (d0 : Efab)
    (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel)
    (rds : List Nat) (wrs : List Register) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (tvs2 : List (Nat × BitVec 8)) :
    devAddr aL = false →
    tvs2.length = ts.length →
    WeakRvwmoCert2.cblkPin im cpu d0 ws (.LLoad aq base ts vs) l rds wrs (cyM aL aS) rs fn ib
      m' rs' fn' ib' →
    ∃ (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register),
      WeakRvwmoCert2.cblkPin im cpu d0 ws
        (.LLoad aq base (tvs2.map Prod.fst) (tvs2.map Prod.snd)) l2 rds2 wrs2
        (cyM aL aS) rs fn ib m' rs' fn' ib' :=
  WeakRvwmoCycWit.cyBlkSubstG (WeakRvwmoCert2.lbPin im) (fun _ h => h.1) aL aS cpu d0 ws aq
    base ts vs l rds wrs rs fn ib m' rs' fn' ib' tvs2

/-! # 2. THE TWO-EVENT ROW, EMITTED -/

def cyRow (aL aS : PAddr) (ts : List Nat) : List Lbl :=
  [.LLoad false (paZ aL) ts cyBytes, .LStore false (paZ aS) cyBytes .WCplain]

def cyEm (aL aS : PAddr) (ts : List Nat) (cpu : CPU) (rs : RegFile) : Hemission :=
  ⟨[(cyWlLd aL ts, some 0), (.LInstr, none), (cyWlSt aS, some 1)], cyP2 cpu rs⟩

theorem cyRelpAfterLoad (aL : PAddr) (ts : List Nat) :
    (lblPost 0 wsInit (.LLoad false (paZ aL) ts cyBytes)).wRelp = false := by
  rw [lblPostRelp]
  rfl

theorem cyHartConf (i : Nat) (aL aS : PAddr) (ts : List Nat) (cpu : CPU) (rs : RegFile)
    (d0 : Efab) :
    devAddr aL = false → devAddr aS = false → ts.length = 4 →
    hartConf i (cyRow aL aS ts) (cyP0 aL aS cpu rs) (fun _ => d0) (cyEm aL aS ts cpu rs) := by
  intro hrL hrS hts
  exact hemit.HEone (dv := fun _ => d0) 0 wsInit (.LLoad false (paZ aL) ts cyBytes)
    [.LStore false (paZ aS) cyBytes .WCplain] (cyP0 aL aS cpu rs) [] (cyP0 aL aS cpu rs) d0
    (cyWlLd aL ts) (cyPa aS cpu rs) [(.LInstr, none), (cyWlSt aS, some 1)] (cyP2 cpu rs)
    (.ARnil _ _) (cyRealizesLd aL aS cpu rs wsInit ts hts) (cyPstepLd aL aS cpu rs d0 ts hrL hts)
    (hemit.HEone 1 (lblPost 0 wsInit (.LLoad false (paZ aL) ts cyBytes))
      (.LStore false (paZ aS) cyBytes .WCplain) [] (cyPa aS cpu rs) [.LInstr] (cyP1 aS cpu rs) d0
      (cyWlSt aS) (cyP2 cpu rs) [] (cyP2 cpu rs)
      (.ARcons _ _ .LInstr _ _ [] _ _ rfl (cyPstepAnn aS cpu rs d0) (.ARnil _ _))
      (cyRealizesSt aS cpu rs _ (cyRelpAfterLoad aL ts)) (cyPstepSt aS cpu rs d0 hrS)
      (.HEnil _ _ _))

theorem cyEmDevfree (aL aS : PAddr) (ts : List Nat) (cpu : CPU) (rs : RegFile) :
    emDevfree (cyEm aL aS ts cpu rs) := by
  simp [emDevfree, emLabels, cyEm, cyWlLd, cyWlSt]

/-- (Lean-only, deviation 4) the emission has no fetch item. -/
theorem WeakRvwmoCycWit.cyEmFetchImg (im : Image) (aL aS : PAddr) (ts : List Nat) (cpu : CPU)
    (rs : RegFile) : emFetchImg im (cyEm aL aS ts cpu rs) := by
  intro l hl
  simp only [emLabels, cyEm, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  rcases hl with rfl | rfl | rfl <;> trivial

/-- THE EMISSION CARRIES NO DEPENDENCY EDGE — computed. -/
theorem cyRowDepsEmpty (aL aS : PAddr) (ts : List Nat) (cpu : CPU) (rs : RegFile)
    (jk : Nat × Nat) : jk ∈ rowDeps (cyEm aL aS ts cpu rs).emItems → False := by
  have h : rowDeps (cyEm aL aS ts cpu rs).emItems = [] := rfl
  rw [h]
  exact List.not_mem_nil

/-! # 3. THE GRAPH: LB, WITH A REAL `racyD` CYCLE -/

def cyTs2 : List Nat := [2, 2, 2, 2]
def cyTs1 : List Nat := [1, 1, 1, 1]

/-- THE ERA IMAGE: ZERO everywhere, so the substituted read returns a DIFFERENT value from the
row's (`cygValuesDiffer`). -/
def cyImg : Image := fun _ => some 0#8

def cyg : Gexec :=
  ⟨cyImg, [cyRow cyA cyB cyTs2, cyRow cyB cyA cyTs1], [(0, 1), (1, 0), (1, 1), (0, 0)]⟩

def cygd : Gdexec := ⟨cyg, []⟩

theorem cygLbl (e : Geid) (l : Lbl) :
    gxLbl cyg e = some l →
    (e = (0, 0) ∧ l = .LLoad false zA cyTs2 cyBytes) ∨
    (e = (0, 1) ∧ l = .LStore false zB cyBytes .WCplain) ∨
    (e = (1, 0) ∧ l = .LLoad false zB cyTs1 cyBytes) ∨
    (e = (1, 1) ∧ l = .LStore false zA cyBytes .WCplain) := by
  obtain ⟨i, k⟩ := e
  intro hl
  rcases i with _ | _ | i <;> rcases k with _ | _ | k <;>
    simp [gxLbl, cyg, cyRow] at hl <;> subst hl <;> simp [zA, zB]

theorem cygPos (e : Geid) : (gxLbl cyg e).isSome = true → e.2 < 2 := by
  intro h
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
  rcases cygLbl e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- The two words are DISJOINT: `&started` and `&started + 8`. -/
theorem cyRangesDisj (j j' : Nat) :
    j < 4 → j' < 4 → accAddr zA j ≠ accAddr zB j' := by
  intro hj hj'
  unfold accAddr
  rw [zAVal, zBVal]
  omega

theorem cygWr (e : Geid) (a : Int) (v : BitVec 8) :
    gwritesByte cyg e a v →
    ∃ j : Nat, j < 4 ∧ cyBytes[j]? = some v ∧
      ((e = (0, 1) ∧ a = accAddr zB j) ∨ (e = (1, 1) ∧ a = accAddr zA j)) := by
  rintro ⟨l, base, vs, j, hl, hwr, hv, ha⟩
  rcases cygLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [lbWr] at hwr
  · simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    have hj : j < 4 := by have := lookup_lt_Some hv; rwa [cyBytesLen] at this
    exact ⟨j, hj, hv, Or.inl ⟨rfl, ha.symm⟩⟩
  · simp [lbWr] at hwr
  · simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at hwr
    obtain ⟨rfl, rfl⟩ := hwr
    have hj : j < 4 := by have := lookup_lt_Some hv; rwa [cyBytesLen] at this
    exact ⟨j, hj, hv, Or.inr ⟨rfl, ha.symm⟩⟩

theorem cygRd (e : Geid) (a : Int) (t : Nat) (v : BitVec 8) :
    greadsByte cyg e a t v →
    ∃ j : Nat, j < 4 ∧ cyBytes[j]? = some v ∧
      ((e = (0, 0) ∧ t = 2 ∧ a = accAddr zA j) ∨ (e = (1, 0) ∧ t = 1 ∧ a = accAddr zB j)) := by
  rintro ⟨l, base, ts, vs, j, hl, hrd, ht, hv, ha⟩
  rcases cygLbl e l hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    have hj : j < 4 := by have := lookup_lt_Some hv; rwa [cyBytesLen] at this
    exact ⟨j, hj, hv, Or.inl ⟨rfl, WeakRvwmoConfWit2.ldTsLookup 2 j t ht, ha.symm⟩⟩
  · simp [lbRd] at hrd
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    have hj : j < 4 := by have := lookup_lt_Some hv; rwa [cyBytesLen] at this
    exact ⟨j, hj, hv, Or.inr ⟨rfl, WeakRvwmoConfWit2.ldTsLookup 1 j t ht, ha.symm⟩⟩
  · simp [lbRd] at hrd

theorem cygGwrites : gwrites cyg = [(0, 1), (1, 1)] := by decide

theorem cygAt1 : gwriteAt cyg 1 = some (0, 1) := by decide
theorem cygAt2 : gwriteAt cyg 2 = some (1, 1) := by decide
theorem cygWix1 : gwix cyg (0, 1) = 1 := by decide
theorem cygWix2 : gwix cyg (1, 1) = 2 := by decide

/-! ## 3.1 Consistency -/

theorem cygGmo20 : gmoLt cyg (1, 1) (0, 0) := ⟨by decide, by decide, by decide⟩

theorem cygGmo01 : gmoLt cyg (0, 1) (1, 0) := ⟨by decide, by decide, by decide⟩

theorem cygGwf : gwf cyg := by
  refine ⟨by decide, ?_, ?_⟩
  · intro e
    constructor
    · intro he
      simp only [cyg, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · rintro ⟨l, hl, _⟩
      rcases cygLbl e l hl with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · intro i p k l hp hk
    rcases i with _ | _ | i <;> simp [cyg] at hp <;> subst hp <;>
      rcases k with _ | _ | k <;> simp [cyRow] at hk <;> subst hk <;>
      simp [cyBytesLen, cyBytesNe, cyTs2, cyTs1]

/-- The BYTE each event touches, inverted. -/
theorem cygAcc (e : Geid) (a : Int) :
    gaccesses cyg e a →
    ∃ j : Nat, j < 4 ∧
      ((e = (0, 0) ∧ a = accAddr zA j) ∨ (e = (0, 1) ∧ a = accAddr zB j) ∨
       (e = (1, 0) ∧ a = accAddr zB j) ∨ (e = (1, 1) ∧ a = accAddr zA j)) := by
  rintro (⟨v, hw⟩ | ⟨t, v, hr⟩)
  · obtain ⟨j, hj, _, h⟩ := cygWr e a v hw
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨j, hj, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨j, hj, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  · obtain ⟨j, hj, _, h⟩ := cygRd e a t v hr
    rcases h with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
    · exact ⟨j, hj, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨j, hj, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩

/-- No ppo⁻ arm fires: disjoint words per hart, no fence, no acquire or release. -/
theorem cygNoppo (e1 e2 : Geid) : ¬ gppo cyg e1 e2 := by
  rintro (hpl | hf | ha | hr)
  · obtain ⟨⟨hag, hlt, _, _⟩, a, h1, h2⟩ := hpl
    obtain ⟨j, hj, h1⟩ := cygAcc e1 a h1
    obtain ⟨j', hj', h2⟩ := cygAcc e2 a h2
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h2 with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ <;>
      simp at hag hlt
    · exact cyRangesDisj j j' hj hj' ha
    · exact cyRangesDisj j' j hj' hj ha.symm
  · obtain ⟨pr, pw, sr, sw, ⟨_, _, kf, _, _, hlf⟩, _, _⟩ := hf
    rcases cygLbl _ _ hlf with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  · obtain ⟨_, ⟨l, hl, _⟩, ⟨l', hl', haq⟩, _⟩ := ha
    rw [hl, Option.some.injEq] at hl'
    subst hl'
    rcases cygLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [lbAq] at haq
  · obtain ⟨_, ⟨l, hl, hrc⟩, _⟩ := hr
    rcases cygLbl _ _ hl with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [lbRcsc, lbAq, lbRl] at hrc

theorem cygConsistent : rvwmoMinusConsistent cyg := by
  refine ⟨cygGwf, fun e1 e2 h => absurd h (cygNoppo e1 e2), ?_, ?_⟩
  · intro e a t v hrd
    obtain ⟨j, hj, hv, h⟩ := cygRd e a t v hrd
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt cyg 2 = some w ∧ gwritesByte cyg w (accAddr zA j) v ∧
          gvisible cyg w (0, 0)
        exact ⟨(1, 1), cygAt2, ⟨_, zA, cyBytes, j, rfl, rfl, hv, rfl⟩, Or.inl cygGmo20⟩
      · intro w' v' hw' _
        obtain ⟨j', hj', _, h'⟩ := cygWr w' _ v' hw'
        rcases h' with ⟨rfl, ha⟩ | ⟨rfl, _⟩
        · exact absurd ha (cyRangesDisj j j' hj hj')
        · rw [cygWix2]
          exact Nat.le_refl _
    · refine ⟨?_, ?_⟩
      · show ∃ w, gwriteAt cyg 1 = some w ∧ gwritesByte cyg w (accAddr zB j) v ∧
          gvisible cyg w (1, 0)
        exact ⟨(0, 1), cygAt1, ⟨_, zB, cyBytes, j, rfl, rfl, hv, rfl⟩, Or.inl cygGmo01⟩
      · intro w' v' hw' _
        obtain ⟨j', hj', _, h'⟩ := cygWr w' _ v' hw'
        rcases h' with ⟨rfl, _⟩ | ⟨rfl, ha⟩
        · rw [cygWix1]
          omega
        · exact absurd ha.symm (cyRangesDisj j' j hj' hj)
  · intro e a t v hrd hw
    obtain ⟨j, _, _, h⟩ := cygRd e a t v hrd
    obtain ⟨l, hl, hlw⟩ := hw
    rcases h with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;>
      rcases cygLbl _ l hl with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      simp [lbIsW] at h1 hlw

theorem cygDepsConsistent : rvwmoMinusDepsConsistent cygd :=
  ⟨cygConsistent, fun _ h => by simp [cygd] at h, fun _ h => by simp [cygd] at h⟩

/-! ## 3.2 The conformance bundle -/

noncomputable def cyBoot (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) : Nat → Pexv6 := fun i =>
  match i with
  | 0 => cyP0 cyA cyB cpu0 rs0
  | 1 => cyP0 cyB cyA cpu1 rs1
  | _ => .PDisk none

theorem cygQconf (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    gdexecQconf (cyBoot cpu0 cpu1 rs0 rs1) d0 cyImg 2 cygd := by
  refine ⟨rfl, by decide, ?_⟩
  intro i row hrow
  rcases i with _ | _ | i
  · obtain rfl : cyRow cyA cyB cyTs2 = row := Option.some.inj hrow
    exact ⟨cyEm cyA cyB cyTs2 cpu0 rs0, cyHartConf _ _ _ _ _ _ _ cyARam cyBRam rfl,
      cyEmDevfree _ _ _ _ _, WeakRvwmoCycWit.cyEmFetchImg _ _ _ _ _ _,
      fun jk hjk => (cyRowDepsEmpty _ _ _ _ _ jk hjk).elim⟩
  · obtain rfl : cyRow cyB cyA cyTs1 = row := Option.some.inj hrow
    exact ⟨cyEm cyB cyA cyTs1 cpu1 rs1, cyHartConf _ _ _ _ _ _ _ cyBRam cyARam rfl,
      cyEmDevfree _ _ _ _ _, WeakRvwmoCycWit.cyEmFetchImg _ _ _ _ _ _,
      fun jk hjk => (cyRowDepsEmpty _ _ _ _ _ jk hjk).elim⟩
  · simp [cygd, cyg] at hrow

/-! ## 3.3 THE CYCLE — the point of the witness -/

theorem cygGpow0 : gpow cyg (0, 0) (0, 1) :=
  ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

theorem cygGpow1 : gpow cyg (1, 0) (1, 1) :=
  ⟨⟨rfl, by decide, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

theorem cygGrf0 : WeakRvwmoAcyc.grf cyg (0, 1) (1, 0) :=
  ⟨accAddr zB 0, 1, nthByte (n := 4) lockOne 0,
    ⟨_, zB, cyTs1, cyBytes, 0, rfl, rfl, rfl, cyBytesNth 0 (by decide), rfl⟩, cygAt1⟩

theorem cygGrf1 : WeakRvwmoAcyc.grf cyg (1, 1) (0, 0) :=
  ⟨accAddr zA 0, 2, nthByte (n := 4) lockOne 0,
    ⟨_, zA, cyTs2, cyBytes, 0, rfl, rfl, rfl, cyBytesNth 0 (by decide), rfl⟩, cygAt2⟩

theorem cygCycle : tc (racyD cygd) (0, 0) (0, 0) :=
  tc_l (Or.inl (Or.inl cygGpow0))
    (tc_l (Or.inl (Or.inr (Or.inl cygGrf0)))
      (tc_l (Or.inl (Or.inl cygGpow1))
        (tc_once (Or.inl (Or.inr (Or.inl cygGrf1))))))

/-- … and the cycle in the form `walkSupply`'s own hypotheses take it. -/
theorem cygSegments : ∃ z ss, ss ≠ [] ∧ rawChain cygd z z ss :=
  cycleSegments cygd (0, 0) cygDepsConsistent.2.1 cygCycle

/-! # 4. THE WALK, RUN ON THE CYCLE

Hart 0's load is the SUBSTITUTED one (its graph source, hart 1's store, is not yet in the log):
it reads the ERA IMAGE, which holds ZERO where `cyg`'s row says `lockOne`.  Hart 1's load is
TRUE: by then hart 0's store is in the log at index 1, its graph source.  The Rocq section
context `cpu0 cpu1 rs0 rs1 d0` is explicit (deviation 1). -/

/-! ## 4.1 The four candidates -/

def cwC0 : Cand := ⟨cyImg, []⟩
def cwLb0 : Lbl := latestReadLbl cwC0 false zA 4
def cwC1 : Cand := candSnoc cwC0 ⟨0, cwLb0⟩
def cwLb1 : Lbl := .LStore false zB cyBytes .WCplain
def cwC2 : Cand := candSnoc cwC1 ⟨0, cwLb1⟩
def cwLb2 : Lbl := latestReadLbl cwC2 false zB 4
def cwC3 : Cand := candSnoc cwC2 ⟨1, cwLb2⟩
def cwLb3 : Lbl := .LStore false zA cyBytes .WCplain
def cwC4 : Cand := candSnoc cwC3 ⟨1, cwLb3⟩

/-! ## 4.2 The substituted / true reads, COMPUTED -/

theorem cwLog0 : cdLogEnd cwC0 = [] := rfl

theorem cwLog2 : cdLogEnd cwC2 = [⟨zB, cyBytes, some 0, .WCplain⟩] := by
  show cdLogEnd (candSnoc (candSnoc cwC0 ⟨0, cwLb0⟩) ⟨0, cwLb1⟩) = _
  rw [cdLogEndSnoc, cdLogEndSnoc]
  rfl

theorem cwLb0Tvs :
    cwLb0 = .LLoad false zA ((witTvs cwC0 zA 4).map Prod.fst) ((witTvs cwC0 zA 4).map Prod.snd) :=
  (witTvsLbl cwC0 false zA 4).symm

theorem cwTvs0Len : (witTvs cwC0 zA 4).length = 4 := witTvsLength cwC0 zA 4

/-- The substituted read's timestamps are the empty log's: all 0, the era image. -/
theorem cwLb0Ts : lrdTs cwC0 zA 4 = [0, 0, 0, 0] := by decide +kernel

theorem cwLb2Eq : cwLb2 = .LLoad false zB cyTs1 cyBytes := by
  have h1 : lrdTs cwC2 zB 4 = cyTs1 := by decide +kernel
  have h2 : lrdVs cwC2 zB 4 = cyBytes := by decide +kernel
  show Lbl.LLoad false zB (lrdTs cwC2 zB 4) (lrdVs cwC2 zB 4) = _
  rw [h1, h2]

/-! ## 4.3 Consistency of the four -/

theorem cwC0Cons : srvwmoConsistent cwC0 :=
  srvwmoOfWf cwC0 (candReachable cwC0 (fun _ _ hs => absurd hs (by simp [cwC0]))).1

theorem cwBytes0 : latestBytesOk cwC0 zA 4 := by
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · omega

theorem cwC1Cons : srvwmoConsistent cwC1 := snocLatestConsistent cwC0 0 false zA 4 cwC0Cons cwBytes0

theorem cwC2Cons : srvwmoConsistent cwC2 :=
  snocWriteConsistent cwC1 0 false zB cyBytes .WCplain cwC1Cons cyBytesNe

theorem cwBytes2 : latestBytesOk cwC2 zB 4 := by
  intro j hj
  rcases j with _ | _ | _ | _ | j
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · omega

theorem cwC3Cons : srvwmoConsistent cwC3 := snocLatestConsistent cwC2 1 false zB 4 cwC2Cons cwBytes2

theorem cwC4Cons : srvwmoConsistent cwC4 :=
  snocWriteConsistent cwC3 1 false zA cyBytes .WCplain cwC3Cons cyBytesNe

/-! ## 4.4 The `wRelp` facts the two store projections need -/

theorem cwRelp0 : ((candLastSt cwC0).msWs 0).wRelp = false := rfl

theorem cwRelp0_1 : ((candLastSt cwC0).msWs 1).wRelp = false := rfl

theorem cwRelp1 : ((candLastSt cwC1).msWs 0).wRelp = false :=
  (candSnocRelp cwC0 0 cwLb0).trans (by rw [cwRelp0]; rfl)

theorem cwRelp3 : ((candLastSt cwC3).msWs 1).wRelp = false := by
  have h2 : ((candLastSt cwC2).msWs 1).wRelp = ((candLastSt cwC1).msWs 1).wRelp :=
    candSnocRelpNe cwC1 0 1 cwLb1 (by decide)
  have h1 : ((candLastSt cwC1).msWs 1).wRelp = ((candLastSt cwC0).msWs 1).wRelp :=
    candSnocRelpNe cwC0 0 1 cwLb0 (by decide)
  refine (candSnocRelp cwC2 1 cwLb2).trans ?_
  rw [h2, h1, cwRelp0_1]
  rfl

/-! ## 4.5 The process supply, one `execProgOk'Snoc` per event (deviation 4: pinned) -/

noncomputable def cwPst0 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) : Nat → List Pexv6 :=
  fun _ => (List.range' 0 2).map (cyBoot cpu0 cpu1 rs0 rs1)
def cwDv0 (d0 : Efab) : Nat → Efab := fun _ => d0
noncomputable def cwPst1 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) : Nat → List Pexv6 :=
  pstSnoc cwC0 (cwPst0 cpu0 cpu1 rs0 rs1) 0 (cyPa cyB cpu0 rs0)
def cwDv1 (d0 : Efab) : Nat → Efab := dvSnoc cwC0 (cwDv0 d0) d0
noncomputable def cwPst2 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) : Nat → List Pexv6 :=
  pstSnoc cwC1 (cwPst1 cpu0 cpu1 rs0 rs1) 0 (cyP2 cpu0 rs0)
def cwDv2 (d0 : Efab) : Nat → Efab := dvSnoc cwC1 (cwDv1 d0) d0
noncomputable def cwPst3 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) : Nat → List Pexv6 :=
  pstSnoc cwC2 (cwPst2 cpu0 cpu1 rs0 rs1) 1 (cyPa cyA cpu1 rs1)
def cwDv3 (d0 : Efab) : Nat → Efab := dvSnoc cwC2 (cwDv2 d0) d0
noncomputable def cwPst4 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) : Nat → List Pexv6 :=
  pstSnoc cwC3 (cwPst3 cpu0 cpu1 rs0 rs1) 1 (cyP2 cpu1 rs1)
def cwDv4 (d0 : Efab) : Nat → Efab := dvSnoc cwC3 (cwDv3 d0) d0

theorem cwProg0 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    execProgOk' (pstepPin cwC0.cdImg pstepEv) pclsEv (cwPst0 cpu0 cpu1 rs0 rs1) (cwDv0 d0)
      (candExec cwC0) := by
  intro k s hs
  exact absurd hs (by simp [candExec, cwC0])

theorem cwProg1 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    execProgOk' (pstepPin cwC1.cdImg pstepEv) pclsEv (cwPst1 cpu0 cpu1 rs0 rs1) (cwDv1 d0)
      (candExec cwC1) :=
  execProgOk'Snoc cwC0 0 (cyP0 cyA cyB cpu0 rs0) (cyP0 cyA cyB cpu0 rs0) d0 []
    (cyWlLd' cyA (witTvs cwC0 zA 4)) cwLb0 (cyPa cyB cpu0 rs0) d0 (cwPst0 cpu0 cpu1 rs0 rs1)
    (cwDv0 d0) (cwProg0 cpu0 cpu1 rs0 rs1 d0) rfl (.ARnil _ _)
    (fun _ h => absurd h List.not_mem_nil)
    (by rw [cwLb0Tvs]; exact cyRealizesLd' cyA cyB cpu0 rs0 _ _)
    (cyPstepLd' cyA cyB cpu0 rs0 d0 _ cyARam cwTvs0Len)

theorem cwProg2 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    execProgOk' (pstepPin cwC2.cdImg pstepEv) pclsEv (cwPst2 cpu0 cpu1 rs0 rs1) (cwDv2 d0)
      (candExec cwC2) :=
  execProgOk'Snoc cwC1 0 (cyPa cyB cpu0 rs0) (cyP1 cyB cpu0 rs0) d0 [.LInstr] (cyWlSt cyB)
    cwLb1 (cyP2 cpu0 rs0) d0 (cwPst1 cpu0 cpu1 rs0 rs1) (cwDv1 d0)
    (cwProg1 cpu0 cpu1 rs0 rs1 d0) rfl
    (.ARcons _ _ .LInstr _ _ [] _ _ rfl (cyPstepAnn cyB cpu0 rs0 d0) (.ARnil _ _))
    (fun l0 h => by rw [List.mem_singleton] at h; subst h; trivial)
    (cyRealizesSt cyB cpu0 rs0 _ cwRelp1) (cyPstepSt cyB cpu0 rs0 d0 cyBRam)

theorem cwProg3 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    execProgOk' (pstepPin cwC3.cdImg pstepEv) pclsEv (cwPst3 cpu0 cpu1 rs0 rs1) (cwDv3 d0)
      (candExec cwC3) :=
  execProgOk'Snoc cwC2 1 (cyP0 cyB cyA cpu1 rs1) (cyP0 cyB cyA cpu1 rs1) d0 []
    (cyWlLd cyB cyTs1) cwLb2 (cyPa cyA cpu1 rs1) d0 (cwPst2 cpu0 cpu1 rs0 rs1) (cwDv2 d0)
    (cwProg2 cpu0 cpu1 rs0 rs1 d0) rfl (.ARnil _ _)
    (fun _ h => absurd h List.not_mem_nil)
    (by rw [cwLb2Eq]; exact cyRealizesLd cyB cyA cpu1 rs1 _ cyTs1 rfl)
    (cyPstepLd cyB cyA cpu1 rs1 d0 cyTs1 cyBRam rfl)

theorem cwProg4 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    execProgOk' (pstepPin cwC4.cdImg pstepEv) pclsEv (cwPst4 cpu0 cpu1 rs0 rs1) (cwDv4 d0)
      (candExec cwC4) :=
  execProgOk'Snoc cwC3 1 (cyPa cyA cpu1 rs1) (cyP1 cyA cpu1 rs1) d0 [.LInstr] (cyWlSt cyA)
    cwLb3 (cyP2 cpu1 rs1) d0 (cwPst3 cpu0 cpu1 rs0 rs1) (cwDv3 d0)
    (cwProg3 cpu0 cpu1 rs0 rs1 d0) rfl
    (.ARcons _ _ .LInstr _ _ [] _ _ rfl (cyPstepAnn cyA cpu1 rs1 d0) (.ARnil _ _))
    (fun l0 h => by rw [List.mem_singleton] at h; subst h; trivial)
    (cyRealizesSt cyA cpu1 rs1 _ cwRelp3) (cyPstepSt cyA cpu1 rs1 d0 cyARam)

/-! ## 4.6 The two certified segments -/

noncomputable def cwS0 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) : CycState :=
  ⟨cwC0, cwPst0 cpu0 cpu1 rs0 rs1, cwDv0 d0⟩
noncomputable def cwS2 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) : CycState :=
  ⟨cwC2, cwPst2 cpu0 cpu1 rs0 rs1, cwDv2 d0⟩
noncomputable def cwS4 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) : CycState :=
  ⟨cwC4, cwPst4 cpu0 cpu1 rs0 rs1, cwDv4 d0⟩

/-- THE VALUES REALLY DIFFER — the anti-coincidence lemma: `cyg`'s row says hart 0 reads
`lockOne`'s bytes; the certified step returns the era image's.  It fails the moment `cyImg` is
put back to `lockOne` at `zA`. -/
theorem cygValuesDiffer : lrdVs cwC0 zA 4 ≠ cyBytes := by decide +kernel

/-- … and the certified step's label IS the substituted one. -/
theorem cwLb0NeRow : cwLb0 ≠ .LLoad false zA (lrdTs cwC0 zA 4) cyBytes := by
  intro h
  apply cygValuesDiffer
  have h' : Lbl.LLoad false zA (lrdTs cwC0 zA 4) (lrdVs cwC0 zA 4) =
      .LLoad false zA (lrdTs cwC0 zA 4) cyBytes := h
  injection h'

def cwO0 : Segout := ⟨0, cyRow cyA cyB cyTs2, 0, [⟨0, cwLb0⟩, ⟨0, cwLb1⟩]⟩
def cwO1 : Segout := ⟨1, cyRow cyB cyA cyTs1, 2, [⟨1, cwLb2⟩, ⟨1, cwLb3⟩]⟩

theorem cwS0Ok (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    cstOk d0 (cwS0 cpu0 cpu1 rs0 rs1 d0) :=
  ⟨cwC0Cons, cwProg0 cpu0 cpu1 rs0 rs1 d0, rfl⟩

theorem cwS2Ok (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    cstOk d0 (cwS2 cpu0 cpu1 rs0 rs1 d0) :=
  ⟨cwC2Cons, cwProg2 cpu0 cpu1 rs0 rs1 d0, rfl⟩

theorem cwS4Ok (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    cstOk d0 (cwS4 cpu0 cpu1 rs0 rs1 d0) :=
  ⟨cwC4Cons, cwProg4 cpu0 cpu1 rs0 rs1 d0, rfl⟩

theorem cwSeg0 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    segStep d0 cwO0 (cwS0 cpu0 cpu1 rs0 rs1 d0) (cwS2 cpu0 cpu1 rs0 rs1 d0) := by
  refine ⟨cwS0Ok cpu0 cpu1 rs0 rs1 d0, cwS2Ok cpu0 cpu1 rs0 rs1 d0, rfl, rfl, ?_, ?_⟩
  · intro s hs
    simp only [cwO0, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> rfl
  · -- THE SUBSTITUTED ARM: same footprint, DIFFERENT values (`cygValuesDiffer`)
    exact .cons (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) (.cons (lblReidxWRefl _) .nil)

theorem cwSeg1 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    segStep d0 cwO1 (cwS2 cpu0 cpu1 rs0 rs1 d0) (cwS4 cpu0 cpu1 rs0 rs1 d0) := by
  refine ⟨cwS2Ok cpu0 cpu1 rs0 rs1 d0, cwS4Ok cpu0 cpu1 rs0 rs1 d0, rfl, rfl, ?_, ?_⟩
  · intro s hs
    simp only [cwO1, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> rfl
  · refine .cons ?_ (.cons (lblReidxWRefl _) .nil)
    show lblReidxW (.LLoad false (paZ cyB) cyTs1 cyBytes) cwLb2
    rw [cwLb2Eq]
    exact lblReidxWRefl _

/-! ## 4.7 … as `WeakRvwmoWalk`'s own steps -/

theorem cwGmsg1 :
    WeakRvwmoKillArms.gmsg cyg (0, 1) = some ⟨zB, cyBytes, some 0, .WCplain⟩ := rfl

theorem cwGmsg2 :
    WeakRvwmoKillArms.gmsg cyg (1, 1) = some ⟨zA, cyBytes, some 1, .WCplain⟩ := rfl

theorem cwStep0 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wlkStep cyg d0 (cwS0 cpu0 cpu1 rs0 rs1 d0) 0 :=
  wlkStepOfSeg cyg d0 (cwS0 cpu0 cpu1 rs0 rs1 d0) (cwS2 cpu0 cpu1 rs0 rs1 d0) 0 cwO0
    [.LLoad false zA cyTs2 cyBytes] false zB cyBytes .WCplain (0, 1)
    (cwSeg0 cpu0 cpu1 rs0 rs1 d0) rfl
    (fun lb h => by rw [List.mem_singleton] at h; subst h; rfl) rfl rfl rfl cygAt1 cwGmsg1

theorem cwStep1 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wlkStep cyg d0 (cwS2 cpu0 cpu1 rs0 rs1 d0) 1 :=
  wlkStepOfSeg cyg d0 (cwS2 cpu0 cpu1 rs0 rs1 d0) (cwS4 cpu0 cpu1 rs0 rs1 d0) 1 cwO1
    [.LLoad false zB cyTs1 cyBytes] false zA cyBytes .WCplain (1, 1)
    (cwSeg1 cpu0 cpu1 rs0 rs1 d0) rfl
    (fun lb h => by rw [List.mem_singleton] at h; subst h; rfl) rfl rfl rfl cygAt2 cwGmsg2

/-! ## 4.8 THE WALK'S CONCLUSION, at the cycle graph -/

theorem cwInv0 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wlkInv (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg (cwS0 cpu0 cpu1 rs0 rs1 d0) 0 :=
  ⟨cwS0Ok cpu0 cpu1 rs0 rs1 d0, rfl, rfl, rfl, wlogPfxNil cyg⟩

theorem cwPfx2 : wlogPfx cyg 1 (cdLogEnd cwC2) := by
  rw [cwLog2]
  exact wlogPfxSnoc cyg 0 [] (0, 1) _ (wlogPfxNil cyg) cygAt1 cwGmsg1

theorem cwInv2 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wlkInv (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg (cwS2 cpu0 cpu1 rs0 rs1 d0) 1 :=
  ⟨cwS2Ok cpu0 cpu1 rs0 rs1 d0, rfl, rfl, rfl, cwPfx2⟩

theorem cwLog4 :
    cdLogEnd cwC4 = [⟨zB, cyBytes, some 0, .WCplain⟩] ++ [⟨zA, cyBytes, some 1, .WCplain⟩] := by
  show cdLogEnd (candSnoc (candSnoc cwC2 ⟨1, cwLb2⟩) ⟨1, cwLb3⟩) = _
  rw [cdLogEndSnoc, cdLogEndSnoc, cwLog2]
  rfl

theorem cwPfx4 : wlogPfx cyg 2 (cdLogEnd cwC4) := by
  have h2 := cwPfx2
  rw [cwLog2] at h2
  rw [cwLog4]
  exact wlogPfxSnoc cyg 1 [⟨zB, cyBytes, some 0, .WCplain⟩] (1, 1) _ h2 cygAt2 cwGmsg2

theorem cwInv4 (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    wlkInv (cyBoot cpu0 cpu1 rs0 rs1) d0 2 cyg (cwS4 cpu0 cpu1 rs0 rs1 d0) 2 :=
  ⟨cwS4Ok cpu0 cpu1 rs0 rs1 d0, rfl, rfl, rfl, cwPfx4⟩

/-- THE WITNESS.  Exactly `WeakRvwmoGlue2.walkSupply`'s conclusion, at a graph that carries a
real `racyD` cycle (`cygCycle`) and is `gdexecQconf`-conformant (`cygQconf`). -/
theorem cygWalk (cpu0 cpu1 : CPU) (rs0 rs1 : RegFile) (d0 : Efab) :
    ∃ (l : List Segout) (S0 Sf : CycState),
      segsRun d0 l S0 Sf ∧
      Sf.cstC.cdImg = cyg.gxImg ∧
      Sf.cstPst 0 = (List.range' 0 2).map (cyBoot cpu0 cpu1 rs0 rs1) ∧
      Sf.cstDv 0 = d0 ∧
      logOf cyg (cdLog Sf.cstC Sf.cstC.cdTr.length) := by
  obtain ⟨_, himg, hpst, hdv, hpfx⟩ := cwInv4 cpu0 cpu1 rs0 rs1 d0
  refine ⟨[cwO0, cwO1], cwS0 cpu0 cpu1 rs0 rs1 d0, cwS4 cpu0 cpu1 rs0 rs1 d0, ?_, himg, hpst,
    hdv, ?_⟩
  · exact .segsMore _ _ _ _ _ (cwSeg0 cpu0 cpu1 rs0 rs1 d0)
      (.segsMore _ _ _ _ _ (cwSeg1 cpu0 cpu1 rs0 rs1 d0)
        (.segsDone _ (cwS4Ok cpu0 cpu1 rs0 rs1 d0)))
  · apply logOfOfPfx
    rw [cygGwrites]
    exact hpfx

end Weak
