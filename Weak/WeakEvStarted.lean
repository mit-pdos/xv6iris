/-
Weak: **the `started` handshake at EVENT granularity** (spike S5).

Rocq: `iris/WeakEvStarted.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE COMPARISON THIS FILE EXISTS TO MAKE.  The instruction-atomic handshake is
`WeakAcquire.wwpStartedSet` (the publisher) and `WkStartedLoad.wwpStartedLoad` /
`wwpStartedFenceR` / `wwpStartedWaitSeq` (the subscriber), each "ONE INSTRUCTION, from `Loop` to
`Loop`, given that instruction's certification".  §§1–3 restate the three INSTRUCTION rules, at
the same altitude and scope, over `WeakEvLang` -- "ONE INSTRUCTION, from `ECycle 0 c m none` to
`ELoop 0 c`" -- where the certification is `WeakEvLift`-shaped: a computed silent stretch per gap
(an UNEVALUATED composition of `esil` cursors) and one memory-event rule per event.  §5
instantiates the publisher's certification at the REAL kernel instruction (`main+0xb0`,
`c.sw a4,0(a5)` = `0xc398`) by kernel evaluation; §6 is the naive per-node calibration point, an
ANTI-PATTERN, not an interface.

WHAT CARRIES OVER UNCHANGED: all of `WeakStarted` (the escrow, its writer `wstartedSet`, its
reader `wstartedObserve`) is σ-altitude over `Wmstate`, and the event σ projects to exactly that
at each hart (`whartView`).  Used VERBATIM.

WHAT CHANGES: (S5-1) the events of one instruction are visible, so the premises are per event;
(S5-2) the escrow is opened around the DATA event only -- the fetch happens outside it;
(S5-3) nothing mentions the instruction's pre-state: each event's rule is at that event's own σ
(no `wadmDown`, no frozen log).

## Deviations from Rocq

1. NAMES / VOCABULARY: the tree's camelCase (map below) and `WeakEvLift`'s vocabulary (its
   deviations 1, 4, 5): `EWP e @ ⊤` ↦ `ewpTriv ⊤ e`, `P -∗ Q -∗ R` ↦ `P ∗ Q ⊢ R`, `gset register`
   ↦ `List Register`, `M unit` ↦ `SailM Unit`, `bv_unsigned w` ↦ `w.toNat`, `Interface.ReadReq.t n`
   ↦ `Mem_read_request n va …` (requests are ALSO indexed by the VA width, so every request
   parameter comes with its `va : Nat`; the kernel's are at `va = 64`), `WriteReq.value req = v` ↦
   `req.value = some v`, `S (length l)` ↦ `l.length + 1`, `lock_zero/one` ↦ `lockZero/lockOne`.
   File-qualified (`notes/weak-port-dupnames.json`): `WeakEvStarted.whartViewImg`.
2. O2 -- THE FETCH (`notes/weak-port-o2-design.md` §1.5; `WeakEvLift` deviation 2).  Rocq measured
   the model's fetch to be a PLAIN read (F7, `ev_fetch_plain`) and every fetch premise was
   `ak_coh = false ∧ ak_latest = false`.  The Lean model tags fetches `AK_ifetch` (the i-cache):
   every fetch premise is `(classify reqf.access_kind).akIfetch = true`, `ev_fetch_plain` is
   `evFetchIfetch : classify evReqf.access_kind = ⟨true, false, false⟩`, and Rocq's
   `efetch_ws`/`efetch_ws_le`/`efetch_ws_relp` steps are gone: after the fetch the hart's view is
   the stretch's own `ws0` (`wsDepmove ws ws0`).  The flag read keeps the data-read premises,
   `akIfetch = false` for Rocq's `ak_coh = false`.
3. THE STORE NODE: `ewpEvSeqStore` takes `n ≠ 0` (discharged by `decide`) and `req.value = some v`.
4. §3: Rocq calls `wstarted_deliver_gen` at a dummy `WMState rs ∅ [] ws1 dev0_state`; Lean has no
   closed `DevStates`, so the delivery is the Lean-only `WeakEvStarted.deliverWs` (the same
   statement at a bare `Wstate`, proved as `WeakInstr.wwpFenceSclGen`).  `wV_fence`'s Lean form is
   `wsLe (barrierPost …) ws'` (closed by `wsLeRefl`).
5. THE PROOF MODE unifies up to reducible unfolding only: the Lean-only `rfl` lemmas
   `WeakEvStarted.ecurReadFst/ecurWriteFst/ecurBarFst` rewrite a resume's register file before
   framing, and the escrow lemmas are applied after rewriting `whartView`'s projections
   (`whartViewLog`, `WeakLang.whartViewImg`, `whartViewWs`).  The post-store `Wmstate` is the
   anonymous-constructor literal of Rocq's `WMState …` (with `wgitv c`).
6. §4 (`Example` in Rocq) is the theorem `ewpEvStartedWaitSeq`.
7. §5, THE CONCRETE STATE AND THE MEASUREMENT (`vm_compute`/`vm_cast_no_check` ↦ `decide +kernel`,
   `Weak/WeakDeps.lean` recipe and `Weak/AxSpinSpikeRun.lean`'s closed-run recipe):
   - the cold-boot file `ColdBoot.cold_regs (mword_of_int 0)` ↦ `bootLand ⟨0, _⟩
     WeakEvStarted.regs0`: the language's own boot landing (`MachCSL.bootLand`, the output of
     `bootProg` -- the machine's booted state, `MachCSL.bootFacts`) from the all-default power-on
     file (Lean-only `WeakEvStarted.regs0`, as `AxSpinSpikeRun.spikeRegs0`);
   - the Lean kernel image: `main+0xb0 = 0x80000f7e` IS `c.sw a4,0(a5)` (`0xc398`,
     `Weak.ksReleaseStoreMainB0Word`), fetched as ONE 2-byte read (pc ≡ 2 mod 4), so
     `evFetchPa = 2147487614` (Rocq: 2147487534, its image places `main` elsewhere);
     `evWord : Nat`, `evPc`/`evFlag` are `BitVec 64` of `KernelSyms.main + 0xb0` / `started`;
   - THE MEASUREMENT MATCHES ROCQ: 107 silent nodes to the fetch, 179 to the store, 8 to `Ret`
     (`evLen1/2/3`);
   - `ev_Dl` is Rocq's `vm_compute`d literal; Lean keeps the collector APPLICATION `evDl`
     (unevaluated, as the cursors) and reads back only its DEDUPLICATED form, the 23-register
     literal `evD` (Rocq `ev_D := list_to_set ev_Dl`; a list here, and a repeated register would
     make `eregFrame` unsatisfiable, `WeakEvLift` deviation 4).  The Lean-only
     `WeakEvStarted.evDCovers` checks every collected register is in `evD`;
   - `ev_reqf`/`ev_reqw` are Rocq's readbacks of the request records; lean-sail's requests have
     no `DecidableEq`, so Lean defines them as `Option.get` of the projection, with the Lean-only
     `WeakEvStarted.evX1IsRead`/`evX2IsWrite` (`isSome`, by `decide +kernel`) as the proof
     argument; `evFetchReq`/`evStoreReq` are then `Option.some_get`, and every field fact is a
     kernel-checked equation (`evStorePa` is stated at `@Eq PAddr`, where `Decidable` is found);
   - the cursor equations of `ewpEvStartedSetAtMain` are `rfl` `have`s, as Rocq's measured note
     recommends (conversion unfolds the cursor definitions and stops).
   Kernel times (c4d VM): each projection fact and stretch count 0.5–3 s; the whole file's type
   checking ~25 s.
8. `erun_count`'s successor is `erunCount n D rs' m' + 1` (Rocq `S (…)`).

**Rocq → Lean name map.**  `whart_view_img` `WeakEvStarted.whartViewImg`, `eread_adm` `ereadAdm`,
`eread_ws` `ereadWs`, `wkernel_text_etext_word` `wkernelTextEtextWord`, `ewp_ev_started_set`
`ewpEvStartedSet`, `ev_rcpt` `evRcpt`, `ev_rcpt_persistent` `evRcpt_persistent`, `ev_rcpt_mono`
`evRcptMono`, `ev_flag_cb` `evFlagCb`, `ev_rcpt_arm_mono` `evRcptArmMono`, `ewp_ev_started_load`
`ewpEvStartedLoad`, `ewp_ev_started_fence` `ewpEvStartedFence`, `ewp_ev_started_wait_seq`
`ewpEvStartedWaitSeq`, `esil_node_any` `esilNodeAny`, `esil_node_reg` `esilNodeReg`, `erun_any`
`erunAny`, `erun_regs` `erunRegs`, `erun_count` `erunCount`, `ecount` `ecount`, `ev_pc` `evPc`,
`ev_flag` `evFlag`, `ev_word` `evWord`, `ev_wf` `evWf`, `ev_rs0` `evRs0`, `ev_c1` `evC1`, `ev_c2`
`evC2`, `ev_Dl` `evDl`, `ev_D` `evD`, `ev_x0..3` `evX0..3`, `ev_reqf` `evReqf`, `ev_reqw`
`evReqw`, `ev_len1..3` `evLen1..3`, `ev_fetch_req` `evFetchReq`, `ev_fetch_plain`
`evFetchIfetch` (deviation 2), `ev_fetch_pa` `evFetchPa`, `ev_store_req` `evStoreReq`,
`ev_store_pa` `evStorePa`, `ev_store_val` `evStoreVal`, `ev_store_plain` `evStorePlain`,
`ev_tail_ret` `evTailRet`, `ev_fetch_ram` `evFetchRam`, `ev_store_ram` `evStoreRam`,
`ev_store_wf` `evStoreWf`, `ewp_ev_started_set_at_main` `ewpEvStartedSetAtMain`, `calib_naive_8`
`calibNaive8`, `calib_batched_8` `calibBatched8`.
Lean-only (file-qualified): `WeakEvStarted.ecurReadFst`, `WeakEvStarted.ecurWriteFst`,
`WeakEvStarted.ecurBarFst` (deviation 5), `WeakEvStarted.deliverWs` (deviation 4),
`WeakEvStarted.regs0`, `WeakEvStarted.evDCovers`, `WeakEvStarted.evX1IsRead`,
`WeakEvStarted.evX2IsWrite` (deviation 7).

**Dropped:** nothing (Rocq 51 declarations; Lean 51 + 8 Lean-only).

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 1–4 and 7.
-/
import Weak.WeakEvLift
import Weak.WkStartedLoad
import Xv6.KernelImage

namespace Weak

open Iris Iris.ProgramLogic Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## 0. The two bridges between the event σ and the escrow's altitude -/

theorem WeakEvStarted.whartViewImg (σ : WGState) (c : CPU) :
    wimg (whartView σ c) = imgZ σ.wgimg := rfl

def ereadAdm (σ : WGState) (ws : Wstate) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak) (w : BitVec (8 * n))
    (tvs : List (Nat × BitVec 8)) : Prop :=
  tvs.length = n ∧
  (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) ∧
  readOk (imgZ σ.wgimg) σ.wglog ws (classify req.access_kind).akSync false (paZ req.pa) tvs

def ereadWs (_σ : WGState) (ws : Wstate) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (tvs : List (Nat × BitVec 8)) : Wstate :=
  loadPostRun ws (classify req.access_kind).akSync (paZ req.pa) (tvs.map Prod.fst)

/-- Lean-only: the resumes leave the register file alone (`rfl`; the proof mode unifies only up
to reducible unfolding). -/
theorem WeakEvStarted.ecurReadFst (v : Nat) (x : ecur) : (ecurRead v x).1 = x.1 := rfl
theorem WeakEvStarted.ecurWriteFst (x : ecur) : (ecurWrite x).1 = x.1 := rfl
theorem WeakEvStarted.ecurBarFst (x : ecur) : (ecurBar x).1 = x.1 := rfl

section startedEv

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

theorem wkernelTextEtextWord (bs : GMapF PAddr (BitVec 8)) (pa : PAddr) (n : Nat)
    (w : BitVec (8 * n)) :
    accWf pa n →
    (∀ j : Nat, j < n → get? bs (pa + BitVec.ofNat 64 j) = some (nthByte w j)) →
    wkernelText (GF := GF) bs ⊢ etextWord (GF := GF) (paZ pa) n w := by
  intro hacc hdom
  unfold etextWord
  refine (show wkernelText (GF := GF) bs ⊢ iprop(□ wkernelText (GF := GF) bs) by
    iintro #H; imodintro; iexact H).trans
    (BigSepL.bigSepL_intro fun i j hj => intuitionistically_elim.trans ?_)
  have hmem := List.mem_of_getElem? hj
  rw [List.mem_range'_1] at hmem
  have hjn : j < n := by omega
  show wkernelText (GF := GF) bs ⊢ etext (GF := GF) (WeakInterp.accAddr pa j) (nthByte w j)
  rw [← accWfByte pa n j hacc hjn]
  unfold wkernelText etext
  exact BigSepM.bigSepM_lookup
    (Φ := fun a b => wlatPointsto (GF := GF) (paZ a) DFrac.discard 0 b) (hdom j hjn)

/-! ## 1. THE PUBLISHER -/

theorem ewpEvStartedSet (a : PAddr) (P : VProp GF) (c : CPU) (D : List Register)
    (m : SailM Unit) (ws : Wstate) (rs : RegFile) (n1 n2 n3 : Nat) (x1 x2 x3 : ecur)
    (nf vaf : Nat) (reqf : Mem_read_request nf vaf Arch.pa Arch.translation Arch.arch_ak)
    (wf : BitVec (8 * nf)) (vaw : Nat)
    (reqw : Mem_write_request 4 vaw Arch.pa Arch.translation Arch.arch_ak) :
    x1 = esil n1 D (rs, m) →
    x2 = esil n2 D (ecurRead wf.toNat x1) →
    x3 = esil n3 D (ecurWrite x2) →
    ereadReqAt nf vaf x1.2 = some reqf →
    ewriteReqAt 4 vaw x2.2 = some reqw →
    enodeTag x3.2 = 0 →
    devAddr reqf.pa = false →
    (classify reqf.access_kind).akIfetch = true →
    devAddr reqw.pa = false →
    (classify reqw.access_kind).akLatest = false →
    reqw.pa = a →
    reqw.value = some lockOne →
    accWf a 4 →
    ws.wRelp = true →
    wstartedInv (hlc := hlc) (GF := GF) a P ∗ etextWord (GF := GF) (paZ reqf.pa) nf wf ∗
      hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ∗ vwpHold P ws ∗
      ▷ (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c x3.1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop 0 c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c m none) := by
  intro hx1 hx2 hx3 hnf hnw htag hdevf hiff hdevw hlatw hpaw hvalw hacc hrelp
  subst hx1 hx2 hx3 hpaw
  unfold wstartedInv
  iintro ⟨#Hinv, #Htext, Hws, Hrf, HP, Hcont⟩
  -- the FETCH event
  iapply ewpEvSeqFetch 0 c D n1 (rs, m) nf vaf reqf wf ws rfl hnf hdevf hiff
  iframe Htext Hws Hrf
  inext
  iintro %ws0 %hd0 Hws Hrf
  have hle0 : wsLe ws ws0 := wsDepmoveLe _ _ hd0
  have hrelp0 : ws0.wRelp = true := by rw [wsDepmoveRelp _ _ hd0]; exact hrelp
  ihave HP := vwpHold_mono P hle0 $$ HP
  -- the STORE event
  iapply ewpEvSeqStore 0 c D n2 (ecurRead wf.toNat (esil n1 D (rs, m))) 4 vaw reqw lockOne ws0
    rfl hnw hdevw (by decide) hvalw hlatw hacc
  rw [WeakEvStarted.ecurReadFst]
  iframe Hws Hrf
  iintro %ws1 %hd1 %σ2 %hws2 %hwf2 %hbnd2 #Hlb2 Hlat2
  subst hws2
  have hrelp1 : (σ2.wgws c).wRelp = true := by rw [wsDepmoveRelp _ _ hd1]; exact hrelp0
  ihave HP := vwpHold_mono P (wsDepmoveLe _ _ hd1) $$ HP
  imod (inv_acc (E := ⊤) (N := wstartedN) (P := wstartedBody (GF := GF) reqw.pa P)
    CoPset.subseteq_top) $$ Hinv with ⟨Hbody, Hclose⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hmask
  inext
  imod Hmask
  unfold wstartedBody wstartedAt
  icases Hbody with ⟨%t0, %v0, Hw0, Hhist⟩
  -- the φ payment is the escrow's own SYNC window, read off the body BEFORE the set
  icases keepPure (nvOkWlat4Sync c σ2.wgimg σ2.wglog reqw.pa t0 v0) $$ Hlat2 Hw0
    with ⟨%hnvok, Hlat2, Hw0⟩
  ihave Hbody : wstartedBody (GF := GF) reqw.pa P $$ [Hw0 Hhist]
  · unfold wstartedBody wstartedAt
    iexists t0, v0
    isplitl [Hw0]
    · iexact Hw0
    · iexact Hhist
  -- the successor's hart state, in the escrow's own vocabulary
  have hQ : wQStore (some c.val) reqw.pa lockOne (whartView σ2 c)
      ⟨σ2.wgregs c, σ2.wgimg, σ2.wglog ++ [wwriteMsg (some c.val)
          (wmClassOf (classify reqw.access_kind) (σ2.wgws c)) reqw.pa 4 lockOne],
        storePostRunD (σ2.wgws c) (classify reqw.access_kind).akSync 0 0
          (paZ reqw.pa) 4 (σ2.wglog.length + 1), σ2.wgdev, σ2.wgitv c⟩ := by
    unfold wQStore wQStoreW wVStoreW
    refine ⟨rfl, ⟨_, rfl, fun _ => WeakInstr.wmClassOfRelp _ _ hrelp1⟩,
      storePostRunDLe _ _ _ _ _ _ _, fun j hj => ?_⟩
    exact flrStorePostRunD _ _ _ _ _ _ _ j hj
  have hset := wstartedSet (GF := GF) reqw.pa P (some c.val) (whartView σ2 c) _ hQ hrelp1 hbnd2
  simp only [whartViewLog, WeakLang.whartViewImg, whartViewWs] at hset
  imod hset $$ Hlb2 Hlat2 Hbody HP with ⟨Hlat2, Hat⟩
  imod Hclose $$ [Hat]
  · inext
    unfold wstartedAt
    iexists _, lockOne
    iexact Hat
  imodintro
  isplitr
  · ipureintro; exact hnvok
  isplitl [Hlat2]
  · iexact Hlat2
  iintro %va' %vd Hws Hrf
  -- the TAIL: back to the boundary
  iapply ewpEvSeqRet 0 c D n3 (ecurWrite (esil n2 D (ecurRead wf.toNat (esil n1 D (rs, m))))) _
    rfl htag
  rw [WeakEvStarted.ecurWriteFst]
  iframe Hws Hrf
  iintro %ws3 %hd3 Hws Hrf
  iapply Hcont $$ %ws3
    %(wsLeTrans hle0 (wsLeTrans (wsDepmoveLe _ _ hd1)
      (wsLeTrans (storePostRunDLe _ _ _ _ _ _ _) (wsDepmoveLe _ _ hd3)))) Hws Hrf

/-! ## 2. THE SUBSCRIBER'S LOAD -/

def evRcpt (P : VProp GF) (ws : Wstate) : IProp GF :=
  iprop(∃ T : Nat, ⌜T ≤ ws.wVrOld⌝ ∗ P.monPred_at (viewScl T))

instance evRcpt_persistent (P : VProp GF) [Persistent P] (ws : Wstate) :
    Persistent (evRcpt P ws) := by
  unfold evRcpt; infer_instance

theorem evRcptMono (P : VProp GF) (ws ws' : Wstate) :
    wsLe ws ws' → evRcpt P ws ⊢ evRcpt P ws' := by
  intro hle
  unfold evRcpt
  iintro ⟨%T, %hT, HP⟩
  iexists T
  isplitr
  · ipureintro; exact Nat.le_trans hT (wsLeVrOld _ _ hle)
  · iexact HP

def evFlagCb (c : CPU) (a : PAddr) (ws : Wstate) (va : Nat)
    (req : Mem_read_request 4 va Arch.pa Arch.translation Arch.arch_ak) : IProp GF :=
  iprop(∀ σ : WGState,
    ⌜σ.wgws c = ws⌝ -∗ ⌜wlogWf σ.wglog⌝ -∗ ⌜wsBounded ws σ.wglog.length⌝ -∗
    wlogLb (GF := GF) σ.wglog -∗
    wlatInterp (GF := GF) σ.wgimg σ.wglog ={⊤ \ ↑wstartedN, ∅}=∗
      ⌜∃ (w : BitVec (8 * 4)) (tvs : List (Nat × BitVec 8)), ereadAdm σ ws 4 va req w tvs⌝ ∗
      ⌜wstartedImgClear (whartView σ c) a⌝ ∗
      ⌜wunwritten ws a 4⌝ ∗
      ▷ (∀ (w : BitVec (8 * 4)) (tvs : List (Nat × BitVec 8)),
          ⌜ereadAdm σ ws 4 va req w tvs⌝ ={∅, ⊤ \ ↑wstartedN}=∗
            ⌜∀ a0 : Int, coh ws a0 < coh (ereadWs σ ws 4 va req tvs) a0 →
              nvOk σ.wglog c a0⌝ ∗
            wlatInterp (GF := GF) σ.wgimg σ.wglog))

theorem evRcptArmMono (P : VProp GF) [Persistent P] (ws ws' : Wstate) (w : BitVec 32) :
    wsLe ws ws' →
    iprop(⌜w = lockZero⌝ ∨ (⌜w ≠ lockZero⌝ ∗ evRcpt P ws)) ⊢
      iprop(⌜w = lockZero⌝ ∨ (⌜w ≠ lockZero⌝ ∗ evRcpt P ws')) := by
  intro hle
  iintro (%h | ⟨%h, Hr⟩)
  · ileft; ipureintro; exact h
  · iright
    isplitr
    · ipureintro; exact h
    · iapply evRcptMono P ws ws' hle $$ Hr

theorem ewpEvStartedLoad (a : PAddr) (P : VProp GF) [Persistent P] (c : CPU)
    (D : List Register) (m : SailM Unit) (ws : Wstate) (rs : RegFile) (n1 n2 n3 : Nat)
    (x1 x2 : ecur) (nf vaf : Nat)
    (reqf : Mem_read_request nf vaf Arch.pa Arch.translation Arch.arch_ak)
    (wf : BitVec (8 * nf)) (val : Nat)
    (reql : Mem_read_request 4 val Arch.pa Arch.translation Arch.arch_ak) :
    x1 = esil n1 D (rs, m) →
    x2 = esil n2 D (ecurRead wf.toNat x1) →
    ereadReqAt nf vaf x1.2 = some reqf →
    ereadReqAt 4 val x2.2 = some reql →
    (∀ w : BitVec (8 * 4), enodeTag (esil n3 D (ecurRead w.toNat x2)).2 = 0) →
    devAddr reqf.pa = false →
    (classify reqf.access_kind).akIfetch = true →
    devAddr reql.pa = false →
    (classify reql.access_kind).akIfetch = false →
    (classify reql.access_kind).akLatest = false →
    reql.pa = a →
    wstartedInv (hlc := hlc) (GF := GF) a P ∗ etextWord (GF := GF) (paZ reqf.pa) nf wf ∗
      hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ∗
      (∀ ws0 : Wstate, ⌜wsLe ws ws0⌝ -∗ evFlagCb (GF := GF) c a ws0 val reql) ∗
      ▷ (∀ (ws' : Wstate) (w : BitVec (8 * 4)), ⌜wsLe ws ws'⌝ -∗
          iprop(⌜w = lockZero⌝ ∨ (⌜w ≠ lockZero⌝ ∗ evRcpt P ws')) -∗
          hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c (esil n3 D (ecurRead w.toNat x2)).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop 0 c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c m none) := by
  intro hx1 hx2 hnf hnl htag hdevf hiff hdevl hifl hlatl hpal
  subst hx1 hx2 hpal
  unfold wstartedInv
  iintro ⟨#Hinv, #Htext, Hws, Hrf, Hflag, Hcont⟩
  -- the FETCH event
  iapply ewpEvSeqFetch 0 c D n1 (rs, m) nf vaf reqf wf ws rfl hnf hdevf hiff
  iframe Htext Hws Hrf
  inext
  iintro %ws0 %hd0 Hws Hrf
  -- the FLAG event, escrow open
  iapply ewpEvSeqLoad 0 c D n2 (ecurRead wf.toNat (esil n1 D (rs, m))) 4 val reql ws0
    rfl hnl hdevl hifl hlatl
  rw [WeakEvStarted.ecurReadFst]
  iframe Hws Hrf
  iintro %ws1 %hd1 %σ2 %hws2 %hwf2 %hbnd2 #Hlb2 Hlat2
  have hle1 : wsLe ws ws1 := wsLeTrans (wsDepmoveLe _ _ hd0) (wsDepmoveLe _ _ hd1)
  ispecialize Hflag $$ %ws1 %hle1
  unfold evFlagCb
  imod (inv_acc (E := ⊤) (N := wstartedN) (P := wstartedBody (GF := GF) reql.pa P)
    CoPset.subseteq_top) $$ Hinv with ⟨Hbody, Hclose⟩
  imod Hflag $$ %σ2 %hws2 %hwf2 %hbnd2 Hlb2 Hlat2 with ⟨%hen2, %himg, %hunw, Hfk2⟩
  imodintro
  isplitr
  · ipureintro
    obtain ⟨w, tvs, h1, h2, h3⟩ := hen2
    exact ⟨w, tvs, h1, h2, h3⟩
  inext
  iintro %w %tvs2 %g1 %g2 %g3
  imod Hfk2 $$ %w %tvs2 %⟨g1, g2, g3⟩ with ⟨%hpay2, Hlat2⟩
  -- THE COLLAPSE, in the non-clear arm
  ihave Harm : iprop(wlatInterp (GF := GF) σ2.wgimg σ2.wglog ∗ wstartedBody (GF := GF) reql.pa P ∗
      (⌜w = lockZero⌝ ∨ (⌜w ≠ lockZero⌝ ∗ evRcpt P (ereadWs σ2 ws1 4 val reql tvs2))))
    $$ [Hlat2 Hbody]
  · by_cases hw0 : w = lockZero
    · isplitl [Hlat2]
      · iexact Hlat2
      isplitl [Hbody]
      · iexact Hbody
      ileft; ipureintro; exact hw0
    · obtain ⟨j, hj, hbne⟩ := bv32NeZeroByte w hw0
      obtain ⟨⟨t, b⟩, ht⟩ : ∃ p, tvs2[j]? = some p :=
        ⟨tvs2[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hb : b = nthByte w j := by
        have h2 := g2 j hj
        rw [List.getElem?_map, ht] at h2
        exact Option.some.inj h2
      subst hb
      have hrd2 : readOk (imgZ σ2.wgimg) σ2.wglog (σ2.wgws c)
          (classify reql.access_kind).akSync false (paZ reql.pa) tvs2 := by
        rw [hws2]; exact g3
      have hok := readOkWbyteOk σ2 c (classify reql.access_kind) (paZ reql.pa) tvs2 j t
        (nthByte w j) hifl hlatl hrd2 ht
      have hobs := wstartedObserve (GF := GF) reql.pa P (whartView σ2 c)
        (classify reql.access_kind) j t (nthByte (n := 4) w j) himg hj hok hbne
      simp only [whartViewLog, WeakLang.whartViewImg] at hobs
      icases hobs $$ Hlb2 Hlat2 Hbody
        with ⟨Hlat2, Hbody, -, %T, %hTle, #HP0⟩
      -- the load's own gain: the timestamp it read is under its read floor
      have hfst : (tvs2.map Prod.fst)[j]? = some t := by rw [List.getElem?_map, ht]; rfl
      have hgain := loadPostRunVrOld ws1 (classify reql.access_kind).akSync (paZ reql.pa)
        (tvs2.map Prod.fst) j (by rw [List.length_map]; omega) (hunw j hj)
      rw [list_lookup_total_correct hfst] at hgain
      isplitl [Hlat2]
      · iexact Hlat2
      isplitl [Hbody]
      · iexact Hbody
      iright
      isplitr
      · ipureintro; exact hw0
      unfold evRcpt
      iexists T
      isplitr
      · ipureintro
        show T ≤ (loadPostRun ws1 _ _ _).wVrOld
        omega
      · iexact HP0
  icases Harm with ⟨Hlat2, Hbody, Harm⟩
  imod Hclose $$ [Hbody]
  · inext
    iexact Hbody
  imodintro
  isplitr
  · ipureintro; exact hpay2
  isplitl [Hlat2]
  · iexact Hlat2
  iintro Hws Hrf
  -- the TAIL
  iapply ewpEvSeqRet 0 c D n3
    (ecurRead w.toNat (esil n2 D (ecurRead wf.toNat (esil n1 D (rs, m)))))
    (loadPostRun ws1 (classify reql.access_kind).akSync (paZ reql.pa) (tvs2.map Prod.fst))
    rfl (htag w)
  rw [WeakEvStarted.ecurReadFst]
  iframe Hws Hrf
  iintro %ws3 %hd3 Hws Hrf
  ihave Harm := evRcptArmMono P (ereadWs σ2 ws1 4 val reql tvs2) ws3 w (wsDepmoveLe _ _ hd3)
    $$ Harm
  iapply Hcont $$ %ws3 %w
    %(wsLeTrans hle1 (wsLeTrans (loadPostRunLe _ _ _ _) (wsDepmoveLe _ _ hd3))) Harm Hws Hrf

/-! ## 3. THE SUBSCRIBER'S FENCE -/

/-- Lean-only: `WeakStarted.wstartedDeliverGen` at a bare `Wstate`. -/
theorem WeakEvStarted.deliverWs (P : VProp GF) (ws ws' : Wstate) (t : Nat) (b : barrier_kind) :
    acqPredR b → t ≤ ws.wVrOld → wsLe (barrierPost ws b) ws' →
    P.monPred_at (viewScl t) ⊢ vwpHold P ws' := by
  intro hb ht hle
  unfold vwpHold
  apply P.monPred_mono
  exact Std.IsPreorder.le_trans _ _ _ (viewScl_acqPredR b ws t hb ht) (wsView_mono _ _ hle)

theorem ewpEvStartedFence (P : VProp GF) (c : CPU) (D : List Register)
    (m : SailM Unit) (ws : Wstate) (rs : RegFile) (n1 n2 n3 : Nat) (x1 x2 x3 : ecur)
    (nf vaf : Nat) (reqf : Mem_read_request nf vaf Arch.pa Arch.translation Arch.arch_ak)
    (wf : BitVec (8 * nf)) (b : barrier_kind) :
    x1 = esil n1 D (rs, m) →
    x2 = esil n2 D (ecurRead wf.toNat x1) →
    x3 = esil n3 D (ecurBar x2) →
    ereadReqAt nf vaf x1.2 = some reqf →
    ebarAt x2.2 = some b →
    enodeTag x3.2 = 0 →
    ebarPark b = none →
    acqPredR b →
    devAddr reqf.pa = false →
    (classify reqf.access_kind).akIfetch = true →
    etextWord (GF := GF) (paZ reqf.pa) nf wf ∗
      hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ∗ evRcpt P ws ∗
      ▷ (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗ vwpHold P ws' -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c x3.1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop 0 c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c m none) := by
  intro hx1 hx2 hx3 hnf hnb htag hpark hacq hdevf hiff
  subst hx1 hx2 hx3
  iintro ⟨#Htext, Hws, Hrf, Hrcpt, Hcont⟩
  -- the FETCH event
  iapply ewpEvSeqFetch 0 c D n1 (rs, m) nf vaf reqf wf ws rfl hnf hdevf hiff
  iframe Htext Hws Hrf
  inext
  iintro %ws0 %hd0 Hws Hrf
  ihave Hrcpt := evRcptMono P ws ws0 (wsDepmoveLe _ _ hd0) $$ Hrcpt
  -- the BARRIER event
  iapply ewpEvSeqBarrier 0 c D n2 (ecurRead wf.toNat (esil n1 D (rs, m))) b ws0 rfl hnb
  rw [WeakEvStarted.ecurReadFst]
  iframe Hws Hrf
  inext
  iintro %ws1 %hd1 Hws Hrf
  ihave Hrcpt := evRcptMono P ws0 ws1 (wsDepmoveLe _ _ hd1) $$ Hrcpt
  -- the barrier's post-view IS `barrierPost`, since nothing is parked
  have hbp : efenceApply ws1 (ebarNow b) = barrierPost ws1 b := by
    rw [← efenceBarrierPost ws1 b, hpark]; rfl
  -- THE DELIVERY
  ihave HP : vwpHold P (efenceApply ws1 (ebarNow b)) $$ [Hrcpt]
  · unfold evRcpt
    icases Hrcpt with ⟨%T, %hT, HP0⟩
    iapply WeakEvStarted.deliverWs P ws1 _ T b hacq hT (by rw [hbp]; exact wsLeRefl _)
    iexact HP0
  rw [hpark]
  -- the TAIL
  iapply ewpEvSeqRet 0 c D n3 (ecurBar (esil n2 D (ecurRead wf.toNat (esil n1 D (rs, m)))))
    (efenceApply ws1 (ebarNow b)) rfl htag
  rw [WeakEvStarted.ecurBarFst]
  iframe Hws Hrf
  iintro %ws2 %hd2 Hws Hrf
  ihave HP := vwpHold_mono P (wsDepmoveLe _ _ hd2) $$ HP
  iapply Hcont $$ %ws2
    %(wsLeTrans (wsDepmoveLe _ _ hd0) (wsLeTrans (wsDepmoveLe _ _ hd1)
      (wsLeTrans (efenceApplyLe _ _) (wsDepmoveLe _ _ hd2)))) HP Hws Hrf

/-! ## 4. THE TWO-INSTRUCTION COMPOSITION -/

theorem ewpEvStartedWaitSeq (a : PAddr) (P : VProp GF) [Persistent P] (c : CPU)
    (D : List Register) (m : SailM Unit) (ws : Wstate) (rs : RegFile)
    (n1 n2 n3 k1 k2 k3 : Nat) (x1 x2 : ecur) (x3 : BitVec (8 * 4) → ecur)
    (y1 y2 y3 : BitVec (8 * 4) → Bool → ecur) (nf vaf : Nat)
    (reqf : Mem_read_request nf vaf Arch.pa Arch.translation Arch.arch_ak)
    (wf : BitVec (8 * nf)) (val : Nat)
    (reql : Mem_read_request 4 val Arch.pa Arch.translation Arch.arch_ak)
    (gf vag : Nat) (reqg : Mem_read_request gf vag Arch.pa Arch.translation Arch.arch_ak)
    (wg : BitVec (8 * gf)) (b : barrier_kind) :
    x1 = esil n1 D (rs, m) →
    x2 = esil n2 D (ecurRead wf.toNat x1) →
    (∀ w : BitVec (8 * 4), x3 w = esil n3 D (ecurRead w.toNat x2)) →
    ereadReqAt nf vaf x1.2 = some reqf →
    ereadReqAt 4 val x2.2 = some reql →
    (∀ w : BitVec (8 * 4), enodeTag (x3 w).2 = 0) →
    devAddr reqf.pa = false →
    (classify reqf.access_kind).akIfetch = true →
    devAddr reql.pa = false →
    (classify reql.access_kind).akIfetch = false →
    (classify reql.access_kind).akLatest = false →
    reql.pa = a →
    (∀ w tick, y1 w tick = esil k1 D (ecurLoop tick (x3 w))) →
    (∀ w tick, y2 w tick = esil k2 D (ecurRead wg.toNat (y1 w tick))) →
    (∀ w tick, y3 w tick = esil k3 D (ecurBar (y2 w tick))) →
    (∀ w tick, ereadReqAt gf vag (y1 w tick).2 = some reqg) →
    (∀ w tick, ebarAt (y2 w tick).2 = some b) →
    (∀ w tick, enodeTag (y3 w tick).2 = 0) →
    ebarPark b = none →
    acqPredR b →
    devAddr reqg.pa = false →
    (classify reqg.access_kind).akIfetch = true →
    wstartedInv (hlc := hlc) (GF := GF) a P ∗ etextWord (GF := GF) (paZ reqf.pa) nf wf ∗
      etextWord (GF := GF) (paZ reqg.pa) gf wg ∗
      hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c rs D ∗
      (∀ ws0 : Wstate, ⌜wsLe ws ws0⌝ -∗ evFlagCb (GF := GF) c a ws0 val reql) ∗
      ▷ (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c (x3 lockZero).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop 0 c)) ∗
      ▷ (∀ (ws' : Wstate) (w : BitVec (8 * 4)) (tick : Bool),
          ⌜wsLe ws ws'⌝ -∗ ⌜w ≠ lockZero⌝ -∗ vwpHold P ws' -∗
          hartWs (GF := GF) c ws' -∗ eregFrame (hlc := hlc) (GF := GF) c (y3 w tick).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop 0 c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c m none) := by
  intro hx1 hx2 hx3 hnf hnl htag hdevf hiff hdevl hifl hlatl hpal hy1 hy2 hy3 hgf hgb hgtag
    hpark hacq hdevg hifg
  iintro ⟨#Hinv, #Htf, #Htg, Hws, Hrf, Hflag, Hclear, Hexit⟩
  iapply ewpEvStartedLoad a P c D m ws rs n1 n2 n3 x1 x2 nf vaf reqf wf val reql hx1 hx2 hnf hnl
    (fun w => by rw [← hx3 w]; exact htag w) hdevf hiff hdevl hifl hlatl hpal
  iframe Hinv Htf Hws Hrf Hflag
  inext
  iintro %ws' %w %hle Harm Hws Hrf
  rw [← hx3 w]
  icases Harm with (%hw0 | ⟨%hne, #Hrcpt⟩)
  · subst hw0
    iapply Hclear $$ %ws' %hle Hws Hrf
  -- the boundary: the tick is the language's, not the caller's
  iapply ewpEloop 0 c ws' rfl
  iframe Hws
  inext
  iintro %tick Hws
  ihave #Hrcpt' := evRcptMono P ws' (instrPost ws') (instrPostLe ws') $$ Hrcpt
  -- INSTRUCTION 2: the fence cashes the receipt
  iapply ewpEvStartedFence P c D (riscvStep tick) (instrPost ws') (x3 w).1 k1 k2 k3
    (y1 w tick) (y2 w tick) (y3 w tick) gf vag reqg wg b (hy1 w tick) (hy2 w tick) (hy3 w tick)
    (hgf w tick) (hgb w tick) (hgtag w tick) hpark hacq hdevg hifg
  iframe Htg Hws Hrf Hrcpt'
  inext
  iintro %ws'' %hle' HP Hws Hrf
  iapply Hexit $$ %ws'' %w %tick %(wsLeTrans hle (wsLeTrans (instrPostLe ws') hle')) %hne HP
    Hws Hrf

end startedEv

/-! ## 5. THE CONCRETE INSTANTIATION -/

/-! ### 5a. The measurement-side scaffolding: a footprint collector -/

def esilNodeAny (rs : RegFile) : SailM Unit → Option (RegFile × SailM Unit)
  | .pure _ => none
  | .impure (.error _) _ => none
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => some (rs, k (rs r))
    | .regWrite r v, k => some (rs.set r v, k PUnit.unit)
    | .instrAnnounce _ _, k => some (rs, k ())
    | .branchAnnounce _ _, k => some (rs, k ())
    | .cacheOp _, k => some (rs, k ())
    | .tlbi _, k => some (rs, k ())
    | .takeException _, k => some (rs, k ())
    | .returnException _, k => some (rs, k ())
    | .translationStart _, k => some (rs, k ())
    | .translationEnd _, k => some (rs, k ())
    | .cycleCount, k => some (rs, k ())
    | .message _, k => some (rs, k ())
    | .getCycleCount, k => some (rs, k (0 : Nat))
    | _, _ => none

def esilNodeReg : SailM Unit → List Register
  | .impure (.ok (.regRead r)) _ => [r]
  | .impure (.ok (.regWrite r _)) _ => [r]
  | _ => []

def erunAny : Nat → RegFile → SailM Unit → RegFile × SailM Unit
  | 0, rs, m => (rs, m)
  | n + 1, rs, m =>
    match esilNodeAny rs m with
    | some (rs', m') => erunAny n rs' m'
    | none => (rs, m)

def erunRegs : Nat → RegFile → SailM Unit → List Register
  | 0, _, _ => []
  | n + 1, rs, m =>
    match esilNodeAny rs m with
    | some (rs', m') => esilNodeReg m ++ erunRegs n rs' m'
    | none => []

def erunCount : Nat → List Register → RegFile → SailM Unit → Nat
  | 0, _, _, _ => 0
  | n + 1, D, rs, m =>
    match esilNode D rs m with
    | some (rs', m') => erunCount n D rs' m' + 1
    | none => 0

def ecount (n : Nat) (D : List Register) (x : ecur) : Nat := erunCount n D x.1 x.2

/-! ### 5b. The concrete state -/

def evPc : BitVec 64 := BitVec.ofNat 64 (KernelSyms.«main» + 0xb0)
def evFlag : PAddr := BitVec.ofNat 64 KernelSyms.«started»
def evWord : Nat := 0xc398
def evWf : BitVec 16 := BitVec.ofNat 16 evWord

/-- Lean-only: the all-default power-on register file. -/
def WeakEvStarted.regs0 : RegFile := fun r => by
  cases r <;> exact default

def evRs0 : RegFile :=
  ((((bootLand ⟨0, by decide⟩ WeakEvStarted.regs0).set .x14 (BitVec.ofNat 64 1)).set .x15
    evFlag).set .PC evPc).set .nextPC evPc

noncomputable def evC1 : RegFile × SailM Unit := erunAny 400 evRs0 (riscvStep false)

noncomputable def evC2 : RegFile × SailM Unit :=
  erunAny 600 evC1.1 (ereadResume evWf.toNat evC1.2)
noncomputable def evDl : List Register :=
  erunRegs 400 evRs0 (riscvStep false) ++
    (erunRegs 600 evC1.1 (ereadResume evWf.toNat evC1.2) ++
      erunRegs 400 evC2.1 (ewriteResume evC2.2))

/-- THE FOOTPRINT, deduplicated (the kernel's `removeDups evDl`, read back once). -/
def evD : List Register :=
  [.mcountinhibit, .minstretcfg, .mideleg, .mip, .sig_meip, .sig_seip, .mie, .elp, .misa, .x14,
   .x15, .mseccfg, .mstatus, .cur_privilege, .pma_regions, .pmpcfg_n, .pmpaddr_n,
   .htif_tohost_base, .hart_state, .nextPC, .PC, .minstret_increment, .minstret]

theorem WeakEvStarted.evDCovers : evDl.all (fun r => decide (r ∈ evD)) = true := by
  decide +kernel

/-! ### 5c. THE CERTIFICATION, as three unevaluated compositions -/

noncomputable def evX0 : ecur := (evRs0, riscvStep false)
noncomputable def evX1 : ecur := esil 400 evD evX0
noncomputable def evX2 : ecur := esil 600 evD (ecurRead evWf.toNat evX1)
noncomputable def evX3 : ecur := esil 400 evD (ecurWrite evX2)

theorem WeakEvStarted.evX1IsRead : (ereadReqAt 2 64 evX1.2).isSome = true := by decide +kernel

noncomputable def evReqf : Mem_read_request 2 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ereadReqAt 2 64 evX1.2).get WeakEvStarted.evX1IsRead

theorem WeakEvStarted.evX2IsWrite : (ewriteReqAt 4 64 evX2.2).isSome = true := by decide +kernel

noncomputable def evReqw : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  (ewriteReqAt 4 64 evX2.2).get WeakEvStarted.evX2IsWrite

/-! ### 5d. THE MEASUREMENT, as compiled evidence -/

theorem evLen1 : ecount 400 evD evX0 = 107 := by decide +kernel
theorem evLen2 : ecount 600 evD (ecurRead evWf.toNat evX1) = 179 := by decide +kernel
theorem evLen3 : ecount 400 evD (ecurWrite evX2) = 8 := by decide +kernel

theorem evFetchReq : ereadReqAt 2 64 evX1.2 = some evReqf := (Option.some_get _).symm

theorem evFetchIfetch : classify evReqf.access_kind = ⟨true, false, false⟩ := by decide +kernel
theorem evFetchPa : paZ evReqf.pa = 2147487614 := by decide +kernel

theorem evStoreReq : ewriteReqAt 4 64 evX2.2 = some evReqw := (Option.some_get _).symm
theorem evStorePa : evReqw.pa = evFlag := (by decide +kernel : @Eq PAddr evReqw.pa evFlag)
theorem evStoreVal : evReqw.value = some lockOne := by decide +kernel
theorem evStorePlain : classify evReqw.access_kind = ⟨false, false, false⟩ := by decide +kernel

theorem evTailRet : enodeTag evX3.2 = 0 := by decide +kernel

theorem evFetchRam : devAddr evReqf.pa = false := by decide +kernel
theorem evStoreRam : devAddr evReqw.pa = false := by decide +kernel
theorem evStoreWf : accWf evFlag 4 := by unfold accWf; decide

/-! ### 5e. THE WHOLE-STRETCH INSTANTIATION -/

section instantiated

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

theorem ewpEvStartedSetAtMain (P : VProp GF) (c : CPU) (ws : Wstate) :
    ws.wRelp = true →
    wstartedInv (hlc := hlc) (GF := GF) evFlag P ∗ etextWord (GF := GF) (paZ evReqf.pa) 2 evWf ∗
      hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c evRs0 evD ∗ vwpHold P ws ∗
      ▷ (∀ ws' : Wstate, ⌜wsLe ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c evX3.1 evD -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ELoop 0 c)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c (riscvStep false) none) := by
  intro hrelp
  have h1 : evX1 = esil 400 evD (evRs0, riscvStep false) := rfl
  have h2 : evX2 = esil 600 evD (ecurRead evWf.toNat evX1) := rfl
  have h3 : evX3 = esil 400 evD (ecurWrite evX2) := rfl
  exact ewpEvStartedSet evFlag P c evD (riscvStep false) ws evRs0 400 600 400 evX1 evX2 evX3
    2 64 evReqf evWf 64 evReqw h1 h2 h3 evFetchReq evStoreReq evTailRet evFetchRam
    (by rw [evFetchIfetch]) evStoreRam (by rw [evStorePlain]) evStorePa evStoreVal evStoreWf hrelp

end instantiated

/-! ## 6. CALIBRATION -/

section calib

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [WeakGS GF]

theorem calibNaive8 (c : CPU) (D : List Register)
    (rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 : RegFile)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 : SailM Unit) (ws : Wstate) :
    esilNode D rs0 m0 = some (rs1, m1) →
    esilNode D rs1 m1 = some (rs2, m2) →
    esilNode D rs2 m2 = some (rs3, m3) →
    esilNode D rs3 m3 = some (rs4, m4) →
    esilNode D rs4 m4 = some (rs5, m5) →
    esilNode D rs5 m5 = some (rs6, m6) →
    esilNode D rs6 m6 = some (rs7, m7) →
    esilNode D rs7 m7 = some (rs8, m8) →
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c rs0 D ∗
      ▷ (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c rs8 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c m8 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c m0 none) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8
  iintro ⟨Hws, Hrf, H⟩
  iapply ewpEvSilNode 0 c D rs0 m0 m1 rs1 ws rfl h1
  iframe Hws Hrf
  inext
  iintro %w1 %hd1 Hws Hrf
  iapply ewpEvSilNode 0 c D rs1 m1 m2 rs2 w1 rfl h2
  iframe Hws Hrf
  inext
  iintro %w2 %hd2 Hws Hrf
  iapply ewpEvSilNode 0 c D rs2 m2 m3 rs3 w2 rfl h3
  iframe Hws Hrf
  inext
  iintro %w3 %hd3 Hws Hrf
  iapply ewpEvSilNode 0 c D rs3 m3 m4 rs4 w3 rfl h4
  iframe Hws Hrf
  inext
  iintro %w4 %hd4 Hws Hrf
  iapply ewpEvSilNode 0 c D rs4 m4 m5 rs5 w4 rfl h5
  iframe Hws Hrf
  inext
  iintro %w5 %hd5 Hws Hrf
  iapply ewpEvSilNode 0 c D rs5 m5 m6 rs6 w5 rfl h6
  iframe Hws Hrf
  inext
  iintro %w6 %hd6 Hws Hrf
  iapply ewpEvSilNode 0 c D rs6 m6 m7 rs7 w6 rfl h7
  iframe Hws Hrf
  inext
  iintro %w7 %hd7 Hws Hrf
  iapply ewpEvSilNode 0 c D rs7 m7 m8 rs8 w7 rfl h8
  iframe Hws Hrf
  inext
  iintro %w8 %hd8 Hws Hrf
  iapply H $$ %w8
    %(wsDepmoveTrans hd1 (wsDepmoveTrans hd2 (wsDepmoveTrans hd3 (wsDepmoveTrans hd4
      (wsDepmoveTrans hd5 (wsDepmoveTrans hd6 (wsDepmoveTrans hd7 hd8))))))) Hws Hrf

theorem calibBatched8 (c : CPU) (D : List Register) (x : ecur) (ws : Wstate) :
    hartWs (GF := GF) c ws ∗ eregFrame (hlc := hlc) (GF := GF) c x.1 D ∗
      (∀ ws' : Wstate, ⌜wsDepmove ws ws'⌝ -∗ hartWs (GF := GF) c ws' -∗
          eregFrame (hlc := hlc) (GF := GF) c (esil 8 D x).1 D -∗
          ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c (esil 8 D x).2 none)) ⊢
    ewpTriv (hlc := hlc) (GF := GF) ⊤ (ECycle 0 c x.2 none) :=
  ewpEvBatch 0 c D 8 x ws rfl

end calib

end Weak
