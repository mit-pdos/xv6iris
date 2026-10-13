/-
Weak: **the OPAX semantics over the event language** (AxSL-style thread steps).

Rocq: `iris/AxOpsem.v` @ xxvzwolszwmp.

## The Rocq header, in substance

LB via AxSL-style base logic (design §1-L0 and §0.5 "The step case").  Port of AxSL's
`lang/opsem.v` thread-step layer (`LThreadStep.t`, `progress_is_valid`, `eids_between`,
`reducible`, `not_stuck`) and of `low/adequacy_partial.v`'s `tpcoverage`, with the tree's
`Pexv6` program as the thread and the row of a `Gdexec` as the thread's event set.

THE SHAPE.  A thread is `⟨p, k⟩ : Athread` — the hart's program node and its ROW POSITION.
The program half of the event language (`WeakEvInst.pstepEv`) sees no memory: a memory label
carries the answers in the label, so "one opax step" is one program step whose label is checked
against `row[k]?` IN IDENTITY (kind / aq-or-rl / base / size; never timestamps, never classes) —
and, for a WRITE, also in the bytes it stores (`AStepWrite`: `wlWdata l = lblData lb`).  Two step
relations:
  `AxOpsem.astepProg` / `astep` — everything but reads.  Administrative labels (in Lean also
                the FETCH, deviation 2) keep `k`; a store or a fence realizes `row[k]?` and
                advances `k`.
  `areadStep` — "`s` is about to perform the read `id = aident (row[k]?)`, and `K vs` is the
                state after receiving the bytes `vs`" — the VALUE IS FREE.  The exclusive read
                half of a fused `LRmw` row item keeps `k`; the exclusive store half advances it.
`astepAny` glues the two.  Row positions are consumed monotonically, one per event step
(`astepAnyK`); the positions a run consumes are exactly the interval between its endpoints
(`arunConsumedIff`), so a run that reaches `row.length` covers the whole row (`coverageOfRow`).
The tree's conformance relation `hartConf`/`hemit` IS an opax run, one step per emission item
(`hemitAstep`).

FACTS THE NEXT LAYER MUST KNOW (Rocq (1)–(6)).
(1) DEVICES ARE ERASED, NOT ORACLED: each constructor quantifies its device input/output
    existentially (every non-`LDev` program step is device-independent).
(2) THE PLIC WIRE IS SEPARATED AND EXCLUDED FROM `reducible`: `pstepEv`'s hart arm is split into
    `pstepProg` (the program's own arms) and `pstepWire`; `astep := astepProg ∨ awire`;
    `reducible` ranges over `astepOwn` = program steps and reads only.
(3) INSTRUCTION FETCH.  Rocq: the fetch is a row event (an `LLoad false …` row item), realized
    either through `areadStep` or by `AStepFetch` (answered by the oracle `fetchImg` on the text
    region `T`).  Lean (O2 Stage C, deviation 2): the fetch is an ADMINISTRATIVE label — no row
    item, no oracle; it is an `AStepAdmin` step (`AxOpsem.lbAdminAx true (LIFetch ..)`).
(4) `terminated s := False` (harts never terminate; row exhaustion is `reducible`'s
    row-extension clause).
(5) SOURCES ARE NOT IN THE ROW IDENTITY: `AxOpsem.astepProg` is INDEXED BY THE INSTANCE LABEL;
    `aidentProjInst` says the row identity is `AxPair.lblIdent` with the sources forgotten,
    `aidentCat` that it is `AxGraphCat.ident` with the write class erased.
(6) THE GRAPH IS TAKEN THROUGH ITS `Gexec` (`growG`/`progressIsValidG`).

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  `Z` ↦ `Int`; `bv 8` ↦ `BitVec 8`; `l !! k` ↦
   `l[k]?`; `S k` ↦ `k + 1`; `is_Some o` ↦ `o.isSome = true`; `tvs.*2` ↦ `tvs.map Prod.snd`;
   `default x o` ↦ `o.getD x`; `agent` ↦ `Nat`; `dev_state` ↦ `Efab` (the event instance's
   fabric, `WeakEvInst` deviation 5); `vs !!! j` ↦ `vs.getD j 0#8`; `Interface.ReadReq.t n` ↦
   `Mem_read_request n va …` (lean-sail indexes the request by the va width too, so `va` is a
   new bound variable); a read continuation receives `.Ok (w, none)` (Rocq `inl (w, None)`).
   Duplicated Rocq names, file-qualified: `AxOpsem.astepProg` (constructors
   `AxOpsem.astepProg.AStepAdmin/AStepWrite/AStepFence`), `AxOpsem.grow`.
2. O2 STAGE C (`notes/weak-port-o2-stageC.md`, owner Q-C1/Q-C2) — THE FETCH IS AN ADMIN LABEL.
   The Lean event instance emits a fetch as the Lean-only `LIFetch base tvs` (`WeakEvInst`
   deviation 2), which the graph tier treats as ADMINISTRATIVE (`WeakAxRealize.lbAdmin true`,
   `projLbl … = none`, `AxPair.lblIdent … = none`): no row item, no identity, no edges.
   - `wlRd`/`wlRvals`/`wlReval` have no `LIFetch` arm (`none` / `[]` / identity);
   - DELETED (Q-C2): Rocq's `fetch_answers`, the `AStep_fetch` constructor, and the oracle
     parameters `T`/`fetchImg` of `astepProg`/`astep`/`astepAny`/`astepOwn`/`reducible`/
     `notStuck`/`consumed`/`hemitAstep`/… (and of their `G`/`Gd` forms); a fetch is an
     `AStepAdmin` step;
   - `rdLabel` takes a first flag `fe` (the access kind's `akIfetch`): `rdLabel true … =
     LIFetch base tvs`; `rdLabelReval`/`rdLabelRvals` take `fe = false`; `pnodeStepReadInv`
     concludes `akIfetch = false` (a read label never comes from the fetch node) where Rocq
     concludes `ak_coh … = false`; `pnodeStepReadAny` has NO premise (Rocq: `ak_coh … =
     false`; the Lean read arm is the TOTAL three-way split on `classify`, so it also covers the
     fetch node — stronger); `pstepProgMemreadLbl` takes `akIfetch = false`;
   - `OpaxWit.wtFetch` runs at a hand-built FETCH node `wtPf0` (an `AK_ifetch` read feeding the
     same store node) as an admin step at any position `k` (Rocq: consumes the row's read item
     at 0); Rocq's `wt_fT`/`wt_fimg`/`wt_T`/`wt_img` are deleted with the oracle.
   No `hart_conf`→`lblRealizes` conversion occurs in this file (`hemit` is stated over Rocq's
   four-conjunct `hlblRealizes`); `hemitAstepAux` reaches a fetch item only through
   `admRunAstep` (it is an admin item of the emission).
3. THE PLIC WIRE (owner decision Q1, `WeakEvInst` deviation 5).  The Lean wire is a step of the
   PLIC PROGRAM in the fabric (`pstepPlic`: the program sits at `.setPin cpu mm b`), not the
   stateless Rocq pin delivery `sig_seip := dev_seip d cpu`.  So `pstepWireInv` concludes
   `d.efPlic = .op (.setPin cpu mm b) k`, `d' = { d with efPlic := k () }` and the new register
   file `pinSet rs mm b` (Rocq: `d' = d`, `register_set sig_seip …`); `pstepWireAlways` takes the
   PLIC program's position as a premise; `awireAlways` (the wire never blocks) quantifies the
   delivered pin (`mm b`) and builds the fabric from any `d : Efab`.  No Iris here: no
   `wireInv`/`plicInv`.
4. THE PROGRAM HALF (`WeakEvInst` deviations 4/5): `pstepProg`/`pstepWire` quantify the
   barrier report `obar` beside `ors`/`oib`; the hart arm of `pstepProg` is `pstepNode` at the
   fabric's device states with `d' = { d with efDev := d'.efDev }` (`pstepHart`'s node arm).
5. `wordOfBytes n vs` is `WeakInterp.assembleBytes n (vs.getD · 0#8)` (Rocq `Z_to_bv (8*n)
   (assemble_bytes vs)`); `pnodeStepReadInv` states the bytes as `tvs.map Prod.snd =
   WeakInterpProj.wbytes n w` (as Rocq), from the Lean arm's per-byte `nthByte` clause.
6. OpaxWit: Rocq's `init_regstate` ↦ an arbitrary register file `rs` (every witness takes it;
   Lean has no named initial register file at this layer); `dev0_state` ↦ `OpaxWit.wtD0`
   (`efInit` of the default device states); the request literals are lean-sail records.
7. Lean-only helpers (file-qualified): `AxOpsem.sndEqWbytes`, `AxOpsem.tagBytes`,
   `AxOpsem.wlRdErwLabel`, `AxOpsem.wlRdEbarLabel`; OpaxWit's `wtFreq`/`wtFm`/`wtPf0`/
   `wtFetchStep` (deviation 2).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `pnodeStepReadInv`'s announce arm goes through `annLabelOr` (an announce node, marker or `LInstr`, is never a read).

**Rocq → Lean name map.**  `athread` `Athread` (`AThread`, `at_p`/`at_k` `atP`/`atK`),
`aident_t` `AidentT` (`IRead/IWrite/IRmw/IFence`), `aident` `aident`, `aident_rd` `aidentRd`,
`aident_wr` `aidentWr`, `aident_fence` `aidentFence`, `aident_n` `aidentN`, `aident_adv_rd`
`aidentAdvRd`, `aident_rd_n` `aidentRdN`, `aident_wr_n` `aidentWrN`, `wl_rd` `wlRd`, `wl_wr`
`wlWr`, `wl_wdata` `wlWdata`, `lbl_data` `lblData`, `wl_fence` `wlFence`, `wl_rmw` `wlRmw`,
`wl_rvals` `wlRvals`, `tag_vals` `tagVals`, `tag_vals_snd/length/fst` `tagValsSnd/Length/Fst`,
`wl_reval` `wlReval`, `wl_rd_n` `wlRdN`, `wl_reval_rd` `wlRevalRd`, `wl_reval_rvals`
`wlRevalRvals`, `aident_proj` `aidentProj`, `aident_proj_data` `aidentProjData`, `aident_pair`
`aidentPair`, `aident_of_inst` `aidentOfInst`, `aident_proj_inst` `aidentProjInst`,
`aident_of_cat` `aidentOfCat`, `aident_cat` `aidentCat`, `pstep_prog` `pstepProg`, `pstep_wire`
`pstepWire`, `pstep_ev_split` `pstepEvSplit`, `pstep_wire_inv` `pstepWireInv`,
`pstep_wire_always` `pstepWireAlways`, `word_of_bytes` `wordOfBytes`, `word_of_bytes_byte`
`wordOfBytesByte`, `word_of_bytes_wbytes` `wordOfBytesWbytes`, `wbytes_word_of_bytes`
`wbytesWordOfBytes`, `rd_label` `rdLabel`, `rd_asrc` `rdAsrc`, `rd_label_reval` `rdLabelReval`,
`rd_label_rvals` `rdLabelRvals`, `pnode_step_read_any` `pnodeStepReadAny`, `pnode_step_read_inv`
`pnodeStepReadInv`, `pstep_prog_read_cont` `pstepProgReadCont`, `pstep_prog_memread_lbl`
`pstepProgMemreadLbl`, `astep_prog` `AxOpsem.astepProg`,
`astep_prog_pstep` `astepProgPstep`, `awire` `awire`, `astep` `astep`, `aread_step`
`areadStep`, `astep_any` `astepAny` (`AAStep`/`AARead`), `astep_of_read` `astepOfRead`,
`astep_own` `astepOwn`, `astep_any_own` `astepAnyOwn`, `astep_prog_k` `astepProgK`,
`aread_step_k` `areadStepK`, `astep_any_k` `astepAnyK`, `astep_progress_mono`
`astepProgressMono`, `astep_admin_or_event` `astepAdminOrEvent`, `astep_event_valid`
`astepEventValid`, `arun_k_mono` `arunKMono`, `consumed` `consumed`, `arun_consumed_iff`
`arunConsumedIff`, `consumed_between` `consumedBetween`, `coverage_of_row` `coverageOfRow`,
`terminated` `terminated`, `awire_always` `awireAlways`, `reducible` `reducible`, `not_stuck`
`notStuck`, `astep_prog_row_agree` `astepProgRowAgree`, `aread_step_row_agree`
`areadStepRowAgree`, `astep_own_row_agree` `astepOwnRowAgree`, `astep_any_row_agree`
`astepAnyRowAgree`, `reducible_valid` `reducibleValid`, `grow_g` `growG`,
`progress_is_valid_g` `progressIsValidG`, `progress_is_valid_grow_g` `progressIsValidGrowG`,
`grow_g_lookup` `growGLookup`, `reducible_g` `reducibleG`, `not_stuck_g` `notStuckG`, `grow`
`AxOpsem.grow`, `progress_is_valid` `progressIsValid`, `reducible_gd` `reducibleGd`,
`not_stuck_gd` `notStuckGd`, `read_block` `readBlock`, `adm_run_astep` `admRunAstep`,
`hemit_astep_aux` `hemitAstepAux`, `hemit_astep` `hemitAstep`, `hart_conf_coverage`
`hartConfCoverage`; `OpaxWit.wt_*` ↦ `OpaxWit.wt*` (`wt_pa` `wtPa`, `wt_pa_ram` `wtPaRam`,
`wt_ak` `wtAk`, `wt_ak_plain` `wtAkPlain`, `wt_rreq` `wtRreq`, `wt_wreq` `wtWreq`, `wt_val`
`wtVal`, `wt_m2` `wtM2`, `wt_m` `wtM`, `wt_p0/p1/p2` `wtP0/P1/P2`, `wt_base` `wtBase`, `wt_row`
`wtRow`, `wt_read_step` `wtReadStep`, `wt_write_step`
`wtWriteStep`, `wt_aread` `wtAread`, `wt_astep_write` `wtAstepWrite`, `wt_run` `wtRun`,
`wt_coverage` `wtCoverage`, `wt_reducible_end` `wtReducibleEnd`, `wt_stuck_empty_row`
`wtStuckEmptyRow`, `wt_reducible_empty_row` `wtReducibleEmptyRow`, `wt_fetch` `wtFetch`, `wt_dv` `wtDv`, `wt_items` `wtItems`, `wt_ws1_relp`
`wtWs1Relp`, `wt_pcls_store` `wtPclsStore`, `wt_hart_conf` `wtHartConf`, `wt_hemit_astep`
`wtHemitAstep`).

**Not ported:** `fetch_answers`, `AStep_fetch`, `wt_T`, `wt_img`, `wt_fT`, `wt_fimg` (deleted by
O2 Stage C, owner Q-C2; deviation 2); the `Print Assumptions` block is replaced by the lint.

**W13 (I) (plan `notes/weak-allocproc-plan.md` §C W13 (I); [OWN.27]).** THE RETIRED OPAX TIER KEEPS MMIO ADMINISTRATIVE: `WeakAxRealize.lbAdmin` dropped `LDev` (MMIO accesses are I/O-class graph events, [OWN.27]); this tier's `AStepAdmin` reads `AxOpsem.lbAdminAx` (= the pre-(I) alphabet, `LDev` included; every `Ax*` file's former `lbAdmin` is `AxOpsem.lbAdminAx`, a semantics-preserving rename), bridged from the graph tier's by `AxOpsem.lbAdminAxOf`.  The tier has no I/O row item, so `hemitAstepAux`/`hemitAstep`/`hartConfCoverage` take the premise that the emission is `LDev`-free.
-/
import Weak.WeakRvwmoConf
import Weak.AxGraphCat
import Weak.AxPair

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 1. Thread state and identities -/

/-- The per-hart thread state: the program node and the row position. -/
structure Athread where
  AThread ::
  atP : Pexv6
  atK : Nat

/-- THE IDENTITY of a row item: kind, the synchronization flag(s), the base address and the width
in bytes.  Values, timestamps and the store's class are dropped. -/
inductive AidentT where
  | IRead (aq : Bool) (base : Int) (n : Nat)
  | IWrite (rl : Bool) (base : Int) (n : Nat)
  | IRmw (aq rl : Bool) (base : Int) (n : Nat)
  | IFence (pr pw sr sw : Bool)
  /-- W13 (E): an I/O-class event (kind, base, byte count). -/
  | IIo (kind : IoKind) (base : Int) (n : Nat)
  deriving DecidableEq

def aident (lb : Lbl) : AidentT :=
  match lb with
  | .LLoad aq base _ vs => .IRead aq base vs.length
  | .LStore rl base vs _ => .IWrite rl base vs.length
  | .LFence pr pw sr sw => .IFence pr pw sr sw
  | .LRmw aq rl base _ _ wvs _ => .IRmw aq rl base wvs.length
  | .LIo kd base vs => .IIo kd base vs.length

/-- The read half / write half / fence content of an identity. -/
def aidentRd (id : AidentT) : Option (Bool × Int × Nat) :=
  match id with
  | .IRead aq base n => some (aq, base, n)
  | .IRmw aq _ base n => some (aq, base, n)
  | _ => none

def aidentWr (id : AidentT) : Option (Bool × Int × Nat) :=
  match id with
  | .IWrite rl base n => some (rl, base, n)
  | .IRmw _ rl base n => some (rl, base, n)
  | _ => none

def aidentFence (id : AidentT) : Option (Bool × Bool × Bool × Bool) :=
  match id with
  | .IFence pr pw sr sw => some (pr, pw, sr, sw)
  | _ => none

/-- The width, and how far the READ half moves the row position. -/
def aidentN (id : AidentT) : Nat :=
  match id with
  | .IRead _ _ n | .IWrite _ _ n | .IRmw _ _ _ n | .IIo _ _ n => n
  | .IFence _ _ _ _ => 0

def aidentAdvRd (id : AidentT) : Nat :=
  match id with
  | .IRmw _ _ _ _ => 0
  | _ => 1

theorem aidentRdN (id : AidentT) (aq : Bool) (base : Int) (n : Nat) :
    aidentRd id = some (aq, base, n) → aidentN id = n := by
  intro h
  cases id <;> simp_all [aidentRd, aidentN]

theorem aidentWrN (id : AidentT) (rl : Bool) (base : Int) (n : Nat) :
    aidentWr id = some (rl, base, n) → aidentN id = n := by
  intro h
  cases id <;> simp_all [aidentWr, aidentN]

/-! ### 1.1 The instance labels' halves (deviation 2: a fetch has no read half) -/

def wlRd (l : Wlabel) : Option (Bool × Int × Nat) :=
  match l with
  | LLoad aq _ base tvs _ => some (aq, base, tvs.length)
  | LExLoad aq base tvs _ => some (aq, base, tvs.length)
  | _ => none

def wlWr (l : Wlabel) : Option (Bool × Int × Nat) :=
  match l with
  | LStore rl base data _ _ => some (rl, base, data.length)
  | LExStore rl base data _ _ => some (rl, base, data.length)
  | _ => none

/-- The DATA a write label stores (instance side). -/
def wlWdata (l : Wlabel) : Option (List (BitVec 8)) :=
  match l with
  | LStore _ _ data _ _ => some data
  | LExStore _ _ data _ _ => some data
  | _ => none

/-- The DATA a row item stores (a store's bytes, an RMW's WRITTEN bytes). -/
def lblData (l : Lbl) : Option (List (BitVec 8)) :=
  match l with
  | .LStore _ _ vs _ => some vs
  | .LRmw _ _ _ _ _ wvs _ => some wvs
  | _ => none

def wlFence (l : Wlabel) : Option (Bool × Bool × Bool × Bool) :=
  match l with
  | LFence pr pw sr sw => some (pr, pw, sr, sw)
  | _ => none

def wlRmw (l : Wlabel) : Bool :=
  match l with
  | LRmw .. => true
  | _ => false

/-- The bytes a read label returns (`[]` off the reads). -/
def wlRvals (l : Wlabel) : List (BitVec 8) :=
  match l with
  | LLoad _ _ _ tvs _ => tvs.map Prod.snd
  | LExLoad _ _ tvs _ => tvs.map Prod.snd
  | _ => []

/-- A byte list as a label payload: every byte at timestamp 0. -/
def tagVals (vs : List (BitVec 8)) : List (Nat × BitVec 8) := vs.map (fun b => (0, b))

theorem tagValsSnd (vs : List (BitVec 8)) : (tagVals vs).map Prod.snd = vs := by
  induction vs with
  | nil => rfl
  | cons b vs ih => simp only [tagVals, List.map_cons] at ih ⊢; rw [ih]

theorem tagValsLength (vs : List (BitVec 8)) : (tagVals vs).length = vs.length := by
  simp [tagVals]

theorem tagValsFst (vs : List (BitVec 8)) :
    (tagVals vs).map Prod.fst = List.replicate vs.length 0 := by
  induction vs with
  | nil => rfl
  | cons b vs ih =>
    simp only [tagVals, List.map_cons, List.length_cons, List.replicate_succ] at ih ⊢
    rw [ih]

/-- Re-valuing a read label: same identity, new bytes. -/
def wlReval (l : Wlabel) (vs : List (BitVec 8)) : Wlabel :=
  match l with
  | LLoad aq lat base _ asrc => LLoad aq lat base (tagVals vs) asrc
  | LExLoad aq base _ asrc => LExLoad aq base (tagVals vs) asrc
  | _ => l

theorem wlRdN (l : Wlabel) (aq : Bool) (base : Int) (n : Nat) :
    wlRd l = some (aq, base, n) → (wlRvals l).length = n := by
  intro h
  cases l <;> simp_all [wlRd, wlRvals]

theorem wlRevalRd (l : Wlabel) (vs : List (BitVec 8)) :
    vs.length = (wlRvals l).length → wlRd (wlReval l vs) = wlRd l := by
  intro h
  cases l <;> simp_all [wlRd, wlReval, wlRvals, tagValsLength]

theorem wlRevalRvals (l : Wlabel) (vs : List (BitVec 8)) :
    (wlRd l).isSome = true → wlRvals (wlReval l vs) = vs := by
  intro h
  cases l <;> simp_all [wlRd, wlReval, wlRvals, tagValsSnd]

/-- THE IDENTITY IS THE PROJECTION MODULO VALUES. -/
theorem aidentProj (k : WmClass) (l : Wlabel) (lb : Lbl) :
    projLbl k l = some lb → wlRmw l = false →
    wlRd l = aidentRd (aident lb) ∧ wlWr l = aidentWr (aident lb) ∧
      wlFence l = aidentFence (aident lb) := by
  intro h hr
  cases l <;> simp only [projLbl, wlRmw, reduceCtorEq, Option.some.injEq, Bool.true_eq_false]
    at h hr <;> subst h <;>
    simp [wlRd, wlWr, wlFence, aident, aidentRd, aidentWr, aidentFence]

/-- … and it has that item's DATA. -/
theorem aidentProjData (k : WmClass) (l : Wlabel) (lb : Lbl) :
    projLbl k l = some lb → wlRmw l = false → wlWdata l = lblData lb := by
  intro h hr
  cases l <;> simp only [projLbl, wlRmw, reduceCtorEq, Option.some.injEq, Bool.true_eq_false]
    at h hr <;> subst h <;> rfl

/-- The exclusive PAIR realizing a fused row item. -/
theorem aidentPair (pa pm : Pexv6) (ws : Wstate) (lb : Lbl) (l1 l2 : Wlabel) :
    hlblRealizesPair pa pm ws lb l1 l2 →
    wlRd l1 = aidentRd (aident lb) ∧ (wlRd l1).isSome = true ∧
    wlWr l2 = aidentWr (aident lb) ∧ (wlWr l2).isSome = true ∧
    aidentAdvRd (aident lb) = 0 := by
  rintro ⟨aq, rl, base, tvs, data, asrc1, asrc2, vsrc2, rfl, rfl, _, hlen, rfl⟩
  simp [wlRd, wlWr, aident, aidentRd, aidentWr, aidentAdvRd, hlen]

/-! ### 1.2 The row identity is the instance identity minus sources -/

def aidentOfInst (i : AxPair.Ident) : AidentT :=
  match i.idKind with
  | .IKload | .IKexload => .IRead i.idAq i.idBase i.idBytes
  | .IKstore | .IKexstore => .IWrite i.idRl i.idBase i.idBytes
  | .IKrmw => .IRmw i.idAq i.idRl i.idBase i.idBytes

theorem aidentProjInst (k : WmClass) (l : Wlabel) (lb : Lbl) (i : AxPair.Ident) :
    projLbl k l = some lb → lblIdent l = some i → aident lb = aidentOfInst i := by
  intro h hi
  cases l <;> simp only [projLbl, lblIdent, reduceCtorEq, Option.some.injEq] at h hi <;>
    subst h <;> subst hi <;> simp [aident, aidentOfInst]

/-! ### 1.3 The row identity is AxGraphCat's identity minus the write class -/

def aidentOfCat (i : IdentT) : AidentT :=
  match i with
  | .IdLoad aq base n => .IRead aq base n
  | .IdStore rl base n _ => .IWrite rl base n
  | .IdFence pr pw sr sw => .IFence pr pw sr sw
  | .IdRmw aq rl base n _ => .IRmw aq rl base n
  | .IdIo kd base n => .IIo kd base n

theorem aidentCat (G : Gexec) (e : Geid) (lb : Lbl) :
    gwf G → gxLbl G e = some lb → aident lb = aidentOfCat (AxGraphCat.ident lb) := by
  intro hwf hl
  have hsh := gwfLblShape G e lb hwf hl
  cases lb <;> simp_all [aident, aidentOfCat, AxGraphCat.ident]

/-! ## 2. The program / wire split of `pstepEv` (deviations 3, 4) -/

def pstepProg (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) : Prop :=
  match p, p' with
  | .PHart cpu m rs fn ib, .PHart cpu' m' rs' fn' ib' =>
      cpu' = cpu ∧
      ∃ (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind),
        rs' = ors.getD rs ∧ ib' = oib.getD ib ∧
        (pstepNode cpu m rs fn ib d.efDev l m' ors fn' d'.efDev oib obar ∧
          d' = { d with efDev := d'.efDev })
  | .PDisk dp, .PDisk dp' => pstepDisk dp d l dp' d'
  | _, _ => False

def pstepWire (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) : Prop :=
  match p, p' with
  | .PHart cpu m rs fn ib, .PHart cpu' m' rs' fn' ib' =>
      cpu' = cpu ∧
      ∃ (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind),
        rs' = ors.getD rs ∧ ib' = oib.getD ib ∧
        pstepPlic cpu m rs fn ib d l m' ors fn' d' oib obar
  | _, _ => False

theorem pstepEvSplit (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepEv p d l p' d' ↔ pstepProg p d l p' d' ∨ pstepWire p d l p' d' := by
  cases p with
  | PHart cpu m rs fn ib =>
    cases p' with
    | PHart cpu' m' rs' fn' ib' =>
      constructor
      · rintro ⟨hc, ors, oib, obar, hrs, hib, h | h⟩
        · exact .inl ⟨hc, ors, oib, obar, hrs, hib, h⟩
        · exact .inr ⟨hc, ors, oib, obar, hrs, hib, h⟩
      · rintro (⟨hc, ors, oib, obar, hrs, hib, h⟩ | ⟨hc, ors, oib, obar, hrs, hib, h⟩)
        · exact ⟨hc, ors, oib, obar, hrs, hib, .inl h⟩
        · exact ⟨hc, ors, oib, obar, hrs, hib, .inr h⟩
    | PDisk dp' =>
      exact ⟨fun h => False.elim h, fun h => h.elim (fun h => False.elim h) (fun h => False.elim h)⟩
  | PDisk dp =>
    cases p' with
    | PHart cpu' m' rs' fn' ib' =>
      exact ⟨fun h => False.elim h, fun h => h.elim (fun h => False.elim h) (fun h => False.elim h)⟩
    | PDisk dp' => exact ⟨Or.inl, fun h => h.elim id (fun h => False.elim h)⟩

/-- THE WIRE, inverted (deviation 3): `LDev`, the PLIC program at a pin write to this hart, which
it advances; the monad and the parked fence untouched; the pin set. -/
theorem pstepWireInv (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepWire p d l p' d' →
    l = LDev .dev 0 [] [] [] ∧
    ∃ (cpu : CPU) (m : SailM Unit) (rs : RegFile) (fn : Option (Bool × Bool × Bool × Bool))
      (ib : Ibch) (mm b : Bool) (k : Unit → DevProg .plic),
      p = .PHart cpu m rs fn ib ∧ d.efPlic = .op (.setPin cpu mm b) k ∧
      d' = { d with efPlic := k () } ∧ p' = .PHart cpu m (pinSet rs mm b) fn ib := by
  intro h
  cases p with
  | PHart cpu m rs fn ib =>
    cases p' with
    | PHart cpu' m' rs' fn' ib' =>
      obtain ⟨rfl, ors, oib, obar, rfl, rfl, mm, b, k, hpl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, cpu', m', rs, fn', ib, mm, b, k, rfl, hpl, rfl, rfl⟩
    | PDisk _ => exact False.elim h
  | PDisk _ =>
    cases p' with
    | PHart _ _ _ _ _ => exact False.elim h
    | PDisk _ => exact False.elim h

/-- The wire is available at every hart state whenever the PLIC program sits at a pin write to
it (deviation 3). -/
theorem pstepWireAlways (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (mm b : Bool)
    (k : Unit → DevProg .plic) :
    d.efPlic = .op (.setPin cpu mm b) k →
    pstepWire (.PHart cpu m rs fn ib) d (LDev .dev 0 [] [] []) (.PHart cpu m (pinSet rs mm b) fn ib)
      { d with efPlic := k () } :=
  fun hd => ⟨rfl, some (pinSet rs mm b), none, none, rfl, rfl,
    pstepPlicPin cpu mm b k rs d hd m fn ib⟩

/-! ## 3. Read nodes: the value-generic step and its inverse -/

/-- The little-endian word of a byte list, at the read's width (deviation 5). -/
def wordOfBytes (n : Nat) (vs : List (BitVec 8)) : BitVec (8 * n) :=
  assembleBytes n (fun j => vs.getD j 0#8)

theorem wordOfBytesByte (n : Nat) (vs : List (BitVec 8)) (j : Nat) :
    vs.length = n → j < n → nthByte (wordOfBytes n vs) j = vs.getD j 0#8 :=
  fun _ hj => nthByteAssembleBytes n _ j hj

theorem wordOfBytesWbytes (n : Nat) (w : BitVec (8 * n)) :
    wordOfBytes n (WeakInterpProj.wbytes n w) = w := by
  apply bvEqOfBytes
  intro j hj
  rw [wordOfBytesByte n _ j (wbytesLength n w) hj, List.getD_eq_getElem?_getD,
    wbytesLookup n w j hj]
  rfl

theorem wbytesWordOfBytes (n : Nat) (vs : List (BitVec 8)) :
    vs.length = n → WeakInterpProj.wbytes n (wordOfBytes n vs) = vs := by
  intro hl
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · have hjv : j < vs.length := by omega
    rw [wbytesLookup n _ j hj, wordOfBytesByte n vs j hl hj, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hjv]
    rfl
  · rw [List.getElem?_eq_none_iff.2 (by rw [wbytesLength]; omega),
      List.getElem?_eq_none_iff.2 (by omega)]

/-- (Lean-only) the Lean read arm's per-byte clause, as Rocq's byte-list equation. -/
theorem AxOpsem.sndEqWbytes (n : Nat) (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)) :
    tvs.length = n → (∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w j)) →
    tvs.map Prod.snd = WeakInterpProj.wbytes n w := by
  intro hl hby
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [hby j hj, wbytesLookup n w j hj]
  · rw [List.getElem?_eq_none_iff.2 (by simp only [List.length_map]; omega),
      List.getElem?_eq_none_iff.2 (by rw [wbytesLength]; omega)]

/-- (Lean-only) the per-byte clause of a re-valued read at `wordOfBytes`. -/
theorem AxOpsem.tagBytes (n : Nat) (vs : List (BitVec 8)) :
    vs.length = n →
    ∀ j : Nat, j < n → ((tagVals vs).map Prod.snd)[j]? = some (nthByte (wordOfBytes n vs) j) := by
  intro hl j hj
  have hjv : j < vs.length := by omega
  rw [tagValsSnd, wordOfBytesByte n vs j hl hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hjv]
  rfl

/-- The read label of a RAM `memRead` node (deviation 2: `fe` is the fetch flag). -/
def rdLabel (fe ex aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) :
    Wlabel :=
  if fe then LIFetch base tvs else if ex then LExLoad aq base tvs asrc else LLoad aq false base tvs asrc

def rdAsrc (ex : Bool) (ib : Ibch) : List Dsrc :=
  if ex then depsAsrc (depsOfIb ib.ibBits) else []

theorem rdLabelReval (fe ex aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) (vs : List (BitVec 8)) : fe = false →
    wlReval (rdLabel fe ex aq base tvs asrc) vs = rdLabel fe ex aq base (tagVals vs) asrc := by
  intro hfe; subst hfe; cases ex <;> rfl

theorem rdLabelRvals (fe ex aq : Bool) (base : Int) (tvs : List (Nat × BitVec 8))
    (asrc : List Dsrc) : fe = false →
    wlRvals (rdLabel fe ex aq base tvs asrc) = tvs.map Prod.snd := by
  intro hfe; subst hfe; cases ex <;> rfl

theorem pnodeStepReadAny (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : DevStates) (vs : List (BitVec 8)) :
    devAddr req.pa = false → vs.length = n →
    pnodeStep (.impure (.ok (.memRead n va req)) KK) rs ib d
      (rdLabel (classify req.access_kind).akIfetch (classify req.access_kind).akLatest
        (classify req.access_kind).akSync (paZ req.pa) (tagVals vs)
        (rdAsrc (classify req.access_kind).akLatest ib))
      (KK (.Ok (wordOfBytes n vs, none))) none none d none none := by
  intro hdev hlen
  have hby := AxOpsem.tagBytes n vs hlen
  have htl : (tagVals vs).length = n := (tagValsLength vs).trans hlen
  simp only [pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte]
  cases hf : (classify req.access_kind).akIfetch
  · cases hl : (classify req.access_kind).akLatest
    · refine Or.inr ⟨rfl, Or.inl ⟨rfl, wordOfBytes n vs, tagVals vs, htl, hby,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
        first | rfl | trivial | simp only [rdLabel, rdAsrc, Bool.false_eq_true, ↓reduceIte]
    · refine Or.inr ⟨rfl, Or.inr ⟨rfl, wordOfBytes n vs, tagVals vs, htl, hby,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
        first | rfl | trivial | simp only [rdLabel, rdAsrc, Bool.false_eq_true, ↓reduceIte]
  · refine Or.inl ⟨rfl, wordOfBytes n vs, tagVals vs, htl, hby, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | trivial | simp only [rdLabel, ↓reduceIte]

theorem AxOpsem.wlRdErwLabel (w : ErwKind) : wlRd (erwLabel w) = none := by
  cases w <;> rfl

theorem AxOpsem.wlRdEbarLabel (b : barrier_kind) : wlRd (ebarLabel b) = none := by
  obtain ⟨_, _, _, _, h⟩ := ebarLabelFence b
  rw [h]; rfl

/-- THE INVERSE: a `pnodeStep` whose label is a read sits at a RAM `memRead` node. -/
theorem pnodeStepReadInv (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m' : SailM Unit) (ors : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep m rs ib d l m' ors fn' d' oib obar → (wlRd l).isSome = true →
    ∃ (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit)
      (w : BitVec (8 * n)) (tvs : List (Nat × BitVec 8)),
      m = .impure (.ok (.memRead n va req)) KK ∧ devAddr req.pa = false ∧
      (classify req.access_kind).akIfetch = false ∧
      l = rdLabel (classify req.access_kind).akIfetch (classify req.access_kind).akLatest
            (classify req.access_kind).akSync (paZ req.pa) tvs
            (rdAsrc (classify req.access_kind).akLatest ib) ∧
      tvs.map Prod.snd = WeakInterpProj.wbytes n w ∧
      m' = KK (.Ok (w, none)) ∧ ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧
      obar = none := by
  intro h hrd
  match m, h with
  | .pure _, h => obtain ⟨_, rfl, _⟩ := h; simp [wlRd] at hrd
  | .impure (.error _) _, h => exact h.elim
  | .impure (.ok o) k, h =>
    cases o with
    | memRead n va req =>
      simp only [pnodeStep] at h
      split at h
      · obtain ⟨_, _, rfl, _⟩ := h; simp [wlRd] at hrd
      · rename_i hd
        have hdev : devAddr req.pa = false := by simpa using hd
        rcases h with ⟨hif, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
          ⟨hif, ⟨hlat, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
            ⟨hlat, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · simp [wlRd] at hrd
        · exact ⟨n, va, req, k, w, tvs, rfl, hdev, hif,
            by simp only [rdLabel, rdAsrc, hif, hlat, Bool.false_eq_true, ↓reduceIte],
            AxOpsem.sndEqWbytes n w tvs hlen hby, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨n, va, req, k, w, tvs, rfl, hdev, hif,
            by simp only [rdLabel, rdAsrc, hif, hlat, Bool.false_eq_true, ↓reduceIte],
            AxOpsem.sndEqWbytes n w tvs hlen hby, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | memWrite n va req =>
      simp only [pnodeStep] at h
      split at h
      · split at h
        · obtain ⟨_, rfl, _⟩ := h; simp [wlRd] at hrd
        · exact h.elim
      · split at h
        · rcases h with ⟨_, ⟨_, rfl, _⟩ | ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩⟩ <;> simp [wlRd] at hrd
        · exact h.elim
    | regWrite r v =>
      obtain ⟨rfl, _⟩ := h
      rw [AxOpsem.wlRdErwLabel] at hrd; simp at hrd
    | barrier b =>
      obtain ⟨rfl, _⟩ := h
      rw [AxOpsem.wlRdEbarLabel] at hrd; simp at hrd
    | choose p => obtain ⟨_, rfl, _⟩ := h; simp [wlRd] at hrd
    | readRam => exact h.elim
    | writeRam => exact h.elim
    | regRead => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | cacheOp => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | tlbi => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | translationStart => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | translationEnd => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | takeException => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | returnException => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | cycleCount => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | getCycleCount => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | message => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd
    | instrAnnounce n w =>
      obtain ⟨rfl, _⟩ := h
      rcases annLabelOr n w with e | e <;> rw [e] at hrd <;> simp [wlRd] at hrd
    | branchAnnounce => obtain ⟨rfl, _⟩ := h; simp [wlRd] at hrd

/-- THE READ CONTINUATION: a program step with a read label determines a function `F` from byte
strings to successor programs, at every device state.  Harts and the disk agent alike. -/
theorem pstepProgReadCont (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg p d l p' d' → (wlRd l).isSome = true →
    ∃ F : List (BitVec 8) → Pexv6,
      p' = F (wlRvals l) ∧ d' = d ∧
      ∀ vs, vs.length = (wlRvals l).length → ∀ d0, pstepProg p d0 (wlReval l vs) (F vs) d0 := by
  intro h hrd
  match p, p', h with
  | .PHart cpu m rs fn ib, .PHart cpu' m' rs' fn' ib', h =>
    obtain ⟨hc, ors, oib, obar, rfl, rfl, hn, hd⟩ := h
    subst cpu'
    cases fn with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, _⟩ := hn
      simp [wlRd] at hrd
    | none =>
      obtain ⟨n, va, req, KK, w, tvs, rfl, hdev, hfe, rfl, htv, rfl, rfl, rfl, hd', rfl, rfl⟩ :=
        pnodeStepReadInv _ _ _ _ _ _ _ _ _ _ _ hn hrd
      refine ⟨fun vs => .PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib, ?_, ?_, ?_⟩
      · simp only [rdLabelRvals _ _ _ _ _ _ hfe, htv, wordOfBytesWbytes, Option.getD_none]
      · rw [hd, hd']
      · intro vs hvs d0
        refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
        rw [rdLabelReval _ _ _ _ _ _ _ hfe]
        exact pnodeStepReadAny n va req KK rs ib d0.efDev vs hdev
          (by rw [hvs, rdLabelRvals _ _ _ _ _ _ hfe, htv, wbytesLength])
  | .PDisk dp, .PDisk dp', h =>
    rcases h with ⟨hp, hd⟩ | ⟨_, rfl, _⟩
    · rcases hp with ⟨_, rfl, _⟩ | ⟨pa, n, aq, k, tvs, rfl, hlen, rfl, rfl, hd'⟩ |
        ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, rfl, _⟩ |
        ⟨_, _, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
      · simp [wlRd] at hrd
      · refine ⟨fun vs => .PDisk (some (k vs)), rfl, ?_, ?_⟩
        · rw [hd, hd']
        · intro vs hvs d0
          refine Or.inl ⟨Or.inr (Or.inl ⟨pa, n, aq, k, tagVals vs, rfl, ?_, rfl,
            by rw [tagValsSnd], rfl⟩), rfl⟩
          rw [tagValsLength, hvs]
          simp [wlRvals, hlen]
      all_goals simp [wlRd] at hrd
    · simp [wlRd] at hrd
  | .PHart .., .PDisk _, h => exact False.elim h
  | .PDisk _, .PHart .., h => exact False.elim h

/-- The label of any step from a RAM `memRead` node is a read of the node's width. -/
theorem pstepProgMemreadLbl (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d l p' d' →
    (wlRd l).isSome = true ∧ (wlRvals l).length = n := by
  intro hdev hfe h
  cases p' with
  | PDisk _ => exact False.elim h
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨_, ors, oib, obar, _, _, hn, _⟩ := h
    simp only [pstepNode, pnodeStep, hdev, Bool.false_eq_true, ↓reduceIte] at hn
    rcases hn with ⟨hif, _⟩ | ⟨_, ⟨_, w, tvs, hlen, _, rfl, _⟩ |
      ⟨_, w, tvs, hlen, _, rfl, _⟩⟩
    · rw [hfe] at hif; exact absurd hif Bool.false_ne_true
    all_goals simp [wlRd, wlRvals, hlen]

/-! ## 4. The opax step relations -/

/-- (W13 (I), deviation 5) THE RETIRED TIER'S ADMINISTRATIVE ALPHABET: the pre-(I) graph-tier
`lbAdmin`, fabric marker INCLUDED.  W13 (I) dropped `LDev` from `WeakAxRealize.lbAdmin` (an MMIO
access is now an I/O-class graph event, [OWN.27]); the opax tier keeps its MMIO accesses as
position-keeping administrative steps, exactly as before (it sees no I/O row item). -/
def AxOpsem.lbAdminAx (instr : Bool) (l : Wlabel) : Prop :=
  match l with
  | .LSilent | .LDev .. | .LRegW .. | .LCtrl _ => True
  | .LInstr | .LIFetch .. => instr = true
  | _ => False

/-- The graph tier's alphabet is a sub-alphabet of the retired tier's. -/
theorem AxOpsem.lbAdminAxOf (instr : Bool) (l : Wlabel) : lbAdmin instr l → AxOpsem.lbAdminAx instr l := by
  cases l <;> simp [lbAdmin, AxOpsem.lbAdminAx]

/-- (A) EVERYTHING BUT READS, program arms only, INDEXED BY THE INSTANCE LABEL (Rocq fact 5).
A fetch is an ADMINISTRATIVE step (`AStepAdmin` at `AxOpsem.lbAdminAx true (LIFetch ..)`; deviation 2). -/
inductive AxOpsem.astepProg (row : List Lbl)  : Athread → Wlabel → Athread → Prop where
  | AStepAdmin (p : Pexv6) (k : Nat) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
      AxOpsem.lbAdminAx true l →
      pstepProg p d l p' d' →
      AxOpsem.astepProg row ⟨p, k⟩ l ⟨p', k⟩
  | AStepWrite (p : Pexv6) (k : Nat) (d : Efab) (l : Wlabel) (lb : Lbl) (p' : Pexv6)
      (d' : Efab) :
      row[k]? = some lb →
      (wlWr l).isSome = true → wlWr l = aidentWr (aident lb) →
      wlWdata l = lblData lb →
      pstepProg p d l p' d' →
      AxOpsem.astepProg row ⟨p, k⟩ l ⟨p', k + 1⟩
  | AStepFence (p : Pexv6) (k : Nat) (d : Efab) (l : Wlabel) (lb : Lbl) (p' : Pexv6)
      (d' : Efab) :
      row[k]? = some lb →
      (wlFence l).isSome = true → wlFence l = aidentFence (aident lb) →
      pstepProg p d l p' d' →
      AxOpsem.astepProg row ⟨p, k⟩ l ⟨p', k + 1⟩

/-- The label is the program's own step's label. -/
theorem astepProgPstep (row : List Lbl) 
    (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' → ∃ d d', pstepProg s.atP d l s'.atP d' := by
  intro h
  cases h with
  | AStepAdmin _ _ d _ _ d' _ hs => exact ⟨d, d', hs⟩
  | AStepWrite _ _ d _ _ _ d' _ _ _ _ hs => exact ⟨d, d', hs⟩
  | AStepFence _ _ d _ _ _ d' _ _ _ hs => exact ⟨d, d', hs⟩

/-- The PLIC wire, as an opax step: position kept, program moved by `pstepWire`. -/
def awire (s s' : Athread) : Prop :=
  s'.atK = s.atK ∧ ∃ d d', pstepWire s.atP d (LDev .dev 0 [] [] []) s'.atP d'

def astep (row : List Lbl) 
    (s s' : Athread) : Prop :=
  (∃ l, AxOpsem.astepProg row s l s') ∨ awire s s'

/-- (B) THE READ, with its continuation; every byte string of the identity's width is
accepted. -/
def areadStep (row : List Lbl) (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) :
    Prop :=
  ∃ lb, row[s.atK]? = some lb ∧ aident lb = id ∧ (aidentRd id).isSome = true ∧
    ∀ vs, vs.length = aidentN id →
      ∃ l d d', wlRd l = aidentRd id ∧ wlRvals l = vs ∧
        pstepProg s.atP d l (K vs).atP d' ∧ (K vs).atK = s.atK + aidentAdvRd id

/-- The glue: one relation for the progress and coverage lemmas. -/
inductive astepAny (row : List Lbl)  :
    Athread → Athread → Prop where
  | AAStep (s s' : Athread) : astep row s s' → astepAny row s s'
  | AARead (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) (vs : List (BitVec 8)) :
      areadStep row s id K → vs.length = aidentN id → astepAny row s (K vs)

theorem astepOfRead (row : List Lbl) 
    (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) :
    areadStep row s id K → ∀ vs, vs.length = aidentN id → astepAny row s (K vs) :=
  fun h vs hvs => .AARead s id K vs h hvs

/-- The hart's OWN steps — everything but the wire. -/
def astepOwn (row : List Lbl) 
    (s s' : Athread) : Prop :=
  (∃ l, AxOpsem.astepProg row s l s') ∨
  ∃ id K vs, areadStep row s id K ∧ vs.length = aidentN id ∧ s' = K vs

theorem astepAnyOwn (row : List Lbl) 
    (s s' : Athread) :
    astepAny row s s' ↔ astepOwn row s s' ∨ awire s s' := by
  constructor
  · intro h
    match h with
    | .AAStep _ _ h =>
      rcases h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    | .AARead _ id K vs h hvs => exact .inl (.inr ⟨id, K, vs, h, hvs, rfl⟩)
  · rintro ((h | ⟨id, K, vs, h, hvs, rfl⟩) | h)
    · exact .AAStep _ _ (.inl h)
    · exact .AARead _ _ _ _ h hvs
    · exact .AAStep _ _ (.inr h)

/-! ### 4.1 Positions: monotone, one per event step, valid -/

theorem astepProgK (row : List Lbl) 
    (s : Athread) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row s l s' →
    s'.atK = s.atK ∨ (s'.atK = s.atK + 1 ∧ (row[s.atK]?).isSome = true) := by
  intro h
  cases h with
  | AStepAdmin => exact .inl rfl
  | AStepWrite _ _ _ _ _ _ _ hrow => exact .inr ⟨rfl, by simp [hrow]⟩
  | AStepFence _ _ _ _ _ _ _ hrow => exact .inr ⟨rfl, by simp [hrow]⟩

theorem areadStepK (row : List Lbl) (s : Athread) (id : AidentT)
    (K : List (BitVec 8) → Athread) (vs : List (BitVec 8)) :
    areadStep row s id K → vs.length = aidentN id →
    (K vs).atK = s.atK ∨ ((K vs).atK = s.atK + 1 ∧ (row[s.atK]?).isSome = true) := by
  rintro ⟨lb, hrow, rfl, _, HK⟩ hvs
  obtain ⟨_, _, _, _, _, _, hk⟩ := HK vs hvs
  rw [hk]
  cases aident lb <;> simp [aidentAdvRd, hrow]

theorem astepAnyK (row : List Lbl) 
    (s s' : Athread) :
    astepAny row s s' →
    s'.atK = s.atK ∨ (s'.atK = s.atK + 1 ∧ (row[s.atK]?).isSome = true) := by
  intro h
  match h with
  | .AAStep _ _ h =>
    rcases h with ⟨l, h⟩ | ⟨hk, _⟩
    · exact astepProgK row _ l _ h
    · exact .inl hk
  | .AARead _ id K vs h hvs => exact areadStepK row _ id K vs h hvs

theorem astepProgressMono (row : List Lbl) 
    (s s' : Athread) : astepAny row s s' → s.atK ≤ s'.atK := by
  intro h
  rcases astepAnyK row s s' h with h | ⟨h, _⟩ <;> omega

theorem astepAdminOrEvent (row : List Lbl)  (s s' : Athread) :
    astepAny row s s' → s'.atK = s.atK ∨ s'.atK = s.atK + 1 := by
  intro h
  rcases astepAnyK row s s' h with h | ⟨h, _⟩
  · exact .inl h
  · exact .inr h

/-- An event step consumes a VALID position (AxSL's `progress_is_valid`). -/
theorem astepEventValid (row : List Lbl) 
    (s s' : Athread) :
    astepAny row s s' → s'.atK = s.atK + 1 → s.atK < row.length := by
  intro h hk
  rcases astepAnyK row s s' h with h | ⟨_, hv⟩
  · omega
  · exact lookup_lt_is_Some_1 hv

theorem arunKMono (row : List Lbl) 
    (s s' : Athread) : rtc (astepAny row) s s' → s.atK ≤ s'.atK := by
  intro h
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ h2 ih => exact Nat.le_trans ih (astepProgressMono row _ _ h2)

/-! ### 4.2 Consumption: the positions a run consumes are its interval -/

def consumed (row : List Lbl) 
    (s s' : Athread) (j : Nat) : Prop :=
  ∃ s1 s2, rtc (astepAny row) s s1 ∧ astepAny row s1 s2 ∧
    rtc (astepAny row) s2 s' ∧ s1.atK = j ∧ s2.atK = j + 1

theorem arunConsumedIff (row : List Lbl) 
    (s s' : Athread) (j : Nat) :
    rtc (astepAny row) s s' →
    (consumed row s s' j ↔ s.atK ≤ j ∧ j < s'.atK) := by
  intro hr
  constructor
  · rintro ⟨s1, s2, h1, _, h2, rfl, hk2⟩
    have := arunKMono row _ _ h1
    have := arunKMono row _ _ h2
    omega
  · induction hr with
    | refl => intro hj; omega
    | @tail b c hab hbc ih =>
      rintro ⟨hle, hlt⟩
      rcases astepAnyK row _ _ hbc with heq | ⟨heq, _⟩
      · obtain ⟨a1, a2, ha1, ha12, ha2, hk1, hk2⟩ := ih ⟨hle, by omega⟩
        exact ⟨a1, a2, ha1, ha12, rtc_r ha2 hbc, hk1, hk2⟩
      · by_cases hjb : j = b.atK
        · exact ⟨b, c, hab, hbc, rtc_refl _, hjb.symm, by omega⟩
        · obtain ⟨a1, a2, ha1, ha12, ha2, hk1, hk2⟩ := ih ⟨hle, by omega⟩
          exact ⟨a1, a2, ha1, ha12, rtc_r ha2 hbc, hk1, hk2⟩

theorem consumedBetween (row : List Lbl) 
    (s s' : Athread) (j : Nat) :
    consumed row s s' j → s.atK ≤ j ∧ j < s'.atK := by
  rintro ⟨s1, s2, h1, _, h2, rfl, hk2⟩
  have := arunKMono row _ _ h1
  have := arunKMono row _ _ h2
  omega

/-- AxSL's `tpcoverage`: a run from position 0 that reaches `row.length` consumes exactly the
row. -/
theorem coverageOfRow (row : List Lbl) 
    (p p' : Pexv6) :
    rtc (astepAny row) ⟨p, 0⟩ ⟨p', row.length⟩ →
    ∀ j, consumed row ⟨p, 0⟩ ⟨p', row.length⟩ j ↔ j < row.length := by
  intro hr j
  rw [arunConsumedIff row _ _ j hr]
  exact ⟨fun h => h.2, fun h => ⟨Nat.zero_le _, h⟩⟩

/-! ### 4.3 `terminated`, `reducible`, `notStuck` -/

/-- Harts never terminate (Rocq fact 4). -/
def terminated (_s : Athread) : Prop := False

/-- The wire never blocks (deviation 3: any pin delivery, from any fabric's devices). -/
theorem awireAlways (cpu : CPU) (m : SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (k : Nat) (d : Efab) (mm b : Bool) :
    awire ⟨.PHart cpu m rs fn ib, k⟩ ⟨.PHart cpu m (pinSet rs mm b) fn ib, k⟩ :=
  ⟨rfl, { d with efPlic := .op (.setPin cpu mm b) (fun _ => d.efPlic) }, _,
    pstepWireAlways cpu m rs fn ib _ mm b (fun _ => d.efPlic) rfl⟩

/-- `reducible`: the program's OWN progress in SOME row extension. -/
def reducible (row : List Lbl) 
    (s : Athread) : Prop :=
  ∃ ext s', astepOwn (row ++ ext) s s'

def notStuck (row : List Lbl) 
    (s : Athread) : Prop :=
  terminated s ∨ reducible row s

/-! ### 4.4 The step relations read the row at the current position only -/

theorem astepProgRowAgree (row row' : List Lbl)  (s : Athread) (l : Wlabel) (s' : Athread) :
    row[s.atK]? = row'[s.atK]? →
    AxOpsem.astepProg row s l s' → AxOpsem.astepProg row' s l s' := by
  intro hag h
  cases h with
  | AStepAdmin p k d l p' d' ha hs => exact .AStepAdmin p k d l p' d' ha hs
  | AStepWrite p k d l lb p' d' hrow hs1 hid hdat hs =>
    have hag' : row[k]? = row'[k]? := hag
    exact .AStepWrite p k d l lb p' d' (hag'.symm.trans hrow) hs1 hid hdat hs
  | AStepFence p k d l lb p' d' hrow hs1 hid hs =>
    have hag' : row[k]? = row'[k]? := hag
    exact .AStepFence p k d l lb p' d' (hag'.symm.trans hrow) hs1 hid hs

theorem areadStepRowAgree (row row' : List Lbl) (s : Athread) (id : AidentT)
    (K : List (BitVec 8) → Athread) :
    row[s.atK]? = row'[s.atK]? → areadStep row s id K → areadStep row' s id K := by
  rintro hag ⟨lb, hrow, hid, hrd, HK⟩
  exact ⟨lb, hag.symm.trans hrow, hid, hrd, HK⟩

theorem astepOwnRowAgree (row row' : List Lbl)  (s s' : Athread) :
    row[s.atK]? = row'[s.atK]? → astepOwn row s s' → astepOwn row' s s' := by
  rintro hag (⟨l, h⟩ | ⟨id, K, vs, h, hvs, rfl⟩)
  · exact .inl ⟨l, astepProgRowAgree row row' s l _ hag h⟩
  · exact .inr ⟨id, K, vs, areadStepRowAgree row row' s id K hag h, hvs, rfl⟩

theorem astepAnyRowAgree (row row' : List Lbl)  (s s' : Athread) :
    row[s.atK]? = row'[s.atK]? → astepAny row s s' → astepAny row' s s' := by
  intro hag h
  rw [astepAnyOwn] at h ⊢
  rcases h with h | h
  · exact .inl (astepOwnRowAgree row row' s s' hag h)
  · exact .inr h

theorem reducibleValid (row : List Lbl) 
    (s : Athread) :
    s.atK < row.length → (reducible row s ↔ ∃ s', astepOwn row s s') := by
  intro hk
  constructor
  · rintro ⟨ext, s', h⟩
    exact ⟨s', astepOwnRowAgree (row ++ ext) row s s' (lookup_app_l hk) h⟩
  · rintro ⟨s', h⟩
    exact ⟨[], s', by rw [List.append_nil]; exact h⟩

/-! ### 4.5 The graph-level instance -/

def growG (G : Gexec) (i : Nat) : List Lbl := (G.gxProg[i]?).getD []

def progressIsValidG (G : Gexec) (i k : Nat) : Prop := (gxLbl G (i, k)).isSome = true

theorem progressIsValidGrowG (G : Gexec) (i k : Nat) :
    progressIsValidG G i k ↔ k < (growG G i).length := by
  unfold progressIsValidG growG gxLbl
  dsimp only
  cases G.gxProg[i]? with
  | none => simp
  | some row => simp

theorem growGLookup (G : Gexec) (i : Nat) (row : List Lbl) :
    G.gxProg[i]? = some row → growG G i = row := by
  intro h
  simp [growG, h]

def reducibleG (G : Gexec) (i : Nat) 
    (s : Athread) : Prop :=
  reducible (growG G i) s

def notStuckG (G : Gexec) (i : Nat) 
    (s : Athread) : Prop :=
  notStuck (growG G i) s

/-- The `Gdexec` instance (the names the design uses). -/
def AxOpsem.grow (GD : Gdexec) : Nat → List Lbl := growG GD.gdG

def progressIsValid (GD : Gdexec) : Nat → Nat → Prop := progressIsValidG GD.gdG

def reducibleGd (GD : Gdexec) : Nat → Athread → Prop :=
  reducibleG GD.gdG

def notStuckGd (GD : Gdexec) : Nat → Athread → Prop :=
  notStuckG GD.gdG

/-! ## 5. The tree's conformance run is an opax run -/

/-- A read block: a program step with a read label that realizes the row item at `k` in identity
is an `areadStep` at `k`, instantiated at the step's own bytes. -/
theorem readBlock (row : List Lbl) 
    (p : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) (k : Nat) (lb : Lbl) :
    pstepProg p d l p' d' → (wlRd l).isSome = true →
    row[k]? = some lb → wlRd l = aidentRd (aident lb) →
    astepAny row ⟨p, k⟩ ⟨p', k + aidentAdvRd (aident lb)⟩ := by
  intro hs hrd hrow hid
  obtain ⟨F, rfl, hdd, HF⟩ := pstepProgReadCont p d l p' d' hs hrd
  subst d'
  obtain ⟨⟨aq, base, n⟩, hl⟩ := Option.isSome_iff_exists.1 hrd
  have hn : aidentN (aident lb) = (wlRvals l).length := by
    rw [aidentRdN _ aq base n (hid.symm.trans hl), wlRdN l aq base n hl]
  have hrb : areadStep row ⟨p, k⟩ (aident lb)
      (fun vs => ⟨F vs, k + aidentAdvRd (aident lb)⟩) := by
    refine ⟨lb, hrow, rfl, by rw [← hid]; exact hrd, ?_⟩
    intro vs hvs
    refine ⟨wlReval l vs, d, d, ?_, wlRevalRvals l vs hrd, HF vs (by rw [hvs, hn]) d, rfl⟩
    rw [wlRevalRd l vs (by rw [hvs, hn])]
    exact hid
  exact astepAny.AARead _ _ _ (wlRvals l) hrb hn.symm

/-- An administrative run is a run of position-preserving opax steps. -/
theorem admRunAstep (row : List Lbl) 
    (instr : Bool) (p : Pexv6) (d : Efab) (ls : List Wlabel) (p' : Pexv6) (d' : Efab) (k : Nat) :
    admRun instr p d ls p' d' → nsteps (astepAny row) ls.length ⟨p, k⟩ ⟨p', k⟩ := by
  intro h
  induction h with
  | ARnil p d => exact nsteps_O _
  | ARcons p d l p1 d1 ls p' d' ha hs _ ih =>
    refine nsteps_l ?_ ih
    apply astepAny.AAStep
    rcases (pstepEvSplit p d l p1 d1).1 hs with hs | hw
    · refine .inl ⟨l, AxOpsem.astepProg.AStepAdmin p k d l p1 d1 ?_ hs⟩
      cases instr
      · exact AxOpsem.lbAdminAxOf true l (lbAdminMono true l ha)
      · exact AxOpsem.lbAdminAxOf true l ha
    · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
      exact .inr ⟨rfl, d, d1, hw⟩

theorem hemitAstepAux (row : List Lbl) 
    (dv : Nat → Efab) (k : Nat) (ws : Wstate) (rrow : List Lbl) (p : Pexv6) (es : List Eitem)
    (pfin : Pexv6) :
    hemit dv k ws rrow p es pfin →
    (∀ j, rrow[j]? = row[k + j]?) →
    (∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst) →
    nsteps (astepAny row) es.length ⟨p, k⟩ ⟨pfin, k + rrow.length⟩ := by
  intro h
  induction h with
  | HEnil k ws p => intro _ _; exact nsteps_O _
  | HEone k ws lb rrow' p ls pa da l p' es pfin har hre hst _ ih =>
    intro hrow hnd
    have hndl : ∀ kd ba bs sa sv, l ≠ LDev kd ba bs sa sv := fun kd ba bs sa sv he =>
      hnd kd ba bs sa sv (List.mem_map.2 ⟨(l, some k), List.mem_append_right _ List.mem_cons_self,
        by rw [he]⟩)
    have hnd' : ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst := fun kd ba bs sa sv hin => by
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hin
      exact hnd kd ba bs sa sv (List.mem_map.2 ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx),
        hxe⟩)
    have hlb : row[k]? = some lb := by
      have h0 := hrow 0
      simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
      exact h0.symm
    have hrow' : ∀ j, rrow'[j]? = row[k + 1 + j]? := by
      intro j
      have hj := hrow (j + 1)
      simp only [List.getElem?_cons_succ] at hj
      rw [hj, show k + (j + 1) = k + 1 + j by omega]
    have har' := admRunAstep row true _ _ _ _ _ k har
    have hstep : astepAny row ⟨pa, k⟩ ⟨p', k + 1⟩ := by
      obtain ⟨hnb, _, _, hpr⟩ := hre
      rcases (pstepEvSplit _ _ _ _ _).1 hst with hs | hw
      · cases l with
        | LLoad aq lat base tvs asrc =>
          have hrd := (aidentProj _ _ _ hpr rfl).1
          simp only [projLbl, Option.some.injEq] at hpr; subst hpr
          exact readBlock row _ _ _ _ _ k _ hs rfl hlb hrd
        | LExLoad aq base tvs asrc =>
          have hrd := (aidentProj _ _ _ hpr rfl).1
          simp only [projLbl, Option.some.injEq] at hpr; subst hpr
          exact readBlock row _ _ _ _ _ k _ hs rfl hlb hrd
        | LIFetch => simp [projLbl] at hpr
        | LStore rl base data asrc vsrc =>
          have hwr := (aidentProj _ _ _ hpr rfl).2.1
          have hdat := aidentProjData _ _ _ hpr rfl
          exact .AAStep _ _ (.inl ⟨_, .AStepWrite _ k _ _ lb _ _ hlb rfl hwr hdat hs⟩)
        | LFence pr pw sr sw =>
          have hf := (aidentProj _ _ _ hpr rfl).2.2
          exact .AAStep _ _ (.inl ⟨_, .AStepFence _ k _ _ lb _ _ hlb rfl hf hs⟩)
        | LRmw aq rl base tvs data asrc vsrc =>
          exact absurd hst (pstepEvNoRmw _ _ _ _ _ _ _ _ _ _ _)
        | LExStore => exact False.elim hnb
        | LSilent => simp [projLbl] at hpr
        | LDev kd ba bs sa sv => exact absurd rfl (hndl kd ba bs sa sv)
        | LRegW => simp [projLbl] at hpr
        | LCtrl => simp [projLbl] at hpr
        | LInstr => simp [projLbl] at hpr
      · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
        exact absurd rfl (hndl _ _ _ _ _)
    have e1 : (eadm ls ++ (l, some k) :: es).length = ls.length + (es.length + 1) := by
      simp [eadm]
    have e2 : k + (lb :: rrow').length = k + 1 + rrow'.length := by
      simp only [List.length_cons]; omega
    rw [e1, e2]
    exact nsteps_trans har' (nsteps_l hstep (ih hrow' hnd'))
  | HEpair k ws lb rrow' p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin har1 hre hst1 har2
      hst2 _ ih =>
    intro hrow hnd
    have hnd' : ∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ es.map Prod.fst := fun kd ba bs sa sv hin => by
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hin
      exact hnd kd ba bs sa sv (List.mem_map.2 ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_cons_of_mem _ hx))), hxe⟩)
    have hlb : row[k]? = some lb := by
      have h0 := hrow 0
      simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
      exact h0.symm
    have hrow' : ∀ j, rrow'[j]? = row[k + 1 + j]? := by
      intro j
      have hj := hrow (j + 1)
      simp only [List.getElem?_cons_succ] at hj
      rw [hj, show k + (j + 1) = k + 1 + j by omega]
    obtain ⟨hrd1, hsome1, hwr2, hsome2, hadv⟩ := aidentPair _ _ _ _ _ _ hre
    have har1' := admRunAstep row true _ _ _ _ _ k har1
    have har2' := admRunAstep row false _ _ _ _ _ k har2
    have hs1 : astepAny row ⟨pa, k⟩ ⟨pm, k⟩ := by
      rcases (pstepEvSplit _ _ _ _ _).1 hst1 with hs | hw
      · have hrb := readBlock row _ _ _ _ _ k lb hs hsome1 hlb hrd1
        rw [hadv, Nat.add_zero] at hrb
        exact hrb
      · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
        simp [wlRd] at hsome1
    have hs2 : astepAny row ⟨pm2, k⟩ ⟨p', k + 1⟩ := by
      rcases (pstepEvSplit _ _ _ _ _).1 hst2 with hs | hw
      · have hdat : wlWdata l2 = lblData lb := by
          obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _, _, rfl⟩ := hre
          rfl
        exact .AAStep _ _ (.inl ⟨_, .AStepWrite _ k _ _ lb _ _ hlb hsome2 hwr2 hdat hs⟩)
      · obtain ⟨rfl, _⟩ := pstepWireInv _ _ _ _ _ hw
        simp [wlWr] at hsome2
    have e1 : (eadm ls1 ++ (l1, some k) :: (eadm ls2 ++ (l2, some k) :: es)).length =
        ls1.length + (0 + 1 + (ls2.length + (es.length + 1))) := by
      simp [eadm]; omega
    have e2 : k + (lb :: rrow').length = k + 1 + rrow'.length := by
      simp only [List.length_cons]; omega
    rw [e1, e2]
    exact nsteps_trans har1' (nsteps_trans (nsteps_l hs1 (nsteps_O _))
      (nsteps_trans har2' (nsteps_l hs2 (ih hrow' hnd'))))

/-- THE RELATION TO THE TREE: a conformant emission is an opax run of one step per emission
item, from position 0 to the row's end. -/
theorem hemitAstep (row : List Lbl)  (i : Nat)
    (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) :
    hartConf i row p0 dv em → (∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ emLabels em) →
    nsteps (astepAny row) em.emItems.length ⟨p0, 0⟩ ⟨em.emFin, row.length⟩ := by
  intro h hnd
  have := hemitAstepAux row dv 0 wsInit row p0 _ _ h (fun j => by rw [Nat.zero_add]) hnd
  rwa [Nat.zero_add] at this

theorem hartConfCoverage (row : List Lbl) 
    (i : Nat) (p0 : Pexv6) (dv : Nat → Efab) (em : Hemission) :
    hartConf i row p0 dv em → (∀ kd ba bs sa sv, LDev kd ba bs sa sv ∉ emLabels em) →
    ∀ j, consumed row ⟨p0, 0⟩ ⟨em.emFin, row.length⟩ j ↔ j < row.length := by
  intro h hnd
  exact coverageOfRow row _ _ (rtc_nsteps_2 (hemitAstep row i p0 dv em h hnd))

/-! ## 6. Non-vacuity: a hand-built two-event program -/

namespace OpaxWit

def wtPa : PAddr := BitVec.ofNat 64 0x80001000

theorem wtPaRam : devAddr wtPa = false := by decide +kernel

def wtAk : AK := .AK_explicit ⟨.AV_plain, .AS_normal⟩

theorem wtAkPlain : classify wtAk = ⟨false, false, false⟩ := rfl

def wtRreq : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := wtAk, va := none, pa := wtPa, translation := (), size := 4, tag := false }

def wtWreq (v : BitVec (8 * 4)) : Mem_write_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := wtAk, va := none, pa := wtPa, translation := (), size := 4, value := some v,
    tag := none }

def wtVal (ans : Result (BitVec (8 * 4) × Option Bool) Arch.abort) : BitVec (8 * 4) :=
  match ans with
  | .Ok (w, _) => w
  | .Err _ => 0

/-- The store node, parametric in the value; the read node feeds it. -/
def wtM2 (v : BitVec (8 * 4)) : SailM Unit :=
  .impure (.ok (.memWrite 4 64 (wtWreq v))) (fun _ => .pure ())

def wtM : SailM Unit := .impure (.ok (.memRead 4 64 wtRreq)) (fun ans => wtM2 (wtVal ans))

def wtP0 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu wtM rs none ibNone

def wtP1 (cpu : CPU) (rs : RegFile) (v : BitVec (8 * 4)) : Pexv6 :=
  .PHart cpu (wtM2 v) rs none ibNone

def wtP2 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu (.pure ()) rs none ibNone

def wtBase : Int := paZ wtPa

/-- A fabric (deviation 6: Rocq `dev0_state`). -/
def wtD0 : Efab := efInit ⟨fun _ => default⟩

/-- THE ROW: the graph says `w0` was read and `w1` written. -/
def wtRow (w0 w1 : BitVec (8 * 4)) : List Lbl :=
  [.LLoad false wtBase [0, 0, 0, 0] (WeakInterpProj.wbytes 4 w0),
   .LStore false wtBase (WeakInterpProj.wbytes 4 w1) .WCplain]

/-! ### 6.1 The two program steps, at EVERY read value -/

theorem wtReadStep (cpu : CPU) (rs : RegFile) (d : Efab) (vs : List (BitVec 8)) :
    vs.length = 4 →
    pstepProg (wtP0 cpu rs) d (LLoad false false wtBase (tagVals vs) [])
      (wtP1 cpu rs (wordOfBytes 4 vs)) d := by
  intro hlen
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  exact pnodeStepReadAny 4 64 wtRreq (fun ans => wtM2 (wtVal ans)) rs ibNone d.efDev vs wtPaRam
    hlen

theorem wtWriteStep (cpu : CPU) (rs : RegFile) (d : Efab) (v : BitVec (8 * 4)) :
    pstepProg (wtP1 cpu rs v) d
      (LStore false wtBase (WeakInterpProj.wbytes 4 v) (depsAsrc (depsOfIb ibNone.ibBits))
        (depsVsrc (depsOfIb ibNone.ibBits)))
      (wtP2 cpu rs) d := by
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  have hpa : devAddr (wtWreq v).pa = false := wtPaRam
  have hval : (wtWreq v).value = some v := rfl
  show pnodeStep (wtM2 v) rs ibNone d.efDev _ _ none none d.efDev none none
  simp only [wtM2, pnodeStep, hpa, hval, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by decide, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> first | rfl | trivial

/-! ### 6.2 The opax steps -/

/-- THE READ, value free. -/
theorem wtAread (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4)) :
    areadStep (wtRow w0 w1) ⟨wtP0 cpu rs, 0⟩ (.IRead false wtBase 4)
      (fun vs => ⟨wtP1 cpu rs (wordOfBytes 4 vs), 1⟩) := by
  refine ⟨.LLoad false wtBase [0, 0, 0, 0] (WeakInterpProj.wbytes 4 w0), rfl, ?_, rfl, ?_⟩
  · simp [aident, wbytesLength]
  · intro vs hvs
    refine ⟨LLoad false false wtBase (tagVals vs) [], wtD0, wtD0, ?_, tagValsSnd vs,
      wtReadStep cpu rs wtD0 vs hvs, rfl⟩
    simp only [wlRd, aidentRd, tagValsLength]
    rw [hvs]; rfl

/-- THE WRITE, IDENTITY AND BYTES. -/
theorem wtAstepWrite (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4)) :
    AxOpsem.astepProg (wtRow w0 w1) ⟨wtP1 cpu rs w1, 1⟩
      (LStore false wtBase (WeakInterpProj.wbytes 4 w1) (depsAsrc (depsOfIb ibNone.ibBits))
        (depsVsrc (depsOfIb ibNone.ibBits)))
      ⟨wtP2 cpu rs, 2⟩ :=
  .AStepWrite _ 1 wtD0 _ (.LStore false wtBase (WeakInterpProj.wbytes 4 w1) .WCplain) _ wtD0 rfl
    rfl rfl rfl (wtWriteStep cpu rs wtD0 w1)

/-- The whole run, for every read value whose word is the row's written one. -/
theorem wtRun (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4)) (vs : List (BitVec 8)) :
    vs.length = 4 → wordOfBytes 4 vs = w1 →
    nsteps (astepAny (wtRow w0 w1)) 2 ⟨wtP0 cpu rs, 0⟩ ⟨wtP2 cpu rs, 2⟩ := by
  intro hvs hw
  subst hw
  have h1 := astepOfRead (wtRow w0 (wordOfBytes 4 vs)) _ _ _
    (wtAread cpu rs w0 (wordOfBytes 4 vs)) vs hvs
  exact nsteps_l h1 (nsteps_l (astepAny.AAStep _ _ (.inl ⟨_, wtAstepWrite cpu rs _ _⟩))
    (nsteps_O _))

theorem wtCoverage (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4)) (j : Nat) :
    consumed (wtRow w0 w1) ⟨wtP0 cpu rs, 0⟩ ⟨wtP2 cpu rs, 2⟩ j ↔ j < 2 :=
  coverageOfRow (wtRow w0 w1) _ _
    (rtc_nsteps_2 (wtRun cpu rs w0 w1 (WeakInterpProj.wbytes 4 w1) (wbytesLength _ _)
      (wordOfBytesWbytes 4 w1))) j

/-! ### 6.3 Progress: the boundary re-fetches; an empty row needs the extension clause -/

theorem wtReducibleEnd (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4)) :
    reducible (wtRow w0 w1) ⟨wtP2 cpu rs, 2⟩ :=
  ⟨[], ⟨.PHart cpu (riscvStep false) rs none ibNone, 2⟩,
    .inl ⟨LInstr, .AStepAdmin _ 2 wtD0 LInstr _ wtD0 rfl
      ⟨rfl, none, some ibNone, none, rfl, rfl, ⟨false, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩⟩

/-- In the EMPTY row the read node has no own step (the wire aside). -/
theorem wtStuckEmptyRow (cpu : CPU) (rs : RegFile) (s' : Athread) :
    ¬ astepOwn [] ⟨wtP0 cpu rs, 0⟩ s' := by
  rintro (⟨l0, h⟩ | ⟨id, K, vs, ⟨lb, hrow, _⟩, _, _⟩)
  · match h with
    | .AStepAdmin _ _ d l _ _ ha hs =>
      obtain ⟨hrd, _⟩ := pstepProgMemreadLbl cpu 4 64 wtRreq (fun ans => wtM2 (wtVal ans)) rs
        ibNone d l _ _ wtPaRam rfl hs
      cases l <;> simp_all [wlRd, AxOpsem.lbAdminAx]
    | .AStepWrite _ _ _ _ _ _ _ hrow _ _ _ _ => simp at hrow
    | .AStepFence _ _ _ _ _ _ _ hrow _ _ _ => simp at hrow
  · simp at hrow

/-- … yet it is reducible: SOME extension supplies the read. -/
theorem wtReducibleEmptyRow (cpu : CPU) (rs : RegFile) :
    reducible [] ⟨wtP0 cpu rs, 0⟩ :=
  ⟨wtRow 0 0, ⟨wtP1 cpu rs (wordOfBytes 4 (WeakInterpProj.wbytes 4 (0 : BitVec (8 * 4)))), 1⟩,
    .inr ⟨.IRead false wtBase 4, fun vs => ⟨wtP1 cpu rs (wordOfBytes 4 vs), 1⟩,
      WeakInterpProj.wbytes 4 (0 : BitVec (8 * 4)), wtAread cpu rs 0 0, wbytesLength _ _, rfl⟩⟩

/-! ### 6.4 The fetch: an ADMINISTRATIVE step at a FETCH node (deviation 2) -/

/-- (Lean-only) the fetch request: the same range, access kind `AK_ifetch`. -/
def wtFreq : Mem_read_request 4 64 Arch.pa Arch.translation Arch.arch_ak :=
  { access_kind := .AK_ifetch (), va := none, pa := wtPa, translation := (), size := 4,
    tag := false }

/-- (Lean-only) the fetch node feeding the same store node. -/
def wtFm : SailM Unit := .impure (.ok (.memRead 4 64 wtFreq)) (fun ans => wtM2 (wtVal ans))

def wtPf0 (cpu : CPU) (rs : RegFile) : Pexv6 := .PHart cpu wtFm rs none ibNone

theorem wtFetchStep (cpu : CPU) (rs : RegFile) (d : Efab) (vs : List (BitVec 8)) :
    vs.length = 4 →
    pstepProg (wtPf0 cpu rs) d (LIFetch wtBase (tagVals vs)) (wtP1 cpu rs (wordOfBytes 4 vs)) d := by
  intro hlen
  refine ⟨rfl, none, none, none, rfl, rfl, ?_, rfl⟩
  exact pnodeStepReadAny 4 64 wtFreq (fun ans => wtM2 (wtVal ans)) rs ibNone d.efDev vs wtPaRam
    hlen

/-- The fetch is an admin step: it consumes NO row item (the position stays `k`). -/
theorem wtFetch (cpu : CPU) (rs : RegFile) (w0 w1 : BitVec (8 * 4)) (k : Nat)
    (vs : List (BitVec 8)) :
    vs.length = 4 →
    AxOpsem.astepProg (wtRow w0 w1) ⟨wtPf0 cpu rs, k⟩
      (LIFetch wtBase (tagVals vs)) ⟨wtP1 cpu rs (wordOfBytes 4 vs), k⟩ := by
  intro hvs
  exact .AStepAdmin _ k wtD0 _ _ wtD0 rfl (wtFetchStep cpu rs wtD0 vs hvs)

/-! ### 6.5 The tree's conformance of the same program, and its opax run -/

def wtDv : Nat → Efab := fun _ => wtD0

def wtItems (w0 : BitVec (8 * 4)) : List Eitem :=
  [(LLoad false false wtBase (tagVals (WeakInterpProj.wbytes 4 w0)) [], some 0),
   (LStore false wtBase (WeakInterpProj.wbytes 4 w0) (depsAsrc (depsOfIb ibNone.ibBits))
      (depsVsrc (depsOfIb ibNone.ibBits)), some 1)]

theorem wtWs1Relp (w0 : BitVec (8 * 4)) :
    (lblPost 0 wsInit (.LLoad false wtBase [0, 0, 0, 0] (WeakInterpProj.wbytes 4 w0))).wRelp =
      false := by
  rw [lblPostRelp]; rfl

/-- The store's class under the tree's projection: plain. -/
theorem wtPclsStore (cpu : CPU) (rs : RegFile) (v : BitVec (8 * 4)) (asrc vsrc : List Dsrc)
    (ws : Wstate) :
    ws.wRelp = false →
    pclsEv (wtP1 cpu rs v) (LStore false wtBase (WeakInterpProj.wbytes 4 v) asrc vsrc) ws =
      .WCplain := by
  intro h
  show wmClassOf (classify wtAk) ws = .WCplain
  rw [wtAkPlain]
  simp [wmClassOf, h]

/-- The program writes what it read, so it conforms exactly to the rows with `w1 = w0`. -/
theorem wtHartConf (i : Nat) (cpu : CPU) (rs : RegFile) (w0 : BitVec (8 * 4)) :
    hartConf i (wtRow w0 w0) (wtP0 cpu rs) wtDv (.HEm (wtItems w0) (wtP2 cpu rs)) := by
  refine hemit.HEone 0 wsInit _ _ _ [] _ _ _ (wtP1 cpu rs w0) _ _ (.ARnil _ _) ?_ ?_ ?_
  · refine ⟨trivial, rfl, rfl, ?_⟩
    simp [projLbl, tagValsSnd, tagValsFst, wbytesLength, List.replicate]
  · have h := wtReadStep cpu rs wtD0 (WeakInterpProj.wbytes 4 w0) (wbytesLength _ _)
    rw [wordOfBytesWbytes] at h
    exact (pstepEvSplit _ _ _ _ _).2 (Or.inl h)
  · refine hemit.HEone 1 _ _ _ _ [] _ _ _ _ _ _ (.ARnil _ _) ?_ ?_ (.HEnil _ _ _)
    · refine ⟨trivial, trivial, trivial, ?_⟩
      rw [wtPclsStore cpu rs w0 _ _ _ (wtWs1Relp w0)]
      rfl
    · exact (pstepEvSplit _ _ _ _ _).2 (Or.inl (wtWriteStep cpu rs wtD0 w0))

/-- `hemitAstep` on it reproduces `wtRun`: two items, two steps. -/
theorem wtHemitAstep (i : Nat) (cpu : CPU) (rs : RegFile) (w0 : BitVec (8 * 4)) :
    nsteps (astepAny (wtRow w0 w0)) 2 ⟨wtP0 cpu rs, 0⟩ ⟨wtP2 cpu rs, 2⟩ :=
  hemitAstep _ i _ wtDv _ (wtHartConf i cpu rs w0)
    (by intro kd ba bs sa sv h; simp [emLabels, wtItems] at h)

end OpaxWit

end Weak
