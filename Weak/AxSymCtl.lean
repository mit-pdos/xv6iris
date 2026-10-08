/-
Weak: **the symbolic WPd engine X with ROW-POSITION COUNTING** — part 1 of 2 (§1–§3, the
GENERIC counting machinery; §4–§5 are the Lean-only split `Weak.AxSymCtlb`).

Rocq: `iris/AxSymCtl.v` @ xxvzwolszwmp.  Importers of the Rocq file (AxSymCtl2–5, AxSpinE*,
AxCert*, …) import `Weak.AxSymCtlb` (which imports this part).

## The Rocq header, in substance

§1 `EvB img QE Q m t b`: `EvA` with a READ BUDGET `b` (= row items left); a graph read of image
bytes consumes one unit (`ebMrd`); at budget 0 a graph read node is accepted with NO continuation
(`ebEnd`: the row ended, the hart is stuck there).  Kit `EvBMono/Bind/Bind0/ReadReg/WriteReg/
TryCatch/LiftRAny/CatchEarlyReturn/Fact`; `nrd` (read-free trees) with `EvBOfEvA` (read-free
`EvA` ⇒ `EvB`, budget unchanged) and the `nrd` combinators.
§2 `cntA`/`cntAR`: the graph reads on `execA`'s path; `cntABindSome` etc.; THE BRIDGE
`execAEvB` (an `execA` run with `cntA m s = c` is an `EvB` at every budget `b`, post
`b = b' + c`); the `nrd` automation and `nrd` of every instruction-independent spine piece
(`nrdShouldIncMinstret`, `nrdZca`, `nrdLpad`, `nrdDispatchInterrupt`, `nrdTickClock`).
§3 `wpdStuckReadM` (a graph read at the row end is stuck: WPd with no continuation),
`wpdOfEvBM` (row length `kend` under the graph fact `G`; continuation at every `.pure ()` with
budget `b'` left at position `kend - b'`), `wpdInstrOfEvBM` (from a boundary, both ticks); the
riscv.cat instances `wpdStuckRead`/`wpdOfEvB`/`wpdInstrOfEvB`.  Nothing in §1–§3 mentions the
fetch's shape.

## Deviations from Rocq

1. O2 STAGE C (fetch = pinned admin step; `AxSymEngine` deviation 1).  In Rocq every plain RAM
   read — the instruction fetch included — is a row item.  In Lean an `akIfetch` read is the
   pinned admin step at the SAME row position and only the other reads (data, page-table walk)
   are graph reads.  So: `EvB.ebMrd` is the GRAPH read (premise `akIfetch = false`, which is
   Rocq's `ak_coh = false` with Lean's renaming) and consumes one unit; the Lean-only
   constructor `EvB.ebIf` is an image FETCH (`akIfetch = true`) and KEEPS the budget; `ebEnd`
   takes `akIfetch = false` (a fetch at the row end is not stuck).  `cntA` counts graph reads
   only (a fetch read counts 0).  `wpdStuckReadM` takes `Hnf : akIfetch = false`.  `wpdOfEvBM`
   runs `ebMrd` through `AxSymEngine3.wpdImgRead3M` (to `k + 1`) and `ebIf` through
   `AxSymEngine3.wpdImgFetch3M` (at `k`).  Rocq's section premise `Hloc` is DROPPED (as
   `AxSymEngine3` deviation 1): premises are `G HG Hmid Htext Hflow kend HGl`.
2. THE PINS (`AxRunClose` deviation 1): `seip_reg` ↦ `AxRunClose.pinReg` in `EvB.ebRd`/`ebWr`,
   `cntA` and every `regsAgree`.
3. Q7: `EvB.ebIa` takes `sfAnnB n w = false`; `cntA` is 0 at an sfence announce (`execA` is
   stuck there).
4. LEAN-SAIL OUTCOMES / MONADS (as `AxSymEngine` deviation 4, `AxSpineOk` deviation 4): `EvB`,
   `nrd`, `cntA` are on `SailM X`; a failure node `.impure (.error e)` is `EvB.ebExt` (QE) /
   `nrd`-free (Rocq's `ExtraOutcome`, `_ => True`).  `cntAR m s := cntA (ExceptT.run m) s`
   (as `execAR`); `cntARRfF` takes `rfF (ExceptT.run m)`.  `EvBLiftRAny` /
   `EvBCatchEarlyReturn` state the `Except` match of `EvALiftR` / `EvACatchEarlyReturn`; an early
   return (`.error (.inr x)`) is a result value and keeps its budget, so `EvBCatchEarlyReturn`
   asks `Q b' x t'` there (Rocq: `∀ b', Q b' r t'`, its early return being a budget-free extra
   outcome) — a weaker premise.  `Defs.try_catch` ↦ `PreSail.tryCatchAll`; `liftR` ↦ `liftM`;
   `catch_early_return` ↦ `SailME.run`; `foreach_ZM_up'`/`foreach_ZM_up` ↦ the step-1 `IntRange`
   loops (as `AxSpineOk2` deviation 2).
5. TACTICS: Rocq `nrd_step`/`nrd_unf`/`nrd_cer`/`nrd_auto` ↦ `ax_sym_ctl_nrd_step` (the
   `AxSpineOk2.rff_step` dispatcher for `nrd`, plus head beta/zeta, and model `*_callback` stubs
   closed by `True.intro` — never unfold `csr_name_write_callback`) / `ax_sym_ctl_nrd_auto`;
   `nseip` ↦ `AxSymEngine2.notPin`; `silent_psB` ↦ `AxSymEngine3.wpdSilentNode3M`.  Rocq's
   `Definition wpd_stuck_read := wpd_stuck_readM rvwmo_cat_consistent` (and the other two) ↦
   theorems at `rvwmoCatConsistent` (with `wpd`).
6. TYPES (as `AxSymEngine` deviation 5): `Z → option (bv 8)` ↦ `Image`, `mstate` ↦ `ExecSt`,
   `register_lookup r rs` ↦ `rs r`, `set_reg` ↦ `ExecSt.setReg`, `read_bytes` ↦ `bmRead`,
   `inl (w, None)` ↦ `.Ok (w, none)`, `S b` ↦ `b + 1`, `Interface.Ret tt` ↦ `.pure ()`,
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`).
7. Q16 (owner ruling, 2026-10-07): THE IMAGELESS FETCH.  In Rocq a fetch was a graph read, so a
   run whose next fetch has no image bytes stopped at the row end (`eb_end`).  In Lean a fetch
   is the pinned admin step, and a pinned fetch with no image bytes has NO step: the Lean-only
   constructor `EvB.ebNf` ENDS the run there (cf. `AxSpinVA`'s `ENf`/`fcNf`, Q13), at any
   budget, premises `devAddr = false`, `akIfetch = true`, `imgBytes img (paZ pa) n = none` and
   the GATE `∀ e, QE e t` (a stuck end, accepted only where `QE` accepts every stuck end).  So
   every existing certificate at `QE := fun _ _ => False` excludes it, and `wpdOfEvBM` /
   `wpdInstrOfEvBM` / `wpdOfEvB` / `wpdInstrOfEvB` / `execAEvB` keep their statements (the new
   `wpdOfEvBM` arm is vacuous).  `EvBTryCatch` gains `HNf : ∀ t', (∀ e, QE1 e t') → ∀ e, QE2 e t'`
   (a stuck end is not caught by the handler; no Lean user).  THE STUCK BRIDGE is Lean-only:
   `AxSymCtl.wpdOfEvBStuckM` / `AxSymCtl.wpdInstrOfEvBStuckM` / `AxSymCtl.wpdInstrOfEvBStuck`
   take certificates at `QE := fun _ _ => True` (failure nodes and imageless fetches are stuck
   ends: `AxSymCtl.wpdStuckErrM`, `AxSymCtl.wpdStuckNfM`) plus `HGimg : ∀ GD, G GD → ∀ a,
   img a = none → GD.gdG.gxImg a = none` (the allowed graphs' boot images lack what `img` lacks
   — `textFixed` gives only `img ⊆ gxImg`; Q12's precedent `GD.gdG.gxImg = img`) and `Herr`
   (the post at a failure node at the row end: failure nodes are not `midState`s).  Stop
   certificates ending at an imageless fetch come from `AxSymCtl.EvBMeet0` (two certificates
   over two EXTENSIONS of `img` met over `img`; disagreeing posts force the hole).

**Rocq → Lean name map.**  `EvB` `EvB` (constructors `eb_ret` `ebRet`, `eb_rd` `ebRd`, `eb_wr`
`ebWr`, `eb_mrd` `ebMrd`, `eb_end` `ebEnd`, `eb_ia` `ebIa`, `eb_ba` `ebBa`, `eb_co` `ebCo`, `eb_tl`
`ebTl`, `eb_te` `ebTe`, `eb_rx` `ebRx`, `eb_ts` `ebTs`, `eb_tx` `ebTx`, `eb_cc` `ebCc`, `eb_msg`
`ebMsg`, `eb_gcc` `ebGcc`, `eb_ext` `ebExt`; Lean-only `ebIf`), `EvB_mono` `EvBMono`, `EvB_bind`
`EvBBind`, `EvB_bind0` `EvBBind0`, `EvB_read_reg` `EvBReadReg`, `EvB_write_reg` `EvBWriteReg`,
`EvB_try_catch` `EvBTryCatch`, `EvB_liftR_any` `EvBLiftRAny`, `EvB_catch_early_return`
`EvBCatchEarlyReturn`, `EvB_fact` `EvBFact`, `nrd` `nrd`, `EvB_of_EvA` `EvBOfEvA`, `nrd_bind`
`nrdBind`, `nrd_bind0` `nrdBind0`, `nrd_try_catch` `nrdTryCatch`, `nrd_liftR` `nrdLiftR`,
`nrd_catch_early_return` `nrdCatchEarlyReturn`, `nrd_of_rf0` `nrdOfRf0`, `nrd_of_rfF`
`nrdOfRfF`, `cntA` `cntA`, `cntAR` `cntAR`, `cntA_bind_Some` `cntABindSome`, `cntA_bind0_Some`
`cntABind0Some`, `cntAR_bind_Some` `cntARBindSome`, `cntAR_bind0_Some` `cntARBind0Some`,
`cntAR_liftR` `cntARLiftR`, `cntAR_liftR_seq` `cntARLiftRSeq`, `cntA_catch_early_return`
`cntACatchEarlyReturn`, `cntA_rfF` `cntARfF`, `cntAR_rfF` `cntARRfF`, `cntA_returnm`
`cntAReturnm`, `cntAR_returnR` `cntARReturnR`, `execA_EvB` `execAEvB`, `nrd_foreach_ZM_up'`
`nrdForeachZMUp'`, `nrd_foreach_ZM_up` `nrdForeachZMUp`, `nrd_should_inc_minstret`
`nrdShouldIncMinstret`, `nrd_zca` `nrdZca`, `nrd_lpad` `nrdLpad`, `nrd_dispatchInterrupt`
`nrdDispatchInterrupt`, `nrd_tick_clock` `nrdTickClock`, `wpd_stuck_read(M)` `wpdStuckRead(M)`,
`wpd_of_EvB(M)` `wpdOfEvB(M)`, `wpd_instr_of_EvB(M)` `wpdInstrOfEvB(M)`; tactics `nrd_step`/
`nrd_unf`/`nrd_cer` ↦ `ax_sym_ctl_nrd_step`, `nrd_auto` ↦ `ax_sym_ctl_nrd_auto`.  None is in the
duplicated-name table.  Lean-only (file-qualified `AxSymCtl.*`): `nrdSailTryCatch`, `nrdRBind`,
`cntABindZero`, `nrdRForInLoop`, `nrdRForIn`, `nrdIte`, `nrdRIte`, `nrdDite`, `nrdRDite`,
`nrdFreeBind`, `nrdLiftSelf`; Q16 (deviation 7): constructor `EvB.ebNf`, `mapMSub`, `mapMNone`,
`imgBytesSub`, `imgBytesSubNone`, `imgBytesNoneByte`, `EvBMeet0`, `errState`, `pstepErrInv`,
`wireKeeps`, `wpdStuckErrM`, `wpdStuckNfM`, `wpdOfEvBStuckM`, `wpdInstrOfEvBStuckM`,
`wpdInstrOfEvBStuck`.

**Dropped:** nothing (this part: Rocq 46 definitions/lemmas + 6 Ltacs; Lean 46 + 25 Lean-only +
2 tactics).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSymEngine3
import Weak.AxSpineOk2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
/-! # 1. `EvB`: the BUDGETED (row-position counting) certificate — generic -/

/-- THE BUDGETED CERTIFICATE (see the header; deviation 1: a fetch read `ebIf` keeps the
budget, a graph read `ebMrd` consumes one unit, the row end `ebEnd` is a graph read). -/
inductive EvB (img : Image) {X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : Nat → X → ExecSt → Prop) : SailM X → ExecSt → Nat → Prop where
  | ebRet (x : X) (t : ExecSt) (b : Nat) : Q b x t → EvB img QE Q (.pure x) t b
  | ebRd (r : Register) (k : RegisterType r → SailM X) (t : ExecSt) (b : Nat) :
      (AxRunClose.pinReg r → ∀ v, EvB img QE Q (k v) t b) →
      (¬ AxRunClose.pinReg r → EvB img QE Q (k (t.regs r)) t b) →
      EvB img QE Q (.impure (.ok (.regRead r)) k) t b
  | ebWr (r : Register) (v : RegisterType r) (k : PUnit → SailM X) (t : ExecSt) (b : Nat) :
      ¬ AxRunClose.pinReg r → EvB img QE Q (k PUnit.unit) (t.setReg r v) b →
      EvB img QE Q (.impure (.ok (.regWrite r v)) k) t b
  | ebMrd (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) (b : Nat)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      imgBytes img (paZ req.pa) n = some vs →
      EvB img QE Q (k (.Ok (wordOfBytes n vs, none))) t b →
      EvB img QE Q (.impure (.ok (.memRead n va req)) k) t (b + 1)
  | ebIf (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) (b : Nat)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = some vs →
      EvB img QE Q (k (.Ok (wordOfBytes n vs, none))) t b →
      EvB img QE Q (.impure (.ok (.memRead n va req)) k) t b
  | ebEnd (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false →
      EvB img QE Q (.impure (.ok (.memRead n va req)) k) t 0
  | ebIa (n : Nat) (w : BitVec n) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      sfAnnB n w = false → EvB img QE Q (k ()) t b →
      EvB img QE Q (.impure (.ok (.instrAnnounce n w)) k) t b
  | ebBa (n : Nat) (a : BitVec n) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.branchAnnounce n a)) k) t b
  | ebCo (c : Arch.cache_op) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.cacheOp c)) k) t b
  | ebTl (c : Arch.tlb_op) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.tlbi c)) k) t b
  | ebTe (f : Arch.fault) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.takeException f)) k) t b
  | ebRx (a : Arch.pa) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.returnException a)) k) t b
  | ebTs (a : Arch.trans_start) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.translationStart a)) k) t b
  | ebTx (a : Arch.trans_end) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.translationEnd a)) k) t b
  | ebCc (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok .cycleCount) k) t b
  | ebMsg (a : String) (k : Unit → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k ()) t b → EvB img QE Q (.impure (.ok (.message a)) k) t b
  | ebGcc (k : Nat → SailM X) (t : ExecSt) (b : Nat) :
      EvB img QE Q (k (0 : Nat)) t b → EvB img QE Q (.impure (.ok .getCycleCount) k) t b
  | ebExt (e : Sail.Error exception) (k : Empty → SailM X) (t : ExecSt) (b : Nat) :
      QE e t → EvB img QE Q (.impure (.error e) k) t b
  /-- (Lean-only, Q16) an i-FETCH WITH NO IMAGE BYTES: the run ends stuck there (no pinned fetch
  exists; deviation 7).  A stuck end, accepted only where `QE` accepts every stuck end. -/
  | ebNf (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt) (b : Nat) :
      devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = none → (∀ e, QE e t) →
      EvB img QE Q (.impure (.ok (.memRead n va req)) k) t b

section evb
variable (img : Image)

theorem EvBMono {X : Type} (QE QE' : Sail.Error exception → ExecSt → Prop)
    (Q Q' : Nat → X → ExecSt → Prop) (m : SailM X) (t : ExecSt) (b : Nat) :
    (∀ e t', QE e t' → QE' e t') → (∀ b' x t', Q b' x t' → Q' b' x t') →
    EvB img QE Q m t b → EvB img QE' Q' m t b := by
  intro HE HQ h
  induction h with
  | ebRet x t b h => exact .ebRet x t b (HQ b x t h)
  | ebExt e k t b h => exact .ebExt e k t b (HE e t h)
  | ebRd r k t b _ _ ihs ihn => exact .ebRd r k t b ihs ihn
  | ebWr r v k t b hr _ ih => exact .ebWr r v k t b hr ih
  | ebMrd n va req k t b vs h1 h2 h3 h4 _ ih => exact .ebMrd n va req k t b vs h1 h2 h3 h4 ih
  | ebIf n va req k t b vs h1 h2 h3 h4 _ ih => exact .ebIf n va req k t b vs h1 h2 h3 h4 ih
  | ebEnd n va req k t h1 h2 h3 => exact .ebEnd n va req k t h1 h2 h3
  | ebNf n va req k t b h1 h2 h3 hq => exact .ebNf n va req k t b h1 h2 h3 (fun e => HE e t (hq e))
  | ebIa n w k t b hs _ ih => exact .ebIa n w k t b hs ih
  | ebBa n a k t b _ ih => exact .ebBa n a k t b ih
  | ebCo c k t b _ ih => exact .ebCo c k t b ih
  | ebTl c k t b _ ih => exact .ebTl c k t b ih
  | ebTe f k t b _ ih => exact .ebTe f k t b ih
  | ebRx a k t b _ ih => exact .ebRx a k t b ih
  | ebTs a k t b _ ih => exact .ebTs a k t b ih
  | ebTx a k t b _ ih => exact .ebTx a k t b ih
  | ebCc k t b _ ih => exact .ebCc k t b ih
  | ebMsg a k t b _ ih => exact .ebMsg a k t b ih
  | ebGcc k t b _ ih => exact .ebGcc k t b ih

theorem EvBBind {X Y : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : Nat → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y) (t : ExecSt) (b : Nat) :
    EvB img QE (fun b' x t' => EvB img QE Q (f x) t' b') m t b → EvB img QE Q (m >>= f) t b := by
  intro h
  induction h with
  | ebRet x t b h => exact h
  | ebExt e k t b h => exact .ebExt e _ t b h
  | ebRd r k t b _ _ ihs ihn => exact .ebRd r _ t b ihs ihn
  | ebWr r v k t b hr _ ih => exact .ebWr r v _ t b hr ih
  | ebMrd n va req k t b vs h1 h2 h3 h4 _ ih => exact .ebMrd n va req _ t b vs h1 h2 h3 h4 ih
  | ebIf n va req k t b vs h1 h2 h3 h4 _ ih => exact .ebIf n va req _ t b vs h1 h2 h3 h4 ih
  | ebEnd n va req k t h1 h2 h3 => exact .ebEnd n va req _ t h1 h2 h3
  | ebNf n va req k t b h1 h2 h3 hq => exact .ebNf n va req _ t b h1 h2 h3 hq
  | ebIa n w k t b hs _ ih => exact .ebIa n w _ t b hs ih
  | ebBa n a k t b _ ih => exact .ebBa n a _ t b ih
  | ebCo c k t b _ ih => exact .ebCo c _ t b ih
  | ebTl c k t b _ ih => exact .ebTl c _ t b ih
  | ebTe f k t b _ ih => exact .ebTe f _ t b ih
  | ebRx a k t b _ ih => exact .ebRx a _ t b ih
  | ebTs a k t b _ ih => exact .ebTs a _ t b ih
  | ebTx a k t b _ ih => exact .ebTx a _ t b ih
  | ebCc k t b _ ih => exact .ebCc _ t b ih
  | ebMsg a k t b _ ih => exact .ebMsg a _ t b ih
  | ebGcc k t b _ ih => exact .ebGcc _ t b ih

theorem EvBBind0 {Y : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : Nat → Y → ExecSt → Prop) (m : SailM Unit) (n : SailM Y) (t : ExecSt) (b : Nat) :
    EvB img QE (fun b' _ t' => EvB img QE Q n t' b') m t b → EvB img QE Q (m >>= fun _ => n) t b :=
  EvBBind img QE Q m (fun _ => n) t b

theorem EvBReadReg (QE : Sail.Error exception → ExecSt → Prop) (r : Register)
    (Q : Nat → RegisterType r → ExecSt → Prop) (t : ExecSt) (b : Nat) :
    ¬ AxRunClose.pinReg r → Q b (t.regs r) t → EvB img QE Q (readReg r : SailM _) t b :=
  fun hr hq => .ebRd r _ t b (fun h => absurd h hr) (fun _ => .ebRet _ t b hq)

theorem EvBWriteReg (QE : Sail.Error exception → ExecSt → Prop) (Q : Nat → PUnit → ExecSt → Prop)
    (r : Register) (v : RegisterType r) (t : ExecSt) (b : Nat) :
    ¬ AxRunClose.pinReg r → Q b PUnit.unit (t.setReg r v) →
    EvB img QE Q (writeReg r v : SailM _) t b :=
  fun hr hq => .ebWr r v _ t b hr (.ebRet _ _ b hq)

theorem EvBTryCatch {X : Type} (QE1 QE2 : Sail.Error exception → ExecSt → Prop)
    (Q : Nat → X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X)
    (t : ExecSt) (b : Nat)
    (HNf : ∀ t', (∀ e, QE1 e t') → ∀ e, QE2 e t') :
    (∀ e t' b', QE1 e t' → EvB img QE2 Q (h e) t' b') →
    EvB img QE1 Q m t b → EvB img QE2 Q (PreSail.tryCatchAll m h) t b := by
  intro Hh H
  induction H with
  | ebRet x t b h => exact .ebRet x t b h
  | ebExt e k t b he => exact Hh e t b he
  | ebRd r k t b _ _ ihs ihn => exact .ebRd r _ t b ihs ihn
  | ebWr r v k t b hr _ ih => exact .ebWr r v _ t b hr ih
  | ebMrd n va req k t b vs h1 h2 h3 h4 _ ih => exact .ebMrd n va req _ t b vs h1 h2 h3 h4 ih
  | ebIf n va req k t b vs h1 h2 h3 h4 _ ih => exact .ebIf n va req _ t b vs h1 h2 h3 h4 ih
  | ebEnd n va req k t h1 h2 h3 => exact .ebEnd n va req _ t h1 h2 h3
  | ebNf n va req k t b h1 h2 h3 hq => exact .ebNf n va req _ t b h1 h2 h3 (HNf t hq)
  | ebIa n w k t b hs _ ih => exact .ebIa n w _ t b hs ih
  | ebBa n a k t b _ ih => exact .ebBa n a _ t b ih
  | ebCo c k t b _ ih => exact .ebCo c _ t b ih
  | ebTl c k t b _ ih => exact .ebTl c _ t b ih
  | ebTe f k t b _ ih => exact .ebTe f _ t b ih
  | ebRx a k t b _ ih => exact .ebRx a _ t b ih
  | ebTs a k t b _ ih => exact .ebTs a _ t b ih
  | ebTx a k t b _ ih => exact .ebTx a _ t b ih
  | ebCc k t b _ ih => exact .ebCc _ t b ih
  | ebMsg a k t b _ ih => exact .ebMsg a _ t b ih
  | ebGcc k t b _ ih => exact .ebGcc _ t b ih

theorem EvBLiftRAny {R X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : Nat → X → ExecSt → Prop) (m : SailM X) (t : ExecSt) (b : Nat) :
    EvB img (fun _ _ => False) Q m t b →
    EvB img QE
      (fun b' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q b' x t'
        | .error _ => False)
      (ExceptT.run (liftM m : SailME R X)) t b := by
  intro H
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  apply EvBBind
  exact EvBMono img _ QE Q _ m t b (fun _ _ h => h.elim) (fun b' x t' h => .ebRet _ t' b' h) H

theorem EvBCatchEarlyReturn {X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : Nat → X → ExecSt → Prop) (m : SailME X X) (t : ExecSt) (b : Nat) :
    EvB img QE
      (fun b' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q b' x t'
        | .error (.inr x) => Q b' x t'
        | .error (.inl e) => QE e t')
      (ExceptT.run m) t b →
    EvB img QE Q (SailME.run m) t b := by
  intro H
  show EvB img QE Q (ExceptT.run m >>= _) t b
  apply EvBBind
  refine EvBMono img QE QE _ _ _ t b (fun _ _ h => h) ?_ H
  intro b' r t' hr
  rcases r with (e | x) | x
  · exact .ebExt e _ t' b' hr
  · exact .ebRet x t' b' hr
  · exact .ebRet x t' b' hr

theorem EvBFact {X Y : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (P : Nat → X → ExecSt → Prop) (Q : Nat → Y → ExecSt → Prop) (m : SailM X)
    (f : X → SailM Y) (t : ExecSt) (b : Nat) :
    EvB img QE P m t b → (∀ b' x t', P b' x t' → EvB img QE Q (f x) t' b') →
    EvB img QE Q (m >>= f) t b := by
  intro Hm Hf
  exact EvBBind img QE Q m f t b (EvBMono img _ _ _ _ m t b (fun _ _ h => h) Hf Hm)

end evb

/-! ### (Lean-only, Q16) image extension and the imageless fetch -/

/-- (Lean-only) `mapM` in `Option` along a pointwise extension. -/
theorem AxSymCtl.mapMSub {α β : Type} (f g : α → Option β) (hfg : ∀ x b, f x = some b → g x = some b) :
    ∀ (l : List α) (vs : List β), l.mapM f = some vs → l.mapM g = some vs
  | [], vs, h => by simpa using h
  | a :: l, vs, h => by
    cases ha : f a with
    | none => simp [List.mapM_cons, ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [List.mapM_cons, ha, hl] at h
      | some bs =>
        simp only [List.mapM_cons, ha, hl, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        simp only [List.mapM_cons, hfg a b ha, AxSymCtl.mapMSub f g hfg l bs hl,
          Option.bind_eq_bind, Option.bind_some, Option.pure_def, h]

/-- (Lean-only) A failed `mapM` in `Option` has a failing entry. -/
theorem AxSymCtl.mapMNone {α β : Type} (f : α → Option β) :
    ∀ (l : List α), l.mapM f = none → ∃ x ∈ l, f x = none
  | [], h => by simp at h
  | a :: l, h => by
    cases ha : f a with
    | none => exact ⟨a, List.mem_cons_self, ha⟩
    | some b =>
      cases hl : l.mapM f with
      | none =>
        obtain ⟨x, hx, hfx⟩ := AxSymCtl.mapMNone f l hl
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩
      | some bs => simp [List.mapM_cons, ha, hl] at h

/-- (Lean-only) Image bytes survive an extension of the image. -/
theorem AxSymCtl.imgBytesSub (img img' : Image) (H : ∀ a v, img a = some v → img' a = some v)
    (base : Int) (n : Nat) (vs : List (BitVec 8)) :
    imgBytes img base n = some vs → imgBytes img' base n = some vs :=
  AxSymCtl.mapMSub _ _ (fun j b h => H _ b h) _ vs

/-- (Lean-only) Missing image bytes stay missing in a sub-image. -/
theorem AxSymCtl.imgBytesSubNone (img img' : Image) (H : ∀ a v, img a = some v → img' a = some v)
    (base : Int) (n : Nat) :
    imgBytes img' base n = none → imgBytes img base n = none := by
  intro h
  cases h0 : imgBytes img base n with
  | none => rfl
  | some vs => rw [AxSymCtl.imgBytesSub img img' H base n vs h0] at h; cases h

/-- (Lean-only) Missing image bytes: one missing byte. -/
theorem AxSymCtl.imgBytesNoneByte (img : Image) (base : Int) (n : Nat) :
    imgBytes img base n = none → ∃ j : Nat, j < n ∧ img (base + (j : Int)) = none := by
  intro h
  obtain ⟨j, hj, hn⟩ := AxSymCtl.mapMNone _ _ h
  exact ⟨j, List.mem_range.mp hj, hn⟩

/-- (Lean-only, Q16) THE MEET at budget 0: two certificates over two EXTENSIONS of `img` give one
over `img`, with both posts.  Where the extensions supply bytes `img` lacks (a hole), the run of
`img` ends stuck at the fetch (`ebNf`).  (At budget 0 a graph read is the row end, `ebEnd`, so
no graph read needs bytes.)  With posts that disagree at every return, the meet is a stop
certificate: the hole is always reached. -/
theorem AxSymCtl.EvBMeet0 (img img1 img2 : Image) {X : Type}
    (QE : Sail.Error exception → ExecSt → Prop)
    (H1 : ∀ a v, img a = some v → img1 a = some v) (H2 : ∀ a v, img a = some v → img2 a = some v)
    (HQE : ∀ e t, QE e t) (P1 P2 : Nat → X → ExecSt → Prop) (m : SailM X) (t : ExecSt) :
    ∀ b, EvB img1 QE P1 m t b → b = 0 → EvB img2 QE P2 m t b →
      EvB img QE (fun b' x t' => P1 b' x t' ∧ P2 b' x t') m t b := by
  intro b d1
  induction d1 with
  | ebRet x t b h =>
    intro _ d2
    cases d2 with
    | ebRet _ _ _ h2 => exact .ebRet x t b ⟨h, h2⟩
  | ebExt e k t b h =>
    intro _ _
    exact .ebExt e k t b h
  | ebRd r k t b _ _ ihs ihn =>
    intro hb d2
    cases d2 with
    | ebRd _ _ _ _ hs2 hn2 =>
      exact .ebRd r k t b (fun hp v => ihs hp v hb (hs2 hp v)) (fun hp => ihn hp hb (hn2 hp))
  | ebWr r v k t b hr _ ih =>
    intro hb d2
    cases d2 with
    | ebWr _ _ _ _ _ _ d2' => exact .ebWr r v k t b hr (ih hb d2')
  | ebMrd n va req k t b vs h1 h2 h3 h4 _ _ =>
    intro hb _
    exact absurd hb (Nat.succ_ne_zero b)
  | ebIf n va req k t b vs h1 h2 h3 h4 _ ih =>
    intro hb d2
    cases hi : imgBytes img (paZ req.pa) n with
    | none => exact .ebNf n va req k t b h1 h3 hi (fun e => HQE e t)
    | some vs0 =>
      have e1 : vs = vs0 := by
        rw [AxSymCtl.imgBytesSub img img1 H1 _ _ vs0 hi] at h4
        exact (Option.some.inj h4).symm
      subst e1
      cases d2 with
      | ebMrd _ _ _ _ _ b' _ _ _ _ _ _ => exact absurd hb (Nat.succ_ne_zero b')
      | ebIf _ _ _ _ _ _ vs2 _ _ _ h4' d2' =>
        have e2 : vs2 = vs := by
          rw [AxSymCtl.imgBytesSub img img2 H2 _ _ vs hi] at h4'
          exact (Option.some.inj h4').symm
        subst e2
        exact .ebIf n va req k t b vs2 h1 h2 h3 hi (ih hb d2')
      | ebEnd _ _ _ _ _ _ _ h3' => rw [h3] at h3'; cases h3'
      | ebNf _ _ _ _ _ _ _ _ hn2 _ =>
        rw [AxSymCtl.imgBytesSub img img2 H2 _ _ vs hi] at hn2
        cases hn2
  | ebEnd n va req k t h1 h2 h3 =>
    intro _ _
    exact .ebEnd n va req k t h1 h2 h3
  | ebNf n va req k t b h1 h2 h3 hq =>
    intro _ _
    exact .ebNf n va req k t b h1 h2 (AxSymCtl.imgBytesSubNone img img1 H1 _ _ h3) hq
  | ebIa n w k t b hs _ ih =>
    intro hb d2
    cases d2 with
    | ebIa _ _ _ _ _ _ d2' => exact .ebIa n w k t b hs (ih hb d2')
  | ebBa n a k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebBa _ _ _ _ _ d2' => exact .ebBa n a k t b (ih hb d2')
  | ebCo c k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebCo _ _ _ _ d2' => exact .ebCo c k t b (ih hb d2')
  | ebTl c k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebTl _ _ _ _ d2' => exact .ebTl c k t b (ih hb d2')
  | ebTe f k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebTe _ _ _ _ d2' => exact .ebTe f k t b (ih hb d2')
  | ebRx a k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebRx _ _ _ _ d2' => exact .ebRx a k t b (ih hb d2')
  | ebTs a k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebTs _ _ _ _ d2' => exact .ebTs a k t b (ih hb d2')
  | ebTx a k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebTx _ _ _ _ d2' => exact .ebTx a k t b (ih hb d2')
  | ebCc k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebCc _ _ _ d2' => exact .ebCc k t b (ih hb d2')
  | ebMsg a k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebMsg _ _ _ _ d2' => exact .ebMsg a k t b (ih hb d2')
  | ebGcc k t b _ ih =>
    intro hb d2
    cases d2 with
    | ebGcc _ _ _ d2' => exact .ebGcc k t b (ih hb d2')

/-! ### Read-free trees (`nrd`) -/

/-- No RAM read node on any branch. -/
def nrd {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .regRead _, k => ∀ v, nrd (k v)
    | .regWrite _ _, k => nrd (k PUnit.unit)
    | .memRead .., _ => False
    | .instrAnnounce _ _, k => nrd (k ())
    | .branchAnnounce _ _, k => nrd (k ())
    | .cacheOp _, k => nrd (k ())
    | .tlbi _, k => nrd (k ())
    | .takeException _, k => nrd (k ())
    | .returnException _, k => nrd (k ())
    | .translationStart _, k => nrd (k ())
    | .translationEnd _, k => nrd (k ())
    | .cycleCount, k => nrd (k ())
    | .message _, k => nrd (k ())
    | .getCycleCount, k => nrd (k (0 : Nat))
    | _, _ => True

theorem EvBOfEvA (img : Image) {X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : X → ExecSt → Prop) (m : SailM X) (t : ExecSt) :
    EvA img QE Q m t → nrd m → ∀ b, EvB img QE (fun b' x t' => b' = b ∧ Q x t') m t b := by
  intro H
  induction H with
  | evRet x t h => intro _ b; exact .ebRet x t b ⟨rfl, h⟩
  | evExt e k t h => intro _ b; exact .ebExt e k t b h
  | evRd r k t _ _ ihs ihn =>
    intro hn b
    exact .ebRd r k t b (fun hp v => ihs hp v (hn v) b) (fun hp => ihn hp (hn _) b)
  | evWr r v k t hr _ ih => intro hn b; exact .ebWr r v k t b hr (ih hn b)
  | evMrd n va req k t vs _ _ _ _ _ => intro hn; exact False.elim hn
  | evIa n w k t hs _ ih => intro hn b; exact .ebIa n w k t b hs (ih hn b)
  | evBa n a k t _ ih => intro hn b; exact .ebBa n a k t b (ih hn b)
  | evCo c k t _ ih => intro hn b; exact .ebCo c k t b (ih hn b)
  | evTl c k t _ ih => intro hn b; exact .ebTl c k t b (ih hn b)
  | evTe f k t _ ih => intro hn b; exact .ebTe f k t b (ih hn b)
  | evRx a k t _ ih => intro hn b; exact .ebRx a k t b (ih hn b)
  | evTs a k t _ ih => intro hn b; exact .ebTs a k t b (ih hn b)
  | evTx a k t _ ih => intro hn b; exact .ebTx a k t b (ih hn b)
  | evCc k t _ ih => intro hn b; exact .ebCc k t b (ih hn b)
  | evMsg a k t _ ih => intro hn b; exact .ebMsg a k t b (ih hn b)
  | evGcc k t _ ih => intro hn b; exact .ebGcc k t b (ih hn b)

theorem nrdBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    nrd m → (∀ x, nrd (f x)) → nrd (m >>= f) := by
  induction m with
  | pure y => intro _ hf; exact hf y
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show nrd (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case regRead r => exact fun v => ih v (hm v) hf
      all_goals first | exact hm | trivial | exact ih _ hm hf

theorem nrdBind0 {Y : Type} (m : SailM Unit) (n : SailM Y) :
    nrd m → nrd n → nrd (m >>= fun _ => n) :=
  fun hm hn => nrdBind m (fun _ => n) hm (fun _ => hn)

theorem nrdTryCatch {X : Type} (m : SailM X) (h : Sail.Error exception → SailM X) :
    nrd m → (∀ e, nrd (h e)) → nrd (PreSail.tryCatchAll m h) := by
  induction m with
  | pure y => intro _ _; trivial
  | impure call k ih =>
    intro hm hh
    cases call with
    | error e => exact hh e
    | ok o =>
      show nrd (FreeM.impure (.ok o) (fun r => PreSail.tryCatchAll (k r) h))
      cases o
      case regRead r => exact fun v => ih v (hm v) hh
      all_goals first | exact hm | trivial | exact ih _ hm hh

/-- (Lean-only) The model's own `try … catch`. -/
theorem AxSymCtl.nrdSailTryCatch {X : Type} (m : SailM X) (h : exception → SailM X) :
    nrd m → (∀ e, nrd (h e)) → nrd (PreSail.sailTryCatch m h) := by
  induction m with
  | pure y => intro _ _; trivial
  | impure call k ih =>
    intro hm hh
    cases call with
    | error e =>
      cases e
      case User u => exact hh u
      all_goals trivial
    | ok o =>
      show nrd (FreeM.impure (.ok o) (fun r => PreSail.sailTryCatch (k r) h))
      cases o
      case regRead r => exact fun v => ih v (hm v) hh
      all_goals first | exact hm | trivial | exact ih _ hm hh

/-- (Lean-only) Bind in the early-return monad. -/
theorem AxSymCtl.nrdRBind {R X Y : Type} (m : SailME R X) (f : X → SailME R Y) :
    nrd (ExceptT.run m) → (∀ x, nrd (ExceptT.run (f x))) → nrd (ExceptT.run (m >>= f)) := by
  intro hm hf
  rw [ExceptT.run_bind]
  refine nrdBind _ _ hm (fun e => ?_)
  cases e with
  | ok x => exact hf x
  | error e => trivial

theorem nrdLiftR {R X : Type} (m : SailM X) : nrd m → nrd (ExceptT.run (liftM m : SailME R X)) := by
  intro h
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  exact nrdBind _ _ h (fun _ => trivial)

theorem nrdCatchEarlyReturn {X : Type} (m : SailME X X) :
    nrd (ExceptT.run m) → nrd (SailME.run m) := by
  intro hm
  show nrd (ExceptT.run m >>= _)
  refine nrdBind _ _ hm (fun e => ?_)
  rcases e with (e | r) | x <;> trivial

theorem nrdOfRf0 {X : Type} (m : SailM X) : rf0 m → nrd m := by
  induction m with
  | pure y => intro _; trivial
  | impure call k ih =>
    intro h
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v => ih v (h.2 v)
      case regWrite r v => exact ih _ h.2
      case instrAnnounce n w => exact ih _ h.2
      all_goals first | exact False.elim h | trivial | exact ih _ h

theorem nrdOfRfF {X : Type} (m : SailM X) : rfF m → nrd m := by
  induction m with
  | pure y => intro _; trivial
  | impure call k ih =>
    intro h
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v => ih v (h.2 v)
      case regWrite r v => exact ih _ h.2
      case instrAnnounce n w => exact ih _ h.2
      all_goals first | exact False.elim h | trivial | exact ih _ h

/-! # 2. The COUNTING twin of `execA` and THE BRIDGE `execAEvB` -/

/-- The graph reads on `execA`'s path (deviation 1: a fetch read counts 0). -/
def cntA {X : Type} : SailM X → ExecSt → Nat
  | .pure _, _ => 0
  | .impure (.error _) _, _ => 0
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => if AxRunClose.pinReg r then 0 else cntA (k (s.regs r)) s
    | .regWrite r v, k =>
      if AxRunClose.pinReg r then 0 else cntA (k PUnit.unit) (s.setReg r v)
    | .memRead n _ req, k =>
      if ramOk req.pa req.access_kind n then
        match bmRead s.mem req.pa n with
        | some w =>
          if (classify req.access_kind).akIfetch then cntA (k (.Ok (w, none))) s
          else cntA (k (.Ok (w, none))) s + 1
        | none => 0
      else 0
    | .memWrite .., _ => 0
    | .barrier _, _ => 0
    | .cacheOp _, k => cntA (k ()) s
    | .tlbi _, k => cntA (k ()) s
    | .translationStart _, k => cntA (k ()) s
    | .translationEnd _, k => cntA (k ()) s
    | .takeException _, k => cntA (k ()) s
    | .returnException _, k => cntA (k ()) s
    | .cycleCount, k => cntA (k ()) s
    | .getCycleCount, k => cntA (k (0 : Nat)) s
    | .message _, k => cntA (k ()) s
    | .instrAnnounce n w, k => if sfAnnB n w then 0 else cntA (k ()) s
    | .branchAnnounce _ _, k => cntA (k ()) s
    | .choose _, _ => 0
    | .readRam .., _ => 0
    | .writeRam .., _ => 0

/-- Rocq `cntAR` (as `execAR`, `AxSpineOk` deviation 4): the count of the `ExceptT` run. -/
def cntAR {R X : Type} (m : SailME R X) (s : ExecSt) : Nat := cntA (ExceptT.run m) s

theorem cntABindSome {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    ∀ s v st, execA m s = some (v, st) → cntA (m >>= f) s = cntA m s + cntA (f v) st := by
  induction m with
  | pure x =>
    intro s v st h
    simp only [execA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    show cntA (f x) s = 0 + cntA (f x) s
    rw [Nat.zero_add]
  | impure call k ih =>
    intro s v st h
    cases call with
    | error e => cases h
    | ok o =>
      show cntA (FreeM.impure (.ok o) (fun v => k v >>= f)) s = _
      cases o
      case regRead r =>
        by_cases hr : AxRunClose.pinReg r
        · exact absurd h (by simp [execA, hr])
        · simp only [execA, hr, ↓reduceIte] at h
          simp only [cntA, hr, ↓reduceIte]
          exact ih _ _ _ _ h
      case regWrite r v' =>
        by_cases hr : AxRunClose.pinReg r
        · exact absurd h (by simp [execA, hr])
        · simp only [execA, hr, ↓reduceIte] at h
          simp only [cntA, hr, ↓reduceIte]
          exact ih _ _ _ _ h
      case memRead n va req =>
        cases hm : ramOk req.pa req.access_kind n
        · exact absurd h (by simp [execA, hm])
        · cases hb : bmRead s.mem req.pa n with
          | none => exact absurd h (by simp [execA, hm, hb])
          | some w =>
            simp only [execA, hm, hb, ↓reduceIte] at h
            cases hf : (classify req.access_kind).akIfetch
            · simp only [cntA, hm, hb, hf, ↓reduceIte, Bool.false_eq_true]
              rw [ih _ _ _ _ h]
              omega
            · simp only [cntA, hm, hb, hf, ↓reduceIte]
              exact ih _ _ _ _ h
      case instrAnnounce n w =>
        cases hs : sfAnnB n w
        · simp only [execA, hs, Bool.false_eq_true, ↓reduceIte] at h
          simp only [cntA, hs, Bool.false_eq_true, ↓reduceIte]
          exact ih _ _ _ _ h
        · exact absurd h (by simp [execA, hs])
      all_goals first | cases h | exact ih _ _ _ _ h

theorem cntABind0Some {Y : Type} (m : SailM Unit) (n : SailM Y) (s : ExecSt) (u : Unit)
    (st : ExecSt) (h : execA m s = some (u, st)) :
    cntA (m >>= fun _ => n) s = cntA m s + cntA n st :=
  cntABindSome m (fun _ => n) s u st h

/-- (Lean-only) A continuation that never reads leaves the count of the head. -/
theorem AxSymCtl.cntABindZero {X Y : Type} (m : SailM X) (f : X → SailM Y)
    (hf : ∀ x s, cntA (f x) s = 0) : ∀ s, cntA (m >>= f) s = cntA m s := by
  induction m with
  | pure x => intro s; exact hf x s
  | impure call k ih =>
    intro s
    cases call with
    | error e => rfl
    | ok o =>
      show cntA (FreeM.impure (.ok o) (fun v => k v >>= f)) s = _
      cases o
      case regRead r =>
        by_cases hr : AxRunClose.pinReg r
        · simp only [cntA, hr, ↓reduceIte]
        · simp only [cntA, hr, ↓reduceIte]; exact ih _ _
      case regWrite r v' =>
        by_cases hr : AxRunClose.pinReg r
        · simp only [cntA, hr, ↓reduceIte]
        · simp only [cntA, hr, ↓reduceIte]; exact ih _ _
      case memRead n va req =>
        cases hm : ramOk req.pa req.access_kind n
        · simp only [cntA, hm, Bool.false_eq_true, ↓reduceIte]
        · cases hb : bmRead s.mem req.pa n with
          | none => simp only [cntA, hm, hb, ↓reduceIte]
          | some w =>
            cases hfe : (classify req.access_kind).akIfetch
            · simp only [cntA, hm, hb, hfe, ↓reduceIte, Bool.false_eq_true]
              rw [ih]
            · simp only [cntA, hm, hb, hfe, ↓reduceIte]
              exact ih _ _
      case instrAnnounce n w =>
        cases hs : sfAnnB n w
        · simp only [cntA, hs, Bool.false_eq_true, ↓reduceIte]; exact ih _ _
        · simp only [cntA, hs, ↓reduceIte]
      all_goals first | rfl | exact ih _ _

theorem cntARBindSome {R X Y : Type} (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y)
    (s' : ExecSt) (h : execAR m s = some (.inr a, s')) :
    cntAR (m >>= f) s = cntAR m s + cntAR (f a) s' := by
  unfold cntAR
  rw [ExceptT.run_bind]
  have h' : execA (ExceptT.run m) s = some (.ok a, s') := by
    unfold execAR at h
    rcases he : execA (ExceptT.run m) s with _ | ⟨e | x, s1⟩
    · rw [he] at h; cases h
    · rcases e with e | r
      · rw [he] at h; cases h
      · rw [he] at h; cases h
    · rw [he] at h
      cases h
      rfl
  rw [cntABindSome _ _ _ _ _ h']

theorem cntARBind0Some {R X : Type} (m : SailME R Unit) (n : SailME R X) (s s' : ExecSt)
    (h : execAR m s = some (.inr (), s')) :
    cntAR (m >>= fun _ => n) s = cntAR m s + cntAR n s' :=
  cntARBindSome m (fun _ => n) s () s' h

theorem cntARLiftR {R X : Type} (m : SailM X) :
    ∀ s, cntAR (liftM m : SailME R X) s = cntA m s := by
  intro s
  unfold cntAR
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  exact AxSymCtl.cntABindZero m _ (fun _ _ => rfl) s

theorem cntARLiftRSeq {R X Y : Type} (m : SailM Y) (f : Y → SailME R X) (s s' : ExecSt) (x : Y)
    (h : execA m s = some (x, s')) :
    cntAR (liftM m >>= f) s = cntA m s + cntAR (f x) s' := by
  rw [cntARBindSome _ _ _ x s' (by rw [execARLiftR, h]), cntARLiftR]

theorem cntACatchEarlyReturn {X : Type} (body : SailME X X) :
    ∀ s, cntA (SailME.run body) s = cntAR body s := by
  intro s
  show cntA (ExceptT.run body >>= _) s = cntA (ExceptT.run body) s
  refine AxSymCtl.cntABindZero _ _ ?_ s
  intro r s1
  rcases r with (e | x) | x <;> rfl

theorem cntARfF {X : Type} (m : SailM X) : rfF m → ∀ s, cntA m s = 0 := by
  induction m with
  | pure y => intro _ s; rfl
  | impure call k ih =>
    intro hrf s
    cases call with
    | error e => rfl
    | ok o =>
      cases o
      case regRead r =>
        simp only [cntA, hrf.1, ↓reduceIte]
        exact ih _ (hrf.2 _) _
      case regWrite r v =>
        simp only [cntA, hrf.1, ↓reduceIte]
        exact ih _ hrf.2 _
      case instrAnnounce n w =>
        simp only [cntA, hrf.1, Bool.false_eq_true, ↓reduceIte]
        exact ih _ hrf.2 _
      all_goals first | rfl | exact False.elim hrf | exact ih _ hrf _

theorem cntARRfF {R X : Type} (m : SailME R X) : rfF (ExceptT.run m) → ∀ s, cntAR m s = 0 :=
  fun h s => cntARfF _ h s

theorem cntAReturnm {X : Type} (x : X) (s : ExecSt) : cntA (pure x : SailM X) s = 0 := rfl
theorem cntARReturnR {R X : Type} (x : X) (s : ExecSt) : cntAR (pure x : SailME R X) s = 0 := rfl

/-- THE BRIDGE: `execA` + count ⇒ `EvB` at every budget. -/
theorem execAEvB {X : Type} (m : SailM X) :
    ∀ s x s', execA m s = some (x, s') →
    ∀ t : ExecSt, t.regs = s.regs → ∀ b,
    EvB (imgOf s) (fun (_ : Sail.Error exception) _ => False)
      (fun b' x' t' => b = b' + cntA m s ∧ x' = x ∧ t'.regs = s'.regs ∧ t'.mem = t.mem ∧
        t'.dev = t.dev) m t b := by
  induction m with
  | pure y =>
    intro s x s' h t ht b
    simp only [execA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .ebRet _ _ _ ⟨(Nat.add_zero b).symm, rfl, ht, rfl, rfl⟩
  | impure call k ih =>
    intro s x s' h t ht b
    cases call with
    | error e => cases h
    | ok o =>
      cases o
      case regRead r =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          have e : cntA (FreeM.impure (.ok (.regRead r)) k) s = cntA (k (s.regs r)) s := by
            simp only [cntA, hr, ↓reduceIte]
          rw [e]
          refine .ebRd r k t b (fun hp => absurd hp hr) (fun _ => ?_)
          rw [ht]
          exact ih _ s x s' h t ht b
      case regWrite r v =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hr
          have e : cntA (FreeM.impure (.ok (.regWrite r v)) k) s =
              cntA (k PUnit.unit) (s.setReg r v) := by
            simp only [cntA, hr, ↓reduceIte]
          rw [e]
          refine .ebWr r v k t b hr ?_
          have HI := ih PUnit.unit (s.setReg r v) x s' h (t.setReg r v) (by simp [ht]) b
          exact EvBMono (imgOf s) _ _ _ _ _ _ b (fun _ _ h => h)
            (fun b' x' t' ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, h3, h4⟩) HI
      case memRead n va req =>
        simp only [execA] at h
        split at h
        · rename_i hok
          obtain ⟨hd, hl, hwf⟩ := AxSpineOk.ramOkSpec _ _ _ hok
          split at h
          · rename_i w hrb
            obtain ⟨vs, hvs, hw⟩ := readBytesImg s req.pa n w hwf hrb
            have HI := ih (.Ok (w, none)) s x s' h t ht
            cases hfe : (classify req.access_kind).akIfetch
            · have e : cntA (FreeM.impure (.ok (.memRead n va req)) k) s =
                  cntA (k (.Ok (w, none))) s + 1 := by
                simp only [cntA, hok, hrb, hfe, ↓reduceIte, Bool.false_eq_true]
              rw [e]
              cases b with
              | zero => exact .ebEnd n va req k t hd hl hfe
              | succ b0 =>
                refine .ebMrd n va req k t b0 vs hd hl hfe hvs ?_
                rw [hw]
                exact EvBMono _ _ _ _ _ _ t b0 (fun _ _ h => h)
                  (fun b' x' t' ⟨h1, h2⟩ => ⟨by omega, h2⟩) (HI b0)
            · have e : cntA (FreeM.impure (.ok (.memRead n va req)) k) s =
                  cntA (k (.Ok (w, none))) s := by
                simp only [cntA, hok, hrb, hfe, ↓reduceIte]
              rw [e]
              refine .ebIf n va req k t b vs hd hl hfe hvs ?_
              rw [hw]
              exact HI b
          · cases h
        · cases h
      case instrAnnounce n w =>
        simp only [execA] at h
        split at h
        · cases h
        · rename_i hs
          have hs' : sfAnnB n w = false := by simpa using hs
          have e : cntA (FreeM.impure (.ok (.instrAnnounce n w)) k) s = cntA (k ()) s := by
            simp only [cntA, hs', Bool.false_eq_true, ↓reduceIte]
          rw [e]
          exact .ebIa n w k t b hs' (ih _ s x s' h t ht b)
      case barrier => cases h
      case memWrite => cases h
      case choose => cases h
      case readRam => cases h
      case writeRam => cases h
      case branchAnnounce => exact .ebBa _ _ k t b (ih _ s x s' h t ht b)
      case cacheOp => exact .ebCo _ k t b (ih _ s x s' h t ht b)
      case tlbi => exact .ebTl _ k t b (ih _ s x s' h t ht b)
      case takeException => exact .ebTe _ k t b (ih _ s x s' h t ht b)
      case returnException => exact .ebRx _ k t b (ih _ s x s' h t ht b)
      case translationStart => exact .ebTs _ k t b (ih _ s x s' h t ht b)
      case translationEnd => exact .ebTx _ k t b (ih _ s x s' h t ht b)
      case cycleCount => exact .ebCc k t b (ih _ s x s' h t ht b)
      case message => exact .ebMsg _ k t b (ih _ s x s' h t ht b)
      case getCycleCount => exact .ebGcc k t b (ih _ s x s' h t ht b)


/-! ### `nrd` automation (the `AxSpineOk2.rff_auto` recipe; pin reads ALLOWED) -/

/-- Rocq `nrd_foreach_ZM_up'` (as `rfFForeachZMUp'`): the step-1 `IntRange` loop. -/
theorem nrdForeachZMUp' {β : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → β → SailM (ForInStep β)) (hf : ∀ i b, nrd (f i b)) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      nrd (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      (range.stop - i + 1).toNat = n →
      nrd (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs) from
    fun i hs b => H _ i hs b rfl
  intro n
  induction n with
  | zero =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    trivial
  | succ n ih =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      refine nrdBind _ _ (hf i b) (fun r => ?_)
      cases r with
      | done b' => trivial
      | yield b' =>
        have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
          simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
          rw [hstep]
          omega
        exact ih _ _ b' hn'
    · simp only [dif_neg h]
      trivial

theorem nrdForeachZMUp {β : Type} (range : IntRange) (hstep : range.step = 1) (b : β)
    (f : Int → β → SailM (ForInStep β)) (hf : ∀ i b, nrd (f i b)) : nrd (forIn range b f) :=
  nrdForeachZMUp' range hstep f hf range.start (by simp) b

/-- (Lean-only) The loop in the early-return monad. -/
theorem AxSymCtl.nrdRForInLoop {R β : Type} (range : IntRange) (hstep : range.step = 1)
    (f : Int → β → SailME R (ForInStep β)) (hf : ∀ i b, nrd (ExceptT.run (f i b))) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      nrd (ExceptT.run (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs)) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (b : β),
      (range.stop - i + 1).toNat = n →
      nrd (ExceptT.run (IntRange.forIn'.loop range (fun a _ b => f a b) b i hs)) from
    fun i hs b => H _ i hs b rfl
  intro n
  induction n with
  | zero =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    have hni : ¬ i ∈ range := by
      intro h
      simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
      have := Int.toNat_eq_zero.mp hn
      omega
    simp only [dif_neg hni]
    trivial
  | succ n ih =>
    intro i hs b hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      refine AxSymCtl.nrdRBind _ _ (hf i b) (fun r => ?_)
      cases r with
      | done b' => trivial
      | yield b' =>
        have hn' : (range.stop - (i + range.step) + 1).toNat = n := by
          simp only [Membership.mem, hstep, show (1 : Int) > 0 from by decide, ite_true] at h
          rw [hstep]
          omega
        exact ih _ _ b' hn'
    · simp only [dif_neg h]
      trivial

theorem AxSymCtl.nrdRForIn {R β : Type} (range : IntRange) (hstep : range.step = 1) (b : β)
    (f : Int → β → SailME R (ForInStep β)) (hf : ∀ i b, nrd (ExceptT.run (f i b))) :
    nrd (ExceptT.run (forIn range b f)) :=
  AxSymCtl.nrdRForInLoop range hstep f hf range.start (by simp) b

/-- (Lean-only) Leaf facts for the automation. -/
theorem AxSymCtl.nrdIte {X : Type} (c : Prop) [Decidable c] (a b : SailM X)
    (ha : nrd a) (hb : nrd b) : nrd (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb
theorem AxSymCtl.nrdRIte {R X : Type} (c : Prop) [Decidable c] (a b : SailME R X)
    (ha : nrd (ExceptT.run a)) (hb : nrd (ExceptT.run b)) :
    nrd (ExceptT.run (if c then a else b)) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb
theorem AxSymCtl.nrdDite {X : Type} (c : Prop) [Decidable c] (a : c → SailM X)
    (b : ¬ c → SailM X) (ha : ∀ h, nrd (a h)) (hb : ∀ h, nrd (b h)) :
    nrd (if h : c then a h else b h) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h
theorem AxSymCtl.nrdRDite {R X : Type} (c : Prop) [Decidable c] (a : c → SailME R X)
    (b : ¬ c → SailME R X) (ha : ∀ h, nrd (ExceptT.run (a h))) (hb : ∀ h, nrd (ExceptT.run (b h))) :
    nrd (ExceptT.run (if h : c then a h else b h)) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h
theorem AxSymCtl.nrdFreeBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    nrd m → (∀ x, nrd (f x)) → nrd (FreeM.bind m f) := nrdBind m f
theorem AxSymCtl.nrdLiftSelf {X : Type} (m : SailM X) (h : nrd m) :
    nrd (monadLift m : SailM X) := h

open Lean Elab Tactic Meta in
/-- Rocq `nrd_step`/`nrd_unf`/`nrd_cer` (with `head_of`): `AxSpineOk2.rff_step` for `nrd`
goals. -/
elab "ax_sym_ctl_nrd_step" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  unless tgt.isAppOf ``Weak.nrd do throwError "ax_sym_ctl_nrd_step: not an nrd goal"
  let t0 := tgt.appArg!
  let wrapped := t0.isAppOf ``ExceptT.run
  let t := if wrapped then t0.appArg! else t0
  let args := t.getAppArgs
  let isE (e : Lean.Expr) : MetaM Bool := do
    return (← whnfR (← instantiateMVars e)).consumeMData.isAppOf ``ExceptT
  let ev (stx : TacticM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← stx)
  let hd := t.getAppFn.constName?
  -- (Lean-only) beta / zeta at the head
  if t.getAppFn.isLambda || t.isLet then
    let t' := if t.isLet then t.letBody!.instantiate1 t.letValue! else t.headBeta
    let t'' ← if wrapped then mkAppM ``ExceptT.run #[t'] else pure t'
    replaceMainGoal [← g.replaceTargetDefEq (← mkAppM ``Weak.nrd #[t''])]
    return
  if !wrapped then
    let isET ← if (hd == some ``Bind.bind || hd == some ``Pure.pure) && args.size > 0 then
        isE args[0]!
      else if (hd == some ``ite || hd == some ``dite) && args.size > 0 then
        (do let a ← whnfR args[0]!; return a.isApp && (← isE a.appFn!))
      else (do let ty ← inferType t; return ty.isApp && (← isE ty.appFn!))
    if isET then
      let ng ← mkAppM ``Weak.nrd #[← mkAppM ``ExceptT.run #[t]]
      replaceMainGoal [← g.replaceTargetDefEq ng]
      return
  match hd with
  | some c =>
    if c == ``Bind.bind || c == ``FreeM.bind then
      if wrapped then ev `(tactic| (apply AxSymCtl.nrdRBind <;> try intro _))
      else if c == ``FreeM.bind then ev `(tactic| (apply AxSymCtl.nrdFreeBind <;> try intro _))
      else ev `(tactic| (apply nrdBind <;> try intro _))
    else if c == ``ite then
      if wrapped then ev `(tactic| apply AxSymCtl.nrdRIte) else ev `(tactic| apply AxSymCtl.nrdIte)
    else if c == ``dite then
      if wrapped then ev `(tactic| (apply AxSymCtl.nrdRDite <;> intro _))
      else ev `(tactic| (apply AxSymCtl.nrdDite <;> intro _))
    else if c == ``liftM || c == ``monadLift || c == ``MonadLiftT.monadLift then
      if wrapped then ev `(tactic| apply nrdLiftR) else ev `(tactic| apply AxSymCtl.nrdLiftSelf)
    else if c == ``SailME.run then ev `(tactic| apply nrdCatchEarlyReturn)
    else if c == ``PreSail.tryCatchAll then ev `(tactic| (apply nrdTryCatch <;> try intro _))
    else if c == ``PreSail.sailTryCatch then
      ev `(tactic| (apply AxSymCtl.nrdSailTryCatch <;> try intro _))
    else if c == ``ForIn.forIn then
      if wrapped then ev `(tactic| (apply AxSymCtl.nrdRForIn _ rfl <;> intro _ _))
      else ev `(tactic| (apply nrdForeachZMUp _ rfl <;> intro _ _))
    else if c == ``Pure.pure || c == ``FreeM.pure then ev `(tactic| exact True.intro)
    else if c == ``FreeM.impure then
      if wrapped then ev `(tactic| first | exact True.intro | simp only [ExceptT.run])
      else ev `(tactic| first | exact True.intro | simp only [nrd])
    else if c == ``readReg || c == ``writeReg then
      ev `(tactic| simp only [readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit])
    else if c == ``letFun then ev `(tactic| dsimp only)
    else if (c.toString.endsWith "_callback") then ev `(tactic| exact True.intro)
    else if ← isMatcher c then
      try ev `(tactic| split)
      catch _ =>
        let some info ← getMatcherInfo? c | throwError "ax_sym_ctl_nrd_step: no matcher info"
        let ds := args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)
        let some d := ds.find? (·.isFVar) | throwError "ax_sym_ctl_nrd_step: no variable discriminant"
        let gs ← g.cases d.fvarId!
        replaceMainGoal (gs.map (·.mvarId)).toList
        evalTactic (← `(tactic| all_goals (try dsimp only)))
    else
      try ev `(tactic| unfold $(mkIdent c):ident)
      catch _ => ev `(tactic| exact True.intro)
  | none =>
    if t.isLet then ev `(tactic| dsimp only) else throwError "ax_sym_ctl_nrd_step: no constant head"

/-- Rocq `nrd_auto`. -/
syntax "ax_sym_ctl_nrd_auto" : tactic
macro_rules
  | `(tactic| ax_sym_ctl_nrd_auto) => `(tactic| repeat (first
      | ax_sym_ctl_nrd_step
      | (intro _)
      | exact True.intro
      | rfl))

/-- The instruction-independent spine pieces are read-free. -/
theorem nrdShouldIncMinstret (p : Privilege) : nrd (should_inc_minstret p) :=
  nrdOfRfF _ (rfFShouldIncMinstret p)
theorem nrdZca : nrd (currentlyEnabled .Ext_Zca) := nrdOfRfF _ rfFCurrentlyEnabledZca
theorem nrdLpad : nrd (is_landing_pad_expected ()) := by ax_sym_ctl_nrd_auto
theorem nrdDispatchInterrupt (p : Privilege) : nrd (dispatchInterrupt p) := by ax_sym_ctl_nrd_auto
theorem nrdTickClock : nrd (tick_clock ()) := by ax_sym_ctl_nrd_auto

/-! # 3. THE BUDGETED BRIDGE `wpdOfEvB`: the row position reported exactly -/

section bridgeB
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (img : Image) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, M GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, M GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (kend : Nat) (HGl : ∀ GD, G GD → (AxOpsem.grow GD i).length = kend)

include HG HGl Hmid in
/-- A GRAPH read at the row end is stuck: no row item, no program step (deviation 1: a fetch
read is not stuck, hence `Hnf`). -/
theorem wpdStuckReadM (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false) :
    ∀ rs, A rs →
    ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, kend⟩ Φ := by
  intro rs HAr
  let P : Athread → Prop := fun s => ∃ rs1 ib1,
    s = ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs1 none ib1, kend⟩ ∧ A rs1
  have Hnord : ∀ GD s1 id K, G GD → P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K HGD ⟨rs1, ib1, rfl, -⟩ ⟨lb, Hlb, -⟩
    simp only at Hlb
    rw [List.getElem?_eq_none (by rw [HGl GD HGD]; exact Nat.le_refl _)] at Hlb
    cases Hlb
  have Hclos : ∀ GD s1 l s2, G GD → P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ False) := by
    rintro GD s1 l s2 - ⟨rs1, ib1, rfl, -⟩ Hst
    exfalso
    obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
    obtain ⟨tvs, -, hl, -⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs1 ib1 d l _ d' Hdev Hlat Hnf hps
    subst hl
    cases Hst with
    | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
    | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
    | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
  have Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ False := by
    rintro s1 s2 ⟨rs1, ib1, rfl, HA1⟩ Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p2, k2⟩ := s2
    simp only at hk hp
    subst hk
    cases p2 with
    | PDisk _ => exact hp.elim
    | PHart c m2 rs2 fn2 ib2 =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      exact .inl ⟨rs2, ib2, rfl, HA rs1 rs2 HA1 hag⟩
  iapply (wpdOfClosedRunGM M i G P (fun _ => False) Φ HG Hnord (fun GD s1 l s2 h1 h2 h3 _ => Hclos GD s1 l s2 h1 h2 h3) Hwire) $$
    %⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, kend⟩ %⟨rs, ib, rfl, HAr⟩
  isplit
  · iintro %s2 %H
    exact H.elim
  · iintro %GD %s1 %HGD %HP1 %Heq
    obtain ⟨rs1, ib1, rfl, -⟩ := HP1
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG HGl Hmid Htext Hflow in
/-- THE BUDGETED BRIDGE. -/
theorem wpdOfEvBM (Q : Nat → Unit → ExecSt → Prop) (m : SailM Unit) (t : ExecSt) (b : Nat) :
    EvB img (fun _ _ => False) Q m t b →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs → k + b = kend →
    ⊢ (∀ b' t' rs' ib' k', ⌜Q b' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜k' + b' = kend⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | ebRet x t b HQ =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply C $$ %b %t %rs %ib %kk %HQ %Hag %Hkb
  | ebExt e k t b he => exact he.elim
  | ebNf _ _ _ _ _ _ _ _ _ hq => exact (hq .Exit).elim
  | ebRd r k t b _ _ IHs IHn =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1 Hkb) $$ C
      · have h := IHn Hs rs1 ib1 kk HA1 Hkb
        rw [← HA1 r Hs] at h
        iapply h $$ C
  | ebWr r v k t b Hr _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hkb) $$ C
  | ebMrd n va req k t b vs Hdev Hlat Hnf Hvs _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdImgRead3M M img i Φ cpu G HG Hmid Htext Hflow n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib (kk + 1) HA' (by omega)) $$ C
  | ebIf n va req k t b vs Hdev Hlat Hfe Hvs _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdImgFetch3M M img i Φ cpu G HG Hmid Htext n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib kk HA' Hkb) $$ C
  | ebEnd n va req k t Hdev Hlat Hnf =>
    intro rs ib kk Hag Hkb
    have e : kk = kend := by omega
    subst e
    iintro -
    iapply (wpdStuckReadM M i Φ cpu G HG Hmid kk HGl n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | ebIa n w k t b Hsf _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hkb) $$ C
  | ebBa _ _ k t b _ IH | ebCo _ k t b _ IH | ebTl _ k t b _ IH | ebTe _ k t b _ IH
  | ebRx _ k t b _ IH | ebTs _ k t b _ IH | ebTx _ k t b _ IH | ebCc k t b _ IH
  | ebMsg _ k t b _ IH | ebGcc k t b _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ _ ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hkb) $$ C

include HG HGl Hmid Htext Hflow in
/-- ONE INSTRUCTION from a `.pure ()` boundary at position `k` (budget `kend - k`),
certificates for both ticks. -/
theorem wpdInstrOfEvBM (Q : Nat → Unit → ExecSt → Prop) (rs : RegFile) (k : Nat) (s : Athread)
    (Hs : RetX cpu rs k s) (Hk : k ≤ kend)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvB img (fun _ _ => False) Q (riscvStep tick) t (kend - k)) :
    ⊢ (∀ b' t' rs' ib' k', ⌜Q b' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜k' + b' = kend⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  iintro C
  iapply (wpdRetNode3M M i Φ cpu G HG rs k s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (wpdOfEvBM M img i Φ cpu G HG Hmid Htext Hflow kend HGl Q _ ⟨rs', fun _ => none, testDevs⟩
    (kend - k) (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k
    (regsAgreeRefl _ _) (by omega)) $$ C

/-! ### (Lean-only, Q16) STUCK ENDS: a failure node and an imageless fetch have no step -/


/-- (Lean-only) A hart thread at a failure node (a stuck end that is not a `midState`). -/
def AxSymCtl.errState (s : Athread) : Prop :=
  ∃ (c : CPU) (e : Sail.Error exception) (KK : Empty → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
    s.atP = .PHart c (.impure (.error e) KK) rs fn ib

/-- (Lean-only) A failure node has no program step. -/
theorem AxSymCtl.pstepErrInv (e : Sail.Error exception) (KK : Empty → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    ¬ pstepProg (.PHart cpu (.impure (.error e) KK) rs none ib) d l p' d' := by
  cases p' with
  | PDisk _ => intro h; exact h.elim
  | PHart c' m' rs' fn' ib' =>
    rintro ⟨-, ors, oib, obar, -, -, hn, -⟩
    first | exact hn | (simp only [pstepNode, pnodeStep] at hn)

/-- (Lean-only) The hart-thread shape kept by a wire step. -/
theorem AxSymCtl.wireKeeps (m : SailM Unit) (k : Nat) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs') (s1 s2 : Athread) :
    (∃ rs1 ib1, s1 = ⟨.PHart cpu m rs1 none ib1, k⟩ ∧ A rs1) → awire s1 s2 →
    (∃ rs1 ib1, s2 = ⟨.PHart cpu m rs1 none ib1, k⟩ ∧ A rs1) ∨ False := by
  rintro ⟨rs1, ib1, rfl, HA1⟩ Hw
  obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
  obtain ⟨p2, k2⟩ := s2
  simp only at hk hp
  subst hk
  cases p2 with
  | PDisk _ => exact hp.elim
  | PHart c m2 rs2 fn2 ib2 =>
    obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
    exact .inl ⟨rs2, ib2, rfl, HA rs1 rs2 HA1 hag⟩

include HG in
/-- (Lean-only, Q16) A FAILURE NODE is stuck: the WPd holds at any row position (at the row end,
the post holds there: `Herr`). -/
theorem AxSymCtl.wpdStuckErrM
    (Herr : ∀ GD s, G GD → AxSymCtl.errState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s)
    (e : Sail.Error exception) (KK : Empty → SailM Unit) (ib : Ibch)
    (k : Nat) (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs') :
    ∀ rs, A rs → ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.error e) KK) rs none ib, k⟩ Φ := by
  intro rs HAr
  let P : Athread → Prop := fun s => ∃ rs1 ib1,
    s = ⟨.PHart cpu (.impure (.error e) KK) rs1 none ib1, k⟩ ∧ A rs1
  have Hnord : ∀ GD s1 id K, G GD → P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K - ⟨rs1, ib1, rfl, -⟩ ⟨lb, -, -, -, HK⟩
    obtain ⟨l, d, d', -, -, hps, -⟩ := HK (List.replicate (aidentN id) (0#8)) List.length_replicate
    exact AxSymCtl.pstepErrInv cpu e KK rs1 ib1 d l _ d' hps
  have Hclos : ∀ GD s1 l s2, G GD → P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ False) := by
    rintro GD s1 l s2 - ⟨rs1, ib1, rfl, -⟩ Hst -
    obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
    exact (AxSymCtl.pstepErrInv cpu e KK rs1 ib1 d l _ d' hps).elim
  iapply (wpdOfClosedRunGM M i G P (fun _ => False) Φ HG Hnord Hclos
    (AxSymCtl.wireKeeps cpu _ k A HA)) $$
    %⟨.PHart cpu (.impure (.error e) KK) rs none ib, k⟩ %⟨rs, ib, rfl, HAr⟩
  isplit
  · iintro %s2 %H
    exact H.elim
  · iintro %GD %s1 %HGD %HP1 %Heq
    obtain ⟨rs1, ib1, rfl, -⟩ := HP1
    iapply (Herr GD _ HGD ⟨cpu, e, KK, rs1, none, ib1, rfl⟩ Heq)

include HG Hmid in
/-- (Lean-only, Q16) AN IMAGELESS FETCH is stuck: when every allowed graph's boot image lacks a
byte of it, no pinned fetch step exists; the WPd holds at any row position. -/
theorem AxSymCtl.wpdStuckNfM (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hfe : (classify req.access_kind).akIfetch = true)
    (Hnone : ∀ GD, G GD → ∃ j : Nat, j < n ∧ GD.gdG.gxImg (paZ req.pa + (j : Int)) = none) :
    ∀ rs, A rs →
    ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  intro rs HAr
  let P : Athread → Prop := fun s => ∃ rs1 ib1,
    s = ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs1 none ib1, k⟩ ∧ A rs1
  have Hnord : ∀ GD s1 id K, G GD → P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K - ⟨rs1, ib1, rfl, -⟩
    exact AxCjrWpd.fetchNoRead _ cpu n va req KK rs1 ib1 k id K Hdev Hfe
  have Hclos : ∀ GD s1 l s2, G GD → P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
      WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ False) := by
    rintro GD s1 l s2 HGD ⟨rs1, ib1, rfl, -⟩ Hst Hpin
    exfalso
    obtain ⟨tvs, hlen, rfl, -⟩ :=
      AxCjrWpd.fetchAstepInv _ cpu n va req KK rs1 ib1 k l s2 Hdev Hfe Hst
    obtain ⟨j, hj, hno⟩ := Hnone GD HGD
    have h := Hpin.2 j (by omega)
    rw [hno, List.getElem?_map, List.getElem?_eq_getElem (by omega : j < tvs.length)] at h
    simp at h
  iapply (wpdOfClosedRunGM M i G P (fun _ => False) Φ HG Hnord Hclos
    (AxSymCtl.wireKeeps cpu _ k A HA)) $$
    %⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ %⟨rs, ib, rfl, HAr⟩
  isplit
  · iintro %s2 %H
    exact H.elim
  · iintro %GD %s1 %HGD %HP1 %Heq
    obtain ⟨rs1, ib1, rfl, -⟩ := HP1
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG HGl Hmid Htext Hflow in
/-- (Lean-only, Q16) THE BUDGETED BRIDGE WITH STUCK ENDS: `wpdOfEvBM` for certificates accepting
every stuck end (`QE := True`: failure nodes and imageless fetches, `EvB.ebNf`).  The imageless
fetch is stuck because the allowed graphs' boot images lack what `img` lacks (`HGimg`). -/
theorem AxSymCtl.wpdOfEvBStuckM
    (HGimg : ∀ GD, G GD → ∀ a, img a = none → GD.gdG.gxImg a = none)
    (Herr : ∀ GD s, G GD → AxSymCtl.errState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s)
    (Q : Nat → Unit → ExecSt → Prop) (m : SailM Unit) (t : ExecSt) (b : Nat) :
    EvB img (fun _ _ => True) Q m t b →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs → k + b = kend →
    ⊢ (∀ b' t' rs' ib' k', ⌜Q b' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜k' + b' = kend⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | ebRet x t b HQ =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply C $$ %b %t %rs %ib %kk %HQ %Hag %Hkb
  | ebExt e k t b _ =>
    intro rs ib kk Hag _
    iintro -
    iapply (AxSymCtl.wpdStuckErrM M i Φ cpu G HG Herr e k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) rs Hag)
  | ebNf n va req k t b Hdev Hfe Hno _ =>
    intro rs ib kk Hag _
    iintro -
    obtain ⟨j, hj, hn⟩ := AxSymCtl.imgBytesNoneByte img _ n Hno
    iapply (AxSymCtl.wpdStuckNfM M i Φ cpu G HG Hmid n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe
      (fun GD hGD => ⟨j, hj, HGimg GD hGD _ hn⟩) rs Hag)
  | ebRd r k t b _ _ IHs IHn =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1 Hkb) $$ C
      · have h := IHn Hs rs1 ib1 kk HA1 Hkb
        rw [← HA1 r Hs] at h
        iapply h $$ C
  | ebWr r v k t b Hr _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hkb) $$ C
  | ebMrd n va req k t b vs Hdev Hlat Hnf Hvs _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdImgRead3M M img i Φ cpu G HG Hmid Htext Hflow n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib (kk + 1) HA' (by omega)) $$ C
  | ebIf n va req k t b vs Hdev Hlat Hfe Hvs _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdImgFetch3M M img i Φ cpu G HG Hmid Htext n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib kk HA' Hkb) $$ C
  | ebEnd n va req k t Hdev Hlat Hnf =>
    intro rs ib kk Hag Hkb
    have e : kk = kend := by omega
    subst e
    iintro -
    iapply (wpdStuckReadM M i Φ cpu G HG Hmid kk HGl n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | ebIa n w k t b Hsf _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hkb) $$ C
  | ebBa _ _ k t b _ IH | ebCo _ k t b _ IH | ebTl _ k t b _ IH | ebTe _ k t b _ IH
  | ebRx _ k t b _ IH | ebTs _ k t b _ IH | ebTx _ k t b _ IH | ebCc k t b _ IH
  | ebMsg _ k t b _ IH | ebGcc k t b _ IH =>
    intro rs ib kk Hag Hkb
    iintro C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ _ ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hkb) $$ C

include HG HGl Hmid Htext Hflow in
/-- (Lean-only, Q16) `wpdInstrOfEvBM` with stuck ends (`AxSymCtl.wpdOfEvBStuckM`). -/
theorem AxSymCtl.wpdInstrOfEvBStuckM
    (HGimg : ∀ GD, G GD → ∀ a, img a = none → GD.gdG.gxImg a = none)
    (Herr : ∀ GD s, G GD → AxSymCtl.errState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s)
    (Q : Nat → Unit → ExecSt → Prop) (rs : RegFile) (k : Nat) (s : Athread)
    (Hs : RetX cpu rs k s) (Hk : k ≤ kend)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvB img (fun _ _ => True) Q (riscvStep tick) t (kend - k)) :
    ⊢ (∀ b' t' rs' ib' k', ⌜Q b' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜k' + b' = kend⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  iintro C
  iapply (wpdRetNode3M M i Φ cpu G HG rs k s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (AxSymCtl.wpdOfEvBStuckM M img i Φ cpu G HG Hmid Htext Hflow kend HGl HGimg Herr Q _
    ⟨rs', fun _ => none, testDevs⟩ (kend - k)
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k
    (regsAgreeRefl _ _) (by omega)) $$ C

end bridgeB

/-! ### The riscv.cat instances under the Rocq names (`…M` at `rvwmoCatConsistent`) -/

section bridgeBCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (kend : Nat) (HGl : ∀ GD, G GD → (AxOpsem.grow GD i).length = kend)

include HG HGl Hmid in
theorem wpdStuckRead (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false) :
    ∀ rs, A rs →
    ⊢ wpd .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, kend⟩ Φ :=
  wpdStuckReadM rvwmoCatConsistent i Φ cpu G HG Hmid kend HGl n va req KK ib A HA Hdev Hlat Hnf

include HG HGl Hmid Htext Hflow in
theorem wpdOfEvB (Q : Nat → Unit → ExecSt → Prop) (m : SailM Unit) (t : ExecSt) (b : Nat)
    (H : EvB img (fun _ _ => False) Q m t b) :
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs → k + b = kend →
    ⊢ (∀ b' t' rs' ib' k', ⌜Q b' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜k' + b' = kend⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ :=
  wpdOfEvBM rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow kend HGl Q m t b H

include HG HGl Hmid Htext Hflow in
theorem wpdInstrOfEvB (Q : Nat → Unit → ExecSt → Prop) (rs : RegFile) (k : Nat) (s : Athread)
    (Hs : RetX cpu rs k s) (Hk : k ≤ kend)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvB img (fun _ _ => False) Q (riscvStep tick) t (kend - k)) :
    ⊢ (∀ b' t' rs' ib' k', ⌜Q b' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜k' + b' = kend⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i s Φ :=
  wpdInstrOfEvBM rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow kend HGl Q rs k s Hs Hk Hb
    Hcert

include HG HGl Hmid Htext Hflow in
/-- (Lean-only, Q16) `AxSymCtl.wpdInstrOfEvBStuckM` at `rvwmoCatConsistent`. -/
theorem AxSymCtl.wpdInstrOfEvBStuck
    (HGimg : ∀ GD, G GD → ∀ a, img a = none → GD.gdG.gxImg a = none)
    (Herr : ∀ GD s, G GD → AxSymCtl.errState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s)
    (Q : Nat → Unit → ExecSt → Prop) (rs : RegFile) (k : Nat) (s : Athread)
    (Hs : RetX cpu rs k s) (Hk : k ≤ kend)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       EvB img (fun _ _ => True) Q (riscvStep tick) t (kend - k)) :
    ⊢ (∀ b' t' rs' ib' k', ⌜Q b' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜k' + b' = kend⌝ -∗
         wpd .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpd .MaybeStuck i s Φ :=
  AxSymCtl.wpdInstrOfEvBStuckM rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow kend HGl HGimg
    Herr Q rs k s Hs Hk Hb Hcert

end bridgeBCat

end Weak
