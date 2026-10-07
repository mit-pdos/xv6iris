/-
Weak: **track F, the AxSL instruction bridge — PART A** (`AxFetch1`): the row shape of `ld8`/
`sd8`, the REGISTER-TOWER PEEL (`execEff` ⇒ an admin-only opax run to the first memory node),
the generic single-node bridges (read / write / FETCH), and the `ld8` instantiation.

Rocq: `iris/AxFetch.v` @ xxvzwolszwmp, lines 1–1053 (header, §1, §2 preamble, §2.0, §2.1).
The Rocq file is split for the port: `AxFetch1` (this file) … later parts (§2.2 onwards: the
ld8/sd8 row runs, jalr/c.jr, the RVC fetch twin, c.ldsp/c.sdsp, §3's demonstration, §4's ctrl
gate) import this file.

## What the whole AxFetch port proves (the Rocq header, in substance)

Track F, first slice: acert → fetch/decode → `AxOpsem.astepProg` for `ld8`/`sd8` (and, in the
later sections, `jalr`/`ret`, `c.jr`/`c.ret`, `c.ldsp`/`c.sdsp`).  Design `claude-notes/design/
weak-memory-lb-axsl.md` §1-L3 ("the leaf layer is RE-DERIVED") and `AxInstr`'s ledger (targets
`tAinstr`/`tAinstrLd8`/`tAinstrSd8`).  `AxInstr` is READ-ONLY from here: nothing in the AxFetch
port discharges its `AxInstrTargets` class (that also needs `AxProt`'s owned-event Iris shell).
What the port adds is the PURE (non-Iris) machinery those targets' eventual proofs run on: the
shape of the graph events an instruction realizes, and generic lemmas showing `astepProg` /
`areadStep` realize a SINGLE Sail memory node of any shape, factored so the instruction-specific
residue is minimal.
* THE REGISTER-TOWER PEEL (§2.0, this file): given `execEff m s = some ((), s', e :: es)` for ANY
  `m : SailM Unit` whose first recorded effect `e` is a plain RAM read (resp. write) of a given
  identity, an `AxOpsem.astepProg` ADMIN-ONLY `rtc` run from `m` to the concrete `memRead`
  (resp. `memWrite`) node `m` unfolds to, at the register file / bits bank the small step
  actually computes, with the memory untouched (`s2.mem = s.mem`) and the node's own `execEff`
  fact.  Proved by induction on the monad, one case per lean-sail `Outcome` constructor: register
  reads/writes, announces and the other silent outcomes are admin steps (`LSilent`/`LRegW`/
  `LCtrl`/`LInstr`), an MMIO access is an admin `LDev` step, a barrier or the wrong RAM access
  would cons the wrong effect.  The Rocq header's "ATTEMPTED AND REMOVED" traps (IH at the outer
  state/bank; `default`-shaped successors) do not arise: each Lean case passes the
  successor's state and bank explicitly, and the admin step is composed by
  `AxFetch1.admPrepend` whose successor is stated at `ors.getD rs`/`oib.getD ib` against the
  IH's run.
* §2.1 (this file): the peel at the REAL `execute (LOAD …)` term (`WeakLeafLd8.execEffLd8At`,
  bind-embedded into `SailM Unit` by `>>= fun _ => pure ()`), composed with the data-read bridge:
  the DATA event's `areadStep`.
* §2.2–§2.7 (later parts): the whole-instruction row runs, gluing the fetch in front by the same
  peel at `riscvStep tick` (`WeakFetchEff`'s `execEffStepOfLeafBase` / the RVC twin), the
  round-trip on the fetched word via the peel's `.mem`-invariance, and the second peel to the
  data node (or to the `pure` boundary for `jalr`/`c.jr`).  §4: the `c.jr ra` control gate
  (`WeakDeps.depsCtrl`/`erwOf` into `AxDeps.dstepT`'s `LCtrl` arm and `AxGate.gateSrcs`).
* OPEN in Rocq (recorded, not admitted): the rows' dependency sources (`AxPair.lblIdent`'s
  sources, `AxDeps`' track); the Iris shell (`AxProt`); the `c.jr` read-set hypothesis on the real
  run beyond §4.6's prerequisites.

## O2 STAGE C (`notes/weak-port-o2-stageC.md` §D, track F) — THE FETCH IS NOT A ROW EVENT

Rocq: an instruction's fetch is a ROW ITEM (`LLoad false pc … [0;0;0;0]`, identity
`af_fetch_ident pc = IRead false pc 4`), realized by `AStep_fetch` answered by the oracle
`fetch_answers T img`; an `ld`/`sd` row is `[fetch @ k; data @ S k]`.  Lean (owner Q-C1/Q-C2,
`AxOpsem` deviation 2): a fetch is an ADMINISTRATIVE step — `AStepAdmin` at
`lbAdmin true (LIFetch base tvs)` — that KEEPS the row position; there is no fetch row item, no
fetch identity, no oracle, and the `T`/`img` parameters of every opax relation are gone.  So in
the whole AxFetch port:
- `af_astep_fetch_of_memread` ↦ `afAstepFetchOfMemread`: the fetch node (a RAM `memRead` whose
  access kind has `akIfetch = true`, e.g. `WeakFetchEff.wakIfetch`) takes ONE admin step with label
  `LIFetch (paZ req.pa) (tagVals vs)` at position `k` → `k` (Rocq: `k` → `S k`, premises the row
  item, its identity, `ak_sync = false`, `fetch_answers`).  `vs` is any byte list of the width;
  the fetched bytes are not a graph value (the image pin lives in `WeakAxRealize.fetchPin`).
- `awp_fetch` ↦ the admin skip (`AxInstr.awpFetch`).
- Row shapes lose their fetch item: `afLd8RowShape row k ea` / `afSd8RowShape row k ea` say the
  DATA item sits at `k` (Rocq: fetch at `k`, data at `S k`); the pc argument is dropped.  A
  whole-instruction run of a load/store goes from position `k` (fetch + admin, kept) to the data
  node at `k`, and the data step moves to `k + 1`; a fetch-only instruction (`jalr`) consumes NO
  position.  §7-style hand-built rows lose their fetch items (positions re-indexed).
- In Lean the fetch's trace element is `.WEread WeakFetchEff.wakIfetch pc 4` (Rocq `wak_plain`),
  so the later parts' peel to the FETCH node is `afAdminRunToMemread` at `ak := wakIfetch`, and
  `afAstepFetchOfMemread` takes `akIfetch = true` (the data bridges take `akIfetch = false`).

## Deviations from Rocq

1. NAMES / VOCABULARY: the tree's camelCase (map below); `M unit` ↦ `SailM Unit`;
   `RiscvLang.mstate` ↦ `ExecSt` (`sregs`/`mem`/`mdev` ↦ `regs`/`mem`/`dev`); `oib32` ↦ `Ibch`;
   `dev_state` (opax) ↦ `Efab` (`AxOpsem` deviation 1), the peel's device is `efInit s.dev`;
   `Interface.ReadReq.t n` ↦ `Mem_read_request n va …` (a new bound `va`, `AxOpsem` deviation
   1), `Interface.WriteReq.t n` ↦ `Mem_write_request n va …`; a read continuation receives
   `.Ok (w, none)`, a write continuation `.Ok (some true)` (Rocq `inl (w, None)` / `inl None`);
   `Interface.WriteReq.value req = v` ↦ `req.value = some v` (lean-sail write values are
   `Option`); `N.to_nat n` ↦ `n`; `S k` ↦ `k + 1`; `l !! k` ↦ `l[k]?`; `rtc` ↦ `MachCSL.rtc`;
   `pa_z` ↦ `paZ`; `wbytes` ↦ `WeakInterpProj.wbytes`.  No name of this file is in
   `notes/weak-port-dupnames.json`.
2. O2 STAGE C (above): `astep_prog row T img` ↦ `AxOpsem.astepProg row` everywhere (the
   peel lemmas lose their `Tt img` binders); `afAstepFetchOfMemread` restated as the admin
   fetch step; the row shapes and their projections restated without the fetch item;
   `af_fetch_ident` and the `_fetch` projections dropped (below).
3. THE PEEL TAKES `n ≠ 0` (`afAdminRunToMemread`/`afAdminRunToMemwrite`).  Lean's `execEff`
   routes an access to the device fabric by `mmioAcc pa n = devAddr pa && n != 0`
   (`Weak.Exec` deviation 2), while `pnodeStep` routes by `devAddr pa` alone; a width-0 access at
   a device address is a RAM effect for `execEff` but an MMIO node for `pnodeStep`.  With
   `n ≠ 0` the target node is a RAM node of `pnodeStep` (`devAddr pa = false` is concluded, as in
   Rocq); width-0 device accesses midstream cons an effect of width 0 and are excluded by the
   same premise.  Every caller's width is a literal (`4`, `8`, `2`), discharged by `decide`.
4. THE O2 READ ARM (`WeakEvInst` deviation 2): Rocq's `ak_coh (classify …) = false` premises of
   the data-read bridges (`afPstepProgReadAny`, `afAreadStepOfMemread`) are
   `(classify …).akIfetch = false` (the plain read arm; `AxOpsem.pnodeStepReadAny` has no
   premise, the label is `rdLabel akIfetch akLatest …`).
5. THE WRITE ARM: `afPnodeStepWriteAny`/`afPstepProgWriteAny`/`afAstepWriteOfMemwrite` take
   `req.value = some v` and state the stored bytes as `wbytes n v` (Rocq `WriteReq.value req`);
   the `pnodeStep`/`pstepProg` facts carry the barrier report `obar = none`
   (`WeakEvInst` deviation 4).
6. §2.1 `afLd8RunToRead`: the premises are `WeakLeafLd8.execEffLd8At`'s (that file's deviations
   1/3: `s0.gpr rs1 + sign_extend imm = ea`, `inRam ea 8`, `BytesAt s0 ea 8 v`,
   `pma_regions = bootPMA`, `pmpAllOff`, `(… == 1#1) = false`); the embedding is
   `execute (…) >>= fun _ => pure ()` (Rocq `Defs.bind … (fun _ => Interface.Ret tt)`); the
   read's access kind is `wakPlain`.
7. Lean-only helpers (file-qualified): `AxFetch1.admPrepend` (one admin `pnodeStep` in front of
   an opax run — the composition every peel arm uses), `AxFetch1.pstepProgFetchAny` (the fetch
   node's `pstepProg` fact, the fetch twin of `afPstepProgReadAny`).

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `afAdminRunToMemread`/`afAdminRunToMemwrite` take `WeakEvLang.noSfAnn m s` (along `execEff`'s path no announce is an SFENCE.VMA word — such an announce emits the marker, a graph event, and the run would not be admin-only); `afAdminRunToMemread` also returns `noSfAnn` at the reached node (for the next peel).  Q10 (owner ruling): `afLd8RunToRead` no longer takes it — its `execute` run's `noSfAnn` is the Lean-only `AxFetch1.noSfAnnLd8At` (the `nosf_run` twin of `WeakLeafLd8.execEffLd8At`, over `WeakFetchEff` §10d).

**Rocq → Lean name map.**  `af_ld8_data_ident` `afLd8DataIdent`, `af_sd8_data_ident`
`afSd8DataIdent`, `af_ld8_row_shape` `afLd8RowShape`, `af_sd8_row_shape` `afSd8RowShape`,
`af_ld8_row_shape_data` `afLd8RowShapeData`, `af_sd8_row_shape_data` `afSd8RowShapeData`,
`erw_label_lb_admin` `erwLabelLbAdmin`, `af_admin_run_to_memread` `afAdminRunToMemread`,
`af_admin_run_to_memwrite` `afAdminRunToMemwrite`, `af_pnode_step_write_any`
`afPnodeStepWriteAny`, `af_pstep_prog_write_any` `afPstepProgWriteAny`,
`af_pstep_prog_read_any` `afPstepProgReadAny`, `af_aread_step_of_memread`
`afAreadStepOfMemread`, `af_astep_fetch_of_memread` `afAstepFetchOfMemread` (restated,
deviation 2), `af_astep_write_of_memwrite` `afAstepWriteOfMemwrite`, `af_ld8_run_to_read`
`afLd8RunToRead`.

**Dropped (O2 Stage C: no fetch row item):** `af_fetch_ident` (the identity of the fetch row
item; used only inside AxFetch.v, for fetch row items), `af_ld8_row_shape_fetch`,
`af_sd8_row_shape_fetch` (projections onto the fetch item; used only inside AxFetch.v).
Counts: Rocq 19 declarations in lines 1–1053; Lean 16 + 2 Lean-only.
-/
import Weak.AxOpsem
import Weak.AxInstr
import Weak.WeakEff
import Weak.WeakLeafLd8

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! ## 1. THE ROW SHAPE OF `ld8`/`sd8`

Rocq: an `ld`/`sd` realizes exactly TWO row events, the fetch and the single data event (a plain
8-byte read, resp. write, at the effective address `ea`).  Lean (O2 Stage C): the fetch is an
admin step, so the row carries ONE event, the data item, at the instruction's position `k`.
`WeakLeafLd8.execEffLd8At` / `WeakLeafSd8`'s traces (`[.WEread wakPlain ea 8]`, singular) confirm
there is no other memory event: the register accesses of the config towers are admin steps. -/

/-- The data identity of `ld8`: a plain 8-byte read at `ea`. -/
def afLd8DataIdent (ea : Int) : AidentT := .IRead false ea 8

/-- The data identity of `sd8`: a plain 8-byte write at `ea`. -/
def afSd8DataIdent (ea : Int) : AidentT := .IWrite false ea 8

/-- The row at position `k` carries `ld8`'s data item (Stage C: no fetch item before it). -/
def afLd8RowShape (row : List Lbl) (k : Nat) (ea : Int) : Prop :=
  ∃ lbd, row[k]? = some lbd ∧ aident lbd = afLd8DataIdent ea

/-- The row at position `k` carries `sd8`'s data item (Stage C: no fetch item before it). -/
def afSd8RowShape (row : List Lbl) (k : Nat) (ea : Int) : Prop :=
  ∃ lbd, row[k]? = some lbd ∧ aident lbd = afSd8DataIdent ea

theorem afLd8RowShapeData (row : List Lbl) (k : Nat) (ea : Int) :
    afLd8RowShape row k ea → ∃ lb, row[k]? = some lb ∧ aident lb = afLd8DataIdent ea :=
  fun h => h

theorem afSd8RowShapeData (row : List Lbl) (k : Nat) (ea : Int) :
    afSd8RowShape row k ea → ∃ lb, row[k]? = some lb ∧ aident lb = afSd8DataIdent ea :=
  fun h => h

/-! ## 2. GENERIC SINGLE-NODE BRIDGES

`AxOpsem.pnodeStepReadAny` gives the read arm generically; `afPnodeStepWriteAny` is its write
twin (the plain, non-exclusive, non-MMIO `memWrite` arm of `pnodeStep`).  On top of both,
`afAreadStepOfMemread` / `afAstepFetchOfMemread` / `afAstepWriteOfMemwrite` restate `OpaxWit`'s
hand-built-witness technique GENERICALLY (any request / continuation / registers / fabric).

### 2.0 THE REGISTER-TOWER PEEL: `execEff` (functional) ⇒ `pnodeStep`/`astepProg` (small step) -/

theorem erwLabelLbAdmin (ek : ErwKind) : lbAdmin true (erwLabel ek) := by
  cases ek <;> trivial

/-- (Lean-only) ONE admin `pnodeStep` (unparked hart) in front of an opax run; the successor is
stated at the step's own register / bank outputs. -/
theorem AxFetch1.admPrepend (row : List Lbl) (cpu : CPU) (m m' : SailM Unit) (rs : RegFile)
    (ib : Ibch) (dd dd' : DevStates) (l : Wlabel) (ors : Option RegFile) (oib : Option Ibch)
    (obar : Option barrier_kind) (kpos : Nat) (T : Athread) :
    rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
      ⟨.PHart cpu m' (ors.getD rs) none (oib.getD ib), kpos⟩ T →
    pnodeStep m rs ib dd l m' ors none dd' oib obar → lbAdmin true l →
    rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2) ⟨.PHart cpu m rs none ib, kpos⟩ T :=
  fun h hn hl =>
    rtc_l ⟨l, .AStepAdmin _ kpos (efInit dd) l (.PHart cpu m' (ors.getD rs) none (oib.getD ib))
      { efInit dd with efDev := dd' } hl
      ⟨rfl, ors, oib, obar, rfl, rfl, hn, rfl⟩⟩ h

/-- THE PEEL (read target): if `execEff` runs `m` from `s` to a trace whose first effect is the
plain RAM read `.WEread ak pa n`, then admin-only opax steps reach the `memRead` node `m` unfolds
to, at the registers / bank the small step computes, memory untouched (deviation 3: `n ≠ 0`). -/
theorem afAdminRunToMemread (m : SailM Unit) :
    ∀ (s : ExecSt) (ib : Ibch) (ak : AkInfo) (pa : PAddr) (n : Nat) (s' : ExecSt)
      (es : List Weff),
      n ≠ 0 →
      execEff m s = some ((), s', .WEread ak pa n :: es) →
      WeakEvLang.noSfAnn m s →
      ∀ (cpu : CPU) (kpos : Nat) (row : List Lbl),
        ∃ (s2 : ExecSt) (ib2 : Ibch) (va : Nat)
          (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit),
          classify req.access_kind = ak ∧ req.pa = pa ∧ devAddr pa = false ∧
          s2.mem = s.mem ∧
          execEff (.impure (.ok (.memRead n va req)) KK) s2 =
            some ((), s', .WEread ak pa n :: es) ∧
          rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
            ⟨.PHart cpu m s.regs none ib, kpos⟩
            ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) s2.regs none ib2, kpos⟩ ∧
          WeakEvLang.noSfAnn (.impure (.ok (.memRead n va req)) KK) s2 := by
  induction m with
  | pure y =>
    intro s ib ak pa n s' es _ hex
    simp [execEff] at hex
  | impure call k ih =>
    intro s ib ak pa n s' es hn hex hsf cpu kpos row
    cases call with
    | error e => simp [execEff] at hex
    | ok o =>
      cases o
      case memRead n0 va req =>
        have hex0 := hex
        simp only [execEff] at hex
        by_cases hm : mmioAcc req.pa n0 = true
        · rw [if_pos hm] at hex
          have hdevT : devAddr req.pa = true := by
            simp only [mmioAcc, Bool.and_eq_true] at hm; exact hm.1
          cases hdr : devRead s.dev req.pa n0 with
          | none => simp only [hdr] at hex; cases hex
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at hex
            simp only [WeakEvLang.noSfAnn, if_pos hm, hdr] at hsf
            obtain ⟨s2, ib2, va2, req2, KK, hcl, hpa, hdev, hmem, hee, hrtc, hns⟩ :=
              ih _ (s.setDev d0) ib ak pa n s' es hn hex hsf cpu kpos row
            refine ⟨s2, ib2, va2, req2, KK, hcl, hpa, hdev, hmem, hee, ?_, hns⟩
            refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0 .LDev none none none kpos _
              hrtc ?_ trivial
            simp only [pnodeStep, hdevT, ↓reduceIte]
            exact ⟨w0, by simp [hdr]⟩
        · rw [if_neg hm] at hex
          cases hrb : bmRead s.mem req.pa n0 with
          | none => simp only [hrb] at hex; cases hex
          | some w0 =>
            simp only [hrb] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            simp only [List.cons.injEq, Weff.WEread.injEq] at hcons
            obtain ⟨⟨hak, hpa, rfl⟩, rfl⟩ := hcons
            have hdevF : devAddr req.pa = false := by
              cases hd : devAddr req.pa
              · rfl
              · simp [mmioAcc, hd, hn] at hm
            exact ⟨s, ib, va, req, k, hak.symm, hpa.symm, hpa ▸ hdevF, rfl, hex0, rtc_refl _, hsf⟩
      case memWrite n0 va req =>
        simp only [execEff] at hex
        cases hv : req.value with
        | none => simp only [hv] at hex; cases hex
        | some w =>
          simp only [hv] at hex
          by_cases hm : mmioAcc req.pa n0 = true
          · rw [if_pos hm] at hex
            have hdevT : devAddr req.pa = true := by
              simp only [mmioAcc, Bool.and_eq_true] at hm; exact hm.1
            cases hdw : devWrite s.dev req.pa n0 w with
            | none => simp only [hdw] at hex; cases hex
            | some d0 =>
              simp only [hdw] at hex
              simp only [WeakEvLang.noSfAnn, hv, if_pos hm, hdw] at hsf
              obtain ⟨s2, ib2, va2, req2, KK, hcl, hpa, hdev, hmem, hee, hrtc, hns⟩ :=
                ih _ (s.setDev d0) ib ak pa n s' es hn hex hsf cpu kpos row
              refine ⟨s2, ib2, va2, req2, KK, hcl, hpa, hdev, hmem, hee, ?_, hns⟩
              refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0 .LDev none none none kpos
                _ hrtc ?_ trivial
              simp only [pnodeStep, hdevT, hv, ↓reduceIte]
              simp [hdw]
          · rw [if_neg hm] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            simp at hcons
      case barrier b =>
        simp only [execEff] at hex
        obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
        simp at hcons
      case regRead r =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee, hrtc, hns⟩ :=
          ih _ s (ibRd ib r) ak pa n s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none (some (ibRd ib r))
            none kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial, hns⟩
      case regWrite r v =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee, hrtc, hns⟩ :=
          ih _ (s.setReg r v) ib ak pa n s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev
            (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) (some (s.regs.set r v)) none none
            kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (erwLabelLbAdmin _), hns⟩
      case instrAnnounce nw w =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨hsw, hsf⟩ := hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee, hrtc, hns⟩ :=
          ih _ s (ibAnn (ibOfBvn w)) ak pa n s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LInstr none
            (some (ibAnn (ibOfBvn w))) none kpos _ hrtc
            ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl, hns⟩
      all_goals first
        | (simp [execEff] at hex; done)
        | (simp only [execEff] at hex
           simp only [WeakEvLang.noSfAnn] at hsf
           obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee, hrtc, hns⟩ :=
             ih _ s ib ak pa n s' es hn hex hsf cpu kpos row
           exact ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, hmem, hee,
             AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none none none kpos _
               hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial, hns⟩)

/-- THE PEEL (write target): the write twin of `afAdminRunToMemread` — the first effect is the
plain RAM write `.WEwrite ak pa n v`; the node's request carries `value = some v`. -/
theorem afAdminRunToMemwrite (m : SailM Unit) :
    ∀ (s : ExecSt) (ib : Ibch) (ak : AkInfo) (pa : PAddr) (n : Nat) (v : BitVec (8 * n))
      (s' : ExecSt) (es : List Weff),
      n ≠ 0 →
      execEff m s = some ((), s', .WEwrite ak pa n v :: es) →
      WeakEvLang.noSfAnn m s →
      ∀ (cpu : CPU) (kpos : Nat) (row : List Lbl),
        ∃ (s2 : ExecSt) (ib2 : Ibch) (va : Nat)
          (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
          (KK : Result (Option Bool) Arch.abort → SailM Unit),
          classify req.access_kind = ak ∧ req.pa = pa ∧ req.value = some v ∧
          devAddr pa = false ∧ s2.mem = s.mem ∧
          execEff (.impure (.ok (.memWrite n va req)) KK) s2 =
            some ((), s', .WEwrite ak pa n v :: es) ∧
          rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
            ⟨.PHart cpu m s.regs none ib, kpos⟩
            ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) s2.regs none ib2, kpos⟩ := by
  induction m with
  | pure y =>
    intro s ib ak pa n v s' es _ hex
    simp [execEff] at hex
  | impure call k ih =>
    intro s ib ak pa n v s' es hn hex hsf cpu kpos row
    cases call with
    | error e => simp [execEff] at hex
    | ok o =>
      cases o
      case memRead n0 va req =>
        simp only [execEff] at hex
        by_cases hm : mmioAcc req.pa n0 = true
        · rw [if_pos hm] at hex
          have hdevT : devAddr req.pa = true := by
            simp only [mmioAcc, Bool.and_eq_true] at hm; exact hm.1
          cases hdr : devRead s.dev req.pa n0 with
          | none => simp only [hdr] at hex; cases hex
          | some p =>
            obtain ⟨w0, d0⟩ := p
            simp only [hdr] at hex
            simp only [WeakEvLang.noSfAnn, if_pos hm, hdr] at hsf
            obtain ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc⟩ :=
              ih _ (s.setDev d0) ib ak pa n v s' es hn hex hsf cpu kpos row
            refine ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, ?_⟩
            refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0 .LDev none none none kpos _
              hrtc ?_ trivial
            simp only [pnodeStep, hdevT, ↓reduceIte]
            exact ⟨w0, by simp [hdr]⟩
        · rw [if_neg hm] at hex
          cases hrb : bmRead s.mem req.pa n0 with
          | none => simp only [hrb] at hex; cases hex
          | some w0 =>
            simp only [hrb] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            simp at hcons
      case memWrite n0 va req =>
        have hex0 := hex
        simp only [execEff] at hex
        cases hv : req.value with
        | none => simp only [hv] at hex; cases hex
        | some w =>
          simp only [hv] at hex
          by_cases hm : mmioAcc req.pa n0 = true
          · rw [if_pos hm] at hex
            have hdevT : devAddr req.pa = true := by
              simp only [mmioAcc, Bool.and_eq_true] at hm; exact hm.1
            cases hdw : devWrite s.dev req.pa n0 w with
            | none => simp only [hdw] at hex; cases hex
            | some d0 =>
              simp only [hdw] at hex
              simp only [WeakEvLang.noSfAnn, hv, if_pos hm, hdw] at hsf
              obtain ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc⟩ :=
                ih _ (s.setDev d0) ib ak pa n v s' es hn hex hsf cpu kpos row
              refine ⟨s2, ib2, va2, req2, KK, hcl, hpa, hval, hdev, hmem, hee, ?_⟩
              refine AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev d0 .LDev none none none kpos
                _ hrtc ?_ trivial
              simp only [pnodeStep, hdevT, hv, ↓reduceIte]
              simp [hdw]
          · rw [if_neg hm] at hex
            obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
            simp only [List.cons.injEq] at hcons
            obtain ⟨he, rfl⟩ := hcons
            injection he with hak hpa hnn hvv
            subst hnn
            have hvv' : v = w := eq_of_heq hvv
            subst hvv'
            have hdevF : devAddr req.pa = false := by
              cases hd : devAddr req.pa
              · rfl
              · simp [mmioAcc, hd, hn] at hm
            exact ⟨s, ib, va, req, k, hak.symm, hpa.symm, hv, hpa ▸ hdevF, rfl, hex0,
              rtc_refl _⟩
      case barrier b =>
        simp only [execEff] at hex
        obtain ⟨es0, _, hcons⟩ := Weff.consEqSome.1 hex
        simp at hcons
      case regRead r =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc⟩ :=
          ih _ s (ibRd ib r) ak pa n v s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none (some (ibRd ib r))
            none kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial⟩
      case regWrite r v0 =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc⟩ :=
          ih _ (s.setReg r v0) ib ak pa n v s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev
            (erwLabel (erwOf (depsOfIb ib.ibBits) ib.ibRds r)) (some (s.regs.set r v0)) none none
            kpos _ hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (erwLabelLbAdmin _)⟩
      case instrAnnounce nw w =>
        simp only [execEff] at hex
        simp only [WeakEvLang.noSfAnn] at hsf
        obtain ⟨hsw, hsf⟩ := hsf
        obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc⟩ :=
          ih _ s (ibAnn (ibOfBvn w)) ak pa n v s' es hn hex hsf cpu kpos row
        exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
          AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LInstr none
            (some (ibAnn (ibOfBvn w))) none kpos _ hrtc
            ⟨(annLabelNot hsw).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl⟩
      all_goals first
        | (simp [execEff] at hex; done)
        | (simp only [execEff] at hex
           simp only [WeakEvLang.noSfAnn] at hsf
           obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee, hrtc⟩ :=
             ih _ s ib ak pa n v s' es hn hex hsf cpu kpos row
           exact ⟨s2, ib2, va, req, KK, hcl, hpa, hval, hdev, hmem, hee,
             AxFetch1.admPrepend row cpu _ _ s.regs ib s.dev s.dev .LSilent none none none kpos _
               hrtc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ trivial⟩)

/-- The write twin of `AxOpsem.pnodeStepReadAny`: the plain-store arm of `pnodeStep`. -/
theorem afPnodeStepWriteAny (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch)
    (d : DevStates) (v : BitVec (8 * n)) :
    devAddr req.pa = false → n ≠ 0 → (classify req.access_kind).akLatest = false →
    req.value = some v →
    pnodeStep (.impure (.ok (.memWrite n va req)) KK) rs ib d
      (LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (KK (.Ok (some true))) none none d none none := by
  intro hdev hn hlat hv
  simp [pnodeStep, hdev, hv, hn, hlat]

/-- … at the `pstepProg` level (no parked fence). -/
theorem afPstepProgWriteAny (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (v : BitVec (8 * n)) :
    devAddr req.pa = false → n ≠ 0 → (classify req.access_kind).akLatest = false →
    req.value = some v →
    pstepProg (.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib) d
      (LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      (.PHart cpu (KK (.Ok (some true))) rs none ib) d :=
  fun hdev hn hlat hv =>
    ⟨rfl, none, none, none, rfl, rfl,
      afPnodeStepWriteAny n va req KK rs ib d.efDev v hdev hn hlat hv, rfl⟩

/-- … and the plain read at the `pstepProg` level (deviation 4: `akIfetch = false`). -/
theorem afPstepProgReadAny (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (vs : List (BitVec 8)) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
    (classify req.access_kind).akLatest = false → vs.length = n →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d
      (LLoad (classify req.access_kind).akSync false (paZ req.pa) (tagVals vs) [])
      (.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib) d := by
  intro hdev hfe hlat hlen
  have h := pnodeStepReadAny n va req KK rs ib d.efDev vs hdev hlen
  rw [hfe, hlat] at h
  exact ⟨rfl, none, none, none, rfl, rfl, h, rfl⟩

/-- (Lean-only) THE FETCH NODE's program step: a RAM `memRead` with `akIfetch = true` steps with
the i-cache label `LIFetch` (any byte list of the width; Stage C). -/
theorem AxFetch1.pstepProgFetchAny (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (vs : List (BitVec 8)) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = true → vs.length = n →
    pstepProg (.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib) d
      (LIFetch (paZ req.pa) (tagVals vs))
      (.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib) d := by
  intro hdev hfe hlen
  have h := pnodeStepReadAny n va req KK rs ib d.efDev vs hdev hlen
  rw [hfe] at h
  exact ⟨rfl, none, none, none, rfl, rfl, h, rfl⟩

/-- THE DATA EVENT OF A LOAD, generic: an `areadStep` realizing the row's data item from a hart
sitting at a plain `memRead` node. -/
theorem afAreadStepOfMemread (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (k : Nat) (lb : Lbl) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = false →
    (classify req.access_kind).akLatest = false →
    row[k]? = some lb →
    aident lb = .IRead (classify req.access_kind).akSync (paZ req.pa) n →
    areadStep row ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩
      (.IRead (classify req.access_kind).akSync (paZ req.pa) n)
      (fun vs => ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib, k + 1⟩) := by
  intro hdev hfe hlat hrow hid
  refine ⟨lb, hrow, hid, rfl, fun vs hvs => ?_⟩
  refine ⟨LLoad (classify req.access_kind).akSync false (paZ req.pa) (tagVals vs) [], d, d,
    ?_, tagValsSnd vs, afPstepProgReadAny cpu n va req KK rs ib d vs hdev hfe hlat hvs, rfl⟩
  simp only [wlRd, aidentRd, tagValsLength]
  rw [hvs]; rfl

/-- THE FETCH, generic (O2 Stage C, deviation 2): from a hart at a RAM `memRead` node with
`akIfetch = true`, ONE administrative opax step (`AStepAdmin` at `lbAdmin true (LIFetch ..)`)
that KEEPS the row position — no row item, no identity, no oracle. -/
theorem afAstepFetchOfMemread (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (d : Efab) (k : Nat) (vs : List (BitVec 8)) :
    devAddr req.pa = false → (classify req.access_kind).akIfetch = true → vs.length = n →
    AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩
      (LIFetch (paZ req.pa) (tagVals vs))
      ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs none ib, k⟩ :=
  fun hdev hfe hlen =>
    .AStepAdmin _ k d _ _ d rfl (AxFetch1.pstepProgFetchAny cpu n va req KK rs ib d vs hdev hfe hlen)

/-- THE DATA EVENT OF A STORE, generic: an `AStepWrite` realizing the row's data item from a
hart sitting at a plain `memWrite` node. -/
theorem afAstepWriteOfMemwrite (row : List Lbl) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (k : Nat) (lb : Lbl) (v : BitVec (8 * n)) :
    devAddr req.pa = false → n ≠ 0 → (classify req.access_kind).akLatest = false →
    req.value = some v →
    row[k]? = some lb →
    aident lb = .IWrite (classify req.access_kind).akSync (paZ req.pa) n →
    lblData lb = some (WeakInterpProj.wbytes n v) →
    AxOpsem.astepProg row ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩
      (LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
        (depsAsrc (depsOfIb ib.ibBits)) (depsVsrc (depsOfIb ib.ibBits)))
      ⟨.PHart cpu (KK (.Ok (some true))) rs none ib, k + 1⟩ := by
  intro hdev hn hlat hv hrow hid hdat
  refine .AStepWrite _ k d _ lb _ d hrow rfl ?_ ?_
    (afPstepProgWriteAny cpu n va req KK rs ib d v hdev hn hlat hv)
  · rw [hid]; simp only [wlWr, aidentWr, wbytesLength]
  · rw [hdat]; rfl

/-! ### 2.1 THE ld8 INSTANTIATION (the data-event half): the REAL `execute (LOAD …)` term

`WeakLeafLd8.execEffLd8At` gives the `execute` term's `execEff` fact (singleton trace
`[.WEread wakPlain ea 8]`); bind-embedding it into `SailM Unit` (`>>= fun _ => pure ()`) keeps the
trace, which is `afAdminRunToMemread`'s hypothesis shape; its admin run composed with
`afAreadStepOfMemread` gives the row's data-event `areadStep` on the actual Sail term. -/

/-- (Lean-only, Q10) `WeakLeafLd8.execEffLd8At`'s `noSfAnn` twin: the LOAD's run announces no
sfence word (the same script, `WeakFetchEff.noSfAnnExecuteLOAD8Gpr` at the end). -/
theorem AxFetch1.noSfAnnLd8At (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (rs1 rd : BitVec 5) (imm : BitVec 12)
    (ea : PAddr) (v : BitVec 64) :
    rd.toNat ≠ 0 →
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    BytesAt s0 ea 8 v →
    WeakEvLang.noSfAnn (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))) ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)) := by
  intro hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal hram hbytes
  -- every config register, moved past the funnel's two pre-writes
  have lpriv_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .cur_privilege = .Machine := by
    leaf_peel .cur_privilege; exact lpriv
  have lms_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .mstatus = s0.regs .mstatus := by
    leaf_peel .mstatus
  have lsec_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .mseccfg = s0.regs .mseccfg := by
    leaf_peel .mseccfg
  have lpmpc_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .pmpcfg_n = s0.regs .pmpcfg_n := by
    leaf_peel .pmpcfg_n
  have lpma_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .pma_regions = s0.regs .pma_regions := by
    leaf_peel .pma_regions
  have lhtif_s : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
      .htif_tohost_base = none := by
    leaf_peel .htif_tohost_base; exact lhtif
  -- the base register
  have hbase : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).gpr rs1 =
      s0.gpr rs1 :=
    uxaXget_congr _ _ (fun r hr => by
      rw [setLookupNe r .nextPC _ _ (WeakLeafLd8.gprsNe r hr).2,
        setLookupNe r .minstret_increment _ _ (WeakLeafLd8.gprsNe r hr).1]) rs1
  have hea' : ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).gpr rs1 +
      sign_extend (m := 64) imm = ea := by rw [hbase]; exact hea
  exact WeakFetchEff.noSfAnnExecuteLOAD8Gpr rs1 rd imm v ramRegion
    ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)) hrd lpriv_s
    (by rw [lms_s]; exact lmprv) (by rw [lsec_s]; exact lpmm) (by rw [hea']; exact hal)
    (by
      rw [hea']
      exact execEffPmpCheckMachineNone _ 8 _ _ (fun i => by rw [lpmpc_s]; exact (lpmp i).1))
    (by rw [lpma_s, lpma, hea']; exact matching_pma_ram ea 8 hram (by decide) (by decide))
    (by rw [hea']; exact hal)
    (by first | rfl | decide +kernel)
    (by rw [hea', within_clint_ram ea 8 hram]; rfl)
    (by
      first
      | rfl
      | (simp only [within_sig, plat_have_sig, Functions.not]; rfl))
    (by rw [hea']; exact execEffWithinHtifFalse _ 8 _ lhtif_s)
    (by rw [hea']; exact devAddrRam ea 8 hram)
    (by rw [hea']; exact hbytes)


theorem afLd8RunToRead (s0 : ExecSt) (b : Bool) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (ea : PAddr) (v : BitVec 64) (cpu : CPU) (row : List Lbl) (ib : Ibch)
    (k : Nat) (lb : Lbl) :
    rd.toNat ≠ 0 →
    s0.regs .cur_privilege = .Machine →
    (_get_Mstatus_MPRV (s0.regs .mstatus) == 1#1) = false →
    pmm_mode_backwards (_get_Seccfg_PMM (s0.regs .mseccfg)) = .PMM_Disabled →
    pmpAllOff (s0.regs .pmpcfg_n) →
    s0.regs .pma_regions = bootPMA →
    s0.regs .htif_tohost_base = none →
    s0.gpr rs1 + sign_extend (m := 64) imm = ea →
    is_aligned_paddr (.Physaddr ea) 8 = true →
    inRam ea 8 →
    BytesAt s0 ea 8 v →
    row[k]? = some lb →
    aident lb = .IRead false (paZ ea) 8 →
    ∃ (s2 : ExecSt) (ib2 : Ibch) (va : Nat)
      (req : Mem_read_request 8 va Arch.pa Arch.translation Arch.arch_ak)
      (KK : Result (BitVec (8 * 8) × Option Bool) Arch.abort → SailM Unit),
      classify req.access_kind = wakPlain ∧ req.pa = ea ∧
      rtc (fun t1 t2 => ∃ l, AxOpsem.astepProg row t1 l t2)
        ⟨.PHart cpu (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) >>= fun _ => pure ())
          ((s0.setReg .minstret_increment b).setReg .nextPC (Sail.BitVec.addInt pc 4)).regs
          none ib, k⟩
        ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) s2.regs none ib2, k⟩ ∧
      areadStep row ⟨.PHart cpu (.impure (.ok (.memRead 8 va req)) KK) s2.regs none ib2, k⟩
        (.IRead (classify req.access_kind).akSync (paZ req.pa) 8)
        (fun vs => ⟨.PHart cpu (KK (.Ok (wordOfBytes 8 vs, none))) s2.regs none ib2, k + 1⟩) := by
  intro hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal hram hbytes hrow hid
  have hm0 := execEffLd8At s0 b pc rs1 rd imm ea v hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal
    hram hbytes
  -- Q10: the run is sfence-free (the LOAD's twin, then the `pure ()`)
  have hsf := WeakEffSkel.noSfAnnBind _ (fun _ : ExecutionResult => (pure () : SailM Unit)) _ _ _ _ hm0
    (AxFetch1.noSfAnnLd8At s0 b pc rs1 rd imm ea v hrd lpriv lmprv lpmm lpmp lpma lhtif hea hal
      hram hbytes) trivial
  have hex := execEffBind _ (fun _ : ExecutionResult => (pure () : SailM Unit)) _ _ _ _ () _ []
    hm0 rfl
  rw [List.append_nil] at hex
  obtain ⟨s2, ib2, va, req, KK, hcl, hpa, hdev, _, _, hrtc, -⟩ :=
    afAdminRunToMemread _ _ ib wakPlain ea 8 _ [] (by decide) hex hsf cpu k row
  refine ⟨s2, ib2, va, req, KK, hcl, hpa, hrtc, ?_⟩
  exact afAreadStepOfMemread row cpu 8 va req KK s2.regs ib2 (efInit s2.dev) k lb
    (by rw [hpa]; exact hdev) (by rw [hcl]; rfl) (by rw [hcl]; rfl) hrow
    (by rw [hid, hcl, hpa]; rfl)

end Weak
