/-
Weak: **W13 (W), increment 2 — the reflective hart runner and `xv6ConfS`'s Bool twin** (plan
`notes/weak-allocproc-plan.md` rev 45, §C top THIRD LAUNCH SET "W13 (W)": W13-wit and [R38.s1]'s
computed satisfiability check; [R41.4]/[R41.s6]).  The concrete witness is `Weak/W13Wit.lean`.

Lean-only, no Rocq twin.

  §1  **`W13Wit.runRow`** — a COMPUTABLE stepper of one hart's Sail monad (kernel-evaluated, the
      way `SrvwmoXv6Witness`'s `esil` stretches are, but over whole blocks and with no register
      footprint): the boundary at tick `false`, register traffic from the register file, the
      announce, fetches answered by the image at timestamp 0 (`W13Wit.admNode`); at an event node a
      plain RAM load answered by the row's own stores over the image, a plain RAM store, or an
      MMIO store through the fabric's `devWrite` (`W13Wit.evNode`).  Blocks (administrative stretch
      + one event) until the first MMIO store, which ends the row; the tagged dependency fold
      `dstepT` and the view state `lblPost` are threaded along, so the run hands back the row and
      `rowDepsT` of its emission without the (≈ 10⁴-item) emission itself.
  §2  **`W13Wit.runRowSound`** — a successful run IS an emission (`hemitf`) from the cursor, at a
      constant fabric but for the last (I/O) block, its contact bit set exactly there, its tagged
      deps the run's, every fetch item pinned (`WeakAxRealize.fetchPin`).  Node-level lemmas:
      `W13Wit.admNodeSound` (an administrative, fabric-preserving `pstepEv` step),
      `W13Wit.admRunSound` (an `admRunT` run with contact bit `false`, emitting no tagged edge),
      `W13Wit.evNodeSound` (a realizing `pstepEv` step; `pdevEv` = "is `LDev`").
  §3  **`xv6ConfSB`** — `xv6ConfS`'s BOOL TWIN [R38.s1]: the decidable clauses of the device-active
      tagged conformance (row count; `gfDev` duplicate-free and in range; per row, membership by
      contact and the tagged dependency clause, over a per-row certificate `GfRowCert` = the run's
      `rowDepsT`, contact bits and moved flags) AND the tagged model's well-formedness `gtdepsWfB`
      over the same edges.  **`xv6ConfSBSound`**: with each row's run facts (an emission whose deps,
      contact bits and moved flags are the certificate's, fetches pinned, members' endpoints on
      the fabric trace — what `runRowSound` supplies), a `true` twin gives `xv6ConfS` and
      `gtdepsWf`.
  §4  **W5d-G G6-2 — the Zifencei twin** `xv6ConfSZB` = `xv6ConfSB` ∧ `emFetchUnwrittenB` (every
      byte the graph writes lies OFF the run's FETCH image, e.g. the kernel text); its soundness
      **`xv6ConfSZBSound`** gives `xv6ConfSZ` (`Weak/GraphFabConf.lean` §2′) when each row's
      fetches are pinned to that sub-image of the graph's image (the slot by
      `GraphFetch.emZifOfPinC`, the stored fragment by `GraphFetch.emFetchInOfUnwritten`).  Both
      soundness theorems go through `W13Wit.confSBRows`, the twin's soundness at any fetch slot.

**Trust.**  Nothing is trusted beyond the kernel: the runner is evaluated by `decide +kernel` and
linked to `pstepEv` by the proofs above (no `native_decide`, unlike `vtest-lean`).  The runner
only ever chooses: tick `false` at each boundary, the image at timestamp 0 for fetches, the
sequential value for loads — choices the LTS allows; a wrong choice makes a run fail, it cannot
make one succeed with a false row.

**Deviations from the plan text.**  (1) The plan's "kernel evaluation on W5c's `esilAdmRun`":
`esilAdmRun` is per stretch and needs a register footprint and an unevaluated cursor per
instruction (`SrvwmoXv6Witness` §3); for a ≈ 10⁴-node run the runner here is the same reflection
one level up (whole blocks, one kernel evaluation, register file answered directly), its soundness
proved once; `SrvwmoXv6Witness.pstepEvNode`/`boundaryPstep`/`erwLabelAdm`/`fetchPinNf` are reused.
(2) The Bool twin checks the decidable clauses over a run CERTIFICATE (`GfRowCert`); the run facts
(`hartConff`, the fabric pins) are its soundness theorem's hypothesis — on W13-wit they come from
`runRowSound`.  (3) [W5d-G G6-2] The runner takes TWO images: loads are answered over `img`, fetches
from `imgF` (a fetch whose bytes `imgF` lacks makes the run fail); `runRowSound`'s pins are to
`imgF`.  W13-wit passes the boot image and its kernel-text restriction, so the run itself
certifies that every fetch reads kernel text — what `emFetchUnwrittenB` needs (the plan's
`xv6ConfSZBSound` "through `xv6ConfSBSound` + `xv6ConfSZOfPin`" would need the unwritten fact for
EVERY emission of a row; the shared `confSBRows` keeps the run's own emission instead).

**Name map.**  None (Lean-only).  Lean-only names: `GfRowCert`, `gfRowCertOk`, `xv6ConfSB`,
`xv6ConfSBSound`, `emFetchUnwrittenB`, `emFetchUnwrittenBSound`, `xv6ConfSZB`, `xv6ConfSZBSound`;
helpers file-qualified `W13Wit.*`.
-/
import Weak.SrvwmoXv6Witness
import Weak.GraphFabConf

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! # 1. The runner (computable; evaluated by the kernel) -/

/-- The hart's cursor: the residual monad, the register file, the announced-bits accumulator
(the parked fence is `none` throughout: the runner never steps a barrier). -/
structure W13Wit.Hs where
  hm : SailM Unit
  hrs : RegFile
  hib : Ibch

/-- The program state of a cursor. -/
def W13Wit.pex (c : CPU) (h : W13Wit.Hs) : Pexv6 := .PHart c h.hm h.hrs none h.hib

/-- The boot image, COMPUTABLY (`bootImage` is sealed; `W13Wit.imfEq`). -/
def W13Wit.imf : Image := fun z => if inRam (zPa z) 1 then some (bootByte (zPa z).toNat) else none

theorem W13Wit.imfEq : imgZ bootImage = W13Wit.imf := by
  funext z
  simp only [imgZ, W13Wit.imf, bootImage_get?]

/-- The little-endian value of a byte list. -/
def W13Wit.leNat : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * W13Wit.leNat bs

/-- The per-byte answer of an `n`-byte access answered by the word `w`, byte `j` stamped
`ts j`. -/
def W13Wit.tvsOf (n : Nat) (w : BitVec (8 * n)) (ts : Nat → Nat) : List (Nat × BitVec 8) :=
  (List.range' 0 n).map (fun j => (ts j, nthByte w j))

/-- The fetched word: the image's bytes at `base`. -/
def W13Wit.fetchW (img : Image) (base : Int) (n : Nat) : BitVec (8 * n) :=
  BitVec.ofNat (8 * n) (W13Wit.leNat ((List.range' 0 n).map (fun j => (img (base + j)).getD 0)))

/-- `WeakAxRealize.fetchPin`, as a `Bool`. -/
def W13Wit.fetchPinB (img : Image) (l : Wlabel) : Bool :=
  match l with
  | .LIFetch base tvs =>
      tvs.all (fun x => decide (x.1 = 0)) &&
      (List.range' 0 tvs.length).all (fun j => decide (img (base + (j : Int)) = (tvs.map Prod.snd)[j]?))
  | _ => true

/-- One ADMINISTRATIVE node (the boundary at tick `false`, register traffic, the announce, a
fetch answered by the image, the label-free nodes). -/
noncomputable def W13Wit.admNode (img : Image) (h : W13Wit.Hs) : Option (Wlabel × W13Wit.Hs) :=
  match h.hm with
  | .pure _ => some (.LInstr, ⟨riscvStep false, h.hrs, ibNone⟩)
  | .impure (.error _) _ => none
  | .impure (.ok o) k =>
    match o, k with
    | .regRead r, k => some (.LSilent, ⟨k (h.hrs r), h.hrs, ibRd h.hib r⟩)
    | .regWrite r v, k =>
        some (erwLabel (erwOf (depsOfIb h.hib.ibBits) h.hib.ibRds r), ⟨k PUnit.unit, h.hrs.set r v, h.hib⟩)
    | .memRead n _ req, k =>
        if !devAddr req.pa && (classify req.access_kind).akIfetch then
          if W13Wit.fetchPinB img
              (.LIFetch (paZ req.pa) (W13Wit.tvsOf n (W13Wit.fetchW img (paZ req.pa) n) (fun _ => 0)))
          then
            some (.LIFetch (paZ req.pa) (W13Wit.tvsOf n (W13Wit.fetchW img (paZ req.pa) n) (fun _ => 0)),
              ⟨k (.Ok (W13Wit.fetchW img (paZ req.pa) n, none)), h.hrs, h.hib⟩)
          else none
        else none
    | .instrAnnounce n w, k =>
        if sfAnnB n w then none else some (annLabel n w, ⟨k (), h.hrs, ibAnn (ibOfBvn w)⟩)
    | .branchAnnounce _ _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .cacheOp _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .tlbi _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .takeException _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .returnException _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .translationStart _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .translationEnd _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .cycleCount, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .message _, k => some (.LSilent, ⟨k (), h.hrs, h.hib⟩)
    | .getCycleCount, k => some (.LSilent, ⟨k (0 : Nat), h.hrs, h.hib⟩)
    | _, _ => none

/-- The head node is a memory EVENT (a data read, or any write). -/
def W13Wit.isEv (m : SailM Unit) : Bool :=
  match m with
  | .impure (.ok (.memRead _ _ req)) _ => devAddr req.pa || !(classify req.access_kind).akIfetch
  | .impure (.ok (.memWrite _ _ _)) _ => true
  | _ => false

/-- The runner's memory: the row's own stores, newest first, per byte (address, write index,
byte); the image below them at index 0. -/
abbrev W13Wit.Mm : Type := List (Int × Nat × BitVec 8)

def W13Wit.memAt (img : Image) (mm : W13Wit.Mm) (a : Int) : Nat × BitVec 8 :=
  match mm.find? (fun e => decide (e.1 = a)) with
  | some e => e.2
  | none => (0, (img a).getD 0)

/-- One memory EVENT: a plain RAM load (answered by the row's memory), a plain RAM store, an
MMIO store (the fabric's `devWrite`). -/
def W13Wit.evNode (img : Image) (mm : W13Wit.Mm) (nw : Nat) (h : W13Wit.Hs) (d : Efab) :
    Option (Wlabel × W13Wit.Hs × Efab × W13Wit.Mm × Nat) :=
  match h.hm with
  | .impure (.ok o) k =>
    match o, k with
    | .memRead n _ req, k =>
        if devAddr req.pa || (classify req.access_kind).akIfetch ||
            (classify req.access_kind).akLatest then none
        else
          some (.LLoad (classify req.access_kind).akSync false (paZ req.pa)
              (W13Wit.tvsOf n
                (BitVec.ofNat (8 * n) (W13Wit.leNat
                  ((List.range' 0 n).map (fun j => (W13Wit.memAt img mm (paZ req.pa + j)).2))))
                (fun j => (W13Wit.memAt img mm (paZ req.pa + j)).1)) [],
            ⟨k (.Ok (BitVec.ofNat (8 * n) (W13Wit.leNat
                  ((List.range' 0 n).map (fun j => (W13Wit.memAt img mm (paZ req.pa + j)).2))),
                none)), h.hrs, h.hib⟩, d, mm, nw)
    | .memWrite n _ req, k =>
        match req.value with
        | none => none
        | some v =>
          if devAddr req.pa then
            match devWrite d.efDev req.pa n v with
            | some ds' =>
                some (.LDev .wr (paZ req.pa) (WeakInterpProj.wbytes n v)
                    (depsAsrc (depsOfIb h.hib.ibBits)) (depsVsrc (depsOfIb h.hib.ibBits)),
                  ⟨k (.Ok (some true)), h.hrs, h.hib⟩, { d with efDev := ds' }, mm, nw)
            | none => none
          else if n = 0 || (classify req.access_kind).akLatest then none
          else
            some (.LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
                (depsAsrc (depsOfIb h.hib.ibBits)) (depsVsrc (depsOfIb h.hib.ibBits)),
              ⟨k (.Ok (some true)), h.hrs, h.hib⟩, d,
              ((List.range' 0 n).map (fun j =>
                (paZ req.pa + (j : Int), nw + 1, (WeakInterpProj.wbytes n v)[j]?.getD 0))).reverse ++ mm,
              nw + 1)
    | _, _ => none
  | _ => none

/-- An I/O (fabric) label. -/
def W13Wit.isDevB (l : Wlabel) : Bool :=
  match l with
  | .LDev .. => true
  | _ => false

/-- The administrative stretch up to the next event node, folding the tagged dependency state. -/
noncomputable def W13Wit.admRun (img : Image) : Nat → W13Wit.Hs → DstateT → Option (W13Wit.Hs × DstateT)
  | 0, _, _ => none
  | f + 1, h, dt =>
    if W13Wit.isEv h.hm then some (h, dt)
    else
      match W13Wit.admNode img h with
      | some (l, h') => W13Wit.admRun img f h' (dstepT dt (l, none)).1
      | none => none

/-- What a row run hands back: the row, its tagged deps (`rowDepsT` of the emission), the fabric
after the last block (the row's one I/O event; every earlier block keeps the fabric), and the final
cursor. -/
structure W13Wit.Out where
  oRow : List Lbl
  oDeps : List Redge
  oDfin : Efab
  oFin : W13Wit.Hs

/-- THE ROW RUNNER: blocks (administrative stretch + one event) until the first I/O event,
which ends the row; loads over `img`, fetches from `imgF` (header, deviation 3).  A non-I/O event keeps the fabric (`W13Wit.evNodeSound`), so the recursion
carries `d` unchanged. -/
noncomputable def W13Wit.runRow (c : CPU) (img imgF : Image) (fa : Nat) :
    Nat → Nat → W13Wit.Hs → Wstate → DstateT → W13Wit.Mm → Nat → Efab → Option W13Wit.Out
  | 0, _, _, _, _, _, _, _ => none
  | fe + 1, k, h, ws, dt, mm, nw, d =>
    match W13Wit.admRun imgF fa h dt with
    | none => none
    | some (ha, dta) =>
      match W13Wit.evNode img mm nw ha d with
      | none => none
      | some (l, hb, d', mm', nw') =>
        match projLbl (pclsEv (W13Wit.pex c ha) l ws) l with
        | none => none
        | some lb =>
          if W13Wit.isDevB l then
            some ⟨[lb], (dstepT dta (l, some k)).2, d', hb⟩
          else
            match W13Wit.runRow c img imgF fa fe (k + 1) hb (lblPost k ws lb) (dstepT dta (l, some k)).1
                mm' nw' d with
            | none => none
            | some o => some ⟨lb :: o.oRow, (dstepT dta (l, some k)).2 ++ o.oDeps, o.oDfin, o.oFin⟩

/-! # 2. The runner's soundness -/

theorem W13Wit.tvsOfLen (n : Nat) (w : BitVec (8 * n)) (ts : Nat → Nat) :
    (W13Wit.tvsOf n w ts).length = n := by
  simp [W13Wit.tvsOf]

theorem W13Wit.tvsOfSnd (n : Nat) (w : BitVec (8 * n)) (ts : Nat → Nat) :
    ∀ j : Nat, j < n → ((W13Wit.tvsOf n w ts).map Prod.snd)[j]? = some (nthByte w j) := by
  intro j hj
  simp [W13Wit.tvsOf, hj]

theorem W13Wit.fetchPinBSound (img : Image) (l : Wlabel) :
    W13Wit.fetchPinB img l = true → WeakAxRealize.fetchPin img l := by
  intro h
  cases l with
  | LIFetch base tvs =>
    simp only [W13Wit.fetchPinB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun t ht => ?_, fun j hj => h2 j (by simp [List.mem_range'_1, hj])⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
    exact h1 x hx
  | _ => trivial

/-- A hart node step that moves the device vector (the MMIO arm). -/
theorem W13Wit.pstepEvNodeDev (c : CPU) (m m' : SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (ds' : DevStates) (l : Wlabel) :
    pnodeStep m rs ib d.efDev l m' none none ds' none none →
    pstepEv (.PHart c m rs none ib) d l (.PHart c m' rs none ib) { d with efDev := ds' } :=
  fun h => ⟨rfl, none, none, none, rfl, rfl, Or.inl ⟨h, rfl⟩⟩

/-- An item without a row position emits no tagged edge. -/
theorem W13Wit.dstepTNone (s : DstateT) (l : Wlabel) : (dstepT s (l, none)).2 = [] := by
  cases l with
  | LDev kd _ _ _ _ => cases kd <;> rfl
  | _ => rfl

/-- ONE ADMINISTRATIVE NODE IS ONE ADMINISTRATIVE HART STEP, fabric-preserving, its fetch (if
any) pinned to the image. -/
theorem W13Wit.admNodeSound (c : CPU) (img : Image) (d : Efab) (h : W13Wit.Hs) (l : Wlabel)
    (h' : W13Wit.Hs) :
    W13Wit.admNode img h = some (l, h') →
    lbAdmin true l ∧ pstepEv (W13Wit.pex c h) d l (W13Wit.pex c h') d ∧
      WeakAxRealize.fetchPin img l := by
  obtain ⟨m, rs, ib⟩ := h
  intro hn
  simp only [W13Wit.pex]
  match m, hn with
  | .pure u, hn =>
    simp only [W13Wit.admNode, Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨rfl, SrvwmoXv6Witness.boundaryPstep c u rs ib d, trivial⟩
  | .impure (.error _) _, hn => simp [W13Wit.admNode] at hn
  | .impure (.ok o) k, hn =>
    cases o with
    | regRead r =>
      simp only [W13Wit.admNode, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact ⟨trivial, SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib _ d _ none (some (ibRd ib r))
        (by simp [pnodeStep]) rfl rfl, trivial⟩
    | regWrite r v =>
      simp only [W13Wit.admNode, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨ha, hf⟩ := SrvwmoXv6Witness.erwLabelAdm (erwOf (depsOfIb ib.ibBits) ib.ibRds r)
      exact ⟨ha, SrvwmoXv6Witness.pstepEvNode c _ _ rs _ ib ib d _ (some (rs.set r v)) none
        (by simp [pnodeStep]) rfl rfl, SrvwmoXv6Witness.fetchPinNf img _ hf⟩
    | memRead n va req =>
      simp only [W13Wit.admNode] at hn
      split at hn
      · rename_i hc
        split at hn
        · rename_i hpin
          simp only [Option.some.injEq, Prod.mk.injEq] at hn
          obtain ⟨rfl, rfl⟩ := hn
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          obtain ⟨hdev, hif⟩ := hc
          refine ⟨rfl, SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none ?_ rfl rfl,
            W13Wit.fetchPinBSound _ _ hpin⟩
          dsimp only [pnodeStep]
          rw [if_neg (by simp [hdev])]
          exact Or.inl ⟨hif, W13Wit.fetchW img (paZ req.pa) n,
            W13Wit.tvsOf n (W13Wit.fetchW img (paZ req.pa) n) (fun _ => 0), W13Wit.tvsOfLen _ _ _,
            W13Wit.tvsOfSnd _ _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · simp at hn
      · simp at hn
    | instrAnnounce n w =>
      simp only [W13Wit.admNode] at hn
      split at hn
      · simp at hn
      · rename_i hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        have hs' : sfAnnB n w = false := by simpa using hs
        refine ⟨by rw [annLabelNot hs']; trivial,
          SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib _ d _ none (some (ibAnn (ibOfBvn w)))
            (by simp [pnodeStep]) rfl rfl, by rw [annLabelNot hs']; trivial⟩
    | getCycleCount =>
      simp only [W13Wit.admNode, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact ⟨trivial, SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none
        (by simp [pnodeStep]) rfl rfl, trivial⟩
    | memWrite => simp [W13Wit.admNode] at hn
    | readRam => simp [W13Wit.admNode] at hn
    | writeRam => simp [W13Wit.admNode] at hn
    | barrier => simp [W13Wit.admNode] at hn
    | choose => simp [W13Wit.admNode] at hn
    | _ =>
      simp only [W13Wit.admNode, Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      exact ⟨trivial, SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none
        (by simp [pnodeStep]) rfl rfl, trivial⟩

/-- THE STRETCH IS AN ADMINISTRATIVE RUN (contact-free, fabric-preserving, fetches pinned), and
its items emit no tagged edge while moving the fold's state to the returned one. -/
theorem W13Wit.admRunSound (c : CPU) (img : Image) :
    ∀ (f : Nat) (h : W13Wit.Hs) (dt : DstateT) (h' : W13Wit.Hs) (dt' : DstateT),
      W13Wit.admRun img f h dt = some (h', dt') → ∀ d : Efab,
      ∃ ls, WeakRvwmoFab.admRunT true (W13Wit.pex c h) d ls (W13Wit.pex c h') d false ∧
        (∀ l, l ∈ ls → WeakAxRealize.fetchPin img l) ∧
        ∀ es, rowDepsTAux dt (eadm ls ++ es) = rowDepsTAux dt' es := by
  intro f
  induction f with
  | zero => intro h dt h' dt' hr; simp [W13Wit.admRun] at hr
  | succ f ih =>
    intro h dt h' dt' hr d
    unfold W13Wit.admRun at hr
    by_cases hev : W13Wit.isEv h.hm = true
    · rw [if_pos hev] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨[], .ATnil _ _, by simp, fun es => rfl⟩
    · rw [if_neg hev] at hr
      rcases hN : W13Wit.admNode img h with _ | ⟨l, h1⟩
      · rw [hN] at hr; cases hr
      rw [hN] at hr
      simp only at hr
      obtain ⟨ha, hs, hfp⟩ := W13Wit.admNodeSound c img d h l h1 hN
      obtain ⟨ls, hrun, hfs, hdeps⟩ := ih h1 _ h' dt' hr d
      have hpd : pdevEv (W13Wit.pex c h) l (W13Wit.pex c h1) = false := by
        rw [GraphFabConf.pdevEvHart _ _ _ rfl]
        exact GraphFabConf.adminNotLDev true l ha
      have hcons := WeakRvwmoFab.admRunT.ATcons _ _ l _ _ ls _ _ false ha hs hrun
      rw [hpd, Bool.or_false] at hcons
      refine ⟨l :: ls, hcons, ?_, fun es => ?_⟩
      · intro l' hl'
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hfp
        · exact hfs l' hl'
      · show rowDepsTAux dt ((l, none) :: (eadm ls ++ es)) = _
        simp only [rowDepsTAux, W13Wit.dstepTNone, List.nil_append]
        exact hdeps es

/-- ONE EVENT NODE IS ONE REALIZING HART STEP: a plain load / plain store keeps the fabric, the
MMIO store is the `LDev` step (its contact bit is "is `LDev`"). -/
theorem W13Wit.evNodeSound (c : CPU) (img : Image) (mm : W13Wit.Mm) (nw : Nat) (h : W13Wit.Hs)
    (d : Efab) (l : Wlabel) (h' : W13Wit.Hs) (d' : Efab) (mm' : W13Wit.Mm) (nw' : Nat) :
    W13Wit.evNode img mm nw h d = some (l, h', d', mm', nw') →
    pstepEv (W13Wit.pex c h) d l (W13Wit.pex c h') d' ∧ lbNobarex l ∧ latFree l ∧
      lbRfoldfree l ∧ (W13Wit.isDevB l = false → d' = d) ∧ (∀ img', WeakAxRealize.fetchPin img' l) ∧
      pdevEv (W13Wit.pex c h) l (W13Wit.pex c h') = W13Wit.isDevB l := by
  obtain ⟨m, rs, ib⟩ := h
  intro hn
  simp only [W13Wit.pex]
  match m, hn with
  | .pure _, hn => simp [W13Wit.evNode] at hn
  | .impure (.error _) _, hn => simp [W13Wit.evNode] at hn
  | .impure (.ok o) k, hn =>
    cases o with
    | memRead n va req =>
      simp only [W13Wit.evNode] at hn
      split at hn
      · simp at hn
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hn
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
        obtain ⟨⟨hdev, hif⟩, hlat⟩ := hc
        refine ⟨SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none ?_ rfl rfl, trivial,
          rfl, rfl, fun _ => rfl, fun _ => trivial, rfl⟩
        dsimp only [pnodeStep]
        rw [if_neg (by simp [hdev])]
        exact Or.inr ⟨hif, Or.inl ⟨hlat, _, _, W13Wit.tvsOfLen _ _ _, W13Wit.tvsOfSnd _ _ _,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    | memWrite n va req =>
      simp only [W13Wit.evNode] at hn
      split at hn
      · simp at hn
      · rename_i v hv
        split at hn
        · rename_i hdev
          split at hn
          · rename_i ds' hdw
            simp only [Option.some.injEq, Prod.mk.injEq] at hn
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hn
            refine ⟨W13Wit.pstepEvNodeDev c _ _ rs ib d ds' _ ?_, trivial, trivial,
              trivial, fun h => by simp [W13Wit.isDevB] at h, fun _ => trivial, rfl⟩
            dsimp only [pnodeStep]
            rw [if_pos hdev, hv]
            exact ⟨hdw, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · simp at hn
        · rename_i hdev
          split at hn
          · simp at hn
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hn
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hn
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hc
            obtain ⟨hn0, hlat⟩ := hc
            have hdev' : devAddr req.pa = false := by simpa using hdev
            refine ⟨SrvwmoXv6Witness.pstepEvNode c _ _ rs rs ib ib d _ none none ?_ rfl rfl,
              trivial, trivial, trivial, fun _ => rfl, fun _ => trivial, rfl⟩
            dsimp only [pnodeStep]
            rw [if_neg (by simp [hdev']), hv]
            exact ⟨hn0, Or.inl ⟨hlat, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    | _ => simp [W13Wit.evNode] at hn

/-- A successful row run has at least one event. -/
theorem W13Wit.runRowNe (c : CPU) (img imgF : Image) (fa : Nat) :
    ∀ (fe k : Nat) (h : W13Wit.Hs) (ws : Wstate) (dt : DstateT) (mm : W13Wit.Mm) (nw : Nat)
      (d : Efab) (o : W13Wit.Out),
      W13Wit.runRow c img imgF fa fe k h ws dt mm nw d = some o → 0 < o.oRow.length := by
  intro fe k h ws dt mm nw d o hr
  cases fe with
  | zero => simp [W13Wit.runRow] at hr
  | succ fe =>
    unfold W13Wit.runRow at hr
    split at hr
    · cases hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · simp only [Option.some.injEq] at hr
            subst hr
            simp
          · split at hr
            · cases hr
            · simp only [Option.some.injEq] at hr
              subst hr
              simp

/-- **THE ROW RUN IS AN EMISSION** (`hemitf`), at the fabric `d` throughout but for the last
block (the I/O event, which moves it to `oDfin`), the contact bit set exactly there; its tagged
deps are the run's; every fetch it carries is pinned to the image. -/
theorem W13Wit.runRowSound (c : CPU) (img imgF : Image) (fa : Nat) (d : Efab) (E : Nat) :
    ∀ (fe k : Nat) (h : W13Wit.Hs) (ws : Wstate) (dt : DstateT) (mm : W13Wit.Mm) (nw : Nat)
      (o : W13Wit.Out),
      W13Wit.runRow c img imgF fa fe k h ws dt mm nw d = some o → k + o.oRow.length = E →
      ∃ es, hemitf (fun _ => d) (fun j => if j + 1 = E then o.oDfin else d)
          (fun j => decide (j + 1 = E)) k ws o.oRow (W13Wit.pex c h) es (W13Wit.pex c o.oFin) ∧
        rowDepsTAux dt es = o.oDeps ∧ ∀ l, l ∈ es.map Prod.fst → WeakAxRealize.fetchPin imgF l := by
  intro fe
  induction fe with
  | zero => intro k h ws dt mm nw o hr; simp [W13Wit.runRow] at hr
  | succ fe ih =>
    intro k h ws dt mm nw o hr hE
    rcases hA : W13Wit.admRun imgF fa h dt with _ | ⟨ha, dta⟩
    · simp only [W13Wit.runRow, hA] at hr; cases hr
    rcases hV : W13Wit.evNode img mm nw ha d with _ | ⟨l, hb, d', mm', nw'⟩
    · simp only [W13Wit.runRow, hA, hV] at hr; cases hr
    rcases hP : projLbl (pclsEv (W13Wit.pex c ha) l ws) l with _ | lb
    · simp only [W13Wit.runRow, hA, hV, hP] at hr; cases hr
    simp only [W13Wit.runRow, hA, hV, hP] at hr
    obtain ⟨hst, hnb, hlat, hrf, hkeep, hfp, hpd⟩ :=
      W13Wit.evNodeSound c img mm nw ha d l hb d' mm' nw' hV
    obtain ⟨ls, hrun, hfls, hdeps⟩ := W13Wit.admRunSound c imgF fa h dt ha dta hA d
    have hre : hlblRealizes (W13Wit.pex c ha) ws lb l := ⟨hnb, hlat, hrf, hP⟩
    cases hdv : W13Wit.isDevB l
    · rw [hdv] at hr
      simp only [Bool.false_eq_true, if_false] at hr
      rcases hR : W13Wit.runRow c img imgF fa fe (k + 1) hb (lblPost k ws lb)
          (dstepT dta (l, some k)).1 mm' nw' d with _ | o'
      · rw [hR] at hr; cases hr
      rw [hR] at hr
      simp only [Option.some.injEq] at hr
      subst hr
      have hne := W13Wit.runRowNe c img imgF fa fe (k + 1) hb _ _ mm' nw' d o' hR
      have hE' : (k + 1) + o'.oRow.length = E := by
        simp only [List.length_cons] at hE; omega
      obtain ⟨es, hem, hd, hf⟩ := ih (k + 1) hb (lblPost k ws lb) _ mm' nw' o' hR hE'
      have hd' : d' = d := hkeep hdv
      subst hd'
      refine ⟨eadm ls ++ (l, some k) :: es, ?_, ?_, ?_⟩
      · refine hemitf.HFone k ws lb o'.oRow (W13Wit.pex c h) ls (W13Wit.pex c ha) d' l
          (W13Wit.pex c hb) es (W13Wit.pex c o'.oFin) false hrun hre ?_ ?_ hem
        · have hk : ¬ (k + 1 = E) := by omega
          simp only [hk, if_false]
          exact hst
        · have hk : ¬ (k + 1 = E) := by omega
          rw [hpd, hdv]
          simp [hk]
      · rw [hdeps]
        simp only [rowDepsTAux, hd]
      · intro l' hl'
        simp only [eadm, List.map_append, List.map_map, List.map_cons, List.mem_append,
          List.mem_cons] at hl'
        rcases hl' with hl' | rfl | hl'
        · obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl'
          exact hfls l0 hl0
        · exact hfp imgF
        · exact hf l' hl'
    · rw [hdv] at hr
      simp only [if_true, Option.some.injEq] at hr
      subst hr
      have hk : k + 1 = E := by simpa using hE
      refine ⟨eadm ls ++ [(l, some k)], ?_, ?_, ?_⟩
      · refine hemitf.HFone k ws lb [] (W13Wit.pex c h) ls (W13Wit.pex c ha) d l
          (W13Wit.pex c hb) [] (W13Wit.pex c hb) false hrun hre ?_ ?_ (hemitf.HFnil _ _ _)
        · simp only [hk, if_true]
          exact hst
        · rw [hpd, hdv]
          simp [hk]
      · rw [hdeps]
        simp [rowDepsTAux]
      · intro l' hl'
        simp only [eadm, List.map_append, List.map_map, List.map_cons, List.map_nil,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with hl' | rfl
        · obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl'
          exact hfls l0 hl0
        · exact hfp imgF

/-! # 3. `xv6ConfS`'s Bool twin ([R38.s1]) -/

/-- What a row's run hands the Bool twin: the tagged deps of its emission (`rowDepsT`), per
block the contact bit and a MOVED flag (`false` ⇒ the block kept the fabric). -/
structure GfRowCert where
  rcDeps : List Redge
  rcTq : List Bool
  rcMoved : List Bool

/-- The decidable residue of `gfexecConfIOT`'s per-row clauses: membership by contact (an
I/O-class event or a contact block is a member, a member is one of them, a moved block is a
member) and the tagged dependency clause. -/
def gfRowCertOk (G : Gexec) (gfDev : List Geid) (deps : List Tdep) (i : Nat) (row : List Lbl)
    (rc : GfRowCert) : Bool :=
  (List.range row.length).all (fun k =>
     (decide ((i, k) ∈ gfDev) == (gisIo G (i, k) || rc.rcTq.getD k false)) &&
     (!(rc.rcMoved.getD k false) || decide ((i, k) ∈ gfDev))) &&
  rc.rcDeps.all (fun e => decide ((((i, e.1.1), (i, e.1.2)), e.2) ∈ deps))

/-- **`xv6ConfS`'s BOOL TWIN** ([R38.s1]): every decidable clause of the device-active tagged
conformance (row count, `gfDev` duplicate-free and in range, per row membership by contact and the
tagged dependency clause over the run's certificate) AND the tagged model's well-formedness
`gtdepsWf` over the same edges — the co-satisfiability check that caught (F-dep)'s vacuity. -/
def xv6ConfSB (nh : Nat) (GT : GfexecT) (cs : List GfRowCert) : Bool :=
  decide (GT.gfGd.gtG.gxProg.length ≤ nh) && decide GT.gfDev.Nodup &&
  GT.gfDev.all (fun ik =>
    match GT.gfGd.gtG.gxProg[ik.1]? with
    | some row => decide (ik.2 < row.length)
    | none => false) &&
  (List.range GT.gfGd.gtG.gxProg.length).all (fun i =>
    match GT.gfGd.gtG.gxProg[i]?, cs[i]? with
    | some row, some rc => gfRowCertOk GT.gfGd.gtG GT.gfDev GT.gfGd.gtDeps i row rc
    | _, _ => false) &&
  gtdepsWfB GT.gfGd.gtG GT.gfGd.gtDeps

/-- (Lean-only, W5d-G G6-2) THE BOOL TWIN'S SOUNDNESS AT ANY FETCH SLOT `F`: with each row's run
facts (an emission realizing it whose tagged deps, contact bits and moved flags are the
certificate's, the slot `F`, members' endpoints on the fabric trace), a `true` twin gives every
clause of the tagged conformance (with slot `F`) and the tagged well-formedness. -/
theorem W13Wit.confSBRows (boot : Nat → Pexv6) (nh : Nat) (GT : GfexecT)
    (cs : List GfRowCert) (fab : Nat → Efab) (F : Nat → Hemission → Prop) :
    xv6ConfSB nh GT cs = true →
    (∀ (i : Nat) (row : List Lbl) (rc : GfRowCert), GT.gfGd.gtG.gxProg[i]? = some row →
       cs[i]? = some rc →
       ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
         hartConff i row (boot i) dvi dvo tq em ∧ rowDepsT em.emItems = rc.rcDeps ∧
         F i em ∧
         (∀ k, k < row.length → tq k = rc.rcTq.getD k false) ∧
         (∀ k, k < row.length → rc.rcMoved.getD k false = false → dvi k = dvo k) ∧
         (∀ k n, GT.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1))) →
    GT.gfGd.gtG.gxProg.length ≤ nh ∧ GT.gfDev.Nodup ∧
    (∀ (n i k : Nat), GT.gfDev[n]? = some (i, k) →
       ∃ row, GT.gfGd.gtG.gxProg[i]? = some row ∧ k < row.length) ∧
    (∀ (i : Nat) (row : List Lbl), GT.gfGd.gtG.gxProg[i]? = some row →
       ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
         hartConff i row (boot i) dvi dvo tq em ∧
         (∀ k : Nat, k < row.length →
            ((i, k) ∈ GT.gfDev ↔ (gisIo GT.gfGd.gtG (i, k) = true ∨ dvi k ≠ dvo k ∨ tq k = true))) ∧
         (∀ (k n : Nat), GT.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1)) ∧
         F i em ∧
         (∀ e, e ∈ rowDepsT em.emItems → (((i, e.1.1), (i, e.1.2)), e.2) ∈ GT.gfGd.gtDeps)) ∧
    gtdepsWf GT.gfGd.gtG GT.gfGd.gtDeps := by
  intro hb hrows
  simp only [xv6ConfSB, Bool.and_eq_true, decide_eq_true_eq, forallbForallTrue] at hb
  obtain ⟨⟨⟨⟨hnh, hnd⟩, hbnd⟩, hall⟩, hwf⟩ := hb
  refine ⟨hnh, hnd, ?_, ?_, gtdepsWfBSound _ _ hwf⟩
  · intro n i k hn
    have h := hbnd (i, k) (List.mem_of_getElem? hn)
    simp only at h
    split at h
    · rename_i row hrow
      exact ⟨row, hrow, by simpa using h⟩
    · cases h
  · intro i row hrow
    have hi : i < GT.gfGd.gtG.gxProg.length := lookup_lt_Some hrow
    have h := hall i (by simp [hi])
    simp only [hrow] at h
    split at h
    · rename_i row' rc hrow' hrc
      simp only [Option.some.injEq] at hrow'
      subst hrow'
      obtain ⟨em, dvi, dvo, tq, hem, hdeps, hfi, htq, hmv, hpin⟩ := hrows i row rc hrow hrc
      simp only [gfRowCertOk, Bool.and_eq_true, forallbForallTrue] at h
      obtain ⟨hks, hds⟩ := h
      refine ⟨em, dvi, dvo, tq, hem, fun k hk => ?_, hpin, hfi, fun e he => ?_⟩
      · have hk' := hks k (by simp [hk])
        simp only [beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hk'
        obtain ⟨hiff, hmov⟩ := hk'
        rw [htq k hk]
        constructor
        · intro hm
          have : (gisIo GT.gfGd.gtG (i, k) || rc.rcTq.getD k false) = true := by
            rw [← hiff]; simp [hm]
          rcases Bool.or_eq_true_iff.1 this with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inr h1)
        · intro hor
          rcases hor with h1 | h1 | h1
          · have h2 : (gisIo GT.gfGd.gtG (i, k) || rc.rcTq.getD k false) = true := by
              rw [h1, Bool.true_or]
            rw [← hiff] at h2
            simpa using h2
          · rcases hmov with h3 | h3
            · exact absurd (hmv k hk h3) h1
            · exact h3
          · have h2 : (gisIo GT.gfGd.gtG (i, k) || rc.rcTq.getD k false) = true := by
              rw [h1, Bool.or_true]
            rw [← hiff] at h2
            simpa using h2
      · rw [hdeps] at he
        simpa using hds e he
    · cases h

/-- **THE BOOL TWIN IS SOUND**: with each row's run facts (an emission realizing it whose tagged
deps, contact bits and moved flags are the certificate's, fetches pinned, members' endpoints on the
fabric trace), a `true` twin gives `xv6ConfS` and the tagged well-formedness. -/
theorem xv6ConfSBSound (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GT : GfexecT)
    (cs : List GfRowCert) (fab : Nat → Efab) :
    xv6ConfSB nh GT cs = true → GT.gfGd.gtG.gxImg = im → fab 0 = d0 →
    (∀ (i : Nat) (row : List Lbl) (rc : GfRowCert), GT.gfGd.gtG.gxProg[i]? = some row →
       cs[i]? = some rc →
       ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
         hartConff i row (boot i) dvi dvo tq em ∧ rowDepsT em.emItems = rc.rcDeps ∧
         emFetchImg im em ∧
         (∀ k, k < row.length → tq k = rc.rcTq.getD k false) ∧
         (∀ k, k < row.length → rc.rcMoved.getD k false = false → dvi k = dvo k) ∧
         (∀ k n, GT.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1))) →
    xv6ConfS boot d0 im nh GT ∧ gtdepsWf GT.gfGd.gtG GT.gfGd.gtDeps := by
  intro hb himg hfab hrows
  obtain ⟨hnh, hnd, hbnd, hr, hwf⟩ := W13Wit.confSBRows boot nh GT cs fab
    (fun _ em => emFetchImg GT.gfGd.gtG.gxImg em) hb (by rw [himg]; exact hrows)
  exact ⟨⟨himg, hnh, fab, hfab, hnd, hbnd, hr⟩, hwf⟩

/-! # 4. The Zifencei twin (W5d-G G6-2) -/

/-- (Lean-only) A pin to a SUB-image is a pin to the image. -/
theorem W13Wit.fetchPinSub (img imgF : Image) (l : Wlabel) :
    (∀ z b, imgF z = some b → img z = some b) →
    WeakAxRealize.fetchPin imgF l → WeakAxRealize.fetchPin img l := by
  intro hsub hp
  cases l with
  | LIFetch base tvs =>
    refine ⟨hp.1, fun j hj => ?_⟩
    have h := hp.2 j hj
    have hs : ((tvs.map Prod.snd)[j]?).isSome := by simp [hj]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
    rw [hb] at h ⊢
    exact hsub _ _ h
  | _ => trivial

theorem W13Wit.emFetchImgSub (img imgF : Image) (em : Hemission) :
    (∀ z b, imgF z = some b → img z = some b) → emFetchImg imgF em → emFetchImg img em :=
  fun hsub h l hl => W13Wit.fetchPinSub img imgF l hsub (h l hl)

/-- **`emFetchUnwritten`'s decidable side**: every byte the graph writes lies OFF the fetch image
`imF` (finite: the rows' write labels). -/
def emFetchUnwrittenB (G : Gexec) (imF : Image) : Bool :=
  G.gxProg.all (fun row => row.all (fun l =>
    match lbWr l with
    | some (base, vs) => (List.range vs.length).all (fun j => (imF (accAddr base j)).isNone)
    | none => true))

theorem W13Wit.emFetchUnwrittenBOff (G : Gexec) (imF : Image) :
    emFetchUnwrittenB G imF = true → ∀ w a v, gwritesByte G w a v → imF a = none := by
  rintro hb w a v ⟨l, base, vs, j, hl, hwr, hv, rfl⟩
  unfold gxLbl at hl
  rcases hrow : G.gxProg[w.1]? with _ | row
  · rw [hrow] at hl; cases hl
  rw [hrow] at hl
  simp only [Option.bind_some] at hl
  simp only [emFetchUnwrittenB, List.all_eq_true] at hb
  have h := hb row (List.mem_of_getElem? hrow) l (List.mem_of_getElem? hl)
  simp only [hwr, List.all_eq_true, List.mem_range, Option.isNone_iff_eq_none] at h
  exact h j (lookup_lt_Some hv)

/-- **SOUND**: an emission pinned to the fetch image `imF` (so every fetched byte is ON it) fetches
only bytes the graph never writes. -/
theorem emFetchUnwrittenBSound (G : Gexec) (imF : Image) (em : Hemission) :
    emFetchUnwrittenB G imF = true → emFetchImg imF em → GraphFetch.emFetchUnwritten G em := by
  intro hb hpin n base tvs hn j hj w v hw
  have hp : WeakAxRealize.fetchPin imF (Wlabel.LIFetch base tvs) :=
    hpin _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hn, rfl⟩)
  have h1 := hp.2 j hj
  have h2 := W13Wit.emFetchUnwrittenBOff G imF hb w _ v hw
  rw [h2] at h1
  simp [hj] at h1

/-- **THE ZIFENCEI BOOL TWIN**: `xv6ConfSB` (its decidable side keeps the pinned fetches as a
run fact) and `emFetchUnwrittenB` at the fetch image `imF`. -/
def xv6ConfSZB (nh : Nat) (GT : GfexecT) (cs : List GfRowCert) (imF : Image) : Bool :=
  xv6ConfSB nh GT cs && emFetchUnwrittenB GT.gfGd.gtG imF

/-- **THE ZIFENCEI TWIN IS SOUND**: with each row's run facts, its fetches pinned to a SUB-image
`imF` of the graph's image (e.g. the kernel text), a `true` twin gives `xv6ConfSZ` — the slot
through the kernel-text instance `GraphFetch.emZifOfPinC`, the stored fragment through
`GraphFetch.emFetchInOfUnwritten` — and the tagged well-formedness. -/
theorem xv6ConfSZBSound (boot : Nat → Pexv6) (d0 : Efab) (im : Image) (nh : Nat) (GT : GfexecT)
    (cs : List GfRowCert) (fab : Nat → Efab) (imF : Image) :
    xv6ConfSZB nh GT cs imF = true → GT.gfGd.gtG.gxImg = im → fab 0 = d0 →
    (∀ z b, imF z = some b → im z = some b) →
    (∀ (i : Nat) (row : List Lbl) (rc : GfRowCert), GT.gfGd.gtG.gxProg[i]? = some row →
       cs[i]? = some rc →
       ∃ (em : Hemission) (dvi dvo : Nat → Efab) (tq : Nat → Bool),
         hartConff i row (boot i) dvi dvo tq em ∧ rowDepsT em.emItems = rc.rcDeps ∧
         emFetchImg imF em ∧
         (∀ k, k < row.length → tq k = rc.rcTq.getD k false) ∧
         (∀ k, k < row.length → rc.rcMoved.getD k false = false → dvi k = dvo k) ∧
         (∀ k n, GT.gfDev[n]? = some (i, k) → dvi k = fab n ∧ dvo k = fab (n + 1))) →
    xv6ConfSZ boot d0 im nh GT ∧ gtdepsWf GT.gfGd.gtG GT.gfGd.gtDeps := by
  intro hb himg hfab hsub hrows
  simp only [xv6ConfSZB, Bool.and_eq_true] at hb
  obtain ⟨hb, hnw⟩ := hb
  obtain ⟨hnh, hnd, hbnd, hr, hwf⟩ := W13Wit.confSBRows boot nh GT cs fab
    (fun i em => emZifencei GT.gfGd.gtG i em ∧ GraphFetch.emFetchIn (forget GT.gfGd) i em) hb
    (fun i row rc hrow hrc => by
      obtain ⟨em, dvi, dvo, tq, hem, hd, hfi, h1, h2, h3⟩ := hrows i row rc hrow hrc
      have hfi' : emFetchImg GT.gfGd.gtG.gxImg em := by
        rw [himg]; exact W13Wit.emFetchImgSub im imF em hsub hfi
      have hu := emFetchUnwrittenBSound GT.gfGd.gtG imF em hnw hfi
      exact ⟨em, dvi, dvo, tq, hem, hd,
        ⟨GraphFetch.emZifOfPinC _ i em hfi' hu,
          GraphFetch.emFetchInOfUnwritten (forget GT.gfGd) i em hfi' hu⟩, h1, h2, h3⟩)
  exact ⟨⟨himg, hnh, fab, hfab, hnd, hbnd, hr⟩, hwf⟩

end Weak
