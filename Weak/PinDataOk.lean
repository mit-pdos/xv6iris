/-
Weak: **`dataOkR` [OWN.95] — (1) THE INTERFACE: a walk load/store's per-access run values, and the
data-access value predicate `dkB`** (cycRun's named premise `PinCycRun.dataOkR`,
`Weak/PinCycRunAsm.lean:502`; `PROGRESS-dataOk.md`).  Lean-only.

A walk load/store cycle at `pc` takes no synchronous exception when its data access translates,
passes PMP/PMA and is aligned.  What that needs from the RUN (values a static walk cannot know) is
`dataRealized`, an interface of `RvwmoXv6Adequacy.syncRealized`'s / `PinCycRun.walkStartRealized`'s
kind that W11-F's composition supplies from the certified run:
* the access's configuration `DCfg` (the walk's three page-table pages `b`, `b1`, `b0`, the
  access's `vpn`, the leaf's `ppn`/`perm` — for xv6 one of `Xv6.kvmMapK`'s maps — and the base
  register's number and value `base`/`bval`), with the pages in RAM (`DCfg.ram`);
* the access itself (`dAccOk`): the walk instruction at `pc` is (or redirects to) a base `LOAD` /
  `STORE` whose base register is `base`, whose virtual address `bval + sext imm` is in the page
  `vpn`, naturally aligned, canonical, and a store only to an `R|W` page;
* at every register READ of the cycle, the value read is `dG`-admitted (`atRegRead`): boot-admitted,
  `satp` the kernel's, the TLB caching for `vpn` only the walk's leaf (`dTlbOk`), supervisor
  mode, `mstatus.MPRV = 0` with an RV64 `SXL`, `menvcfg = menvcfgS` (Svadu `ADUE`), `mseccfg = 0`,
  xv6's PMP tables (`start.c`), and the base register holding `bval`;
* every RAM-read label of the cycle carries filter-admitted bytes (`labAnsOkD`): a page-table read
  at one of the walk's three slots answers the slot's value (as `Xv6.kptMapsAt` gives at the graph).

`dkB c P m` is the matching all-paths predicate on a Sail tree (state-free, as `PinFetchPa.tvB`):
register reads answered by `dG c`-admitted values, memory reads by `dAns c`-admitted values, a
memory write answered `.Ok (some true)` (the only answer `WeakEvInst.pnodeStep` gives, `:354-382`),
register writes unconstrained (the filters are justified per read by the interface, not by the
tree), a failure stuck, `.pure x` owing `P x`.  The Sail-side theorems (step (3)) are `dkB` facts.

Spec (FIRST): Sail `vmem_read`/`vmem_write` (`VmemUtils.lean:440-460`) trap on a misaligned access
(`plat_misaligned_exception`), a failed translation (`translateAddr`, `Vmem.lean:567`) or a failed
PMP/PMA check (`checked_mem_read`/`_write`, `Mem.lean`); the privileged spec's Sv39 permission
check (R for a load, W for a store, U clear in S-mode) and the Svadu A/D update; PMP entry 0 TOR
over [0, 2^56) R/W/X after `start()`; RVWMO is silent on faults.  FAITHFUL (an interface of run
values, no ISA assumption).  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinCycRunAsm
import Weak.PinFetchPaRun
import MachCSL.PmpXv6Defs

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinDataOk
open SailCycleOrderK PinCycRun
open PinFetchPa (kSatp)

/-! ## 1. The access's configuration and the filters -/

/-- **A walk access's configuration**: the walk's three pages, the access's vpn, the leaf's page
and permission, the base register's number and value. -/
structure DCfg where
  b : BitVec 44
  b1 : BitVec 44
  b0 : BitVec 44
  vpn : BitVec 27
  ppn : BitVec 44
  perm : KPerm
  base : Nat
  bval : BitVec 64

/-- A RAM page (xv6: RAM is `0x80000000 ..< 0x88000000`, the PMA table's RAM region). -/
def ramPage (p : BitVec 44) : Prop := 0x80000 ≤ p.toNat ∧ p.toNat < 0x88000

/-- The walk's pages and the leaf's page are RAM pages. -/
def DCfg.ram (c : DCfg) : Prop := ramPage c.b ∧ ramPage c.b1 ∧ ramPage c.b0 ∧ ramPage c.ppn

/-- **The PTE filter**: an 8-byte read at one of the walk's slots answers the slot's value. -/
def dAns (c : DCfg) (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)) : Prop :=
  n = 8 →
    (pa = pteAddr c.b (vpnIdx c.vpn 2) → w.toNat = (kPtr c.b1).toNat) ∧
    (pa = pteAddr c.b1 (vpnIdx c.vpn 1) → w.toNat = (kPtr c.b0).toNat) ∧
    (pa = pteAddr c.b0 (vpnIdx c.vpn 0) → ∃ a d : BitVec 1, w.toNat = (kLeaf c.ppn c.perm a d).toNat)

/-- **The TLB filter**: every resident entry matching `vpn` at ASID 0 caches the walk's leaf (any
A/D) at the leaf's slot (what `MachCSL.tlbOk` gives for the sealed table). -/
def dTlbOk (c : DCfg) (tlb : Tlb) : Prop :=
  ∀ (i : Nat) (hi : i < 2 ^ 6) (ent : TLB_Entry), tlb[i] = some ent →
    match_TLB_Entry ent 0#16 (sign_extend (m := 45) c.vpn) = true →
    ∃ a d : BitVec 1, ent = tlbEntryOf 0#16 c.vpn c.ppn (kLeaf c.ppn c.perm a d) (pteAddr c.b0 (vpnIdx c.vpn 0))

/-- `mstatus` at a kernel data access: no `MPRV`, an RV64 supervisor (`SXL = 2`). -/
def dMstatusOk (v : BitVec 64) : Prop := _get_Mstatus_MPRV v = 0#1 ∧ _get_Mstatus_SXL v = 2#2

/-- The filtered registers' clause. -/
def dFix (c : DCfg) (r : Register) (v : RegisterType r) : Prop :=
  (∀ h : r = .satp, cast (congrArg RegisterType h) v = kSatp c.b) ∧
  (∀ h : r = .tlb, dTlbOk c (cast (congrArg RegisterType h) v)) ∧
  (∀ h : r = .cur_privilege, cast (congrArg RegisterType h) v = Privilege.Supervisor) ∧
  (∀ h : r = .mstatus, dMstatusOk (cast (congrArg RegisterType h) v)) ∧
  (∀ h : r = .menvcfg, cast (congrArg RegisterType h) v = menvcfgS) ∧
  (∀ h : r = .mseccfg, cast (congrArg RegisterType h) v = 0#64) ∧
  (∀ h : r = .pmpcfg_n, cast (congrArg RegisterType h) v = xv6Pmpcfg) ∧
  (∀ h : r = .pmpaddr_n, cast (congrArg RegisterType h) v = xv6Pmpaddr) ∧
  (∀ h : RegisterType r = BitVec 64, eregGprNum r = some c.base → cast h v = c.bval)

/-- **The register filter**: boot-admitted, and the filtered registers' clause. -/
def dG (c : DCfg) (r : Register) (v : RegisterType r) : Prop := Rboot r v ∧ dFix c r v

/-! ## 2. The access -/

/-- A base load / store's base register, offset, width and store-ness. -/
def memAcc : instruction → Option (regidx × BitVec 12 × Int × Bool)
  | .LOAD (imm, rs1, _, _, w) => some (rs1, imm, w, false)
  | .STORE (imm, _, rs1, w) => some (rs1, imm, w, true)
  | _ => none

/-- The access's virtual address. -/
def DCfg.va (c : DCfg) (imm : BitVec 12) : BitVec 64 := c.bval + sign_extend (m := 64) imm

/-- **The walk access at `pc`** under `c`: a base load/store (or a compressed form redirecting to
one) of width 1/2/4/8 on base `c.base ≠ 0`, at an address in page `c.vpn`, naturally aligned,
canonical, and a store only to an `R|W` page. -/
def dAccOk (pc : Int) (c : DCfg) : Prop :=
  ∃ (a b : instruction) (rs1 : regidx) (imm : BitVec 12) (w : Int) (st : Bool),
    PinWalkTab.decS pc = some a ∧ (b = a ∨ execute a = pure (.ExecuteAs b)) ∧
    memAcc b = some (rs1, imm, w, st) ∧ (w.toNat = 1 ∨ w.toNat = 2 ∨ w.toNat = 4 ∨ w.toNat = 8) ∧
    (uxaIdx rs1).toNat = c.base ∧ c.base ≠ 0 ∧
    vpnOf (c.va imm) = c.vpn ∧ (c.va imm).toNat % w.toNat = 0 ∧ (c.va imm).toNat < 2 ^ 38 ∧
    (st = true → c.perm = .rw)

/-! ## 3. The interface -/

/-- The hart at `p`, if at a register read, reads a `G`-admitted value. -/
def atRegRead (p : Pexv6) (G : (r : Register) → RegisterType r → Prop) : Prop :=
  ∀ (cpu : CPU) (r : Register) (k : RegisterType r → SailM Unit) (rs : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch),
    p = .PHart cpu (.impure (.ok (.regRead r)) k) rs fn ib → G r (rs r)

/-- The PTE filter on a label's address and bytes. -/
def dAnsL (c : DCfg) (a : Int) (bs : List (BitVec 8)) : Prop :=
  ∀ (pa : BitVec 64) (n : Nat) (w : BitVec (8 * n)), paZ pa = a →
    bs = (List.range n).map (fun j => nthByte w j) → dAns c pa n w

/-- Every RAM-read label carries filter-admitted bytes. -/
def labAnsOkD (c : DCfg) : Wlabel → Prop
  | .LLoad _ _ a tvs _ => dAnsL c a (tvs.map Prod.snd)
  | .LExLoad _ a tvs _ => dAnsL c a (tvs.map Prod.snd)
  | .LIFetch a tvs => dAnsL c a (tvs.map Prod.snd)
  | _ => True

/-- **THE DATA ACCESS, REALIZED (INTERFACE, header; W11-F's obligation)**: at every walk
load/store cycle at `pc`, there is a configuration of its access (`dAccOk`, pages in RAM) such that
along every partial run of the cycle, every register read is `dG`-admitted and every RAM-read
label is `labAnsOkD`. -/
def dataRealized (p0 : Pexv6) (d0 : Efab) (em : Hemission) (pc : Int) : Prop :=
  memPc pc = true →
  ∀ (pfx : List Eitem) (ls0 : List Wlabel) (q : Pexv6) (d1 : Efab),
    cycStart p0 d0 em pfx pc ls0 q d1 →
    ∃ c : DCfg, c.ram ∧ dAccOk pc c ∧
      ∀ (ls1 : List Wlabel) (pm : Pexv6) (dm : Efab), cycIn em pfx ls0 ls1 → irun ls1 q d1 pm dm →
        atRegRead pm (dG c) ∧ ∀ l ∈ ls1, labAnsOkD c l

/-! ## 4. The data-access value predicate -/

/-- **THE DATA-ACCESS VALUE PREDICATE** (header). -/
def dkB (c : DCfg) {X : Type} (P : X → Prop) : SailM X → Prop
  | .pure x => P x
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .memRead n _ req, k => ∀ w : BitVec (8 * n), dAns c req.pa n w → dkB c P (k (.Ok (w, none)))
    | .memWrite .., k => dkB c P (k (.Ok (some true)))
    | .regRead r, k => ∀ v, dG c r v → dkB c P (k v)
    | .regWrite _ _, k => ∀ u, dkB c P (k u)
    | .instrAnnounce .., k => ∀ v, dkB c P (k v)
    | .barrier _, k => ∀ v, dkB c P (k v)
    | .branchAnnounce .., k => ∀ v, dkB c P (k v)
    | .cacheOp _, k => ∀ v, dkB c P (k v)
    | .tlbi _, k => ∀ v, dkB c P (k v)
    | .takeException _, k => ∀ v, dkB c P (k v)
    | .returnException _, k => ∀ v, dkB c P (k v)
    | .translationStart _, k => ∀ v, dkB c P (k v)
    | .translationEnd _, k => ∀ v, dkB c P (k v)
    | .cycleCount, k => ∀ v, dkB c P (k v)
    | .getCycleCount, k => ∀ v, dkB c P (k v)
    | .message _, k => ∀ v, dkB c P (k v)
    | .choose _, k => ∀ v, dkB c P (k v)
    | .readRam .., k => ∀ v, dkB c P (k v)
    | .writeRam .., k => ∀ v, dkB c P (k v)

variable {c : DCfg}

theorem dkBind {X Y : Type} (Q : X → Prop) (P : Y → Prop) (m : SailM X) (f : X → SailM Y) :
    dkB c Q m → (∀ x, Q x → dkB c P (f x)) → dkB c P (m >>= f) := by
  induction m with
  | pure y => intro hm hf; exact hf y hm
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show dkB c P (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case memRead => exact fun w hw => ih _ (hm w hw) hf
      case memWrite => exact ih _ hm hf
      case regRead => exact fun v hv => ih v (hm v hv) hf
      all_goals exact fun v => ih v (hm v) hf

theorem dkMono {X : Type} (P P' : X → Prop) (hP : ∀ x, P x → P' x) :
    ∀ (m : SailM X), dkB c P m → dkB c P' m := by
  intro m
  induction m with
  | pure y => exact hP y
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead => exact fun w hw => ih _ (hm w hw)
      case memWrite => exact ih _ hm
      case regRead => exact fun v hv => ih v (hm v hv)
      all_goals exact fun v => ih v (hm v)

theorem dkPure {X : Type} (P : X → Prop) (x : X) : P x → dkB c P (pure x : SailM X) := fun h => h

/-- **The lift**: W-SCO's strict footprint (`fp`: no fetch read, any answer) gives `dkB` with its
post — `dG` is boot-admitted, and `dkB` constrains no write. -/
theorem dkOfFp {X : Type} (S : X → Prop) : ∀ (m : SailM X), SailCycleOrderFp.fp S m → dkB c S m := by
  intro m
  induction m with
  | pure y => intro h; exact h
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req => exact fun w _ => ih _ (hm.2 _)
      case memWrite => exact ih _ (hm _)
      case instrAnnounce => exact hm.elim
      case barrier => exact fun v => ih v hm.2
      case regRead r => exact fun v hv => ih v (hm v hv.1)
      case regWrite r v => exact fun u => ih u (hm.2 u)
      all_goals exact fun v => ih v (hm v)

/-- The lift from the `satp`/`tlb`-free footprint (`PinFetchPaFp.xf`). -/
theorem dkOfXf {X : Type} (S : X → Prop) : ∀ (m : SailM X), PinFetchPaFp.xf S m → dkB c S m := by
  intro m
  induction m with
  | pure y => intro h; exact h
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead n va req => exact fun w _ => ih _ (hm.2 _)
      case memWrite => exact ih _ (hm _)
      case instrAnnounce => exact hm.elim
      case barrier => exact fun v => ih v hm.2
      case regRead r => exact fun v hv => ih v (hm v hv.1)
      case regWrite r v => exact fun u => ih u (hm.2 u)
      all_goals exact fun v => ih v (hm v)

/-- A footprint head of a bind. -/
theorem dkXfBind {X Y : Type} (S : X → Prop) (P : Y → Prop) (m : SailM X) (f : X → SailM Y)
    (hm : PinFetchPaFp.xf S m) (hf : ∀ x, S x → dkB c P (f x)) : dkB c P (m >>= f) :=
  dkBind S P m f (dkOfXf S m hm) hf

/-- A footprint head with the trivial post. -/
theorem dkXfT {X Y : Type} {P : Y → Prop} (m : SailM X) (f : X → SailM Y) (hm : PinFetchPaFp.xfT m)
    (hf : ∀ x, dkB c P (f x)) : dkB c P (m >>= f) :=
  dkXfBind _ P m f hm (fun x _ => hf x)

/-- A register read node. -/
theorem dkReadReg {X : Type} {P : X → Prop} (r : Register) (f : RegisterType r → SailM X)
    (h : ∀ v, dG c r v → dkB c P (f v)) : dkB c P (readReg r >>= f) := h

/-- A register write node. -/
theorem dkWriteReg {X : Type} {P : X → Prop} (r : Register) (v : RegisterType r) (f : Unit → SailM X)
    (h : dkB c P (f ())) : dkB c P (writeReg r v >>= f) := fun _ => h

/-! ## 5. The filter's projections -/

theorem dGSatp {v : RegisterType .satp} (h : dG c .satp v) : v = kSatp c.b := h.2.1 rfl
theorem dGTlb {v : RegisterType .tlb} (h : dG c .tlb v) : dTlbOk c v := h.2.2.1 rfl
theorem dGPriv {v : RegisterType .cur_privilege} (h : dG c .cur_privilege v) : v = .Supervisor :=
  h.2.2.2.1 rfl
theorem dGMstatus {v : RegisterType .mstatus} (h : dG c .mstatus v) : dMstatusOk v := h.2.2.2.2.1 rfl
theorem dGMenvcfg {v : RegisterType .menvcfg} (h : dG c .menvcfg v) : v = menvcfgS := h.2.2.2.2.2.1 rfl
theorem dGMseccfg {v : RegisterType .mseccfg} (h : dG c .mseccfg v) : v = 0#64 := h.2.2.2.2.2.2.1 rfl
theorem dGPmpcfg {v : RegisterType .pmpcfg_n} (h : dG c .pmpcfg_n v) : v = xv6Pmpcfg :=
  h.2.2.2.2.2.2.2.1 rfl
theorem dGPmpaddr {v : RegisterType .pmpaddr_n} (h : dG c .pmpaddr_n v) : v = xv6Pmpaddr :=
  h.2.2.2.2.2.2.2.2.1 rfl

end PinDataOk
end Weak
