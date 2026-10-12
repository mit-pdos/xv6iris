/-
Weak: **the SYMBOLIC DATA SIDE of loads / stores, ONCE, over an ABSTRACT certificate kit** (to be
instantiated at `AxSymMem.EvD` and at `AxCert.Cert` by the later AxDataX files).

Rocq: `iris/AxDataX.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 THE KIT `XKit img S C`: a certificate predicate `C` over control states `S` with the
structural rules every certificate of the engine has (ret, bind, mono, register read / write off
the pins, try-catch, failure node, the `EvA` embedding at a fixed state) — and, separately (as
section variables of §2 / §3), the DATA NODES: `CDrd` (a plain RAM read at a `dok` request,
DEMONIC, from a pending state `pend s` to `srd s vs`) and `CDwr` (a plain RAM write at a `dok`
request, to `swr s bytes ak`).  Derived: `CBind0`, `CLiftR`, `CCatchEarlyReturn`, `CReadReg`,
`CExecA`/`CExecASame` (an `execA` fact at the IMAGE state `tσ σ t` is a `C` fact), `CUntilMT1`.
§2 THE READ CHAIN (width generic, `Load Data`, aligned in-page): `XReadRam` (the data node; value
`rrv w vs` = the model's word of the bytes), `XCheckedMemRead`, `XMemRead`, `XTranslateAndRead`,
`XVmemReadAddr`, `XVmemRead`, `XExecuteLOAD`; the register-only callees are `execA` premises
(SC `exec` facts through `to_a`), the translation an `execA` fact at the image state.
§3 THE WRITE CHAIN: `XWriteRam`, `XCheckedMemWrite`, `XMemWriteValue`, `XMemWriteEa`,
`XVmemWriteAddr`, `XVmemWrite`, `XExecuteSTORE`.

## Deviations from Rocq

1. THE KIT IS A STRUCTURE.  Rocq's section `kit` takes `C0` and eight rule `Context`s and
   each lemma abstracts only those it uses; Lean bundles the rules as `XKit img S C` (fields
   `cMono` `cRet` `cBind` `cTryCatch` `cExt` `cRd` `cWr` `cEvA` = Rocq `C_mono` … `C_EvA`), and
   every kit / chain lemma takes `K : XKit img S C` first; the read chain then takes
   `pend srd CDrd`, the write chain `pend swr CDwr` (`XMemWriteEa` takes neither `CDwr` nor the
   width premise, as in Rocq).  Downstream instances build one `XKit` and pass it.
   `img` / `dok` / `S` / `C` are implicit.
2. LEAN-SAIL MONADS (as `AxSymEngine` deviation 4 / `AxSpineOk` deviation 4).  `C` is stated on
   `SailM X` with failure predicate over `Sail.Error exception` (Rocq: any `Defs.monad E X`);
   the early-return monad `SailME R X` is reached through `ExceptT.run`, with result type
   `Except (Sail.Error exception ⊕ R) X`.  `CLiftR` is over `ExceptT.run (liftM m)` (post
   `.ok x ↦ Q x`, `.error _ ↦ False`); `CCatchEarlyReturn` is over `SailME.run` (as
   `EvACatchEarlyReturn`); `CUntilMT1` is lean-sail's `untilFuelM 1` in the early-return monad
   (where the model's split loops live); `Defs.try_catch` ↦ `PreSail.tryCatchAll` (`cTryCatch`).
   `C_rd`/`C_wr`: lean-sail register events carry no access kind; `C_ext`'s continuation is
   `Empty → SailM X`.  `seip_reg` ↦ `AxRunClose.pinReg` (both pins).
3. DATA NODES.  `CDrd`'s node is `.impure (.ok (.memRead n va req)) k` with the answer
   `.Ok (wordOfBytes n vs, none)`, premises `devAddr req.pa = false`,
   `(classify req.access_kind).akLatest = false`, `(classify req.access_kind).akIfetch = false`,
   `dok (paZ req.pa) n`.  `CDwr` (lean-sail write values are `Option`) takes the written word `v`
   with `req.value = some v` and continues at `swr s (WeakInterpProj.wbytes n v) req.access_kind`
   with answer `.Ok (some true)`.  The Lean model's `checked_mem_read` reads with `Read_ifetch` /
   `Read_ttw` / `Read_plain` by access class (Rocq: always `Read_plain`), so the generic data
   node is the Lean-only `AxDataX.xReadRamK` (`Read_plain` or `Read_ttw`) and
   `XCheckedMemRead` / `XMemRead` take `acc ≠ .InstructionFetch ()` (section variable `hacc`,
   after `hw`); `XReadRam` is its `Read_plain` instance.  See deviation 7.
4. WIDTHS.  `Z` widths ↦ `Nat`; Rocq's section hypothesis `0 < w` (`X_checked_mem_read`,
   `X_mem_read`, `X_checked_mem_write`, `X_mem_write_value`) and `X_translate_and_read`'s `0 < w`
   ↦ `vmemWidth w` (the model's accumulator / extract casts are closed per width: the proofs
   case on the four widths for the final bit-vector equation, as `AxSpineOk3`).  `rrv w vs` is
   `wordOfBytes w vs` (already at `BitVec (8 * w)`): Rocq's `cast_N` and `rrv_eq` / `rrv_pi` /
   `wrb_pi` are trivial (`rfl`) in Lean, kept for the name map.  `wrb w data` is
   `WeakInterpProj.wbytes w data`.
5. SPELLING (as `ExecSC*`).  `mstate` ↦ `ExecSt`, `MState t.(sregs) σ.(mem) t.(mdev)` ↦
   `⟨t.regs, σ.mem, t.dev⟩` (`tσ σ t`, an `abbrev`), `register_lookup r t.(sregs)` ↦ `t.regs r`,
   `img_of` ↦ `imgOf`, `uint pa` ↦ `paZ pa`, `init_ext_ptw` / `tt` ↦ `()`, `sign_extend' 64 imm`
   ↦ `sign_extend (m := 64) imm`, `default_meta` kept.  `X_execute_LOAD`'s
   `set_reg t1 (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg v)` ↦ `t1.setGpr rd v`
   (the `rd ≠ 0` premise kept, `rd.toNat ≠ 0`); `X_execute_STORE`'s `v2` (the `rs2` value) ↦
   `t.gpr rs2` and its stored word `autocast (subrange_vec_dec v2 (w * 8 - 1) 0)` ↦ the
   Lean-only `AxDataX.stData w (t.gpr rs2)` (the model's `setWidth (8 * w) (extractLsb …)`).
   `wX_bits` / `rX_bits` steps use `AxSymEngine2.rf0EvA` with `rf0WXBits` / `rf0RXBits` and the
   SC facts `execWXBitsGpr` / `execRXBitsGpr` (Rocq: `toA` of the SC facts).
6. TACTICS.  Rocq `nseipK` is dropped (the pin test is `AxSymEngine2.notPin _ (by decide)
   (by decide)`); `x_step` / `x_go` ↦ the tactic `ax_datax_go K` over the Lean-only stepping
   lemmas; `x_use σ H` / `x_useT σ H` ↦ the Lean-only `AxDataX.cRUse` / `cRUseT` (early-return
   monad) and `AxDataX.cFactUse` / `cFactUseT` (base monad).
7. INTERFACE FIX (2026-10-07, owner-approved, for `AxDataX2`'s instances).  The data nodes are
   stated to match `EvD.evdDrd`/`evdDwr` and `AxCert.Cert.cDrd`/`cDwr`: `CDrd` gained the
   `akIfetch = false` premise (a data read is never a fetch; Stage C), so `xReadRamK` no longer
   covers `Read_ifetch` and `XCheckedMemRead`/`XMemRead` exclude `.InstructionFetch`; `CDwr`'s
   continuation answer is `.Ok (some true)` (was `.Ok none`; `write_ram` matches `.Ok _`, so
   `XWriteRam` is unchanged).  Every other statement is unchanged.

**Rocq → Lean name map.**  `tσ` `tσ`, `rd_facts` `rdFacts`, `wr_facts` `wrFacts`, `rrv_eq`
`rrvEq`, `rrv` `rrv`, `rrv_pi` `rrvPi`, `wrb` `AxDataX.wrb` (duplicated name), `wrb_pi` `wrbPi`,
the section `kit`'s `C0`/`C_mono`…`C_EvA` ↦ `XKit` and its fields, `C_bind0` `CBind0`, `C_liftR`
`CLiftR`, `C_catch_early_return` `CCatchEarlyReturn`, `C_read_reg` `CReadReg`, `C_execA`
`CExecA`, `C_execA_same` `CExecASame`, `C_untilMT_1` `CUntilMT1`, `C_drd` `CDrd`, `C_dwr` `CDwr`
(section variables), `X_read_ram` `XReadRam`, `X_checked_mem_read` `XCheckedMemRead`,
`X_mem_read` `XMemRead`, `X_translate_and_read` `XTranslateAndRead`, `X_vmem_read_addr`
`XVmemReadAddr`, `X_vmem_read` `XVmemRead`, `X_execute_LOAD` `XExecuteLOAD`, `ak_plain`
`AxDataX.akPlain` (duplicated name), `X_write_ram` `XWriteRam`, `X_checked_mem_write`
`XCheckedMemWrite`, `X_mem_write_value` `XMemWriteValue`, `X_mem_write_ea` `XMemWriteEa`,
`X_vmem_write_addr` `XVmemWriteAddr`, `X_vmem_write` `XVmemWrite`, `X_execute_STORE`
`XExecuteSTORE`; Ltacs `x_step`/`x_go` ↦ `ax_datax_go`, `x_use`/`x_useT` ↦ lemmas (deviation 6).
Lean-only (file-qualified `AxDataX.*`): `substArg`, `cRBind`, `cRLift`, `cFact`, `cFactRead`,
`cFactPure`, `cFactAssoc`, `cRRead`, `cRPureBind`, `cRAssoc`, `cRPure`, `cRUse`, `cRUseT`,
`cFactUse`, `cFactUseT`, `cRLiftLast`, `cFactEvA`, `xReadRamK`, `stData`.

**Dropped:** the Ltac `nseipK` (deviation 6).  No definition or lemma dropped (Rocq 6
definitions + 24 lemmas; Lean 30 + `XKit` + 19 Lean-only + 1 tactic).

**Import hygiene.**  `bv_decide` adds the auxiliary definitions `SATPMode.enumToBitVec` /
`Register.enumToBitVec` for the enums it meets; two modules that each add them cannot be imported
together.  `MachCSL.BvEnumSatp` and `Xv6.UkFetchFact` add them first, so they are imported here
and `bv_decide` reuses their copies.
-/
import Weak.AxSpineOk3
import Weak.AxSymEngine2
import Weak.ExecSC8
import MachCSL.BvEnumSatp
import Xv6.UkFetchFact

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. The kit -/

/-- The IMAGE state at the thread's registers. -/
abbrev tσ (σ t : ExecSt) : ExecSt := ⟨t.regs, σ.mem, t.dev⟩

/-- The register-only facts of a data READ at `pa` (width `w`, access `acc`), at the image state. -/
def rdFacts (σ : ExecSt) (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (w : Nat) (pa : BitVec 64) (t : ExecSt) : Prop :=
  execA (effectivePrivilege acc (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
    = some (.Supervisor, tσ σ t) ∧
  execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tσ σ t)
    = some (.Ok pmaOkAligned, tσ σ t) ∧
  execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) ∧
  execA (within_mmio_readable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t)

/-- The register-only facts of a data WRITE. -/
def wrFacts (σ : ExecSt) (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (w : Nat) (pa : BitVec 64) (t : ExecSt) : Prop :=
  execA (effectivePrivilege acc (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
    = some (.Supervisor, tσ σ t) ∧
  execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tσ σ t)
    = some (.Ok pmaOkAligned, tσ σ t) ∧
  execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) ∧
  execA (within_mmio_writable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t)

/-- Rocq `rrv_eq` (deviation: both sides are `8 * w` in Lean). -/
theorem rrvEq (w : Nat) : 8 * w = 8 * w := rfl

/-- The model's value of a `w`-byte read answered by `vs`. -/
def rrv (w : Nat) (vs : List (BitVec 8)) : BitVec (8 * w) := wordOfBytes w vs

theorem rrvPi (w : Nat) (vs : List (BitVec 8)) (e : 8 * w = 8 * w) :
    cast (congrArg BitVec e) (wordOfBytes w vs) = rrv w vs := rfl

/-- The bytes a `w`-byte plain write of `data` puts on the bus. -/
def AxDataX.wrb (w : Nat) (data : BitVec (8 * w)) : List (BitVec 8) :=
  WeakInterpProj.wbytes w data

theorem wrbPi (w : Nat) (data : BitVec (8 * w)) (e : 8 * w = 8 * w) :
    WeakInterpProj.wbytes w (cast (congrArg BitVec e) data) = AxDataX.wrb w data := rfl

/-- (Lean-only) Transport a predicate along an equation of its argument. -/
theorem AxDataX.substArg {α : Sort _} (P : α → Prop) {a b : α} (h : a = b) (hb : P b) : P a :=
  h ▸ hb

/-- **The kit** (Rocq: the section `kit`'s structural `Context` rules, bundled). -/
structure XKit (img : Image) (S : Type)
    (C : ∀ {X : Type}, (S → Sail.Error exception → ExecSt → Prop) → (S → X → ExecSt → Prop) →
      S → SailM X → ExecSt → Prop) : Prop where
  cMono : ∀ {X : Type} (QE QE' : S → Sail.Error exception → ExecSt → Prop)
    (Q Q' : S → X → ExecSt → Prop) (s : S) (m : SailM X) (t : ExecSt),
    (∀ s' e t', QE s' e t' → QE' s' e t') → (∀ s' x t', Q s' x t' → Q' s' x t') →
    C QE Q s m t → C QE' Q' s m t
  cRet : ∀ {X : Type} (QE : S → Sail.Error exception → ExecSt → Prop) (Q : S → X → ExecSt → Prop)
    (s : S) (x : X) (t : ExecSt), Q s x t → C QE Q s (pure x) t
  cBind : ∀ {X Y : Type} (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → Y → ExecSt → Prop) (m : SailM X) (f : X → SailM Y) (s : S) (t : ExecSt),
    C QE (fun s' x t' => C QE Q s' (f x) t') s m t → C QE Q s (m >>= f) t
  cTryCatch : ∀ {X : Type} (QE1 QE2 : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → X → ExecSt → Prop) (m : SailM X) (h : Sail.Error exception → SailM X) (s : S)
    (t : ExecSt),
    (∀ s' e t', QE1 s' e t' → C QE2 Q s' (h e) t') → C QE1 Q s m t →
    C QE2 Q s (PreSail.tryCatchAll m h) t
  cExt : ∀ {X : Type} (QE : S → Sail.Error exception → ExecSt → Prop) (Q : S → X → ExecSt → Prop)
    (s : S) (e : Sail.Error exception) (k : Empty → SailM X) (t : ExecSt),
    QE s e t → C QE Q s (.impure (.error e) k) t
  cRd : ∀ {X : Type} (QE : S → Sail.Error exception → ExecSt → Prop) (Q : S → X → ExecSt → Prop)
    (s : S) (r : Register) (k : RegisterType r → SailM X) (t : ExecSt),
    ¬ AxRunClose.pinReg r → C QE Q s (k (t.regs r)) t →
    C QE Q s (.impure (.ok (.regRead r)) k) t
  cWr : ∀ {X : Type} (QE : S → Sail.Error exception → ExecSt → Prop) (Q : S → X → ExecSt → Prop)
    (s : S) (r : Register) (v : RegisterType r) (k : PUnit → SailM X) (t : ExecSt),
    ¬ AxRunClose.pinReg r → C QE Q s (k PUnit.unit) (t.setReg r v) →
    C QE Q s (.impure (.ok (.regWrite r v)) k) t
  cEvA : ∀ {X : Type} (QE0 : Sail.Error exception → ExecSt → Prop) (Q0 : X → ExecSt → Prop)
    (QE : S → Sail.Error exception → ExecSt → Prop) (Q : S → X → ExecSt → Prop) (s : S)
    (m : SailM X) (t : ExecSt),
    (∀ e t', QE0 e t' → QE s e t') → (∀ x t', Q0 x t' → Q s x t') →
    EvA img QE0 Q0 m t → C QE Q s m t

section kit
variable {img : Image} {S : Type}
  {C : ∀ {X : Type}, (S → Sail.Error exception → ExecSt → Prop) → (S → X → ExecSt → Prop) →
    S → SailM X → ExecSt → Prop}
  (K : XKit img S C)
include K

theorem CBind0 {Y : Type} (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → Y → ExecSt → Prop) (m : SailM Unit) (n : SailM Y) (s : S) (t : ExecSt) :
    C QE (fun s' _ t' => C QE Q s' n t') s m t → C QE Q s (m >>= fun _ => n) t :=
  K.cBind QE Q m (fun _ => n) s t

theorem CLiftR {R X : Type} (QE' : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → X → ExecSt → Prop) (m : SailM X) (s : S) (t : ExecSt) :
    C (fun _ _ _ => False) Q s m t →
    C QE' (fun s' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q s' x t'
        | .error _ => False)
      s (ExceptT.run (liftM m : SailME R X)) t := by
  intro H
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  apply K.cBind
  exact K.cMono _ _ _ _ s m t (fun _ _ _ h => h.elim) (fun s' x t' h => K.cRet _ _ s' _ t' h) H

theorem CCatchEarlyReturn {X : Type} (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → X → ExecSt → Prop) (m : SailME X X) (s : S) (t : ExecSt) :
    C QE (fun s' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q s' x t'
        | .error (.inr x) => Q s' x t'
        | .error (.inl e) => QE s' e t')
      s (ExceptT.run m) t →
    C QE Q s (SailME.run m) t := by
  intro H
  show C QE Q s (ExceptT.run m >>= _) t
  apply K.cBind
  refine K.cMono _ _ _ _ s _ t (fun _ _ _ h => h) ?_ H
  intro s' r t' hr
  rcases r with (e | x) | x
  · exact K.cExt _ _ s' e _ t' hr
  · exact K.cRet _ _ s' x t' hr
  · exact K.cRet _ _ s' x t' hr

theorem CReadReg (QE : S → Sail.Error exception → ExecSt → Prop) (r : Register)
    (Q : S → RegisterType r → ExecSt → Prop) (s : S) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q s (t.regs r) t → C QE Q s (readReg r : SailM _) t :=
  fun hr hq => K.cRd QE Q s r _ t hr (K.cRet QE Q s _ t hq)

/-- An `execA` fact at the IMAGE state (the thread's registers, the image's memory) is a `C`
fact; the result and the registers are the run's. -/
theorem CExecA {X : Type} (Q : S → X → ExecSt → Prop) (σ : ExecSt) (m : SailM X) (x : X)
    (s1 : ExecSt) (s : S) (t : ExecSt) :
    img = imgOf σ →
    execA m ⟨t.regs, σ.mem, t.dev⟩ = some (x, s1) →
    Q s x ⟨s1.regs, t.mem, t.dev⟩ →
    C (fun _ (_ : Sail.Error exception) _ => False) Q s m t := by
  intro hi he hq
  subst hi
  have HE := execAEvA m _ x s1 he t rfl
  refine K.cEvA _ _ _ _ s m t (fun _ _ h => h.elim) ?_ HE
  rintro x' ⟨r', m', d'⟩ ⟨rfl, hr, hm, hd⟩
  simp only at hr hm hd
  subst hr hm hd
  exact hq

theorem CExecASame {X : Type} (Q : S → X → ExecSt → Prop) (σ : ExecSt) (m : SailM X) (x : X)
    (s : S) (t : ExecSt) :
    img = imgOf σ →
    execA m ⟨t.regs, σ.mem, t.dev⟩ = some (x, ⟨t.regs, σ.mem, t.dev⟩) →
    Q s x t → C (fun _ (_ : Sail.Error exception) _ => False) Q s m t :=
  fun hi he hq => CExecA K Q σ m x _ s t hi he hq

/-- Rocq `C_untilMT_1` (lean-sail `untilFuelM 1`), in the early-return monad. -/
theorem CUntilMT1 {R Vars : Type} (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → Except (Sail.Error exception ⊕ R) Vars → ExecSt → Prop) (vars : Vars)
    (cond : Vars → SailME R Bool) (body : Vars → SailME R Vars) (s : S) (t : ExecSt) :
    C QE (fun s' r t' => match r with
      | .ok v => C QE (fun s'' r' t'' => match r' with
          | .ok b => b = true ∧ Q s'' (.ok v) t''
          | .error e => Q s'' (.error e) t'') s' (ExceptT.run (cond v)) t'
      | .error e => Q s' (.error e) t') s (ExceptT.run (body vars)) t →
    C QE Q s (ExceptT.run (untilFuelM 1 cond vars body)) t := by
  intro Hb
  unfold untilFuelM untilFuelM.go
  rw [ExceptT.run_bind]
  apply K.cBind
  refine K.cMono _ _ _ _ s _ t (fun _ _ _ h => h) ?_ Hb
  intro s' r t' hr
  rcases r with e | v
  · exact K.cRet _ _ s' _ t' hr
  · show C QE Q s' (ExceptT.run (cond v >>= fun b => if b then pure v else _)) t'
    rw [ExceptT.run_bind]
    apply K.cBind
    refine K.cMono _ _ _ _ s' _ t' (fun _ _ _ h => h) ?_ hr
    intro s'' r' t'' hr'
    rcases r' with e | b
    · exact K.cRet _ _ s'' _ t'' hr'
    · obtain ⟨rfl, hq⟩ := hr'
      exact K.cRet _ _ s'' _ t'' hq

/-! ### (Lean-only) the stepping kit (Rocq's `x_step`/`x_go`/`x_use`/`x_useT`, as lemmas) -/

/-- (Lean-only) The early-return monad's bind, through `ExceptT.run`. -/
theorem AxDataX.cRBind {R X Y : Type} (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop) (m : SailME R Y)
    (f : Y → SailME R X) (s : S) (t : ExecSt) :
    C QE (fun s' r t' => match r with
      | .ok a => C QE Q s' (ExceptT.run (f a)) t'
      | .error e => Q s' (.error e) t') s (ExceptT.run m) t →
    C QE Q s (ExceptT.run (m >>= f)) t := by
  intro H
  rw [ExceptT.run_bind]
  apply K.cBind
  refine K.cMono _ _ _ _ s _ t (fun _ _ _ h => h) ?_ H
  intro s' r t' h
  cases r with
  | ok a => exact h
  | error e => exact K.cRet _ _ _ _ _ h

/-- (Lean-only) A lifted base-monad step, then the early-return continuation. -/
theorem AxDataX.cRLift {R X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {P : S → X → ExecSt → Prop} {Q : S → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {s : S} {t : ExecSt}
    (Hm : C (fun _ _ _ => False) P s m t)
    (Hf : ∀ s' x t', P s' x t' → C QE Q s' (ExceptT.run (f x)) t') :
    C QE Q s (ExceptT.run (liftM m >>= f)) t := by
  apply AxDataX.cRBind K
  refine K.cMono _ _ _ _ s _ t (fun _ _ _ h => h) ?_ (CLiftR K QE P m s t Hm)
  intro s' r t' h
  cases r with
  | ok a => exact Hf s' a t' h
  | error e => exact h.elim

/-- (Lean-only) A base-monad step, then the continuation. -/
theorem AxDataX.cFact {X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {P : S → X → ExecSt → Prop} {Q : S → Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {s : S} {t : ExecSt}
    (Hm : C (fun _ _ _ => False) P s m t)
    (Hf : ∀ s' x t', P s' x t' → C QE Q s' (f x) t') : C QE Q s (m >>= f) t :=
  K.cBind QE Q m f s t (K.cMono _ _ _ _ s m t (fun _ _ _ h => h.elim) Hf Hm)

theorem AxDataX.cFactRead {Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Y → ExecSt → Prop} {r : Register} {f : RegisterType r → SailM Y} {s : S}
    {t : ExecSt} (hr : ¬ AxRunClose.pinReg r) (H : C QE Q s (f (t.regs r)) t) :
    C QE Q s (readReg r >>= f) t :=
  K.cRd QE Q s r _ t hr H

theorem AxDataX.cFactPure {X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Y → ExecSt → Prop} {x : X} {f : X → SailM Y} {s : S} {t : ExecSt}
    (H : C QE Q s (f x) t) : C QE Q s (pure x >>= f) t := H

theorem AxDataX.cFactAssoc {X Y Z : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Z → ExecSt → Prop} {m : SailM X} {f : X → SailM Y} {g : Y → SailM Z} {s : S}
    {t : ExecSt} (H : C QE Q s (m >>= fun x => f x >>= g) t) : C QE Q s ((m >>= f) >>= g) t := by
  rw [bind_assoc]; exact H

theorem AxDataX.cRRead {R X : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {r : Register}
    {f : RegisterType r → SailME R X} {s : S} {t : ExecSt} (hr : ¬ AxRunClose.pinReg r)
    (H : C QE Q s (ExceptT.run (f (t.regs r))) t) :
    C QE Q s (ExceptT.run (liftM (readReg r) >>= f)) t :=
  AxDataX.cRLift K (P := fun s' x t' => s' = s ∧ x = t.regs r ∧ t' = t)
    (CReadReg K _ r _ s t hr ⟨rfl, rfl, rfl⟩) (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxDataX.cRPureBind {R X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {x : Y} {f : Y → SailME R X}
    {s : S} {t : ExecSt} (H : C QE Q s (ExceptT.run (f x)) t) :
    C QE Q s (ExceptT.run (pure x >>= f)) t := H

theorem AxDataX.cRAssoc {R X Y Z : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Except (Sail.Error exception ⊕ R) Z → ExecSt → Prop} {m : SailME R X}
    {f : X → SailME R Y} {g : Y → SailME R Z} {s : S} {t : ExecSt}
    (H : C QE Q s (ExceptT.run (m >>= fun x => f x >>= g)) t) :
    C QE Q s (ExceptT.run ((m >>= f) >>= g)) t := by
  rw [bind_assoc]; exact H

/-- (Lean-only) `pure` in the early-return monad. -/
theorem AxDataX.cRPure {R X : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {x : X} {s : S} {t : ExecSt}
    (H : Q s (.ok x) t) : C QE Q s (ExceptT.run (pure x : SailME R X)) t :=
  K.cRet _ _ _ _ _ H

/-- (Lean-only) Rocq `x_use σ H` in the early-return monad: an `execA` fact at the image state
that leaves it unchanged. -/
theorem AxDataX.cRUse {R X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop} {σ : ExecSt}
    {m : SailM X} {f : X → SailME R Y} {s : S} {t : ExecSt} {a : X}
    (hi : img = imgOf σ) (He : execA m (tσ σ t) = some (a, tσ σ t))
    (H : C QE Q s (ExceptT.run (f a)) t) : C QE Q s (ExceptT.run (liftM m >>= f)) t :=
  AxDataX.cRLift K (CExecASame K (fun s' x t' => s' = s ∧ x = a ∧ t' = t) σ m a s t hi He
    ⟨rfl, rfl, rfl⟩) (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- (Lean-only) Rocq `x_useT σ H` in the early-return monad: the registers change. -/
theorem AxDataX.cRUseT {R X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop} {σ : ExecSt}
    {m : SailM X} {f : X → SailME R Y} {s : S} {t s1 : ExecSt} {a : X}
    (hi : img = imgOf σ) (He : execA m (tσ σ t) = some (a, s1))
    (H : C QE Q s (ExceptT.run (f a)) ⟨s1.regs, t.mem, t.dev⟩) :
    C QE Q s (ExceptT.run (liftM m >>= f)) t :=
  AxDataX.cRLift K (CExecA K (fun s' x t' => s' = s ∧ x = a ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) σ m a
    s1 s t hi He ⟨rfl, rfl, rfl⟩) (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- (Lean-only) Rocq `x_use σ H` in the base monad. -/
theorem AxDataX.cFactUse {X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Y → ExecSt → Prop} {σ : ExecSt} {m : SailM X} {f : X → SailM Y} {s : S}
    {t : ExecSt} {a : X} (hi : img = imgOf σ) (He : execA m (tσ σ t) = some (a, tσ σ t))
    (H : C QE Q s (f a) t) : C QE Q s (m >>= f) t :=
  AxDataX.cFact K (CExecASame K (fun s' x t' => s' = s ∧ x = a ∧ t' = t) σ m a s t hi He
    ⟨rfl, rfl, rfl⟩) (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- (Lean-only) Rocq `x_useT σ H` in the base monad. -/
theorem AxDataX.cFactUseT {X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Y → ExecSt → Prop} {σ : ExecSt} {m : SailM X} {f : X → SailM Y} {s : S}
    {t s1 : ExecSt} {a : X} (hi : img = imgOf σ) (He : execA m (tσ σ t) = some (a, s1))
    (H : C QE Q s (f a) ⟨s1.regs, t.mem, t.dev⟩) : C QE Q s (m >>= f) t :=
  AxDataX.cFact K (CExecA K (fun s' x t' => s' = s ∧ x = a ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) σ m a
    s1 s t hi He ⟨rfl, rfl, rfl⟩) (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

/-- (Lean-only) A lifted base-monad tree ending a `SailME.run` block. -/
theorem AxDataX.cRLiftLast {X : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → X → ExecSt → Prop} {m : SailM X} {s : S} {t : ExecSt}
    (Hm : C (fun _ _ _ => False) Q s m t) :
    C QE (fun s' (r : Except (Sail.Error exception ⊕ X) X) t' =>
        match r with
        | .ok x => Q s' x t'
        | .error (.inr x) => Q s' x t'
        | .error (.inl e) => QE s' e t')
      s (ExceptT.run (liftM m : SailME X X)) t :=
  K.cMono _ _ _ _ s _ t (fun _ _ _ h => h) (fun s' r t' h => by
    rcases r with (e | x) | x
    · exact h.elim
    · exact h.elim
    · exact h) (CLiftR K QE Q m s t Hm)

/-- (Lean-only) An `EvA` fact with a determined result and state, then the continuation. -/
theorem AxDataX.cFactEvA {X Y : Type} {QE : S → Sail.Error exception → ExecSt → Prop}
    {Q : S → Y → ExecSt → Prop} {m : SailM X} {f : X → SailM Y} {s : S} {t t1 : ExecSt} {a : X}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t)
    (H : C QE Q s (f a) t1) : C QE Q s (m >>= f) t :=
  AxDataX.cFact K (K.cEvA _ (fun x t' => x = a ∧ t' = t1) (fun _ _ _ => False)
    (fun s' x t' => s' = s ∧ x = a ∧ t' = t1) s m t (fun _ _ h => h)
    (fun _ _ h => ⟨rfl, h.1, h.2⟩) Hm) (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

end kit

/-- Rocq `x_go` (file-qualified tactic name): run the register reads, `pure`s and re-associate
binds, in both monads.  `K` is the kit hypothesis. -/
macro "ax_datax_go " K:term : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxDataX.cRRead $K ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxDataX.cRPureBind $K ?_
  | with_reducible refine AxDataX.cRAssoc $K ?_
  | with_reducible refine AxDataX.cFactAssoc $K ?_
  | ((with_reducible refine AxDataX.cFactRead $K ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxDataX.cFactPure $K ?_))

/-! # 2. The read chain -/

section rd
variable {img : Image} {dok : Int → Nat → Prop} {S : Type}
  {C : ∀ {X : Type}, (S → Sail.Error exception → ExecSt → Prop) → (S → X → ExecSt → Prop) →
    S → SailM X → ExecSt → Prop}
  (K : XKit img S C) (pend : S → Prop) (srd : S → List (BitVec 8) → S)
  (CDrd : ∀ {X : Type} (QE : S → Sail.Error exception → ExecSt → Prop) (Q : S → X → ExecSt → Prop)
    (s : S) (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (t : ExecSt),
    pend s → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akIfetch = false → dok (paZ req.pa) n →
    (∀ vs : List (BitVec 8), vs.length = n → C QE Q (srd s vs) (k (.Ok (wordOfBytes n vs, none))) t) →
    C QE Q s (.impure (.ok (.memRead n va req)) k) t)
include K CDrd

/-- (Lean-only) The data node at any non-latest RAM read kind (the Lean model reads with
`Read_ifetch` / `Read_ttw` / `Read_plain` by access class; deviation 3). -/
theorem AxDataX.xReadRamK (rk : read_kind) (hrk : rk = .Read_plain ∨ rk = .Read_ttw)
    (w : Nat) (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (s : S) (t : ExecSt) :
    pend s → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q (srd s vs) (rrv w vs, default_meta) t) →
    C QE Q s (read_ram rk (.Physaddr pa) w false) t := by
  intro hp hdev hdok hq
  rcases hrk with rfl | rfl <;>
  · simp only [read_ram, PreSail.sail_mem_read, PreSail.emit]
    refine CDrd QE Q s w 64 _ _ t hp hdev rfl rfl hdok (fun vs hvs => ?_)
    exact K.cRet _ _ _ _ _ (hq vs hvs)

/-- THE DATA NODE. -/
theorem XReadRam (w : Nat) (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → (BitVec (8 * w) × Unit) → ExecSt → Prop) (pa : BitVec 64) (s : S) (t : ExecSt) :
    pend s → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q (srd s vs) (rrv w vs, default_meta) t) →
    C QE Q s (read_ram .Read_plain (.Physaddr pa) w false) t :=
  AxDataX.xReadRamK K pend srd CDrd _ (Or.inl rfl) w QE Q pa s t

section cmr
variable (σ : ExecSt) (himg : img = imgOf σ) (acc : MemoryAccessType mem_payload)
  (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
  (hacc : acc ≠ .InstructionFetch ())
include himg hw hacc

theorem XCheckedMemRead (Q : S → Result (BitVec (8 * w) × Unit) (physaddr × ExceptionType) → ExecSt → Prop)
    (s : S) (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tσ σ t)
      = some (.Ok pmaOkAligned, tσ σ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) →
    execA (within_mmio_readable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t) →
    pend s → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q (srd s vs) (.Ok (rrv w vs, default_meta)) t) →
    C (fun _ _ _ => False) Q s
      (checked_mem_read acc pbmt .Supervisor (.Physaddr pa) w false false false false) t := by
  intro hcp hpmp hmm hp hdev hdok hq
  unfold checked_mem_read
  apply CCatchEarlyReturn K
  refine AxDataX.cRAssoc K ?_
  refine AxDataX.cRUse K himg hcp ?_
  refine AxDataX.cRPureBind K ?_
  refine AxDataX.cRUse K himg (a := ((1 : Int), (w : Int))) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero]
  rcases hw with rfl | rfl | rfl | rfl
  all_goals
    cases acc <;> (try (rename_i p; cases p))
  all_goals try exact absurd rfl hacc
  all_goals
    simp only [read_kind_of_flags]
    first | refine AxDataX.cRUse K himg rfl ?_ | refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRAssoc K ?_
    refine AxDataX.cRBind K _ _ _ _ s t ?_
    refine CUntilMT1 K _ _ _ _ _ s t ?_
    refine AxDataX.cRUse K himg rfl ?_
    simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_one,
      Int.mul_one]
    refine AxDataX.cRUse K himg hpmp ?_
    dsimp only
    refine AxDataX.cRUse K himg hmm ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine AxDataX.cRAssoc K ?_
    refine AxDataX.cRLift K
      (P := fun s' x t' => ∃ vs : List (BitVec 8), vs.length = _ ∧ s' = srd s vs ∧
        x = (rrv _ vs, default_meta) ∧ t' = t)
      (AxDataX.xReadRamK K pend srd CDrd _ (by simp) _ _ _ pa s t hp hdev hdok
        (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRPure K ?_
    refine AxDataX.cRPure K ⟨rfl, ?_⟩
    refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRPure K ?_
    refine AxDataX.substArg (fun v => Q _ v _) ?_ (hq vs hvs)
    simp only [Result.Ok.injEq, Prod.mk.injEq, and_true, Nat.reduceMul, Int.reduceMul, Int.reduceAdd,
      Int.reduceSub, Int.reduceToNat, BitVec.setWidth_eq]
    try simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange]
    try bv_decide

theorem XMemRead (Q : S → Result (BitVec (8 * w)) (physaddr × ExceptionType) → ExecSt → Prop)
    (s : S) (t : ExecSt) :
    rdFacts σ acc pbmt w pa t → pend s → devAddr pa = false → dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q (srd s vs) (.Ok (rrv w vs)) t) →
    C (fun _ _ _ => False) Q s (mem_read acc pbmt (.Physaddr pa) w false false false) t := by
  rintro ⟨heff, hcp, hpmp, hmm⟩ hp hdev hdok hq
  unfold mem_read
  ax_datax_go K
  refine AxDataX.cFactUse K himg heff ?_
  unfold mem_read_priv mem_read_priv_meta
  ax_datax_go K
  refine AxDataX.cFact K (XCheckedMemRead K pend srd CDrd σ himg acc pbmt w pa hw hacc
    (fun s' r t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = srd s vs ∧
      r = .Ok (rrv w vs, default_meta) ∧ t' = t) s t hcp hpmp hmm hp hdev hdok
    (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
  rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
  ax_datax_go K
  exact K.cRet _ _ _ _ _ (hq vs hvs)

end cmr

/-- Translate (an `execA` fact: the Sv39 walk at the image) then read. -/
theorem XTranslateAndRead (σ : ExecSt) (himg : img = imgOf σ) (va pa : BitVec 64) (w : Nat)
    (Q : S → Result (physaddr × BitVec (8 * w)) ExecutionResult → ExecSt → Prop) (s : S)
    (t s1 : ExecSt) :
    vmemWidth w →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → pend s → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q (srd s vs) (.Ok (.Physaddr pa, rrv w vs)) ⟨s1.regs, t.mem, t.dev⟩) →
    C (fun _ _ _ => False) Q s
      (translate_and_read_value (.Virtaddr va) w (.Load .Data) false false false) t := by
  intro hw htr hrf hp hdev hdok hq
  unfold translate_and_read_value
  refine AxDataX.cFactUseT K himg htr ?_
  dsimp only
  refine AxDataX.cFact K (XMemRead K pend srd CDrd σ himg (.Load .Data) .PBMT_PMA w pa hw
    (by intro h; cases h) (fun s' r t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = srd s vs ∧
      r = .Ok (rrv w vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) s _ hrf hp hdev hdok
    (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
  rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
  dsimp only
  exact K.cRet _ _ _ _ _ (hq vs hvs)

theorem XVmemReadAddr (σ : ExecSt) (himg : img = imgOf σ) (va pa : BitVec 64) (w : Nat)
    (md : SATPMode) (Q : S → Result (BitVec (8 * w)) ExecutionResult → ExecSt → Prop) (s : S)
    (t s1 : ExecSt) :
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → pend s → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q (srd s vs) (.Ok (rrv w vs)) ⟨s1.regs, t.mem, t.dev⟩) →
    C (fun _ _ _ => False) Q s (vmem_read_addr (.Virtaddr va) w (.Load .Data) false false false) t := by
  intro hw hal heff htm htr hrf hp hdev hdok hq
  have hsp := splitOnPageBoundaryAlignedEq va w hw hal
  unfold vmem_read_addr
  simp only [bits_of_virtaddr, hsp, pure_bind, hal, Functions.not, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  apply CCatchEarlyReturn K
  ax_datax_go K
  refine AxDataX.cRUse K himg rfl ?_
  ax_datax_go K
  refine AxDataX.cRUse K himg heff ?_
  refine AxDataX.cRUse K himg htm ?_
  cases md <;>
  · dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57,
      Int.toNat_natCast, sys_misaligned_order_decreasing, Bool.false_and]
    refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRAssoc K ?_
    refine AxDataX.cRLift K (XTranslateAndRead K pend srd CDrd σ himg va pa w
      (fun s' r t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = srd s vs ∧
        r = .Ok (.Physaddr pa, rrv w vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) s t s1 hw htr hrf hp hdev hdok
      (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
    rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
    dsimp only
    refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRPure K ?_
    refine AxDataX.substArg (fun v => Q _ v _) ?_ (hq vs hvs)
    simp only [Result.Ok.injEq]
    rcases hw with rfl | rfl | rfl | rfl <;>
    · simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', BitVec.updateSubrange,
        zeros, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub, Int.reduceToNat, Nat.reduceSub,
        Nat.reduceAdd, BitVec.setWidth_eq]
      bv_decide

theorem XVmemRead (σ : ExecSt) (himg : img = imgOf σ) (rs1 : BitVec 5) (offset va pa : BitVec 64)
    (w : Nat) (md : SATPMode) (Q : S → Result (BitVec (8 * w)) ExecutionResult → ExecSt → Prop)
    (s : S) (t s1 : ExecSt) :
    execA (get_transformed_data_addr (.Regidx rs1) offset (.Load .Data) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → pend s → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w → Q (srd s vs) (.Ok (rrv w vs)) ⟨s1.regs, t.mem, t.dev⟩) →
    C (fun _ _ _ => False) Q s (vmem_read (.Regidx rs1) offset w (.Load .Data) false false false) t := by
  intro hgta hw hal heff htm htr hrf hp hdev hdok hq
  unfold vmem_read
  apply CCatchEarlyReturn K
  ax_datax_go K
  refine AxDataX.cRUse K himg hgta ?_
  dsimp only
  ax_datax_go K
  exact AxDataX.cRLiftLast K (XVmemReadAddr K pend srd CDrd σ himg va pa w md Q s t s1 hw hal heff htm
    htr hrf hp hdev hdok hq)

/-- THE LOAD: `execute (LOAD …)`, the data read DEMONIC, `rd :=` the extended value of the
answer (`rd ≠ x0`). -/
theorem XExecuteLOAD (σ : ExecSt) (himg : img = imgOf σ) (imm : BitVec 12) (rs1 rd : BitVec 5)
    (is_unsigned : Bool) (w : Nat) (va pa : BitVec 64) (md : SATPMode)
    (Q : S → ExecutionResult → ExecSt → Prop) (s : S) (t s1 : ExecSt) :
    w ≤ 8 → rd.toNat ≠ 0 →
    execA (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Load .Data) w)
      (tσ σ t) = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Load .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Load .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    rdFacts σ (.Load .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → pend s → devAddr pa = false →
    dok (paZ pa) w →
    (∀ vs : List (BitVec 8), vs.length = w →
      Q (srd s vs) RETIRE_SUCCESS
        ((⟨s1.regs, t.mem, t.dev⟩ : ExecSt).setGpr rd (extend_value is_unsigned (rrv w vs)))) →
    C (fun _ _ _ => False) Q s (execute (.LOAD (imm, .Regidx rs1, .Regidx rd, is_unsigned, w))) t := by
  intro hw8 _hrd hgta hw hal heff htm htr hrf hp hdev hdok hq
  show C _ Q s (execute_LOAD imm (.Regidx rs1) (.Regidx rd) is_unsigned w) t
  unfold execute_LOAD
  have h8 : (w ≤b Functions.xlen_bytes) = true := by
    simp only [Functions.xlen_bytes, decide_eq_true_eq]; omega
  simp only [h8]
  refine AxDataX.cFactUse K himg (execAAssertExpTrue _ _) ?_
  refine AxDataX.cFact K (XVmemRead K pend srd CDrd σ himg rs1 _ va pa w md
    (fun s' r t' => ∃ vs : List (BitVec 8), vs.length = w ∧ s' = srd s vs ∧
      r = .Ok (rrv w vs) ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) s t s1 hgta hw hal heff htm htr hrf hp hdev
    hdok (fun vs hvs => ⟨vs, hvs, rfl, rfl, rfl⟩)) ?_
  rintro s' x t' ⟨vs, hvs, rfl, rfl, rfl⟩
  dsimp only
  refine AxDataX.cFactEvA K (rf0EvA img _ _ (rf0WXBits rd _) _ _ _ (execWXBitsGpr rd _ _)) ?_
  exact K.cRet _ _ _ _ _ (hq vs hvs)

end rd

/-! # 3. The write chain -/

/-- (Lean-only) The model's stored word of `execute_STORE` at width `w`: the low `w` bytes of the
source register (Rocq `autocast (subrange_vec_dec v2 (w * 8 - 1) 0)`). -/
def AxDataX.stData (w : Nat) (v2 : BitVec 64) : BitVec (8 * w) :=
  BitVec.setWidth (8 * w) (Sail.BitVec.extractLsb v2 ((w : Int) * 8 - 1).toNat 0)

/-- The plain access kind of `write_ram Write_plain`. -/
def AxDataX.akPlain : AK := .AK_explicit ⟨.AV_plain, .AS_normal⟩

section wr
variable {img : Image} {dok : Int → Nat → Prop} {S : Type}
  {C : ∀ {X : Type}, (S → Sail.Error exception → ExecSt → Prop) → (S → X → ExecSt → Prop) →
    S → SailM X → ExecSt → Prop}
  (K : XKit img S C) (pend : S → Prop) (swr : S → List (BitVec 8) → AK → S)
  (CDwr : ∀ {X : Type} (QE : S → Sail.Error exception → ExecSt → Prop) (Q : S → X → ExecSt → Prop)
    (s : S) (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X) (t : ExecSt) (v : BitVec (8 * n)),
    pend s → devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    dok (paZ req.pa) n → req.value = some v →
    C QE Q (swr s (WeakInterpProj.wbytes n v) req.access_kind) (k (.Ok (some true))) t →
    C QE Q s (.impure (.ok (.memWrite n va req)) k) t)
include K CDwr

theorem XWriteRam (w : Nat) (QE : S → Sail.Error exception → ExecSt → Prop)
    (Q : S → Bool → ExecSt → Prop) (pa : BitVec 64) (data : BitVec (8 * w)) (s : S) (t : ExecSt) :
    pend s → devAddr pa = false → dok (paZ pa) w →
    Q (swr s (AxDataX.wrb w data) AxDataX.akPlain) true t →
    C QE Q s (write_ram .Write_plain (.Physaddr pa) w data ()) t := by
  intro hp hdev hdok hq
  simp only [write_ram, PreSail.sail_mem_write, PreSail.emit]
  refine CDwr QE Q s w 64 _ _ t data hp hdev rfl hdok rfl ?_
  exact K.cRet _ _ _ _ _ hq

section cmw
variable (σ : ExecSt) (himg : img = imgOf σ) (acc : MemoryAccessType mem_payload)
  (pbmt : page_based_mem_type) (w : Nat) (pa : BitVec 64) (hw : vmemWidth w)
include himg hw

theorem XCheckedMemWrite (data : BitVec (8 * w))
    (Q : S → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (s : S) (t : ExecSt) :
    execA (check_pma_with_pmp_priority acc pbmt .Supervisor (.Physaddr pa) w false) (tσ σ t)
      = some (.Ok pmaOkAligned, tσ σ t) →
    execA (pmpCheck (.Physaddr pa) w acc .Supervisor) (tσ σ t) = some (none, tσ σ t) →
    execA (within_mmio_writable (.Physaddr pa) w) (tσ σ t) = some (false, tσ σ t) →
    pend s → devAddr pa = false → dok (paZ pa) w →
    Q (swr s (AxDataX.wrb w data) AxDataX.akPlain) (.Ok true) t →
    C (fun _ _ _ => False) Q s
      (checked_mem_write (.Physaddr pa) w data acc pbmt .Supervisor () false false false) t := by
  intro hcp hpmp hmm hp hdev hdok hq
  unfold checked_mem_write
  apply CCatchEarlyReturn K
  refine AxDataX.cRAssoc K ?_
  refine AxDataX.cRUse K himg hcp ?_
  refine AxDataX.cRPureBind K ?_
  refine AxDataX.cRUse K himg (a := ((1 : Int), (w : Int))) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxDataX.cRUse K himg rfl ?_
  refine AxDataX.cRBind K _ _ _ _ s t ?_
  refine CUntilMT1 K _ _ _ _ _ s t ?_
  refine AxDataX.cRUse K himg rfl ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxDataX.cRUse K himg hpmp ?_
  dsimp only
  refine AxDataX.cRAssoc K ?_
  refine AxDataX.cRUse K himg hmm ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine AxDataX.cRAssoc K ?_
  refine AxDataX.cRLift K (P := fun s' b t' => s' = swr s (AxDataX.wrb w _) AxDataX.akPlain ∧
      b = true ∧ t' = t)
    (XWriteRam K pend swr CDwr w _ _ pa _ s t hp hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  refine AxDataX.cRPureBind K ?_
  refine AxDataX.cRPure K ?_
  refine AxDataX.cRPure K ⟨rfl, ?_⟩
  refine AxDataX.cRPure K ?_
  refine AxDataX.substArg (fun z => Q (swr s z AxDataX.akPlain) _ _) ?_ hq
  refine congrArg (AxDataX.wrb w) ?_
  rcases hw with rfl | rfl | rfl | rfl <;>
  · simp only [Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub,
      Int.reduceToNat, Int.reduceAdd, Nat.reduceMul]
    bv_decide

theorem XMemWriteValue (data : BitVec (8 * w))
    (Q : S → Result Bool (physaddr × ExceptionType) → ExecSt → Prop) (s : S) (t : ExecSt) :
    wrFacts σ acc pbmt w pa t → pend s → devAddr pa = false → dok (paZ pa) w →
    Q (swr s (AxDataX.wrb w data) AxDataX.akPlain) (.Ok true) t →
    C (fun _ _ _ => False) Q s (mem_write_value (.Physaddr pa) w data acc pbmt false false false) t := by
  rintro ⟨heff, hcp, hpmp, hmm⟩ hp hdev hdok hq
  unfold mem_write_value mem_write_value_meta
  ax_datax_go K
  refine AxDataX.cFactUse K himg heff ?_
  unfold mem_write_value_priv_meta
  ax_datax_go K
  refine AxDataX.cFact K (XCheckedMemWrite K pend swr CDwr σ himg acc pbmt w pa hw data
    (fun s' r t' => s' = swr s (AxDataX.wrb w data) AxDataX.akPlain ∧ r = .Ok true ∧ t' = t) s t
    hcp hpmp hmm hp hdev hdok ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  ax_datax_go K
  exact K.cRet _ _ _ _ _ hq

omit CDwr hw in
/-- `mem_write_ea`: register-only (PMA/PMP checks, the split loop's address announcement). -/
theorem XMemWriteEa (Q : S → Result Unit (physaddr × ExceptionType) → ExecSt → Prop) (s : S)
    (t : ExecSt) :
    wrFacts σ acc pbmt w pa t → Q s (.Ok ()) t →
    C (fun _ _ _ => False) Q s (mem_write_ea (.Physaddr pa) w acc pbmt false false false) t := by
  rintro ⟨heff, hcp, hpmp, _⟩ hq
  unfold mem_write_ea
  apply CCatchEarlyReturn K
  ax_datax_go K
  refine AxDataX.cRUse K himg heff ?_
  ax_datax_go K
  refine AxDataX.cRUse K himg hcp ?_
  ax_datax_go K
  refine AxDataX.cRUse K himg (a := ((1 : Int), (w : Int))) rfl ?_
  simp only [misaligned_order, sys_misaligned_order_decreasing, ↓reduceIte, Bool.false_eq_true,
    Int.reduceSub, Int.toNat_zero, write_kind_of_flags]
  refine AxDataX.cRUse K himg rfl ?_
  refine AxDataX.cRBind K _ _ _ _ s t ?_
  refine CUntilMT1 K _ _ _ _ _ s t ?_
  refine AxDataX.cRUse K himg rfl ?_
  simp only [bits_of_physaddr, Int.cast_ofNat_Int, Int.zero_mul, addIntZero, Int.toNat_natCast]
  refine AxDataX.cRUse K himg hpmp ?_
  dsimp only
  refine AxDataX.cRPure K ?_
  refine AxDataX.cRPure K ⟨rfl, ?_⟩
  refine AxDataX.cRPure K ?_
  exact hq

end cmw
theorem XVmemWriteAddr (σ : ExecSt) (himg : img = imgOf σ) (va pa : BitVec 64) (w : Nat)
    (data : BitVec (8 * w)) (md : SATPMode)
    (Q : S → Result Bool ExecutionResult → ExecSt → Prop) (s : S) (t s1 : ExecSt) :
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → pend s → devAddr pa = false →
    dok (paZ pa) w →
    Q (swr s (AxDataX.wrb w data) AxDataX.akPlain) (.Ok true) ⟨s1.regs, t.mem, t.dev⟩ →
    C (fun _ _ _ => False) Q s
      (vmem_write_addr (.Virtaddr va) w data (.Store .Data) false false false) t := by
  intro hw hal heff htm htr hwf hp hdev hdok hq
  have hsp := splitOnPageBoundaryAlignedEq va w hw hal
  unfold vmem_write_addr
  simp only [bits_of_virtaddr, hsp, pure_bind, hal, Functions.not, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  apply CCatchEarlyReturn K
  ax_datax_go K
  refine AxDataX.cRUse K himg rfl ?_
  ax_datax_go K
  refine AxDataX.cRUse K himg heff ?_
  refine AxDataX.cRUse K himg htm ?_
  cases md <;>
  · dsimp only [iteNoSplitBare, iteNoSplitSv32, iteNoSplitSv39, iteNoSplitSv48, iteNoSplitSv57,
      Int.toNat_natCast, sys_misaligned_order_decreasing, Bool.false_and]
    refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRAssoc K ?_
    refine AxDataX.cRUseT K himg htr ?_
    dsimp only
    refine AxDataX.cRAssoc K ?_
    refine AxDataX.cRUse K himg rfl ?_
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine AxDataX.cRAssoc K ?_
    refine AxDataX.cRLift K (XMemWriteEa K σ himg (.Store .Data) .PBMT_PMA w pa
      (fun s' r t' => s' = s ∧ r = .Ok () ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) s _ hwf ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨hs, rfl, rfl⟩
    subst s'
    dsimp only
    refine AxDataX.cRAssoc K ?_
    refine AxDataX.cRLift K (XMemWriteValue K pend swr CDwr σ himg (.Store .Data) .PBMT_PMA w pa hw _
      (fun s' r t' => s' = swr s (AxDataX.wrb w _) AxDataX.akPlain ∧ r = .Ok true ∧
        t' = ⟨s1.regs, t.mem, t.dev⟩) s _ hwf hp hdev hdok ⟨rfl, rfl, rfl⟩) ?_
    rintro s' x t' ⟨rfl, rfl, rfl⟩
    dsimp only
    refine AxDataX.cRPureBind K ?_
    refine AxDataX.cRPure K ?_
    refine AxDataX.substArg (fun z => Q (swr s z AxDataX.akPlain) _ _) ?_ hq
    refine congrArg (AxDataX.wrb w) ?_
    rcases hw with rfl | rfl | rfl | rfl <;>
    · simp only [Sail.BitVec.extractLsb, Int.cast_ofNat_Int, Int.reduceMul, Int.reduceSub,
        Int.reduceToNat, Nat.reduceMul]
      bv_decide

theorem XVmemWrite (σ : ExecSt) (himg : img = imgOf σ) (rs1 : BitVec 5) (offset va pa : BitVec 64)
    (w : Nat) (data : BitVec (8 * w)) (md : SATPMode)
    (Q : S → Result Bool ExecutionResult → ExecSt → Prop) (s : S) (t s1 : ExecSt) :
    execA (get_transformed_data_addr (.Regidx rs1) offset (.Store .Data) w) (tσ σ t)
      = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → pend s → devAddr pa = false →
    dok (paZ pa) w →
    Q (swr s (AxDataX.wrb w data) AxDataX.akPlain) (.Ok true) ⟨s1.regs, t.mem, t.dev⟩ →
    C (fun _ _ _ => False) Q s
      (vmem_write (.Regidx rs1) offset w data (.Store .Data) false false false) t := by
  intro hgta hw hal heff htm htr hwf hp hdev hdok hq
  unfold vmem_write
  apply CCatchEarlyReturn K
  ax_datax_go K
  refine AxDataX.cRUse K himg hgta ?_
  dsimp only
  ax_datax_go K
  exact AxDataX.cRLiftLast K (XVmemWriteAddr K pend swr CDwr σ himg va pa w data md Q s t s1 hw hal
    heff htm htr hwf hp hdev hdok hq)

/-- THE STORE: `execute (STORE …)`: the data write of rs2's low `w` bytes, no GPR written. -/
theorem XExecuteSTORE (σ : ExecSt) (himg : img = imgOf σ) (imm : BitVec 12) (rs2 rs1 : BitVec 5)
    (w : Nat) (va pa : BitVec 64) (md : SATPMode)
    (Q : S → ExecutionResult → ExecSt → Prop) (s : S) (t s1 : ExecSt) :
    w ≤ 8 →
    execA (get_transformed_data_addr (.Regidx rs1) (sign_extend (m := 64) imm) (.Store .Data) w)
      (tσ σ t) = some (.Ext_DataAddr_OK (.Virtaddr va), tσ σ t) →
    vmemWidth w →
    is_aligned_vaddr (.Virtaddr va) w = true →
    execA (effectivePrivilege (.Store .Data) (t.regs .mstatus) (t.regs .cur_privilege)) (tσ σ t)
      = some (.Supervisor, tσ σ t) →
    execA (translationMode .Supervisor) (tσ σ t) = some (md, tσ σ t) →
    execA (translateAddr (.Virtaddr va) (.Store .Data)) (tσ σ t)
      = some (.Ok (.Physaddr pa, .PBMT_PMA, ()), s1) →
    wrFacts σ (.Store .Data) .PBMT_PMA w pa ⟨s1.regs, t.mem, t.dev⟩ → pend s → devAddr pa = false →
    dok (paZ pa) w →
    Q (swr s (AxDataX.wrb w (AxDataX.stData w (t.gpr rs2))) AxDataX.akPlain) RETIRE_SUCCESS
      ⟨s1.regs, t.mem, t.dev⟩ →
    C (fun _ _ _ => False) Q s (execute (.STORE (imm, .Regidx rs2, .Regidx rs1, w))) t := by
  intro hw8 hgta hw hal heff htm htr hwf hp hdev hdok hq
  show C _ Q s (execute_STORE imm (.Regidx rs2) (.Regidx rs1) w) t
  unfold execute_STORE
  have h8 : (w ≤b Functions.xlen_bytes) = true := by
    simp only [Functions.xlen_bytes, decide_eq_true_eq]; omega
  simp only [h8]
  refine AxDataX.cFactUse K himg (execAAssertExpTrue _ _) ?_
  refine AxDataX.cFactEvA K (rf0EvA img _ _ (rf0RXBits rs2) _ _ _ (execRXBitsGpr rs2 t)) ?_
  refine AxDataX.cFactPure K ?_
  refine AxDataX.cFact K (XVmemWrite K pend swr CDwr σ himg rs1 _ va pa w
    (AxDataX.stData w (t.gpr rs2)) md
    (fun s' r t' => s' = swr s (AxDataX.wrb w (AxDataX.stData w (t.gpr rs2))) AxDataX.akPlain ∧
      r = .Ok true ∧ t' = ⟨s1.regs, t.mem, t.dev⟩) s t s1 hgta hw hal heff htm htr hwf hp hdev hdok
    ⟨rfl, rfl, rfl⟩) ?_
  rintro s' x t' ⟨rfl, rfl, rfl⟩
  dsimp only
  exact K.cRet _ _ _ _ _ hq

end wr

end Weak
