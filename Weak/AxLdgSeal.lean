/-
Weak: **the "CONCRETE-CONTROL, SYMBOLIC-DATA" ledger kit** (Rocq: the sealed-data-operation
variant).  The per-hart engine for kernel code: ONE whole-instruction `wpd` (`riscvStep tick`,
boundary → fetch → post-fetch → `Ret`) at a pc with CONCRETE control registers (the `base`
register file: priv, misa, mstatus, pmp/pma, PC, …) and a SYMBOLIC data register file restricted
to a declared list `gs` of 64-bit registers (GPRs, or counters such as `minstret`/`mip`), valid
for ALL values of those registers and from ANY register file agreeing with `base` on the step's
upward-exposed read set `A` minus `gs`.

Rocq: `iris/AxLdgSeal.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 the reference state `ldgRef base gs xs` (`base` with `gs := xs`); `agreeLdg`: a caller's `rs`
agreeing with `base` on `A ∖ syms gs` agrees with `ldgRef base gs (lookups rs gs)` on all of `A`
(the symbolic values are INSTANTIATED by the caller's own register values).  §2 the post kit
`ldgPost pcn obs`: PC = `pcn` and each observed register has the given unsigned value, compared
with the SEALED `zeqb`.  §3 the ledger `LdgFacts` (∀ `xs` of the right length, the tracked
`CjrFrameFacts` at the reference state), the engine `wpdLdg` (= `wpdCjrFrameGen` ∘ `agreeLdg`),
the sanity lemma `ldgInvReachesRet`, and the tick = true twins over `CjrTickFrameFacts`.  §4 the
footprint sets for register-only code and the `A` tracer `upx`/`AOf`.  §5 the seals and the
ledger tactics.  §6 equation lemmas for the sealed operations.

Rocq's measurements (why seal): under `vm_compute` the RUN on a symbolic word is cheap; the
READBACK of a wrapped value (`bv_wrap` = `Z.modulo` under binders) explodes, so the data
operations are generalised to variables once the executed `execute_*` body is unfolded, and the
post is stated with the SAME model operation.  COVERAGE (Rocq): OP / OP-IMM / OP-32 / OP-IMM-32
incl. slt/sltu and compressed forms executing as one of them, both tick bits, any number of
symbolic registers.  NOT covered: control on symbolic data (branches, jalr's target beyond
`AxEpiCjrSym`'s low-bit split, loads/stores: a symbolic ADDRESS reaches translation/PMA).

## The Lean method

The kernel has no readback: `Kernel.whnf` of the ledger with the source values free stops only
at a stuck application in head position, and the post leaves `E a b` (`zeqb` generalised to `E`,
as Rocq) are closed by `AxEpiCjrFrame.kloopCore` (`ax_epi_cjr_frame_kloop`), the kernel checking
`a ≡ b` lazily (same head ⇒ arguments first, so `x + c'` meets `x + c` with `c' ≡ c` concrete).
So in Lean the seals are NOT needed: measured (scratch run, not kept) `ax_ldg_seal_solve
(unfold post) (skip)` closes addi (`[x5]`), add (`[x5, x6]`), addiw (32-bit wrap + sign
extension) and, by `ax_ldg_seal_solve_tick`, addi with `[x5, minstret, mcycle]` symbolic; about
4 s of tactic per branch and 20–60 s of kernel check per ledger.  The seals are ported
(`ax_ldg_seal_alu`/`ext`/`cmp`/`all`) and harmless (addi with `ax_ldg_seal_alu` after unfolding
`execute_ITYPE` also closes: the leaf meets as `E (ADD x c') (ADD x c)`).  A WRONG post (addi
with immediate 8) is rejected by the KERNEL at the declaration ("application type mismatch"),
not at tactic time: `kloopCore` builds the `false` arm without checking `a ≡ b`.

## Deviations from Rocq

1. Two pins / Stage C (as `AxEpiCjrFrame` deviations 1–2): the engines take `Hgd` as
   `AxCjrWpd.fetchImgOk`, drop `Hflow`/`Hloc`, state `RetS`/`RetP` at `kk` (Rocq `S kk`), are
   generic in `hlc` (Rocq `HasNoLc`).  `DLdg` and `AOfT` remove BOTH pins (Rocq only
   `sig_seip`; in Lean `sig_meip` is a pin answered by the walk, never read from the file, cf.
   `AxEpiCjrFrame` deviation 3); `DrLdg` is over `AxEpiProbe.drNopin` (Rocq `Dr_noseip`).
2. TYPES: Rocq `w64r` (Sail's enumeration of the 64-bit registers) ↦ the structure `W64r`
   (a register with a proof that its type is `BitVec 64`; lookup/set through `cast`, which the
   kernel reduces by K); `R_bitvector_64` ↦ `W64r.reg`; Rocq `PC` as a `w64r` ↦ Lean-only
   `AxLdgSeal.pcR`; `gset register` ↦ `List Register` (`A ∖ syms gs` ↦ `A.filter (· ∉ syms gs)`,
   `{[PC]} ∪ syms gs` ↦ `.PC :: syms gs`, `list_to_set l ∖ {[…]}` ↦ `List.filter`); `mword 64`
   ↦ `BitVec 64`; `Z` ↦ `Int` (`bv_unsigned` ↦ `toNat` cast to `Int`); `Z.eqb` ↦ `decide`;
   `forallb` ↦ `List.all`; `Forall` ↦ `∀ p ∈ obs`; `regstate`/`mstate` ↦ `RegFile`/`ExecSt`,
   `gmap pa (bv 8)` ↦ `BMap`, `dev0_state` ↦ `testDevs`; `zip`/`foldr` as Rocq.
3. `upx` (as `AxEpiProbe.ftp`, deviation 3 there): the RAM read answers `.Ok (w, none)` from
   `bmRead`; `.error`, `memWrite`, `choose` and the legacy RAM events give `none`; `barrier`
   continues (as Rocq).  `memAt` is a `find?` byte map (Rocq `list_to_map ∘ imap`).
4. §6: `bv_wrap 64 z` ↦ `z % 2 ^ 64` over `Int`; `Z.land`/`Z.lor` ↦ the `Nat` operations
   (both arguments are non-negative), cast to `Int`.
5. TACTICS (Rocq `Ltac` ↦ Lean macros, file-prefixed): `ldg_split_xs` ↦ `ax_ldg_seal_split_xs`
   (by the Lean-only `AxLdgSeal.forallLenZero`/`forallLenSucc`), `ldg_unfold_step` ↦
   `ax_ldg_seal_unfold_step`, `ldg_close` ↦ `ax_ldg_seal_close` (generalise `zeqb`, then
   `ax_epi_cjr_frame_kloop`), `ldg_seal_alu`/`ext`/`cmp`/`all` ↦ `ax_ldg_seal_alu`/`ext`/`cmp`/
   `all` (generalising the Lean model's `+`/`-`/`&&&`/`|||`/`^^^`/`shift_bits_*`,
   `Sail.BitVec.extractLsb`/`sign_extend`/`zero_extend`, `zopz0zI_s`/`zopz0zI_u` at width 64),
   `ldg_solve unf seal` ↦ `ax_ldg_seal_solve (unf) (seal)`, `ldg_solve_tick` ↦
   `ax_ldg_seal_solve_tick`.  `vm_compute; reflexivity` ↦ `decide +kernel` (closed fields) and
   `ax_epi_ledger_krfl` (the boundary walk, free words).  The tick = false ledger has the
   Lean `cfHead` and the `…MeipDr`/`…MeipD` fields and four branch fields.

**Rocq → Lean name map.**  `w64r` `W64r`, `set64` `set64`, `ldg_ref` `ldgRef`, `syms` `syms`,
`lookups` `lookups`, `lookups_length` `lookupsLength`, `agree_ldg` `agreeLdg`, `ldg_state`
`ldgState`, `zeqb` `zeqb`, `zeqb_refl` `zeqbRefl`, `zeqb_true` `zeqbTrue`, `obs64` `obs64`,
`ldg_post` `ldgPost`, `P_regs` `PRegs`, `ldg_post_local` `ldgPostLocal`, `ldg_post_spec`
`ldgPostSpec`, `LdgFacts` `LdgFacts`, `ldg_inv_reaches_ret` `ldgInvReachesRet`, `wpd_ldg`
`wpdLdg`, `LdgFactsT` `LdgFactsT`, `ldg_inv_reaches_ret_tick` `ldgInvReachesRetTick`,
`wpd_ldg_tick` `wpdLdgTick`, `gprs_all` `gprsAll`, `Dr_ldg` `DrLdg`, `Dw_ldg` `DwLdg`, `D_ldg`
`DLdg`, `upx` `upx`, `mem_at` `memAt`, `A_of_t` `AOfT`, `A_of` `AOf`, `add_vec_unsigned`
`addVecUnsigned`, `sub_vec_unsigned` `subVecUnsigned`, `and_vec_unsigned` `andVecUnsigned`,
`or_vec_unsigned` `orVecUnsigned`; tactics as deviation 5.  None is in the duplicated-name
table.  Lean-only (file-qualified): `AxLdgSeal.pcR`, `AxLdgSeal.castCast`,
`AxLdgSeal.forallLenZero`, `AxLdgSeal.forallLenSucc`.

**Dropped:** nothing (Rocq 34 definitions/lemmas + 9 Ltac; Lean 34 + 9 macros + 4 Lean-only).
`Set Printing Depth` has no twin.
-/
import Weak.AxEpiCjrFrame

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The reference state -/

/-- Rocq `w64r`: a register whose type is `BitVec 64`. -/
structure W64r where
  reg : Register
  isW : RegisterType reg = BitVec 64

/-- (Lean-only) Rocq `PC` as a `w64r`. -/
def AxLdgSeal.pcR : W64r := ⟨.PC, rfl⟩

/-- Rocq `set64`. -/
def set64 (ps : List (W64r × BitVec 64)) (rs : RegFile) : RegFile :=
  ps.foldr (fun p rs => rs.set p.1.reg (cast p.1.isW.symm p.2)) rs

/-- Rocq `ldg_ref`. -/
def ldgRef (base : RegFile) (gs : List W64r) (xs : List (BitVec 64)) : RegFile :=
  set64 (gs.zip xs) base

/-- Rocq `syms`. -/
def syms (gs : List W64r) : List Register := gs.map W64r.reg

/-- Rocq `lookups`. -/
def lookups (rs : RegFile) (gs : List W64r) : List (BitVec 64) :=
  gs.map fun g => cast g.isW (rs g.reg)

theorem lookupsLength (rs : RegFile) (gs : List W64r) : (lookups rs gs).length = gs.length := by
  simp [lookups]

/-- (Lean-only) The two casts cancel. -/
theorem AxLdgSeal.castCast {α β : Type} (h : α = β) (a : α) : cast h.symm (cast h a) = a := by
  subst h; rfl

theorem agreeLdg (A : List Register) (base rs : RegFile) (gs : List W64r) :
    agreeOn (A.filter fun r => !decide (r ∈ syms gs)) rs base →
    agreeOn A rs (ldgRef base gs (lookups rs gs)) := by
  induction gs generalizing A with
  | nil =>
    intro H r Hr
    exact H r (List.mem_filter.2 ⟨Hr, by simp [syms]⟩)
  | cons g gs IH =>
    intro H r Hr
    show rs r = (set64 (gs.zip (lookups rs gs)) base).set g.reg
      (cast g.isW.symm (cast g.isW (rs g.reg))) r
    by_cases he : r = g.reg
    · subst he
      rw [RegFile.set_same, AxLdgSeal.castCast]
    · rw [RegFile.set_other _ _ _ _ he]
      refine IH (A.filter fun r => !decide (r = g.reg)) ?_ r
        (List.mem_filter.2 ⟨Hr, by simp [he]⟩)
      intro r' Hr'
      apply H r'
      simp only [List.mem_filter, syms, List.map_cons, List.mem_cons, Bool.not_eq_true',
        decide_eq_false_iff_not, not_or] at Hr' ⊢
      exact ⟨Hr'.1.1, Hr'.1.2, Hr'.2⟩

/-- Rocq `ldg_state`. -/
def ldgState (mem : BMap) (base : RegFile) (gs : List W64r) (xs : List (BitVec 64)) : ExecSt :=
  ⟨ldgRef base gs xs, mem, testDevs⟩

/-! # 2. The post kit -/

/-- Rocq `zeqb`: sealed `Z.eqb`, generalised to a variable by `ax_ldg_seal_close`. -/
def zeqb (a b : Int) : Bool := decide (a = b)

theorem zeqbRefl (a : Int) : zeqb a a = true := by simp [zeqb]

theorem zeqbTrue (a b : Int) : zeqb a b = true ↔ a = b := by simp [zeqb]

/-- Rocq `obs64`: the unsigned value of a 64-bit register. -/
def obs64 (r : W64r) (rs : RegFile) : Int := ((cast r.isW (rs r.reg)).toNat : Int)

/-- Rocq `ldg_post`: PC = `pcn` and every observed register has the given unsigned value. -/
def ldgPost (pcn : Int) (obs : List (W64r × Int)) (rs : RegFile) : Bool :=
  zeqb (obs64 AxLdgSeal.pcR rs) pcn && obs.all fun p => zeqb (obs64 p.1 rs) p.2

/-- Rocq `P_regs`: the post's footprint, PC and the observed registers. -/
def PRegs (gs : List W64r) : List Register := .PC :: syms gs

theorem ldgPostLocal (pcn : Int) (obs : List (W64r × Int)) :
    postLocal (PRegs (obs.map Prod.fst)) (ldgPost pcn obs) := by
  intro rs rs' H
  have hpc : obs64 AxLdgSeal.pcR rs = obs64 AxLdgSeal.pcR rs' := by
    show ((cast rfl (rs .PC)).toNat : Int) = ((cast rfl (rs' .PC)).toNat : Int)
    rw [H .PC (List.mem_cons_self ..)]
  have ho : ∀ p ∈ obs, obs64 p.1 rs = obs64 p.1 rs' := by
    intro p hp
    unfold obs64
    rw [H p.1.reg (List.mem_cons_of_mem _ (List.mem_map.2
      ⟨p.1, List.mem_map.2 ⟨p, hp, rfl⟩, rfl⟩))]
  unfold ldgPost
  rw [hpc]
  congr 1
  clear H hpc
  induction obs with
  | nil => rfl
  | cons p obs IH =>
    simp only [List.all_cons]
    rw [ho p (List.mem_cons_self ..), IH (fun q hq => ho q (List.mem_cons_of_mem _ hq))]

theorem ldgPostSpec (pcn : Int) (obs : List (W64r × Int)) (rs : RegFile) :
    ldgPost pcn obs rs = true ↔ obs64 AxLdgSeal.pcR rs = pcn ∧ ∀ p ∈ obs, obs64 p.1 rs = p.2 := by
  simp [ldgPost, zeqb, List.all_eq_true]

/-! # 3. The ledger and the engine -/

/-- THE LEDGER (Rocq `LdgFacts`): for every value list `xs` (one word per symbolic register),
the tracked facts at the reference state. -/
def LdgFacts (mem : BMap) (base : RegFile) (gs : List W64r) (A Dr Dw D : List Register)
    (pc : Int) (vs : List (BitVec 8)) (P : List Register)
    (post : List (BitVec 64) → RegFile → Bool) : Prop :=
  ∀ xs, xs.length = gs.length → CjrFrameFacts (ldgState mem base gs xs) A Dr Dw D pc vs P (post xs)

/-- SANITY (non-vacuity): every row-end state of the ledger at the CALLER's register file runs to
a `Ret` satisfying the post. -/
theorem ldgInvReachesRet (mem : BMap) (base : RegFile) (gs : List W64r)
    (A Dr Dw D : List Register) (pc : Int) (vs : List (BitVec 8)) (P : List Register)
    (post : List (BitVec 64) → RegFile → Bool) (rs : RegFile) (cpu : CPU) (kk : Nat)
    (s1 : Athread) :
    LdgFacts mem base gs A Dr Dw D pc vs P post →
    (∀ xs, postLocal P (post xs)) →
    agreeOn (A.filter fun r => !decide (r ∈ syms gs)) rs base →
    AxEpiLedger.ledgerInv ⟨rs, mem, testDevs⟩ Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (AxEpiLedger.ledgerStep cpu vs) t0 s' ∧
      RetS cpu (post (lookups rs gs)) kk s' := by
  intro F Hpl Hag
  exact ledgerInvReachesRet _ _ _ _ pc _ _ cpu kk s1
    (frameFactsTransfer _ _ _ _ _ _ _ _ _ ⟨rs, mem, testDevs⟩ (F _ (lookupsLength rs gs))
      (Hpl _) (agreeOnSym _ _ _ (agreeLdg A base rs gs Hag)))

section engine
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- THE ENGINE: the whole-instruction `wpd` from ANY register file `rs` agreeing with the
concrete control `base` on `A ∖ syms gs`; the post is instantiated at the caller's own values of
the symbolic registers. -/
theorem wpdLdg (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (mem : BMap) (base : RegFile) (gs : List W64r) (A Dr Dw D : List Register) (pc : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : List (BitVec 64) → RegFile → Bool)
    (F : LdgFacts mem base gs A Dr Dw D pc vs P post)
    (Hpl : ∀ xs, postLocal P (post xs))
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pc vs⌝)
    (rs : RegFile) (Hag : agreeOn (A.filter fun r => !decide (r ∈ syms gs)) rs base) :
    ⊢ ((∀ s', ⌜RetS cpu (post (lookups rs gs)) kk s'⌝ -∗ wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜AxEpiLedger.ledgerInv ⟨rs, mem, testDevs⟩ Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) rs none ib, kk⟩ Φ :=
  wpdCjrFrameGen i Φ cpu ib kk (ldgState mem base gs (lookups rs gs)) A Dr Dw D pc vs P
    (post (lookups rs gs)) (F _ (lookupsLength rs gs)) (Hpl _) Hgd rs
    (agreeLdg A base rs gs Hag)

end engine

/-- Rocq `LdgFactsT`: the tick = true ledger (every non-first instruction of a row).  `mip` /
`mtime` must stay CONCRETE in `base` (`tick_clock` branches on them); `minstret` and `mcycle`
may be listed in `gs`. -/
def LdgFactsT (mem : BMap) (base : RegFile) (gs : List W64r) (A Dr Dw D : List Register)
    (pc : Int) (vs : List (BitVec 8)) (P : List Register)
    (post : List (BitVec 64) → RegFile → Bool) : Prop :=
  ∀ xs, xs.length = gs.length →
    CjrTickFrameFacts (ldgState mem base gs xs) A Dr Dw D pc vs P (post xs)

theorem ldgInvReachesRetTick (mem : BMap) (base : RegFile) (gs : List W64r)
    (A Dr Dw D : List Register) (pc : Int) (vs : List (BitVec 8)) (P : List Register)
    (post : List (BitVec 64) → RegFile → Bool) (rs : RegFile) (cpu : CPU) (kk : Nat)
    (s1 : Athread) :
    LdgFactsT mem base gs A Dr Dw D pc vs P post →
    (∀ xs, postLocal P (post xs)) →
    agreeOn (A.filter fun r => !decide (r ∈ syms gs)) rs base →
    ledgerCjrtInv ⟨rs, mem, testDevs⟩ Dr Dw D vs cpu kk s1 →
    ∃ t0 s', aeqv s1 t0 ∧ rtc (ldStep cpu vs) t0 s' ∧
      RetP cpu (fun rs3 => post (lookups rs gs) rs3 = true) kk s' := by
  intro F Hpl Hag
  exact ledgerCjrtInvReachesRet _ _ _ _ pc _ _ cpu kk s1
    (tickFrameFactsTransfer _ _ _ _ _ _ _ _ _ ⟨rs, mem, testDevs⟩ (F _ (lookupsLength rs gs))
      (Hpl _) (agreeOnSym _ _ _ (agreeLdg A base rs gs Hag)))

section engineTick
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdLdgTick (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (mem : BMap) (base : RegFile) (gs : List W64r) (A Dr Dw D : List Register) (pc : Int)
    (vs : List (BitVec 8)) (P : List Register) (post : List (BitVec 64) → RegFile → Bool)
    (F : LdgFactsT mem base gs A Dr Dw D pc vs P post)
    (Hpl : ∀ xs, postLocal P (post xs))
    (Hgd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk pc vs⌝)
    (rs : RegFile) (Hag : agreeOn (A.filter fun r => !decide (r ∈ syms gs)) rs base) :
    ⊢ ((∀ s', ⌜RetP cpu (fun rs3 => post (lookups rs gs) rs3 = true) kk s'⌝ -∗
          wpd .MaybeStuck i s' Φ) ∧
       (∀ (GD : Gdexec) s1,
          ⌜ledgerCjrtInv ⟨rs, mem, testDevs⟩ Dr Dw D vs cpu kk s1⌝ -∗
          ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1)) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep true) rs none ib, kk⟩ Φ :=
  wpdCjrFrameTickGen i Φ cpu ib kk (ldgState mem base gs (lookups rs gs)) A Dr Dw D pc vs P
    (post (lookups rs gs)) (F _ (lookupsLength rs gs)) (Hpl _) Hgd rs
    (agreeLdg A base rs gs Hag)

end engineTick

/-! # 4. Footprint sets for register-only code, and the `A` tracer -/

/-- Rocq `gprs_all`. -/
def gprsAll : List W64r :=
  [⟨.x1, rfl⟩, ⟨.x2, rfl⟩, ⟨.x3, rfl⟩, ⟨.x4, rfl⟩, ⟨.x5, rfl⟩, ⟨.x6, rfl⟩, ⟨.x7, rfl⟩,
   ⟨.x8, rfl⟩, ⟨.x9, rfl⟩, ⟨.x10, rfl⟩, ⟨.x11, rfl⟩, ⟨.x12, rfl⟩, ⟨.x13, rfl⟩, ⟨.x14, rfl⟩,
   ⟨.x15, rfl⟩, ⟨.x16, rfl⟩, ⟨.x17, rfl⟩, ⟨.x18, rfl⟩, ⟨.x19, rfl⟩, ⟨.x20, rfl⟩, ⟨.x21, rfl⟩,
   ⟨.x22, rfl⟩, ⟨.x23, rfl⟩, ⟨.x24, rfl⟩, ⟨.x25, rfl⟩, ⟨.x26, rfl⟩, ⟨.x27, rfl⟩, ⟨.x28, rfl⟩,
   ⟨.x29, rfl⟩, ⟨.x30, rfl⟩, ⟨.x31, rfl⟩]

/-- Rocq `Dr_ldg`: the epilogue's CSR read footprint (neither pin) plus all 31 GPRs. -/
noncomputable def DrLdg : List Register := AxEpiProbe.drNopin ++ syms gprsAll
/-- Rocq `Dw_ldg`. -/
noncomputable def DwLdg : List Register := DwAll ++ syms gprsAll
/-- Rocq `D_ldg` (deviation 1: both pins removed). -/
noncomputable def DLdg : List Register :=
  (DrLdg ++ DwLdg).eraseDups.filter fun r => !decide (r = .sig_seip) && !decide (r = .sig_meip)

/-- Rocq `upx`: the upward-exposed reads (read before any write) of a whole step, reads answered
from the state and RAM reads from its memory (discovery helper). -/
def upx {X : Type} : SailM X → ExecSt → List Register → List Register → Option (List Register)
  | .pure _, _, rd, _ => some rd
  | .impure (.error _) _, _, _, _ => none
  | .impure (.ok o) k, t, rd, wr =>
    match o, k with
    | .regRead r, k =>
      upx (k (t.regs r)) t (if r ∈ wr then rd else if r ∈ rd then rd else r :: rd) wr
    | .regWrite r v, k => upx (k PUnit.unit) (t.setReg r v) rd (r :: wr)
    | .memRead n _ req, k =>
      match bmRead t.mem req.pa n with
      | some w => upx (k (.Ok (w, none))) t rd wr
      | none => none
    | .instrAnnounce _ _, k => upx (k ()) t rd wr
    | .branchAnnounce _ _, k => upx (k ()) t rd wr
    | .barrier _, k => upx (k ()) t rd wr
    | .cacheOp _, k => upx (k ()) t rd wr
    | .tlbi _, k => upx (k ()) t rd wr
    | .takeException _, k => upx (k ()) t rd wr
    | .returnException _, k => upx (k ()) t rd wr
    | .translationStart _, k => upx (k ()) t rd wr
    | .translationEnd _, k => upx (k ()) t rd wr
    | .cycleCount, k => upx (k ()) t rd wr
    | .message _, k => upx (k ()) t rd wr
    | .getCycleCount, k => upx (k (0 : Nat)) t rd wr
    | _, _ => none

/-- Rocq `mem_at`: a memory holding `vs` at `pc` (for the tracer only; the ledger takes the
fetched bytes from the graph). -/
def memAt (pc : Int) (vs : List (BitVec 8)) : BMap := fun a =>
  (((List.range vs.length).zip vs).find? fun p => BitVec.ofInt 64 (pc + p.1) == a).map (·.2)

/-- Rocq `A_of_t`: the upward-exposed read set of `riscvStep tick` for bytes `vs` at the
concrete control `base`, both pins excluded (deviation 1). -/
noncomputable def AOfT (tick : Bool) (base : RegFile) (pc : Int) (vs : List (BitVec 8)) :
    List Register :=
  match upx (riscvStep tick) ⟨base, memAt pc vs, testDevs⟩ [] [] with
  | some l => l.filter fun r => !decide (r = .sig_seip) && !decide (r = .sig_meip)
  | none => []

/-- Rocq `A_of`. -/
noncomputable def AOf : RegFile → Int → List (BitVec 8) → List Register := AOfT false

/-! # 5. The seals and the ledger tactics

Rocq's FINDING (AxLdgSealArith): the run with a symbolic `x` is cheap, the READBACK of a wrapped
value explodes, so the data operations are generalised after unfolding the executed body.  Sound
for every value: the goal is proved for EVERY interpretation of the operations.  Requires that
CONTROL does not depend on the sealed results.  In Lean (method above) the seals are optional;
`ax_ldg_seal_close` is what matters: `zeqb` generalised to `E` with `HE : ∀ a, E a a = true`, then
`ax_epi_cjr_frame_kloop HE` cases every post leaf `E a b` of the kernel spine (the `false` arm
absurd by `HE b`, the kernel checking `a ≡ b`). -/

/-- (Lean-only) Split a length-0 value list. -/
theorem AxLdgSeal.forallLenZero {α : Type} {P : List α → Prop} (h : P []) :
    ∀ xs : List α, xs.length = 0 → P xs := by
  intro xs hl
  rw [List.length_eq_zero_iff.1 hl]
  exact h

/-- (Lean-only) Split a length-`n+1` value list into a head and a tail. -/
theorem AxLdgSeal.forallLenSucc {α : Type} {P : List α → Prop} {n : Nat}
    (h : ∀ x, ∀ xs : List α, xs.length = n → P (x :: xs)) :
    ∀ xs : List α, xs.length = n + 1 → P xs := by
  intro xs hl
  cases xs with
  | nil => exact absurd hl (by simp)
  | cons x xs => exact h x xs (by simpa using hl)

/-- Rocq `ldg_split_xs`: turn `∀ xs, xs.length = gs.length → …` into one variable per
symbolic register. -/
macro "ax_ldg_seal_split_xs" : tactic => `(tactic| (
  repeat (first
    | (apply AxLdgSeal.forallLenZero)
    | (apply AxLdgSeal.forallLenSucc; intro _))))

/-- Rocq `ldg_unfold_step`: expose the executed instruction (for the seals). -/
macro "ax_ldg_seal_unfold_step" : tactic => `(tactic| (
  (try unfold branchAtAg); (try unfold branchAtTickAg);
  unfold riscvStep Functions.try_step Functions.run_hart_active Functions.execute))

/-- Rocq `ldg_close`: generalise the sealed comparison and close the post leaves. -/
macro "ax_ldg_seal_close" : tactic => `(tactic| (
  (try unfold ldgPost);
  have HE : ∀ a, zeqb a a = true := zeqbRefl;
  generalize zeqb = E at HE ⊢;
  ax_epi_cjr_frame_kloop HE))

/-- Rocq `ldg_seal_alu`: seal the 64-bit data operations of the integer OP / OP-IMM classes. -/
macro "ax_ldg_seal_alu" : tactic => `(tactic| (
  (try generalize (HAdd.hAdd : BitVec 64 → BitVec 64 → BitVec 64) = ADD);
  (try generalize (HSub.hSub : BitVec 64 → BitVec 64 → BitVec 64) = SUB);
  (try generalize (HAnd.hAnd : BitVec 64 → BitVec 64 → BitVec 64) = AND);
  (try generalize (HOr.hOr : BitVec 64 → BitVec 64 → BitVec 64) = OR);
  (try generalize (HXor.hXor : BitVec 64 → BitVec 64 → BitVec 64) = XOR);
  (try generalize (shift_bits_left (n := 64) (m := 6)) = SLL);
  (try generalize (shift_bits_right (n := 64) (m := 6)) = SRL);
  (try generalize (shift_bits_right_arith (k_n := 64) (k_m := 6)) = SRA)))

/-- Rocq `ldg_seal_ext`: the width-changing helpers of OP-IMM-32 / OP-32 (posts must write the
extension VISIBLY). -/
macro "ax_ldg_seal_ext" : tactic => `(tactic| (
  (try generalize (@Sail.BitVec.extractLsb 64) = SUBR);
  (try generalize (sign_extend (k_n := 32) (m := 64)) = SEXT32);
  (try generalize (sign_extend (k_n := 12) (m := 64)) = SEXT12);
  (try generalize (zero_extend (k_n := 1) (m := 64)) = ZEXT)))

/-- Rocq `ldg_seal_cmp`: the set-less-than comparisons (data, not control). -/
macro "ax_ldg_seal_cmp" : tactic => `(tactic| (
  (try generalize (zopz0zI_s (k_n := 64)) = SLT);
  (try generalize (zopz0zI_u (k_n := 64)) = SLTU)))

/-- Rocq `ldg_seal_all`. -/
macro "ax_ldg_seal_all" : tactic => `(tactic| (ax_ldg_seal_alu; ax_ldg_seal_ext; ax_ldg_seal_cmp))

/-- Rocq `ldg_solve unf seal`: `unf` unfolds the post function (and, for the seals, the
executed `execute_*` body); `seal` generalises the data operations. -/
syntax "ax_ldg_seal_solve " "(" tacticSeq ")" "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| ax_ldg_seal_solve ($unf:tacticSeq) ($sl:tacticSeq)) => `(tactic| (
    ax_ldg_seal_split_xs;
    constructor;
    case cfSeipDr => decide +kernel
    case cfMeipDr => decide +kernel
    case cfSeipD => decide +kernel
    case cfMeipD => decide +kernel
    case cfHead => decide +kernel
    case cfToSeip => ax_epi_ledger_krfl
    all_goals (ax_ldg_seal_unfold_step; ($unf:tacticSeq); ($sl:tacticSeq); ax_ldg_seal_close)))

/-- Rocq `ldg_solve_tick` (`CjrTickFrameFacts` has no head field). -/
syntax "ax_ldg_seal_solve_tick " "(" tacticSeq ")" "(" tacticSeq ")" : tactic
macro_rules
  | `(tactic| ax_ldg_seal_solve_tick ($unf:tacticSeq) ($sl:tacticSeq)) => `(tactic| (
    ax_ldg_seal_split_xs;
    constructor;
    case cftSeipDr => decide +kernel
    case cftMeipDr => decide +kernel
    case cftSeipD => decide +kernel
    case cftMeipD => decide +kernel
    case cftToSeip => ax_epi_ledger_krfl
    all_goals (ax_ldg_seal_unfold_step; ($unf:tacticSeq); ($sl:tacticSeq); ax_ldg_seal_close)))

/-! # 6. Equation lemmas for the sealed operations (posts are stated with the model's own
functions; these turn them into integer arithmetic). -/

theorem addVecUnsigned (x y : BitVec 64) :
    ((x + y).toNat : Int) = ((x.toNat : Int) + y.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add]; omega

theorem subVecUnsigned (x y : BitVec 64) :
    ((x - y).toNat : Int) = ((x.toNat : Int) - y.toNat) % 2 ^ 64 := by
  have hx := x.isLt; have hy := y.isLt
  rw [BitVec.toNat_sub]; omega

theorem andVecUnsigned (x y : BitVec 64) :
    ((x &&& y).toNat : Int) = ((x.toNat &&& y.toNat : Nat) : Int) := by
  rw [BitVec.toNat_and]

theorem orVecUnsigned (x y : BitVec 64) :
    ((x ||| y).toNat : Int) = ((x.toNat ||| y.toNat : Nat) : Int) := by
  rw [BitVec.toNat_or]

end Weak
