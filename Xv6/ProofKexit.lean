/-
Proof of `kexit`'s contract (`SpecKexit.KEXIT`), given `myproc`, the
file-system boundary (`FsEnv`: fileclose / begin_op / iput / end_op),
`acquire`, `reparent`, `wakeup`, `release` and `sched`.

    80002050: c.addi16sp sp,-48; sd ra/s0/s1/s2/s3/s4; addi s0,sp,48   <- prologue (6 slots)
    80002060: mv s4,a0; jal myproc; mv s3,a0
    80002068: auipc a5,0x8; ld a5,536(a5)          -- a5 = *initproc
    80002070: addi s1,a0,208; addi s2,a0,336       -- s1=&ofile[0], s2=&cwd
    80002078: bne a5,a0,0x8000213c                 -- p != initproc: enter loop
    ...       (panic("init exiting"), NOT taken)
    80002088: addi s1,8; beq s1,s2,0x8000214a; ld a0,0(s1); beqz a0,back;
              jal fileclose; sd zero,0(s1); j back  -- the ofile loop
    8000209c: jal begin_op; ld a0,336(s3); jal iput; jal end_op; sd zero,336(s3)
    800020b0: acquire(&wait_lock); reparent(p); ld a0,56(s3); wakeup(p->parent)
    800020ca: acquire(&p->lock); p->xstate=s4; p->state=ZOMBIE
    800020da: release(&wait_lock); sched()          -- the ZOMBIE park
    800020ea: panic("zombie exit")                  -- dead

The thread parks at ZOMBIE and never resumes: `needsCtx ZOMBIE = false`, so
`sched`'s continuation is `emp`.  What it owes the slot is
`procDormantNoctx (procAddr j) ZOMBIE` -- its private block minus the save
area, plus the whole kernel stack -- built (`kx_dormant_build`) from the
zeroed `procPrivNoctxAt` (the ofile loop and `p->cwd = 0` are the payment)
and the stack the caller's STACK CLOSER produces.
-/
import MachCSL.WpSmodeFrame
import Xv6.SpecKexit
import Xv6.SpecMyproc
import Xv6.SpecAcquire
import Xv6.SpecRelease
import Xv6.SpecSched
import Xv6.SpecReparent
import Xv6.SpecWakeup
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false

/-! ## Pure geometry facts -/

/-- `&p->ofile[0]` from the base pointer. -/
theorem kx_pOfile0 (pa : BitVec 64) : pOfile pa 0 = pa + 208#64 := by
  unfold pOfile; simp only [Nat.mul_zero]; bv_omega

/-- `&p->cwd` from the base pointer (what `addi s2,a0,336` computes). -/
theorem kx_pCwd (pa : BitVec 64) : pa + 336#64 = pCwd pa := rfl

/-- The scan's increment. -/
theorem kx_pOfile_succ (pa : BitVec 64) (fd : Nat) : pOfile pa fd + 8#64 = pOfile pa (fd + 1) := by
  unfold pOfile
  rw [show 8 * (fd + 1) = 8 * fd + 8 from by omega, BitVec.ofNat_add]
  bv_omega

/-- The scan's exit address IS `&p->cwd`. -/
theorem kx_pOfile_end (pa : BitVec 64) : pOfile pa NOFILE = pCwd pa := by
  unfold pOfile pCwd NOFILE
  bv_omega

/-- Before the end, an ofile slot address is not `&p->cwd`. -/
theorem kx_pOfile_ne_cwd (pa : BitVec 64) (m : Nat) (hm : m < NOFILE) : pOfile pa m ≠ pCwd pa := by
  unfold pOfile pCwd NOFILE at *
  intro h
  have hmm : 8 * m < 128 := by omega
  bv_omega

/-- `beq` as an equality test. -/
theorem kx_ite_beq {α : Type _} (x y : BitVec 64) (p q : α) :
    (if bcond bop.BEQ x y then p else q) = if x = y then p else q := by
  by_cases h : x = y <;> simp [bcond, h]

/-- `bne` as a disequality test. -/
theorem kx_ite_bne {α : Type _} (x y : BitVec 64) (p q : α) :
    (if bcond bop.BNE x y then p else q) = if x ≠ y then p else q := by
  by_cases h : x = y <;> simp [bcond, h]

/-- The immediate `-48` of `c.addi16sp sp,-48`. -/
theorem kx_imm_m48 : BitVec.signExtend 64 4048#12 = -(8#64 * BitVec.ofNat 64 6) := by
  simp only [BitVec.reduceSignExtend, BitVec.reduceMul, BitVec.reduceNeg]

theorem kx_pState (pa : BitVec 64) : pa + 24#64 = pState pa := rfl
theorem kx_pXstate (pa : BitVec 64) : pa + 44#64 = pXstate pa := rfl
theorem kx_pParent (pa : BitVec 64) : pa + 56#64 = pParent pa := rfl
theorem kx_pCwd0 (pa : BitVec 64) : pa + 336#64 = pCwd pa := rfl

/-- `&wait_lock` from `auipc a0,0x10; addi a0,a0,752` at `0x8000215e`. -/
theorem kx_wl_addr1 :
    (0x8000215e#64 : BitVec 64) + (BitVec.signExtend 64 (16#20 ++ 0#12) + 746#64) = 0x80012448#64 := by
  decide

/-- `&wait_lock` from `auipc a0,0x10; addi a0,a0,710` at `0x80002188`. -/
theorem kx_wl_addr2 :
    (0x80002188#64 : BitVec 64) + (BitVec.signExtend 64 (16#20 ++ 0#12) + 704#64) = 0x80012448#64 := by
  decide

theorem kx_zombie : BitVec.extractLsb' 0 32 (5#64 : BitVec 64) = ZOMBIE := by decide
theorem kx_parkOk_zombie : parkOk ZOMBIE := by decide
theorem kx_needsCtx_zombie : ¬ needsCtx ZOMBIE := by decide
theorem kx_invDormant_zombie : invDormant ZOMBIE := by decide

/-! ## The ZOMBIE park's payment -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]

/-- The dormant block a ZOMBIE park owes, built from the zeroed private block
and the whole kernel stack (at the explicit context key `parkPay` wants). -/
theorem kx_dormant_build (ξ : CtxId) (pa : BitVec 64) (pid : BitVec 32) (V : ProcPriv)
    (M : Nat → List (BitVec 8)) (hof : V.ofile = List.replicate NOFILE 0#64) (hcwd : V.cwd = 0#64) :
    procPrivNoctxAt (GF := GF) ξ pa pid V M ∗
      @stackOwn hlc GF _ ⟨ξ, KTier.kpt⟩ (V.kstack + 4096#64) 512 ⊢
      @procDormantNoctx hlc GF _ ⟨ξ, KTier.kpt⟩ pa ZOMBIE := by
  unfold procPrivNoctxAt procDormantNoctx
  iintro ⟨⟨%hpure, Hpid, Hfields, Hpt, Htf⟩, Hstk⟩
  isplitl []
  · ipureintro; right; rfl
  iexists V, pid
  isplitl []
  · ipureintro; exact ⟨hof, hcwd, hpure.1⟩
  iframe Hpid Hfields
  unfold dormantSpace
  rw [if_neg (by decide : ¬ (ZOMBIE = UNUSED))]
  iexists M
  isplitl []
  · ipureintro; exact ⟨hpure.2.2.1, hpure.2.2.2, hpure.2.1⟩
  iframe Hpt Htf Hstk

end

/-- The frame context of `kexit`'s body: interrupts off at depth 0, no lock,
Kpt, running proc `j`, `s2 = &cwd`, `s3 = p`, `s4 = status`, a fixed `sp`,
and enough budget for a blocking call. -/
def kxFrame (k : KCtx) (j : Nat) (status : BitVec 64) (spval : BitVec 64) (availval : Nat) : Prop :=
  k.sie = false ∧ k.noff = 0 ∧ k.locks = [] ∧ k.tier = KTier.kpt ∧ k.proc = procAddr j ∧
  fsSlots ≤ k.avail ∧ k.regs 18#5 = pCwd (procAddr j) ∧ k.regs 19#5 = procAddr j ∧
  k.regs 20#5 = status ∧ k.sp = spval ∧ k.avail = availval

/-- A length-`NOFILE` list all of whose entries are zero IS `replicate`. -/
theorem kx_list_zero (L : List (BitVec 64)) (hlen : L.length = NOFILE)
    (h : ∀ i, i < NOFILE → L[i]? = some 0#64) : L = List.replicate NOFILE 0#64 := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    have hi : i < NOFILE := by rw [hlen] at h1; exact h1
    have := h i hi
    rw [List.getElem?_eq_getElem h1] at this
    have he : L[i] = 0#64 := Option.some.inj this
    rw [he, List.getElem_replicate]

/-- Nulling slot `fd` extends the zero-prefix invariant. -/
theorem kx_set_inv (L : List (BitVec 64)) (fd : Nat) (hlen : L.length = NOFILE) (hfd : fd < NOFILE)
    (hinv : ∀ i, i < fd → L[i]? = some 0#64) :
    ∀ i, i < fd + 1 → (L.set fd 0#64)[i]? = some 0#64 := by
  intro i hi
  by_cases h : i = fd
  · subst h
    rw [List.getElem?_set_self (by rw [hlen]; exact hfd)]
  · rw [List.getElem?_set_ne (fun e => h e.symm)]
    exact hinv i (by omega)

/-- The zero-already slot keeps the invariant (`beqz` taken arm). -/
theorem kx_keep_inv (L : List (BitVec 64)) (fd : Nat) (hfd2 : fd < L.length)
    (hz : L[fd] = 0#64) (hinv : ∀ i, i < fd → L[i]? = some 0#64) :
    ∀ i, i < fd + 1 → L[i]? = some 0#64 := by
  intro i hi
  by_cases h : i = fd
  · subst h; rw [List.getElem?_eq_getElem hfd2, hz]
  · exact hinv i (by omega)

/-- `kxFrame` transports across a blocking call (callee-saved). -/
theorem kxFrame_cross {k : KCtx} {j : Nat} {status : BitVec 64} {spval : BitVec 64} {availval : Nat}
    (hf : kxFrame k j status spval availval) (spie spp : Bool) (R' : RegMap)
    (hcs : calleeSaved k.regs R') :
    kxFrame ((k.withSpie spie spp).withRegs R') j status spval availval := by
  obtain ⟨hs, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩ := hf
  unfold calleeSaved at hcs
  refine ⟨hs, hn, hl, ht, hp, hK, ?_, ?_, ?_, ?_, ?_⟩
  · show R' 18#5 = pCwd (procAddr j); rw [hcs.2.2.2.1]; exact h18
  · show R' 19#5 = procAddr j; rw [hcs.2.2.2.2.1]; exact h19
  · show R' 20#5 = status; rw [hcs.2.2.2.2.2.1]; exact h20
  · show R' 2#5 = spval; rw [hcs.1]; exact hsp
  · show ((k.withSpie spie spp).withRegs R').avail = availval
    simp only [KCtx.withRegs_avail, KCtx.withSpie_avail]; exact hav

/-- `kxFrame` is preserved by a register write outside `sp`, `s2`, `s3`, `s4`. -/
theorem kx_setReg_frame {availval : Nat} (k : KCtx) (j : Nat) (status : BitVec 64) (spval : BitVec 64)
    (i : BitVec 5) (v : BitVec 64) (hf : kxFrame k j status spval availval)
    (h2 : i ≠ 2#5) (h18 : i ≠ 18#5) (h19 : i ≠ 19#5) (h20 : i ≠ 20#5) :
    kxFrame (k.setReg i v) j status spval availval := by
  obtain ⟨hsie, hn, hl, ht, hp, hK, hh18, hh19, hh20, hsp, hav⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [KCtx.setReg_sie]; exact hsie
  · simp only [KCtx.setReg_noff]; exact hn
  · simp only [KCtx.setReg_locks]; exact hl
  · simp only [KCtx.setReg_tier]; exact ht
  · simp only [KCtx.setReg_proc]; exact hp
  · simp only [KCtx.setReg_avail]; exact hK
  · show (k.setReg i v).regs 18#5 = pCwd (procAddr j)
    rw [KCtx.setReg_regs, RegMap.set_apply, if_neg (fun e => h18 e.symm)]; exact hh18
  · show (k.setReg i v).regs 19#5 = procAddr j
    rw [KCtx.setReg_regs, RegMap.set_apply, if_neg (fun e => h19 e.symm)]; exact hh19
  · show (k.setReg i v).regs 20#5 = status
    rw [KCtx.setReg_regs, RegMap.set_apply, if_neg (fun e => h20 e.symm)]; exact hh20
  · show (k.setReg i v).regs 2#5 = spval
    rw [KCtx.setReg_regs, RegMap.set_apply, if_neg (fun e => h2 e.symm)]; exact hsp
  · show (k.setReg i v).avail = availval
    rw [KCtx.setReg_avail]; exact hav

/-- `+ signExtend 0` is the identity. -/
theorem kx_add0 (a : BitVec 64) : a + BitVec.signExtend 64 0#12 = a := by
  simp only [BitVec.reduceSignExtend, BitVec.add_zero]

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]
/-- The resume pc of a call whose return address `v` (even) sits in `ra`. -/
theorem kx_pcIs_jump (cpu : CPU) (X : KCtx) (R : RegMap) (v : BitVec 64) (hv : jumpPc v = v) :
    pcIs (GF := GF) cpu (jumpPc ((X.withRegs (R.set 1#5 v)).regs 1#5)) ⊢ pcIs cpu v := by
  rw [KCtx.withRegs_regs, RegMap.set_apply, if_pos rfl, hv]
end

/-- The scan's increment, with the immediate as the instruction supplies it. -/
theorem kx_succ8 (pa : BitVec 64) (fd : Nat) :
    pOfile pa fd + BitVec.signExtend 64 8#12 = pOfile pa (fd + 1) := by
  rw [show BitVec.signExtend 64 8#12 = 8#64 from by simp]
  exact kx_pOfile_succ pa fd

theorem kx_pcIs_pos {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    (cpu : CPU) (p : Prop) [Decidable p] (a b : BitVec 64) (h : p) :
    pcIs (GF := GF) cpu (if p then a else b) ⊢ pcIs cpu a := by rw [if_pos h]

theorem kx_pcIs_neg {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    (cpu : CPU) (p : Prop) [Decidable p] (a b : BitVec 64) (h : ¬ p) :
    pcIs (GF := GF) cpu (if p then a else b) ⊢ pcIs cpu b := by rw [if_neg h]

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [X : CurCtx]

/-- The blocking `fileclose` call at hart `c`, context `kk`. -/
theorem kx_fileclose (FC : FsEntry filecloseAddr) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (kk : KCtx) (j : Nat) (hj : j < NPROC) (hp : kk.proc = procAddr j)
    (hK : fsSlots ≤ kk.avail) (hs : kk.sie = false) (hn : kk.noff = 0) (hl : kk.locks = [])
    (ht : kk.tier = KTier.kpt) :
    kctx c kk ∗ pcIs c 0x8000421c#64 ∗ procsInv Γ ∗ trapCsrs c ∗ cpuClaim c (procAddr j) ∗
      intrRes c ∗
      wpNext true (procAddr j) c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
        kctx cpu' ((kk.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (kk.regs 1#5)) -∗
        trapCsrs cpu' -∗ cpuClaim cpu' (procAddr j) -∗ intrRes cpu' -∗
        ⌜calleeSaved kk.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := FC (hlc := hlc) (GF := GF) Γ c kk j hj hp hK hs hn hl ht
  unfold wp_blocking_body at h
  rw [hp] at h
  rw [show filecloseAddr = 0x8000421c#64 from rfl] at h
  exact h

/-- A general blocking fs call at entry `entry` (numeric literal `pcnum`),
hart `c`, context `kk`. -/
theorem kx_fscall (entry pcnum : BitVec 64) (heq : entry = pcnum) (FC : FsEntry entry)
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (c : CPU) (kk : KCtx) (j : Nat) (hj : j < NPROC) (hp : kk.proc = procAddr j)
    (hK : fsSlots ≤ kk.avail) (hs : kk.sie = false) (hn : kk.noff = 0) (hl : kk.locks = [])
    (ht : kk.tier = KTier.kpt) :
    kctx c kk ∗ pcIs c pcnum ∗ procsInv Γ ∗ trapCsrs c ∗ cpuClaim c (procAddr j) ∗
      intrRes c ∗
      wpNext true (procAddr j) c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
        kctx cpu' ((kk.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (kk.regs 1#5)) -∗
        trapCsrs cpu' -∗ cpuClaim cpu' (procAddr j) -∗ intrRes cpu' -∗
        ⌜calleeSaved kk.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := FC (hlc := hlc) (GF := GF) Γ c kk j hj hp hK hs hn hl ht
  unfold wp_blocking_body at h
  rw [hp] at h
  rw [heq] at h
  exact h

set_option maxHeartbeats 8000000 in
/-- **The ofile scan** from `0x8000213c` (the `ld a0,0(s1)`) at index `fd`,
with `fd + n + 1 = NOFILE` slots left (so `n` after the current one).
Hart-generic: `fileclose` may resume the thread on another hart.  `L` is
nulled slot by slot; `hinv` records the zero prefix, `kx_list_zero` turns the
completed scan into `replicate NOFILE 0` for the continuation `Φ`. -/
theorem kx_loop (FC : FsEntry filecloseAddr) (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (j : Nat) (hj : j < NPROC) (status : BitVec 64) (spval : BitVec 64) (availval : Nat) (Ψ : IProp GF)
    (hΨ : ∀ (c' : CPU) (kk : KCtx), kxFrame kk j status spval availval →
        (kctx c' kk ∗ pcIs c' 0x8000214a#64 ∗ procsInv Γ ∗ trapCsrs c' ∗
          cpuClaim c' (procAddr j) ∗ intrRes c' ∗
          ofileCells (procAddr j) (DFrac.own 1) (List.replicate NOFILE 0#64) ∗ Ψ) ⊢ wpLoop (GF := GF) c') :
    ∀ (n fd : Nat), fd + n + 1 = NOFILE → ∀ (c : CPU) (k : KCtx) (L : List (BitVec 64)),
      kxFrame k j status spval availval → k.regs 9#5 = pOfile (procAddr j) fd → L.length = NOFILE →
      (∀ i, i < fd → L[i]? = some 0#64) →
      (kctx c k ∗ pcIs c 0x8000213c#64 ∗ procsInv Γ ∗ trapCsrs c ∗ cpuClaim c (procAddr j) ∗
        intrRes c ∗ ([∗list] i ↦ f ∈ L, wordPointsTo (pOfile (procAddr j) i) 8 (DFrac.own 1) f) ∗
        Ψ)
      ⊢ wpLoop (GF := GF) c := by
  -- the body from `0x8000213c`: `ld`, the `beqz` test, `fileclose` (crossing)
  -- and the nulling store, handing the `0x80002136` state (list nulled at
  -- `fd`) to `TT`.
  have hbody : ∀ (fd : Nat) (hfdlt : fd < NOFILE) (L : List (BitVec 64)) (hlen : L.length = NOFILE)
      (TT : ∀ (c'' : CPU) (k'' : KCtx), kxFrame k'' j status spval availval →
        k''.regs 9#5 = pOfile (procAddr j) fd →
        (kctx c'' k'' ∗ pcIs c'' 0x80002136#64 ∗ procsInv Γ ∗ trapCsrs c'' ∗
          cpuClaim c'' (procAddr j) ∗ intrRes c'' ∗
          ([∗list] i ↦ f ∈ L.set fd 0#64, wordPointsTo (pOfile (procAddr j) i) 8 (DFrac.own 1) f) ∗
          Ψ) ⊢ wpLoop (GF := GF) c''),
      ∀ (c : CPU) (k : KCtx), kxFrame k j status spval availval → k.regs 9#5 = pOfile (procAddr j) fd →
        (kctx c k ∗ pcIs c 0x8000213c#64 ∗ procsInv Γ ∗ trapCsrs c ∗ cpuClaim c (procAddr j) ∗
          intrRes c ∗ ([∗list] i ↦ f ∈ L, wordPointsTo (pOfile (procAddr j) i) 8 (DFrac.own 1) f) ∗
          Ψ)
        ⊢ wpLoop (GF := GF) c := by
    intro fd hfdlt L hlen TT c k hf h9
    obtain ⟨hsie, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩ := hf
    have hfdlt2 : fd < L.length := by rw [hlen]; exact hfdlt
    iintro ⟨Hk, Hpc, #Hpinv, Htc, Hclaim, Hres, Hbig, HΨ⟩
    icases kctx_tier c k $$ Hk with ⟨%hct, Hk⟩
    icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
    have hget : L[fd]? = some (L[fd]'hfdlt2) := List.getElem?_eq_getElem hfdlt2
    icases BigSepL.bigSepL_insert_acc
      (Φ := fun i f => wordPointsTo (pOfile (procAddr j) i) 8 (DFrac.own 1) f) hget $$ Hbig
      with ⟨Hcell, Hback⟩
    -- ld a0,0(s1)
    k_step (wp_s_ld c _ 0x8000213c#64 true 0#12 10#5 9#5 (by decide) (by decide)
        (DFrac.own 1) (L[fd]'hfdlt2))
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, h9, kx_add0]
    iintro Hk Hpc Hcell
    have hval : (k.setReg 10#5 (L[fd]'hfdlt2)).rget c 10#5 = L[fd]'hfdlt2 :=
      KCtx.rget_setReg_same c k 10#5 _ (by decide) (by decide)
    -- beqz a0
    k_step (wp_s_branch c _ 0x8000213e#64 true 8184#13 10#5 0#5 (by decide) bop.BEQ)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [kx_ite_beq, KCtx.rget_eq, KCtx.setReg_regs, RegMap.set_apply, KCtx.setReg_sie, KCtx.setReg_proc]
    iintro Hk Hpc
    have hkframe10 : kxFrame (k.setReg 10#5 (L[fd]'hfdlt2)) j status spval availval :=
      kx_setReg_frame k j status spval 10#5 _ ⟨hsie, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩
        (by decide) (by decide) (by decide) (by decide)
    have h9_10 : (k.setReg 10#5 (L[fd]'hfdlt2)).regs 9#5 = pOfile (procAddr j) fd := by
      rw [KCtx.setReg_regs, RegMap.set_apply, if_neg (by decide), h9]
    by_cases hz : L[fd]'hfdlt2 = 0#64
    · -- already null: reassemble the (unchanged, but named `set fd 0`) list, jump to inc
      ihave Hpc := kx_pcIs_pos c _ _ _ hz $$ Hpc
      ihave Hcell0 : wordPointsTo (pOfile (procAddr j) fd) 8 (DFrac.own 1) 0#64 $$ [Hcell]
      case' _ => rw [← hz]; iexact Hcell
      ihave Hbig := Hback $$ %(0#64) Hcell0
      iapply (TT c (k.setReg 10#5 (L[fd]'hfdlt2)) hkframe10 h9_10)
      iframe Hk Hpc Hpinv Htc Hclaim Hres Hbig HΨ
    · -- open file: fileclose, then null the slot
      ihave Hpc := kx_pcIs_neg c _ _ _ hz $$ Hpc
      -- jal fileclose
      k_step (wp_s_jal c _ 0x80002140#64 false 8412#21 1#5 (by decide))
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [KCtx.setReg_sie, KCtx.setReg_proc]
      iintro Hk Hpc
      -- fileclose(a0)
      have hfc := kx_fileclose (hlc := hlc) (GF := GF) FC Γ c
        ((k.setReg 10#5 (L[fd]'hfdlt2)).setReg 1#5 0x80002144#64) j hj
        (by simp only [KCtx.setReg_proc]; exact hp) (by simp only [KCtx.setReg_avail]; exact hK)
        (by simp only [KCtx.setReg_sie]; exact hsie) (by simp only [KCtx.setReg_noff]; exact hn)
        (by simp only [KCtx.setReg_locks]; exact hl) (by simp only [KCtx.setReg_tier]; exact ht)
      iapply hfc $$ [- $Hk $Hpc $Hpinv $Htc $Hclaim $Hres]
      iapply wpNext_intro_pin
      iintro %c2 %hpin2
      iintro %spie %spp %R' Hk Hpc Htc Hclaim Hres %hcs
      have hkframe1 : kxFrame ((k.setReg 10#5 (L[fd]'hfdlt2)).setReg 1#5 0x80002144#64) j status spval availval :=
        kx_setReg_frame _ j status spval 1#5 _ hkframe10 (by decide) (by decide) (by decide) (by decide)
      have hR9 : R' 9#5 = pOfile (procAddr j) fd := by
        rw [hcs.2.2.1, KCtx.setReg_regs, RegMap.set_apply, if_neg (by decide),
          KCtx.setReg_regs, RegMap.set_apply, if_neg (by decide), h9]
      have hjump : jumpPc (((k.setReg 10#5 (L[fd]'hfdlt2)).setReg 1#5 0x80002144#64).regs 1#5)
          = 0x80002144#64 := by
        rw [KCtx.setReg_regs, RegMap.set_apply, if_pos rfl]; decide
      ihave Hpc := (show pcIs (GF := GF) c2 (jumpPc (((k.setReg 10#5 (L[fd]'hfdlt2)).setReg 1#5
          0x80002144#64).regs 1#5)) ⊢ pcIs c2 0x80002144#64 from by rw [hjump]) $$ Hpc
      -- sd zero,0(s1)
      k_step (wp_s_sd c2 _ 0x80002144#64 false 0#12 9#5 0#5 (by decide) (L[fd]'hfdlt2))
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [KCtx.rget_withRegs', hR9, kx_add0, KCtx.rget_zero, KCtx.setReg_sie, KCtx.setReg_proc]
      iintro Hk Hpc Hcell
      ihave Hbig := Hback $$ %(0#64) Hcell
      -- j 0x80002136
      k_step (wp_s_j c2 _ 0x80002148#64 true 2097134#21)
        from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
        with [KCtx.setReg_sie, KCtx.setReg_proc]
      iintro Hk Hpc
      have hkframeR := kxFrame_cross hkframe1 spie spp R' hcs
      iapply (TT c2 _ hkframeR (by rw [KCtx.withRegs_regs]; exact hR9))
      iframe Hk Hpc Hpinv Htc Hclaim Hres Hbig HΨ
  -- the induction on the number of slots after the current one
  intro n
  induction n with
  | zero =>
    intro fd hfd c k L hf h9 hlen hinv
    have hfdlt : fd < NOFILE := by omega
    have hfd1 : fd + 1 = NOFILE := by omega
    refine hbody fd hfdlt L hlen (fun c'' k'' hf'' h9'' => ?_) c k hf h9
    obtain ⟨hsie, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩ := hf''
    iintro ⟨Hk, Hpc, #Hpinv, Htc, Hclaim, Hres, Hbig, HΨ⟩
    icases kctx_tier c'' k'' $$ Hk with ⟨%hct, Hk⟩
    icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
    -- addi s1,8
    k_step (wp_s_addi c'' _ 0x80002136#64 true 8#12 9#5 9#5 (by decide))
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [KCtx.setReg_sie, KCtx.setReg_proc]
    iintro Hk Hpc
    -- beq s1,s2 (taken)
    k_step (wp_s_branch c'' _ 0x80002138#64 false 18#13 9#5 18#5 (by decide) bop.BEQ)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [kx_ite_beq, KCtx.rget_eq, KCtx.setReg_regs, RegMap.set_apply, h9'', kx_pOfile_succ, h18, KCtx.setReg_sie, KCtx.setReg_proc]
    iintro Hk Hpc
    ihave Hpc := kx_pcIs_pos c'' _ _ _
      (show pOfile (procAddr j) (fd + 1) = pCwd (procAddr j) from by
        rw [hfd1]; exact kx_pOfile_end (procAddr j)) $$ Hpc
    have hall : L.set fd 0#64 = List.replicate NOFILE 0#64 :=
      kx_list_zero _ (by rw [List.length_set]; exact hlen)
        (fun i hi => kx_set_inv L fd hlen hfdlt hinv i (by omega))
    have hkf : kxFrame (k''.setReg 9#5 (pOfile (procAddr j) (fd + 1))) j status spval availval :=
      kx_setReg_frame k'' j status spval 9#5 _ ⟨hsie, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩
        (by decide) (by decide) (by decide) (by decide)
    iapply (hΨ c'' (k''.setReg 9#5 (pOfile (procAddr j) (fd + 1))) hkf)
    unfold ofileCells
    iframe Hk Hpc Hpinv Htc Hclaim Hres HΨ
    isplitl []
    · ipureintro; simp
    · rw [← hall]; iexact Hbig
  | succ m IH =>
    intro fd hfd c k L hf h9 hlen hinv
    have hfdlt : fd < NOFILE := by omega
    have hfdlt1 : fd + 1 < NOFILE := by omega
    refine hbody fd hfdlt L hlen (fun c'' k'' hf'' h9'' => ?_) c k hf h9
    obtain ⟨hsie, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩ := hf''
    iintro ⟨Hk, Hpc, #Hpinv, Htc, Hclaim, Hres, Hbig, HΨ⟩
    icases kctx_tier c'' k'' $$ Hk with ⟨%hct, Hk⟩
    icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
    -- addi s1,8
    k_step (wp_s_addi c'' _ 0x80002136#64 true 8#12 9#5 9#5 (by decide))
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [KCtx.setReg_sie, KCtx.setReg_proc]
    iintro Hk Hpc
    -- beq s1,s2 (not taken)
    k_step (wp_s_branch c'' _ 0x80002138#64 false 18#13 9#5 18#5 (by decide) bop.BEQ)
      from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
      with [kx_ite_beq, KCtx.rget_eq, KCtx.setReg_regs, RegMap.set_apply, h9'', kx_pOfile_succ, h18, KCtx.setReg_sie, KCtx.setReg_proc]
    iintro Hk Hpc
    ihave Hpc := kx_pcIs_neg c'' _ _ _
      (kx_pOfile_ne_cwd (procAddr j) (fd + 1) hfdlt1) $$ Hpc
    have hkf : kxFrame (k''.setReg 9#5 (pOfile (procAddr j) (fd + 1))) j status spval availval :=
      kx_setReg_frame k'' j status spval 9#5 _ ⟨hsie, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩
        (by decide) (by decide) (by decide) (by decide)
    have h9r : (k''.setReg 9#5 (pOfile (procAddr j) (fd + 1))).regs 9#5 = pOfile (procAddr j) (fd + 1) := by
      rw [KCtx.setReg_regs, RegMap.set_apply, if_pos rfl]
    iapply (IH (fd + 1) (by omega) c''
      (k''.setReg 9#5 (pOfile (procAddr j) (fd + 1)))
      (L.set fd 0#64) hkf h9r (by rw [List.length_set]; exact hlen)
      (fun i hi => kx_set_inv L fd hlen hfdlt hinv i hi))
    iframe Hk Hpc Hpinv Htc Hclaim Hres Hbig HΨ

/-- A general blocking fs call helper (`begin_op`/`iput`/`end_op`) at the
frame context `kk`, packaged like `kx_fscall` but at a numeric pc. -/
theorem kx_fs (entry pcnum : BitVec 64) (heq : entry = pcnum) (FC : FsEntry entry)
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] (status : BitVec 64) (spval : BitVec 64)
    (availval : Nat) (c : CPU) (kk : KCtx) (j : Nat) (hj : j < NPROC)
    (hf : kxFrame kk j status spval availval) :
    kctx c kk ∗ pcIs c pcnum ∗ procsInv Γ ∗ trapCsrs c ∗ cpuClaim c (procAddr j) ∗ intrRes c ∗
      wpNext true (procAddr j) c (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap),
        kctx cpu' ((kk.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (kk.regs 1#5)) -∗
        trapCsrs cpu' -∗ cpuClaim cpu' (procAddr j) -∗ intrRes cpu' -∗
        ⌜calleeSaved kk.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  obtain ⟨hsie, hn, hl, ht, hp, hK, h18, h19, h20, hsp, hav⟩ := hf
  exact kx_fscall entry pcnum heq FC Γ c kk j hj hp hK hsie hn hl ht

/-- `reparent`'s contract at its call site `0x800020a8`, with the `p`
argument (`a0`) named `pv` so the rewritten payload is `reparented … pv`. -/
theorem kx_reparent (RP : REPARENT) (Γ : SchedNames) (c : CPU) (k' : KCtx)
    (parents : Nat → BitVec 64) (ip pv : BitVec 64) (ha0 : k'.regs 10#5 = pv)
    (hnoff' : k'.noff + 1 < 2 ^ 31) (hK' : reparentSlots ≤ k'.avail) (hlk' : "proc" ∉ k'.locks)
    (hwl' : "wait_lock" ∈ k'.locks) (htier' : k'.tier = KTier.kpt) :
    kctx c k' ∗ pcIs c 0x800020a8#64 ∗ procsInv Γ ∗ initprocIs ip ∗ waitResAt curCtx parents ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      waitResAt curCtx (reparented parents pv ip) -∗
      ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := RP.wp_reparent (hlc := hlc) (GF := GF) Γ c k' parents ip hnoff' hK' hlk' hwl' htier'
  unfold wp_reparent_body at h
  simp only [reparentAddr, KernelSyms.«reparent»] at h
  rw [ha0] at h
  exact h

/-- `wakeup`'s contract at its call site `0x80002042`. -/
theorem kx_wakeup (WU : WAKEUP) (Γ : SchedNames) (c : CPU) (k' : KCtx)
    (hnoff' : k'.noff + 1 < 2 ^ 31) (hK' : wakeupSlots ≤ k'.avail) (hlk' : "proc" ∉ k'.locks)
    (htier' : k'.tier = KTier.kpt) :
    kctx c k' ∗ pcIs c 0x80002042#64 ∗ procsInv Γ ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := WU.wp_wakeup (hlc := hlc) (GF := GF) Γ c k' hnoff' hK' hlk' htier'
  unfold wp_wakeup_body at h
  simp only [wakeupAddr, KernelSyms.«wakeup»] at h
  exact h

/-- The payload cells at the ambient context are ordinary points-to (`rfl`). -/
theorem kx_wordAtN_wp (va : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    wordAtN (GF := GF) curCtx va n dq w ⊢ wordPointsTo va n dq w := by rw [wordAtN_cur]

theorem kx_wp_wordAtN (va : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    wordPointsTo (GF := GF) va n dq w ⊢ wordAtN curCtx va n dq w := by rw [wordAtN_cur]

theorem kx_procPubRest_split (pa : BitVec 64) (kl xs pid : BitVec 32) :
    procPubRest (GF := GF) pa kl xs pid ⊢
      wordPointsTo (pKilled pa) 4 (DFrac.own 1) kl ∗ wordPointsTo (pXstate pa) 4 (DFrac.own 1) xs ∗
      wordPointsTo (pPid pa) 4 pidPub pid := by unfold procPubRest; iintro H; iexact H

theorem kx_procPubRest_join (pa : BitVec 64) (kl xs pid : BitVec 32) :
    wordPointsTo (GF := GF) (pKilled pa) 4 (DFrac.own 1) kl ∗
      wordPointsTo (pXstate pa) 4 (DFrac.own 1) xs ∗ wordPointsTo (pPid pa) 4 pidPub pid ⊢
      procPubRest pa kl xs pid := by unfold procPubRest; iintro H; iexact H

set_option maxHeartbeats 8000000 in
/-- **`kexit`'s tail** from `0x8000214a`: `begin_op(); iput(p->cwd); end_op();
p->cwd=0;` then the lock section and the ZOMBIE park. -/
theorem kx_rest (AC : ACQUIRE) (RE : RELEASE) (RP : REPARENT) (WU : WAKEUP) (SC : SCHED) [FsEnv]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] (γw : GName) (j : Nat) (hj : j < NPROC)
    (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (ip : BitVec 64)
    (status : BitVec 64) (spval : BitVec 64) (availval : Nat)
    (hV : V.sz.toNat ≤ uvmMaxsz ∧ umBelow V.sz V.upt ∧
      V.pagetable = pageAddr V.upt.root ∧ V.trapframe = pageAddr V.upt.tfp)
    (hinit : procAddr j ≠ ip)
    (c : CPU) (k : KCtx) (hf : kxFrame k j status spval availval) :
    kctx c k ∗ pcIs c 0x8000214a#64 ∗ procsInv Γ ∗ trapCsrs c ∗ cpuClaim c (procAddr j) ∗ intrRes c ∗
    ofileCells (procAddr j) (DFrac.own 1) (List.replicate NOFILE 0#64) ∗
    wordPointsTo (pPid (procAddr j)) 4 pidPriv pid ∗
    wordPointsTo (pKstack (procAddr j)) 8 (DFrac.own 1) V.kstack ∗
    wordPointsTo (pSz (procAddr j)) 8 (DFrac.own 1) V.sz ∗
    wordPointsTo (pPagetable (procAddr j)) 8 (DFrac.own 1) V.pagetable ∗
    wordPointsTo (pTrapframe (procAddr j)) 8 (DFrac.own 1) V.trapframe ∗
    wordPointsTo (pCwd (procAddr j)) 8 (DFrac.own 1) V.cwd ∗
    pnameCells (procAddr j) (DFrac.own 1) V.name ∗
    procPtAt V.upt M ∗ tfPageAt V.upt.tfp V.tf ∗
    stackOwn (spval + 48#64) 6 ∗
    (stackOwn (spval + 48#64) (availval + 6) -∗ stackOwn (V.kstack + 4096#64) 512) ∗
    isLock γw waitLockAddr "wait_lock" waitLockPay ∗ initprocIs ip
    ⊢ wpLoop (GF := GF) c := by
  obtain ⟨ξ0, t0⟩ := X
  letI : CurCtx := ⟨ξ0, t0⟩
  have hsie : k.sie = false := hf.1
  have hav : k.avail = availval := hf.2.2.2.2.2.2.2.2.2.2
  iintro ⟨Hk, Hpc, #Hpinv, Htc, Hclaim, Hres, Hofile, Hpid, Hks, Hsz, Hpg, Htf,
    Hcwd, Hname, HPt, HTf, Hframe, Hcloser, #Hwl, #Hinit⟩
  icases kctx_tier c k $$ Hk with ⟨%hct, Hk⟩
  have ht0 : t0 = KTier.kpt := hct.symm.trans hf.2.2.2.1
  subst ht0
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  -- jal begin_op
  k_step (wp_s_jal c _ 0x8000214a#64 false 7192#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  have hf1 : kxFrame (k.setReg 1#5 0x8000214e#64) j status spval availval :=
    kx_setReg_frame k j status spval 1#5 _ hf (by decide) (by decide) (by decide) (by decide)
  iapply (kx_fs beginOpAddr 0x80003d62#64 rfl FsEnv.begin_op Γ status spval availval c
    (k.setReg 1#5 0x8000214e#64) j hj hf1) $$ [- $Hk $Hpc $Hpinv $Htc $Hclaim $Hres]
  iapply wpNext_intro_pin
  iintro %c1 %hpin1
  iintro %spie1 %spp1 %R1 Hk Hpc Htc Hclaim Hres %hcs1
  have hjp1 : jumpPc ((k.setReg 1#5 0x8000214e#64).regs 1#5) = 0x8000214e#64 := by
    rw [KCtx.setReg_regs, RegMap.set_apply, if_pos rfl]; decide
  ihave Hpc := (show pcIs (GF := GF) c1 (jumpPc ((k.setReg 1#5 0x8000214e#64).regs 1#5)) ⊢
      pcIs c1 0x8000214e#64 from by rw [hjp1]) $$ Hpc
  have hf1 := kxFrame_cross hf1 spie1 spp1 R1 hcs1
  -- ld a0,336(s3)
  k_step (wp_s_ld c1 _ 0x8000214e#64 false 336#12 10#5 19#5 (by decide) (by decide)
      (DFrac.own 1) V.cwd)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, hf1.2.2.2.2.2.2.2.1, kx_pCwd0, KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc Hcwd
  have hf1a : kxFrame (((k.setReg 1#5 0x8000214e#64).withSpie spie1 spp1).withRegs
      (R1.set 10#5 V.cwd)) j status spval availval :=
    kx_setReg_frame _ j status spval 10#5 V.cwd hf1 (by decide) (by decide) (by decide) (by decide)
  -- jal iput
  k_step (wp_s_jal c1 _ 0x80002152#64 false 4904#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  have hf1b : kxFrame (((k.setReg 1#5 0x8000214e#64).withSpie spie1 spp1).withRegs
      ((R1.set 10#5 V.cwd).set 1#5 0x80002156#64)) j status spval availval :=
    kx_setReg_frame _ j status spval 1#5 0x80002156#64 hf1a
      (by decide) (by decide) (by decide) (by decide)
  iapply (kx_fs iputAddr 0x8000347a#64 rfl FsEnv.iput Γ status spval availval c1 _ j hj hf1b)
    $$ [- $Hk $Hpc $Hpinv $Htc $Hclaim $Hres]
  iapply wpNext_intro_pin
  iintro %c2 %hpin2
  iintro %spie2 %spp2 %R2 Hk Hpc Htc Hclaim Hres %hcs2
  ihave Hpc := (kx_pcIs_jump c2 _ (R1.set 10#5 V.cwd) 0x80002156#64 (by decide)) $$ Hpc
  have hf2 := kxFrame_cross hf1b spie2 spp2 R2 hcs2
  -- jal end_op
  k_step (wp_s_jal c2 _ 0x80002156#64 false 7320#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  have hf2a := kx_setReg_frame _ j status spval 1#5 0x8000215a#64 hf2
    (by decide) (by decide) (by decide) (by decide)
  iapply (kx_fs endOpAddr 0x80003dee#64 rfl FsEnv.end_op Γ status spval availval c2 _ j hj ?hfe)
    $$ [- $Hk $Hpc $Hpinv $Htc $Hclaim $Hres]
  case hfe => exact hf2a
  iapply wpNext_intro_pin
  iintro %c3 %hpin3
  iintro %spie3 %spp3 %R3 Hk Hpc Htc Hclaim Hres %hcs3
  ihave Hpc := (kx_pcIs_jump c3 _ R2 0x8000215a#64 (by decide)) $$ Hpc
  have hf3 := kxFrame_cross hf2a spie3 spp3 R3 hcs3
  have h19R3 : R3 19#5 = procAddr j := hf3.2.2.2.2.2.2.2.1
  -- sd zero,336(s3): p->cwd = 0
  k_step (wp_s_sd c3 _ 0x8000215a#64 false 336#12 19#5 0#5 (by decide) V.cwd)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, KCtx.withRegs_regs, h19R3, kx_pCwd0, KCtx.rget_zero, KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc Hcwd
  -- ==== the lock section (0x8000215e → 0x80002194) ====
  -- acquire(&wait_lock): auipc a0,0x10; addi a0,a0,752; jal acquire
  k_step (wp_s_auipc c3 _ 0x8000215e#64 false 16#20 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  k_step (wp_s_addi c3 _ 0x80002162#64 false 746#12 10#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, kx_wl_addr1, KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  k_step (wp_s_jal c3 _ 0x80002166#64 false 2091762#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  -- acquire(&wait_lock) at 0x80000c58
  have hacw : ∀ (k' : KCtx) (hsie' : k'.sie = false) (hnoff' : k'.noff + 1 < 2 ^ 31)
      (hK' : 10 ≤ k'.avail) (hs' : "wait_lock" ∉ k'.locks) (ha0 : k'.regs 10#5 = waitLockAddr),
      kctx c3 k' ∗ pcIs c3 0x80000c58#64 ∗ isLock γw waitLockAddr "wait_lock" waitLockPay ∗
      (∀ R' : RegMap,
        kctx c3 (((k'.pushOffAt k'.spie k'.spp).withRegs R').withLocks ("wait_lock" :: k'.locks)) -∗
        pcIs c3 (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ locked γw c3 -∗
        waitLockPay curCtx -∗ (∃ K : Nat, viewLb c3 K) -∗ sieArm c3 k'.sie k'.proc -∗ wpLoop c3)
      ⊢ wpLoop (GF := GF) c3 := by
    intro k' hsie' hnoff' hK' hs' ha0
    have h := AC.wp_acquire (hlc := hlc) (GF := GF) c3 k' γw "wait_lock" waitLockPay hnoff' hK' hs'
    unfold wp_acquire_body at h
    simp only [acquireAddr, KernelSyms.«acquire»] at h
    rw [ha0] at h
    iintro ⟨Hk, Hp, #Hlk', Hcont⟩
    iapply h
    iframe Hk Hp Hlk'
    rw [hsie']
    iapply wpNext_off_intro
    iintro %spie %spp %R' %hsp Hk Hp %hcs Hlocked HR Hview Harm
    obtain ⟨rfl, rfl⟩ := hsp rfl
    iapply Hcont $$ %R' Hk Hp %hcs Hlocked HR Hview Harm
  iapply (hacw _ ?hsA ?hnA ?hKA ?hlA ?ha0A) $$ [- $Hk $Hpc $Hwl]
  rotate_right 1
  case hsA => k_norm [KCtx.setReg_sie, hf.1]
  case hnA => k_norm [KCtx.setReg_noff, hf.2.1]; omega
  case hKA =>
    have := hf.2.2.2.2.2.1; unfold fsSlots at this
    k_norm [KCtx.setReg_avail]; omega
  case hlA => k_norm [KCtx.setReg_locks, hf.2.2.1]; exact List.not_mem_nil
  case ha0A => k_norm [KCtx.setReg_regs, RegMap.set_apply]; rfl
  iintro %R4 Hk Hpc %hcs4 Hlocked HR Hview Harm
  ihave Hpc := (kx_pcIs_jump c3 _ _ 0x8000216a#64 (by decide)) $$ Hpc
  ihave HW := (show waitLockPay (GF := GF) curCtx ⊢ ∃ parents, waitResAt curCtx parents from by
    unfold waitLockPay; iintro H; iexact H) $$ HR
  icases HW with ⟨%parents, HW⟩
  unfold calleeSaved at hcs4
  k_norm at hcs4
  obtain ⟨c4_2, c4_8, c4_9, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27⟩ := hcs4
  have hW19 : R4 19#5 = procAddr j := c4_19.trans h19R3
  -- c.mv a0,s3
  k_step (wp_s_add c3 _ 0x8000216a#64 true 10#5 0#5 19#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, hW19, KCtx.rget_zero]
  iintro Hk Hpc
  -- jal reparent
  k_step (wp_s_jal c3 _ 0x8000216c#64 false 2096956#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  -- reparent(p)
  iapply (kx_reparent RP Γ c3 _ parents ip (procAddr j) ?ha0R ?hnR ?hKR ?hlR ?hwR ?htR)
    $$ [- $Hk $Hpc $Hpinv $Hinit $HW]
  rotate_right 1
  case ha0R => k_norm [KCtx.setReg_regs, RegMap.set_apply]
  case hnR => k_norm [KCtx.setReg_noff, hf.2.1]; omega
  case hKR =>
    have := hf.2.2.2.2.2.1; unfold fsSlots at this
    k_norm [KCtx.setReg_avail]; unfold reparentSlots; omega
  case hlR => k_norm [KCtx.setReg_locks, hf.2.2.1]; decide
  case hwR => k_norm [KCtx.setReg_locks]; simp
  case htR => k_norm [KCtx.setReg_tier, hf.2.2.2.1]
  -- past reparent: hart pinned (interrupts off), payload rewritten
  iapply wpNext_intro_pin
  iintro %c5 %hp5 %spie5 %spp5 %R5 %hsp5 Hk Hpc HWrep %hcs5
  have hc5 : c5 = c3 := by apply hp5; left; k_norm [KCtx.setReg_sie, hf.1]
  subst c5
  ihave Hpc := (kx_pcIs_jump c3 _ _ 0x80002170#64 (by decide)) $$ Hpc
  unfold calleeSaved at hcs5
  k_norm at hcs5
  obtain ⟨c5_2, c5_8, c5_9, c5_18, c5_19, c5_20, c5_21, c5_22, c5_23, c5_24, c5_25, c5_26, c5_27⟩ := hcs5
  have hR5_19 : R5 19#5 = procAddr j := c5_19.trans hW19
  -- open p->parent out of the payload
  icases waitRes_acc curCtx (reparented parents (procAddr j) ip) j hj $$ HWrep with ⟨Hword, Hback⟩
  ihave Hword := kx_wordAtN_wp (pParent (procAddr j)) 8 (DFrac.own 1)
    ((reparented parents (procAddr j) ip) j) $$ Hword
  -- ld a0,56(s3): a0 = p->parent
  k_step (wp_s_ld c3 _ 0x80002170#64 false 56#12 10#5 19#5 (by decide) (by decide) (DFrac.own 1)
      ((reparented parents (procAddr j) ip) j))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, hR5_19, kx_pParent, KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc Hword
  -- put the parent word back (unchanged)
  ihave Hword := kx_wp_wordAtN (pParent (procAddr j)) 8 (DFrac.own 1)
    ((reparented parents (procAddr j) ip) j) $$ Hword
  ihave HWrep := Hback $$ %((reparented parents (procAddr j) ip) j) Hword
  -- jal wakeup
  k_step (wp_s_jal c3 _ 0x80002174#64 false 2096846#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  -- wakeup(p->parent)
  iapply (kx_wakeup WU Γ c3 _ ?hnW ?hKW ?hlW ?htW) $$ [- $Hk $Hpc $Hpinv]
  rotate_right 1
  case hnW => k_norm [KCtx.setReg_noff, hf.2.1]; omega
  case hKW =>
    have := hf.2.2.2.2.2.1; unfold fsSlots at this
    k_norm [KCtx.setReg_avail]; unfold wakeupSlots; omega
  case hlW => k_norm [KCtx.setReg_locks, hf.2.2.1]; decide
  case htW => k_norm [KCtx.setReg_tier, hf.2.2.2.1]
  -- past wakeup: hart pinned (interrupts off)
  iapply wpNext_intro_pin
  iintro %c6 %hp6 %spie6 %spp6 %R6 %hsp6 Hk Hpc %hcs6
  have hc6 : c6 = c3 := by apply hp6; left; k_norm [KCtx.setReg_sie, hf.1]
  subst c6
  ihave Hpc := (kx_pcIs_jump c3 _ _ 0x80002178#64 (by decide)) $$ Hpc
  unfold calleeSaved at hcs6
  k_norm at hcs6
  obtain ⟨d6_2, d6_8, d6_9, d6_18, d6_19, d6_20, d6_21, d6_22, d6_23, d6_24, d6_25, d6_26, d6_27⟩ := hcs6
  have hd6_19 : R6 19#5 = procAddr j := d6_19.trans hR5_19
  -- acquire(&p->lock): c.mv a0,s3; jal acquire
  k_step (wp_s_add c3 _ 0x80002178#64 true 10#5 0#5 19#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, hd6_19, KCtx.rget_zero]
  iintro Hk Hpc
  k_step (wp_s_jal c3 _ 0x8000217a#64 false 2091742#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  ihave #Hlk := procsInv_lookup Γ j hj $$ Hpinv
  have hacp : ∀ (k' : KCtx) (hsie' : k'.sie = false) (hnoff' : k'.noff + 1 < 2 ^ 31)
      (hK' : 10 ≤ k'.avail) (hs' : "proc" ∉ k'.locks) (ha0 : k'.regs 10#5 = procAddr j),
      kctx c3 k' ∗ pcIs c3 0x80000c58#64 ∗ isLock (Γ.lock j) (procAddr j) "proc" (procLockPay Γ j) ∗
      (∀ R' : RegMap,
        kctx c3 (((k'.pushOffAt k'.spie k'.spp).withRegs R').withLocks ("proc" :: k'.locks)) -∗
        pcIs c3 (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ locked (Γ.lock j) c3 -∗
        procLockPay Γ j curCtx -∗ (∃ K : Nat, viewLb c3 K) -∗ sieArm c3 k'.sie k'.proc -∗ wpLoop c3)
      ⊢ wpLoop (GF := GF) c3 := by
    intro k' hsie' hnoff' hK' hs' ha0
    have h := AC.wp_acquire (hlc := hlc) (GF := GF) c3 k' (Γ.lock j) "proc" (procLockPay Γ j)
      hnoff' hK' hs'
    unfold wp_acquire_body at h
    simp only [acquireAddr, KernelSyms.«acquire»] at h
    rw [ha0] at h
    iintro ⟨Hk, Hp, #Hlk', Hcont⟩
    iapply h
    iframe Hk Hp Hlk'
    rw [hsie']
    iapply wpNext_off_intro
    iintro %spie %spp %R' %hsp Hk Hp %hcs Hlocked2 HRp Hview2 Harm2
    obtain ⟨rfl, rfl⟩ := hsp rfl
    iapply Hcont $$ %R' Hk Hp %hcs Hlocked2 HRp Hview2 Harm2
  iapply (hacp _ ?hsP ?hnP ?hKP ?hlP ?ha0P) $$ [- $Hk $Hpc $Hlk]
  rotate_right 1
  case hsP => k_norm [KCtx.setReg_sie, hf.1]
  case hnP => k_norm [KCtx.setReg_noff, hf.2.1]; omega
  case hKP =>
    have := hf.2.2.2.2.2.1; unfold fsSlots at this
    k_norm [KCtx.setReg_avail]; omega
  case hlP => k_norm [KCtx.setReg_locks, hf.2.2.1]; decide
  case ha0P => k_norm [KCtx.setReg_regs, RegMap.set_apply, hd6_19]
  iintro %R7 Hk Hpc %hcs7 Hlocked2 HRp Hview2 Harm2
  ihave Hpc := (kx_pcIs_jump c3 _ _ 0x8000217e#64 (by decide)) $$ Hpc
  unfold calleeSaved at hcs7
  k_norm at hcs7
  obtain ⟨e7_2, e7_8, e7_9, e7_18, e7_19, e7_20, e7_21, e7_22, e7_23, e7_24, e7_25, e7_26, e7_27⟩ := hcs7
  have hR7_19 : R7 19#5 = procAddr j := e7_19.trans hd6_19
  have hR7_20 : R7 20#5 = status :=
    e7_20.trans (d6_20.trans (c5_20.trans (c4_20.trans hf3.2.2.2.2.2.2.2.2.1)))
  -- the payload & the claim: this hart runs proc j, so the slot is RUNNING
  ihave HR := (show procLockPay (GF := GF) Γ j curCtx ⊢ procLockResAt Γ ξ0 (procAddr j) from by
      unfold procLockPay; iintro H; iexact H) $$ HRp
  icases procLockRes_elim Γ ξ0 (procAddr j) $$ HR with
    ⟨%st, %ch, Hstate, Hpsl, Hchan, ⟨%kl, %xs, %pid2, Hrest⟩, Hslots⟩
  ihave Hcl := (show cpuClaim (hlc := hlc) (GF := GF) c3 (procAddr j) ⊢
      pstateHlf Γ j RUNNING ∗ hartHlf Γ j c3 from by
      rw [cpuClaim_eq Γ]; exact procClaim_elim Γ c3 j hj) $$ Hclaim
  icases Hcl with ⟨Hpst, Hhart⟩
  icases procSlots_running Γ ξ0 j c3 st hj $$ [$Hhart $Hslots] with ⟨%hstr, Htag, Hcells, Hvc⟩
  subst hstr
  have hsplit := pstateWhole_split (GF := GF) Γ (procAddr j) RUNNING
  rw [if_neg (by decide : ¬ unclaimed RUNNING)] at hsplit
  ihave Hpst := pstateAt_intro Γ j (1 : Qp).half RUNNING hj $$ Hpst
  ihave Hwhole := hsplit.mpr $$ [$Hpsl $Hpst]
  icases kx_procPubRest_split (procAddr j) kl xs pid2 $$ Hrest with ⟨Hkilled, Hxstate, Hpidpub⟩
  -- sw s4,44(s3): p->xstate = status
  k_step (wp_s_sw c3 _ 0x8000217e#64 false 44#12 19#5 20#5 (by decide) xs)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, hR7_19, kx_pXstate]
  iintro Hk Hpc Hxstate
  -- c.li a5,5
  k_step (wp_s_addi c3 _ 0x80002182#64 true 5#12 15#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq]
  iintro Hk Hpc
  -- sw a5,24(s3): p->state = ZOMBIE
  k_step (wp_s_sw c3 _ 0x80002184#64 false 24#12 19#5 15#5 (by decide) RUNNING)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, hR7_19, kx_pState, KCtx.setReg_regs, RegMap.set_apply, kx_zombie]
  iintro Hk Hpc Hstate
  -- the mirror follows the cell: RUNNING → ZOMBIE
  iapply wpLoop_bupd
  imod (pstateWhole_update Γ (procAddr j) RUNNING ZOMBIE) $$ Hwhole with Hwhole
  imodintro
  -- the held p->lock at ZOMBIE, kept aside through the release
  ihave Hrest := kx_procPubRest_join (procAddr j) kl _ pid2 $$ [$Hkilled $Hxstate $Hpidpub]
  ihave Hheld := procHeldAt_intro Γ ξ0 c3 j ZOMBIE ch kl _ pid2
    $$ [$Hlocked2 $Hwhole $Hstate $Hchan $Hrest]
  -- release(&wait_lock): auipc a0,0x10; addi a0,a0,710; jal release
  k_step (wp_s_auipc c3 _ 0x80002188#64 false 16#20 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  k_step (wp_s_addi c3 _ 0x8000218c#64 false 704#12 10#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [KCtx.rget_eq, kx_wl_addr2, KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  k_step (wp_s_jal c3 _ 0x80002190#64 false 2091856#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  have hrew : ∀ (k' : KCtx) (hsie' : k'.sie = false) (hnoff' : 1 ≤ k'.noff)
      (hK' : 10 ≤ k'.avail) (hreen0 : k'.noff ≠ 1) (ha0 : k'.regs 10#5 = waitLockAddr),
      kctx c3 k' ∗ pcIs c3 0x80000ce0#64 ∗ isLock γw waitLockAddr "wait_lock" waitLockPay ∗
      locked γw c3 ∗ waitLockPay curCtx ∗
      (∀ R' : RegMap,
        kctx c3 ((k'.popOff.withRegs R').withLocks (k'.locks.filter (fun x => x ≠ "wait_lock"))) -∗
        pcIs c3 (jumpPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ wpLoop c3)
      ⊢ wpLoop (GF := GF) c3 := by
    intro k' hsie' hnoff' hK' hreen0 ha0
    have hreen : false = (decide (k'.noff = 1) && k'.intena) := by
      simp [hreen0]
    have hon : (false : Bool) = true → k'.tier = KTier.kpt ∧ trapRes true + 6 ≤ k'.avail := by
      intro hc; exact absurd hc (by decide)
    have h := RE.wp_release (hlc := hlc) (GF := GF) c3 k' γw "wait_lock" waitLockPay
      hsie' hnoff' hK' false hreen hon
    unfold wp_release_body at h
    simp only [releaseAddr, KernelSyms.«release», KCtx.popExit_false, popArm_false,
      KCtx.popOff_sie, hsie'] at h
    rw [ha0] at h
    iintro ⟨Hk, Hp, #Hlk', Hlocked, HR, Hcont⟩
    iapply h
    iframe Hk Hp Hlk' Hlocked HR
    isplitl []
    · iempintro
    iapply wpNext_off_intro
    iintro %R' Hk Hp %hcs
    iapply Hcont $$ %R' Hk Hp %hcs
  ihave HWpay := (show waitResAt (GF := GF) curCtx _ ⊢ waitLockPay curCtx from by
    unfold waitLockPay; iintro H; iexists _; iexact H) $$ HWrep
  iapply (hrew _ ?hsRl ?hnRl ?hKRl ?hrRl ?ha0Rl) $$ [- $Hk $Hpc $Hwl $Hlocked $HWpay]
  rotate_right 1
  case hsRl => k_norm [KCtx.setReg_sie, hf.1]
  case hnRl => k_norm [KCtx.setReg_noff, hf.2.1]; omega
  case hKRl =>
    have := hf.2.2.2.2.2.1; unfold fsSlots at this
    k_norm [KCtx.setReg_avail]; omega
  case hrRl => k_norm [KCtx.setReg_noff, hf.2.1]; omega
  case ha0Rl => k_norm [KCtx.setReg_regs, RegMap.set_apply]; rfl
  iintro %R8 Hk Hpc %hcs8
  ihave Hpc := (kx_pcIs_jump c3 _ _ 0x80002194#64 (by decide)) $$ Hpc
  -- jal sched
  k_step (wp_s_jal c3 _ 0x80002194#64 false 2096474#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.setReg_sie, KCtx.setReg_proc]
  iintro Hk Hpc
  unfold calleeSaved at hcs8
  k_norm at hcs8
  obtain ⟨f8_2, f8_8, f8_9, f8_18, f8_19, f8_20, f8_21, f8_22, f8_23, f8_24, f8_25, f8_26, f8_27⟩ := hcs8
  have hR8_2 : R8 2#5 = spval :=
    f8_2.trans (e7_2.trans (d6_2.trans (c5_2.trans (c4_2.trans hf3.2.2.2.2.2.2.2.2.2.1))))
  -- sched()'s ZOMBIE park: needsCtx ZOMBIE = false, so the continuation is emp
  have hsc : ∀ (k' : KCtx) (ch' : BitVec 64) (hK' : schedSlots ≤ k'.avail) (hsie' : k'.sie = false)
      (hnoff' : k'.noff = 1) (hlocks' : k'.locks = ["proc"]) (htier' : k'.tier = KTier.kpt)
      (hproc' : k'.proc = procAddr j) (hsp' : k'.sp = spval) (hav' : k'.avail = availval),
      kctx c3 k' ∗ pcIs c3 0x80001eee#64 ∗ procsInv Γ ∗ procHeld Γ c3 j ZOMBIE ch' ∗
      (stackOwn spval availval -∗ parkPay (procAddr j) ZOMBIE) ∗
      trapCsrs c3 ∗ intrRes c3 ∗ ownCtxCells (pContext (procAddr j) 0) ∗ hartFull Γ j c3 ∗
      ▷ schedVcAt Γ c3 (cpuCtxAddr c3) (procAddr j)
      ⊢ wpLoop (GF := GF) c3 := by
    intro k' ch' hK' hsie' hnoff' hlocks' htier' hproc' hsp' hav'
    have h := SC.wp_sched (hlc := hlc) (GF := GF) Γ c3 k' j ZOMBIE ch' hj
      kx_parkOk_zombie hK' hsie' hnoff' hlocks' htier' hproc'
    unfold wp_sched_body at h
    rw [if_neg kx_needsCtx_zombie] at h
    simp only [schedAddr, KernelSyms.«sched»] at h
    rw [hsp', hav'] at h
    iintro ⟨Hk, Hpc, #Hpinv, Hheld, Hwand, Htc, Hres, Hcells, Htag, Hvc⟩
    iapply h
    iframe Hk Hpc Hpinv Hheld Hwand Htc Hres Hcells Htag Hvc
  -- the park wand: the zeroed private block + the whole kernel stack → procDormantNoctx
  have hsub : (spval + 48#64) - 8#64 * BitVec.ofNat 64 6 = spval := by bv_omega
  ihave Hpriv := (show
      wordPointsTo (pPid (procAddr j)) 4 pidPriv pid ∗
      wordPointsTo (pKstack (procAddr j)) 8 (DFrac.own 1) V.kstack ∗
      wordPointsTo (pSz (procAddr j)) 8 (DFrac.own 1) V.sz ∗
      wordPointsTo (pPagetable (procAddr j)) 8 (DFrac.own 1) V.pagetable ∗
      wordPointsTo (pTrapframe (procAddr j)) 8 (DFrac.own 1) V.trapframe ∗
      wordPointsTo (pCwd (procAddr j)) 8 (DFrac.own 1) 0#64 ∗
      pnameCells (procAddr j) (DFrac.own 1) V.name ∗
      ofileCells (procAddr j) (DFrac.own 1) (List.replicate NOFILE 0#64) ∗
      procPtAt V.upt M ∗ tfPageAt V.upt.tfp V.tf ⊢
      procPrivNoctxAt (GF := GF) ξ0 (procAddr j) pid
        { V with ofile := List.replicate NOFILE 0#64, cwd := 0#64 } M from by
    unfold procPrivNoctxAt procFieldsNoctx
    iintro ⟨Hpid, Hks, Hsz, Hpg, Htf, Hcwd, Hname, Hofile, HPt, HTf⟩
    isplitl []
    · ipureintro; exact hV
    iframe) $$ [$Hpid $Hks $Hsz $Hpg $Htf $Hcwd $Hname $Hofile $HPt $HTf]
  ihave Hwand : (stackOwn (GF := GF) spval availval -∗ parkPay (procAddr j) ZOMBIE)
    $$ [Hpriv Hframe Hcloser]
  case' _ =>
    iintro Hstk
    ihave Hbig : stackOwn (GF := GF) (spval + 48#64) (availval + 6) $$ [Hframe Hstk]
    case' _ =>
      rw [Nat.add_comm availval 6]
      iapply stackOwn_join (spval + 48#64) 6 availval
      isplitl [Hframe]
      · iexact Hframe
      · rw [hsub]; iexact Hstk
    ihave Hstack512 := Hcloser $$ [$Hbig]
    ihave Hdorm := kx_dormant_build ξ0 (procAddr j) pid
      { V with ofile := List.replicate NOFILE 0#64, cwd := 0#64 } M rfl rfl $$ [$Hpriv $Hstack512]
    unfold parkPay parkPayAt
    rw [if_pos kx_invDormant_zombie]
    iexact Hdorm
  iapply (hsc _ ch ?hKsc ?hssc ?hnsc ?hlsc ?htsc ?hpsc ?hspsc ?havsc)
    $$ [- $Hk $Hpc $Hpinv $Hheld $Hwand $Htc $Hres $Hcells $Htag $Hvc]
  rotate_right 1
  case hKsc =>
    have := hf.2.2.2.2.2.1; unfold fsSlots at this
    k_norm [KCtx.setReg_avail, KCtx.popOff_avail, KCtx.pushOffAt_avail, trapRes_off, hf.1]
    unfold schedSlots; omega
  case hssc => k_norm [KCtx.setReg_sie, hf.1]
  case hnsc => k_norm [KCtx.setReg_noff, KCtx.popOff_noff, KCtx.pushOffAt_noff, hf.2.1]
  case hlsc => k_norm [KCtx.setReg_locks, hf.2.2.1]; decide
  case htsc => k_norm [KCtx.setReg_tier, hf.2.2.2.1]
  case hpsc => k_norm [KCtx.setReg_proc, hf.2.2.2.2.1]
  case hspsc =>
    show _ = spval
    k_norm [KCtx.setReg_regs, RegMap.set_apply, KCtx.popOff_sp, KCtx.sp_withLocks]
    exact hR8_2
  case havsc =>
    k_norm [KCtx.setReg_avail, KCtx.popOff_avail, KCtx.pushOffAt_avail, KCtx.setReg_sie,
      trapRes_off, hf.1, hav]

end

/-! ## The whole function -/

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [X : CurCtx]

/-- `&initproc` from `auipc a5,0x8; ld a5,536(a5)` at `0x80002116`. -/
theorem kx_initproc_addr :
    (0x80002116#64 : BitVec 64) + (BitVec.signExtend 64 (8#20 ++ 0#12) + 554#64) = initprocAddr := by
  decide

/-- `initprocIs` opened to its points-to (`rfl`). -/
theorem kx_initprocIs_wp (ip : BitVec 64) :
    initprocIs (GF := GF) ip ⊢ wordPointsTo initprocAddr 8 DFrac.discard ip := by
  unfold initprocIs; iintro H; iexact H

/-- The immediate `-48` folds, `spval + 48 = sp`. -/
theorem kx_sp48 (sp : BitVec 64) : (sp - 8#64 * BitVec.ofNat 64 6) + 48#64 = sp := by bv_omega

end

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
/-- **`kexit` meets its specification.** -/
theorem kexit_proof (MP : MYPROC) (AC : ACQUIRE) (RE : RELEASE) (RP : REPARENT) (WU : WAKEUP)
    (SC : SCHED) : KEXIT :=
  ⟨fun {hlc GF} _ _ X Γ _ _ cpu k γw j pid V M ip hj hproc hK hsie hnoff hlocks htier hinit => by
  obtain ⟨ξ0, t0⟩ := X
  letI : CurCtx := ⟨ξ0, t0⟩
  unfold wp_kexit_body
  simp only [kexitAddr, KernelSyms.«kexit»]
  iintro ⟨Hk, Hpc, #Hpinv, Htc, Hclaim, Hres, #Hwl, #Hinit, Hpriv, Hcloser⟩
  icases kctx_tier cpu k $$ Hk with ⟨%hct, Hk⟩
  have ht0 : t0 = KTier.kpt := hct.symm.trans htier
  subst ht0
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  ihave Hclaim := (show cpuClaim (hlc := hlc) (GF := GF) cpu k.proc ⊢ cpuClaim cpu (procAddr j) from by
    rw [hproc]) $$ Hclaim
  have hK6 : 6 ≤ k.avail := by unfold kexitSlots fsSlots at hK; omega
  -- unpack the private block: the ofile scan takes the ofile cells, the rest goes to Ψ
  icases (show procPrivNoctxAt (GF := GF) curCtx (procAddr j) pid V M ⊢
      ⌜V.sz.toNat ≤ uvmMaxsz ∧ umBelow V.sz V.upt ∧
        V.pagetable = pageAddr V.upt.root ∧ V.trapframe = pageAddr V.upt.tfp⌝ ∗
      wordPointsTo (pPid (procAddr j)) 4 pidPriv pid ∗
      (wordPointsTo (pKstack (procAddr j)) 8 (DFrac.own 1) V.kstack ∗
       wordPointsTo (pSz (procAddr j)) 8 (DFrac.own 1) V.sz ∗
       wordPointsTo (pPagetable (procAddr j)) 8 (DFrac.own 1) V.pagetable ∗
       wordPointsTo (pTrapframe (procAddr j)) 8 (DFrac.own 1) V.trapframe ∗
       (⌜V.ofile.length = NOFILE⌝ ∗
         ([∗list] i ↦ f ∈ V.ofile, wordPointsTo (pOfile (procAddr j) i) 8 (DFrac.own 1) f)) ∗
       wordPointsTo (pCwd (procAddr j)) 8 (DFrac.own 1) V.cwd ∗
       pnameCells (procAddr j) (DFrac.own 1) V.name) ∗
      procPtAt V.upt M ∗ tfPageAt V.upt.tfp V.tf from by
    unfold procPrivNoctxAt procFieldsNoctx ofileCells; iintro H; iexact H) $$ Hpriv
    with ⟨%hVpure, Hpid, ⟨Hks, Hsz, Hpg, Htf, ⟨%hoflen, Hbig⟩, Hcwd, Hname⟩, HPt, HTf⟩
  -- the prologue: c.addi16sp sp,-48 ; six sd ; c.addi4spn s0,sp,48
  k_step (wp_s_push cpu _ 0x800020fe#64 true 4048#12 6 hK6 kx_imm_m48)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc Hframe
  irevert Hframe
  stack_cells
  iintro ⟨⟨%w0, F0⟩, ⟨%w1, F1⟩, ⟨%w2, F2⟩, ⟨%w3, F3⟩, ⟨%w4, F4⟩, ⟨%w5, F5⟩, _⟩
  k_step (wp_s_sd cpu _ 0x80002100#64 true 40#12 2#5 1#5 (by decide) w0)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc F0
  k_step (wp_s_sd cpu _ 0x80002102#64 true 32#12 2#5 8#5 (by decide) w1)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc F1
  k_step (wp_s_sd cpu _ 0x80002104#64 true 24#12 2#5 9#5 (by decide) w2)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc F2
  k_step (wp_s_sd cpu _ 0x80002106#64 true 16#12 2#5 18#5 (by decide) w3)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc F3
  k_step (wp_s_sd cpu _ 0x80002108#64 true 8#12 2#5 19#5 (by decide) w4)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc F4
  k_step (wp_s_sd cpu _ 0x8000210a#64 true 0#12 2#5 20#5 (by decide) w5)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc F5
  k_step (wp_s_addi cpu _ 0x8000210c#64 true 48#12 8#5 2#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- c.mv s4,a0: s4 = status (= a0 at entry)
  k_step (wp_s_add cpu _ 0x8000210e#64 true 20#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, KCtx.rget_zero]
  iintro Hk Hpc
  -- jal myproc
  k_step (wp_s_jal cpu _ 0x80002110#64 false 2095224#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- myproc()
  have hmp : ∀ (k' : KCtx) (hsie' : k'.sie = false) (hnoff' : k'.noff + 1 < 2 ^ 31)
      (hK' : 10 ≤ k'.avail),
      kctx cpu k' ∗ pcIs cpu 0x80001988#64 ∗
      (∀ R' : RegMap, kctx cpu (k'.withRegs R') -∗ pcIs cpu (jumpPc (k'.regs 1#5)) -∗
        ⌜calleeSaved k'.regs R' ∧ R' 10#5 = k'.proc⌝ -∗ wpLoop cpu)
      ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' hnoff' hK'
    have h := MP.wp_myproc (hlc := hlc) (GF := GF) cpu k' hnoff' hK'
    unfold wp_myproc_body at h
    simp only [myprocAddr, KernelSyms.«myproc»] at h
    iintro ⟨Hk, Hp, Hcont⟩
    iapply h
    iframe Hk Hp
    rw [hsie']
    iapply wpNext_off_intro
    iintro %spie %spp %R' %hsp Hk Hp %hcs
    obtain ⟨rfl, rfl⟩ := hsp rfl
    rw [KCtx.withSpie_self' k' _ _ rfl rfl]
    iapply Hcont $$ %_ Hk Hp %hcs
  iapply (hmp _ ?hsM ?hnM ?hKM) $$ [- $Hk $Hpc]
  rotate_right 1
  case hsM => k_norm [KCtx.setReg_sie]
  case hnM => k_norm [KCtx.setReg_noff]; omega
  case hKM => k_norm [KCtx.setReg_avail]; unfold kexitSlots fsSlots at hK; omega
  iintro %R2 Hk Hpc %⟨hcs2, h10⟩
  have hret66 : jumpPc 0x80002114#64 = 0x80002114#64 := by decide
  k_norm [hret66]
  k_norm [KCtx.setReg_proc, KCtx.push_proc] at h10
  rw [hproc] at h10
  unfold calleeSaved at hcs2
  k_norm [KCtx.setReg_regs, RegMap.set_apply, KCtx.push_regs] at hcs2
  obtain ⟨g2_2, g2_8, g2_9, g2_18, g2_19, g2_20, g2_21, g2_22, g2_23, g2_24, g2_25, g2_26, g2_27⟩ := hcs2
  -- c.mv s3,a0: s3 = p = procAddr j
  k_step (wp_s_add cpu _ 0x80002114#64 true 19#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, h10, KCtx.rget_zero]
  iintro Hk Hpc
  -- auipc a5,0x8 ; ld a5,536(a5): a5 = *initproc = ip
  ihave #Hinitw := kx_initprocIs_wp ip $$ Hinit
  k_step (wp_s_auipc cpu _ 0x80002116#64 false 8#20 15#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  iapply (wp_s_ld cpu _ 0x8000211a#64 false 554#12 15#5 15#5 (by decide) (by decide)
      DFrac.discard ip) $$ [- $Hk $Hpc]
  rotate_right 1
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  iframe #
  k_norm_g [kx_initproc_addr]
  iframe Hinitw
  inext
  iapply wpNext_intro_pin
  iintro %cld %hpld
  have hcld : cld = cpu := by
    apply hpld; left; k_norm_g [hsie]
  subst cld
  k_norm_g
  iintro Hk Hpc _
  -- addi s1,a0,208: s1 = &ofile[0]
  k_step (wp_s_addi cpu _ 0x8000211e#64 false 208#12 9#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, h10]
  iintro Hk Hpc
  -- addi s2,a0,336: s2 = &cwd
  k_step (wp_s_addi cpu _ 0x80002122#64 false 336#12 18#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [KCtx.rget_eq, h10]
  iintro Hk Hpc
  -- bne a5,a0: p != initproc, so jump to the loop at 0x8000213c
  k_step (wp_s_branch cpu _ 0x80002126#64 false 22#13 15#5 10#5 (by decide) bop.BNE)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [kx_ite_bne, KCtx.rget_eq, KCtx.setReg_regs, RegMap.set_apply, h10]
  iintro Hk Hpc
  ihave Hpc := kx_pcIs_pos cpu _ _ _ (show ip ≠ procAddr j from fun e => hinit e.symm) $$ Hpc
  -- reassemble the 6-slot frame and re-shape the stack closer
  ihave Hframe : stackOwn (GF := GF) (k.regs 2#5 - 8#64 * BitVec.ofNat 64 6 + 48#64) 6
    $$ [F0 F1 F2 F3 F4 F5]
  case' _ => rw [kx_sp48]; stack_cells; iframe
  have hav6 : (k.avail - 6) + 6 = k.avail := by unfold kexitSlots fsSlots at hK; omega
  ihave Hcloser := (show iprop(stackOwn (GF := GF) (k.regs 2#5) k.avail -∗ stackOwn (V.kstack + 4096#64) 512) ⊢
      iprop(stackOwn (k.regs 2#5 - 8#64 * BitVec.ofNat 64 6 + 48#64) ((k.avail - 6) + 6) -∗
        stackOwn (V.kstack + 4096#64) 512) from by
    rw [kx_sp48, hav6]) $$ Hcloser
  -- wire the ofile scan, whose continuation is the tail (`kx_rest`)
  iapply (kx_loop FsEnv.fileclose Γ j hj (k.regs 10#5)
      (k.regs 2#5 - 8#64 * BitVec.ofNat 64 6) (k.avail - 6)
      iprop(wordPointsTo (pPid (procAddr j)) 4 pidPriv pid ∗
        wordPointsTo (pKstack (procAddr j)) 8 (DFrac.own 1) V.kstack ∗
        wordPointsTo (pSz (procAddr j)) 8 (DFrac.own 1) V.sz ∗
        wordPointsTo (pPagetable (procAddr j)) 8 (DFrac.own 1) V.pagetable ∗
        wordPointsTo (pTrapframe (procAddr j)) 8 (DFrac.own 1) V.trapframe ∗
        wordPointsTo (pCwd (procAddr j)) 8 (DFrac.own 1) V.cwd ∗
        pnameCells (procAddr j) (DFrac.own 1) V.name ∗
        procPtAt V.upt M ∗ tfPageAt V.upt.tfp V.tf ∗
        stackOwn (k.regs 2#5 - 8#64 * BitVec.ofNat 64 6 + 48#64) 6 ∗
        (stackOwn (k.regs 2#5 - 8#64 * BitVec.ofNat 64 6 + 48#64) ((k.avail - 6) + 6) -∗
          stackOwn (V.kstack + 4096#64) 512) ∗
        isLock γw waitLockAddr "wait_lock" waitLockPay ∗ initprocIs ip)
      (fun c' kk hkk => kx_rest AC RE RP WU SC Γ γw j hj pid V M ip (k.regs 10#5)
        (k.regs 2#5 - 8#64 * BitVec.ofNat 64 6) (k.avail - 6) hVpure hinit c' kk hkk)
      15 0 (by decide) cpu _ V.ofile ?hkframe ?h9 hoflen (fun i hi => absurd hi (Nat.not_lt_zero i)))
    $$ [- $Hk $Hpc $Hpinv $Htc $Hclaim $Hres $Hbig $Hpid $Hks $Hsz $Hpg $Htf $Hcwd $Hname
        $HPt $HTf $Hframe $Hcloser $Hwl $Hinit]
  rotate_right 2
  case hkframe =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · k_norm [KCtx.setReg_sie, KCtx.push_sie, hsie]
    · k_norm [KCtx.setReg_noff, KCtx.push_noff, hnoff]
    · k_norm [KCtx.setReg_locks, KCtx.push_locks, hlocks]
    · k_norm [KCtx.setReg_tier, KCtx.push_tier, htier]
    · k_norm [KCtx.setReg_proc, KCtx.push_proc, hproc]
    · unfold kexitSlots fsSlots at hK
      k_norm [KCtx.setReg_avail, KCtx.push_avail, KCtx.withRegs_avail]
      unfold fsSlots; omega
    · show _ = pCwd (procAddr j)
      k_norm [KCtx.setReg_regs, RegMap.set_apply, h10, kx_pCwd]
    · k_norm [KCtx.setReg_regs, RegMap.set_apply]
    · show _ = k.regs 10#5
      k_norm [KCtx.setReg_regs, RegMap.set_apply, KCtx.push_regs, g2_20]
    · show _ = k.regs 2#5 - 8#64 * BitVec.ofNat 64 6
      k_norm [KCtx.setReg_regs, RegMap.set_apply, KCtx.push_regs, g2_2]
    · k_norm [KCtx.setReg_avail, KCtx.push_avail]
  case h9 =>
    show _ = pOfile (procAddr j) 0
    k_norm [KCtx.setReg_regs, RegMap.set_apply, h10, kx_pOfile0]⟩

end

end Xv6
