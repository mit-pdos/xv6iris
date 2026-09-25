/-
`namex`'s ROOT CORNER `namex("/", 0, name)` (Rocq `ProofNamexRoot.v`): a
straight line of fifty-two instructions with ONE call in it.

    +0x000 .. +0x01a  the 12-slot frame
    +0x01c .. +0x020  s1 = path, s6 = nameiparent, s5 = name
    +0x022 .. +0x02a  lbu a4,0(a0) ; li a5,47 ; beq a4,a5,+0x48   TAKEN ('/')
    +0x048 .. +0x04c  li a1,1 ; mv a0,a1 ; jal iget         iget(ROOTDEV, ROOTINO)
    +0x050 .. +0x052  s4 = a0 ; j +0x3c
    +0x03c .. +0x046  s3 = 47, s8 = 13, s9 = 14, s7 = 1 ; j +0xf4
    +0x0f4 .. +0x0f8  lbu a5,0(s1) ; bne a5,s3,+0x106        FALLS  (it is '/')
    +0x0fc .. +0x102  addi s1,s1,1 ; lbu a5,0(s1) ; beq a5,s3  FALLS  (NUL)
    +0x106            c.beqz a5,+0x140                        TAKEN
    +0x140            beq s6,zero,+0x5c                       TAKEN (a1 = 0)
    +0x05c .. +0x078  a0 = s4, the twelve restores, the pop, ret

The proof takes exactly ONE callee, `IGET`, and touches no resource but the
inode cache and the two path bytes.

**Deviation from Rocq.**  The corner runs at ANY interrupt state and depth
(it never parks): every step is a `k_step_gen`-style step whose pinning fact
shifts the contract's `wpNext` along (`k_step_r`, below), and iget is crossed
at its own `wpNext k.sie`.  The prologue / epilogue are namex's own frame
rules (`Xv6/NamexFrame.lean`), shared with the walk, as in Rocq.
-/
import Xv6.NamexFrame
import Xv6.CodeTactics

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- One step at any `SIE` and depth, the contract's continuation `Hnext`
(a `wpNext`) shifted to the step's hart, which SHADOWS the name `cpu`. -/
syntax "k_step_r" term:max " from " term:max ident " $$ " specPat : tactic
syntax "k_step_r" term:max " from " term:max ident " $$ " specPat " with " "[" term,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| k_step_r $rule:term from $code:term $ht:ident $$ $pat:specPat) =>
    `(tactic| k_step_r $rule:term from $code:term $ht:ident $$ $pat:specPat with [])
  | `(tactic| k_step_r $rule:term from $code:term $ht:ident $$ $pat:specPat with [$extra,*]) =>
    `(tactic| (iapply $rule:term $$ $pat:specPat
               rotate_right 1
               k_code $code:term $ht:ident
               iframe #
               k_norm_goal [$extra,*]
               iframe
               first
                 | inext_goal
                 | (k_norm_g [$extra,*]; iframe; inext_goal)
               iapply wpNext_intro_pin
               iintro %cpu %hpin
               try simp only [k_norm_simps] at hpin
               ihave Hnext := wpNext_shift _ _ _ _ _ hpin $$ Hnext
               clear hpin
               k_norm_g [$extra,*]
               try (case hs => k_norm_g)))

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
  [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF] [IcboxG GF]
  [SleepLockG GF] [IrefslotG GF] [CtokG GF] [WchG GF] [Appcfg GF] [Fscfg] [Icfg] [CurCtx]

theorem namex_rootc_held (kk : Nat) (q : Qp) (hkk : kk < NINODE) (hnib0 : 0 < icfgNib) :
    inodeRefb (GF := GF) (isClaim .rootL) kk q icfgDev (BitVec.ofNat 32 ROOTINO) ⊢
      inodeHeldAt (ientry kk) ROOTINO := by
  have hc : isClaim .rootL = false := rfl
  unfold inodeRefb inodeHeldAt inodeRefp
  rw [hc]
  iintro ⟨Hr, Hu⟩
  iexists kk, q, BitVec.ofNat 32 ROOTINO
  iframe Hr
  isplitr; · ipureintro; rfl
  isplitr; · ipureintro; exact hkk
  isplitr; · ipureintro; unfold ROOTINO; simp; omega
  isplitr; · ipureintro; unfold ROOTINO; simp
  isplitr; · ipureintro; unfold ROOTINO; simp
  iapply runitAny_intro; iexact Hu

/-- `iget(dev, inum)` at a call site (a copy of `Xv6.dirlookup_iget`,
DirlookupDefs; promotion candidate). -/
theorem namex_iget_call (IG : IGET) (c : CPU) (k' : KCtx) (inum : BitVec 32) (l : Ilic)
    (hK : igetSlots ≤ k'.avail) (hnoff : k'.noff + 3 < 2 ^ 31)
    (hnib : inum.toNat < 16 * icfgNib) (hpos : 0 < inum.toNat)
    (ha0 : k'.regs 10#5 = BitVec.signExtend 64 icfgDev)
    (ha1 : k'.regs 11#5 = BitVec.signExtend 64 inum)
    (hit : "itable" ∉ k'.locks) (hpr : "pr" ∉ k'.locks) (huart : "uart1" ∉ k'.locks) :
    kctx c k' ∗ pcIs c KA.«iget» ∗
    isItable2 fscItlock fscIc fscFs fscIreg fscCov fscLogst icfgNib icfgDev ∗
    itableInv (hlc := hlc) ∗ iregReg (hlc := hlc) fscIreg fscFs icfgIst icfgNib ∗ panicEnv ∗
    irefSlot ∗ iname fscIreg fscFs icfgIst inum l ∗
    wpNext k'.sie k'.proc c (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
      ⌜k'.sie = false → spie = k'.spie ∧ spp = k'.spp⌝ -∗
      kctx cpu' ((k'.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k'.regs 1#5)) -∗
      ⌜calleeSaved k'.regs R'⌝ -∗
      ∀ (kk : Nat) (q : Qp), ⌜kk < NINODE ∧ R' 10#5 = ientry kk⌝ -∗
      inodeRefb (isClaim l) kk q icfgDev inum -∗
      iname fscIreg fscFs icfgIst inum l -∗ wpLoop cpu'))
    ⊢ wpLoop (GF := GF) c := by
  have h := IG.wp_iget (hlc := hlc) (GF := GF) c k' inum l hK hnoff hnib hpos ha0 ha1 hit hpr huart
  unfold wp_iget_body at h
  simp only [igetAddr] at h
  exact h

theorem namex_root_ctx (k : KCtx) (spie spp : Bool) (R : RegMap) :
    ((k.pushed 12).withSpie spie spp).withRegs R = ((k.withSpie spie spp).pushed 12).withRegs R := by
  kctx_ext

theorem namex_root_slots (a : Nat) (h : namexRootSlots ≤ a) : igetSlots ≤ a - 12 := by
  unfold namexRootSlots at h; omega

theorem namex_root_12 (a : Nat) (h : namexRootSlots ≤ a) : 12 ≤ a := by
  unfold namexRootSlots at h; omega

/-- The root corner's continuation (the contract's, named). -/
def namexRootPost (k : KCtx) (dqp : DFrac) (cpu' : CPU) : IProp GF :=
  iprop(∀ (spie spp : Bool) (R' : RegMap) (ipv : BitVec 64),
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = ipv⌝ -∗
    byteBuf (k.regs 10#5) dqp [SLASH, 0#8] -∗
    inodeHeldAt ipv ROOTINO -∗ wpLoop cpu')

set_option maxHeartbeats 16000000 in
/-- **`+0x50 .. +0x78`, after iget**: `s4 := ip`, the constants, one turn
of the separator skip (the '/' and then the NUL), the nameiparent test, the
tail. -/
theorem namex_root_after (cpu : CPU) (k : KCtx) (dqp : DFrac) (spie spp : Bool) (R2 : RegMap)
    (kk : Nat) (hK12 : 12 ≤ k.avail) (ha1 : k.regs 11#5 = 0#64)
    (b2 : R2 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFA0#64) (b9 : R2 9#5 = k.regs 10#5)
    (b22 : R2 22#5 = k.regs 11#5) (b27 : R2 27#5 = k.regs 27#5) (ha0 : R2 10#5 = ientry kk)
    (hsp : k.sie = false → spie = k.spie ∧ spp = k.spp) (Φ : CPU → IProp GF)
    (hΦ : ∀ c, Φ c ⊢ namexRootPost k dqp c) :
    kctx cpu (((k.withSpie spie spp).pushed 12).withRegs R2) ∗ pcIs cpu (KA.«namex» + 0x50#64) ∗
    frame12 (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) (k.regs 18#5) (k.regs 19#5)
      (k.regs 20#5) (k.regs 21#5) (k.regs 22#5) (k.regs 23#5) (k.regs 24#5) (k.regs 25#5)
      (k.regs 26#5) ∗
    byteBuf (k.regs 10#5) dqp [SLASH, 0#8] ∗ inodeHeldAt (ientry kk) ROOTINO ∗
    wpNext k.sie k.proc cpu Φ
    ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨Hk, Hpc, Hframe, Hpath, Hheld, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  -- +0x50  c.mv s4,a0 ; +0x52  c.j +0x3c
  k_step_r (wp_s_add cpu _ (KA.«namex» + 0x50#64) true 20#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [ha0]
  iintro Hk Hpc
  k_step_r (wp_s_j cpu _ (KA.«namex» + 0x52#64) true 2097130#21)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- +0x3c .. +0x46  the constants, and the jump into the walk
  k_step_r (wp_s_addi cpu _ (KA.«namex» + 0x3c#64) false 47#12 19#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_addi cpu _ (KA.«namex» + 0x40#64) true 13#12 24#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_addi cpu _ (KA.«namex» + 0x42#64) true 14#12 25#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_addi cpu _ (KA.«namex» + 0x44#64) true 1#12 23#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_j cpu _ (KA.«namex» + 0x46#64) true 174#21)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- +0xf4  lbu a5,0(s1) : '/' again ; +0xf8  bne a5,s3 (FALLS)
  icases byteBuf_acc (k.regs 10#5) dqp [SLASH, 0#8] 0 SLASH rfl $$ Hpath with ⟨Hb, Hbk⟩
  isimp only [BitVec.reduceOfNat, BitVec.add_zero] at Hb Hbk
  k_step_r (wp_s_lbu cpu _ (KA.«namex» + 0xf4#64) false 0#12 15#5 9#5 (by decide) (by decide) dqp
      SLASH)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [b9]
  iintro Hk Hpc Hb
  ihave Hpath := Hbk $$ Hb
  k_step_r (wp_s_branch cpu _ (KA.«namex» + 0xf8#64) false 14#13 15#5 19#5 (by decide) bop.BNE)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [namex_slash_ofNat, (show bcond bop.BNE 47#64 47#64 = false by decide)]
  iintro Hk Hpc
  -- +0xfc  c.addi s1,s1,1 ; +0xfe  lbu a5,0(s1) : NUL ; +0x102  beq a5,s3 (FALLS)
  k_step_r (wp_s_addi cpu _ (KA.«namex» + 0xfc#64) true 1#12 9#5 9#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [b9]
  iintro Hk Hpc
  icases byteBuf_acc (k.regs 10#5) dqp [SLASH, 0#8] 1 0#8 rfl $$ Hpath with ⟨Hb, Hbk⟩
  try isimp only [BitVec.reduceOfNat] at Hb Hbk
  k_step_r (wp_s_lbu cpu _ (KA.«namex» + 0xfe#64) false 0#12 15#5 9#5 (by decide) (by decide) dqp
      0#8)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc Hb
  ihave Hpath := Hbk $$ Hb
  k_step_r (wp_s_branch cpu _ (KA.«namex» + 0x102#64) false 8186#13 15#5 19#5 (by decide) bop.BEQ)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [(show bcond bop.BEQ 0#64 47#64 = false by decide)]
  iintro Hk Hpc
  -- +0x106  c.beqz a5,+0x140 (TAKEN) ; +0x140  beqz s6,+0x5c (TAKEN: a1 = 0)
  k_step_r (wp_s_branch cpu _ (KA.«namex» + 0x106#64) true 58#13 15#5 0#5 (by decide) bop.BEQ)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [(show bcond bop.BEQ 0#64 0#64 = true by decide)]
  iintro Hk Hpc
  k_step_r (wp_s_branch cpu _ (KA.«namex» + 0x140#64) false 7964#13 22#5 0#5 (by decide) bop.BEQ)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [b22, ha1, (show bcond bop.BEQ 0#64 0#64 = true by decide)]
  iintro Hk Hpc
  -- +0x5c  c.mv a0,s4 ; the epilogue
  k_step_r (wp_s_add cpu _ (KA.«namex» + 0x5c#64) true 10#5 0#5 20#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  iapply (wp_epilogue_namex cpu (k.withSpie spie spp) (KA.«namex» + 0x5e#64) hK12 _ ?hr2
      (k.regs 1#5) (k.regs 8#5) (k.regs 9#5) (k.regs 18#5) (k.regs 19#5) (k.regs 20#5)
      (k.regs 21#5) (k.regs 22#5) (k.regs 23#5) (k.regs 24#5) (k.regs 25#5) (k.regs 26#5))
  rotate_left
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %cpu %hpin
  try simp only [k_norm_simps] at hpin
  ihave Hnext := wpNext_shift _ _ _ _ _ hpin $$ Hnext
  clear hpin
  iintro Hk Hpc
  k_norm_g
  ihave HΦ := wpNext_at k.sie k.proc cpu cpu _ (fun _ => rfl) $$ Hnext
  ihave HΦ := hΦ cpu $$ HΦ
  unfold namexRootPost
  iapply HΦ $$ %spie %spp %_ %(ientry kk) %hsp Hk Hpc [] Hpath
  · ipureintro
    refine ⟨?_, by simp [RegMap.set_apply, ha0]⟩
    unfold calleeSaved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] <;>
      first | rfl | (rw [b27]; try simp [RegMap.set_apply])
  · iexact Hheld
  case hr2 => simp [RegMap.set_apply, b2]

set_option maxHeartbeats 16000000 in
/-- **THE ROOT CORNER meets its specification** (Rocq's
`NamexRootProof.wp_namex_root`), at any interrupt state and depth. -/
theorem namex_root_main (IG : IGET) (cpu : CPU) (k : KCtx) (dqp : DFrac)
    (hK : namexRootSlots ≤ k.avail) (hnoff : k.noff + 3 < 2 ^ 31)
    (hroot : icfgDev = BitVec.ofNat 32 ROOTDEV) (hnib0 : 0 < icfgNib)
    (ha1 : k.regs 11#5 = 0#64)
    (hit : "itable" ∉ k.locks) (hpr : "pr" ∉ k.locks) (huart : "uart1" ∉ k.locks) :
    wp_namex_root_body (hlc := hlc) (GF := GF) cpu k dqp hK hnoff hroot hnib0 ha1 hit hpr huart := by
  unfold wp_namex_root_body
  have hK12 := namex_root_12 _ hK
  have hdev : (1#64 : BitVec 64) = BitVec.signExtend 64 icfgDev := by rw [hroot]; decide
  iintro ⟨Hk, Hpc, #Hit2, #Hiti, #Hreg, #Hpe, Hslot, Hpath, Hnext⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  simp only [namexAddr]
  -- +0x00 .. +0x1a  the prologue
  iapply (wp_prologue_namex cpu k KA.«namex» hK12)
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %cpu %hpin
  try simp only [k_norm_simps] at hpin
  ihave Hnext := wpNext_shift _ _ _ _ _ hpin $$ Hnext
  clear hpin
  iintro Hk Hpc Hframe
  k_norm_g
  -- +0x1c .. +0x20  the moves
  k_step_r (wp_s_add cpu _ (KA.«namex» + 0x1c#64) true 9#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_add cpu _ (KA.«namex» + 0x1e#64) true 22#5 0#5 11#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_add cpu _ (KA.«namex» + 0x20#64) true 21#5 0#5 12#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  -- +0x22  lbu a4,0(a0) : '/'
  icases byteBuf_acc (k.regs 10#5) dqp [SLASH, 0#8] 0 SLASH rfl $$ Hpath with ⟨Hb, Hbk⟩
  isimp only [BitVec.reduceOfNat, BitVec.add_zero] at Hb Hbk
  k_step_r (wp_s_lbu cpu _ (KA.«namex» + 0x22#64) false 0#12 14#5 10#5 (by decide) (by decide) dqp
      SLASH)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc Hb
  ihave Hpath := Hbk $$ Hb
  -- +0x26  li a5,47 ; +0x2a  beq a4,a5,+0x48 (TAKEN)
  k_step_r (wp_s_addi cpu _ (KA.«namex» + 0x26#64) false 47#12 15#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_branch cpu _ (KA.«namex» + 0x2a#64) false 30#13 14#5 15#5 (by decide) bop.BEQ)
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
    with [namex_slash_ofNat, (show bcond bop.BEQ 47#64 47#64 = true by decide)]
  iintro Hk Hpc
  -- +0x48  c.li a1,1 ; +0x4a  c.mv a0,a1 ; +0x4c  jal iget
  k_step_r (wp_s_addi cpu _ (KA.«namex» + 0x48#64) true 1#12 11#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_add cpu _ (KA.«namex» + 0x4a#64) true 10#5 0#5 11#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc]
  iintro Hk Hpc
  k_step_r (wp_s_jal cpu _ (KA.«namex» + 0x4c#64) false 2094466#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [namex_br_iget]
  iintro Hk Hpc
  ihave Hlic : iname fscIreg fscFs icfgIst (BitVec.ofNat 32 ROOTINO) .rootL $$ []
  · unfold iname; ipureintro; rfl
  iapply (namex_iget_call IG cpu _ (BitVec.ofNat 32 ROOTINO) .rootL ?gK ?gn
      (by unfold ROOTINO; simp; omega) (by unfold ROOTINO; simp) ?ga0 ?ga1 ?git ?gpr ?guart)
    $$ [- $Hk $Hpc $Hslot]
  rotate_right 1
  k_norm_g
  iframe Hlic
  iframe #
  case gK => k_norm_g; exact namex_root_slots _ hK
  case gn => k_norm_g; exact hnoff
  case ga0 => k_norm_g; exact hdev
  case ga1 => k_norm_g; unfold ROOTINO; decide
  case git => k_norm_g; exact hit
  case gpr => k_norm_g; exact hpr
  case guart => k_norm_g; exact huart
  iapply wpNext_intro_pin
  iintro %cpu %hpin
  try simp only [k_norm_simps] at hpin
  ihave Hnext := wpNext_shift _ _ _ _ _ hpin $$ Hnext
  clear hpin
  iintro %spie %spp %R2 %hsp Hk Hpc %hcs %kk %q %⟨hkk, ha0⟩ Href -
  k_norm_g [namex_ret_50]
  ihave Hk := kctx_eq_mono cpu _ (((k.withSpie spie spp).pushed 12).withRegs R2)
    (namex_root_ctx k spie spp R2) $$ Hk
  try simp only [k_norm_simps] at hsp
  unfold calleeSaved at hcs
  k_norm_g at hcs
  obtain ⟨b2, b8, b9, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27⟩ := hcs
  ihave Hheld := namex_rootc_held kk q hkk hnib0 $$ Href
  iapply (namex_root_after cpu k dqp spie spp R2 kk hK12 ha1 b2 b9 b22 b27 ha0 hsp _ ?hΦ)
    $$ [$Hk $Hpc $Hframe $Hpath $Hheld $Hnext]
  case hΦ => intro c; exact .rfl

end

end Xv6
