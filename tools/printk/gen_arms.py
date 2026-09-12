# Generate the per-directive arm lemmas of printk.
HDR = '''set_option maxHeartbeats 4000000 in
/-- {DOC} -/
theorem printk_arm_{NAME} {IFACE} {{hlc : HasLC}} {{GF : BundledGFunctors}} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γpr γl : GName) (γd : UartNames) (bs : List (BitVec 8)) (dqf : DFrac)
    (f : List (BitVec 8)) (descs : List PkArgDesc)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 48 ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (huart : "uart" ∉ k.locks) (hf : stackFacts (k.regs 2#5) 24) (hflen : f.length + 4 < 2 ^ 31)
    (i kk : Nat) (R : RegMap) (w18 : BitVec 64) (hR : pkRegs k.regs R) (hR20 : R 20#5 = BitVec.ofNat 64 i)
    {HYPS} :
    printkText ∗ kernelText ∗ kernelData ∗ isTxLock γl γd ∗
    kctx cpu ((pkBase k).withRegs R) ∗ clockCells cpu ∗ pcIs cpu {PC0} ∗
    byteBuf (k.regs 10#5) dqf (f ++ [0#8]) ∗ pkDescs k.regs descs ∗
    pkFrame (k.regs 2#5) k.regs (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 kk) w18 ∗
    uartSentSub γd bs ∗ locked γpr cpu ∗ pkNext cpu k γpr γd bs dqf f descs i
    ⊢ wpLoop (GF := GF) cpu := by
  unfold pkNext
  iintro ⟨#HT, #Htext, #HD, #Htx, Hk, Hclock, Hpc, Hbuf, Hdescs, Hframe, Hsent, Hlocked, Hnext⟩
  have hR8 : R 8#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFC0#64 := hR.1.2.1
  have hR19 : R 19#5 = 37#64 := hR.1.2.2.2.1
  have hR22 : R 22#5 = 10#64 := hR.1.2.2.2.2.1
  have huart' : "uart" ∉ "pr" :: k.locks := by
    intro h; rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact huart h
'''

def hx(a): return f"0x{a + 0x80000000:08x}#64"

def instr_facts(pcs):
    return "".join(f"  ihave #Hi_{pc:x} := instr_printk_{pc:x} $$ HT\n" for pc in pcs)

def step_ld_ap(pc):
    return f'''  -- ld a5,-120(s0)
  icases pkFrame_ap_acc _ _ _ _ $$ Hframe with ⟨Hap, Hfr⟩
  k_step (wp_s_ld cpu _ ?hs ?ht {hx(pc)} false 3976#12 15#5 8#5 (by decide) (DFrac.own 1)
    (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 kk)) $$ [- $Hk $Hclock $Hpc] with [hR8]
  iintro Hk Hclock Hpc Hap
'''
def step_addi_a4(pc):
    return f'''  -- addi a4,a5,8
  k_step (wp_s_addi cpu _ ?hs ?ht {hx(pc)} false 8#12 14#5 15#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc
'''
def step_sd_ap(pc):
    return f'''  -- sd a4,-120(s0)
  k_step (wp_s_sd cpu _ ?hs ?ht {hx(pc)} false 3976#12 8#5 14#5 (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 kk)
   ) $$ [- $Hk $Hclock $Hpc] with [hR8, ap_next']
  iintro Hk Hclock Hpc Hap
  ihave Hframe := Hfr $$ %_ Hap
'''
def step_li(pc, rd, imm, rvc):
    return f'''  -- li x{rd},{imm}
  k_step (wp_s_addi cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {imm}#12 {rd}#5 0#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc
'''
def step_mv(pc, rd, rs, rvc, extra=""):
    return f'''  -- mv x{rd},x{rs}
  k_step (wp_s_add cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {rd}#5 0#5 {rs}#5 (by decide)) $$ [- $Hk $Hclock $Hpc]{extra}
  iintro Hk Hclock Hpc
'''
def step_load_va(pc, kind):
    if kind == "ld":
        return f'''  -- ld a0,0(a5)
  icases pkFrame_va_acc _ _ _ _ kk hk7 $$ Hframe with ⟨Hva, Hfr⟩
  k_step (wp_s_ld cpu _ ?hs ?ht {hx(pc)} true 0#12 10#5 15#5 (by decide) (DFrac.own 1)
    (k.regs (BitVec.ofNat 5 (11 + kk)))) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc Hva
  ihave Hframe := Hfr $$ Hva
'''
    rule = "wp_s_lw" if kind == "lw" else "wp_s_lwu"
    rvc = "true" if kind == "lw" else "false"
    return f'''  -- {kind} a0,0(a5)
  icases pkFrame_va_acc _ _ _ _ kk hk7 $$ Hframe with ⟨Hva, Hfr⟩
  icases cell8_lo_acc _ _ _ $$ Hva with ⟨Hlo, Hvc⟩
  k_step ({rule} cpu _ ?hs ?ht {hx(pc)} {rvc} 0#12 10#5 15#5 (by decide) (DFrac.own 1)
    (BitVec.extractLsb' 0 32 (k.regs (BitVec.ofNat 5 (11 + kk))))) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc Hlo
  ihave Hva := Hvc $$ Hlo
  ihave Hframe := Hfr $$ Hva
'''
def step_printint(pc, imm, base):
    hb = {"mv": "exact Or.inl hR22", "10": "exact Or.inl rfl", "16": "exact Or.inr rfl"}[base]
    return f'''  -- jal printint
  iapply (printk_printint PI cpu (pkBase k) _ γl γd bs ?hs ?ht ?hK ?hb ?hn ?hu {hx(pc)} {imm}#21 (by decide) (by decide))
    $$ [- $Hk $Hclock $Hpc $Hsent]
  rotate_right 1
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hK => k_norm; omega
  case hb => k_norm; first | exact Or.inl hR22 | exact Or.inl trivial | exact Or.inr trivial
  case hn => k_norm; omega
  case hu => k_norm; exact huart'
  iintro %R2 %cs Hk Hclock Hpc %hcs Hsent
  unfold calleeSaved at hcs
  k_norm at hcs
  k_norm
'''
def step_consputc(pc, imm, n, prev):
    # n: index of the result map (R2, R3); prev: name of previous cs list
    return f'''  -- jal consputc
  iapply (printk_consputc CP cpu (pkBase k) _ γl γd _ ?hs ?ht ?hK ?hn ?hu {hx(pc)} {imm}#21 (by decide) (by decide))
    $$ [- $Hk $Hclock $Hpc $Hsent]
  rotate_right 1
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hK => k_norm; omega
  case hn => k_norm; omega
  case hu => k_norm; exact huart'
  iintro %R{n} %cs{n} Hk Hclock Hpc %hcs{n} Hsent
  unfold calleeSaved at hcs{n}
  k_norm at hcs{n}
  k_norm
'''
def step_addiw(pc, adv):
    lem = {2: "addiw_succ2", 3: "addiw_succ3"}[adv]
    return f'''  -- addiw s1,s4,{adv}
  have h20 : R2 20#5 = BitVec.ofNat 64 i := hcs.2.2.2.2.2.1.trans hR20
  k_step (wp_s_addiw cpu _ ?hs ?ht {hx(pc)} false {adv}#12 9#5 20#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
    with [h20, {lem} i (by omega)]
  iintro Hk Hclock Hpc
'''
def step_j(pc, imm, rvc):
    return f'''  -- j 0x56e
  k_step (wp_s_j cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {imm}#21 ?htgt) $$ [- $Hk $Hclock $Hpc]
  case htgt => k_tgt
  iintro Hk Hclock Hpc
'''

NUM_ARMS = [
 # name, pc0, adv, li_a2 (None|(pc,imm,rvc)), a1 ((pc,kind) kind: mv|10|16), load (pc,kind), jal (pc,imm), addiw pc, j (pc,imm,rvc)
 ("d",   0x5ca, 1, (0x5d6,1,True),  (0x5d8,"mv"), (0x5da,"lw"),  (0x5dc,2096784), None,  (0x5e0,2097038,True)),
 ("ld",  0x5ae, 2, (0x5ba,1,True),  (0x5bc,"mv"), (0x5be,"ld"),  (0x5c0,2096812), 0x5c4, (0x5c8,2097062,True)),
 ("lld", 0x5ec, 3, (0x5f8,1,True),  (0x5fa,"10"), (0x5fc,"ld"),  (0x5fe,2096750), 0x602, (0x606,2097000,True)),
 ("u",   0x608, 1, (0x614,0,True),  (0x616,"mv"), (0x618,"lwu"), (0x61c,2096720), None,  (0x620,2096974,True)),
 ("lu",  0x622, 2, (0x62e,0,True),  (0x630,"mv"), (0x632,"ld"),  (0x634,2096696), 0x638, (0x63c,2096946,True)),
 ("llu", 0x63e, 3, (0x64a,0,True),  (0x64c,"10"), (0x64e,"ld"),  (0x650,2096668), 0x654, (0x658,2096918,True)),
 ("x",   0x65a, 1, (0x666,0,True),  (0x668,"16"), (0x66a,"lwu"), (0x66e,2096638), None,  (0x672,2096892,True)),
 ("lx",  0x674, 2, None,            (0x680,"16"), (0x682,"ld"),  (0x684,2096616), 0x688, (0x68c,2096866,True)),
 ("llx", 0x68e, 3, (0x69a,0,True),  (0x69c,"16"), (0x69e,"ld"),  (0x6a0,2096588), 0x6a4, (0x6a8,2096838,True)),
]

EXTRA = r"""
set_option maxHeartbeats 4000000 in
/-- One turn of the `%p` digit loop at `0x800006d6`, count `n + 1`. -/
theorem printk_hex_iter (CP : CONSPUTC) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γd : UartNames)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 48 ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (huart : "uart" ∉ k.locks) (n : Nat) (R : RegMap) (bs : List (BitVec 8))
    (hR : pkRegsN k.regs R) (hR25 : R 25#5 = 0x80007730#64) (hR20 : R 20#5 = BitVec.ofNat 64 (n + 1))
    (hn : n + 1 ≤ 16) (tgt : BitVec 64) (htgt : tgt = if n = 0 then 0x800006ec#64 else 0x800006d6#64) :
    printkText ∗ kernelText ∗ kernelData ∗ isTxLock γl γd ∗
    kctx cpu ((pkBase k).withRegs R) ∗ clockCells cpu ∗ pcIs cpu 0x800006d6#64 ∗ uartSentSub γd bs ∗
    (∀ (R' : RegMap) (cs : List (BitVec 8)), kctx cpu ((pkBase k).withRegs R') -∗ clockCells cpu -∗
      pcIs cpu tgt -∗ uartSentSub γd (bs ++ cs) -∗
      ⌜pkRegsN k.regs R' ∧ R' 9#5 = R 9#5 ∧ R' 25#5 = R 25#5 ∧ R' 20#5 = BitVec.ofNat 64 n⌝ -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  subst htgt
  iintro ⟨#HT, #Htext, #HD, #Htx, Hk, Hclock, Hpc, Hsent, HΦ⟩
  have huart' : "uart" ∉ "pr" :: k.locks := by
    intro h; rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact huart h
  have h16 : (R 21#5 >>> 60).toNat < digitsStr.length := by
    have := shr60_lt (R 21#5)
    simp only [digitsStr, List.length_cons, List.length_nil]; omega
  have hdig : digitsStr[(R 21#5 >>> 60).toNat]? = some (digitsStr[(R 21#5 >>> 60).toNat]'h16) :=
    List.getElem?_eq_getElem h16
  ihave #Hi_6d6 := instr_printk_6d6 $$ HT
  ihave #Hi_6da := instr_printk_6da $$ HT
  ihave #Hi_6dc := instr_printk_6dc $$ HT
  ihave #Hi_6e0 := instr_printk_6e0 $$ HT
  ihave #Hi_6e4 := instr_printk_6e4 $$ HT
  ihave #Hi_6e6 := instr_printk_6e6 $$ HT
  ihave #Hi_6e8 := instr_printk_6e8 $$ HT
  -- srli a5,s5,60
  k_step (wp_s_srli cpu _ ?hs ?ht 0x800006d6#64 false 60#6 15#5 21#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc
  -- add a5,s9,a5
  k_step (wp_s_add cpu _ ?hs ?ht 0x800006da#64 true 15#5 15#5 25#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
    with [hR25, BitVec.add_comm (R 21#5 >>> 60) 0x80007730#64]
  iintro Hk Hclock Hpc
  -- lbu a0,0(a5)
  ihave Hdig := kernelData_digits $$ HD
  icases byteBuf_acc _ _ _ _ _ hdig $$ Hdig with ⟨Hb, _⟩
  ihave Hb := (show bytesPointsTo (0x80007730#64 + BitVec.ofNat 64 (R 21#5 >>> 60).toNat) 1 DFrac.discard
      (digitsStr[(R 21#5 >>> 60).toNat]'h16) ⊢
      bytesPointsTo (GF := GF) (0x80007730#64 + R 21#5 >>> 60) 1 DFrac.discard (digitsStr[(R 21#5 >>> 60).toNat]'h16)
      from by rw [← shr60_ofNat]) $$ Hb
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x800006dc#64 false 0#12 10#5 15#5 (by decide) DFrac.discard
    (digitsStr[(R 21#5 >>> 60).toNat]'h16) ?hram) $$ [- $Hk $Hclock $Hpc]
  case hram => k_norm; rw [shr60_ofNat]; exact inRam_byte inRam_digits _ (shr60_lt _)
  iintro Hk Hclock Hpc _
  -- jal consputc
  iapply (printk_consputc CP cpu (pkBase k) _ γl γd _ ?hs ?ht ?hK ?hn ?hu 0x800006e0#64 2096042#21 (by decide) (by decide))
    $$ [- $Hk $Hclock $Hpc $Hsent]
  rotate_right 1
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hK => k_norm; omega
  case hn => k_norm; omega
  case hu => k_norm; exact huart'
  iintro %R2 %cs2 Hk Hclock Hpc %hcs2 Hsent
  unfold calleeSaved at hcs2
  k_norm at hcs2
  k_norm
  have h20 : R2 20#5 = BitVec.ofNat 64 (n + 1) := hcs2.2.2.2.2.2.1.trans hR20
  -- slli s5,s5,4
  k_step (wp_s_slli cpu _ ?hs ?ht 0x800006e4#64 true 4#6 21#5 21#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc
  -- addiw s4,s4,-1
  k_step (wp_s_addiw cpu _ ?hs ?ht 0x800006e6#64 true 4095#12 20#5 20#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
    with [h20, addiw_pred (n + 1) (by omega) (by omega), Nat.add_sub_cancel]
  iintro Hk Hclock Hpc
  -- bnez s4 → 0x6d6
  k_step (wp_s_branch cpu _ ?hs ?ht 0x800006e8#64 false 8174#13 20#5 0#5 (by decide) bop.BNE ?htgt)
    $$ [- $Hk $Hclock $Hpc] with [bcond_bne_ofNat n (by omega), ite_decide_ne]
  case htgt => k_tgt
  iintro Hk Hclock Hpc
  iapply HΦ $$ %_ %cs2 Hk Hclock Hpc Hsent
  ipureintro
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pkRegsN_set _ _ 20#5 _ (pkRegsN_set _ _ 21#5 _ (pkRegsN_calleeSaved _ _ _ hR hcs2) (by decide)) (by decide)
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; exact hcs2.2.2.1
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; exact hcs2.2.2.2.2.2.2.2.2.2.1
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_true]

set_option maxHeartbeats 4000000 in
/-- The `%p` digit loop: from count `m + 1` down to the exit at `0x800006ec`. -/
theorem printk_hex_loop (CP : CONSPUTC) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γd : UartNames)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 48 ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (huart : "uart" ∉ k.locks) (m : Nat) :
    ∀ (R : RegMap) (bs : List (BitVec 8)), pkRegsN k.regs R → R 25#5 = 0x80007730#64 →
    R 20#5 = BitVec.ofNat 64 (m + 1) → m + 1 ≤ 16 →
    printkText ∗ kernelText ∗ kernelData ∗ isTxLock γl γd ∗
    kctx cpu ((pkBase k).withRegs R) ∗ clockCells cpu ∗ pcIs cpu 0x800006d6#64 ∗ uartSentSub γd bs ∗
    (∀ (R' : RegMap) (cs : List (BitVec 8)), kctx cpu ((pkBase k).withRegs R') -∗ clockCells cpu -∗
      pcIs cpu 0x800006ec#64 -∗ uartSentSub γd (bs ++ cs) -∗
      ⌜pkRegsN k.regs R' ∧ R' 9#5 = R 9#5 ∧ R' 25#5 = R 25#5⌝ -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  induction m with
  | zero =>
    intro R bs hR hR25 hR20 hm
    iintro ⟨#HT, #Htext, #HD, #Htx, Hk, Hclock, Hpc, Hsent, HΦ⟩
    iapply (printk_hex_iter CP cpu k γl γd hsie htier hK hnoff huart 0 R bs hR hR25 hR20 hm 0x800006ec#64 (by simp))
      $$ [- $Hk $Hclock $Hpc $Hsent]
    iframe #
    iintro %R' %cs Hk Hclock Hpc Hsent %h
    iapply HΦ $$ %_ %cs Hk Hclock Hpc Hsent
    ipureintro
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  | succ m ih =>
    intro R bs hR hR25 hR20 hm
    iintro ⟨#HT, #Htext, #HD, #Htx, Hk, Hclock, Hpc, Hsent, HΦ⟩
    iapply (printk_hex_iter CP cpu k γl γd hsie htier hK hnoff huart (m + 1) R bs hR hR25 hR20 hm 0x800006d6#64
      (by simp)) $$ [- $Hk $Hclock $Hpc $Hsent]
    iframe #
    iintro %R' %cs Hk Hclock Hpc Hsent %h
    iapply (ih R' (bs ++ cs) h.1 (h.2.2.1.trans hR25) h.2.2.2 (by omega)) $$ [- $Hk $Hclock $Hpc $Hsent]
    iframe #
    iintro %R'' %cs' Hk Hclock Hpc Hsent %h'
    ihave Hsent := (show uartSentSub γd (bs ++ cs ++ cs') ⊢ uartSentSub γd (bs ++ (cs ++ cs')) from
      by rw [List.append_assoc]) $$ Hsent
    iapply HΦ $$ %_ %(cs ++ cs') Hk Hclock Hpc Hsent
    ipureintro
    exact ⟨h'.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2.1⟩

set_option maxHeartbeats 4000000 in
/-- The `%s` character loop at `0x80000720`: `s4 = v + j`, `a0 = s[j]`
(non-NUL), `n` more characters after `j`; ends at `0x8000056e`. -/
theorem printk_str_loop (CP : CONSPUTC) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γd : UartNames)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 48 ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (huart : "uart" ∉ k.locks) (v : BitVec 64) (dq : DFrac) (s : List (BitVec 8)) (hs : nonul s)
    (hram : inRam v (s.length + 1)) (n : Nat) :
    ∀ (j : Nat) (R : RegMap) (bs : List (BitVec 8)), j + n + 1 = s.length → pkRegs k.regs R →
    R 20#5 = v + BitVec.ofNat 64 j → R 10#5 = BitVec.setWidth 64 (fmtByte s j) →
    printkText ∗ kernelText ∗ isTxLock γl γd ∗
    kctx cpu ((pkBase k).withRegs R) ∗ clockCells cpu ∗ pcIs cpu 0x80000720#64 ∗ byteBuf v dq (s ++ [0#8]) ∗
    uartSentSub γd bs ∗
    (∀ (R' : RegMap) (cs : List (BitVec 8)), kctx cpu ((pkBase k).withRegs R') -∗ clockCells cpu -∗
      pcIs cpu 0x8000056e#64 -∗ byteBuf v dq (s ++ [0#8]) -∗ uartSentSub γd (bs ++ cs) -∗
      ⌜pkRegs k.regs R' ∧ R' 9#5 = R 9#5⌝ -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  induction n with
  | zero =>
    intro j R bs hj hR hR20 hR10
    iintro ⟨#HT, #Htext, #Htx, Hk, Hclock, Hpc, Hbuf, Hsent, HΦ⟩
    have huart' : "uart" ∉ "pr" :: k.locks := by
      intro h; rcases List.mem_cons.mp h with h | h
      · exact absurd h (by decide)
      · exact huart h
    ihave #Hi_720 := instr_printk_720 $$ HT
    ihave #Hi_724 := instr_printk_724 $$ HT
    ihave #Hi_726 := instr_printk_726 $$ HT
    ihave #Hi_72a := instr_printk_72a $$ HT
    ihave #Hi_72c := instr_printk_72c $$ HT
    -- jal consputc
    iapply (printk_consputc CP cpu (pkBase k) _ γl γd _ ?hs ?ht ?hK ?hn ?hu 0x80000720#64 2095978#21 (by decide)
      (by decide)) $$ [- $Hk $Hclock $Hpc $Hsent]
    rotate_right 1
    iframe #
    case hs => k_norm
    case ht => k_norm
    case hK => k_norm; omega
    case hn => k_norm; omega
    case hu => k_norm; exact huart'
    iintro %R2 %cs2 Hk Hclock Hpc %hcs2 Hsent
    unfold calleeSaved at hcs2
    k_norm at hcs2
    k_norm
    have h20 : R2 20#5 = v + BitVec.ofNat 64 j := hcs2.2.2.2.2.2.1.trans hR20
    -- addi s4,s4,1
    k_step (wp_s_addi cpu _ ?hs ?ht 0x80000724#64 true 1#12 20#5 20#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
      with [h20, ofNat_succ']
    iintro Hk Hclock Hpc
    -- lbu a0,0(s4): the terminator
    have hb : (s ++ [0#8])[j + 1]? = some (fmtByte s (j + 1)) := fmtByte_get s (j + 1) (by omega)
    have hz : fmtByte s (j + 1) = 0#8 := by rw [show j + 1 = s.length by omega]; exact fmtByte_end s
    icases byteBuf_acc v dq (s ++ [0#8]) (j + 1) _ hb $$ Hbuf with ⟨Hb, Hclose⟩
    k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000726#64 false 0#12 10#5 20#5 (by decide) dq (fmtByte s (j + 1)) ?hram)
      $$ [- $Hk $Hclock $Hpc]
    case hram => k_norm; exact inRam_byte hram (j + 1) (by omega)
    iintro Hk Hclock Hpc Hb
    ihave Hbuf := Hclose $$ Hb
    -- bnez a0 → 0x720: not taken
    k_step (wp_s_branch cpu _ ?hs ?ht 0x8000072a#64 true 8182#13 10#5 0#5 (by decide) bop.BNE ?htgt)
      $$ [- $Hk $Hclock $Hpc] with [ite_bne_byte, if_pos hz]
    case htgt => k_tgt
    iintro Hk Hclock Hpc
    -- j 0x56e
    k_step (wp_s_j cpu _ ?hs ?ht 0x8000072c#64 true 2096706#21 ?htgt) $$ [- $Hk $Hclock $Hpc]
    case htgt => k_tgt
    iintro Hk Hclock Hpc
    iapply HΦ $$ %_ %cs2 Hk Hclock Hpc Hbuf Hsent
    ipureintro
    refine ⟨?_, ?_⟩
    · exact pkRegs_set _ _ 10#5 _ (pkRegs_set _ _ 20#5 _ (pkRegs_calleeSaved _ _ _ hR hcs2) (by decide)) (by decide)
    · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]; exact hcs2.2.2.1
  | succ n ih =>
    intro j R bs hj hR hR20 hR10
    iintro ⟨#HT, #Htext, #Htx, Hk, Hclock, Hpc, Hbuf, Hsent, HΦ⟩
    have huart' : "uart" ∉ "pr" :: k.locks := by
      intro h; rcases List.mem_cons.mp h with h | h
      · exact absurd h (by decide)
      · exact huart h
    ihave #Hi_720 := instr_printk_720 $$ HT
    ihave #Hi_724 := instr_printk_724 $$ HT
    ihave #Hi_726 := instr_printk_726 $$ HT
    ihave #Hi_72a := instr_printk_72a $$ HT
    -- jal consputc
    iapply (printk_consputc CP cpu (pkBase k) _ γl γd _ ?hs ?ht ?hK ?hn ?hu 0x80000720#64 2095978#21 (by decide)
      (by decide)) $$ [- $Hk $Hclock $Hpc $Hsent]
    rotate_right 1
    iframe #
    case hs => k_norm
    case ht => k_norm
    case hK => k_norm; omega
    case hn => k_norm; omega
    case hu => k_norm; exact huart'
    iintro %R2 %cs2 Hk Hclock Hpc %hcs2 Hsent
    unfold calleeSaved at hcs2
    k_norm at hcs2
    k_norm
    have h20 : R2 20#5 = v + BitVec.ofNat 64 j := hcs2.2.2.2.2.2.1.trans hR20
    -- addi s4,s4,1
    k_step (wp_s_addi cpu _ ?hs ?ht 0x80000724#64 true 1#12 20#5 20#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
      with [h20, ofNat_succ']
    iintro Hk Hclock Hpc
    -- lbu a0,0(s4): the next character
    have hb : (s ++ [0#8])[j + 1]? = some (fmtByte s (j + 1)) := fmtByte_get s (j + 1) (by omega)
    have hnz : fmtByte s (j + 1) ≠ 0#8 := fmtByte_ne_zero s hs (j + 1) (by omega)
    icases byteBuf_acc v dq (s ++ [0#8]) (j + 1) _ hb $$ Hbuf with ⟨Hb, Hclose⟩
    k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000726#64 false 0#12 10#5 20#5 (by decide) dq (fmtByte s (j + 1)) ?hram)
      $$ [- $Hk $Hclock $Hpc]
    case hram => k_norm; exact inRam_byte hram (j + 1) (by omega)
    iintro Hk Hclock Hpc Hb
    ihave Hbuf := Hclose $$ Hb
    -- bnez a0 → 0x720: taken
    k_step (wp_s_branch cpu _ ?hs ?ht 0x8000072a#64 true 8182#13 10#5 0#5 (by decide) bop.BNE ?htgt)
      $$ [- $Hk $Hclock $Hpc] with [ite_bne_byte, if_neg hnz]
    case htgt => k_tgt
    iintro Hk Hclock Hpc
    iapply (ih (j + 1) _ (bs ++ cs2) (by omega)
      (pkRegs_set _ _ 10#5 _ (pkRegs_set _ _ 20#5 _ (pkRegs_calleeSaved _ _ _ hR hcs2) (by decide)) (by decide))
      (by simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true])
      (by simp only [RegMap.set_apply, BitVec.reduceEq, ite_true])) $$ [- $Hk $Hclock $Hpc $Hbuf $Hsent]
    iframe #
    iintro %R' %cs' Hk Hclock Hpc Hbuf Hsent %h'
    ihave Hsent := (show uartSentSub γd (bs ++ cs2 ++ cs') ⊢ uartSentSub γd (bs ++ (cs2 ++ cs')) from
      by rw [List.append_assoc]) $$ Hsent
    iapply HΦ $$ %_ %(cs2 ++ cs') Hk Hclock Hpc Hbuf Hsent
    ipureintro
    refine ⟨h'.1, ?_⟩
    rw [h'.2]
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false]
    exact hcs2.2.2.1

"""
out = []
for (name, pc0, adv, li_a2, a1, load, jal, addiw, j) in NUM_ARMS:
    pcs = [pc0, pc0+4, pc0+8] + ([li_a2[0]] if li_a2 else []) + [a1[0], load[0], jal[0]] + ([addiw] if addiw else []) + [j[0]]
    hyps = f'''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1))
    (hp : i + {adv} < f.length) (hkk : kk < descs.length) (hdlen : descs.length ≤ 7)
    (hkinds : pkKinds (f.drop (i + {adv} + 1)) = (descs.drop (kk + 1)).map PkArgDesc.kind)'''
    doc = f"The `%{name}` arm at `{hx(pc0)}`: the next vararg to `printint`."
    t = HDR.format(DOC=doc, NAME=name, IFACE="(PI : PRINTINT)", HYPS=hyps, PC0=hx(pc0))
    t += '''  have hk7 : kk < 7 := by omega
'''
    t += instr_facts(pcs)
    t += step_ld_ap(pc0) + step_addi_a4(pc0+4) + step_sd_ap(pc0+8)
    if li_a2: t += step_li(li_a2[0], 12, li_a2[1], li_a2[2])
    if a1[1] == "mv": t += step_mv(a1[0], 11, 22, True)
    else: t += step_li(a1[0], 11, int(a1[1]), True)
    t += step_load_va(load[0], load[1])
    t += step_printint(jal[0], jal[1], a1[1])
    if addiw: t += step_addiw(addiw, adv)
    t += step_j(j[0], j[1], j[2])
    t += f'''  iapply Hnext $$ %_ %(i + {adv}) %(kk + 1) %cs %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
  ipureintro
  refine ⟨?_, ?_, by omega, hp, hkinds⟩
'''
    if addiw:
        t += '''  · exact pkRegs_set _ _ 9#5 _ (pkRegs_calleeSaved _ _ _ hR hcs) (by decide)
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_true]

'''
    else:
        t += '''  · exact pkRegs_calleeSaved _ _ _ hR hcs
  · exact hcs.2.2.1.trans hR9

'''
    out.append(t)

# %c arm
t = HDR.format(DOC="The `%c` arm at `0x800006f0`: the next vararg to `consputc`.", NAME="c", IFACE="(CP : CONSPUTC)",
  HYPS='''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1))
    (hp : i + 1 < f.length) (hkk : kk < descs.length) (hdlen : descs.length ≤ 7)
    (hkinds : pkKinds (f.drop (i + 1 + 1)) = (descs.drop (kk + 1)).map PkArgDesc.kind)''', PC0=hx(0x6f0))
t += '''  have hk7 : kk < 7 := by omega
'''
t += instr_facts([0x6f0, 0x6f4, 0x6f8, 0x6fc, 0x6fe, 0x702])
t += step_ld_ap(0x6f0) + step_addi_a4(0x6f4) + step_sd_ap(0x6f8) + step_load_va(0x6fc, "lw")
t += step_consputc(0x6fe, 2096012, 2, None)
t += step_j(0x702, 2096748, True)
t += '''  iapply Hnext $$ %_ %(i + 1) %(kk + 1) %cs2 %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
  ipureintro
  refine ⟨?_, ?_, by omega, hp, hkinds⟩
  · exact pkRegs_calleeSaved _ _ _ hR hcs2
  · exact hcs2.2.2.1.trans hR9

'''
out.append(t)

# %% arm at 0x73c: mv a0,s5 ; jal consputc ; j 0x56e
t = HDR.format(DOC="The `%%` arm at `0x8000073c`: `consputc('%')`.", NAME="pct", IFACE="(CP : CONSPUTC)",
  HYPS='''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1))
    (hp : i + 1 < f.length)
    (hkinds : pkKinds (f.drop (i + 1 + 1)) = (descs.drop kk).map PkArgDesc.kind)''', PC0=hx(0x73c))
t += instr_facts([0x73c, 0x73e, 0x742])
t += step_mv(0x73c, 10, 21, True)
t += step_consputc(0x73e, 2095948, 2, None)
t += step_j(0x742, 2096684, True)
t += '''  iapply Hnext $$ %_ %(i + 1) %kk %cs2 %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
  ipureintro
  refine ⟨?_, ?_, by omega, hp, hkinds⟩
  · exact pkRegs_calleeSaved _ _ _ hR hcs2
  · exact hcs2.2.2.1.trans hR9

'''
out.append(t)

# default arm at 0x7f0: li a0,37 ; jal ; mv a0,s5 ; jal ; j
t = HDR.format(DOC="The default arm at `0x800007f0`: `consputc('%'); consputc(c)`.", NAME="default", IFACE="(CP : CONSPUTC)",
  HYPS='''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1))
    (hp : i + 1 < f.length)
    (hkinds : pkKinds (f.drop (i + 1 + 1)) = (descs.drop kk).map PkArgDesc.kind)''', PC0=hx(0x7f0))
t += instr_facts([0x7f0, 0x7f4, 0x7f8, 0x7fa, 0x7fe])
t += step_li(0x7f0, 10, 37, False)
t += step_consputc(0x7f4, 2095766, 2, None)
t += step_mv(0x7f8, 10, 21, True)
t += step_consputc(0x7fa, 2095760, 3, None)
t += step_j(0x7fe, 2096496, True)
t += '''  ihave Hsent := (show uartSentSub γd (bs ++ cs2 ++ cs3) ⊢ uartSentSub γd (bs ++ (cs2 ++ cs3)) from
    by rw [List.append_assoc]) $$ Hsent
  iapply Hnext $$ %_ %(i + 1) %kk %(cs2 ++ cs3) %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
  ipureintro
  refine ⟨?_, ?_, by omega, hp, hkinds⟩
  · exact pkRegs_calleeSaved _ _ _ (pkRegs_calleeSaved _ _ _ hR hcs2) hcs3
  · exact hcs3.2.2.1.trans (hcs2.2.2.1.trans hR9)

'''
out.append(t)

# plain arm at 0x57c: bne a0,s3 -> 0x568 ; jal consputc ; mv s1,s4 -> 0x56e
t = HDR.format(DOC="A plain character at `0x8000057c`: `consputc(c)`, then back at `0x56e` with `s1 = i`.", NAME="plain", IFACE="(CP : CONSPUTC)",
  HYPS='''(hR10 : R 10#5 = BitVec.setWidth 64 (fmtByte f i))
    (hi : i < f.length) (hne : fmtByte f i ≠ chPct)
    (hkinds : pkKinds (f.drop (i + 1)) = (descs.drop kk).map PkArgDesc.kind)''', PC0=hx(0x57c))
t += instr_facts([0x57c, 0x568, 0x56c])
t += '''  -- bne a0,s3 → 0x568
  k_step (wp_s_branch cpu _ ?hs ?ht 0x8000057c#64 false 8172#13 10#5 19#5 (by decide) bop.BNE ?htgt)
    $$ [- $Hk $Hclock $Hpc] with [hR10, hR19, ite_bne_zext_pct, if_neg hne]
  case htgt => k_tgt
  iintro Hk Hclock Hpc
'''
t += step_consputc(0x568, 2096418, 2, None)
t += '''  have h20 : R2 20#5 = BitVec.ofNat 64 i := hcs2.2.2.2.2.2.1.trans hR20
'''
t += step_mv(0x56c, 9, 20, True, extra=" with [h20]")
t += '''  iapply Hnext $$ %_ %i %kk %cs2 %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
  ipureintro
  refine ⟨?_, ?_, le_refl _, hi, hkinds⟩
  · exact pkRegs_set _ _ 9#5 _ (pkRegs_calleeSaved _ _ _ hR hcs2) (by decide)
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_true]

'''
out.append(t)

out.append(EXTRA)
import sys
open(sys.argv[1], 'w').write("".join(out))
