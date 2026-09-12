# The dispatch chain, %p, %s, the '%' turn, the walk and the entry.
def hx(a): return f"0x{a + 0x80000000:08x}#64"
def facts(pcs, ind="  "): return "".join(f"{ind}ihave #Hi_{pc:x} := instr_printk_{pc:x} $$ HT\n" for pc in pcs)
def br(pc, rvc, imm, rs1, rs2, op, lem, ind="  "):
    w = f" with [{lem}]" if lem else ""
    return (f"{ind}k_step (wp_s_branch cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {imm}#13 {rs1}#5 {rs2}#5 (by decide) bop.{op} ?htgt)\n"
            f"{ind}  $$ [- $Hk $Hclock $Hpc]{w}\n{ind}case htgt => k_tgt\n{ind}iintro Hk Hclock Hpc\n")
def li(pc, rd, imm, rvc, ind="  "):
    return (f"{ind}k_step (wp_s_addi cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {imm}#12 {rd}#5 0#5 (by decide)) $$ [- $Hk $Hclock $Hpc]\n"
            f"{ind}iintro Hk Hclock Hpc\n")
def addi(pc, rd, rs, imm, rvc, lem, ind="  "):
    w = f" with [{lem}]" if lem else ""
    return (f"{ind}k_step (wp_s_addi cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {imm}#12 {rd}#5 {rs}#5 (by decide)) $$ [- $Hk $Hclock $Hpc]{w}\n"
            f"{ind}iintro Hk Hclock Hpc\n")
def add(pc, rd, rs1, rs2, rvc, lem="", ind="  "):
    w = f" with [{lem}]" if lem else ""
    return (f"{ind}k_step (wp_s_add cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {rd}#5 {rs1}#5 {rs2}#5 (by decide)) $$ [- $Hk $Hclock $Hpc]{w}\n"
            f"{ind}iintro Hk Hclock Hpc\n")
def mv(pc, rd, rs, rvc, lem="", ind="  "): return add(pc, rd, 0, rs, rvc, lem, ind)
def sltiu(pc, rd, rs, lem, ind="  ", gen=None):
    t = (f"{ind}k_step (wp_s_sltiu cpu _ ?hs ?ht {hx(pc)} false 1#12 {rd}#5 {rs}#5 (by decide)) $$ [- $Hk $Hclock $Hpc] with [{lem}]\n"
            f"{ind}iintro Hk Hclock Hpc\n")
    if gen: t += (f"{ind}generalize hb{gen[0]}g : (if {gen[1]} then 1#64 else 0#64) = b{gen[0]}\n"
                  f"{ind}have hb{gen[0]} : b{gen[0]} = (if {gen[1]} then 1#64 else 0#64) := hb{gen[0]}g.symm\n")
    return t
def andbits(pc, rd, rs1, rs2, p, q, l1, l2, ind="  ", gen=None):
    t = (f"{ind}k_step (wp_s_and_bits cpu _ ?hs ?ht {hx(pc)} true {rd}#5 {rs1}#5 {rs2}#5 (by decide) ({p}) ({q}) ?h1 ?h2)\n"
            f"{ind}  $$ [- $Hk $Hclock $Hpc]\n{ind}case h1 => simp only [KCtx.rget_withRegs', KCtx.setReg_withRegs, RegMap.set_apply, BitVec.reduceEq]; exact {l1}\n{ind}case h2 => simp only [KCtx.rget_withRegs', KCtx.setReg_withRegs, RegMap.set_apply, BitVec.reduceEq]; exact {l2}\n"
            f"{ind}iintro Hk Hclock Hpc\n")
    if gen: t += (f"{ind}generalize hb{gen}g : (if {p} ∧ {q} then 1#64 else 0#64) = b{gen}\n"
                  f"{ind}have hb{gen} : b{gen} = (if {p} ∧ {q} then 1#64 else 0#64) := hb{gen}g.symm\n")
    return t
def jmp(pc, imm, rvc, ind="  "):
    return (f"{ind}k_step (wp_s_j cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {imm}#21 ?htgt) $$ [- $Hk $Hclock $Hpc]\n"
            f"{ind}case htgt => k_tgt\n{ind}iintro Hk Hclock Hpc\n")
def pos(h, ind): return f"{ind}ihave Hpc := pcIs_ite_pos _ _ _ _ {h} $$ Hpc\n"
def neg(h, ind): return f"{ind}ihave Hpc := pcIs_ite_neg _ _ _ _ {h} $$ Hpc\n"
SIMPSET = "RegMap.set_apply, BitVec.reduceEq, if_false, if_true"
def finish(tgt, posf, negs, ind="  "):
    if posf: simpargs = ", ".join(["dispatch7a0", "chD", "chU", "chX", "chP", "chC", "chS", "chL", "chPct"] + posf)
    else: simpargs = ", ".join(["dispatch7a0"] + [f"eq_false {h}" for h in negs])
    t = f"{ind}have htgt : dispatch7a0 c0 c1 c2 = {tgt} := by simp [{simpargs}]\n"
    t += f"{ind}simp only [htgt]\n{ind}iapply HΦ $$ %_ Hk Hclock Hpc\n{ind}ipureintro\n{ind}refine ⟨?_, ?_, ?_, ?_⟩\n"
    t += f"{ind}· repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))\n"
    t += f"{ind}all_goals simp only [{SIMPSET}, h21]\n"
    return t
def call_next(name, args, sfx, ind="  "):
    import re as _re
    args2 = _re.sub(r"\?H(\w+)", lambda m: "?H" + m.group(1) + sfx, args)
    return (f"{ind}iapply ({name} cpu k hsie htier c0 c1 c2 _ {args2}) $$ [- $Hk $Hclock $Hpc]\n"
            f"{ind}rotate_right 1\n{ind}iframe #\n")
def after_next(ind="  "):
    return (f"{ind}iintro %R'' Hk Hclock Hpc %h''\n{ind}iapply HΦ $$ %_ Hk Hclock Hpc\n{ind}ipureintro\n"
            f"{ind}refine ⟨h''.1, ?_, ?_, ?_⟩ <;> simp only [h''.2.1, h''.2.2.1, h''.2.2.2, {SIMPSET}, h21]\n")
def S(h): return f"(by simp only [{SIMPSET}, {h}])"

HDR = '''set_option maxHeartbeats 4000000 in
/-- {DOC} -/
theorem {NAME} {{hlc : HasLC}} {{GF : BundledGFunctors}} [MachGS hlc GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (hsie : k.sie = false) (htier : k.tier = KTier.bare)
    (c0 c1 c2 : BitVec 8) (R : RegMap) (hR : pkRegs k.regs R) (h21 : R 21#5 = BitVec.setWidth 64 c0)
    {HYPS} :
    printkText ∗ kctx cpu ((pkBase k).withRegs R) ∗ clockCells cpu ∗ pcIs cpu {PC0} ∗
    (∀ R' : RegMap, kctx cpu ((pkBase k).withRegs R') -∗ clockCells cpu -∗ pcIs cpu (dispatch7a0 c0 c1 c2) -∗
      ⌜pkRegs k.regs R' ∧ R' 9#5 = R 9#5 ∧ R' 20#5 = R 20#5 ∧ R' 21#5 = R 21#5⌝ -∗ wpLoop cpu)
    ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨#HT, Hk, Hclock, Hpc, HΦ⟩
'''
out = []
# ---- 7d0 ----
t = HDR.format(DOC="The dispatch chain from `0x800007d0`: `%p`, `%c`, `%s`, `%%`, the end-of-string exit, the default.",
  NAME="printk_dispatch_7d0", PC0=hx(0x7d0),
  HYPS='''(hu : c0 ≠ chU) (hlu : ¬(c1 = chU ∧ c0 = chL)) (hllu : ¬(c2 = chU ∧ (c1 = chL ∧ c0 = chL)))
    (hx : c0 ≠ chX) (hlx : ¬(c1 = chX ∧ c0 = chL)) (hllx : ¬(c2 = chX ∧ (c1 = chL ∧ c0 = chL)))''')
t += "  have h27 : R 27#5 = 112#64 := hR.1.2.2.2.2.2.2.2.2\n"
t += facts([0x7d0, 0x7d4, 0x7d8, 0x7dc, 0x7e0, 0x7e4, 0x7e8, 0x7ec])
NEG = ["hu","hlu","hllu","hx","hlx","hllx"]
t += br(0x7d0, False, 7898, 21, 27, "BEQ", "h21, h27, ite_beq_zext_p")
t += "  by_cases hp : c0 = chP\n  · " + pos("hp", "").lstrip() + finish(hx(0x6aa), ["hp"], [], ind="    ")
t += neg("hp", "  ")
t += li(0x7d4, 15, 99, False)
t += br(0x7d8, False, 7960, 21, 15, "BEQ", "h21, ite_beq_zext_c")
t += "  by_cases hc : c0 = chC\n  · " + pos("hc", "").lstrip() + finish(hx(0x6f0), ["hc"], [], ind="    ")
t += neg("hc", "  ")
t += li(0x7dc, 15, 115, False)
t += br(0x7e0, False, 7972, 21, 15, "BEQ", "h21, ite_beq_zext_s")
t += "  by_cases hs : c0 = chS\n  · " + pos("hs", "").lstrip() + finish(hx(0x704), ["hs"], [], ind="    ")
t += neg("hs", "  ")
t += li(0x7e4, 15, 37, False)
t += br(0x7e8, False, 8020, 21, 15, "BEQ", "h21, ite_beq_zext_pct")
t += "  by_cases hpct : c0 = chPct\n  · " + pos("hpct", "").lstrip() + finish(hx(0x73c), ["hpct"], [], ind="    ")
t += neg("hpct", "  ")
t += br(0x7ec, False, 20, 21, 0, "BEQ", "h21, ite_beq_byte")
t += "  by_cases h0 : c0 = 0#8\n  · " + pos("h0", "").lstrip() + finish(hx(0x800), ["h0"], [], ind="    ")
t += neg("h0", "  ")
t += finish(hx(0x7f0), [], NEG + ["hp","hc","hs","hpct","h0"])
out.append(t + "\n")
# ---- 7c6 ----
t = HDR.format(DOC="The dispatch chain from `0x800007c6`: `%llx`, then `0x7d0`.", NAME="printk_dispatch_7c6", PC0=hx(0x7c6),
  HYPS='''(h13 : R 13#5 = BitVec.setWidth 64 c2) (h15 : R 15#5 = if c1 = chL ∧ c0 = chL then 1#64 else 0#64)
    (hu : c0 ≠ chU) (hlu : ¬(c1 = chU ∧ c0 = chL)) (hllu : ¬(c2 = chU ∧ (c1 = chL ∧ c0 = chL)))
    (hx : c0 ≠ chX) (hlx : ¬(c1 = chX ∧ c0 = chL))''')
t += facts([0x7c6, 0x7ca, 0x7cc])
t += addi(0x7c6, 13, 13, 3976, False, "h13")
NEXT7D0 = "(pkRegs_set _ _ _ _ hR (by decide)) " + S("h21") + " hu hlu hllu hx hlx ?Hllx"
t += br(0x7ca, True, 6, 13, 0, "BNE", "ite_bne_sub_x")
t += "  by_cases hc2 : c2 = chX\n  · " + pos("hc2", "").lstrip()
t += br(0x7cc, False, 7874, 15, 0, "BNE", "h15, ite_bne_bit", ind="    ")
t += "    by_cases hll : c1 = chL ∧ c0 = chL\n    · " + pos("hll", "").lstrip()
t += finish(hx(0x68e), ["hc2", "hll.1", "hll.2"], [], ind="      ")
t += neg("hll", "    ")
t += call_next("printk_dispatch_7d0", NEXT7D0, "a", ind="    ") + "    case Hllxa => intro h; exact hll h.2\n" + after_next("    ")
t += neg("hc2", "  ")
t += call_next("printk_dispatch_7d0", NEXT7D0, "b") + "  case Hllxb => intro h; exact hc2 h.1\n" + after_next()
out.append(t + "\n")
# ---- 7b8 ----
t = HDR.format(DOC="The dispatch chain from `0x800007b8`: `%x`, `%lx`, then `0x7c6`.", NAME="printk_dispatch_7b8", PC0=hx(0x7b8),
  HYPS='''(h12 : R 12#5 = BitVec.setWidth 64 c1) (h13 : R 13#5 = BitVec.setWidth 64 c2)
    (h14 : R 14#5 = if c0 = chL then 1#64 else 0#64) (h15 : R 15#5 = if c1 = chL ∧ c0 = chL then 1#64 else 0#64)
    (hu : c0 ≠ chU) (hlu : ¬(c1 = chU ∧ c0 = chL)) (hllu : ¬(c2 = chU ∧ (c1 = chL ∧ c0 = chL)))''')
t += "  have h26 : R 26#5 = 120#64 := hR.1.2.2.2.2.2.2.2.1\n"
t += facts([0x7b8, 0x7bc, 0x7c0, 0x7c2])
t += br(0x7b8, False, 7842, 21, 26, "BEQ", "h21, h26, ite_beq_zext_x")
t += "  by_cases hx : c0 = chX\n  · " + pos("hx", "").lstrip() + finish(hx(0x65a), ["hx"], [], ind="    ")
t += neg("hx", "  ")
t += addi(0x7bc, 12, 12, 3976, False, "h12")
NEXT7C6 = "(pkRegs_set _ _ _ _ hR (by decide)) " + S("h21") + " " + S("h13") + " " + S("h15") + " hu hlu hllu hx ?Hlx"
t += br(0x7c0, True, 6, 12, 0, "BNE", "ite_bne_sub_x")
t += "  by_cases hc1 : c1 = chX\n  · " + pos("hc1", "").lstrip()
t += br(0x7c2, False, 7858, 14, 0, "BNE", "h14, ite_bne_bit", ind="    ")
t += "    by_cases hl : c0 = chL\n    · " + pos("hl", "").lstrip()
t += finish(hx(0x674), ["hc1", "hl"], [], ind="      ")
t += neg("hl", "    ")
t += call_next("printk_dispatch_7c6", NEXT7C6, "a", ind="    ") + "    case Hlxa => intro h; exact hl h.2\n" + after_next("    ")
t += neg("hc1", "  ")
t += call_next("printk_dispatch_7c6", NEXT7C6, "b") + "  case Hlxb => intro h; exact hc1 h.1\n" + after_next()
out.append(t + "\n")
# ---- 7ae ----
t = HDR.format(DOC="The dispatch chain from `0x800007ae`: `%llu`, then `0x7b8`.", NAME="printk_dispatch_7ae", PC0=hx(0x7ae),
  HYPS='''(h12 : R 12#5 = BitVec.setWidth 64 c1) (h13 : R 13#5 = BitVec.setWidth 64 c2)
    (h14 : R 14#5 = if c0 = chL then 1#64 else 0#64) (h15 : R 15#5 = if c1 = chL ∧ c0 = chL then 1#64 else 0#64)
    (hu : c0 ≠ chU) (hlu : ¬(c1 = chU ∧ c0 = chL))''')
t += facts([0x7ae, 0x7b2, 0x7b4])
t += addi(0x7ae, 11, 13, 3979, False, "h13")
NEXT7B8 = "(pkRegs_set _ _ _ _ hR (by decide)) " + " ".join([S("h21"), S("h12"), S("h13"), S("h14"), S("h15")]) + " hu hlu ?Hllu"
t += br(0x7b2, True, 6, 11, 0, "BNE", "ite_bne_sub_u")
t += "  by_cases hc2 : c2 = chU\n  · " + pos("hc2", "").lstrip()
t += br(0x7b4, False, 7818, 15, 0, "BNE", "h15, ite_bne_bit", ind="    ")
t += "    by_cases hll : c1 = chL ∧ c0 = chL\n    · " + pos("hll", "").lstrip()
t += finish(hx(0x63e), ["hc2", "hll.1", "hll.2"], [], ind="      ")
t += neg("hll", "    ")
t += call_next("printk_dispatch_7b8", NEXT7B8, "a", ind="    ") + "    case Hllua => intro h; exact hll h.2\n" + after_next("    ")
t += neg("hc2", "  ")
t += call_next("printk_dispatch_7b8", NEXT7B8, "b") + "  case Hllub => intro h; exact hc2 h.1\n" + after_next()
out.append(t + "\n")
# ---- 7a0 ----
t = HDR.format(DOC="The dispatch chain from `0x800007a0`: `%u`, `%lu`, then `0x7ae`.", NAME="printk_dispatch_7a0", PC0=hx(0x7a0),
  HYPS='''(h12 : R 12#5 = BitVec.setWidth 64 c1) (h13 : R 13#5 = BitVec.setWidth 64 c2)
    (h14 : R 14#5 = if c0 = chL then 1#64 else 0#64) (h15 : R 15#5 = if c1 = chL ∧ c0 = chL then 1#64 else 0#64)''')
t += "  have h24 : R 24#5 = 117#64 := hR.1.2.2.2.2.2.2.1\n"
t += facts([0x7a0, 0x7a4, 0x7a8, 0x7aa])
t += br(0x7a0, False, 7784, 21, 24, "BEQ", "h21, h24, ite_beq_zext_u")
t += "  by_cases hu : c0 = chU\n  · " + pos("hu", "").lstrip() + finish(hx(0x608), ["hu"], [], ind="    ")
t += neg("hu", "  ")
t += addi(0x7a4, 11, 12, 3979, False, "h12")
NEXT7AE = "(pkRegs_set _ _ _ _ hR (by decide)) " + " ".join([S("h21"), S("h12"), S("h13"), S("h14"), S("h15")]) + " hu ?Hlu"
t += br(0x7a8, True, 6, 11, 0, "BNE", "ite_bne_sub_u")
t += "  by_cases hc1 : c1 = chU\n  · " + pos("hc1", "").lstrip()
t += br(0x7aa, False, 7800, 14, 0, "BNE", "h14, ite_bne_bit", ind="    ")
t += "    by_cases hl : c0 = chL\n    · " + pos("hl", "").lstrip()
t += finish(hx(0x622), ["hc1", "hl"], [], ind="      ")
t += neg("hl", "    ")
t += call_next("printk_dispatch_7ae", NEXT7AE, "a", ind="    ") + "    case Hlua => intro h; exact hl h.2\n" + after_next("    ")
t += neg("hc1", "  ")
t += call_next("printk_dispatch_7ae", NEXT7AE, "b") + "  case Hlub => intro h; exact hc1 h.1\n" + after_next()
out.append(t + "\n")

# ================= the arms with loops: %p and %s =================
ARMHDR = '''set_option maxHeartbeats 4000000 in
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
  have hR2 : R 2#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFF40#64 := hR.1.1
  have hR8 : R 8#5 = k.regs 2#5 + 0xFFFFFFFFFFFFFFC0#64 := hR.1.2.1
  have huart' : "uart" ∉ "pr" :: k.locks := by
    intro h; rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact huart h
  have hk7 : kk < 7 := by omega
  have ⟨hramA, halA⟩ := slot184_ok _ hf
  have ⟨hramV, halV⟩ := va_slot_ok (k.regs 2#5) kk (by omega) hf
'''
def ld_ap(pc):
    return f'''  -- ld a5,-120(s0)
  icases pkFrame_ap_acc _ _ _ _ $$ Hframe with ⟨Hap, Hfr⟩
  k_step (wp_s_ld cpu _ ?hs ?ht {hx(pc)} false 3976#12 15#5 8#5 (by decide) (DFrac.own 1)
    (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 kk) ?hram ?hal) $$ [- $Hk $Hclock $Hpc] with [hR8]
  case hram => k_norm [hR8]; exact hramA
  case hal => k_norm [hR8]; exact halA
  iintro Hk Hclock Hpc Hap
  -- addi a4,a5,8
  k_step (wp_s_addi cpu _ ?hs ?ht {hx(pc+4)} false 8#12 14#5 15#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc
  -- sd a4,-120(s0)
  k_step (wp_s_sd cpu _ ?hs ?ht {hx(pc+8)} false 3976#12 8#5 14#5 (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 kk)
    ?hram ?hal) $$ [- $Hk $Hclock $Hpc] with [hR8, ap_next']
  case hram => k_norm [hR8]; exact hramA
  case hal => k_norm [hR8]; exact halA
  iintro Hk Hclock Hpc Hap
  ihave Hframe := Hfr $$ %_ Hap
'''
def ld_va(pc, rd, rvc):
    return f'''  -- ld x{rd},0(a5)
  icases pkFrame_va_acc _ _ _ _ kk hk7 $$ Hframe with ⟨Hva, Hfr⟩
  k_step (wp_s_ld cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} 0#12 {rd}#5 15#5 (by decide) (DFrac.own 1)
    (k.regs (BitVec.ofNat 5 (11 + kk))) ?hram ?hal) $$ [- $Hk $Hclock $Hpc]
  case hram => k_norm; exact hramV
  case hal => k_norm; exact halV
  iintro Hk Hclock Hpc Hva
  ihave Hframe := Hfr $$ Hva
'''
def consputc(pc, imm, n, ind="  "):
    return f'''{ind}-- jal consputc
{ind}iapply (printk_consputc CP cpu (pkBase k) _ γl γd _ ?hs ?ht ?hK ?hn ?hu {hx(pc)} {imm}#21 (by decide) (by decide))
{ind}  $$ [- $Hk $Hclock $Hpc $Hsent]
{ind}rotate_right 1
{ind}iframe #
{ind}case hs => k_norm
{ind}case ht => k_norm
{ind}case hK => k_norm; omega
{ind}case hn => k_norm; omega
{ind}case hu => k_norm; exact huart'
{ind}iintro %R{n} %cs{n} Hk Hclock Hpc %hcs{n} Hsent
{ind}unfold calleeSaved at hcs{n}
{ind}k_norm at hcs{n}
{ind}k_norm
'''
# ---- %p ----
t = ARMHDR.format(DOC="The `%p` arm at `0x800006aa`: `0x` and sixteen hex digits of the next vararg.", NAME="p", IFACE="(CP : CONSPUTC)",
  HYPS='''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1))
    (hp : i + 1 < f.length) (hkk : kk < descs.length) (hdlen : descs.length ≤ 7)
    (hkinds : pkKinds (f.drop (i + 1 + 1)) = (descs.drop (kk + 1)).map PkArgDesc.kind)''', PC0=hx(0x6aa))
t += "  have hR25 : R 25#5 = k.regs 25#5 := hR.2\n"
t += facts([0x6aa, 0x6ac, 0x6b0, 0x6b4, 0x6b8, 0x6bc, 0x6c0, 0x6c4, 0x6c8, 0x6cc, 0x6ce, 0x6d2, 0x6ec, 0x6ee])
t += '''  -- sd s9,40(sp)
  icases pkFrame_s9_acc _ _ _ _ $$ Hframe with ⟨H18, Hfr18⟩
  k_step (wp_s_sd cpu _ ?hs ?ht 0x800006aa#64 true 40#12 2#5 25#5 w18 ?hram ?hal) $$ [- $Hk $Hclock $Hpc]
    with [hR2, hR25]
  case hram => k_norm [hR2]; exact (slot152_ok _ hf).1
  case hal => k_norm [hR2]; exact (slot152_ok _ hf).2
  iintro Hk Hclock Hpc H18
  ihave Hframe := Hfr18 $$ %_ H18
'''
t += ld_ap(0x6ac) + ld_va(0x6b8, 21, False)
t += li(0x6bc, 10, 48, False) + consputc(0x6c0, 2096074, 2) + li(0x6c4, 10, 120, False) + consputc(0x6c8, 2096066, 3)
t += li(0x6cc, 20, 16, True)
t += '''  -- auipc s9,7 ; addi s9,s9,98
  k_step (wp_s_auipc cpu _ ?hs ?ht 0x800006ce#64 false 7#20 25#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc
  k_step (wp_s_addi cpu _ ?hs ?ht 0x800006d2#64 false 98#12 25#5 25#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
    with [digits_addr]
  iintro Hk Hclock Hpc
  -- the sixteen digits
  iapply (printk_hex_loop CP cpu k γl γd hsie htier hK hnoff huart 15 _ _ ?hN ?h25 ?h20 (by omega))
    $$ [- $Hk $Hclock $Hpc $Hsent]
  rotate_right 1
  iframe #
  case hN =>
    exact pkRegsN_set _ _ 25#5 _ (pkRegsN_set _ _ 25#5 _ (pkRegsN_set _ _ 20#5 _
      (pkRegsN_of_cs _ _ _ (pkRegsN_of_cs _ _ _ hR.1 ⟨hcs2.1, hcs2.2.1, hcs2.2.2.2.1, hcs2.2.2.2.2.1, hcs2.2.2.2.2.2.2.2.1, hcs2.2.2.2.2.2.2.2.2.1, hcs2.2.2.2.2.2.2.2.2.2.1, hcs2.2.2.2.2.2.2.2.2.2.2.2.1, hcs2.2.2.2.2.2.2.2.2.2.2.2.2⟩) ⟨hcs3.1, hcs3.2.1, hcs3.2.2.2.1, hcs3.2.2.2.2.1, hcs3.2.2.2.2.2.2.2.1, hcs3.2.2.2.2.2.2.2.2.1, hcs3.2.2.2.2.2.2.2.2.2.1, hcs3.2.2.2.2.2.2.2.2.2.2.2.1, hcs3.2.2.2.2.2.2.2.2.2.2.2.2⟩) (by decide)) (by decide)) (by decide)
  case h25 => simp only [RegMap.set_apply, BitVec.reduceEq, if_true]
  case h20 => simp only [RegMap.set_apply, BitVec.reduceEq, if_true, if_false]
  iintro %R4 %cs4 Hk Hclock Hpc Hsent %h4
  -- ld s9,40(sp)
  icases pkFrame_s9_acc _ _ _ _ $$ Hframe with ⟨H18, Hfr18⟩
  k_step (wp_s_ld cpu _ ?hs ?ht 0x800006ec#64 true 40#12 25#5 2#5 (by decide) (DFrac.own 1) (k.regs 25#5) ?hram ?hal)
    $$ [- $Hk $Hclock $Hpc] with [h4.1.1]
  case hram => k_norm [h4.1.1]; exact (slot152_ok _ hf).1
  case hal => k_norm [h4.1.1]; exact (slot152_ok _ hf).2
  iintro Hk Hclock Hpc H18
  ihave Hframe := Hfr18 $$ %_ H18
'''
t += jmp(0x6ee, 2096768, True)
t += '''  ihave Hsent := (show uartSentSub γd (bs ++ cs2 ++ cs3 ++ cs4) ⊢ uartSentSub γd (bs ++ (cs2 ++ (cs3 ++ cs4))) from
    by rw [List.append_assoc, List.append_assoc]) $$ Hsent
  iapply Hnext $$ %_ %(i + 1) %(kk + 1) %(cs2 ++ (cs3 ++ cs4)) %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
  ipureintro
  refine ⟨pkRegs_set25 _ _ h4.1, ?_, by omega, hp, hkinds⟩
  simp only [RegMap.set_apply, BitVec.reduceEq, if_false]
  rw [h4.2.1]
  simp only [RegMap.set_apply, BitVec.reduceEq, if_false]
  exact hcs3.2.2.1.trans (hcs2.2.2.1.trans hR9)

'''
out.append(t)
# ---- %s ----
t = ARMHDR.format(DOC="The `%s` arm at `0x80000704`: the string the next vararg points to, or `(null)`.", NAME="s", IFACE="(CP : CONSPUTC)",
  HYPS='''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1))
    (hp : i + 1 < f.length) (hdlen : descs.length ≤ 7) (d : PkArgDesc) (hd : descs[kk]? = some d) (hdk : d.kind = .str)
    (hkinds : pkKinds (f.drop (i + 1 + 1)) = (descs.drop (kk + 1)).map PkArgDesc.kind)''', PC0=hx(0x704))
t = t.replace("  have hk7 : kk < 7 := by omega\n", "  have hkk : kk < descs.length := (List.getElem?_eq_some_iff.mp hd).1\n  have hk7 : kk < 7 := by omega\n")
t += facts([0x704, 0x708, 0x70c, 0x710, 0x714, 0x718, 0x71c, 0x72e, 0x732, 0x736, 0x73a])
t += ld_ap(0x704) + ld_va(0x710, 20, False)
t += '''  icases pkDescs_acc k.regs descs kk d hd $$ Hdescs with ⟨Hd, Hdcl⟩
  rcases d with _ | _ | ⟨dq, s⟩
  · exact absurd hdk (by decide)
  · -- a null pointer: "(null)"
    icases pkDescRes_null_pure _ $$ Hd with %hv
    have hv' : k.regs (BitVec.ofNat 5 (11 + kk)) = 0#64 := hv
'''
t += br(0x714, False, 26, 20, 0, "BEQ", "hv', ite_beq_zero", ind="    ")
t += '''    k_step (wp_s_auipc cpu _ ?hs ?ht 0x8000072e#64 false 7#20 20#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
    iintro Hk Hclock Hpc
    k_step (wp_s_addi cpu _ ?hs ?ht 0x80000732#64 false 2266#12 20#5 20#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
      with [null_addr]
    iintro Hk Hclock Hpc
'''
t += li(0x736, 10, 40, False, ind="    ") + jmp(0x73a, 2097126, True, ind="    ")
t += '''    ihave Hnull := kernelData_null $$ HD
    ihave Hnull := (show byteBuf 0x80007008#64 DFrac.discard nullStr ⊢
      byteBuf (GF := GF) 0x80007008#64 DFrac.discard (nullBody ++ [0#8]) from by rw [nullStr_eq]) $$ Hnull
    iapply (printk_str_loop CP cpu k γl γd hsie htier hK hnoff huart 0x80007008#64 DFrac.discard nullBody nullBody_nonul
      inRam_null 5 0 _ bs (by decide) ?hRn ?h20n ?h10n) $$ [- $Hk $Hclock $Hpc $Hsent]
    rotate_right 1
    iframe #
    first | (isplitr; · iexact Hnull) | skip
    case hRn => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
    case h20n => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; rfl
    case h10n => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; decide
    iintro %R' %cs Hk Hclock Hpc _ Hsent %h'
    ihave Hd := pkDescRes_null_intro _ hv
    ihave Hdescs := Hdcl $$ Hd
    iapply Hnext $$ %_ %(i + 1) %(kk + 1) %cs %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
    ipureintro
    refine ⟨h'.1, ?_, by omega, hp, hkinds⟩
    rw [h'.2]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false]; exact hR9
  · -- a string
    icases pkDescRes_str_acc _ _ _ $$ Hd with ⟨%⟨hs, hv, hram⟩, Hbs, Hdcl'⟩
    have hv' : k.regs (BitVec.ofNat 5 (11 + kk)) ≠ 0#64 := hv
'''
t += br(0x714, False, 26, 20, 0, "BEQ", "ite_beq_zero, if_neg hv'", ind="    ")
t += '''    -- lbu a0,0(s4): the first character
    simp only [pkVararg] at hv hram
    simp only [pkVararg]
    have hb0 : (s ++ [0#8])[0]? = some (fmtByte s 0) := fmtByte_get s 0 (Nat.zero_le _)
    icases byteBuf_acc0 _ dq (s ++ [0#8]) _ hb0 $$ Hbs with ⟨Hb, Hclose⟩
    k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000718#64 false 0#12 10#5 20#5 (by decide) dq (fmtByte s 0) ?hram)
      $$ [- $Hk $Hclock $Hpc]
    case hram => k_norm; simpa using inRam_byte hram 0 (by omega)
    iintro Hk Hclock Hpc Hb
    ihave Hbs := Hclose $$ Hb
'''
t += br(0x71c, False, 7762, 10, 0, "BEQ", "ite_beq_byte", ind="    ")
t += '''    rcases Nat.eq_zero_or_pos s.length with hs0 | hspos
    · -- the empty string
      have hz : fmtByte s 0 = 0#8 := by have := fmtByte_end s; rw [hs0] at this; exact this
      ihave Hpc := pcIs_ite_pos _ _ _ _ hz $$ Hpc
      ihave Hd := Hdcl' $$ Hbs
      ihave Hdescs := Hdcl $$ Hd
      ihave Hsent := (show uartSentSub γd bs ⊢ uartSentSub γd (bs ++ []) from by rw [List.append_nil]) $$ Hsent
      iapply Hnext $$ %_ %(i + 1) %(kk + 1) %([]) %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
      ipureintro
      refine ⟨?_, ?_, by omega, hp, hkinds⟩
      · repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
      · simp only [RegMap.set_apply, BitVec.reduceEq, if_false]; exact hR9
    · have hnz : fmtByte s 0 ≠ 0#8 := fmtByte_ne_zero s hs 0 hspos
      ihave Hpc := pcIs_ite_neg _ _ _ _ hnz $$ Hpc
      iapply (printk_str_loop CP cpu k γl γd hsie htier hK hnoff huart (k.regs (BitVec.ofNat 5 (11 + kk))) dq s hs hram
        (s.length - 1) 0 _ bs (by omega) ?hRs ?h20s ?h10s) $$ [- $Hk $Hclock $Hpc $Hbs $Hsent]
      rotate_right 1
      iframe #
      case hRs => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
      case h20s => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; simp
      case h10s => simp only [RegMap.set_apply, BitVec.reduceEq, if_true]
      iintro %R' %cs Hk Hclock Hpc Hbs Hsent %h'
      ihave Hd := Hdcl' $$ Hbs
      ihave Hdescs := Hdcl $$ Hd
      iapply Hnext $$ %_ %(i + 1) %(kk + 1) %cs %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
      ipureintro
      refine ⟨h'.1, ?_, by omega, hp, hkinds⟩
      rw [h'.2]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false]; exact hR9

'''
out.append(t)

# ================= the '%' turn =================
TURNHDR = '''set_option maxHeartbeats 4000000 in
/-- {DOC} -/
theorem {NAME} (CP : CONSPUTC) (PI : PRINTINT) {{hlc : HasLC}} {{GF : BundledGFunctors}} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γpr γl : GName) (γd : UartNames) (bs : List (BitVec 8)) (dqf : DFrac)
    (f : List (BitVec 8)) (descs : List PkArgDesc)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 48 ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (huart : "uart" ∉ k.locks) (hf : stackFacts (k.regs 2#5) 24) (hflen : f.length + 4 < 2 ^ 31)
    (hnonul : nonul f) (hdlen : descs.length ≤ 7) (hfmt : inRam (k.regs 10#5) (f.length + 1))
    (i kk : Nat) (R : RegMap) (w18 : BitVec 64) (hR : pkRegs k.regs R) (hR20 : R 20#5 = BitVec.ofNat 64 i)
    {HYPS}
    (hi : i < f.length) (hp : fmtByte f i = chPct)
    (hkinds : pkKinds (f.drop i) = (descs.drop kk).map PkArgDesc.kind) :
    printkText ∗ kernelText ∗ kernelData ∗ isTxLock γl γd ∗
    kctx cpu ((pkBase k).withRegs R) ∗ clockCells cpu ∗ pcIs cpu {PC0} ∗
    byteBuf (k.regs 10#5) dqf (f ++ [0#8]) ∗ pkDescs k.regs descs ∗
    pkFrame (k.regs 2#5) k.regs (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 kk) w18 ∗
    uartSentSub γd bs ∗ locked γpr cpu ∗ pkCont cpu k γpr γd bs dqf f descs i kk
    ⊢ wpLoop (GF := GF) cpu := by
  iintro ⟨#HT, #Htext, #HD, #Htx, Hk, Hclock, Hpc, Hbuf, Hdescs, Hframe, Hsent, Hlocked, Hcont⟩
'''
ARMARGS = "cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf hflen i kk _ w18"
STATE = "$Hk $Hclock $Hpc $Hbuf $Hdescs $Hframe $Hsent $Hlocked"
def arm_call(name, iface, sfx, extra, ind):
    return (f"{ind}ihave Hnext := pkCont_next _ _ _ _ _ _ _ _ _ _ $$ Hcont\n"
            f"{ind}iapply (printk_arm_{name} {iface} {ARMARGS} ?HR{sfx} ?H20{sfx} ?H9{sfx} {extra}) $$ [- {STATE} $Hnext]\n"
            f"{ind}rotate_right 1\n{ind}iframe #\n"
            f"{ind}case HR{sfx} => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))\n"
            f"{ind}case H20{sfx} => first | (rw [h'.2.2.1]; simp only [{SIMPSET}, hR20]) | simp only [{SIMPSET}, hR20]\n"
            f"{ind}case H9{sfx} => first | (rw [h'.2.1]; simp only [{SIMPSET}, hR9]) | simp only [{SIMPSET}, hR9] | simp only [{SIMPSET}]\n")
def kinds_num(pkdir, n, ind):
    return (f"{ind}have hk := pkKinds_at_dir f i hi hp c0 c1 c2 hc0 hc1 hc2 .num {n} (by omega) ({pkdir})\n"
            f"{ind}rw [hk] at hkinds\n"
            f"{ind}obtain ⟨d, hd, hdk, hrest⟩ := kinds_step _ _ _ _ hkinds.symm\n"
            f"{ind}have hkk : kk < descs.length := (List.getElem?_eq_some_iff.mp hd).1\n")
# ---- the tail after the dispatch ----
t = TURNHDR.format(DOC="After the dispatch: the arm `dispatch7a0` selected (`%d`, `%ld`, `%lld` excluded).", NAME="printk_pct_tail",
  HYPS='''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1))
    (c0 c1 c2 : BitVec 8) (hc0 : c0 = fmtByte f (i + 1)) (hc1 : c1 = fmtByte f (i + 2)) (hc2 : c2 = fmtByte f (i + 3))
    (hR21 : R 21#5 = BitVec.setWidth 64 c0)
    (hd : c0 ≠ chD) (hld : ¬(c1 = chD ∧ c0 = chL)) (hlld : ¬(c2 = chD ∧ (c1 = chL ∧ c0 = chL)))''',
  PC0="(dispatch7a0 c0 c1 c2)")
t = t.replace("  iintro ⟨#HT, #Htext, #HD, #Htx, Hk, Hclock, Hpc, Hbuf, Hdescs, Hframe, Hsent, Hlocked, Hcont⟩\n",
  "  iintro ⟨#HT, #Htext, #HD, #Htx, Hk, Hclock, Hpc, Hbuf, Hdescs, Hframe, Hsent, Hlocked, Hcont⟩\n  have h' : pkRegs k.regs R ∧ R 9#5 = R 9#5 ∧ R 20#5 = R 20#5 ∧ R 21#5 = R 21#5 := ⟨hR, rfl, rfl, rfl⟩\n  unfold dispatch7a0\n")
def nz(ch, cvar, hcv): return f"(fmt_lt_of_ne f _ (by omega) (by rw [← {hcv}, {ch}]; decide))"
# order: u, lu, llu, x, lx, llx, p, c, s, pct, 0, default
cases = [
  ("hu", "c0 = chU", "u", "(PI : PRINTINT)".replace("(PI : PRINTINT)","PI"), "pkDir_u c1 c2", 0, ["hu"], "hp1 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hu]; decide)\n"),
  ("hlu", "c1 = chU ∧ c0 = chL", "lu", "PI", "pkDir_lu c2", 1, ["hlu.1","hlu.2"], "hp2 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hlu.2]; decide)\nhave hp2 : i + 2 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc1, hlu.1]; decide)\n"),
  ("hllu", "c2 = chU ∧ (c1 = chL ∧ c0 = chL)", "llu", "PI", "pkDir_llu", 2, ["hllu.1","hllu.2.1","hllu.2.2"], "hp3 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hllu.2.2]; decide)\nhave hp2 : i + 2 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc1, hllu.2.1]; decide)\nhave hp3 : i + 3 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc2, hllu.1]; decide)\n"),
  ("hx", "c0 = chX", "x", "PI", "pkDir_x c1 c2", 0, ["hx"], "hp1 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hx]; decide)\n"),
  ("hlx", "c1 = chX ∧ c0 = chL", "lx", "PI", "pkDir_lx c2", 1, ["hlx.1","hlx.2"], "hp2 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hlx.2]; decide)\nhave hp2 : i + 2 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc1, hlx.1]; decide)\n"),
  ("hllx", "c2 = chX ∧ (c1 = chL ∧ c0 = chL)", "llx", "PI", "pkDir_llx", 2, ["hllx.1","hllx.2.1","hllx.2.2"], "hp3 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hllx.2.2]; decide)\nhave hp2 : i + 2 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc1, hllx.2.1]; decide)\nhave hp3 : i + 3 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc2, hllx.1]; decide)\n"),
  ("hpp", "c0 = chP", "p", "CP", "pkDir_p c1 c2", 0, ["hpp"], "hp1 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hpp]; decide)\n"),
  ("hc", "c0 = chC", "c", "CP", "pkDir_c c1 c2", 0, ["hc"], "hp1 hkk hdlen hrest.symm", "have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hc]; decide)\n"),
]
for (hn, cond, arm, iface, pkdir, n, subs, extra, hps) in cases:
    t += f"  by_cases {hn} : {cond}\n  · ihave Hpc := pcIs_ite_pos _ _ _ _ {hn} $$ Hpc\n"
    for line in hps.strip().split("\n"): t += "    " + line + "\n"
    dirproof = "by rw [" + ", ".join(subs) + "]; exact " + pkdir
    t += kinds_num(dirproof, n, "    ")
    t += arm_call(arm, iface, arm, extra, "    ")
    t += f"  ihave Hpc := pcIs_ite_neg _ _ _ _ {hn} $$ Hpc\n"
# %s
t += '''  by_cases hs : c0 = chS
  · ihave Hpc := pcIs_ite_pos _ _ _ _ hs $$ Hpc
    have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hs]; decide)
    have hk := pkKinds_at_dir f i hi hp c0 c1 c2 hc0 hc1 hc2 .str 0 (by omega) (by rw [hs]; exact pkDir_s c1 c2)
    rw [hk] at hkinds
    obtain ⟨d, hd, hdk, hrest⟩ := kinds_step _ _ _ _ hkinds.symm
'''
t += arm_call("s", "CP", "s", "hp1 hdlen d hd hdk hrest.symm", "    ")
t += "  ihave Hpc := pcIs_ite_neg _ _ _ _ hs $$ Hpc\n"
# %%
t += '''  by_cases hpct : c0 = chPct
  · ihave Hpc := pcIs_ite_pos _ _ _ _ hpct $$ Hpc
    have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0, hpct]; decide)
    have hk := pkKinds_at_none f i hi hp c0 c1 c2 hc0 hc1 hc2 (by rw [hpct]; exact pkDir_pct c1 c2)
    rw [hk] at hkinds
'''
t += arm_call("pct", "CP", "pct", "hp1 hkinds", "    ")
t += "  ihave Hpc := pcIs_ite_neg _ _ _ _ hpct $$ Hpc\n"
# exit
t += '''  by_cases h0 : c0 = 0#8
  · ihave Hpc := pcIs_ite_pos _ _ _ _ h0 $$ Hpc
    ihave Hexit := pkCont_exit _ _ _ _ _ _ _ _ _ _ $$ Hcont
    iapply Hexit $$ %_ %_ Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked
    ipureintro
    exact hR
  ihave Hpc := pcIs_ite_neg _ _ _ _ h0 $$ Hpc
  -- the default arm
  have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0]; exact h0)
  have hnone : pkDir c0 c1 c2 = (none, 0) := by
    apply pkDir_none
    intro h
    rcases h with h | h | h | h | h | h | ⟨hl, h | h | h | ⟨hll, h | h | h⟩⟩
    · exact hd h
    · exact hu h
    · exact hx h
    · exact hpp h
    · exact hc h
    · exact hs h
    · exact hld ⟨h, hl⟩
    · exact hlu ⟨h, hl⟩
    · exact hlx ⟨h, hl⟩
    · exact hlld ⟨h, hll, hl⟩
    · exact hllu ⟨h, hll, hl⟩
    · exact hllx ⟨h, hll, hl⟩
  have hk := pkKinds_at_none f i hi hp c0 c1 c2 hc0 hc1 hc2 hnone
  rw [hk] at hkinds
'''
t += arm_call("default", "CP", "def", "hp1 hkinds", "  ")
out.append(t + "\n")

# ---- the 0x5e2 path ----
def dispatch_and_tail(sfx, hlld, ind):
    return f'''{ind}iapply (printk_dispatch_7a0 cpu k hsie htier c0 c1 c2 _ ?HR{sfx} ?H21{sfx} ?H12{sfx} ?H13{sfx} ?H14{sfx} ?H15{sfx})
{ind}  $$ [- $Hk $Hclock $Hpc]
{ind}rotate_right 1
{ind}iframe #
{ind}case HR{sfx} => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
{ind}case H21{sfx} => simp only [{SIMPSET}, hR21]
{ind}case H12{sfx} => simp only [{SIMPSET}]
{ind}case H13{sfx} => simp only [{SIMPSET}]
{ind}case H14{sfx} => simp only [KCtx.rget_withRegs', KCtx.setReg_withRegs, RegMap.set_apply, BitVec.reduceEq]; exact hR14
{ind}case H15{sfx} => simp only [KCtx.rget_withRegs', KCtx.setReg_withRegs, RegMap.set_apply, BitVec.reduceEq]; exact hb15'
{ind}iintro %R' Hk Hclock Hpc %h'
{ind}iapply (printk_pct_tail CP PI cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf hflen hnonul hdlen hfmt i kk R' w18
{ind}  h'.1 ?HA{sfx} ?HB{sfx} c0 c1 c2 hc0 hc1 hc2 ?HC{sfx} hd hld {hlld} hi hp hkinds) $$ [- {STATE} $Hcont]
{ind}rotate_right 1
{ind}iframe #
{ind}case HA{sfx} => rw [h'.2.2.1]; simp only [{SIMPSET}]; exact hR20
{ind}case HB{sfx} => rw [h'.2.1]; simp only [{SIMPSET}]; exact hR9
{ind}case HC{sfx} => rw [h'.2.2.2]; simp only [{SIMPSET}, hR21]
'''
t = TURNHDR.format(DOC="The `%` path from `0x800005e2`: the third byte, the `l`/`ll` flags, `%lld`, the dispatch.", NAME="printk_pct_5e2",
  HYPS='''(hR9 : R 9#5 = BitVec.ofNat 64 (i + 1)) (hR15 : R 15#5 = BitVec.ofNat 64 (i + 1))
    (c0 c1 : BitVec 8) (hc0 : c0 = fmtByte f (i + 1)) (hc1 : c1 = fmtByte f (i + 2))
    (hp1 : i + 1 < f.length) (hc00 : c0 ≠ 0#8) (hc10 : c1 ≠ 0#8) (hd : c0 ≠ chD) (hld : ¬(c1 = chD ∧ c0 = chL))
    (hR13 : R 13#5 = BitVec.setWidth 64 c1) (hR14 : R 14#5 = if c0 = chL then 1#64 else 0#64)
    (hR21 : R 21#5 = BitVec.setWidth 64 c0)''', PC0=hx(0x5e2))
t += '''  have hR18 : R 18#5 = k.regs 10#5 := hR.1.2.2.1
  have hp2 : i + 2 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc1]; exact hc10)
'''
t += facts([0x5e2, 0x5e4, 0x5e6, 0x5ea, 0x78c, 0x790, 0x794, 0x796, 0x79a, 0x79c])
t += add(0x5e2, 15, 15, 18, True, "hR15, hR18") + mv(0x5e4, 12, 13, True, "hR13")
t += '''  -- lbu a3,2(a5): the third byte
  obtain ⟨c2, hc2⟩ : ∃ c, c = fmtByte f (i + 3) := ⟨_, rfl⟩
  have hb3 : (f ++ [0#8])[i + 3]? = some c2 := by rw [hc2]; exact fmtByte_get f (i + 3) (by omega)
  icases byteBuf_acc _ dqf _ (i + 3) c2 hb3 $$ Hbuf with ⟨Hb, Hclose⟩
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x800005e6#64 false 2#12 13#5 15#5 (by decide) dqf c2 ?hram) $$ [- $Hk $Hclock $Hpc]
    with [fmt_i3]
  case hram => k_norm [fmt_i3]; exact inRam_byte hfmt (i + 3) (by omega)
  iintro Hk Hclock Hpc Hb
  ihave Hbuf := Hclose $$ Hb
'''
t += jmp(0x5ea, 418, True)
t += addi(0x78c, 15, 12, 3988, False, "") + sltiu(0x790, 15, 15, "sltiu_zext_l", gen=("15", "c1 = chL"))
t += andbits(0x794, 15, 15, 14, "c1 = chL", "c0 = chL", "hb15", "hR14", gen="15'")
t += addi(0x796, 11, 13, 3996, False, "")
t += br(0x79a, True, 6, 11, 0, "BNE", "ite_bne_sub_d")
t += "  by_cases hc2d : c2 = chD\n  · ihave Hpc := pcIs_ite_pos _ _ _ _ hc2d $$ Hpc\n"
t += br(0x79c, False, 7760, 15, 0, "BNE", "", ind="    ")
t += "    ihave Hpc := pcIs_bne_bit _ _ _ _ _ hb15' $$ Hpc\n"
t += '''    by_cases hll : c1 = chL ∧ c0 = chL
    · ihave Hpc := pcIs_ite_pos _ _ _ _ hll $$ Hpc
      have hp3 : i + 3 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc2, hc2d]; decide)
      have h' : pkRegs k.regs R ∧ R 9#5 = R 9#5 ∧ R 20#5 = R 20#5 ∧ R 21#5 = R 21#5 := ⟨hR, rfl, rfl, rfl⟩
'''
t += kinds_num("by rw [hll.2, hll.1, hc2d]; exact pkDir_lld", 2, "      ")
t += arm_call("lld", "PI", "lld", "hp3 hkk hdlen hrest.symm", "      ")
t += "    ihave Hpc := pcIs_ite_neg _ _ _ _ hll $$ Hpc\n"
t += dispatch_and_tail("a", "(fun h => hll h.2)", "    ")
t += "  ihave Hpc := pcIs_ite_neg _ _ _ _ hc2d $$ Hpc\n"
t += dispatch_and_tail("b", "(fun h => hc2d h.1)", "  ")
out.append(t + "\n")

# ---- the '%' prefix from 0x57c ----
def indent(txt, n):
    pad = " " * n
    return "".join((pad + l if l.strip() else l) for l in txt.splitlines(True))
def d_arm(sfx, ind):
    return (f"{ind}have h' : pkRegs k.regs R ∧ R 9#5 = R 9#5 ∧ R 20#5 = R 20#5 ∧ R 21#5 = R 21#5 := ⟨hR, rfl, rfl, rfl⟩\n"
            + kinds_num("by rw [hd]; exact pkDir_d c1 (fmtByte f (i + 3))", 0, ind).replace("c0 c1 c2 hc0 hc1 hc2", "c0 c1 (fmtByte f (i + 3)) hc0 hc1 rfl")
            + arm_call("d", "PI", "d" + sfx, "hp1 hkk hdlen hrest.symm", ind))
def to_5e2(sfx, hld, ind):
    return f"""{ind}iapply (printk_pct_5e2 CP PI cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf hflen hnonul hdlen hfmt i kk _ w18
{ind}  ?HR{sfx} ?H20{sfx} ?H9{sfx} ?H15{sfx} c0 c1 hc0 hc1 hp1 hc00 hc10 hd {hld} ?H13{sfx} ?H14{sfx} ?H21{sfx} hi hp hkinds)
{ind}  $$ [- {STATE} $Hcont]
{ind}rotate_right 1
{ind}iframe #
{ind}case HR{sfx} => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
{ind}case H20{sfx} => simp only [{SIMPSET}]; exact hR20
{ind}case H9{sfx} => simp only [{SIMPSET}]
{ind}case H15{sfx} => simp only [{SIMPSET}]
{ind}case H13{sfx} => simp only [{SIMPSET}]
{ind}case H14{sfx} => simp only [KCtx.rget_withRegs', KCtx.setReg_withRegs, RegMap.set_apply, BitVec.reduceEq]; exact hb14
{ind}case H21{sfx} => simp only [{SIMPSET}]
"""
t = TURNHDR.format(DOC="A `%` at `0x8000057c`: the next bytes, `%d`, `%ld`, and the paths to the dispatch.", NAME="printk_pct",
  HYPS="(hR10 : R 10#5 = BitVec.setWidth 64 (fmtByte f i))", PC0=hx(0x57c))
t += """  have hR18 : R 18#5 = k.regs 10#5 := hR.1.2.2.1
  have hR19 : R 19#5 = 37#64 := hR.1.2.2.2.1
  have hR23 : R 23#5 = 100#64 := hR.1.2.2.2.2.2.1
"""
t += facts([0x57c, 0x580, 0x584, 0x586, 0x58a, 0x58e, 0x592, 0x596, 0x59a, 0x59e, 0x5a2, 0x5a6, 0x5aa, 0x5ac,
            0x76e, 0x772, 0x776, 0x77a, 0x77c, 0x77e, 0x79c, 0x780, 0x784, 0x788, 0x78a, 0x78c, 0x790, 0x794, 0x796, 0x79a])
t += br(0x57c, False, 8172, 10, 19, "BNE", "hR10, hR19, ite_bne_zext_pct, if_pos hp")
t += """  -- addiw a5,s4,1 ; mv s1,a5 ; add a4,s2,a5
  k_step (wp_s_addiw cpu _ ?hs ?ht 0x80000580#64 false 1#12 15#5 20#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
    with [hR20, addiw_succ i (by omega)]
  iintro Hk Hclock Hpc
"""
t += mv(0x584, 9, 15, True) + add(0x586, 14, 18, 15, False, "hR18")
t += """  -- lbu s5,0(a4): the byte after the `%`
  obtain ⟨c0, hc0⟩ : ∃ c, c = fmtByte f (i + 1) := ⟨_, rfl⟩
  have hb1 : (f ++ [0#8])[i + 1]? = some c0 := by rw [hc0]; exact fmtByte_get f (i + 1) (by omega)
  icases byteBuf_acc _ dqf _ (i + 1) c0 hb1 $$ Hbuf with ⟨Hb, Hclose⟩
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x8000058a#64 false 0#12 21#5 14#5 (by decide) dqf c0 ?hram) $$ [- $Hk $Hclock $Hpc]
  case hram => k_norm; exact inRam_byte hfmt (i + 1) (by omega)
  iintro Hk Hclock Hpc Hb
  ihave Hbuf := Hclose $$ Hb
"""
t += br(0x58e, False, 498, 21, 0, "BEQ", "ite_beq_byte")
t += "  by_cases hc00 : c0 = 0#8\n"
z = "ihave Hpc := pcIs_ite_pos _ _ _ _ hc00 $$ Hpc\n"
z += """have hend : i + 1 = f.length := (fmtByte_zero_iff f hnonul (i + 1) (by omega)).1 (by rw [← hc0]; exact hc00)
have hc1z : fmtByte f (i + 2) = 0#8 := fmtByte_ge f _ (by omega)
have hc2z : fmtByte f (i + 3) = 0#8 := fmtByte_ge f _ (by omega)
"""
z += addi(0x780, 14, 21, 3988, False, "", ind="") + sltiu(0x784, 14, 14, "sltiu_zext_l", ind="", gen=("14", "c0 = chL"))
z += mv(0x788, 12, 21, True, ind="") + mv(0x78a, 13, 21, True, ind="")
z += addi(0x78c, 15, 12, 3988, False, "", ind="") + sltiu(0x790, 15, 15, "sltiu_zext_l", ind="", gen=("15", "c0 = chL"))
z += andbits(0x794, 15, 15, 14, "c0 = chL", "c0 = chL", "hb15", "hb14", ind="", gen="15'")
z += addi(0x796, 11, 13, 3996, False, "", ind="")
z += br(0x79a, True, 6, 11, 0, "BNE", "ite_bne_sub_d", ind="")
z += """ihave Hpc := pcIs_ite_neg _ _ _ _ (by rw [hc00]; decide) $$ Hpc
iapply (printk_dispatch_7a0 cpu k hsie htier c0 (fmtByte f (i + 2)) (fmtByte f (i + 3)) _ ?HRz ?H21z ?H12z ?H13z ?H14z ?H15z)
  $$ [- $Hk $Hclock $Hpc]
rotate_right 1
iframe #
case HRz => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
case H21z => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
case H12z => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; rw [hc1z, hc00]
case H13z => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; rw [hc2z, hc00]
case H14z => simp only [KCtx.rget_withRegs', KCtx.setReg_withRegs, RegMap.set_apply, BitVec.reduceEq]; exact hb14
case H15z => exact hb15'.trans (by rw [hc1z, hc00])
iintro %R' Hk Hclock Hpc %h'
iapply (printk_pct_tail CP PI cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf hflen hnonul hdlen hfmt i kk R' w18
  h'.1 ?HAz ?HBz c0 (fmtByte f (i + 2)) (fmtByte f (i + 3)) hc0 rfl rfl ?HCz (by rw [hc00]; decide)
  (fun h => by rw [hc1z] at h; exact absurd h.1 (by decide)) (fun h => by rw [hc2z] at h; exact absurd h.1 (by decide))
  hi hp hkinds) $$ [- """ + STATE + """ $Hcont]
rotate_right 1
iframe #
case HAz => rw [h'.2.2.1]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; exact hR20
case HBz => rw [h'.2.1]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
case HCz => rw [h'.2.2.2]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
"""
t += "  · " + indent(z, 4).lstrip()
n1 = "ihave Hpc := pcIs_ite_neg _ _ _ _ hc00 $$ Hpc\n"
n1 += """have hp1 : i + 1 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc0]; exact hc00)
-- lbu a3,1(a4): the second byte
obtain ⟨c1, hc1⟩ : ∃ c, c = fmtByte f (i + 2) := ⟨_, rfl⟩
have hb2 : (f ++ [0#8])[i + 2]? = some c1 := by rw [hc1]; exact fmtByte_get f (i + 2) (by omega)
icases byteBuf_acc _ dqf _ (i + 2) c1 hb2 $$ Hbuf with ⟨Hb, Hclose⟩
k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000592#64 false 1#12 13#5 14#5 (by decide) dqf c1 ?hram) $$ [- $Hk $Hclock $Hpc]
  with [ofNat_succ', Nat.add_assoc, Nat.reduceAdd]
case hram => k_norm [ofNat_succ', Nat.add_assoc, Nat.reduceAdd]; exact inRam_byte hfmt (i + 2) (by omega)
iintro Hk Hclock Hpc Hb
ihave Hbuf := Hclose $$ Hb
"""
n1 += br(0x596, False, 472, 13, 0, "BEQ", "ite_beq_byte", ind="")
n1 += "by_cases hc10 : c1 = 0#8\n"
y = "ihave Hpc := pcIs_ite_pos _ _ _ _ hc10 $$ Hpc\n"
y += """have hend : i + 2 = f.length := (fmtByte_zero_iff f hnonul (i + 2) (by omega)).1 (by rw [← hc1]; exact hc10)
have hc2z : fmtByte f (i + 3) = 0#8 := fmtByte_ge f _ (by omega)
"""
y += br(0x76e, False, 7772, 21, 23, "BEQ", "hR23, ite_beq_zext_d", ind="")
y += "by_cases hd : c0 = chD\n"
y += "· " + indent("ihave Hpc := pcIs_ite_pos _ _ _ _ hd $$ Hpc\n" + d_arm("1", ""), 2).lstrip()
yn = "ihave Hpc := pcIs_ite_neg _ _ _ _ hd $$ Hpc\n"
yn += addi(0x772, 14, 21, 3988, False, "", ind="") + sltiu(0x776, 14, 14, "sltiu_zext_l", ind="", gen=("14", "c0 = chL"))
yn += mv(0x77a, 12, 13, True, ind="") + li(0x77c, 15, 0, True, ind="") + jmp(0x77e, 34, True, ind="")
yn += """iapply (printk_dispatch_7a0 cpu k hsie htier c0 c1 (fmtByte f (i + 3)) _ ?HRy ?H21y ?H12y ?H13y ?H14y ?H15y)
  $$ [- $Hk $Hclock $Hpc]
rotate_right 1
iframe #
case HRy => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
case H21y => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
case H12y => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
case H13y => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; rw [hc2z, hc10]
case H14y => simp only [KCtx.rget_withRegs', KCtx.setReg_withRegs, RegMap.set_apply, BitVec.reduceEq]; exact hb14
case H15y =>
  refine Eq.trans (b := 0#64) rfl ?_
  rw [if_neg]; intro h; rw [hc10] at h; exact absurd h.1 (by decide)
iintro %R' Hk Hclock Hpc %h'
iapply (printk_pct_tail CP PI cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf hflen hnonul hdlen hfmt i kk R' w18
  h'.1 ?HAy ?HBy c0 c1 (fmtByte f (i + 3)) hc0 hc1 rfl ?HCy hd
  (fun h => by rw [hc10] at h; exact absurd h.1 (by decide)) (fun h => by rw [hc2z] at h; exact absurd h.1 (by decide))
  hi hp hkinds) $$ [- """ + STATE + """ $Hcont]
rotate_right 1
iframe #
case HAy => rw [h'.2.2.1]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]; exact hR20
case HBy => rw [h'.2.1]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
case HCy => rw [h'.2.2.2]; simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
"""
y += "· " + indent(yn, 2).lstrip()
n1 += "· " + indent(y, 2).lstrip()
x = "ihave Hpc := pcIs_ite_neg _ _ _ _ hc10 $$ Hpc\n"
x += "have hp2 : i + 2 < f.length := fmt_lt_of_ne f _ (by omega) (by rw [← hc1]; exact hc10)\n"
x += br(0x59a, False, 48, 21, 23, "BEQ", "hR23, ite_beq_zext_d", ind="")
x += "by_cases hd : c0 = chD\n"
x += "· " + indent("ihave Hpc := pcIs_ite_pos _ _ _ _ hd $$ Hpc\n" + d_arm("2", ""), 2).lstrip()
xn = "ihave Hpc := pcIs_ite_neg _ _ _ _ hd $$ Hpc\n"
xn += addi(0x59e, 14, 21, 3988, False, "", ind="") + sltiu(0x5a2, 14, 14, "sltiu_zext_l", ind="", gen=("14", "c0 = chL")) + addi(0x5a6, 12, 13, 3996, False, "", ind="")
xn += br(0x5aa, True, 56, 12, 0, "BNE", "ite_bne_sub_d", ind="")
xn += "by_cases hc1d : c1 = chD\n"
w = "ihave Hpc := pcIs_ite_pos _ _ _ _ hc1d $$ Hpc\n"
w += br(0x5ac, True, 54, 14, 0, "BEQ", "", ind="")
w += "ihave Hpc := pcIs_beq_bit _ _ _ _ _ hb14 $$ Hpc\n"
w += "by_cases hl : c0 = chL\n"
wl = "ihave Hpc := pcIs_ite_pos _ _ _ _ hl $$ Hpc\n"
wl += "have h' : pkRegs k.regs R ∧ R 9#5 = R 9#5 ∧ R 20#5 = R 20#5 ∧ R 21#5 = R 21#5 := ⟨hR, rfl, rfl, rfl⟩\n"
wl += kinds_num("by rw [hl, hc1d]; exact pkDir_ld (fmtByte f (i + 3))", 1, "").replace("c0 c1 c2 hc0 hc1 hc2", "c0 c1 (fmtByte f (i + 3)) hc0 hc1 rfl")
wl += arm_call("ld", "PI", "ld", "hp2 hkk hdlen hrest.symm", "")
w += "· " + indent(wl, 2).lstrip()
w += "· " + indent("ihave Hpc := pcIs_ite_neg _ _ _ _ hl $$ Hpc\n" + to_5e2("a", "(fun h => hl h.2)", ""), 2).lstrip()
xn += "· " + indent(w, 2).lstrip()
xn += "· " + indent("ihave Hpc := pcIs_ite_neg _ _ _ _ hc1d $$ Hpc\n" + to_5e2("b", "(fun h => hc1d h.1)", ""), 2).lstrip()
x += "· " + indent(xn, 2).lstrip()
n1 += "· " + indent(x, 2).lstrip()
t += "  · " + indent(n1, 4).lstrip()
out.append(t + "\n")

# ---- the turn ----
t = TURNHDR.format(DOC="One turn of the walk at `0x8000057c` (`a0 = f[i] ≠ 0`, `s4 = i`).", NAME="printk_turn",
  HYPS='''(hR10 : R 10#5 = BitVec.setWidth 64 (fmtByte f i))''', PC0=hx(0x57c))
t = t.replace("    (hi : i < f.length) (hp : fmtByte f i = chPct)\n", "    (hi : i < f.length)\n")
t += '''  by_cases hp : fmtByte f i = chPct
  · iapply (printk_pct CP PI cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf hflen hnonul hdlen hfmt i kk R w18
      hR hR20 hR10 hi hp hkinds) $$ [- ''' + STATE + ''' $Hcont]
    iframe #
  · ihave Hnext := pkCont_next _ _ _ _ _ _ _ _ _ _ $$ Hcont
    iapply (printk_arm_plain CP cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf hflen i kk R w18 hR hR20 hR10
      hi hp (by rw [← pkKinds_plain f i hi hp]; exact hkinds)) $$ [- ''' + STATE + ''' $Hnext]
    iframe #

'''
out.append(t)

# ---- the loop ----
t = '''set_option maxHeartbeats 4000000 in
/-- The walk from `0x8000056e` (`s1 = p`, the last consumed index): the
rest of the string, then the exit. -/
theorem printk_loop (CP : CONSPUTC) (PI : PRINTINT) (RE : RELEASE) {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]
    [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γpr γl : GName) (γd : UartNames) (bs0 : List (BitVec 8)) (dqf : DFrac)
    (f : List (BitVec 8)) (descs : List PkArgDesc)
    (hsie : k.sie = false) (htier : k.tier = KTier.bare) (hK : 48 ≤ k.avail) (hnoff : k.noff + 2 < 2 ^ 31)
    (hpr : "pr" ∉ k.locks) (huart : "uart" ∉ k.locks) (hwf : k.wf) (hf : stackFacts (k.regs 2#5) k.avail)
    (hflen : f.length + 4 < 2 ^ 31) (hnonul : nonul f) (hdlen : descs.length ≤ 7)
    (hfmt : inRam (k.regs 10#5) (f.length + 1)) (n : Nat) :
    ∀ (p kk : Nat) (R : RegMap) (w18 : BitVec 64) (cs0 : List (BitVec 8)), f.length - p ≤ n → p < f.length →
    pkRegs k.regs R → R 9#5 = BitVec.ofNat 64 p → pkKinds (f.drop (p + 1)) = (descs.drop kk).map PkArgDesc.kind →
    printkText ∗ kernelText ∗ kernelData ∗ isTxLock γl γd ∗ isLock γpr prLock "pr" (fun _ => emp) ∗
    kctx cpu ((pkBase k).withRegs R) ∗ clockCells cpu ∗ pcIs cpu 0x8000056e#64 ∗
    byteBuf (k.regs 10#5) dqf (f ++ [0#8]) ∗ pkDescs k.regs descs ∗
    pkFrame (k.regs 2#5) k.regs (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 kk) w18 ∗
    uartSentSub γd (bs0 ++ cs0) ∗ locked γpr cpu ∗ pkPost cpu k γd bs0 dqf f descs
    ⊢ wpLoop (GF := GF) cpu := by
  induction n with
  | zero =>
    intro p kk R w18 cs0 hn hp
    exact absurd hn (by omega)
  | succ n ih =>
    intro p kk R w18 cs0 hn hp hR hR9 hkinds
    iintro ⟨#HT, #Htext, #HD, #Htx, #Hlk, Hk, Hclock, Hpc, Hbuf, Hdescs, Hframe, Hsent, Hlocked, HΦ⟩
    have hf24 : stackFacts (k.regs 2#5) 24 := stackFacts_mono hf (by omega)
    have hR18 : R 18#5 = k.regs 10#5 := hR.1.2.2.1
'''
t += facts([0x56e, 0x570, 0x572, 0x574, 0x578], ind="    ")
t += '''    -- addiw s1,s1,1 ; mv s4,s1 ; add s1,s2,s1
    k_step (wp_s_addiw cpu _ ?hs ?ht 0x8000056e#64 true 1#12 9#5 9#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
      with [hR9, addiw_succ p (by omega)]
    iintro Hk Hclock Hpc
'''
t += mv(0x570, 20, 9, True, ind="    ") + add(0x572, 9, 9, 18, True, "hR18, BitVec.add_comm (BitVec.ofNat 64 (p + 1)) (k.regs 10#5)", ind="    ")
t += '''    -- lbu a0,0(s1)
    have hb : (f ++ [0#8])[p + 1]? = some (fmtByte f (p + 1)) := fmtByte_get f (p + 1) (by omega)
    icases byteBuf_acc _ dqf _ (p + 1) _ hb $$ Hbuf with ⟨Hb, Hclose⟩
    k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000574#64 false 0#12 10#5 9#5 (by decide) dqf (fmtByte f (p + 1)) ?hram)
      $$ [- $Hk $Hclock $Hpc]
    case hram => k_norm; exact inRam_byte hfmt (p + 1) (by omega)
    iintro Hk Hclock Hpc Hb
    ihave Hbuf := Hclose $$ Hb
'''
t += br(0x578, False, 460, 10, 0, "BEQ", "ite_beq_byte", ind="    ")
t += '''    by_cases hz : fmtByte f (p + 1) = 0#8
    · ihave Hpc := pcIs_ite_pos _ _ _ _ hz $$ Hpc
      iapply (printk_exit RE cpu k γpr γd bs0 cs0 dqf f descs hsie htier hK hpr hwf hf 0x80000744#64 (Or.inl rfl) _ ?HRe _ w18)
        $$ [- $Hk $Hclock $Hpc $Hlocked $Hframe $Hbuf $Hdescs $Hsent $HΦ]
      rotate_right 1
      iframe #
      case HRe => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
    ihave Hpc := pcIs_ite_neg _ _ _ _ hz $$ Hpc
    have hlt : p + 1 < f.length := fmt_lt_of_ne f (p + 1) (by omega) hz
    iapply (printk_turn CP PI cpu k γpr γl γd (bs0 ++ cs0) dqf f descs hsie htier hK hnoff huart hf24 hflen hnonul hdlen hfmt
      (p + 1) kk _ w18 ?HRt ?H20t ?H10t hlt hkinds) $$ [- ''' + STATE + ''']
    rotate_right 1
    iframe #
    case HRt => repeat (first | exact hR | refine pkRegs_set _ _ _ _ ?_ (by decide))
    case H20t => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
    case H10t => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
    isplit
    · -- back at 0x56e
      iintro %R' %p' %kk' %cs %w18' Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked %h'
      ihave Hsent := (show uartSentSub γd (bs0 ++ cs0 ++ cs) ⊢ uartSentSub γd (bs0 ++ (cs0 ++ cs)) from
        by rw [List.append_assoc]) $$ Hsent
      iapply (ih p' kk' R' w18' (cs0 ++ cs) (by omega) h'.2.2.2.1 h'.1 h'.2.1 h'.2.2.2.2)
        $$ [- $Hk $Hclock $Hpc $Hbuf $Hdescs $Hframe $Hsent $Hlocked $HΦ]
      iframe #
    · -- a `%` ended the string
      iintro %R' %w18' Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked %h'
      iapply (printk_exit RE cpu k γpr γd bs0 cs0 dqf f descs hsie htier hK hpr hwf hf 0x80000800#64 (Or.inr rfl) R' h' _ w18')
        $$ [- $Hk $Hclock $Hpc $Hlocked $Hframe $Hbuf $Hdescs $Hsent $HΦ]
      iframe #

'''
out.append(t)

# ---- the entry ----
def sd(pc, rvc, imm, rs1, rs2, old, lem, slot, ind="  "):
    w = f" with [{lem}]" if lem else ""
    return (f"{ind}k_step (wp_s_sd cpu _ ?hs ?ht {hx(pc)} {str(rvc).lower()} {imm}#12 {rs1}#5 {rs2}#5 {old} ?hram ?hal) $$ [- $Hk $Hclock $Hpc]{w}\n"
            f"{ind}case hram => k_norm [{lem}]; exact (slot{slot}_ok _ hf24).1\n{ind}case hal => k_norm [{lem}]; exact (slot{slot}_ok _ hf24).2\n"
            f"{ind}iintro Hk Hclock Hpc {old}\n")
t = '''set_option maxHeartbeats 4000000 in
/-- **`printk` meets its specification**, given `acquire`, `release`,
`consputc` and `printint`. -/
theorem printk_proof (AC : ACQUIRE) (RE : RELEASE) (CP : CONSPUTC) (PI : PRINTINT) : PRINTK :=
  ⟨fun {hlc GF} _ _ _ cpu k γpr γl γd bs dqf f descs hsie htier hK hflen hnonul hkinds hdlen hnoff hpr huart hfmt => by
  unfold wp_printk_body
  simp only [printkAddr, KernelSyms.«printk»]
  rw [hsie]
  iintro ⟨Hk, #Htext, #HD, Hclock, Hpc, Hbuf, Hdescs, #Hlk, #Htx, Hsent, Hnext⟩
  ihave HΦ := wpNext_off _ _ _ $$ Hnext
  ihave #HT := kernelText_printk $$ Htext
  icases kctx_wf _ _ $$ Hk with ⟨%hwf, Hk⟩
  icases kctx_stackFacts _ _ $$ Hk with ⟨%hf0, Hk⟩
  have hf : stackFacts (k.regs 2#5) k.avail := by rw [hsie, trapRes_off] at hf0; exact hf0
  have hf24 : stackFacts (k.regs 2#5) 24 := stackFacts_mono hf (by omega)
  have hnoff1 : k.noff + 1 < 2 ^ 31 := by omega
  have hi0 : 0 < f.length ∨ f.length = 0 := by omega
'''
t += facts([0x502, 0x504, 0x506, 0x508, 0x50a, 0x50c, 0x50e, 0x510, 0x512, 0x514, 0x516, 0x518, 0x51c, 0x520, 0x524,
            0x528, 0x52c, 0x530, 0x534, 0x538, 0x53c, 0x53e, 0x540, 0x542, 0x544, 0x546, 0x548, 0x54a, 0x54c,
            0x54e, 0x550, 0x554, 0x558, 0x55c, 0x560, 0x562, 0x566])
t += '''  -- addi sp,sp,-192
  k_step (wp_s_push cpu _ ?hs ?ht 0x80000502#64 true 3904#12 24 (by omega) imm_m192) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc Hstk
  icases stackOwn_24_cases _ $$ Hstk with ⟨%_, %w0, %w1, %w2, %w3, %w4, %w5, %w6, %w7, %w8, %w9, %w10, %w11, %w12, %w13,
    %w14, %w15, %w16, %w17, %w18, %w19, %w20, %w21, %w22, %w23, C0, C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12,
    C13, C14, C15, C16, C17, C18, C19, C20, C21, C22, C23⟩
'''
t += sd(0x504, True, 120, 2, 1, "w8", "", 72).replace("k_norm []", "k_norm").replace("C8", "C8")
t = t.replace("iintro Hk Hclock Hpc w8\n", "iintro Hk Hclock Hpc C8\n")
t += sd(0x506, True, 112, 2, 8, "w9", "", 80).replace("iintro Hk Hclock Hpc w9\n", "iintro Hk Hclock Hpc C9\n")
t += sd(0x508, True, 96, 2, 18, "w11", "", 96).replace("iintro Hk Hclock Hpc w11\n", "iintro Hk Hclock Hpc C11\n")
t = t.replace("k_norm []", "k_norm")
t += addi(0x50a, 8, 2, 128, True, "") + mv(0x50c, 18, 10, True)
for (pc, imm, reg, w, slot, rvc) in [(0x50e, 8, 11, 6, 56, True), (0x510, 16, 12, 5, 48, True), (0x512, 24, 13, 4, 40, True),
                                     (0x514, 32, 14, 3, 32, True), (0x516, 40, 15, 2, 24, True), (0x518, 48, 16, 1, 16, False), (0x51c, 56, 17, 0, 8, False)]:
    t += sd(pc, rvc, imm, 8, reg, f"w{w}", "", slot).replace(f"iintro Hk Hclock Hpc w{w}\n", f"iintro Hk Hclock Hpc C{w}\n").replace("k_norm []", "k_norm")
t += '''  -- a0 = &pr.lock ; jal acquire
  k_step (wp_s_auipc cpu _ ?hs ?ht 0x80000520#64 false 18#20 10#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
  iintro Hk Hclock Hpc
  k_step (wp_s_addi cpu _ ?hs ?ht 0x80000524#64 false 3608#12 10#5 10#5 (by decide)) $$ [- $Hk $Hclock $Hpc]
    with [pr_addr_520]
  iintro Hk Hclock Hpc
  k_step (wp_s_jal cpu _ ?hs ?ht 0x80000528#64 false 1682#21 1#5 (by decide) ?htgt) $$ [- $Hk $Hclock $Hpc]
  case htgt => k_tgt
  iintro Hk Hclock Hpc
  have hac : ∀ (k' : KCtx) (hsie' : k'.sie = false) (htier' : k'.tier = KTier.bare) (hnoff' : k'.noff + 1 < 2 ^ 31)
      (hK' : 10 ≤ k'.avail) (hs' : "pr" ∉ k'.locks),
      kctx cpu k' ∗ kernelText ∗ clockCells cpu ∗ pcIs cpu 0x80000bba#64 ∗ isLock γpr (k'.regs 10#5) "pr" (fun _ => emp) ∗
      (∀ R' : RegMap, kctx cpu ((k'.pushOff.withRegs R').withLocks ("pr" :: k'.locks)) -∗ clockCells cpu -∗
        pcIs cpu (retPc (k'.regs 1#5)) -∗ ⌜calleeSaved k'.regs R'⌝ -∗ locked γpr cpu -∗ wpLoop cpu)
      ⊢ wpLoop (GF := GF) cpu := by
    intro k' hsie' htier' hnoff' hK' hs'
    have h := AC.wp_acquire (hlc := hlc) (GF := GF) cpu k' γpr "pr" (fun _ => emp) hsie' htier' hnoff' hK' hs'
    unfold wp_acquire_body at h
    simp only [acquireAddr, KernelSyms.«acquire»] at h
    iintro ⟨Hk, #HT, Hc, Hp, #Hl, Hcont⟩
    iapply h
    iframe Hk Hc Hp
    iframe #
    rw [hsie']
    iapply wpNext_off_intro
    iintro %R' Hk Hc Hp %hcs Hlo _ _
    iapply Hcont $$ %_ Hk Hc Hp %hcs Hlo
  ihave #Hlk' := (show isLock γpr prLock "pr" (fun _ => emp) ⊢ isLock (GF := GF) γpr 0x80012338#64 "pr" (fun _ => emp)
    from by rw [show prLock = 0x80012338#64 from rfl]) $$ Hlk
  iapply (hac _ ?hs ?ht ?hn ?hK ?hl) $$ [- $Hk $Hclock $Hpc]
  rotate_right 1
  k_norm
  iframe #
  case hs => k_norm
  case ht => k_norm
  case hn => k_norm; omega
  case hK => k_norm; omega
  case hl => k_norm; exact hpr
  iintro %R2 Hk Hclock Hpc %hcs2 Hlocked
  unfold calleeSaved at hcs2
  k_norm at hcs2
  k_norm [ret_52c]
  obtain ⟨h2_2, h2_8, h2_9, h2_18, h2_19, h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27⟩ := hcs2
  -- a5 = s0 + 8 ; the va_list slot
  k_step (wp_s_addi cpu _ ?hs ?ht 0x8000052c#64 false 8#12 15#5 8#5 (by decide)) $$ [- $Hk $Hclock $Hpc] with [h2_8]
  iintro Hk Hclock Hpc
  k_step (wp_s_sd cpu _ ?hs ?ht 0x80000530#64 false 3976#12 8#5 15#5 w22 ?hram ?hal) $$ [- $Hk $Hclock $Hpc] with [h2_8]
  case hram => k_norm [h2_8]; exact (slot184_ok _ hf24).1
  case hal => k_norm [h2_8]; exact (slot184_ok _ hf24).2
  iintro Hk Hclock Hpc C22
  -- lbu a0,0(s2): the first byte
  have hb0 : (f ++ [0#8])[0]? = some (fmtByte f 0) := fmtByte_get f 0 (Nat.zero_le _)
  icases byteBuf_acc0 _ dqf _ _ hb0 $$ Hbuf with ⟨Hb, Hclose⟩
  k_step (wp_s_lbu cpu _ ?hs ?ht 0x80000534#64 false 0#12 10#5 18#5 (by decide) dqf (fmtByte f 0) ?hram)
    $$ [- $Hk $Hclock $Hpc] with [h2_18]
  case hram => k_norm [h2_18]; simpa using inRam_byte hfmt 0 (by omega)
  iintro Hk Hclock Hpc Hb
  ihave Hbuf := Hclose $$ Hb
'''
t += br(0x538, False, 542, 10, 0, "BEQ", "ite_beq_byte")
t += '''  by_cases h0 : fmtByte f 0 = 0#8
  · -- the empty format: release and return
    ihave Hpc := pcIs_ite_pos _ _ _ _ h0 $$ Hpc
    ihave Hexit := pkFrameExit_intro (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 18#5)
      (k.regs 17#5) (k.regs 16#5) (k.regs 15#5) (k.regs 14#5) (k.regs 13#5) (k.regs 12#5) (k.regs 11#5) w7
      w10 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 (k.regs 2#5 + 0xFFFFFFFFFFFFFFC8#64) w23
      $$ [C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23]
    case' _ => iframe
    iapply (printk_release_tail RE cpu k γpr hsie htier hK hpr hwf hf _ ?hR2 ?hcs) $$ [- $Hk $Hclock $Hpc $Hlocked $Hexit]
    rotate_right 1
    iframe #
    case hR2 => simp only [RegMap.set_apply, BitVec.reduceEq, if_false]; exact h2_2
    case hcs =>
      simp only [RegMap.set_apply, BitVec.reduceEq, if_false]
      exact ⟨h2_9, h2_19, h2_20, h2_21, h2_22, h2_23, h2_24, h2_25, h2_26, h2_27⟩
    iintro %R' Hk Hclock Hpc %h
    ihave Hsent := (show uartSentSub γd bs ⊢ uartSentSub γd (bs ++ []) from by rw [List.append_nil]) $$ Hsent
    iapply HΦ $$ %_ %([]) Hk Hclock Hpc %h Hbuf Hdescs Hsent
  ihave Hpc := pcIs_ite_neg _ _ _ _ h0 $$ Hpc
  have hi : 0 < f.length := fmt_lt_of_ne f 0 (Nat.zero_le _) h0
'''
for (pc, imm, reg, cell, slot, hh) in [(0x53c, 104, 9, 10, 88, "h2_9"), (0x53e, 88, 19, 12, 104, "h2_19"), (0x540, 80, 20, 13, 112, "h2_20"),
                                       (0x542, 72, 21, 14, 120, "h2_21"), (0x544, 64, 22, 15, 128, "h2_22"), (0x546, 56, 23, 16, 136, "h2_23"),
                                       (0x548, 48, 24, 17, 144, "h2_24"), (0x54a, 32, 26, 19, 160, "h2_26"), (0x54c, 24, 27, 20, 168, "h2_27")]:
    t += sd(pc, True, imm, 2, reg, f"w{cell}", f"h2_2, {hh}", slot).replace(f"iintro Hk Hclock Hpc w{cell}\n", f"iintro Hk Hclock Hpc C{cell}\n")
t += li(0x54e, 20, 0, True) + li(0x550, 19, 37, False) + li(0x554, 24, 117, False) + li(0x558, 26, 120, False) + li(0x55c, 27, 112, False)
t += li(0x560, 22, 10, True) + li(0x562, 23, 100, False)
t += jmp(0x566, 22, True)
t += '''  -- the frame
  ihave Hframe := pkFrame_intro (k.regs 2#5) k.regs (k.regs 2#5 + 0xFFFFFFFFFFFFFFC8#64) w7 w18 w21 w23
    $$ [C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23]
  case' _ => iframe
  ihave Hframe := (show pkFrame (k.regs 2#5) k.regs (k.regs 2#5 + 0xFFFFFFFFFFFFFFC8#64) w18 ⊢
    pkFrame (GF := GF) (k.regs 2#5) k.regs (pkApBase (k.regs 2#5) + 8#64 * BitVec.ofNat 64 0) w18 from
    by simp [pkApBase]) $$ Hframe
  -- the walk
  iapply (printk_turn CP PI cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff huart hf24 hflen hnonul hdlen hfmt 0 0 _ w18
    ?HR ?H20 ?H10 hi (by simpa using hkinds)) $$ [- ''' + STATE + ''']
  rotate_right 1
  iframe #
  case HR =>
    unfold pkRegs pkRegsN pkConsts
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true, and_true, true_and]
    exact ⟨⟨h2_2, h2_8, h2_18⟩, h2_25⟩
  case H20 => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
  case H10 => simp only [RegMap.set_apply, BitVec.reduceEq, if_false, if_true]
  isplit
  · iintro %R' %p' %kk' %cs %w18' Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked %h'
    iapply (printk_loop CP PI RE cpu k γpr γl γd bs dqf f descs hsie htier hK hnoff hpr huart hwf hf hflen hnonul hdlen hfmt
      f.length p' kk' R' w18' cs (by omega) h'.2.2.2.1 h'.1 h'.2.1 h'.2.2.2.2)
      $$ [- $Hk $Hclock $Hpc $Hbuf $Hdescs $Hframe $Hsent $Hlocked $HΦ]
    iframe #
  · iintro %R' %w18' Hk Hclock Hpc Hbuf Hdescs Hframe Hsent Hlocked %h'
    ihave Hsent := (show uartSentSub γd bs ⊢ uartSentSub γd (bs ++ []) from by rw [List.append_nil]) $$ Hsent
    iapply (printk_exit RE cpu k γpr γd bs [] dqf f descs hsie htier hK hpr hwf hf 0x80000800#64 (Or.inr rfl) R' h' _ w18')
      $$ [- $Hk $Hclock $Hpc $Hlocked $Hframe $Hbuf $Hdescs $Hsent $HΦ]
    iframe #⟩

'''
out.append(t)

import sys
open(sys.argv[1], 'w').write("".join(out))
