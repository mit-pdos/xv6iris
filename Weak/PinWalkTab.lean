/-
Weak: **W9a (B) B5 — the GENERATED walk-state table and psitesA's per-state content** (plan
`notes/weak-allocproc-plan.md` rev 52 §C "W9a (B)", "(B5) assembly": "the per-state table of the
1,631 walk states GENERATED (untrusted generator + `decide +kernel` check, the B2 pattern)";
[OWN.60], [OWN.68], [OWN.75]).  Lean-only, no Rocq twin.

**The table** (`walkRows`, between the GENERATED markers; `tools/gen_weak_walktab.py --emit`,
`--check`): for each of the 469 walk-certifying rows of B3's claimed pin set `pinsW9a`, in table
order, the load pc, the row's `own` bit and the states the all-paths search `pdfs` visits from
`pinStart` — 1,559 states, 1,031 distinct pcs (the spike's "1,631" counted the pin instructions
of all 470 rows).  UNTRUSTED: the generator only proposes the lists; the reflection lemmas below
re-check them through the merged Lean definitions (`pstep`, `pinStart`, `krole`, `kflowOf`) and
the Sail model's own decoder (`ext_decode` / `ext_decode_compressed`, evaluated by the kernel on
the supervisor-mode reference configuration `drefS`, `MachCSL/DecodeBridge.lean`, as
`Weak/KernelSites.lean` does):

  * `walkRowsCover` — the rows are EXACTLY the walk-certifying rows of `pinsW9a` (pc, `own`);
  * `walkRowsOk` (`rowOk` per row) — each list contains the row's `pinStart`, is CLOSED under
    `pstep`'s successors (so it contains every state `preach` reaches: `walkReach`), and every
    state passes `stOk`:
      - the taint avoids `stimecmp` (`presOkb`: every tainted register is in `presRegs`) — the
        census-decidable conjunct (i) of B2's `texcFree` (`walkPres`);
      - at a NON-pin state: the instruction's four bytes lie in the text (B4's arms,
        `walkText`); the decoded instruction (`decS`) passes B1's per-word check extended by the
        pure CSR reads (`dfInstrOkB5`, `Weak/PinDataflowSatp.lean`: `csrr satp`, `rdtime` —
        the only two words B1's check rejects, one walk state and one census state) — the
        per-state content of `psitesA`'s per-instruction dataflow (`walkDec`); the decoded
        instruction's CONTROL CLASS is the checker's (`astFlow pc ast = kflowOf pc`: branch and
        jump targets, call vs jump, `ret` vs indirect — the static half of the next-pc
        alignment, `walkFlow`); every successor's taint is below the decoded update
        (`taintSubb`, `reachesA`'s `taintSub` obligation, `walkTaint`).

**The census states** (`trapDecOk`): at every fence-free trap-path state of B2's carry table
(`PinTrapSites.trapFlow`, 383 states), the decoded instruction passes the same per-word check —
the per-state content of `texcM`'s `grpOkb` obligation.

Spec: the decoder is Sail's (`LeanRV64D` `ext_decode`); the checks are proof organisation.  The
supervisor-mode reference configuration (`cur_privilege = S`, `misa`, the kernel's `menvcfg`,
`mseccfg = 0`) is the kernel's (`MachCSL.decodesAll32`'s S-mode half); that the RUN's decode
reads these values is part of the cycle alignment (`Weak/WeakRvwmoPinBridge5.lean`, r4), not of
this file.  FAITHFUL.  Every helper is `Weak.PinWalkTab.*`.
-/
import Weak.PinDataflowSatp
import Weak.WeakRvwmoPinBridge4
import Weak.PinTrapSites
import MachCSL.DecodeBridge

namespace Weak

open MachCSL KernelPinsDef LeanRV64D
open WeakRvwmoPinBridge3 (preach)
open WeakRvwmoPinBridge4 (walkOwn)
open PinTrapSites

-- The decoder's walk reads the platform configuration (see `Xv6/CodeTactics.lean`).
attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

namespace PinWalkTab

/-! ## 1. The per-state checks -/

/-- THE DECODED INSTRUCTION at a text pc: Sail's decoder on the fetched word (the low half for a
compressed word), on the supervisor-mode reference configuration. -/
noncomputable def decS (pc : Int) : Option instruction :=
  let w := kw pc
  let r := if wIsRvc w then
      runRead drefS (LeanRV64D.Functions.ext_decode_compressed (BitVec.ofNat 16 w))
    else runRead drefS (LeanRV64D.Functions.ext_decode (BitVec.ofNat 32 w))
  match r with
  | some (a, _) => some a
  | none => none

/-- B1's per-word check (with the `satp` read) at the decoded instruction. -/
noncomputable def decOk (pc : Int) : Bool :=
  match decS pc with
  | some a => PinDataflow.dfInstrOkB5 (krole pc) a
  | none => false

/-- THE CONTROL CLASS of a decoded instruction at `pc`, in the checker's vocabulary: the
targets as Sail's `execute` computes them (`PC + sign_extend imm`; the compressed forms through
their `ExecuteAs` targets, `InstsEnd.lean`), a call iff the link register is not `x0`, `ret` iff
`jalr x0, 0(ra)`, every other register-indirect transfer and every trap/return instruction
indirect. -/
def astFlow (pc : Int) : instruction → Kflow
  | .BTYPE (imm, _, _, _) => .FLbranch (pc + imm.toInt)
  | .JAL (imm, regidx.Regidx rd) =>
      if rd = 0#5 then .FLjump (pc + imm.toInt) else .FLcall (pc + imm.toInt)
  | .JALR (imm, regidx.Regidx rs1, regidx.Regidx rd) =>
      if rd = 0#5 ∧ rs1 = 1#5 ∧ imm = 0#12 then .FLret else .FLind
  | .C_J imm => .FLjump (pc + (BitVec.signExtend 21 (imm ++ 0#1)).toInt)
  | .C_BEQZ (imm, _) => .FLbranch (pc + (BitVec.signExtend 13 (imm ++ 0#1)).toInt)
  | .C_BNEZ (imm, _) => .FLbranch (pc + (BitVec.signExtend 13 (imm ++ 0#1)).toInt)
  | .C_JR (regidx.Regidx rs1) => if rs1 = 1#5 then .FLret else .FLind
  | .C_JALR _ => .FLind
  | .ECALL _ | .MRET _ | .SRET _ | .EBREAK _ | .C_EBREAK _ => .FLind
  | _ => .FLnone

/-- The decoded instruction's control class is the checker's. -/
noncomputable def ctlOk (pc : Int) : Bool :=
  match decS pc with
  | some a => astFlow pc a == kflowOf pc
  | none => false

/-- `taintSub`, decided. -/
def taintSubb (t t' : List Nat) : Bool := t.all (fun r => taintMem r t')

/-- The taint avoids `stimecmp` (B2's `presRegs`). -/
def presOkb (t : List Nat) : Bool := t.all (fun r => presRegs.contains r)

/-- THE PER-STATE CHECK. -/
noncomputable def stOk (own : Bool) (s : PState) : Bool :=
  presOkb s.psT &&
    match pstep own s with
    | none => false
    | some [] => true
    | some l => decide (textLo ≤ s.psPc) && decide (s.psPc + 3 < textHi) &&
        decOk s.psPc && ctlOk s.psPc &&
        l.all (fun s' => taintSubb s'.psT (taintStep s.psT s.psPc))

/-- One row of the table. -/
structure WRow where
  WR ::
  wPc : Int
  wOwn : Bool
  wSts : List PState

/-- Closure of a state list under `pstep`'s successors, at one state. -/
def closedb (own : Bool) (sts : List PState) (s : PState) : Bool :=
  match pstep own s with
  | some l => l.all (fun s' => sts.any (pstateEqb s'))
  | none => false

/-- THE ROW CHECK: the start state is listed, the list is closed, every state passes `stOk`. -/
noncomputable def rowOk (r : WRow) : Bool :=
  r.wSts.any (pstateEqb (pinStart r.wPc)) &&
    r.wSts.all (fun s => stOk r.wOwn s && closedb r.wOwn r.wSts s)

end PinWalkTab

open PinWalkTab

/-! ## 2. The table -/

-- BEGIN GENERATED (tools/gen_weak_walktab.py --emit)
def walkRows0 : List WRow := [
  ⟨0x800001b6, false, [PState.PSt 0x800001ba [15] [], PState.PSt 0x800001be [15] []]⟩,
  ⟨0x800001ba, false, [PState.PSt 0x800001be [14] []]⟩,
  ⟨0x800001e2, false, [PState.PSt 0x800001e6 [15] [], PState.PSt 0x800001ea [15] []]⟩,
  ⟨0x800001e6, false, [PState.PSt 0x800001ea [14] []]⟩,
  ⟨0x80000206, false, [PState.PSt 0x8000020a [14] [], PState.PSt 0x8000020e [21, 14] [], PState.PSt 0x80000210 [21, 14] []]⟩,
  ⟨0x800002fe, false, [PState.PSt 0x80000302 [15] [], PState.PSt 0x80000306 [15] [], PState.PSt 0x80000308 [15] [], PState.PSt 0x8000030c [15] []]⟩,
  ⟨0x80000302, false, [PState.PSt 0x80000306 [14] [], PState.PSt 0x80000308 [15, 14] [], PState.PSt 0x8000030c [15] []]⟩,
  ⟨0x80000324, false, [PState.PSt 0x80000328 [13] [], PState.PSt 0x8000032c [15, 13] [], PState.PSt 0x8000032e [12, 15, 13] []]⟩,
  ⟨0x8000034a, false, [PState.PSt 0x8000034e [14] [], PState.PSt 0x80000350 [15, 14] [], PState.PSt 0x80000354 [15] []]⟩,
  ⟨0x80000366, false, [PState.PSt 0x8000036a [15] [], PState.PSt 0x8000036e [15] [], PState.PSt 0x80000372 [15] [], PState.PSt 0x80000376 [15] [], PState.PSt 0x80000378 [15] [], PState.PSt 0x8000037c [15] []]⟩,
  ⟨0x8000036a, false, [PState.PSt 0x8000036e [14] [], PState.PSt 0x80000372 [14] [], PState.PSt 0x80000376 [14] [], PState.PSt 0x80000378 [14] [], PState.PSt 0x8000037c [14] []]⟩,
  ⟨0x80000388, false, [PState.PSt 0x8000038c [14] []]⟩,
  ⟨0x8000039a, false, [PState.PSt 0x8000039e [15] [], PState.PSt 0x800003a2 [15] []]⟩,
  ⟨0x8000039e, false, [PState.PSt 0x800003a2 [14] []]⟩,
  ⟨0x800003c0, false, [PState.PSt 0x800003c4 [15] [], PState.PSt 0x800003c8 [15] []]⟩,
  ⟨0x800003c4, false, [PState.PSt 0x800003c8 [14] []]⟩,
  ⟨0x80000404, false, [PState.PSt 0x80000408 [14] [], PState.PSt 0x8000040c [13, 14] [], PState.PSt 0x8000040e [12, 13, 14] []]⟩,
  ⟨0x800004c0, false, [PState.PSt 0x800004c4 [15] []]⟩,
  ⟨0x80000558, false, [PState.PSt 0x8000055c [10] []]⟩,
  ⟨0x80000598, false, [PState.PSt 0x8000059c [10] []]⟩,
  ⟨0x800005ae, false, [PState.PSt 0x800005b2 [21] []]⟩,
  ⟨0x800005b6, false, [PState.PSt 0x800005ba [13] []]⟩,
  ⟨0x800005d2, false, [PState.PSt 0x800005d6 [15] [], PState.PSt 0x800005da [14, 15] []]⟩,
  ⟨0x800005e2, true, [PState.PSt 0x800005e4 [10] [], PState.PSt 0x80000490 [10] [0x800005e8], PState.PSt 0x80000492 [10] [0x800005e8], PState.PSt 0x80000494 [10] [0x800005e8], PState.PSt 0x80000496 [10] [0x800005e8], PState.PSt 0x80000498 [10] [0x800005e8], PState.PSt 0x8000049a [10] [0x800005e8], PState.PSt 0x8000049c [10] [0x800005e8], PState.PSt 0x800004a0 [10] [0x800005e8], PState.PSt 0x800004a2 [10] [0x800005e8], PState.PSt 0x800004a6 [10] [0x800005e8], PState.PSt 0x800004a8 [10] [0x800005e8], PState.PSt 0x800004aa [10] [0x800005e8], PState.PSt 0x800004ae [10] [0x800005e8], PState.PSt 0x800004b2 [10] [0x800005e8], PState.PSt 0x800004b4 [10] [0x800005e8], PState.PSt 0x800004b8 [10] [0x800005e8], PState.PSt 0x800004ba [10] [0x800005e8], PState.PSt 0x800004be [15, 10] [0x800005e8], PState.PSt 0x800004c0 [15, 10] [0x800005e8], PState.PSt 0x800004c4 [15, 10] [0x800005e8]]⟩,
  ⟨0x800005ee, false, [PState.PSt 0x800005f2 [15] [], PState.PSt 0x800005f6 [14, 15] []]⟩,
  ⟨0x800005fe, true, [PState.PSt 0x80000600 [10] [], PState.PSt 0x80000490 [10] [0x80000604], PState.PSt 0x80000492 [10] [0x80000604], PState.PSt 0x80000494 [10] [0x80000604], PState.PSt 0x80000496 [10] [0x80000604], PState.PSt 0x80000498 [10] [0x80000604], PState.PSt 0x8000049a [10] [0x80000604], PState.PSt 0x8000049c [10] [0x80000604], PState.PSt 0x800004a0 [10] [0x80000604], PState.PSt 0x800004a2 [10] [0x80000604], PState.PSt 0x800004a6 [10] [0x80000604], PState.PSt 0x800004a8 [10] [0x80000604], PState.PSt 0x800004aa [10] [0x80000604], PState.PSt 0x800004ae [10] [0x80000604], PState.PSt 0x800004b2 [10] [0x80000604], PState.PSt 0x800004b4 [10] [0x80000604], PState.PSt 0x800004b8 [10] [0x80000604], PState.PSt 0x800004ba [10] [0x80000604], PState.PSt 0x800004be [15, 10] [0x80000604], PState.PSt 0x800004c0 [15, 10] [0x80000604], PState.PSt 0x800004c4 [15, 10] [0x80000604]]⟩,
  ⟨0x8000060a, false, [PState.PSt 0x8000060e [13] [], PState.PSt 0x800007b0 [13] [], PState.PSt 0x800007b4 [13] [], PState.PSt 0x800007b8 [13] [], PState.PSt 0x800007ba [13] [], PState.PSt 0x800007be [11, 13] []]⟩,
  ⟨0x80000610, false, [PState.PSt 0x80000614 [15] [], PState.PSt 0x80000618 [14, 15] []]⟩,
  ⟨0x80000620, true, [PState.PSt 0x80000622 [10] [], PState.PSt 0x80000490 [10] [0x80000626], PState.PSt 0x80000492 [10] [0x80000626], PState.PSt 0x80000494 [10] [0x80000626], PState.PSt 0x80000496 [10] [0x80000626], PState.PSt 0x80000498 [10] [0x80000626], PState.PSt 0x8000049a [10] [0x80000626], PState.PSt 0x8000049c [10] [0x80000626], PState.PSt 0x800004a0 [10] [0x80000626], PState.PSt 0x800004a2 [10] [0x80000626], PState.PSt 0x800004a6 [10] [0x80000626], PState.PSt 0x800004a8 [10] [0x80000626], PState.PSt 0x800004aa [10] [0x80000626], PState.PSt 0x800004ae [10] [0x80000626], PState.PSt 0x800004b2 [10] [0x80000626], PState.PSt 0x800004b4 [10] [0x80000626], PState.PSt 0x800004b8 [10] [0x80000626], PState.PSt 0x800004ba [10] [0x80000626], PState.PSt 0x800004be [15, 10] [0x80000626], PState.PSt 0x800004c0 [15, 10] [0x80000626], PState.PSt 0x800004c4 [15, 10] [0x80000626]]⟩,
  ⟨0x8000062c, false, [PState.PSt 0x80000630 [15] [], PState.PSt 0x80000634 [14, 15] []]⟩,
  ⟨0x8000063c, true, [PState.PSt 0x80000640 [10] [], PState.PSt 0x80000490 [10] [0x80000644], PState.PSt 0x80000492 [10] [0x80000644], PState.PSt 0x80000494 [10] [0x80000644], PState.PSt 0x80000496 [10] [0x80000644], PState.PSt 0x80000498 [10] [0x80000644], PState.PSt 0x8000049a [10] [0x80000644], PState.PSt 0x8000049c [10] [0x80000644], PState.PSt 0x800004a0 [10] [0x80000644], PState.PSt 0x800004a2 [10] [0x80000644], PState.PSt 0x800004a6 [10] [0x80000644], PState.PSt 0x800004a8 [10] [0x80000644], PState.PSt 0x800004aa [10] [0x80000644], PState.PSt 0x800004ae [10] [0x80000644], PState.PSt 0x800004b2 [10] [0x80000644], PState.PSt 0x800004b4 [10] [0x80000644], PState.PSt 0x800004b8 [10] [0x80000644], PState.PSt 0x800004ba [10] [0x80000644], PState.PSt 0x800004be [15, 10] [0x80000644], PState.PSt 0x800004c0 [15, 10] [0x80000644], PState.PSt 0x800004c4 [15, 10] [0x80000644]]⟩,
  ⟨0x80000646, false, [PState.PSt 0x8000064a [15] [], PState.PSt 0x8000064e [14, 15] []]⟩,
  ⟨0x80000656, true, [PState.PSt 0x80000658 [10] [], PState.PSt 0x80000490 [10] [0x8000065c], PState.PSt 0x80000492 [10] [0x8000065c], PState.PSt 0x80000494 [10] [0x8000065c], PState.PSt 0x80000496 [10] [0x8000065c], PState.PSt 0x80000498 [10] [0x8000065c], PState.PSt 0x8000049a [10] [0x8000065c], PState.PSt 0x8000049c [10] [0x8000065c], PState.PSt 0x800004a0 [10] [0x8000065c], PState.PSt 0x800004a2 [10] [0x8000065c], PState.PSt 0x800004a6 [10] [0x8000065c], PState.PSt 0x800004a8 [10] [0x8000065c], PState.PSt 0x800004aa [10] [0x8000065c], PState.PSt 0x800004ae [10] [0x8000065c], PState.PSt 0x800004b2 [10] [0x8000065c], PState.PSt 0x800004b4 [10] [0x8000065c], PState.PSt 0x800004b8 [10] [0x8000065c], PState.PSt 0x800004ba [10] [0x8000065c], PState.PSt 0x800004be [15, 10] [0x8000065c], PState.PSt 0x800004c0 [15, 10] [0x8000065c], PState.PSt 0x800004c4 [15, 10] [0x8000065c]]⟩,
  ⟨0x80000662, false, [PState.PSt 0x80000666 [15] [], PState.PSt 0x8000066a [14, 15] []]⟩,
  ⟨0x80000672, true, [PState.PSt 0x80000674 [10] [], PState.PSt 0x80000490 [10] [0x80000678], PState.PSt 0x80000492 [10] [0x80000678], PState.PSt 0x80000494 [10] [0x80000678], PState.PSt 0x80000496 [10] [0x80000678], PState.PSt 0x80000498 [10] [0x80000678], PState.PSt 0x8000049a [10] [0x80000678], PState.PSt 0x8000049c [10] [0x80000678], PState.PSt 0x800004a0 [10] [0x80000678], PState.PSt 0x800004a2 [10] [0x80000678], PState.PSt 0x800004a6 [10] [0x80000678], PState.PSt 0x800004a8 [10] [0x80000678], PState.PSt 0x800004aa [10] [0x80000678], PState.PSt 0x800004ae [10] [0x80000678], PState.PSt 0x800004b2 [10] [0x80000678], PState.PSt 0x800004b4 [10] [0x80000678], PState.PSt 0x800004b8 [10] [0x80000678], PState.PSt 0x800004ba [10] [0x80000678], PState.PSt 0x800004be [15, 10] [0x80000678], PState.PSt 0x800004c0 [15, 10] [0x80000678], PState.PSt 0x800004c4 [15, 10] [0x80000678]]⟩,
  ⟨0x8000067e, false, [PState.PSt 0x80000682 [15] [], PState.PSt 0x80000686 [14, 15] []]⟩,
  ⟨0x8000068e, true, [PState.PSt 0x80000692 [10] [], PState.PSt 0x80000490 [10] [0x80000696], PState.PSt 0x80000492 [10] [0x80000696], PState.PSt 0x80000494 [10] [0x80000696], PState.PSt 0x80000496 [10] [0x80000696], PState.PSt 0x80000498 [10] [0x80000696], PState.PSt 0x8000049a [10] [0x80000696], PState.PSt 0x8000049c [10] [0x80000696], PState.PSt 0x800004a0 [10] [0x80000696], PState.PSt 0x800004a2 [10] [0x80000696], PState.PSt 0x800004a6 [10] [0x80000696], PState.PSt 0x800004a8 [10] [0x80000696], PState.PSt 0x800004aa [10] [0x80000696], PState.PSt 0x800004ae [10] [0x80000696], PState.PSt 0x800004b2 [10] [0x80000696], PState.PSt 0x800004b4 [10] [0x80000696], PState.PSt 0x800004b8 [10] [0x80000696], PState.PSt 0x800004ba [10] [0x80000696], PState.PSt 0x800004be [15, 10] [0x80000696], PState.PSt 0x800004c0 [15, 10] [0x80000696], PState.PSt 0x800004c4 [15, 10] [0x80000696]]⟩,
  ⟨0x80000698, false, [PState.PSt 0x8000069c [15] [], PState.PSt 0x800006a0 [14, 15] []]⟩,
  ⟨0x800006a6, true, [PState.PSt 0x800006a8 [10] [], PState.PSt 0x80000490 [10] [0x800006ac], PState.PSt 0x80000492 [10] [0x800006ac], PState.PSt 0x80000494 [10] [0x800006ac], PState.PSt 0x80000496 [10] [0x800006ac], PState.PSt 0x80000498 [10] [0x800006ac], PState.PSt 0x8000049a [10] [0x800006ac], PState.PSt 0x8000049c [10] [0x800006ac], PState.PSt 0x800004a0 [10] [0x800006ac], PState.PSt 0x800004a2 [10] [0x800006ac], PState.PSt 0x800004a6 [10] [0x800006ac], PState.PSt 0x800004a8 [10] [0x800006ac], PState.PSt 0x800004aa [10] [0x800006ac], PState.PSt 0x800004ae [10] [0x800006ac], PState.PSt 0x800004b2 [10] [0x800006ac], PState.PSt 0x800004b4 [10] [0x800006ac], PState.PSt 0x800004b8 [10] [0x800006ac], PState.PSt 0x800004ba [10] [0x800006ac], PState.PSt 0x800004be [15, 10] [0x800006ac], PState.PSt 0x800004c0 [15, 10] [0x800006ac], PState.PSt 0x800004c4 [15, 10] [0x800006ac]]⟩,
  ⟨0x800006b2, false, [PState.PSt 0x800006b6 [15] [], PState.PSt 0x800006ba [14, 15] []]⟩
]

def walkRows1 : List WRow := [
  ⟨0x800006c2, true, [PState.PSt 0x800006c4 [10] [], PState.PSt 0x80000490 [10] [0x800006c8], PState.PSt 0x80000492 [10] [0x800006c8], PState.PSt 0x80000494 [10] [0x800006c8], PState.PSt 0x80000496 [10] [0x800006c8], PState.PSt 0x80000498 [10] [0x800006c8], PState.PSt 0x8000049a [10] [0x800006c8], PState.PSt 0x8000049c [10] [0x800006c8], PState.PSt 0x800004a0 [10] [0x800006c8], PState.PSt 0x800004a2 [10] [0x800006c8], PState.PSt 0x800004a6 [10] [0x800006c8], PState.PSt 0x800004a8 [10] [0x800006c8], PState.PSt 0x800004aa [10] [0x800006c8], PState.PSt 0x800004ae [10] [0x800006c8], PState.PSt 0x800004b2 [10] [0x800006c8], PState.PSt 0x800004b4 [10] [0x800006c8], PState.PSt 0x800004b8 [10] [0x800006c8], PState.PSt 0x800004ba [10] [0x800006c8], PState.PSt 0x800004be [15, 10] [0x800006c8], PState.PSt 0x800004c0 [15, 10] [0x800006c8], PState.PSt 0x800004c4 [15, 10] [0x800006c8]]⟩,
  ⟨0x800006d0, false, [PState.PSt 0x800006d4 [15] [], PState.PSt 0x800006d8 [14, 15] []]⟩,
  ⟨0x800006dc, true, [PState.PSt 0x800006e0 [21] [], PState.PSt 0x800006e4 [21] [], PState.PSt 0x80000478 [21] [0x800006e8], PState.PSt 0x8000047a [21] [0x800006e8], PState.PSt 0x8000047c [21] [0x800006e8], PState.PSt 0x8000047e [21] [0x800006e8], PState.PSt 0x80000480 [21] [0x800006e8], PState.PSt 0x80000482 [21] [0x800006e8], PState.PSt 0x80000484 [21] [0x800006e8], PState.PSt 0x800009ac [21] [0x80000488, 0x800006e8], PState.PSt 0x800009ae [21] [0x80000488, 0x800006e8], PState.PSt 0x800009b0 [21] [0x80000488, 0x800006e8], PState.PSt 0x800009b2 [21] [0x80000488, 0x800006e8], PState.PSt 0x800009b4 [21] [0x80000488, 0x800006e8], PState.PSt 0x800009b6 [21] [0x80000488, 0x800006e8], PState.PSt 0x800009b8 [21] [0x80000488, 0x800006e8], PState.PSt 0x800009ba [21] [0x80000488, 0x800006e8]]⟩,
  ⟨0x80000714, false, [PState.PSt 0x80000718 [15] [], PState.PSt 0x8000071c [14, 15] []]⟩,
  ⟨0x80000728, false, [PState.PSt 0x8000072c [15] [], PState.PSt 0x80000730 [14, 15] []]⟩,
  ⟨0x80000734, false, [PState.PSt 0x80000738 [20] []]⟩,
  ⟨0x8000073c, false, [PState.PSt 0x80000740 [10] []]⟩,
  ⟨0x8000074a, false, [PState.PSt 0x8000074e [10] []]⟩,
  ⟨0x8000089e, false, [PState.PSt 0x800008a0 [15] []]⟩,
  ⟨0x800008a4, false, [PState.PSt 0x800008a6 [15] [], PState.PSt 0x800008aa [15] []]⟩,
  ⟨0x800008ae, false, [PState.PSt 0x800008b0 [14] [], PState.PSt 0x800008b2 [14] []]⟩,
  ⟨0x800008b6, false, [PState.PSt 0x800008b8 [14] []]⟩,
  ⟨0x800008bc, false, [PState.PSt 0x800008be [14] []]⟩,
  ⟨0x800008c2, false, [PState.PSt 0x800008c4 [15] [], PState.PSt 0x800008c6 [15] []]⟩,
  ⟨0x800008ca, false, [PState.PSt 0x800008cc [15] [], PState.PSt 0x800008d0 [15] [], PState.PSt 0x800008d2 [15] [], PState.PSt 0x800008d4 [15] []]⟩,
  ⟨0x800008d2, false, [PState.PSt 0x800008d4 [14] []]⟩,
  ⟨0x80000972, false, [PState.PSt 0x80000976 [14] [], PState.PSt 0x8000097a [15, 14] [], PState.PSt 0x8000097e [15, 14] []]⟩,
  ⟨0x80000976, false, [PState.PSt 0x8000097a [15] [], PState.PSt 0x8000097e [15] []]⟩,
  ⟨0x80000984, false, [PState.PSt 0x80000988 [15] []]⟩,
  ⟨0x800009e4, false, [PState.PSt 0x800009e8 [13] [], PState.PSt 0x800009ec [14, 13] [], PState.PSt 0x800009f0 [15, 14, 13] [], PState.PSt 0x800009f4 [15, 14, 13] []]⟩,
  ⟨0x800009ec, false, [PState.PSt 0x800009f0 [15] [], PState.PSt 0x800009f4 [15] []]⟩,
  ⟨0x80000a34, false, [PState.PSt 0x80000a36 [15] [], PState.PSt 0x80000a3a [14, 15] [], PState.PSt 0x80000a3e [14, 15] [], PState.PSt 0x80000a42 [14, 15] []]⟩,
  ⟨0x80000a3a, false, [PState.PSt 0x80000a3e [15] [], PState.PSt 0x80000a42 [15] []]⟩,
  ⟨0x80000a56, false, [PState.PSt 0x80000a58 [14] [], PState.PSt 0x80000a5c [13, 14] [], PState.PSt 0x80000a60 [15, 13, 14] [], PState.PSt 0x80000a62 [15, 13, 14] []]⟩,
  ⟨0x80000a5c, false, [PState.PSt 0x80000a60 [15] [], PState.PSt 0x80000a62 [15] []]⟩,
  ⟨0x80000a6c, false, [PState.PSt 0x80000a6e [15] []]⟩,
  ⟨0x80000ada, false, [PState.PSt 0x80000ade [15] []]⟩,
  ⟨0x80000b98, false, [PState.PSt 0x80000b9c [9] []]⟩,
  ⟨0x80000b9e, false, [PState.PSt 0x80000ba0 [15] [], PState.PSt 0x80000ba4 [15] []]⟩,
  ⟨0x80000bf2, false, [PState.PSt 0x80000bf4 [15] []]⟩,
  ⟨0x80000c32, false, [PState.PSt 0x80000c34 [15] []]⟩,
  ⟨0x80000c3a, false, [PState.PSt 0x80000c3c [15] [], PState.PSt 0x80000c3e [15] []]⟩,
  ⟨0x80000cac, false, [PState.PSt 0x80000cae [15] []]⟩,
  ⟨0x80000cb8, false, [PState.PSt 0x80000cba [15] []]⟩,
  ⟨0x80000d50, false, [PState.PSt 0x80000d54 [15] [], PState.PSt 0x80000d58 [15] []]⟩,
  ⟨0x80000d54, false, [PState.PSt 0x80000d58 [14] []]⟩,
  ⟨0x80000d94, false, [PState.PSt 0x80000d98 [13] []]⟩,
  ⟨0x80000dca, false, [PState.PSt 0x80000dce [12] []]⟩,
  ⟨0x80000df6, false, [PState.PSt 0x80000dfa [15] []]⟩,
  ⟨0x80000dfc, false, [PState.PSt 0x80000e00 [14] []]⟩
]

def walkRows2 : List WRow := [
  ⟨0x80000e40, false, [PState.PSt 0x80000e44 [14] []]⟩,
  ⟨0x80000e8c, false, [PState.PSt 0x80000e90 [14] []]⟩,
  ⟨0x80000eaa, false, [PState.PSt 0x80000eae [15] []]⟩,
  ⟨0x80000eb8, false, [PState.PSt 0x80000ebc [14] []]⟩,
  ⟨0x80000ee4, false, [PState.PSt 0x80000ee6 [15] []]⟩,
  ⟨0x80000fe0, false, [PState.PSt 0x80000fe4 [9] [], PState.PSt 0x80000fe8 [15, 9] []]⟩,
  ⟨0x80001064, false, [PState.PSt 0x80001066 [15] [], PState.PSt 0x8000106a [13, 15] [], PState.PSt 0x8000106c [13, 15] [], PState.PSt 0x8000106e [13, 15] []]⟩,
  ⟨0x800010cc, false, [PState.PSt 0x800010ce [15] [], PState.PSt 0x800010d0 [15] []]⟩,
  ⟨0x800012be, false, [PState.PSt 0x800012c0 [15] [], PState.PSt 0x800012c4 [14, 15] []]⟩,
  ⟨0x80001402, false, [PState.PSt 0x80001404 [15] [], PState.PSt 0x80001408 [14, 15] []]⟩,
  ⟨0x8000149c, false, [PState.PSt 0x800014a0 [19] [], PState.PSt 0x800014a4 [15, 19] []]⟩,
  ⟨0x80001510, false, [PState.PSt 0x80001512 [15] [], PState.PSt 0x80001514 [15] []]⟩,
  ⟨0x80001644, false, [PState.PSt 0x80001646 [15] [], PState.PSt 0x80001648 [15] []]⟩,
  ⟨0x800017d0, false, [PState.PSt 0x800017d4 [13] []]⟩,
  ⟨0x800019c6, false, [PState.PSt 0x800019ca [15] []]⟩,
  ⟨0x800019f4, false, [PState.PSt 0x800019f6 [15] []]⟩,
  ⟨0x800019f8, false, [PState.PSt 0x800019fa [15] [], PState.PSt 0x800019fc [14, 15] [], PState.PSt 0x800019fe [14] []]⟩,
  ⟨0x800019fa, false, [PState.PSt 0x800019fc [14] [], PState.PSt 0x800019fe [14] []]⟩,
  ⟨0x80001b1a, false, [PState.PSt 0x80001b1c [10] []]⟩,
  ⟨0x80001b26, false, [PState.PSt 0x80001b28 [10] []]⟩,
  ⟨0x80001b2a, true, [PState.PSt 0x80001b2c [11] [], PState.PSt 0x80001ac8 [11] [0x80001b30], PState.PSt 0x80001aca [11] [0x80001b30], PState.PSt 0x80001acc [11] [0x80001b30], PState.PSt 0x80001ace [11] [0x80001b30], PState.PSt 0x80001ad0 [11] [0x80001b30], PState.PSt 0x80001ad2 [11] [0x80001b30], PState.PSt 0x80001ad4 [11] [0x80001b30], PState.PSt 0x80001ad6 [11] [0x80001b30], PState.PSt 0x80001ad8 [18, 11] [0x80001b30], PState.PSt 0x80001ada [18, 11] [0x80001b30], PState.PSt 0x80001adc [18, 11] [0x80001b30], PState.PSt 0x80001ae0 [18] [0x80001b30], PState.PSt 0x80001ae2 [18] [0x80001b30], PState.PSt 0x80001ae4 [18] [0x80001b30], PState.PSt 0x80001260 [18] [0x80001ae8, 0x80001b30], PState.PSt 0x80001262 [18] [0x80001ae8, 0x80001b30], PState.PSt 0x80001264 [18] [0x80001ae8, 0x80001b30], PState.PSt 0x80001266 [18] [0x80001ae8, 0x80001b30], PState.PSt 0x80001268 [18] [0x80001ae8, 0x80001b30], PState.PSt 0x8000126c [18] [0x80001ae8, 0x80001b30], PState.PSt 0x8000126e [18] [0x80001ae8, 0x80001b30], PState.PSt 0x8000128e [18] [0x80001ae8, 0x80001b30], PState.PSt 0x80001290 [18] [0x80001ae8, 0x80001b30]]⟩,
  ⟨0x80001b94, false, [PState.PSt 0x80001b96 [15] []]⟩,
  ⟨0x80001bba, false, [PState.PSt 0x80001bbe [13] [], PState.PSt 0x80001bc2 [13] [], PState.PSt 0x80001bc4 [13] [], PState.PSt 0x80001bc8 [13] [], PState.PSt 0x80001bcc [13] [], PState.PSt 0x80001bd4 [13] [], PState.PSt 0x80001bd6 [13] []]⟩,
  ⟨0x80001be6, false, [PState.PSt 0x80001be8 [14] []]⟩,
  ⟨0x80001c3c, false, [PState.PSt 0x80001c3e [15] [], PState.PSt 0x80001c40 [15] [], PState.PSt 0x80001c42 [15] []]⟩,
  ⟨0x80001cc8, true, [PState.PSt 0x80001cca [11] [], PState.PSt 0x80001cce [11] [], PState.PSt 0x80001cd2 [12, 11] [], PState.PSt 0x80001cd6 [12, 11] [], PState.PSt 0x80001cd8 [12, 11] [], PState.PSt 0x80001cda [12, 11] [], PState.PSt 0x80001cfc [11] [], PState.PSt 0x80001d00 [11] [], PState.PSt 0x80001d04 [12, 11] [], PState.PSt 0x80001d06 [12, 11] [], PState.PSt 0x800012ea [12, 11] [0x80001d0a], PState.PSt 0x800012ec [12, 11] [0x80001d0a], PState.PSt 0x800012ee [12, 11] [0x80001d0a], PState.PSt 0x800012f0 [12, 11] [0x80001d0a], PState.PSt 0x800012f2 [12, 11] [0x80001d0a], PState.PSt 0x800012f4 [12, 11] [0x80001d0a], PState.PSt 0x800012f6 [9, 12, 11] [0x80001d0a], PState.PSt 0x80001cea [11] []]⟩,
  ⟨0x80001d34, false, [PState.PSt 0x80001d38 [12] [], PState.PSt 0x80001d3a [12] [], PState.PSt 0x80001d3e [12] [], PState.PSt 0x80001466 [12] [0x80001d42]]⟩,
  ⟨0x80001d4a, false, [PState.PSt 0x80001d4e [15] []]⟩,
  ⟨0x80001d52, false, [PState.PSt 0x80001d56 [13] [], PState.PSt 0x80001d58 [15, 13] [], PState.PSt 0x80001d5c [15, 13] [], PState.PSt 0x80001d60 [15, 13] [], PState.PSt 0x80001d62 [10, 15, 13] [], PState.PSt 0x80001d64 [11, 10, 15, 13] [], PState.PSt 0x80001d66 [12, 11, 10, 15, 13] []]⟩,
  ⟨0x80001d58, false, [PState.PSt 0x80001d5c [14] [], PState.PSt 0x80001d60 [14] [], PState.PSt 0x80001d62 [14] [], PState.PSt 0x80001d64 [14] [], PState.PSt 0x80001d66 [14] []]⟩,
  ⟨0x80001d60, false, [PState.PSt 0x80001d62 [10] [], PState.PSt 0x80001d64 [10] [], PState.PSt 0x80001d66 [10] []]⟩,
  ⟨0x80001d6c, false, [PState.PSt 0x80001d6e [12] []]⟩,
  ⟨0x80001d7c, false, [PState.PSt 0x80001d80 [15] []]⟩,
  ⟨0x80001dac, false, [PState.PSt 0x80001dae [10] []]⟩,
  ⟨0x80001dba, true, [PState.PSt 0x80001dbe [10] [], PState.PSt 0x8000331c [10] [0x80001dc2], PState.PSt 0x8000331e [10] [0x80001dc2], PState.PSt 0x80003320 [10] [0x80001dc2], PState.PSt 0x80003322 [10] [0x80001dc2], PState.PSt 0x80003324 [10] [0x80001dc2], PState.PSt 0x80003326 [10] [0x80001dc2], PState.PSt 0x80003328 [9, 10] [0x80001dc2], PState.PSt 0x8000332c [9] [0x80001dc2], PState.PSt 0x80003330 [9] [0x80001dc2], PState.PSt 0x80000c58 [9] [0x80003334, 0x80001dc2], PState.PSt 0x80000c5a [9] [0x80003334, 0x80001dc2], PState.PSt 0x80000c5c [9] [0x80003334, 0x80001dc2], PState.PSt 0x80000c5e [9] [0x80003334, 0x80001dc2]]⟩,
  ⟨0x80001dc6, true, [PState.PSt 0x80001dca [10] [], PState.PSt 0x8000331c [10] [0x80001dce], PState.PSt 0x8000331e [10] [0x80001dce], PState.PSt 0x80003320 [10] [0x80001dce], PState.PSt 0x80003322 [10] [0x80001dce], PState.PSt 0x80003324 [10] [0x80001dce], PState.PSt 0x80003326 [10] [0x80001dce], PState.PSt 0x80003328 [9, 10] [0x80001dce], PState.PSt 0x8000332c [9] [0x80001dce], PState.PSt 0x80003330 [9] [0x80001dce], PState.PSt 0x80000c58 [9] [0x80003334, 0x80001dce], PState.PSt 0x80000c5a [9] [0x80003334, 0x80001dce], PState.PSt 0x80000c5c [9] [0x80003334, 0x80001dce], PState.PSt 0x80000c5e [9] [0x80003334, 0x80001dce]]⟩,
  ⟨0x80001de0, false, [PState.PSt 0x80001de4 [15] []]⟩,
  ⟨0x80001de8, true, [PState.PSt 0x80001dec [9] [], PState.PSt 0x80001dee [9] [], PState.PSt 0x80000ce0 [9] [0x80001df2], PState.PSt 0x80000ce2 [9] [0x80001df2], PState.PSt 0x80000ce4 [9] [0x80001df2], PState.PSt 0x80000ce6 [9] [0x80001df2]]⟩,
  ⟨0x80001e9a, false, [PState.PSt 0x80001e9c [15] []]⟩,
  ⟨0x80001f20, false, [PState.PSt 0x80001f22 [14] [], PState.PSt 0x80001f24 [14] []]⟩
]

def walkRows3 : List WRow := [
  ⟨0x80002024, false, [PState.PSt 0x80002026 [15] []]⟩,
  ⟨0x8000207e, false, [PState.PSt 0x80002080 [15] []]⟩,
  ⟨0x80002088, false, [PState.PSt 0x8000208a [15] []]⟩,
  ⟨0x800020da, false, [PState.PSt 0x800020dc [15] []]⟩,
  ⟨0x800020e0, false, [PState.PSt 0x800020e4 [10] []]⟩,
  ⟨0x80002118, false, [PState.PSt 0x8000211c [15] [], PState.PSt 0x80002120 [15] [], PState.PSt 0x80002124 [15] []]⟩,
  ⟨0x8000213a, false, [PState.PSt 0x8000213c [10] []]⟩,
  ⟨0x8000214c, true, [PState.PSt 0x80002150 [10] [], PState.PSt 0x800034d4 [10] [0x80002154], PState.PSt 0x800034d6 [10] [0x80002154], PState.PSt 0x800034d8 [10] [0x80002154], PState.PSt 0x800034da [10] [0x80002154], PState.PSt 0x800034dc [10] [0x80002154], PState.PSt 0x800034de [10] [0x80002154], PState.PSt 0x800034e0 [9, 10] [0x80002154], PState.PSt 0x800034e4 [9] [0x80002154], PState.PSt 0x800034e8 [9] [0x80002154], PState.PSt 0x80000c58 [9] [0x800034ec, 0x80002154], PState.PSt 0x80000c5a [9] [0x800034ec, 0x80002154], PState.PSt 0x80000c5c [9] [0x800034ec, 0x80002154], PState.PSt 0x80000c5e [9] [0x800034ec, 0x80002154]]⟩,
  ⟨0x80002160, true, [PState.PSt 0x80002164 [10] [], PState.PSt 0x800034d4 [10] [0x80002168], PState.PSt 0x800034d6 [10] [0x80002168], PState.PSt 0x800034d8 [10] [0x80002168], PState.PSt 0x800034da [10] [0x80002168], PState.PSt 0x800034dc [10] [0x80002168], PState.PSt 0x800034de [10] [0x80002168], PState.PSt 0x800034e0 [9, 10] [0x80002168], PState.PSt 0x800034e4 [9] [0x80002168], PState.PSt 0x800034e8 [9] [0x80002168], PState.PSt 0x80000c58 [9] [0x800034ec, 0x80002168], PState.PSt 0x80000c5a [9] [0x800034ec, 0x80002168], PState.PSt 0x80000c5c [9] [0x800034ec, 0x80002168], PState.PSt 0x80000c5e [9] [0x800034ec, 0x80002168]]⟩,
  ⟨0x800021de, false, [PState.PSt 0x800021e0 [15] []]⟩,
  ⟨0x800021fa, false, [PState.PSt 0x800021fc [14] [], PState.PSt 0x800021fe [14] []]⟩,
  ⟨0x80002322, false, [PState.PSt 0x80002324 [15] []]⟩,
  ⟨0x8000232e, false, [PState.PSt 0x80002330 [15] []]⟩,
  ⟨0x80002468, true, [PState.PSt 0x8000246c [11] [], PState.PSt 0x8000246e [11] [], PState.PSt 0x80000526 [11] [0x80002472], PState.PSt 0x80000528 [11] [0x80002472], PState.PSt 0x8000052a [11] [0x80002472], PState.PSt 0x8000052c [11] [0x80002472], PState.PSt 0x8000052e [11] [0x80002472], PState.PSt 0x80000530 [11] [0x80002472], PState.PSt 0x80000532 [11] [0x80002472]]⟩,
  ⟨0x80002482, false, [PState.PSt 0x80002486 [15] []]⟩,
  ⟨0x80002498, false, [PState.PSt 0x8000249a [12] []]⟩,
  ⟨0x80002590, false, [PState.PSt 0x80002592 [15] [], PState.PSt 0x80002596 [15] []]⟩,
  ⟨0x80002598, false, [PState.PSt 0x8000259a [14] [], PState.PSt 0x8000259c [14] [], PState.PSt 0x8000259e [14] [], PState.PSt 0x800025a0 [14] []]⟩,
  ⟨0x8000259a, false, [PState.PSt 0x8000259c [15] [], PState.PSt 0x8000259e [15] [], PState.PSt 0x800025a0 [15] []]⟩,
  ⟨0x800025a2, false, [PState.PSt 0x800025a4 [15] [], PState.PSt 0x800025a8 [15] [], PState.PSt 0x800025ac [15] []]⟩,
  ⟨0x800025ae, false, [PState.PSt 0x800025b0 [15] [], PState.PSt 0x800025b2 [15] []]⟩,
  ⟨0x80002610, false, [PState.PSt 0x80002612 [15] [], PState.PSt 0x80002614 [15] []]⟩,
  ⟨0x800026d8, false, [PState.PSt 0x800026da [15] [], PState.PSt 0x800026de [15] []]⟩,
  ⟨0x80002746, false, [PState.PSt 0x80002748 [14] [], PState.PSt 0x8000274a [15, 14] [], PState.PSt 0x8000274c [15, 14] []]⟩,
  ⟨0x80002748, false, [PState.PSt 0x8000274a [15] [], PState.PSt 0x8000274c [15] []]⟩,
  ⟨0x8000278e, true, [PState.PSt 0x80002790 [11] [], PState.PSt 0x80002792 [11] [], PState.PSt 0x80001546 [11] [0x80002796], PState.PSt 0x80001548 [11] [0x80002796], PState.PSt 0x8000154a [11] [0x80002796], PState.PSt 0x8000154c [11] [0x80002796], PState.PSt 0x8000154e [11] [0x80002796], PState.PSt 0x80001550 [11] [0x80002796], PState.PSt 0x80001552 [11] [0x80002796]]⟩,
  ⟨0x800028be, false, [PState.PSt 0x800028c0 [11] []]⟩,
  ⟨0x800029a8, false, [PState.PSt 0x800029ac [18] [], PState.PSt 0x800029b0 [15, 18] [], PState.PSt 0x800029b4 [13, 15, 18] [], PState.PSt 0x800029b6 [13, 15, 18] [], PState.PSt 0x800029b8 [13, 15, 18] []]⟩,
  ⟨0x800029ac, false, [PState.PSt 0x800029b0 [15] [], PState.PSt 0x800029b4 [13, 15] [], PState.PSt 0x800029b6 [13, 15] [], PState.PSt 0x800029b8 [13, 15] []]⟩,
  ⟨0x800029ca, false, [PState.PSt 0x800029cc [14] []]⟩,
  ⟨0x800029ce, false, [PState.PSt 0x800029d2 [15] [], PState.PSt 0x800029d6 [15] [], PState.PSt 0x800029d8 [15] []]⟩,
  ⟨0x800029ee, true, [PState.PSt 0x800029f0 [11] [], PState.PSt 0x800029f4 [11] [], PState.PSt 0x800029f8 [11] [], PState.PSt 0x80000526 [11] [0x800029fc], PState.PSt 0x80000528 [11] [0x800029fc], PState.PSt 0x8000052a [11] [0x800029fc], PState.PSt 0x8000052c [11] [0x800029fc], PState.PSt 0x8000052e [11] [0x800029fc], PState.PSt 0x80000530 [11] [0x800029fc], PState.PSt 0x80000532 [11] [0x800029fc]]⟩,
  ⟨0x800029fc, false, [PState.PSt 0x800029fe [15] [], PState.PSt 0x80002a00 [15] []]⟩,
  ⟨0x80002aa0, true, [PState.PSt 0x80002aa2 [9] [], PState.PSt 0x80002aa6 [9] [], PState.PSt 0x80002aa8 [9] [], PState.PSt 0x80002aac [9] [], PState.PSt 0x80002ab0 [9] [], PState.PSt 0x80002ab4 [9] [], PState.PSt 0x80002ab6 [15, 9] [], PState.PSt 0x80002aba [15, 9] [], PState.PSt 0x80002abc [15, 9] [], PState.PSt 0x80002abe [15, 9] [], PState.PSt 0x80002ad6 [9] [], PState.PSt 0x80002ada [9] [], PState.PSt 0x80001cb4 [9] [0x80002ade], PState.PSt 0x80001cb6 [9] [0x80002ade], PState.PSt 0x80001cb8 [9] [0x80002ade], PState.PSt 0x80001cba [9] [0x80002ade]]⟩,
  ⟨0x80002aa2, false, [PState.PSt 0x80002aa6 [14] [], PState.PSt 0x80002aa8 [14] []]⟩,
  ⟨0x80002aac, false, [PState.PSt 0x80002ab0 [15] []]⟩,
  ⟨0x80002aca, false, [PState.PSt 0x80002ace [14] [], PState.PSt 0x80002ad0 [14] [], PState.PSt 0x80002ad2 [15, 14] []]⟩,
  ⟨0x80002ace, false, [PState.PSt 0x80002ad0 [15] [], PState.PSt 0x80002ad2 [15] []]⟩,
  ⟨0x80002ad6, true, [PState.PSt 0x80002ada [10] [], PState.PSt 0x80001cb4 [10] [0x80002ade], PState.PSt 0x80001cb6 [10] [0x80002ade], PState.PSt 0x80001cb8 [10] [0x80002ade], PState.PSt 0x80001cba [10] [0x80002ade], PState.PSt 0x80001cbc [10] [0x80002ade], PState.PSt 0x80001cbe [10] [0x80002ade], PState.PSt 0x80001cc0 [10] [0x80002ade], PState.PSt 0x80001cc2 [9, 10] [0x80002ade], PState.PSt 0x8000197c [9, 10] [0x80001cc6, 0x80002ade], PState.PSt 0x8000197e [9, 10] [0x80001cc6, 0x80002ade], PState.PSt 0x80001980 [9, 10] [0x80001cc6, 0x80002ade], PState.PSt 0x80001982 [9, 10] [0x80001cc6, 0x80002ade]]⟩,
  ⟨0x80002b08, false, [PState.PSt 0x80002b0c [15] []]⟩
]

def walkRows4 : List WRow := [
  ⟨0x80002b1c, false, [PState.PSt 0x80002b20 [15] []]⟩,
  ⟨0x80002b60, false, [PState.PSt 0x80002b64 [15] [], PState.PSt 0x80002b68 [15] [], PState.PSt 0x80002b6c [15] []]⟩,
  ⟨0x80002b68, false, [PState.PSt 0x80002b6c [14] []]⟩,
  ⟨0x80002bba, false, [PState.PSt 0x80002bbe [10] [], PState.PSt 0x800021b6 [10] [0x80002bc2]]⟩,
  ⟨0x80002be4, true, [PState.PSt 0x80002be8 [15] [], PState.PSt 0x80002bea [9, 15] [], PState.PSt 0x80002bee [9, 15] [], PState.PSt 0x80002bf2 [9, 15] [], PState.PSt 0x80000ce0 [9, 15] [0x80002bf6], PState.PSt 0x80000ce2 [9, 15] [0x80002bf6], PState.PSt 0x80000ce4 [9, 15] [0x80002bf6], PState.PSt 0x80000ce6 [9, 15] [0x80002bf6]]⟩,
  ⟨0x80002c1c, false, [PState.PSt 0x80002c20 [15] [], PState.PSt 0x80002c24 [15] [], PState.PSt 0x80002c26 [15] []]⟩,
  ⟨0x80002c20, false, [PState.PSt 0x80002c24 [14] [], PState.PSt 0x80002c26 [15, 14] []]⟩,
  ⟨0x80002c84, false, [PState.PSt 0x80002c88 [15] []]⟩,
  ⟨0x80002c98, false, [PState.PSt 0x80002c9c [15] []]⟩,
  ⟨0x80002cdc, false, [PState.PSt 0x80002ce0 [9] [], PState.PSt 0x80002ce4 [9] [], PState.PSt 0x80002ce8 [9] []]⟩,
  ⟨0x80002cf0, false, [PState.PSt 0x80002cf2 [9] []]⟩,
  ⟨0x80002cf6, false, [PState.PSt 0x80002cf8 [15] []]⟩,
  ⟨0x80002cfc, false, [PState.PSt 0x80002cfe [15] []]⟩,
  ⟨0x80002d02, false, [PState.PSt 0x80002d04 [15] [], PState.PSt 0x80002d06 [15] []]⟩,
  ⟨0x80002d22, false, [PState.PSt 0x80002d26 [9] [], PState.PSt 0x80002d2a [9] [], PState.PSt 0x80002d2e [9] []]⟩,
  ⟨0x80002d34, false, [PState.PSt 0x80002d36 [15] []]⟩,
  ⟨0x80002d38, false, [PState.PSt 0x80002d3a [9] []]⟩,
  ⟨0x80002d6e, false, [PState.PSt 0x80002d70 [15] []]⟩,
  ⟨0x80002dee, false, [PState.PSt 0x80002df0 [15] [], PState.PSt 0x80002df2 [15] []]⟩,
  ⟨0x80002df6, false, [PState.PSt 0x80002df8 [14] [], PState.PSt 0x80002dfa [14] []]⟩,
  ⟨0x80002df8, false, [PState.PSt 0x80002dfa [15] []]⟩,
  ⟨0x80002dfc, false, [PState.PSt 0x80002dfe [14] []]⟩,
  ⟨0x80002e08, false, [PState.PSt 0x80002e0c [14] []]⟩,
  ⟨0x80002e18, false, [PState.PSt 0x80002e1c [14] []]⟩,
  ⟨0x80002e5e, false, [PState.PSt 0x80002e60 [15] [], PState.PSt 0x80002e62 [15] []]⟩,
  ⟨0x80002e92, false, [PState.PSt 0x80002e94 [15] [], PState.PSt 0x80002e96 [15] []]⟩,
  ⟨0x80002ebc, false, [PState.PSt 0x80002ec0 [15] []]⟩,
  ⟨0x80002f42, false, [PState.PSt 0x80002f46 [15] []]⟩,
  ⟨0x80002f5c, false, [PState.PSt 0x80002f60 [10] [], PState.PSt 0x80002f62 [10] [], PState.PSt 0x80002f64 [10] []]⟩,
  ⟨0x80002f82, false, [PState.PSt 0x80002f86 [12] [], PState.PSt 0x80002f8a [11, 12] []]⟩,
  ⟨0x80002ff8, false, [PState.PSt 0x80002ffa [15] []]⟩,
  ⟨0x80002ffe, false, [PState.PSt 0x80003000 [14] []]⟩,
  ⟨0x80003004, false, [PState.PSt 0x80003006 [14] []]⟩,
  ⟨0x80003090, false, [PState.PSt 0x80003094 [14] [], PState.PSt 0x80003098 [13, 14] []]⟩,
  ⟨0x800030ec, false, [PState.PSt 0x800030f0 [9] []]⟩,
  ⟨0x80003112, false, [PState.PSt 0x80003116 [9] []]⟩,
  ⟨0x80003148, false, [PState.PSt 0x8000314a [9] []]⟩,
  ⟨0x800031ee, false, [PState.PSt 0x800031f2 [14] [], PState.PSt 0x800031f4 [14] []]⟩,
  ⟨0x80003230, false, [PState.PSt 0x80003234 [15] []]⟩,
  ⟨0x8000323c, false, [PState.PSt 0x80003240 [14] [], PState.PSt 0x80003244 [14] []]⟩
]

def walkRows5 : List WRow := [
  ⟨0x800032c8, false, [PState.PSt 0x800032ca [14] [], PState.PSt 0x800032cc [14] [], PState.PSt 0x800032ce [14] [], PState.PSt 0x800032d0 [15, 14] [], PState.PSt 0x800032d4 [15] []]⟩,
  ⟨0x800032d0, false, [PState.PSt 0x800032d4 [14] []]⟩,
  ⟨0x800032d8, false, [PState.PSt 0x800032dc [14] []]⟩,
  ⟨0x800032e0, false, [PState.PSt 0x800032e4 [14] []]⟩,
  ⟨0x800032e8, false, [PState.PSt 0x800032ec [14] []]⟩,
  ⟨0x800032f0, false, [PState.PSt 0x800032f2 [14] []]⟩,
  ⟨0x80003334, false, [PState.PSt 0x80003336 [15] [], PState.PSt 0x80003338 [15] []]⟩,
  ⟨0x80003360, false, [PState.PSt 0x80003362 [15] []]⟩,
  ⟨0x8000336c, false, [PState.PSt 0x8000336e [15] []]⟩,
  ⟨0x800033a6, false, [PState.PSt 0x800033a8 [15] [], PState.PSt 0x800033aa [15] [], PState.PSt 0x800033ac [15] [], PState.PSt 0x800033ae [11, 15] [], PState.PSt 0x800033b2 [11, 15] []]⟩,
  ⟨0x800033ae, false, [PState.PSt 0x800033b2 [15] []]⟩,
  ⟨0x800033b6, false, [PState.PSt 0x800033ba [15] []]⟩,
  ⟨0x800033be, false, [PState.PSt 0x800033c2 [15] []]⟩,
  ⟨0x800033c6, false, [PState.PSt 0x800033ca [15] []]⟩,
  ⟨0x800033ce, false, [PState.PSt 0x800033d0 [15] []]⟩,
  ⟨0x800033ea, false, [PState.PSt 0x800033ee [15] []]⟩,
  ⟨0x8000341c, false, [PState.PSt 0x8000341e [15] []]⟩,
  ⟨0x80003460, false, [PState.PSt 0x80003462 [11] []]⟩,
  ⟨0x80003472, false, [PState.PSt 0x80003476 [11] []]⟩,
  ⟨0x800034ac, false, [PState.PSt 0x800034ae [11] []]⟩,
  ⟨0x800034c0, true, [PState.PSt 0x800034c4 [11] [], PState.PSt 0x800034c8 [11] [], PState.PSt 0x8000305e [11] [0x800034cc], PState.PSt 0x80003060 [11] [0x800034cc], PState.PSt 0x80003062 [11] [0x800034cc], PState.PSt 0x80003064 [11] [0x800034cc], PState.PSt 0x80003066 [11] [0x800034cc], PState.PSt 0x80003068 [11] [0x800034cc], PState.PSt 0x8000306a [11] [0x800034cc], PState.PSt 0x8000306c [9, 11] [0x800034cc], PState.PSt 0x80003070 [15, 9, 11] [0x800034cc], PState.PSt 0x80003074 [15, 9] [0x800034cc], PState.PSt 0x80003078 [15, 9] [0x800034cc], PState.PSt 0x8000307a [11, 15, 9] [0x800034cc], PState.PSt 0x80002cba [11, 15, 9] [0x8000307e, 0x800034cc], PState.PSt 0x80002cbc [11, 15, 9] [0x8000307e, 0x800034cc], PState.PSt 0x80002cbe [11, 15, 9] [0x8000307e, 0x800034cc], PState.PSt 0x80002cc0 [11, 15, 9] [0x8000307e, 0x800034cc]]⟩,
  ⟨0x800034ec, false, [PState.PSt 0x800034ee [15] [], PState.PSt 0x800034f0 [15] []]⟩,
  ⟨0x8000350e, false, [PState.PSt 0x80003510 [14] []]⟩,
  ⟨0x8000351e, false, [PState.PSt 0x80003522 [14] []]⟩,
  ⟨0x8000355a, false, [PState.PSt 0x8000355c [15] [], PState.PSt 0x8000355e [15] []]⟩,
  ⟨0x800035ca, false, [PState.PSt 0x800035ce [14] [], PState.PSt 0x800035d0 [14] []]⟩,
  ⟨0x80003636, false, [PState.PSt 0x8000363a [14] [], PState.PSt 0x8000363e [14] []]⟩,
  ⟨0x80003664, false, [PState.PSt 0x80003668 [14] []]⟩,
  ⟨0x8000366a, false, [PState.PSt 0x8000366e [15] []]⟩,
  ⟨0x800036c2, false, [PState.PSt 0x800036c6 [14] [], PState.PSt 0x800036ca [14] [], PState.PSt 0x800036ce [14] []]⟩,
  ⟨0x80003706, false, [PState.PSt 0x80003708 [15] []]⟩,
  ⟨0x8000370a, false, [PState.PSt 0x8000370c [15] []]⟩,
  ⟨0x8000370e, false, [PState.PSt 0x80003712 [15] []]⟩,
  ⟨0x80003716, false, [PState.PSt 0x8000371a [15] []]⟩,
  ⟨0x8000371e, false, [PState.PSt 0x80003722 [15] []]⟩,
  ⟨0x8000372c, false, [PState.PSt 0x8000372e [15] []]⟩,
  ⟨0x8000381e, false, [PState.PSt 0x80003820 [15] []]⟩,
  ⟨0x800038da, false, [PState.PSt 0x800038de [15] []]⟩,
  ⟨0x80003942, false, [PState.PSt 0x80003946 [14] [], PState.PSt 0x80003948 [14] []]⟩,
  ⟨0x8000395a, true, [PState.PSt 0x8000395c [9] [], PState.PSt 0x8000197c [9] [0x80003960], PState.PSt 0x8000197e [9] [0x80003960], PState.PSt 0x80001980 [9] [0x80003960], PState.PSt 0x80001982 [9] [0x80003960]]⟩
]

def walkRows6 : List WRow := [
  ⟨0x80003960, false, [PState.PSt 0x80003964 [15] [], PState.PSt 0x80003966 [15] []]⟩,
  ⟨0x80003964, false, [PState.PSt 0x80003966 [15] []]⟩,
  ⟨0x80003970, false, [PState.PSt 0x80003974 [15] [], PState.PSt 0x80003976 [15] [], PState.PSt 0x8000397a [15] [], PState.PSt 0x8000397c [15] [], PState.PSt 0x80003980 [15] []]⟩,
  ⟨0x800039cc, false, [PState.PSt 0x800039d0 [15] []]⟩,
  ⟨0x800039e6, false, [PState.PSt 0x800039ea [15] []]⟩,
  ⟨0x80003a4c, false, [PState.PSt 0x80003a50 [14] [], PState.PSt 0x80003a54 [14] []]⟩,
  ⟨0x80003a5c, true, [PState.PSt 0x80003a60 [10] [], PState.PSt 0x8000331c [10] [0x80003a64], PState.PSt 0x8000331e [10] [0x80003a64], PState.PSt 0x80003320 [10] [0x80003a64], PState.PSt 0x80003322 [10] [0x80003a64], PState.PSt 0x80003324 [10] [0x80003a64], PState.PSt 0x80003326 [10] [0x80003a64], PState.PSt 0x80003328 [9, 10] [0x80003a64], PState.PSt 0x8000332c [9] [0x80003a64], PState.PSt 0x80003330 [9] [0x80003a64], PState.PSt 0x80000c58 [9] [0x80003334, 0x80003a64], PState.PSt 0x80000c5a [9] [0x80003334, 0x80003a64], PState.PSt 0x80000c5c [9] [0x80003334, 0x80003a64], PState.PSt 0x80000c5e [9] [0x80003334, 0x80003a64]]⟩,
  ⟨0x80003a76, true, [PState.PSt 0x80003a7a [10] [], PState.PSt 0x8000331c [10] [0x80003a7e], PState.PSt 0x8000331e [10] [0x80003a7e], PState.PSt 0x80003320 [10] [0x80003a7e], PState.PSt 0x80003322 [10] [0x80003a7e], PState.PSt 0x80003324 [10] [0x80003a7e], PState.PSt 0x80003326 [10] [0x80003a7e], PState.PSt 0x80003328 [9, 10] [0x80003a7e], PState.PSt 0x8000332c [9] [0x80003a7e], PState.PSt 0x80003330 [9] [0x80003a7e], PState.PSt 0x80000c58 [9] [0x80003334, 0x80003a7e], PState.PSt 0x80000c5a [9] [0x80003334, 0x80003a7e], PState.PSt 0x80000c5c [9] [0x80003334, 0x80003a7e], PState.PSt 0x80000c5e [9] [0x80003334, 0x80003a7e]]⟩,
  ⟨0x80003adc, false, [PState.PSt 0x80003ae0 [15] []]⟩,
  ⟨0x80003ae6, false, [PState.PSt 0x80003aea [15] []]⟩,
  ⟨0x80003af4, false, [PState.PSt 0x80003af8 [15] []]⟩,
  ⟨0x80003afc, false, [PState.PSt 0x80003b00 [15] []]⟩,
  ⟨0x80003b06, false, [PState.PSt 0x80003b0a [15] []]⟩,
  ⟨0x80003b22, false, [PState.PSt 0x80003b26 [15] []]⟩,
  ⟨0x80003b2c, false, [PState.PSt 0x80003b30 [15] []]⟩,
  ⟨0x80003b36, false, [PState.PSt 0x80003b3a [15] [], PState.PSt 0x80003b3e [14, 15] []]⟩,
  ⟨0x80003b46, false, [PState.PSt 0x80003b4a [15] [], PState.PSt 0x80003b4e [14, 15] []]⟩,
  ⟨0x80003b9a, false, [PState.PSt 0x80003b9e [9] []]⟩,
  ⟨0x80003bbe, false, [PState.PSt 0x80003bc2 [15] []]⟩,
  ⟨0x80003bc6, false, [PState.PSt 0x80003bca [15] []]⟩,
  ⟨0x80003c92, false, [PState.PSt 0x80003c96 [12] []]⟩,
  ⟨0x80003caa, false, [PState.PSt 0x80003cac [13] []]⟩,
  ⟨0x80003cd2, false, [PState.PSt 0x80003cd6 [15] []]⟩,
  ⟨0x80003d32, false, [PState.PSt 0x80003d36 [15] []]⟩,
  ⟨0x80003dc2, false, [PState.PSt 0x80003dc6 [11] []]⟩,
  ⟨0x80003dd4, false, [PState.PSt 0x80003dd6 [12] []]⟩,
  ⟨0x80003dec, false, [PState.PSt 0x80003dee [13] []]⟩,
  ⟨0x80003e56, false, [PState.PSt 0x80003e58 [15] []]⟩,
  ⟨0x80003e5a, false, [PState.PSt 0x80003e5c [14] [], PState.PSt 0x80003e5e [14] [], PState.PSt 0x80003e62 [15, 14] [], PState.PSt 0x80003e64 [15, 14] [], PState.PSt 0x80003e68 [15, 14] [], PState.PSt 0x80003e6a [15, 14] [], PState.PSt 0x80003e6c [15, 14] []]⟩,
  ⟨0x80003e68, false, [PState.PSt 0x80003e6a [13] [], PState.PSt 0x80003e6c [15, 13] []]⟩,
  ⟨0x80003ec2, false, [PState.PSt 0x80003ec4 [15] [], PState.PSt 0x80003ec6 [15] [], PState.PSt 0x80003ec8 [18, 15] []]⟩,
  ⟨0x80003eca, false, [PState.PSt 0x80003ecc [15] []]⟩,
  ⟨0x80003ee4, false, [PState.PSt 0x80003ee6 [15] []]⟩,
  ⟨0x80003efc, false, [PState.PSt 0x80003efe [15] [], PState.PSt 0x80003f00 [15] []]⟩,
  ⟨0x80003fa4, false, [PState.PSt 0x80003fa8 [15] []]⟩,
  ⟨0x80003fe6, false, [PState.PSt 0x80003fea [12] [], PState.PSt 0x80003fec [12] []]⟩,
  ⟨0x80003ff4, false, [PState.PSt 0x80003ff8 [15] []]⟩,
  ⟨0x80004002, false, [PState.PSt 0x80004004 [11] [], PState.PSt 0x80004008 [11] [], PState.PSt 0x8000400c [11] [], PState.PSt 0x8000400e [11] [], PState.PSt 0x80004010 [11] []]⟩,
  ⟨0x8000400e, false, [PState.PSt 0x80004010 [13] []]⟩,
  ⟨0x8000402c, false, [PState.PSt 0x8000402e [14] []]⟩
]

def walkRows7 : List WRow := [
  ⟨0x8000403e, false, [PState.PSt 0x80004040 [15] [], PState.PSt 0x80004042 [15] []]⟩,
  ⟨0x80004070, false, [PState.PSt 0x80004072 [13] []]⟩,
  ⟨0x800040a6, false, [PState.PSt 0x800040aa [15] []]⟩,
  ⟨0x800040b0, false, [PState.PSt 0x800040b4 [15] []]⟩,
  ⟨0x800040c0, true, [PState.PSt 0x800040c4 [18] [], PState.PSt 0x800040c8 [18] [], PState.PSt 0x800040cc [18] [], PState.PSt 0x800040ce [18] [], PState.PSt 0x80001fd4 [18] [0x800040d2], PState.PSt 0x80001fd6 [18] [0x800040d2], PState.PSt 0x80001fd8 [18] [0x800040d2], PState.PSt 0x80001fda [18] [0x800040d2], PState.PSt 0x80001fdc [18] [0x800040d2]]⟩,
  ⟨0x800040e2, false, [PState.PSt 0x800040e4 [15] []]⟩,
  ⟨0x80004150, false, [PState.PSt 0x80004152 [15] []]⟩,
  ⟨0x8000416a, false, [PState.PSt 0x8000416c [15] []]⟩,
  ⟨0x80004176, false, [PState.PSt 0x80004178 [15] []]⟩,
  ⟨0x800041dc, false, [PState.PSt 0x800041de [15] []]⟩,
  ⟨0x80004200, true, [PState.PSt 0x80004202 [9] [], PState.PSt 0x80004206 [9] [], PState.PSt 0x8000420a [9] [], PState.PSt 0x8000420c [9] [], PState.PSt 0x800041e2 [9] [], PState.PSt 0x800041e4 [9] [], PState.PSt 0x80000ce0 [9] [0x800041e8], PState.PSt 0x80000ce2 [9] [0x800041e8], PState.PSt 0x80000ce4 [9] [0x800041e8], PState.PSt 0x80000ce6 [9] [0x800041e8]]⟩,
  ⟨0x80004258, false, [PState.PSt 0x8000425a [15] []]⟩,
  ⟨0x800042a8, false, [PState.PSt 0x800042aa [15] []]⟩,
  ⟨0x800042ee, false, [PState.PSt 0x800042f0 [15] []]⟩,
  ⟨0x800043ac, false, [PState.PSt 0x800043ae [15] [], PState.PSt 0x800043b0 [15] [], PState.PSt 0x800043b2 [15] []]⟩,
  ⟨0x800043bc, true, [PState.PSt 0x800043be [10] [], PState.PSt 0x80003352 [10] [0x800043c2], PState.PSt 0x80003354 [10] [0x800043c2], PState.PSt 0x80003356 [10] [0x800043c2], PState.PSt 0x80003358 [10] [0x800043c2], PState.PSt 0x8000335a [10] [0x800043c2], PState.PSt 0x8000335c [10] [0x800043c2]]⟩,
  ⟨0x800043c8, true, [PState.PSt 0x800043ca [10] [], PState.PSt 0x800036fe [10] [0x800043ce], PState.PSt 0x80003700 [10] [0x800043ce], PState.PSt 0x80003702 [10] [0x800043ce], PState.PSt 0x80003704 [10] [0x800043ce], PState.PSt 0x80003706 [10] [0x800043ce], PState.PSt 0x80003708 [15, 10] [0x800043ce]]⟩,
  ⟨0x800043ce, true, [PState.PSt 0x800043d0 [10] [], PState.PSt 0x80003400 [10] [0x800043d4], PState.PSt 0x80003402 [10] [0x800043d4], PState.PSt 0x80003404 [10] [0x800043d4], PState.PSt 0x80003406 [10] [0x800043d4], PState.PSt 0x80003408 [10] [0x800043d4], PState.PSt 0x8000340a [10] [0x800043d4], PState.PSt 0x8000340c [10] [0x800043d4]]⟩,
  ⟨0x80004408, false, [PState.PSt 0x8000440c [15] []]⟩,
  ⟨0x8000441e, false, [PState.PSt 0x80004420 [15] [], PState.PSt 0x80004422 [15] []]⟩,
  ⟨0x80004432, true, [PState.PSt 0x80004434 [10] [], PState.PSt 0x80003352 [10] [0x80004438], PState.PSt 0x80003354 [10] [0x80004438], PState.PSt 0x80003356 [10] [0x80004438], PState.PSt 0x80003358 [10] [0x80004438], PState.PSt 0x8000335a [10] [0x80004438], PState.PSt 0x8000335c [10] [0x80004438]]⟩,
  ⟨0x8000443a, false, [PState.PSt 0x8000443c [13] [], PState.PSt 0x8000443e [13] [], PState.PSt 0x80004440 [13] [], PState.PSt 0x80004442 [13] [], PState.PSt 0x8000372c [13] [0x80004446], PState.PSt 0x8000372e [13] [0x80004446]]⟩,
  ⟨0x80004440, false, [PState.PSt 0x80004442 [10] [], PState.PSt 0x8000372c [10] [0x80004446], PState.PSt 0x8000372e [15, 10] [0x80004446]]⟩,
  ⟨0x8000444c, false, [PState.PSt 0x8000444e [15] [], PState.PSt 0x80004450 [15] []]⟩,
  ⟨0x80004452, true, [PState.PSt 0x80004454 [10] [], PState.PSt 0x80003400 [10] [0x80004458], PState.PSt 0x80003402 [10] [0x80004458], PState.PSt 0x80003404 [10] [0x80004458], PState.PSt 0x80003406 [10] [0x80004458], PState.PSt 0x80003408 [10] [0x80004458], PState.PSt 0x8000340a [10] [0x80004458], PState.PSt 0x8000340c [10] [0x80004458]]⟩,
  ⟨0x80004468, true, [PState.PSt 0x8000446a [10] [], PState.PSt 0x8000484c [10] [0x8000446e], PState.PSt 0x8000484e [10] [0x8000446e], PState.PSt 0x80004850 [10] [0x8000446e], PState.PSt 0x80004852 [10] [0x8000446e], PState.PSt 0x80004854 [10] [0x8000446e], PState.PSt 0x80004856 [10] [0x8000446e], PState.PSt 0x80004858 [10] [0x8000446e], PState.PSt 0x8000485a [10] [0x8000446e], PState.PSt 0x8000485c [10] [0x8000446e], PState.PSt 0x8000485e [10] [0x8000446e], PState.PSt 0x80004860 [9, 10] [0x8000446e], PState.PSt 0x80004862 [9, 10] [0x8000446e], PState.PSt 0x80004864 [9, 10] [0x8000446e], PState.PSt 0x8000197c [9, 10] [0x80004868, 0x8000446e], PState.PSt 0x8000197e [9, 10] [0x80004868, 0x8000446e], PState.PSt 0x80001980 [9, 10] [0x80004868, 0x8000446e], PState.PSt 0x80001982 [9, 10] [0x80004868, 0x8000446e]]⟩,
  ⟨0x80004476, false, [PState.PSt 0x8000447a [15] [], PState.PSt 0x8000447e [13, 15] [], PState.PSt 0x80004480 [13, 15] [], PState.PSt 0x80004482 [13, 15] []]⟩,
  ⟨0x80004492, false, [PState.PSt 0x80004494 [15] []]⟩,
  ⟨0x800044cc, false, [PState.PSt 0x800044d0 [15] []]⟩,
  ⟨0x800044f0, false, [PState.PSt 0x800044f2 [15] [], PState.PSt 0x800044f4 [15] []]⟩,
  ⟨0x80004528, true, [PState.PSt 0x8000452a [10] [], PState.PSt 0x80004730 [10] [0x8000452e], PState.PSt 0x80004732 [10] [0x8000452e], PState.PSt 0x80004734 [10] [0x8000452e], PState.PSt 0x80004736 [10] [0x8000452e], PState.PSt 0x80004738 [10] [0x8000452e], PState.PSt 0x8000473a [10] [0x8000452e], PState.PSt 0x8000473c [10] [0x8000452e], PState.PSt 0x8000473e [10] [0x8000452e], PState.PSt 0x80004740 [10] [0x8000452e], PState.PSt 0x80004742 [10] [0x8000452e], PState.PSt 0x80004744 [9, 10] [0x8000452e], PState.PSt 0x80004746 [9, 10] [0x8000452e], PState.PSt 0x80004748 [9, 10] [0x8000452e], PState.PSt 0x8000197c [9, 10] [0x8000474c, 0x8000452e], PState.PSt 0x8000197e [9, 10] [0x8000474c, 0x8000452e], PState.PSt 0x80001980 [9, 10] [0x8000474c, 0x8000452e], PState.PSt 0x80001982 [9, 10] [0x8000474c, 0x8000452e]]⟩,
  ⟨0x80004530, false, [PState.PSt 0x80004534 [15] [], PState.PSt 0x80004538 [13, 15] [], PState.PSt 0x8000453a [13, 15] [], PState.PSt 0x8000453c [13, 15] []]⟩,
  ⟨0x8000454c, false, [PState.PSt 0x8000454e [15] []]⟩,
  ⟨0x8000455c, true, [PState.PSt 0x80004560 [10] [], PState.PSt 0x80003352 [10] [0x80004564], PState.PSt 0x80003354 [10] [0x80004564], PState.PSt 0x80003356 [10] [0x80004564], PState.PSt 0x80003358 [10] [0x80004564], PState.PSt 0x8000335a [10] [0x80004564], PState.PSt 0x8000335c [10] [0x80004564]]⟩,
  ⟨0x80004566, false, [PState.PSt 0x8000456a [13] [], PState.PSt 0x8000456e [13] [], PState.PSt 0x80004570 [13] [], PState.PSt 0x80004574 [13] [], PState.PSt 0x8000381e [13] [0x80004578], PState.PSt 0x80003820 [13] [0x80004578]]⟩,
  ⟨0x80004570, false, [PState.PSt 0x80004574 [10] [], PState.PSt 0x8000381e [10] [0x80004578], PState.PSt 0x80003820 [15, 10] [0x80004578]]⟩,
  ⟨0x8000457e, false, [PState.PSt 0x80004582 [15] [], PState.PSt 0x80004584 [15] []]⟩,
  ⟨0x80004588, true, [PState.PSt 0x8000458c [10] [], PState.PSt 0x80003400 [10] [0x80004590], PState.PSt 0x80003402 [10] [0x80004590], PState.PSt 0x80003404 [10] [0x80004590], PState.PSt 0x80003406 [10] [0x80004590], PState.PSt 0x80003408 [10] [0x80004590], PState.PSt 0x8000340a [10] [0x80004590], PState.PSt 0x8000340c [10] [0x80004590]]⟩,
  ⟨0x8000465e, false, [PState.PSt 0x80004660 [15] []]⟩,
  ⟨0x80004664, false, [PState.PSt 0x80004666 [15] []]⟩
]

def walkRows8 : List WRow := [
  ⟨0x8000466a, false, [PState.PSt 0x8000466c [15] []]⟩,
  ⟨0x80004670, false, [PState.PSt 0x80004672 [15] []]⟩,
  ⟨0x80004676, false, [PState.PSt 0x8000467a [15] []]⟩,
  ⟨0x8000467e, false, [PState.PSt 0x80004682 [15] []]⟩,
  ⟨0x80004686, false, [PState.PSt 0x8000468a [15] []]⟩,
  ⟨0x8000468e, false, [PState.PSt 0x80004692 [15] []]⟩,
  ⟨0x8000469e, false, [PState.PSt 0x800046a0 [10] []]⟩,
  ⟨0x800046aa, false, [PState.PSt 0x800046ac [10] []]⟩,
  ⟨0x800046b2, false, [PState.PSt 0x800046b6 [15] [], PState.PSt 0x800046b8 [15] []]⟩,
  ⟨0x800046f6, false, [PState.PSt 0x800046fa [15] []]⟩,
  ⟨0x800046fc, false, [PState.PSt 0x80004700 [15] []]⟩,
  ⟨0x800047bc, false, [PState.PSt 0x800047c0 [15] []]⟩,
  ⟨0x800047ca, false, [PState.PSt 0x800047ce [15] [], PState.PSt 0x800047d2 [15] [], PState.PSt 0x800047d6 [15] []]⟩,
  ⟨0x800047ce, false, [PState.PSt 0x800047d2 [14] [], PState.PSt 0x800047d6 [14] []]⟩,
  ⟨0x800047f2, false, [PState.PSt 0x800047f6 [15] [], PState.PSt 0x800047fa [14, 15] []]⟩,
  ⟨0x80004804, false, [PState.PSt 0x80004808 [14] []]⟩,
  ⟨0x80004870, false, [PState.PSt 0x80004874 [14] [], PState.PSt 0x80004878 [14] [], PState.PSt 0x8000487c [14] []]⟩,
  ⟨0x80004874, false, [PState.PSt 0x80004878 [15] [], PState.PSt 0x8000487c [15] []]⟩,
  ⟨0x80004880, false, [PState.PSt 0x80004884 [15] []]⟩,
  ⟨0x800048a4, false, [PState.PSt 0x800048a8 [14] [], PState.PSt 0x800048ac [14] []]⟩,
  ⟨0x800048a8, false, [PState.PSt 0x800048ac [15] []]⟩,
  ⟨0x800048de, false, [PState.PSt 0x800048e2 [15] [], PState.PSt 0x800048e6 [15] []]⟩,
  ⟨0x800048e2, false, [PState.PSt 0x800048e6 [14] []]⟩,
  ⟨0x800048f0, false, [PState.PSt 0x800048f4 [15] []]⟩,
  ⟨0x8000490e, false, [PState.PSt 0x80004912 [15] [], PState.PSt 0x80004914 [15] []]⟩,
  ⟨0x800049c4, false, [PState.PSt 0x800049c8 [14] [], PState.PSt 0x800049cc [14] [], PState.PSt 0x800049d0 [14] []]⟩,
  ⟨0x80004a1a, false, [PState.PSt 0x80004a1e [15] []]⟩,
  ⟨0x80004a94, false, [PState.PSt 0x80004a98 [15] []]⟩,
  ⟨0x80004ab2, false, [PState.PSt 0x80004ab6 [15] [], PState.PSt 0x80004ab8 [15] []]⟩,
  ⟨0x80004abc, false, [PState.PSt 0x80004ac0 [9] [], PState.PSt 0x80004ac4 [9] []]⟩,
  ⟨0x80004ac0, false, [PState.PSt 0x80004ac4 [15] []]⟩,
  ⟨0x80004ac8, false, [PState.PSt 0x80004acc [15] [], PState.PSt 0x80004ace [9, 15] []]⟩,
  ⟨0x80004ad2, false, [PState.PSt 0x80004ad6 [14] [], PState.PSt 0x80004ad8 [15, 14] []]⟩,
  ⟨0x80004adc, true, [PState.PSt 0x80004ae0 [10] [], PState.PSt 0x80004950 [10] [0x80004ae4], PState.PSt 0x80004952 [10] [0x80004ae4], PState.PSt 0x80004954 [10] [0x80004ae4], PState.PSt 0x80004956 [10] [0x80004ae4], PState.PSt 0x80004958 [10] [0x80004ae4], PState.PSt 0x8000495a [15, 10] [0x80004ae4], PState.PSt 0x8000495e [15, 10] [0x80004ae4], PState.PSt 0x80004960 [15, 10] [0x80004ae4], PState.PSt 0x80004962 [15, 10] [0x80004ae4]]⟩,
  ⟨0x80004af8, false, [PState.PSt 0x80004afc [19] []]⟩,
  ⟨0x80004b00, false, [PState.PSt 0x80004b04 [24] [], PState.PSt 0x80004b08 [24] [], PState.PSt 0x80004b0a [24] [], PState.PSt 0x80004a66 [24] [], PState.PSt 0x80004a6a [24] [], PState.PSt 0x80004a6c [24] [], PState.PSt 0x80004a6e [11, 24] [], PState.PSt 0x80004a70 [11, 24] [], PState.PSt 0x80001048 [11, 24] [0x80004a74], PState.PSt 0x8000104a [11, 24] [0x80004a74], PState.PSt 0x8000104c [11, 24] [0x80004a74]]⟩,
  ⟨0x80004b78, false, [PState.PSt 0x80004b7c [15] [], PState.PSt 0x80004b7e [10, 15] []]⟩,
  ⟨0x80004b7c, false, [PState.PSt 0x80004b7e [10] []]⟩,
  ⟨0x80004b9c, true, [PState.PSt 0x80004ba0 [26] [], PState.PSt 0x80004ba4 [25, 26] [], PState.PSt 0x80004ba6 [10, 25, 26] [], PState.PSt 0x80000ea2 [10, 25, 26] [0x80004baa], PState.PSt 0x80000ea4 [10, 25, 26] [0x80004baa], PState.PSt 0x80000ea6 [10, 25, 26] [0x80004baa], PState.PSt 0x80000ea8 [10, 25, 26] [0x80004baa], PState.PSt 0x80000eaa [10, 25, 26] [0x80004baa], PState.PSt 0x80000eae [15, 10, 25, 26] [0x80004baa]]⟩,
  ⟨0x80004ba0, true, [PState.PSt 0x80004ba4 [25] [], PState.PSt 0x80004ba6 [10, 25] [], PState.PSt 0x80000ea2 [10, 25] [0x80004baa], PState.PSt 0x80000ea4 [10, 25] [0x80004baa], PState.PSt 0x80000ea6 [10, 25] [0x80004baa], PState.PSt 0x80000ea8 [10, 25] [0x80004baa], PState.PSt 0x80000eaa [10, 25] [0x80004baa], PState.PSt 0x80000eae [15, 10, 25] [0x80004baa]]⟩
]

def walkRows9 : List WRow := [
  ⟨0x80004bd2, false, [PState.PSt 0x80004bd6 [10] []]⟩,
  ⟨0x80004c0c, false, [PState.PSt 0x80004c10 [15] []]⟩,
  ⟨0x80004c14, false, [PState.PSt 0x80004c18 [15] [], PState.PSt 0x80004c1c [14, 15] []]⟩,
  ⟨0x80004c18, false, [PState.PSt 0x80004c1c [14] []]⟩,
  ⟨0x80004c2e, false, [PState.PSt 0x80004c32 [14] []]⟩,
  ⟨0x80004c58, false, [PState.PSt 0x80004c5c [15] [], PState.PSt 0x80004c60 [15] []]⟩,
  ⟨0x80004c5c, false, [PState.PSt 0x80004c60 [14] []]⟩,
  ⟨0x80004c62, false, [PState.PSt 0x80004c66 [15] []]⟩,
  ⟨0x80004c8e, true, [PState.PSt 0x80004c92 [11] [], PState.PSt 0x80004c94 [11] [], PState.PSt 0x80001ac8 [11] [0x80004c98], PState.PSt 0x80001aca [11] [0x80004c98], PState.PSt 0x80001acc [11] [0x80004c98], PState.PSt 0x80001ace [11] [0x80004c98], PState.PSt 0x80001ad0 [11] [0x80004c98], PState.PSt 0x80001ad2 [11] [0x80004c98], PState.PSt 0x80001ad4 [11] [0x80004c98], PState.PSt 0x80001ad6 [11] [0x80004c98], PState.PSt 0x80001ad8 [18, 11] [0x80004c98], PState.PSt 0x80001ada [18, 11] [0x80004c98], PState.PSt 0x80001adc [18, 11] [0x80004c98], PState.PSt 0x80001ae0 [18] [0x80004c98], PState.PSt 0x80001ae2 [18] [0x80004c98], PState.PSt 0x80001ae4 [18] [0x80004c98], PState.PSt 0x80001260 [18] [0x80001ae8, 0x80004c98], PState.PSt 0x80001262 [18] [0x80001ae8, 0x80004c98], PState.PSt 0x80001264 [18] [0x80001ae8, 0x80004c98], PState.PSt 0x80001266 [18] [0x80001ae8, 0x80004c98], PState.PSt 0x80001268 [18] [0x80001ae8, 0x80004c98], PState.PSt 0x8000126c [18] [0x80001ae8, 0x80004c98], PState.PSt 0x8000126e [18] [0x80001ae8, 0x80004c98], PState.PSt 0x8000128e [18] [0x80001ae8, 0x80004c98], PState.PSt 0x80001290 [18] [0x80001ae8, 0x80004c98]]⟩,
  ⟨0x80004ce2, false, [PState.PSt 0x80004ce6 [14] [], PState.PSt 0x80004ce8 [14] []]⟩,
  ⟨0x80004cf0, false, [PState.PSt 0x80004cf4 [14] [], PState.PSt 0x80004cf8 [15, 14] [], PState.PSt 0x80004cfc [15, 14] [], PState.PSt 0x80004cfe [10, 15, 14] [], PState.PSt 0x80004d00 [10, 15, 14] []]⟩,
  ⟨0x80004cfe, false, [PState.PSt 0x80004d00 [15] []]⟩,
  ⟨0x80004d3e, false, [PState.PSt 0x80004d40 [14] []]⟩,
  ⟨0x80004d8e, false, [PState.PSt 0x80004d92 [15] []]⟩,
  ⟨0x80004dc4, false, [PState.PSt 0x80004dc8 [15] [], PState.PSt 0x80004dca [15] [], PState.PSt 0x80004dcc [15] [], PState.PSt 0x80004dce [15] [], PState.PSt 0x80004dd0 [15] []]⟩,
  ⟨0x80004e98, false, [PState.PSt 0x80004e9c [15] [], PState.PSt 0x80004e9e [15] []]⟩,
  ⟨0x80004ee6, true, [PState.PSt 0x80004eea [9] [], PState.PSt 0x80004eec [10, 9] [], PState.PSt 0x80004d24 [10, 9] [0x80004ef0], PState.PSt 0x80004d26 [10, 9] [0x80004ef0], PState.PSt 0x80004d28 [10, 9] [0x80004ef0], PState.PSt 0x80004d2a [10, 9] [0x80004ef0]]⟩,
  ⟨0x80004f4c, true, [PState.PSt 0x80004f50 [10] [], PState.PSt 0x800043fe [10] [0x80004f54], PState.PSt 0x80004400 [10] [0x80004f54], PState.PSt 0x80004402 [10] [0x80004f54], PState.PSt 0x80004404 [10] [0x80004f54], PState.PSt 0x80004406 [10] [0x80004f54], PState.PSt 0x80004408 [10] [0x80004f54], PState.PSt 0x8000440c [15, 10] [0x80004f54]]⟩,
  ⟨0x80004f94, false, [PState.PSt 0x80004f98 [10] [], PState.PSt 0x800044cc [10] [0x80004f9c], PState.PSt 0x800044d0 [15, 10] [0x80004f9c]]⟩,
  ⟨0x80004fc4, false, [PState.PSt 0x80004fc8 [15] [], PState.PSt 0x80004fca [15] [], PState.PSt 0x80004fce [15] [], PState.PSt 0x80004fd0 [10, 15] []]⟩,
  ⟨0x80004fd4, true, [PState.PSt 0x80004fd8 [10] [], PState.PSt 0x800042d6 [10] [0x80004fdc], PState.PSt 0x800042d8 [10] [0x80004fdc], PState.PSt 0x800042da [10] [0x80004fdc], PState.PSt 0x800042dc [10] [0x80004fdc], PState.PSt 0x800042de [10] [0x80004fdc], PState.PSt 0x800042e0 [10] [0x80004fdc], PState.PSt 0x800042e2 [9, 10] [0x80004fdc], PState.PSt 0x800042e6 [9] [0x80004fdc], PState.PSt 0x800042ea [9] [0x80004fdc], PState.PSt 0x80000c58 [9] [0x800042ee, 0x80004fdc], PState.PSt 0x80000c5a [9] [0x800042ee, 0x80004fdc], PState.PSt 0x80000c5c [9] [0x800042ee, 0x80004fdc], PState.PSt 0x80000c5e [9] [0x800042ee, 0x80004fdc]]⟩,
  ⟨0x80005012, true, [PState.PSt 0x80005016 [10] [], PState.PSt 0x80004398 [10] [0x8000501a], PState.PSt 0x8000439a [10] [0x8000501a], PState.PSt 0x8000439c [10] [0x8000501a], PState.PSt 0x8000439e [10] [0x8000501a], PState.PSt 0x800043a0 [10] [0x8000501a], PState.PSt 0x800043a2 [10] [0x8000501a], PState.PSt 0x800043a4 [10] [0x8000501a], PState.PSt 0x800043a6 [9, 10] [0x8000501a], PState.PSt 0x800043a8 [9, 10] [0x8000501a], PState.PSt 0x8000197c [9, 10] [0x800043ac, 0x8000501a], PState.PSt 0x8000197e [9, 10] [0x800043ac, 0x8000501a], PState.PSt 0x80001980 [9, 10] [0x800043ac, 0x8000501a], PState.PSt 0x80001982 [9, 10] [0x800043ac, 0x8000501a]]⟩,
  ⟨0x80005068, false, [PState.PSt 0x8000506c [14] [], PState.PSt 0x8000506e [14] []]⟩,
  ⟨0x80005072, false, [PState.PSt 0x80005076 [15] [], PState.PSt 0x80005078 [15] [], PState.PSt 0x8000507a [15] []]⟩,
  ⟨0x800050a6, false, [PState.PSt 0x800050aa [15] []]⟩,
  ⟨0x800050ae, false, [PState.PSt 0x800050b2 [14] [], PState.PSt 0x800050b4 [14] []]⟩,
  ⟨0x800050b2, false, [PState.PSt 0x800050b4 [15] []]⟩,
  ⟨0x8000511c, false, [PState.PSt 0x80005120 [15] [], PState.PSt 0x80005122 [15] []]⟩,
  ⟨0x800051be, false, [PState.PSt 0x800051c2 [15] []]⟩,
  ⟨0x800051c6, false, [PState.PSt 0x800051ca [14] [], PState.PSt 0x800051cc [14] []]⟩,
  ⟨0x800051e0, false, [PState.PSt 0x800051e4 [13] [], PState.PSt 0x800051e6 [13] [], PState.PSt 0x800051e8 [13] [], PState.PSt 0x800051ea [13] [], PState.PSt 0x8000381e [13] [0x800051ee], PState.PSt 0x80003820 [13] [0x800051ee]]⟩,
  ⟨0x800051f4, false, [PState.PSt 0x800051f8 [14] [], PState.PSt 0x800051fa [14] []]⟩,
  ⟨0x80005204, false, [PState.PSt 0x80005208 [15] [], PState.PSt 0x8000520a [15] []]⟩,
  ⟨0x8000523e, false, [PState.PSt 0x80005242 [14] [], PState.PSt 0x80005246 [14] []]⟩,
  ⟨0x80005262, false, [PState.PSt 0x80005266 [15] []]⟩,
  ⟨0x8000526a, false, [PState.PSt 0x8000526e [15] []]⟩,
  ⟨0x8000528c, false, [PState.PSt 0x80005290 [15] [], PState.PSt 0x80005292 [15] []]⟩,
  ⟨0x800052f4, false, [PState.PSt 0x800052f8 [15] [], PState.PSt 0x800052fc [15] []]⟩,
  ⟨0x80005310, false, [PState.PSt 0x80005314 [14] [], PState.PSt 0x80005316 [14] []]⟩,
  ⟨0x8000531a, false, [PState.PSt 0x8000531e [14] [], PState.PSt 0x80005320 [14] []]⟩
]

def walkRows10 : List WRow := [
  ⟨0x8000533a, false, [PState.PSt 0x8000533e [14] [], PState.PSt 0x80005340 [14] []]⟩,
  ⟨0x80005352, false, [PState.PSt 0x80005356 [15] [], PState.PSt 0x8000535a [14, 15] [], PState.PSt 0x8000535e [14, 15] []]⟩,
  ⟨0x80005374, false, [PState.PSt 0x80005378 [14] [], PState.PSt 0x8000537a [14] []]⟩,
  ⟨0x800053b2, false, [PState.PSt 0x800053b6 [14] [], PState.PSt 0x800053b8 [14] []]⟩,
  ⟨0x800053bc, false, [PState.PSt 0x800053c0 [15] []]⟩,
  ⟨0x8000540a, false, [PState.PSt 0x8000540e [15] []]⟩,
  ⟨0x800054fc, false, [PState.PSt 0x80005500 [14] [], PState.PSt 0x80005502 [14] []]⟩,
  ⟨0x8000550c, true, [PState.PSt 0x80005510 [10] [], PState.PSt 0x800034d4 [10] [0x80005514], PState.PSt 0x800034d6 [10] [0x80005514], PState.PSt 0x800034d8 [10] [0x80005514], PState.PSt 0x800034da [10] [0x80005514], PState.PSt 0x800034dc [10] [0x80005514], PState.PSt 0x800034de [10] [0x80005514], PState.PSt 0x800034e0 [9, 10] [0x80005514], PState.PSt 0x800034e4 [9] [0x80005514], PState.PSt 0x800034e8 [9] [0x80005514], PState.PSt 0x80000c58 [9] [0x800034ec, 0x80005514], PState.PSt 0x80000c5a [9] [0x800034ec, 0x80005514], PState.PSt 0x80000c5c [9] [0x800034ec, 0x80005514], PState.PSt 0x80000c5e [9] [0x800034ec, 0x80005514]]⟩,
  ⟨0x8000557c, false, [PState.PSt 0x80005580 [14] [], PState.PSt 0x80005582 [14] []]⟩,
  ⟨0x8000558c, true, [PState.PSt 0x80005590 [10] [], PState.PSt 0x800034d4 [10] [0x80005594], PState.PSt 0x800034d6 [10] [0x80005594], PState.PSt 0x800034d8 [10] [0x80005594], PState.PSt 0x800034da [10] [0x80005594], PState.PSt 0x800034dc [10] [0x80005594], PState.PSt 0x800034de [10] [0x80005594], PState.PSt 0x800034e0 [9, 10] [0x80005594], PState.PSt 0x800034e4 [9] [0x80005594], PState.PSt 0x800034e8 [9] [0x80005594], PState.PSt 0x80000c58 [9] [0x800034ec, 0x80005594], PState.PSt 0x80000c5a [9] [0x800034ec, 0x80005594], PState.PSt 0x80000c5c [9] [0x800034ec, 0x80005594], PState.PSt 0x80000c5e [9] [0x800034ec, 0x80005594]]⟩,
  ⟨0x80005620, true, [PState.PSt 0x80005624 [15] [], PState.PSt 0x80005626 [10, 15] [], PState.PSt 0x800028aa [10, 15] [0x8000562a], PState.PSt 0x800028ac [10, 15] [0x8000562a], PState.PSt 0x800028ae [10, 15] [0x8000562a], PState.PSt 0x800028b0 [10, 15] [0x8000562a], PState.PSt 0x800028b2 [10, 15] [0x8000562a], PState.PSt 0x800028b4 [10, 15] [0x8000562a], PState.PSt 0x800028b6 [10, 15] [0x8000562a], PState.PSt 0x800028b8 [9, 10, 15] [0x8000562a], PState.PSt 0x800028ba [9, 10, 15] [0x8000562a], PState.PSt 0x8000197c [9, 10, 15] [0x800028be, 0x8000562a], PState.PSt 0x8000197e [9, 10, 15] [0x800028be, 0x8000562a], PState.PSt 0x80001980 [9, 10, 15] [0x800028be, 0x8000562a], PState.PSt 0x80001982 [9, 10, 15] [0x800028be, 0x8000562a]]⟩,
  ⟨0x8000562e, false, [PState.PSt 0x80005632 [15] []]⟩,
  ⟨0x8000565a, false, [PState.PSt 0x8000565c [10] []]⟩,
  ⟨0x80005698, false, [PState.PSt 0x8000569a [10] []]⟩,
  ⟨0x80005700, true, [PState.PSt 0x80005704 [10] [], PState.PSt 0x80004d24 [10] [0x80005708], PState.PSt 0x80004d26 [10] [0x80005708], PState.PSt 0x80004d28 [10] [0x80005708], PState.PSt 0x80004d2a [10] [0x80005708], PState.PSt 0x80004d2c [10] [0x80005708], PState.PSt 0x80004d2e [10] [0x80005708], PState.PSt 0x80004d30 [9, 10] [0x80005708], PState.PSt 0x8000197c [9, 10] [0x80004d34, 0x80005708], PState.PSt 0x8000197e [9, 10] [0x80004d34, 0x80005708], PState.PSt 0x80001980 [9, 10] [0x80004d34, 0x80005708], PState.PSt 0x80001982 [9, 10] [0x80004d34, 0x80005708]]⟩,
  ⟨0x80005710, true, [PState.PSt 0x80005714 [10] [], PState.PSt 0x80004d24 [10] [0x80005718], PState.PSt 0x80004d26 [10] [0x80005718], PState.PSt 0x80004d28 [10] [0x80005718], PState.PSt 0x80004d2a [10] [0x80005718], PState.PSt 0x80004d2c [10] [0x80005718], PState.PSt 0x80004d2e [10] [0x80005718], PState.PSt 0x80004d30 [9, 10] [0x80005718], PState.PSt 0x8000197c [9, 10] [0x80004d34, 0x80005718], PState.PSt 0x8000197e [9, 10] [0x80004d34, 0x80005718], PState.PSt 0x80001980 [9, 10] [0x80004d34, 0x80005718], PState.PSt 0x80001982 [9, 10] [0x80004d34, 0x80005718]]⟩,
  ⟨0x80005750, false, [PState.PSt 0x80005754 [15] [], PState.PSt 0x80005756 [15] [], PState.PSt 0x8000575a [15] [], PState.PSt 0x8000575c [15] []]⟩,
  ⟨0x80005760, false, [PState.PSt 0x80005764 [15] [], PState.PSt 0x80005766 [15] [], PState.PSt 0x8000576a [15] [], PState.PSt 0x8000576c [9, 15] []]⟩,
  ⟨0x80005770, true, [PState.PSt 0x80005774 [10] [], PState.PSt 0x800042d6 [10] [0x80005778], PState.PSt 0x800042d8 [10] [0x80005778], PState.PSt 0x800042da [10] [0x80005778], PState.PSt 0x800042dc [10] [0x80005778], PState.PSt 0x800042de [10] [0x80005778], PState.PSt 0x800042e0 [10] [0x80005778], PState.PSt 0x800042e2 [9, 10] [0x80005778], PState.PSt 0x800042e6 [9] [0x80005778], PState.PSt 0x800042ea [9] [0x80005778], PState.PSt 0x80000c58 [9] [0x800042ee, 0x80005778], PState.PSt 0x80000c5a [9] [0x800042ee, 0x80005778], PState.PSt 0x80000c5c [9] [0x800042ee, 0x80005778], PState.PSt 0x80000c5e [9] [0x800042ee, 0x80005778]]⟩,
  ⟨0x80005778, true, [PState.PSt 0x8000577c [10] [], PState.PSt 0x800042d6 [10] [0x80005780], PState.PSt 0x800042d8 [10] [0x80005780], PState.PSt 0x800042da [10] [0x80005780], PState.PSt 0x800042dc [10] [0x80005780], PState.PSt 0x800042de [10] [0x80005780], PState.PSt 0x800042e0 [10] [0x80005780], PState.PSt 0x800042e2 [9, 10] [0x80005780], PState.PSt 0x800042e6 [9] [0x80005780], PState.PSt 0x800042ea [9] [0x80005780], PState.PSt 0x80000c58 [9] [0x800042ee, 0x80005780], PState.PSt 0x80000c5a [9] [0x800042ee, 0x80005780], PState.PSt 0x80000c5c [9] [0x800042ee, 0x80005780], PState.PSt 0x80000c5e [9] [0x800042ee, 0x80005780]]⟩,
  ⟨0x80005784, false, [PState.PSt 0x80005788 [15] []]⟩,
  ⟨0x80005798, true, [PState.PSt 0x8000579c [10] [], PState.PSt 0x800042d6 [10] [0x800057a0], PState.PSt 0x800042d8 [10] [0x800057a0], PState.PSt 0x800042da [10] [0x800057a0], PState.PSt 0x800042dc [10] [0x800057a0], PState.PSt 0x800042de [10] [0x800057a0], PState.PSt 0x800042e0 [10] [0x800057a0], PState.PSt 0x800042e2 [9, 10] [0x800057a0], PState.PSt 0x800042e6 [9] [0x800057a0], PState.PSt 0x800042ea [9] [0x800057a0], PState.PSt 0x80000c58 [9] [0x800042ee, 0x800057a0], PState.PSt 0x80000c5a [9] [0x800042ee, 0x800057a0], PState.PSt 0x80000c5c [9] [0x800042ee, 0x800057a0], PState.PSt 0x80000c5e [9] [0x800042ee, 0x800057a0]]⟩,
  ⟨0x800057a0, true, [PState.PSt 0x800057a4 [10] [], PState.PSt 0x800042d6 [10] [0x800057a8], PState.PSt 0x800042d8 [10] [0x800057a8], PState.PSt 0x800042da [10] [0x800057a8], PState.PSt 0x800042dc [10] [0x800057a8], PState.PSt 0x800042de [10] [0x800057a8], PState.PSt 0x800042e0 [10] [0x800057a8], PState.PSt 0x800042e2 [9, 10] [0x800057a8], PState.PSt 0x800042e6 [9] [0x800057a8], PState.PSt 0x800042ea [9] [0x800057a8], PState.PSt 0x80000c58 [9] [0x800042ee, 0x800057a8], PState.PSt 0x80000c5a [9] [0x800042ee, 0x800057a8], PState.PSt 0x80000c5c [9] [0x800042ee, 0x800057a8], PState.PSt 0x80000c5e [9] [0x800042ee, 0x800057a8]]⟩,
  ⟨0x800058ce, false, [PState.PSt 0x800058d2 [15] []]⟩,
  ⟨0x800058e0, false, [PState.PSt 0x800058e2 [14] [], PState.PSt 0x800058e4 [14] []]⟩,
  ⟨0x800058e8, false, [PState.PSt 0x800058ea [14] [], PState.PSt 0x800058ec [14] []]⟩,
  ⟨0x80005950, false, [PState.PSt 0x80005952 [14] [], PState.PSt 0x80005954 [14] [], PState.PSt 0x80005958 [14] [], PState.PSt 0x8000595c [14] []]⟩,
  ⟨0x80005964, false, [PState.PSt 0x80005966 [15] [], PState.PSt 0x80005968 [15] [], PState.PSt 0x8000596a [15] []]⟩,
  ⟨0x80005972, false, [PState.PSt 0x80005974 [15] [], PState.PSt 0x80005976 [15] []]⟩,
  ⟨0x8000597e, false, [PState.PSt 0x80005980 [14] [], PState.PSt 0x80005982 [14] [], PState.PSt 0x80005986 [14] [], PState.PSt 0x8000598a [14] []]⟩,
  ⟨0x800059a2, false, [PState.PSt 0x800059a4 [14] [], PState.PSt 0x800059a8 [14] [], PState.PSt 0x800059ac [14] [], PState.PSt 0x800059ae [14] [], PState.PSt 0x800059b2 [14] []]⟩,
  ⟨0x800059bc, false, [PState.PSt 0x800059be [15] [], PState.PSt 0x800059c2 [18, 15] [], PState.PSt 0x800059c4 [18, 15] []]⟩,
  ⟨0x800059d0, false, [PState.PSt 0x800059d2 [15] [], PState.PSt 0x800059d4 [15] []]⟩,
  ⟨0x800059dc, false, [PState.PSt 0x800059de [15] [], PState.PSt 0x800059e0 [15] []]⟩,
  ⟨0x80005a06, false, [PState.PSt 0x80005a08 [10] []]⟩,
  ⟨0x80005a10, false, [PState.PSt 0x80005a14 [14] []]⟩,
  ⟨0x80005a44, false, [PState.PSt 0x80005a46 [14] []]⟩,
  ⟨0x80005a4a, false, [PState.PSt 0x80005a4c [14] []]⟩,
  ⟨0x80005a50, false, [PState.PSt 0x80005a52 [15] [], PState.PSt 0x80005a56 [13, 15] [], PState.PSt 0x80005a5a [13, 15] []]⟩,
  ⟨0x80005a64, false, [PState.PSt 0x80005a66 [15] [], PState.PSt 0x80005a6a [13, 15] []]⟩
]

def walkRows11 : List WRow := [
  ⟨0x80005b5c, false, [PState.PSt 0x80005b60 [13] []]⟩,
  ⟨0x80005b72, true, [PState.PSt 0x80005b76 [10] [], PState.PSt 0x800058b6 [10] [0x80005b7a], PState.PSt 0x800058b8 [10] [0x80005b7a], PState.PSt 0x800058ba [10] [0x80005b7a], PState.PSt 0x800058bc [10] [0x80005b7a], PState.PSt 0x800058be [10] [0x80005b7a], PState.PSt 0x800058c0 [10] [0x80005b7a]]⟩,
  ⟨0x80005b80, true, [PState.PSt 0x80005b84 [10] [], PState.PSt 0x800058b6 [10] [0x80005b88], PState.PSt 0x800058b8 [10] [0x80005b88], PState.PSt 0x800058ba [10] [0x80005b88], PState.PSt 0x800058bc [10] [0x80005b88], PState.PSt 0x800058be [10] [0x80005b88], PState.PSt 0x800058c0 [10] [0x80005b88]]⟩,
  ⟨0x80005bb8, false, [PState.PSt 0x80005bbc [10] [], PState.PSt 0x80005bc0 [13, 10] [], PState.PSt 0x80005bc4 [13, 10] [], PState.PSt 0x80005bc8 [13, 10] [], PState.PSt 0x80005bcc [14, 13, 10] [], PState.PSt 0x80005bd0 [14, 13, 10] [], PState.PSt 0x80005bd2 [14, 13, 10] [], PState.PSt 0x80005bd6 [14, 13, 10] []]⟩,
  ⟨0x80005be0, false, [PState.PSt 0x80005be2 [14] [], PState.PSt 0x80005be4 [14] [], PState.PSt 0x80005be8 [14] [], PState.PSt 0x80005bea [14] []]⟩,
  ⟨0x80005bec, false, [PState.PSt 0x80005bee [12] [], PState.PSt 0x80005bf2 [16, 12] [], PState.PSt 0x80005bf4 [16, 12] []]⟩,
  ⟨0x80005bfe, false, [PState.PSt 0x80005c02 [14] []]⟩,
  ⟨0x80005c12, false, [PState.PSt 0x80005c16 [17] [], PState.PSt 0x80005c18 [14, 17] [], PState.PSt 0x80005c1c [14, 17] []]⟩,
  ⟨0x80005c2c, false, [PState.PSt 0x80005c30 [12] []]⟩,
  ⟨0x80005c52, false, [PState.PSt 0x80005c54 [14] [], PState.PSt 0x80005c56 [14] []]⟩,
  ⟨0x80005c6a, false, [PState.PSt 0x80005c6c [13] [], PState.PSt 0x80005c70 [14, 13] [], PState.PSt 0x80005c72 [14, 13] [], PState.PSt 0x80005c74 [14, 13] [], PState.PSt 0x80005c76 [14, 13] []]⟩,
  ⟨0x80005c6c, false, [PState.PSt 0x80005c70 [14] [], PState.PSt 0x80005c72 [14] [], PState.PSt 0x80005c74 [14] [], PState.PSt 0x80005c76 [13, 14] []]⟩,
  ⟨0x80005c7e, false, [PState.PSt 0x80005c80 [14] [], PState.PSt 0x80005c84 [15, 14] [], PState.PSt 0x80005c86 [15, 14] []]⟩,
  ⟨0x80005c80, false, [PState.PSt 0x80005c84 [15] [], PState.PSt 0x80005c86 [15] []]⟩,
  ⟨0x80005c96, false, [PState.PSt 0x80005c9a [15] [], PState.PSt 0x80005c9e [15] [], PState.PSt 0x80005ca2 [15] [], PState.PSt 0x80005ca4 [15] []]⟩,
  ⟨0x80005cbe, false, [PState.PSt 0x80005cc2 [15] []]⟩,
  ⟨0x80005cc6, false, [PState.PSt 0x80005cca [18] [], PState.PSt 0x80005cce [14, 18] [], PState.PSt 0x80005cd2 [14, 18] [], PState.PSt 0x80005cd6 [14, 18] [], PState.PSt 0x80005cda [14, 18] [], PState.PSt 0x80005cdc [15, 14, 18] []]⟩,
  ⟨0x80005d4a, false, [PState.PSt 0x80005d4c [15] [], PState.PSt 0x80005d4e [15] [], PState.PSt 0x80005d52 [15] []]⟩,
  ⟨0x80005d58, false, [PState.PSt 0x80005d5a [15] [], PState.PSt 0x80005d5e [15] [], PState.PSt 0x80005d62 [15] []]⟩,
  ⟨0x80005d5a, false, [PState.PSt 0x80005d5e [14] [], PState.PSt 0x80005d62 [14] []]⟩,
  ⟨0x80005d5e, false, [PState.PSt 0x80005d62 [15] []]⟩,
  ⟨0x80005d6a, false, [PState.PSt 0x80005d6c [14] [], PState.PSt 0x80005d70 [14] [], PState.PSt 0x80005d72 [14] [], PState.PSt 0x80005d74 [14] [], PState.PSt 0x80005d76 [15, 14] [], PState.PSt 0x80005d78 [15, 14] [], PState.PSt 0x80005d7c [15, 14] [], PState.PSt 0x80005d80 [15, 14] [], PState.PSt 0x80005d82 [15, 14] [], PState.PSt 0x80005d86 [15, 14] []]⟩,
  ⟨0x80005d6c, false, [PState.PSt 0x80005d70 [15] [], PState.PSt 0x80005d72 [15] [], PState.PSt 0x80005d74 [15] [], PState.PSt 0x80005d76 [15] [], PState.PSt 0x80005d78 [15] [], PState.PSt 0x80005d7c [14, 15] [], PState.PSt 0x80005d80 [14, 15] [], PState.PSt 0x80005d82 [14, 15] [], PState.PSt 0x80005d86 [14, 15] []]⟩,
  ⟨0x80005d76, false, [PState.PSt 0x80005d78 [15] [], PState.PSt 0x80005d7c [14, 15] [], PState.PSt 0x80005d80 [14, 15] [], PState.PSt 0x80005d82 [14, 15] [], PState.PSt 0x80005d86 [14, 15] []]⟩,
  ⟨0x80005d82, false, [PState.PSt 0x80005d86 [14] []]⟩,
  ⟨0x80005d90, false, [PState.PSt 0x80005d92 [10] []]⟩,
  ⟨0x80005d9a, false, [PState.PSt 0x80005d9e [15] [], PState.PSt 0x80005da0 [15] [], PState.PSt 0x80005da2 [15] [], PState.PSt 0x80005da4 [15] []]⟩,
  ⟨0x80005da8, false, [PState.PSt 0x80005daa [14] [], PState.PSt 0x80005dae [14] []]⟩,
  ⟨0x80005daa, false, [PState.PSt 0x80005dae [14] []]⟩
]

/-- THE WALK-STATE TABLE: per walk-certifying row of `pinsW9a`, in table order, the
load pc, the `own` bit and the states the all-paths search visits. -/
def walkRows : List WRow :=
  walkRows0 ++ walkRows1 ++ walkRows2 ++ walkRows3 ++ walkRows4 ++ walkRows5 ++ walkRows6 ++ walkRows7 ++ walkRows8 ++ walkRows9 ++ walkRows10 ++ walkRows11

theorem walkRowsOk0 : walkRows0.all rowOk = true := by decide +kernel
theorem walkRowsOk1 : walkRows1.all rowOk = true := by decide +kernel
theorem walkRowsOk2 : walkRows2.all rowOk = true := by decide +kernel
theorem walkRowsOk3 : walkRows3.all rowOk = true := by decide +kernel
theorem walkRowsOk4 : walkRows4.all rowOk = true := by decide +kernel
theorem walkRowsOk5 : walkRows5.all rowOk = true := by decide +kernel
theorem walkRowsOk6 : walkRows6.all rowOk = true := by decide +kernel
theorem walkRowsOk7 : walkRows7.all rowOk = true := by decide +kernel
theorem walkRowsOk8 : walkRows8.all rowOk = true := by decide +kernel
theorem walkRowsOk9 : walkRows9.all rowOk = true := by decide +kernel
theorem walkRowsOk10 : walkRows10.all rowOk = true := by decide +kernel
theorem walkRowsOk11 : walkRows11.all rowOk = true := by decide +kernel

/-- Every row of the table passes the closure and per-state checks. -/
theorem walkRowsOk : walkRows.all rowOk = true := by
  simp only [walkRows, List.all_append, walkRowsOk0, walkRowsOk1, walkRowsOk2, walkRowsOk3, walkRowsOk4, walkRowsOk5, walkRowsOk6, walkRowsOk7, walkRowsOk8, walkRowsOk9, walkRowsOk10, walkRowsOk11, Bool.and_self]
-- END GENERATED

/-! ## 3. What the table gives -/

/-- The table's rows are exactly the walk-certifying rows of `pinsW9a`. -/
theorem walkRowsCover :
    walkRows.map (fun r => (r.wPc, r.wOwn)) =
      pinsW9a.filterMap (fun p => (walkOwn p.2).map (fun o => (p.1, o))) := by
  decide +kernel

theorem PinWalkTab.closedReach (own : Bool) (sts : List PState)
    (hcl : ∀ s, s ∈ sts → closedb own sts s = true) :
    ∀ s x n, preach own s x n → s ∈ sts → x ∈ sts := by
  intro s x n h
  induction h with
  | prRefl s => exact id
  | prStep s s' x l n hp hm _ ih =>
    intro hs
    apply ih
    have hc := hcl s hs
    unfold closedb at hc
    rw [hp] at hc
    obtain ⟨y, hy, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc s' hm)
    rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ he]
    exact hy

/-- A checked row's states contain everything the walk reaches, and each passes `stOk`. -/
theorem PinWalkTab.rowReach (r : WRow) (h : rowOk r = true) :
    ∀ x n, preach r.wOwn (pinStart r.wPc) x n → stOk r.wOwn x = true := by
  intro x n hx
  unfold rowOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp h0
  have hst : pinStart r.wPc ∈ r.wSts := by
    rw [WeakRvwmoPinBridge3.pstateEqbEq _ _ he]; exact hy
  have hall := List.all_eq_true.mp h1
  have hx' := PinWalkTab.closedReach r.wOwn r.wSts
    (fun s hs => (Bool.and_eq_true _ _ ▸ hall s hs).2) _ x n hx hst
  exact (Bool.and_eq_true _ _ ▸ hall x hx').1

/-- **EVERY STATE THE WALK OF A CLAIMED SITE REACHES PASSES THE PER-STATE CHECK** (header). -/
theorem walkReach (pc : Int) (w : Pin) (own : Bool) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own →
    ∀ x n, preach own (pinStart pc) x n → stOk own x = true := by
  intro hm hw x n hx
  have hin : (pc, own) ∈ walkRows.map (fun r => (r.wPc, r.wOwn)) := by
    rw [walkRowsCover]
    exact List.mem_filterMap.2 ⟨(pc, w), hm, by simp [hw]⟩
  obtain ⟨r, hr, he⟩ := List.mem_map.1 hin
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact PinWalkTab.rowReach r (List.all_eq_true.mp walkRowsOk r hr) x n hx

/-- The certifying classes carry their `own` bit. -/
theorem PinWalkTab.walkOwnOf (pc' : Int) (own : Bool) (w : Pin) :
    (w = .PDep pc' own ∨ w = .PCtrl pc' own ∨ w = .PFence pc' own) → walkOwn w = some own := by
  rintro (rfl | rfl | rfl) <;> rfl

theorem PinWalkTab.taintMemContains (r : Nat) (t : List Nat) : taintMem r t = true → r ∈ t := by
  induction t with
  | nil => intro h; cases h
  | cons x t ih =>
    intro h
    simp only [taintMem, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.eq_of_beq_eq_true h]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

/-- (i) THE TAINT AVOIDS `stimecmp` at every reached state (B2's `texcFree`, conjunct one). -/
theorem walkPres (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    ∀ r, taintMem r x.psT = true → r ∈ presRegs := by
  intro hm hw hx r hr
  have h := walkReach pc w own hm hw x n hx
  unfold stOk at h
  rw [Bool.and_eq_true] at h
  have hp := List.all_eq_true.mp h.1 r (PinWalkTab.taintMemContains r _ hr)
  exact List.contains_iff_mem.mp hp

/-- The non-pin half of the per-state check. -/
theorem PinWalkTab.stOkStep (own : Bool) (x : PState) (l : List PState) :
    stOk own x = true → pstep own x = some l → l ≠ [] →
    (textLo ≤ x.psPc ∧ x.psPc + 3 < textHi) ∧ decOk x.psPc = true ∧ ctlOk x.psPc = true ∧
      ∀ s', s' ∈ l → taintSubb s'.psT (taintStep x.psT x.psPc) = true := by
  intro h hp hne
  unfold stOk at h
  rw [hp, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases l with
  | nil => exact absurd rfl hne
  | cons a l =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h0, h0'⟩, h1⟩, h2⟩, h3⟩ := h
    exact ⟨⟨h0, h0'⟩, h1, h2, fun s' hs => List.all_eq_true.mp h3 s' hs⟩

/-- (ii) THE DECODED INSTRUCTION PASSES B1's CHECK at every reached non-pin state. -/
theorem walkDec (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → l ≠ [] →
    ∃ a, decS x.psPc = some a ∧ PinDataflow.dfInstrOkB5 (krole x.psPc) a = true := by
  intro hm hw hx hp hne
  have h := (PinWalkTab.stOkStep own x l (walkReach pc w own hm hw x n hx) hp hne).2.1
  unfold decOk at h
  cases hd : decS x.psPc with
  | none => rw [hd] at h; cases h
  | some a => rw [hd] at h; exact ⟨a, rfl, h⟩

/-- (iii) THE DECODED CONTROL CLASS IS THE CHECKER'S at every reached non-pin state. -/
theorem walkFlow (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → l ≠ [] →
    ∃ a, decS x.psPc = some a ∧ astFlow x.psPc a = kflowOf x.psPc := by
  intro hm hw hx hp hne
  have h := (PinWalkTab.stOkStep own x l (walkReach pc w own hm hw x n hx) hp hne).2.2.1
  unfold ctlOk at h
  cases hd : decS x.psPc with
  | none => rw [hd] at h; cases h
  | some a => rw [hd] at h; exact ⟨a, rfl, beq_iff_eq.mp h⟩

/-- (iv) EVERY SUCCESSOR's taint is below the decoded update (`reachesA`'s `taintSub`). -/
theorem walkTaint (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState)
    (s' : PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → s' ∈ l → taintSub s'.psT (taintStep x.psT x.psPc) := by
  intro hm hw hx hp hs r hr
  have hne : l ≠ [] := by rintro rfl; cases hs
  have h := (PinWalkTab.stOkStep own x l (walkReach pc w own hm hw x n hx) hp hne).2.2.2 s' hs
  exact List.all_eq_true.mp h r (PinWalkTab.taintMemContains r _ hr)

/-- (v) EVERY REACHED NON-PIN STATE's instruction lies in the text, all four bytes (B4's arms). -/
theorem walkText (pc : Int) (w : Pin) (own : Bool) (x : PState) (n : Nat) (l : List PState) :
    (pc, w) ∈ pinsW9a → walkOwn w = some own → preach own (pinStart pc) x n →
    pstep own x = some l → l ≠ [] → textLo ≤ x.psPc ∧ x.psPc + 3 < textHi :=
  fun hm hw hx hp hne => (PinWalkTab.stOkStep own x l (walkReach pc w own hm hw x n hx) hp hne).1

/-! ## 4. The census states (B2's carry table) -/

set_option maxRecDepth 100000 in
/-- **`texcM`'s per-state content**: at every fence-free trap-path state of the carry table the
decoded instruction passes B1's per-word check. -/
theorem trapDecOk : trapFlow.all (fun r => decOk r.1.tPc) = true := by
  decide +kernel

end Weak
