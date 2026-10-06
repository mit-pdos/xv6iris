/-
Weak: **RVWMO's syntactic operand roles, decoded from the instruction bits** (stage D3).

Rocq: `iris/WeakDeps.v` @ xxvzwolszwmp (1cc222280).

Rocq header (verbatim, Rocq vocabulary; the one edit: the S-slash-M alias pair is spelled `S-&M-`, since a
dash followed by a slash would close this comment):

    (** * WeakDeps.v — RVWMO's SYNTACTIC OPERAND ROLES, decoded from the bits

        Design: [claude-notes/design/weak-memory-deps.md] §2.4/§2.5 (stage D3).

        RVWMO defines a syntactic dependency on the instruction's ENCODING — WHICH
        integer register fields it reads and writes — not on the Sail node stream
        (which shows [RegRead]/[RegWrite]/[MemRead] but never says which register
        a memory address was computed from; Sail's pure code between nodes is
        opaque, and "every register read so far" is the WRONG polarity).  So the
        program step reads the announced instruction bits
        ([Interface.InstrAnnounce], live in the model since the [-D SYMBOLIC]
        regeneration) and calls the PURE decoder below.

        ------------------------------------------------------------------------
        WHAT IT COVERS, and what it deliberately does not.

        Covered: base RV64I (R/I/S/B/U/J: loads, stores, branches, [jal],
        [jalr], the ALU forms), M (they are R-format [OP]/[OP-32]), A (the AMOs,
        [lr] and [sc]), Zicsr, and the C extension forms xv6 contains.

        NOT covered — every one returns [ORnone], which is the SAFE
        UNDER-approximation (deviation D-4: fewer dependencies = MORE behaviors =
        free for containment):
          - CSR-mediated chains ([SYSTEM]): RVWMO's syntactic dependency is on
            the integer/FP source registers, and a CSR is neither;
          - the F/D floating-point forms (xv6 executes none in the kernel);
          - anything unrecognised, including a malformed word.

        [x0] is NEVER a source and NEVER a destination: it is hardwired to zero,
        so no value flows through it.  The decoder returns register NUMBERS
        (0..31); [wreg_of_num] drops [0], which is what implements that rule.

        ------------------------------------------------------------------------
        RECORDED DECODER DEVIATIONS.

        (DEC-1) [c.jal] is RV32-only.  At [op = 01, funct3 = 001] an RV64 hart
          decodes [c.addiw], and this decoder does likewise.  The stage brief
          lists [c.jal]; on [rv64d] the encoding simply is not that instruction.
          Both roles happen to write [rd] and neither carries a memory operand,
          so no dependency edge differs.

        (DEC-2) An AMO's [rd] takes role [ORamo]'s destination, whose source list
          is [[DLdRes]] — the READ half's post-view (PARM's [res]).  [sc]'s [rd]
          is the success flag, which PARM gives the exclusive write's timestamp
          view; we give it the read half's, which is SMALLER (the read is ordered
          before the write by the machine), hence WEAKER — free.

        (DEC-3) [auipc]/[lui] have NO register source: their result is
          PC-derived or immediate.  [jal]/[jalr]'s link value likewise (D-4), so
          [ORjal]/[ORjalr] contribute a destination with an EMPTY source list —
          the write still RESETS [rd]'s view (PARM's [step_assign] overwrites),
          which is the point of emitting it at all.

        (DEC-4 / F5', 2026-08-22) A LOAD's [rd] takes [DLdRes :: deps_addr role]
          — the load result AND the address sources — where D-8 keeps the same
          sources OFF the [LLoad] label.  RVWMO rule 9 orders a load after its
          address registers and rules 9/10 order a later store after the load's
          result; the composite is RVWMO-honest, and recording it on the result
          REGISTER is the only place D-8 leaves open.  It is what makes a
          two-deep pointer chase ([ld r1,[x]; ld r2,[r1]; sd r2,[q]]) put the
          FIRST load in the store's dependency set.

        (DEC-5 / THE SATP-PROVENANCE EDGE, 2026-08-22; route-b design §4e)
          D-4 SAYS SYSTEM INSTRUCTIONS HAVE NO ROLE — AND [satp] IS THE ONE
          EXCEPTION.  Every memory access of a hart is translated through the
          page table [satp] names, so a value that reaches [satp] reaches the
          ADDRESS of every later access; RVWMO has no syntactic dependency for
          that (a CSR is not an integer register), but the privileged spec's
          [sfence.vma] discipline is exactly what makes hardware order a store
          after the load that produced its [satp] value.  Without an edge for it
          a witness value could flow [ld -> csrw satp -> sfence.vma -> st] into
          the store's TRANSLATION with nothing in the declared model to stop the
          store being gmo-early — which real hardware cannot do.

          So the [satp] CSR forms get a role, and only they: [satp] is modelled
          as the PSEUDO-REGISTER [SATP] (= [32], one past [x31] — [wreg] is
          [nat] and [w_regv]/[ds_prov] are [gmap]s with a default, so a number
          outside [0..31] costs nothing anywhere and no bound is tripped).
            [csrrw  SATP, rs1] ([csrw satp,rs1])  ~>  [ORalu SATP [rs1]]
            [csrrs/csrrc rd, satp, x0] ([csrr])   ~>  [ORalu rd [SATP]]
            [csrrs/csrrc SATP, rs1]               ~>  [ORalu SATP [rs1; SATP]]
            [csrrwi SATP, uimm]                   ~>  [ORalu SATP []]
          i.e. every form that WRITES [satp] rewrites its provenance (so a later
          write UNLINKS the earlier one — no stale claim), and the pure-read
          form transfers it into [rd].  EVERY OTHER CSR AND EVERY OTHER SYSTEM
          INSTRUCTION STAYS AT [ORnone]: D-4 is untouched for them.

          The consumer is [WeakRvwmoConf.dedges], which adds [dprov s SATP] to
          every store's/RMW's dependency sources.  Polarity: this ADDS edges
          (STRONGER — removes behaviors), justified by the [sfence.vma]
          discipline above rather than by RVWMO ppo, and recorded as such.

          xv6's image contains exactly two forms — [csrw satp,rs1]
          (0x18079073 / 0x18031073 / 0x18051073, in [kvminithart] and
          [trampoline.S]) and [csrr rd,satp] (0x18002773, in [kernelvec]).

          GENERALISED BY DEC-6 BELOW: [satp] is now one row of a CSR table, and
          [deps_of_csr_satp] has become [deps_of_csr].  [SATP] is still [32].

        (DEC-6 / CSR PROVENANCE FOR EVERY CSR xv6 WRITES FROM A GPR, 2026-08-22;
         route-b design §4e's REFINEMENTS block)
          DEC-5's argument is not special to [satp].  Any CSR a witness value can
          reach decides something the hart later does: [sepc]/[mepc] decide the
          [sret]/[mret] TARGET (so a witness value could choose the resumption
          PC), [sscratch]/[mscratch] carry the trapframe pointer, [sstatus]/[sie]
          the interrupt state, [stvec]/[mtvec] the trap entry.  D-4 dropped all of
          them, so §4e's uniform rule replaces the per-CSR exception: EVERY CSR
          the image touches gets a PSEUDO-REGISTER [32 + k] and the same role
          rules, and only the CSRs OUTSIDE the table stay at [ORnone] (D-4 —
          which is where the un-modelled remainder of the CSR space now lives).

          THE TABLE ([csr_reg], §4a0) — 21 pseudo-registers, [32 .. 52]:
            [satp] 0x180 -> 32     [sepc] 0x141 -> 33     [mepc] 0x341 -> 34
            [sscratch] 0x140 -> 35 [mscratch] 0x340 -> 36 [stvec] 0x105 -> 37
            [mtvec] 0x305 -> 38    [mstatus] 0x300 AND [sstatus] 0x100 -> 39
            [mie] 0x304 AND [sie] 0x104 -> 40   [mip] 0x344 AND [sip] 0x144 -> 41
            [medeleg] 0x302 -> 42  [mideleg] 0x303 -> 43  [pmpaddr0] 0x3b0 -> 44
            [pmpcfg0] 0x3a0 -> 45  [mcounteren] 0x306 -> 46 [menvcfg] 0x30a -> 47
            [mhartid] 0xf14 -> 48  [time] 0xc01 -> 49     [scause] 0x142 -> 50
            [stval] 0x143 -> 51    [stimecmp] 0x14d -> 52
          THE S-&M-ALIASES SHARE A PSEUDO-REGISTER ON PURPOSE: [sstatus] is a
          restricted VIEW of the one physical [mstatus] (likewise [sie]/[mie],
          [sip]/[mip]), and the Sail model has no separate register for it — a
          [csrw sstatus,a5] emits [RegWrite mstatus].  One key for both is
          therefore the only choice that makes the machine side land, and it is
          an OVER-approximation on the read side (a [csrr rd,sstatus] inherits
          the whole register's provenance), i.e. the safe polarity.

          TWO DESTINATIONS, HONESTLY ([ORcsr], and DEC-5's under-modelling
          RETRACTED).  A [csrrw/csrrs/csrrc(+i)] with [rd <> x0] writes BOTH the
          CSR and [rd] (with the OLD CSR value).  The image HAS one:
          [csrrci a5,sstatus,2] (0x100177f3, in [intr_get]).  Rather than grow a
          second destination into every role, the CSR forms get their own
          constructor [ORcsr p srcs rd] — "writes [p] from [srcs], and writes
          [rd] from [p]" — and a SECOND projection [deps_rd2] beside [deps_rd];
          [WeakEvLang.erw_of] consults [deps_rd] first and [deps_rd2] only when
          the node's register did not match, so every pre-existing role (for
          which [deps_rd2] is [None]) behaves exactly as before.  [rd = x0]
          collapses [ORcsr] to the plain single-destination write, which is
          xv6's [csrw] and 23 of the image's 24 write sites.

          CONTROL THROUGH [sepc]/[mepc].  [sret] (funct3 = 0, funct12 = 0x102)
          and [mret] (0x302) take the JALR-LIKE role [ORjalr 0 SEPC] /
          [ORjalr 0 MEPC]: [deps_ctrl] of an [ORjalr] is its base register, so
          the resumption PC's provenance flows into [ds_ctl] through the ordinary
          [LCtrl] node ([WeakEvLang]'s [nextPC] arm, deviation D-9) and taints
          every po-later store.  Link register [x0] means [deps_rd] is [None] —
          neither instruction writes a GPR.  Reusing [ORjalr] is exactly the
          point: no new path through [deps_ctrl] is created.

          RESIDUAL (recorded, not fixed): TRAP ENTRY takes no [stvec]/[mtvec]
          edge.  The emission's control hook is [erw_of]'s [nextPC] arm, whose
          sources come from the DECODED ROLE OF THE CURRENT INSTRUCTION; a trap's
          redirect is the same [RegWrite nextPC] node, and nothing at that node
          distinguishes it from the instruction's own, so there is no place to
          attach [stvec]'s provenance without a new emission hook.  xv6 writes
          [stvec]/[mtvec] from CONSTANTS (the [kernelvec]/[uservec] addresses) at
          boot and in [usertrapret], so no witness value can reach them; the
          residual is recorded here and in route-b §4e, and it stays inside D-4.

          Polarity, as in DEC-5: every clause ADDS sources (STRONGER — removes
          behaviors); the justification is the privileged spec's discipline, not
          RVWMO ppo, and [WeakRvwmoConf]'s [dedges] is UNCHANGED (only [satp]
          feeds translation, so only [dprov s wsatp] is a store's extra source —
          the new CSRs reach a store through [ds_ctl] and through GPR dataflow).

          THE IMAGE'S SYSTEM INVENTORY (71 words, all 32-bit): 24 GPR writes
          ([csrrw], funct3 = 1, [rd = x0] at all 24 sites) to 15 distinct CSRs;
          31 pure reads ([csrrs] with [rs1 = x0]) of 12 CSRs; 6 immediate forms
          on [sstatus] ([csrsi]/[csrci] x5 with [rd = x0], and the one
          [csrrci a5,sstatus,2]); [sret] x2, [mret] x1, [wfi] x1,
          [sfence.vma] x6, and no [ecall]/[ebreak] in the kernel image.

        (DEC-7 / THE SOURCE LISTS ARE NOT USED BY THE EMISSION ANY MORE,
         2026-08-22; route-b design §4e, slice 2a "DYNAMIC PROVENANCE")
          **SOURCES ARE DYNAMIC; THE DECODER'S SOURCE LISTS REMAIN AS THE
          SYNTACTIC REFERENCE AND AS [vm_compute] CROSS-CHECKS.**

          Provenance SOUNDNESS — "two runs of the same instruction from
          regstates that agree on the sources the emission NAMES emit the same
          label" — needs the named sources to COVER the registers the Sail
          semantics actually reads, and no decoder can see those: a translated
          access reads [satp] and [mstatus], [sret] reads [sepc], and no
          encoding field names them.  So [WeakEvLang.erw_of] now builds a
          register write's source list from the PER-INSTRUCTION READ SET the
          machine accumulates ([WeakLang.ibch]'s [ib_rds], appended to at every
          [RegRead] of a carrier register, reset at the two instruction
          boundaries), and coverage holds by construction
          ([WeakEvProv.erun_ib_rds] / [WeakEvProv.erun_silent_dagree]).

          WHAT THIS FILE IS STILL THE ORACLE FOR — everything except the source
          lists: WHICH register is the destination ([deps_rd]/[deps_rd2], the
          DEC-4 join that decides which [RegWrite] node emits [LRegW] at all),
          whether the result carries the load result ([DLdRes], a role question),
          whether a [nextPC] write is a CONTROL node at all ([deps_ctrl] being
          non-empty — without that gate EVERY instruction would become a
          control-dependency point, far beyond RVWMO and beyond hardware), and
          the memory labels' own operand lists ([deps_asrc]/[deps_vsrc], which
          slice 2a does not touch).

          HONESTY AND POLARITY.  The dynamic set is a SUPERSET of the decoded
          one on the image's forms (the [erw_of_*] witnesses in [WeakEvLang]
          re-record exactly that: fed the decoded registers, [erw_of] returns
          the decoded answer), so no RVWMO syntactic dependency is lost.  The
          extra sources are CSR-mediated, and an edge from a CSR exists only
          when that CSR's own provenance is non-empty — a chain real hardware
          also orders.  Adding sources is the STRONGER direction, as in DEC-5/6.

**Against which decoder.**  The Rocq file never consults the Sail model's decoder
(`rv64d.v`): `deps_of_bits` is its own pure bit-surgery decoder, and the tests below
are genuine rv64 encodings taken from the kernel image.  So nothing here is
retargeted at `model/Lean_RV64D`; the decoder is the same function of the bits.
(The consumer that ties the announced word to the model is `WeakEvLang`, where the
`instrAnnounce` node of the `-D SYMBOLIC` Lean model — `notes/symbolic-model.md` —
carries the word.)

**THE `vm_compute` → `decide +kernel` RECIPE** (the port's first test; later workers reuse it).

1. A Rocq `vm_compute. reflexivity.` on a CLOSED equation `f c = v` becomes
   `by decide +kernel`, with `DecidableEq` DERIVED on every inductive in the result
   type (`OpRoles` here; `Dsrc` in `WeakMem`).  `decide +kernel` skips the elaborator's
   `Decidable` evaluation and asks the kernel alone to check `decide p ≡ true`; the
   proof term is `of_decide_eq_true (Eq.refl true)` — no `Lean.ofReduceBool`, no
   compiler in the trusted base (`#print axioms` of every test below: `[propext]` only,
   which comes from the definitions' equation compilation, not from the tactic).
2. Write the evaluated function so the KERNEL reduces it fast: structural recursion
   only (no `termination_by`/WF — the kernel unfolds `WellFounded.fix` badly), and
   bit surgery through `Nat` (`BitVec.toNat`, `>>>`, `%`, `2 ^ _`), whose closed
   instances the kernel computes by its GMP extensions.  Literal `match`es on
   `Int`/`Nat` (`match ibits w 6 0 with | 3 => …`) compile to `Nat.decEq` chains that
   the kernel also evaluates natively.  Avoid `BitVec` pattern matching and
   `Int.land`-style definitions that go through `Int`'s binary recursion.
3. State the result with Lean literals (`.ORload 15 15`, `some (15, [.DLdRes, .DReg 15])`)
   — the kernel compares them with the evaluated left side by `Nat`/`Int` literal
   equality, again native.
4. Measured (GCP VM, profiler): the whole file — 50 definitions, 9 conversion lemmas,
   124 tests — builds in 0.8 s; the kernel's total `type checking` is 244 ms, the slowest single test 3 ms.
   One test three ways (`depsRd (depsOfBits (dbits 0x100177f3)) = …`): `decide +kernel`
   0.9 ms elaboration + 2.5 ms kernel; plain `decide` 4.2 ms tactic + 2.6 ms kernel;
   `rfl` 5.4 ms elaboration + 2.0 ms kernel.  So for decoder-sized closed facts all
   three are cheap; `decide +kernel` is the default because it alone scales (the
   elaborator's `whnf` is what blows up on big closed evaluations, never needed here).
   No `maxRecDepth`/`maxHeartbeats` bump, no sweep split, no `ulimit`.
5. When `decide +kernel` is NOT the tool: an OPEN goal (a variable among the inputs)
   fails with "free variables"; there, prove the general lemma (`simp only [defs]` and
   `split`) or reflect the open part into a closed checker quantified over the few
   data-dependent bits (`notes/weak-port-iris-gaps.md` §4).  `rfl` also closes these
   goals but runs the elaborator's `isDefEq` first (slower, and `whnfR`-sensitive);
   `native_decide` is banned.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase convention (see the name map below); constructors keep
   their Rocq spelling (`ORnone`, `ORload`, …), as do the all-caps pseudo-register
   constants (`SATP`, `SEPC`, …).
2. TYPES: Rocq `mword 32` ↦ `BitVec 32`; the `rnum := Z` notation is written `Int`
   directly (Rocq `Z`); `wreg` is `Nat` (as in `WeakMem`); `bool_decide` ↦ `decide`;
   `mjoin (f <$> l)` ↦ `(l.map f).flatten`; `Z.to_nat` ↦ `Int.toNat`; `Z_to_bv 32` ↦
   `BitVec.ofInt 32`.
3. `ibits w hi lo` takes `hi lo : Nat` (Rocq `Z`) and is computed as
   `(w.toNat >>> lo) % 2 ^ (hi - lo + 1)` cast to `Int` (Rocq
   `Z.land (Z.shiftr (ib_z w) lo) (Z.ones (hi - lo + 1))`).  Equal at every call site
   (all are literals with `lo ≤ hi`); the `Nat` form is what the kernel evaluates
   natively (recipe item 2).  `ibZ` is kept, as Rocq's `ib_z`.
4. The Rocq `Example`s are named `theorem`s (a Lean `example` is anonymous, and a
   regression must name the failing word).
5. `op_roles_eq_dec` (`solve_decision`) is a `deriving DecidableEq` clause.

**Drift:** none (no SC dependency; `WeakMem.Dsrc` is the only import used).

**Name map** (Rocq → Lean): `ib_z`→`ibZ`, `ibits`→`ibits`, `ib_compressed`→`ibCompressed`,
`op_roles`→`OpRoles`, `op_roles_eq_dec`→derived `DecidableEq`, `wreg_of_num`→`wregOfNum`,
`dsrc_of_num`→`dsrcOfNum`, `dsrcs_of_nums`→`dsrcsOfNums`, `SATP`/`SEPC`/…/`STIMECMP`
unchanged, `wsatp`→`wsatp`, `wreg_of_num_satp`→`wregOfNumSatp`,
`dsrc_of_num_satp`→`dsrcOfNumSatp`, `wcsr`→`wcsr`, `wcsr_satp`→`wcsrSatp`,
`deps_ctrl/addr/asrc/vsrc/rd/rd2`→`depsCtrl/Addr/Asrc/Vsrc/Rd/Rd2`, `csr_reg`→`csrReg`,
`csr_satp`→`csrSatp`, `csr_reg_satp`→`csrRegSatp`, `f12_sret/mret`→`f12Sret/f12Mret`,
`deps_of_csr/system/base`→`depsOfCsr/System/Base`, `creg`→`creg`,
`deps_of_c0/c1/c2`→`depsOfC0/C1/C2`, `deps_of_bits`→`depsOfBits`, `deps_of_ib`→`depsOfIb`,
`deps_of_ib_none`→`depsOfIbNone`, `deps_{ctrl,asrc,vsrc,rd}_none`→`deps{Ctrl,Asrc,Vsrc,Rd}None`,
`dbits`→`dbits`, and every test `deps_<a>_<b>…`→`deps<A><B>…` (e.g. `deps_ld_a4_a5_rd`→
`depsLdA4A5Rd`, `deps_csrw_satp_a5_rd2`→`depsCsrwSatpA5Rd2`).

**Not ported:** none.

**Statements checked** (diffed against Rocq by hand): every definition and all 124 tests
(generated from the Rocq source by a script, then reviewed).
-/
import Weak.WeakMem

namespace Weak

/-! ## 1. Bit surgery on the announced word

The announce carries a `BitVec n` (16 bits for an RVC halfword, 32 for a base word); the
language ZERO-EXTENDS it to `BitVec 32`.  That is lossless and unambiguous: an RVC halfword
has `bits[1:0] ≠ 0b11`, which is exactly the test `ibCompressed` below uses. -/

/-- The word as a nonnegative integer (Rocq `ib_z`). -/
def ibZ (w : BitVec 32) : Int := w.toNat

/-- Bits `[hi:lo]` of the word, as a nonnegative `Int` (deviation 3). -/
def ibits (w : BitVec 32) (hi lo : Nat) : Int :=
  (((w.toNat >>> lo) % 2 ^ (hi - lo + 1) : Nat) : Int)

def ibCompressed (w : BitVec 32) : Bool :=
  decide (ibits w 1 0 ≠ 3)

/-! ## 2. The roles

A register NUMBER (Rocq `rnum := Z`) in `0..31`; `0` means "x0", i.e. no dependency. -/

inductive OpRoles where
  | ORnone
  | ORload   (rd rs1 : Int)
  | ORstore  (rs1 rs2 : Int)
  | ORamo    (rd rs1 rs2 : Int)
  | ORbranch (rs1 rs2 : Int)
  | ORjalr   (rd rs1 : Int)
  | ORjal    (rd : Int)
  | ORalu    (rd : Int) (srcs : List Int)
  /-- DEC-6: a Zicsr access.  `p` is the CSR's PSEUDO-REGISTER, written from `srcs`; `rd` is
  the GPR destination that receives the OLD `p` (`rd = 0` — xv6's `csrw` — means there is
  none).  TWO destinations, which is why it needs a constructor of its own: `depsRd` hands
  out the first, `depsRd2` the second.  A PURE read (`csrr rd,csr`) writes no CSR and stays
  an ordinary `ORalu rd [p]`. -/
  | ORcsr    (p : Int) (srcs : List Int) (rd : Int)
  deriving DecidableEq, Inhabited, Repr

open OpRoles

/-- `x0` IS NEVER A SOURCE AND NEVER A DESTINATION.  Every consumer goes through this and
`dsrcOfNum`, so the rule is implemented once. -/
def wregOfNum (n : Int) : Option Nat :=
  if n = 0 then none else some n.toNat

def dsrcOfNum (n : Int) : List Dsrc :=
  match wregOfNum n with
  | some r => [.DReg r]
  | none => []

def dsrcsOfNums (l : List Int) : List Dsrc :=
  (l.map dsrcOfNum).flatten

/-- THE `satp` PSEUDO-REGISTER (DEC-5).  `32` is one past `x31`; `wreg` is `Nat` and every
consumer of it (`WeakMem.Wstate.wRegv`, `WeakRvwmoConf.ds_prov`) is a map read through a
default, so the number is simply a fresh key — there is no 32-entry structure anywhere to
overflow. -/
def SATP : Int := 32
def wsatp : Nat := 32

theorem wregOfNumSatp : wregOfNum SATP = some wsatp := rfl

theorem dsrcOfNumSatp : dsrcOfNum SATP = [.DReg wsatp] := rfl

/-! ... AND THE REST OF THE CSR FILE (DEC-6).  `32 .. 52`, one per CSR the image touches,
with the S-&M-aliases sharing a key because they are the same physical register (`sstatus`
is a view of `mstatus`).  Every one is `≥ 32`, so `wregOfNum` never drops one and none can
collide with a GPR. -/
def SEPC       : Int := 33
def MEPC       : Int := 34
def SSCRATCH   : Int := 35
def MSCRATCH   : Int := 36
def STVEC      : Int := 37
def MTVEC      : Int := 38
/-- `sstatus` too — one physical CSR. -/
def MSTATUS    : Int := 39
/-- `sie` too. -/
def MIE        : Int := 40
/-- `sip` too. -/
def MIP        : Int := 41
def MEDELEG    : Int := 42
def MIDELEG    : Int := 43
def PMPADDR0   : Int := 44
def PMPCFG0    : Int := 45
def MCOUNTEREN : Int := 46
def MENVCFG    : Int := 47
def MHARTID    : Int := 48
def TIME       : Int := 49
def SCAUSE     : Int := 50
def STVAL      : Int := 51
def STIMECMP   : Int := 52

/-- The `wreg` a pseudo-register number denotes.  `wreg` is `Nat` and every consumer is a map
read through a default, so these are simply fresh keys (DEC-5's note, unchanged). -/
def wcsr (n : Int) : Nat := n.toNat

theorem wcsrSatp : wcsr SATP = wsatp := rfl

/-! ## 3. The four projections the language uses

Each is a total function of the role; `ORnone` gives the empty answer everywhere, which is why
an unrecognised word costs nothing. -/

/-- ppo 11 — the CONTROL sources: a conditional branch's two comparands and an indirect jump's
base register.  Emitted at the ANNOUNCE node (`LInstr`), so it fires on the TAKEN AND THE
NOT-TAKEN arm alike (PARM's `step_if` is likewise unconditional). -/
def depsCtrl (r : OpRoles) : List Dsrc :=
  match r with
  | ORbranch rs1 rs2 => dsrcsOfNums [rs1, rs2]
  | ORjalr _ rs1 => dsrcOfNum rs1
  | _ => []

/-- THE ADDRESS SOURCES of a memory access — the ONE place a base register is read as such,
for EVERY memory role (load, store, AMO alike).  Two consumers sit on top of it and they want
different halves of D-8: `depsAsrc` (the ppo-9 operand list that goes on the memory LABEL)
masks the load arm off, `depsRd` (F5', below) uses it raw. -/
def depsAddr (r : OpRoles) : List Dsrc :=
  match r with
  | ORload _ rs1 | ORstore rs1 _ | ORamo _ rs1 _ => dsrcOfNum rs1
  | _ => []

/-- ppo 9 — the ADDRESS sources that go on the memory access's own label.  See deviation D-8:
the LOAD arm is masked to `[]` (a load's data read and the page walker's PTE read are
indistinguishable at the node), only stores and the fused RMW carry it. -/
def depsAsrc (r : OpRoles) : List Dsrc :=
  match r with
  | ORload _ _ => []  -- D-8 — see `depsAddr`
  | _ => depsAddr r

/-- ppo 10 — the DATA sources of a store. -/
def depsVsrc (r : OpRoles) : List Dsrc :=
  match r with
  | ORstore _ rs2 => dsrcOfNum rs2
  | ORamo _ _ rs2 => dsrcOfNum rs2
  | _ => []

/-- PARM's `step_assign` — the destination register and the sources whose views it inherits.
`none` means "this instruction has no dependency destination", in which case every `RegWrite`
of it stays `LSilent`.

* `ORload` — F5', TRANSITIVE PROVENANCE THROUGH LOAD ADDRESSES.  RVWMO rule 9 orders a load
  after the registers its ADDRESS was computed from, and rules 9/10 order a later store after
  the load's RESULT; composing them, the store depends on the address registers too.  D-8
  keeps those sources OFF the `LLoad` label (the PTE read is indistinguishable there), so the
  composition has to be recorded on the RESULT REGISTER instead: `rd`'s provenance is the load
  event PLUS the load's address sources — the very list `depsAddr` hands a store.  Composing
  rules 9 and 10 is RVWMO-honest, so this only raises a dependency view / adds a dep edge,
  never removes one.
* `ORamo` — needs no such patch: its address sources are already on the `LRmw` LABEL
  (`depsAsrc`), so a chain through an AMO's `rd` is pinned by two dep edges and gmo's
  transitivity.
* `ORjal`/`ORjalr` — D-4/DEC-3: the link value is PC-derived, so no source — but the write
  still OVERWRITES `rd`'s view, which is PARM's `step_assign`.
* `ORcsr` — DEC-6: the CSR destination.  `p ≥ 32`, so `wregOfNum` always succeeds; the GPR
  destination is `depsRd2`'s. -/
def depsRd (r : OpRoles) : Option (Nat × List Dsrc) :=
  match r with
  | ORload rd rs1 =>
      match wregOfNum rd with
      | some w => some (w, .DLdRes :: depsAddr (ORload rd rs1))
      | none => none
  | ORamo rd _ _ =>
      match wregOfNum rd with
      | some w => some (w, [.DLdRes])
      | none => none
  | ORjal rd | ORjalr rd _ =>
      match wregOfNum rd with
      | some w => some (w, [])
      | none => none
  | ORalu rd srcs =>
      match wregOfNum rd with
      | some w => some (w, dsrcsOfNums srcs)
      | none => none
  | ORcsr p srcs _ =>
      match wregOfNum p with
      | some w => some (w, dsrcsOfNums srcs)
      | none => none
  | ORnone | ORstore _ _ | ORbranch _ _ => none

/-- THE SECOND DESTINATION (DEC-6).  Only a Zicsr access has one: a `csrrw/csrrs/csrrc(+i)`
with `rd ≠ x0` also writes `rd`, with the CSR's OLD value — so `rd` inherits the CSR
pseudo-register's provenance.  `none` for every other role, which is why
`WeakEvLang.erw_of`'s extra lookup changes nothing outside the CSR forms. -/
def depsRd2 (r : OpRoles) : Option (Nat × List Dsrc) :=
  match r with
  | ORcsr p _ rd =>
      match wregOfNum rd with
      | some w => some (w, dsrcOfNum p)
      | none => none
  | _ => none

/-! ## 4. The decoder

### 4a0. THE SYSTEM FORMS THAT HAVE A ROLE: the CSR table (DEC-6).

`funct3` (bits `[14:12]`) selects the Zicsr form: `001` csrrw, `010` csrrs, `011` csrrc,
`101` csrrwi, `110` csrrsi, `111` csrrci; `000` is `ecall`/`ebreak`/`sret`/`mret`/`wfi`/
`sfence.vma`, which are not CSR accesses at all — `sret`/`mret` are handled separately below,
the rest stay `ORnone`.  A `csrrs`/`csrrc` with a ZERO source field performs NO write (that
is `csrr`); with a nonzero one it writes the CSR from the old CSR and the source.  The
immediate forms take their operand from the `rs1` FIELD, so they have no register source —
but a nonzero `uimm` still makes them WRITE, hence the same split. -/

/-- THE TABLE: the CSR number xv6 touches ↦ its pseudo-register.  Anything NOT here is D-4
(no role at all) — that is where the un-modelled remainder of the 4096-entry CSR space lives.
`sstatus`/`mstatus`, `sie`/`mie` and `sip`/`mip` deliberately share a row: they are one
physical register, and the Sail model has only the M-mode one. -/
def csrReg (c : Int) : Option Int :=
  match c with
  | 0x180 => some SATP
  | 0x141 => some SEPC
  | 0x341 => some MEPC
  | 0x140 => some SSCRATCH
  | 0x340 => some MSCRATCH
  | 0x105 => some STVEC
  | 0x305 => some MTVEC
  | 0x100 | 0x300 => some MSTATUS
  | 0x104 | 0x304 => some MIE
  | 0x144 | 0x344 => some MIP
  | 0x302 => some MEDELEG
  | 0x303 => some MIDELEG
  | 0x3b0 => some PMPADDR0
  | 0x3a0 => some PMPCFG0
  | 0x306 => some MCOUNTEREN
  | 0x30a => some MENVCFG
  | 0xf14 => some MHARTID
  | 0xc01 => some TIME
  | 0x142 => some SCAUSE
  | 0x143 => some STVAL
  | 0x14d => some STIMECMP
  | _ => none

/-- Kept from DEC-5 (the one CSR `WeakRvwmoConf.dedges` consumes). -/
def csrSatp : Int := 0x180

theorem csrRegSatp : csrReg csrSatp = some SATP := rfl

/-- The funct12 fields of the two returns. -/
def f12Sret : Int := 0x102
def f12Mret : Int := 0x302

/-- A Zicsr access on a TABLE CSR `p`.  `ORcsr p srcs rd` carries both destinations; `rd = 0`
(xv6's `csrw`) collapses it to the CSR alone. -/
def depsOfCsr (p : Int) (w : BitVec 32) : OpRoles :=
  let rd  := ibits w 11 7
  let rs1 := ibits w 19 15
  match ibits w 14 12 with
  | 1 => ORcsr p [rs1] rd                 -- csrrw  — xv6's `csrw csr,rs1`
  | 5 => ORcsr p [] rd                    -- csrrwi — an immediate source
  | 2 | 3 =>                              -- csrrs / csrrc
      if rs1 = 0
      then ORalu rd [p]                   --   `csrr rd,csr` — a pure read
      else ORcsr p [rs1, p] rd            --   a read-modify-write
  | 6 | 7 =>                              -- csrrsi / csrrci
      if rs1 = 0
      then ORalu rd [p]
      else ORcsr p [p] rd
  | _ => ORnone                           -- funct3 = 000/100: not Zicsr

/-- THE WHOLE SYSTEM OPCODE.  Three cases: the two returns (a JALR-LIKE role on the
resumption-PC CSR, so `depsCtrl` picks it up — DEC-6), a Zicsr access on a table CSR, and D-4
for everything else.  Not a CSR access (`funct3 = 0`): `sret`/`mret` resume at `sepc`/`mepc`,
the role is `ORjalr 0 <that CSR>`, whose `depsCtrl` is the base register — the existing
control path, no new machinery; link register `x0`: neither writes a GPR;
`ecall`/`ebreak`/`wfi`/`sfence.vma` keep D-4. -/
def depsOfSystem (w : BitVec 32) : OpRoles :=
  let c := ibits w 31 20
  if ibits w 14 12 = 0
  then
    (if c = f12Sret then ORjalr 0 SEPC
     else if c = f12Mret then ORjalr 0 MEPC
     else ORnone)
  else match csrReg c with
       | some p => depsOfCsr p w
       | none => ORnone                   -- D-4: a CSR outside the table

/-! ### 4a. The base (32-bit) formats. -/
def depsOfBase (w : BitVec 32) : OpRoles :=
  let rd  := ibits w 11 7
  let rs1 := ibits w 19 15
  let rs2 := ibits w 24 20
  match ibits w 6 0 with
  | 3  => ORload rd rs1                   -- LOAD:      lb/lh/lw/ld/...
  | 35 => ORstore rs1 rs2                 -- STORE:     sb/sh/sw/sd
  | 99 => ORbranch rs1 rs2                -- BRANCH
  | 103 => ORjalr rd rs1                  -- JALR
  | 111 => ORjal rd                       -- JAL
  | 55 => ORalu rd []                     -- LUI
  | 23 => ORalu rd []                     -- AUIPC
  | 19 => ORalu rd [rs1]                  -- OP-IMM
  | 27 => ORalu rd [rs1]                  -- OP-IMM-32
  | 51 => ORalu rd [rs1, rs2]             -- OP     (incl. M)
  | 59 => ORalu rd [rs1, rs2]             -- OP-32  (incl. M)
  | 47 =>                                 -- AMO (A extension)
      if ibits w 31 27 = 2
      then ORload rd rs1                  --   lr.w / lr.d
      else ORamo rd rs1 rs2               --   sc.*, amo*.*
  | 115 => depsOfSystem w                 -- SYSTEM (Zicsr, sret/mret)
  | _ => ORnone       -- MISC-MEM (fence), F/D, anything unrecognised

/-! ### 4b. The C extension.

The three quadrants, by `op = bits[1:0]` and `funct3 = bits[15:13]`.  A primed register field
`rd'`/`rs1'`/`rs2'` denotes `x8 + field`. -/
def creg (n : Int) : Int := 8 + n

def depsOfC0 (w : BitVec 32) : OpRoles :=
  let rd_  := creg (ibits w 4 2)
  let rs1_ := creg (ibits w 9 7)
  match ibits w 15 13 with
  | 0 => -- c.addi4spn rd', sp, nzuimm.  `nzuimm = 0` (bits `[12:5]`) is the RESERVED
         -- encoding — in particular the all-zero halfword, which is the canonical illegal
         -- instruction — so it takes no role.
      if ibits w 12 5 = 0 then ORnone else ORalu rd_ [2]
  | 2 => ORload rd_ rs1_                  -- c.lw
  | 3 => ORload rd_ rs1_                  -- c.ld
  | 6 => ORstore rs1_ rd_                 -- c.sw
  | 7 => ORstore rs1_ rd_                 -- c.sd
  | _ => ORnone                           -- c.fld/c.fsd/reserved

def depsOfC1 (w : BitVec 32) : OpRoles :=
  let rd   := ibits w 11 7
  let rd_  := creg (ibits w 9 7)
  let rs2_ := creg (ibits w 4 2)
  match ibits w 15 13 with
  | 0 => ORalu rd [rd]                    -- c.addi (c.nop at rd = 0)
  | 1 => ORalu rd [rd]                    -- c.addiw (RV64; DEC-1)
  | 2 => ORalu rd []                      -- c.li
  | 3 => if rd = 2
         then ORalu 2 [2]                 -- c.addi16sp
         else ORalu rd []                 -- c.lui
  | 4 =>
      match ibits w 11 10 with
      | 0 => ORalu rd_ [rd_]              -- c.srli
      | 1 => ORalu rd_ [rd_]              -- c.srai
      | 2 => ORalu rd_ [rd_]              -- c.andi
      | _ =>
          if ibits w 12 12 = 0
          then ORalu rd_ [rd_, rs2_]      -- c.sub/c.xor/c.or/c.and
          else if ibits w 6 5 ≤ 1
               then ORalu rd_ [rd_, rs2_] -- c.subw/c.addw
               else ORnone                -- reserved
  | 5 => ORnone                           -- c.j — jal x0, no rd
  | 6 => ORbranch rd_ 0                   -- c.beqz
  | 7 => ORbranch rd_ 0                   -- c.bnez
  | _ => ORnone

def depsOfC2 (w : BitVec 32) : OpRoles :=
  let rd  := ibits w 11 7
  let rs2 := ibits w 6 2
  match ibits w 15 13 with
  | 0 => ORalu rd [rd]                    -- c.slli
  | 2 => ORload rd 2                      -- c.lwsp
  | 3 => ORload rd 2                      -- c.ldsp
  | 4 =>
      if ibits w 12 12 = 0
      then (if rs2 = 0
            then ORjalr 0 rd              -- c.jr rs1
            else ORalu rd [rs2])          -- c.mv
      else (if rs2 = 0
            then (if rd = 0
                  then ORnone             -- c.ebreak
                  else ORjalr 1 rd)       -- c.jalr — link is x1
            else ORalu rd [rd, rs2])      -- c.add
  | 6 => ORstore 2 rs2                    -- c.swsp
  | 7 => ORstore 2 rs2                    -- c.sdsp
  | _ => ORnone                           -- c.fldsp/c.fsdsp/reserved

def depsOfBits (w : BitVec 32) : OpRoles :=
  match ibits w 1 0 with
  | 0 => depsOfC0 w
  | 1 => depsOfC1 w
  | 2 => depsOfC2 w
  | _ => depsOfBase w

/-- THE TOTAL FORM the language uses: no announced word yet (the hart is at an instruction
boundary, or the fetch has not been announced) means NO dependency role — the safe
under-approximation again. -/
def depsOfIb (ib : Option (BitVec 32)) : OpRoles :=
  match ib with
  | some w => depsOfBits w
  | none => ORnone

theorem depsOfIbNone : depsOfIb none = ORnone := rfl

/-! The four projections at `ORnone` — all empty, BY CONVERSION.  This is what makes a hart
with no announced instruction behave exactly like the D2 (dependency-free) machine. -/
theorem depsCtrlNone : depsCtrl ORnone = [] := rfl
theorem depsAsrcNone : depsAsrc ORnone = [] := rfl
theorem depsVsrcNone : depsVsrc ORnone = [] := rfl
theorem depsRdNone : depsRd ORnone = none := rfl

/-! ## 5. THE TESTS — real words out of the kernel image, by `decide +kernel`

Recorded as theorems so that a regression in the bit surgery cannot pass the build.  Each
word below is a genuine `rv64` encoding; the comment gives the assembly. -/

/-- The test words (Rocq `dbits z := Z_to_bv 32 z`). -/
def dbits (z : Int) : BitVec 32 := BitVec.ofInt 32 z

-- --- base formats ------------------------------------------------------

-- lw a5,0(a5)   = 0x0007a783 : rd = x15, rs1 = x15

theorem depsLw :
    depsOfBits (dbits 0x0007a783) = .ORload 15 15 := by
  decide +kernel

-- ld a5,0(a5)   = 0x0007b783

theorem depsLd :
    depsOfBits (dbits 0x0007b783) = .ORload 15 15 := by
  decide +kernel

-- F5': the load's RESULT REGISTER carries the load AND its address source.
--    [lw a5,0(a5)] is the degenerate case rs1 = rd; [ld a4,0(a5)] = 0x0007b703
--    separates them.

theorem depsLwRd :
    depsRd (depsOfBits (dbits 0x0007a783)) = some (15, [.DLdRes, .DReg 15]) := by
  decide +kernel

theorem depsLdA4A5Rd :
    depsRd (depsOfBits (dbits 0x0007b703)) = some (14, [.DLdRes, .DReg 15]) := by
  decide +kernel

-- ... and D-8 is UNCHANGED: nothing lands on the load's own label.

theorem depsLwAsrc :
    depsAsrc (depsOfBits (dbits 0x0007a783)) = [] := by
  decide +kernel

-- [ld a5,0(x0)] = 0x00003783 — an x0 base contributes no source, so the
--    result register is back to the pre-F5' shape.

theorem depsLdX0Rd :
    depsRd (depsOfBits (dbits 0x00003783)) = some (15, [.DLdRes]) := by
  decide +kernel

-- sw a4,0(a5)   = 0x00e7a023 : rs1 = x15 (base), rs2 = x14 (data)

theorem depsSw :
    depsOfBits (dbits 0x00e7a023) = .ORstore 15 14 := by
  decide +kernel

-- sd a4,0(a5)   = 0x00e7b023

theorem depsSd :
    depsOfBits (dbits 0x00e7b023) = .ORstore 15 14 := by
  decide +kernel

-- beq a5,zero,. = 0x00078063 : rs1 = x15, rs2 = x0 -> x0 dropped

theorem depsBeq :
    depsOfBits (dbits 0x00078063) = .ORbranch 15 0 := by
  decide +kernel

theorem depsBeqCtrl :
    depsCtrl (depsOfBits (dbits 0x00078063)) = [.DReg 15] := by
  decide +kernel

-- bne a5,a4,.   = 0x00e79063 : rs1 = x15, rs2 = x14

theorem depsBneCtrl :
    depsCtrl (depsOfBits (dbits 0x00e79063)) = [.DReg 15, .DReg 14] := by
  decide +kernel

-- jal ra,.      = 0x000000ef : rd = x1

theorem depsJal :
    depsOfBits (dbits 0x000000ef) = .ORjal 1 := by
  decide +kernel

-- jalr ra,0(a5) = 0x000780e7 : rd = x1, rs1 = x15

theorem depsJalr :
    depsOfBits (dbits 0x000780e7) = .ORjalr 1 15 := by
  decide +kernel

theorem depsJalrCtrl :
    depsCtrl (depsOfBits (dbits 0x000780e7)) = [.DReg 15] := by
  decide +kernel

-- ret = jalr x0,0(x1) = 0x00008067 : rd = x0 -> no destination

theorem depsRetRd :
    depsRd (depsOfBits (dbits 0x00008067)) = none := by
  decide +kernel

-- lui a5,0x8    = 0x000087b7

theorem depsLui :
    depsOfBits (dbits 0x000087b7) = .ORalu 15 [] := by
  decide +kernel

-- auipc a5,0x0  = 0x00000797

theorem depsAuipc :
    depsOfBits (dbits 0x00000797) = .ORalu 15 [] := by
  decide +kernel

-- addi a5,a5,1  = 0x00178793

theorem depsAddi :
    depsOfBits (dbits 0x00178793) = .ORalu 15 [15] := by
  decide +kernel

-- addiw a5,a5,1 = 0x0017879b

theorem depsAddiw :
    depsOfBits (dbits 0x0017879b) = .ORalu 15 [15] := by
  decide +kernel

-- add a5,a5,a4  = 0x00e787b3

theorem depsAdd :
    depsOfBits (dbits 0x00e787b3) = .ORalu 15 [15, 14] := by
  decide +kernel

-- addw a5,a5,a4 = 0x00e787bb

theorem depsAddw :
    depsOfBits (dbits 0x00e787bb) = .ORalu 15 [15, 14] := by
  decide +kernel

-- mul a5,a5,a4  = 0x02e787b3 : an M-extension OP, same role as [add]

theorem depsMul :
    depsOfBits (dbits 0x02e787b3) = .ORalu 15 [15, 14] := by
  decide +kernel

-- fence rw,rw   = 0x0ff0000f : no role (D-4)

theorem depsFence :
    depsOfBits (dbits 0x0ff0000f) = .ORnone := by
  decide +kernel

-- --- DEC-6: THE CSR TABLE, the two returns, and what still has no role
--        ------------------------------------------------------------------
--    Every word below is out of the image (the 71-instruction SYSTEM
--    inventory of the header).

-- [csrw satp,a5] = csrrw x0,satp,a5 = 0x18079073 — [kvminithart]'s write
--    and [trampoline.S]'s.  [rd = x0], so the [ORcsr] has no second
--    destination and [deps_rd] is the CSR's.

theorem depsCsrwSatpA5 :
    depsOfBits (dbits 0x18079073) = .ORcsr SATP [15] 0 := by
  decide +kernel

theorem depsCsrwSatpA5Rd :
    depsRd (depsOfBits (dbits 0x18079073)) = some (wsatp, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwSatpA5Rd2 :
    depsRd2 (depsOfBits (dbits 0x18079073)) = none := by
  decide +kernel

-- [csrw satp,t1] = 0x18031073 and [csrw satp,a0] = 0x18051073 — the other
--    two sites in the image (trampoline).

theorem depsCsrwSatpT1Rd :
    depsRd (depsOfBits (dbits 0x18031073)) = some (wsatp, [.DReg 6]) := by
  decide +kernel

theorem depsCsrwSatpA0Rd :
    depsRd (depsOfBits (dbits 0x18051073)) = some (wsatp, [.DReg 10]) := by
  decide +kernel

-- [csrr a4,satp] = csrrs a4,satp,x0 = 0x18002773 — the image's read site;
--    it TRANSFERS the translation context's provenance into [a4].  A pure read
--    writes no CSR, so it stays an ordinary [ORalu].

theorem depsCsrrSatp :
    depsOfBits (dbits 0x18002773) = .ORalu 14 [SATP] := by
  decide +kernel

theorem depsCsrrSatpRd :
    depsRd (depsOfBits (dbits 0x18002773)) = some (14, [.DReg wsatp]) := by
  decide +kernel

-- A CSR form carries NO memory operands and NO control sources.

theorem depsCsrwSatpAsrc :
    depsAsrc (depsOfBits (dbits 0x18079073)) = [] := by
  decide +kernel

theorem depsCsrwSatpVsrc :
    depsVsrc (depsOfBits (dbits 0x18079073)) = [] := by
  decide +kernel

theorem depsCsrwSatpCtrl :
    depsCtrl (depsOfBits (dbits 0x18079073)) = [] := by
  decide +kernel

-- THE OTHER GPR-WRITTEN CSRs OF THE IMAGE — the same shape, one row of the
--    table each.  [csrw sepc,a5] = 0x14179073 ([usertrapret]),
--    [csrw sepc,s2] = 0x14191073 ([usertrap]'s restore),
--    [csrw mepc,a5] = 0x34179073 ([start]),
--    [csrw stvec,a5] = 0x10579073, [csrw sstatus,a5] = 0x10079073,
--    [csrw sie,a5] = 0x10479073, [csrw mstatus,a5] = 0x30079073,
--    [csrw medeleg,a5] = 0x30279073, [csrw mideleg,a5] = 0x30379073,
--    [csrw pmpaddr0,a5] = 0x3b079073, [csrw pmpcfg0,a5] = 0x3a079073,
--    [csrw mcounteren,a5] = 0x30679073, [csrw menvcfg,a5] = 0x30a79073,
--    [csrw stimecmp,a5] = 0x14d79073.

theorem depsCsrwSepcA5 :
    depsRd (depsOfBits (dbits 0x14179073)) = some (wcsr SEPC, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwSepcS2 :
    depsRd (depsOfBits (dbits 0x14191073)) = some (wcsr SEPC, [.DReg 18]) := by
  decide +kernel

theorem depsCsrwMepcA5 :
    depsRd (depsOfBits (dbits 0x34179073)) = some (wcsr MEPC, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwStvecA5 :
    depsRd (depsOfBits (dbits 0x10579073)) = some (wcsr STVEC, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwSstatusA5 :
    depsRd (depsOfBits (dbits 0x10079073)) = some (wcsr MSTATUS, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwSieA5 :
    depsRd (depsOfBits (dbits 0x10479073)) = some (wcsr MIE, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwMstatusA5 :
    depsRd (depsOfBits (dbits 0x30079073)) = some (wcsr MSTATUS, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwMedelegA5 :
    depsRd (depsOfBits (dbits 0x30279073)) = some (wcsr MEDELEG, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwMidelegA5 :
    depsRd (depsOfBits (dbits 0x30379073)) = some (wcsr MIDELEG, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwPmpaddr0A5 :
    depsRd (depsOfBits (dbits 0x3b079073)) = some (wcsr PMPADDR0, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwPmpcfg0A5 :
    depsRd (depsOfBits (dbits 0x3a079073)) = some (wcsr PMPCFG0, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwMcounterenA5 :
    depsRd (depsOfBits (dbits 0x30679073)) = some (wcsr MCOUNTEREN, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwMenvcfgA5 :
    depsRd (depsOfBits (dbits 0x30a79073)) = some (wcsr MENVCFG, [.DReg 15]) := by
  decide +kernel

theorem depsCsrwStimecmpA5 :
    depsRd (depsOfBits (dbits 0x14d79073)) = some (wcsr STIMECMP, [.DReg 15]) := by
  decide +kernel

-- [csrw sscratch,a0] = 0x14051073 — [uservec]'s very first instruction.

theorem depsCsrwSscratchA0 :
    depsRd (depsOfBits (dbits 0x14051073)) = some (wcsr SSCRATCH, [.DReg 10]) := by
  decide +kernel

-- THE PURE READS of the image — [csrr a5,sstatus] = 0x100027f3 (which
--    DEC-5 still left at [ORnone]), [csrr a4,scause] = 0x14202773,
--    [csrr a4,sepc] = 0x14102773, [csrr a1,stval] = 0x143025f3,
--    [csrr t0,sscratch] = 0x140022f3, [csrr a1,mhartid] = 0xf14025f3,
--    [rdtime a5] = 0xc01027f3.

theorem depsCsrrSstatus :
    depsOfBits (dbits 0x100027f3) = .ORalu 15 [MSTATUS] := by
  decide +kernel

theorem depsCsrrScauseRd :
    depsRd (depsOfBits (dbits 0x14202773)) = some (14, [.DReg (wcsr SCAUSE)]) := by
  decide +kernel

theorem depsCsrrSepcRd :
    depsRd (depsOfBits (dbits 0x14102773)) = some (14, [.DReg (wcsr SEPC)]) := by
  decide +kernel

theorem depsCsrrStvalRd :
    depsRd (depsOfBits (dbits 0x143025f3)) = some (11, [.DReg (wcsr STVAL)]) := by
  decide +kernel

theorem depsCsrrSscratchRd :
    depsRd (depsOfBits (dbits 0x140022f3)) = some (5, [.DReg (wcsr SSCRATCH)]) := by
  decide +kernel

theorem depsCsrrMhartidRd :
    depsRd (depsOfBits (dbits 0xf14025f3)) = some (11, [.DReg (wcsr MHARTID)]) := by
  decide +kernel

theorem depsRdtimeRd :
    depsRd (depsOfBits (dbits 0xc01027f3)) = some (15, [.DReg (wcsr TIME)]) := by
  decide +kernel

-- THE IMMEDIATE FORMS.  [csrsi sstatus,2] = 0x10016073 and
--    [csrci sstatus,2] = 0x10017073 write the CSR from ITSELF (the operand is
--    an immediate) and have no GPR destination.

theorem depsCsrsiSstatus :
    depsOfBits (dbits 0x10016073) = .ORcsr MSTATUS [MSTATUS] 0 := by
  decide +kernel

theorem depsCsrciSstatusRd :
    depsRd (depsOfBits (dbits 0x10017073)) = some (wcsr MSTATUS, [.DReg (wcsr MSTATUS)]) := by
  decide +kernel

-- THE ONE TWO-DESTINATION FORM IN THE IMAGE: [csrrci a5,sstatus,2]
--    = 0x100177f3 ([intr_get]).  BOTH destinations get provenance — the CSR
--    from itself ([deps_rd]) and [a5] from the CSR's old value
--    ([deps_rd2]).

theorem depsCsrrciSstatusA5 :
    depsOfBits (dbits 0x100177f3) = .ORcsr MSTATUS [MSTATUS] 15 := by
  decide +kernel

theorem depsCsrrciSstatusA5Rd :
    depsRd (depsOfBits (dbits 0x100177f3)) = some (wcsr MSTATUS, [.DReg (wcsr MSTATUS)]) := by
  decide +kernel

theorem depsCsrrciSstatusA5Rd2 :
    depsRd2 (depsOfBits (dbits 0x100177f3)) = some (15, [.DReg (wcsr MSTATUS)]) := by
  decide +kernel

-- A hypothetical [csrrw a0,sscratch,a0] = 0x14051573 — the swap
--    [trampoline.S] used to carry.  Not in this image (uservec reads
--    [sscratch] with a plain [csrr] instead), but the decoder handles it: the
--    CSR takes [a0]'s provenance, [a0] takes the CSR's.

theorem depsCsrrwSscratchA0 :
    depsOfBits (dbits 0x14051573) = .ORcsr SSCRATCH [10] 10 := by
  decide +kernel

theorem depsCsrrwSscratchA0Rd :
    depsRd (depsOfBits (dbits 0x14051573)) = some (wcsr SSCRATCH, [.DReg 10]) := by
  decide +kernel

theorem depsCsrrwSscratchA0Rd2 :
    depsRd2 (depsOfBits (dbits 0x14051573)) = some (10, [.DReg (wcsr SSCRATCH)]) := by
  decide +kernel

-- THE TWO RETURNS.  [sret] = 0x10200073, [mret] = 0x30200073: a JALR-LIKE
--    role whose CONTROL source is the resumption-PC CSR, and no destination.

theorem depsSret :
    depsOfBits (dbits 0x10200073) = .ORjalr 0 SEPC := by
  decide +kernel

theorem depsSretCtrl :
    depsCtrl (depsOfBits (dbits 0x10200073)) = [.DReg (wcsr SEPC)] := by
  decide +kernel

theorem depsSretRd :
    depsRd (depsOfBits (dbits 0x10200073)) = none := by
  decide +kernel

theorem depsMret :
    depsOfBits (dbits 0x30200073) = .ORjalr 0 MEPC := by
  decide +kernel

theorem depsMretCtrl :
    depsCtrl (depsOfBits (dbits 0x30200073)) = [.DReg (wcsr MEPC)] := by
  decide +kernel

-- WHAT STILL HAS NO ROLE (D-4).  A CSR outside the table — [fcsr]
--    ([csrw fcsr,a5] = 0x00379073) — and the non-Zicsr SYSTEM forms
--    [sfence.vma] = 0x12000073, [wfi] = 0x10500073, [ecall] = 0x73,
--    [ebreak] = 0x00100073.

theorem depsCsrwFcsr :
    depsOfBits (dbits 0x00379073) = .ORnone := by
  decide +kernel

theorem depsSfenceVma :
    depsOfBits (dbits 0x12000073) = .ORnone := by
  decide +kernel

theorem depsWfi :
    depsOfBits (dbits 0x10500073) = .ORnone := by
  decide +kernel

theorem depsEcall :
    depsOfBits (dbits 0x00000073) = .ORnone := by
  decide +kernel

theorem depsEbreak :
    depsOfBits (dbits 0x00100073) = .ORnone := by
  decide +kernel

-- amoswap.w.aq a5,a4,(a3) = 0x0ce6a7af : rd = x15, rs1 = x13, rs2 = x14

theorem depsAmoswap :
    depsOfBits (dbits 0x0ce6a7af) = .ORamo 15 13 14 := by
  decide +kernel

theorem depsAmoswapA :
    depsAsrc (depsOfBits (dbits 0x0ce6a7af)) = [.DReg 13] := by
  decide +kernel

theorem depsAmoswapV :
    depsVsrc (depsOfBits (dbits 0x0ce6a7af)) = [.DReg 14] := by
  decide +kernel

theorem depsAmoswapRd :
    depsRd (depsOfBits (dbits 0x0ce6a7af)) = some (15, [.DLdRes]) := by
  decide +kernel

-- amoadd.w a5,a4,(a3) = 0x00e6a7af

theorem depsAmoadd :
    depsOfBits (dbits 0x00e6a7af) = .ORamo 15 13 14 := by
  decide +kernel

-- lr.w a5,(a3)  = 0x1006a7af : rd = x15, rs1 = x13, funct5 = 00010

theorem depsLr :
    depsOfBits (dbits 0x1006a7af) = .ORload 15 13 := by
  decide +kernel

-- sc.w a5,a4,(a3) = 0x18e6a7af

theorem depsSc :
    depsOfBits (dbits 0x18e6a7af) = .ORamo 15 13 14 := by
  decide +kernel

-- --- the C extension ----------------------------------------------------

-- c.nop  = 0x0001 : c.addi with rd = x0 -> no destination

theorem depsCnop :
    depsRd (depsOfBits (dbits 0x0001)) = none := by
  decide +kernel

-- c.addi a5,1 = 0x0785

theorem depsCaddi :
    depsOfBits (dbits 0x0785) = .ORalu 15 [15] := by
  decide +kernel

-- c.addiw a5,1 = 0x2785

theorem depsCaddiw :
    depsOfBits (dbits 0x2785) = .ORalu 15 [15] := by
  decide +kernel

-- c.li a5,0 = 0x4781

theorem depsCli :
    depsOfBits (dbits 0x4781) = .ORalu 15 [] := by
  decide +kernel

-- c.lui a5,0x1 = 0x6785

theorem depsClui :
    depsOfBits (dbits 0x6785) = .ORalu 15 [] := by
  decide +kernel

-- c.addi16sp sp,16 = 0x6141

theorem depsCaddi16sp :
    depsOfBits (dbits 0x6141) = .ORalu 2 [2] := by
  decide +kernel

-- c.addi4spn a0,sp,16 = 0x0808 : rd' = x8 + 2 = x10

theorem depsCaddi4spn :
    depsOfBits (dbits 0x0808) = .ORalu 10 [2] := by
  decide +kernel

-- c.mv a5,a4 = 0x87ba

theorem depsCmv :
    depsOfBits (dbits 0x87ba) = .ORalu 15 [14] := by
  decide +kernel

-- c.add a5,a4 = 0x97ba

theorem depsCadd :
    depsOfBits (dbits 0x97ba) = .ORalu 15 [15, 14] := by
  decide +kernel

-- c.slli a5,1 = 0x0786

theorem depsCslli :
    depsOfBits (dbits 0x0786) = .ORalu 15 [15] := by
  decide +kernel

-- c.srli a3,1 = 0x8285 : rd' = x8 + 5 = x13

theorem depsCsrli :
    depsOfBits (dbits 0x8285) = .ORalu 13 [13] := by
  decide +kernel

-- c.srai a3,1 = 0x8685

theorem depsCsrai :
    depsOfBits (dbits 0x8685) = .ORalu 13 [13] := by
  decide +kernel

-- c.andi a3,1 = 0x8a85

theorem depsCandi :
    depsOfBits (dbits 0x8a85) = .ORalu 13 [13] := by
  decide +kernel

-- c.sub a3,a4 = 0x8e99 : rd' = x13, rs2' = x8 + 6 = x14

theorem depsCsub :
    depsOfBits (dbits 0x8e99) = .ORalu 13 [13, 14] := by
  decide +kernel

-- c.xor a3,a4 = 0x8eb9

theorem depsCxor :
    depsOfBits (dbits 0x8eb9) = .ORalu 13 [13, 14] := by
  decide +kernel

-- c.or  a3,a4 = 0x8ed9

theorem depsCor :
    depsOfBits (dbits 0x8ed9) = .ORalu 13 [13, 14] := by
  decide +kernel

-- c.and a3,a4 = 0x8ef9

theorem depsCand :
    depsOfBits (dbits 0x8ef9) = .ORalu 13 [13, 14] := by
  decide +kernel

-- c.subw a3,a4 = 0x9e99

theorem depsCsubw :
    depsOfBits (dbits 0x9e99) = .ORalu 13 [13, 14] := by
  decide +kernel

-- c.addw a3,a4 = 0x9eb9

theorem depsCaddw :
    depsOfBits (dbits 0x9eb9) = .ORalu 13 [13, 14] := by
  decide +kernel

-- c.lw a4,0(a5) = 0x4398 : rd' = x8 + 6 = x14, rs1' = x8 + 7 = x15

theorem depsClw :
    depsOfBits (dbits 0x4398) = .ORload 14 15 := by
  decide +kernel

-- c.ld a4,0(a5) = 0x6398

theorem depsCld :
    depsOfBits (dbits 0x6398) = .ORload 14 15 := by
  decide +kernel

theorem depsCldRd :
    depsRd (depsOfBits (dbits 0x6398)) = some (14, [.DLdRes, .DReg 15]) := by
  decide +kernel

theorem depsCldAsrc :
    depsAsrc (depsOfBits (dbits 0x6398)) = [] := by
  decide +kernel

-- c.sw a4,0(a5) = 0xc398 — the [started] publisher's store

theorem depsCsw :
    depsOfBits (dbits 0xc398) = .ORstore 15 14 := by
  decide +kernel

theorem depsCswA :
    depsAsrc (depsOfBits (dbits 0xc398)) = [.DReg 15] := by
  decide +kernel

theorem depsCswV :
    depsVsrc (depsOfBits (dbits 0xc398)) = [.DReg 14] := by
  decide +kernel

theorem depsCswRd :
    depsRd (depsOfBits (dbits 0xc398)) = none := by
  decide +kernel

-- c.sd a4,0(a5) = 0xe398

theorem depsCsd :
    depsOfBits (dbits 0xe398) = .ORstore 15 14 := by
  decide +kernel

-- c.lwsp a5,0(sp) = 0x4782

theorem depsClwsp :
    depsOfBits (dbits 0x4782) = .ORload 15 2 := by
  decide +kernel

-- c.ldsp a5,0(sp) = 0x6782

theorem depsCldsp :
    depsOfBits (dbits 0x6782) = .ORload 15 2 := by
  decide +kernel

-- c.swsp a5,0(sp) = 0xc03e

theorem depsCswsp :
    depsOfBits (dbits 0xc03e) = .ORstore 2 15 := by
  decide +kernel

-- c.sdsp a5,0(sp) = 0xe03e

theorem depsCsdsp :
    depsOfBits (dbits 0xe03e) = .ORstore 2 15 := by
  decide +kernel

-- c.beqz a5,. = 0xc781 : rs1' = x8 + 7 = x15

theorem depsCbeqz :
    depsOfBits (dbits 0xc781) = .ORbranch 15 0 := by
  decide +kernel

theorem depsCbeqzCtrl :
    depsCtrl (depsOfBits (dbits 0xc781)) = [.DReg 15] := by
  decide +kernel

-- c.bnez a5,. = 0xe781

theorem depsCbnez :
    depsOfBits (dbits 0xe781) = .ORbranch 15 0 := by
  decide +kernel

-- c.j . = 0xa001 : no rd, no control source we model (unconditional)

theorem depsCj :
    depsOfBits (dbits 0xa001) = .ORnone := by
  decide +kernel

-- c.jr a5 = 0x8782 : an INDIRECT jump, hence a control source (D-3)

theorem depsCjr :
    depsOfBits (dbits 0x8782) = .ORjalr 0 15 := by
  decide +kernel

theorem depsCjrCtrl :
    depsCtrl (depsOfBits (dbits 0x8782)) = [.DReg 15] := by
  decide +kernel

theorem depsCjrRd :
    depsRd (depsOfBits (dbits 0x8782)) = none := by
  decide +kernel

-- c.jalr a5 = 0x9782 : links into x1

theorem depsCjalr :
    depsOfBits (dbits 0x9782) = .ORjalr 1 15 := by
  decide +kernel

theorem depsCjalrRd :
    depsRd (depsOfBits (dbits 0x9782)) = some (1, []) := by
  decide +kernel

-- c.ret = c.jr ra = 0x8082

theorem depsCret :
    depsOfBits (dbits 0x8082) = .ORjalr 0 1 := by
  decide +kernel

-- c.ebreak = 0x9002 : no role

theorem depsCebreak :
    depsOfBits (dbits 0x9002) = .ORnone := by
  decide +kernel

-- --- the ZERO word: not an instruction, and no role ----------------------

theorem depsZero :
    depsOfBits (dbits 0) = .ORnone := by
  decide +kernel

end Weak
