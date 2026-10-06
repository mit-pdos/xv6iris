/-
Weak: **the symbolic register surface** (LB/AxSL rev 7, design
`claude-notes/design/weak-memory-lb-axsl.md` §7 item (4)).

Rocq: `iris/AxSymReg.v` @ xxvzwolszwmp (1cc222280).

Rocq header (verbatim, Rocq vocabulary):

    AxSymReg.v — the SYMBOLIC REGISTER SURFACE (LB/AxSL rev 7, design
    [claude-notes/design/weak-memory-lb-axsl.md] §7 item (4); reviewed by
    [claude-notes/design/weak-memory-lb-axsl-review-fetch.md] Q1).

    TASK.  §7 item (4)'s register surface is

      [r ↦ᵣ⟨x⟩ := ∃ v P, r ↦ v ∗ prov r = P ∗ (annots(P) ⇒ v = x)]

    — value [v], provenance [P], and a fact tying [v] to a LOGICAL value
    [x] CONDITIONALLY on [P]'s annotations being validated.  This file
    states that surface over an ABSTRACT provenance/annotation layer
    ([prov], [valid : prov → Prop] — kept uninterpreted, per the task: the
    real content is AxGate/AxCov's job, C1/C6, elsewhere and already
    proved/tracked) and PROVES, from EXPLICIT hypotheses about the
    underlying weak-memory WP rules (Section variables, not [Axiom]s), the
    symbolic ld / addi / sd / jalr-ret leaf specs of item (3), plus the
    ADAPTER of item (4): existing SC-shaped leaf lemmas
    ([wp_addi_conc]/[wp_sd_conc]/[wp_ret_conc] below, stated in exactly
    [WpMmodeLoad.wp_ld_gpr]'s own CPS shape — see (1) in the final report)
    are reused VERBATIM; only [provl] gets threaded alongside.

    GENERICITY (durable-notes' guiding principle: one abstraction, not a
    cross-product).  [loc] covers BOTH register names and owned memory
    addresses: [sd]'s target needs the IDENTICAL wrapper as a register
    (item 4(b): the store's data check consumes exactly the register's
    conditional fact, and the byte it writes needs the same conditional
    fact back), so [sym_pt]/[sym_pt]'s gate lemma and the carry rule below
    are each written ONCE and reused for [ld]/[addi]/[sd]/[ret] alike,
    rather than one wrapper for registers and a duplicate for memory.

**Deviations from Rocq.**

1. The Section `Context`s become `variable`s; the hypotheses a statement does not mention are
   brought in with `include … in` (Lean's rule for section hypotheses).  The `Persistent`
   contexts become instance-implicit variables.
2. A Rocq hypothesis or lemma `A -∗ B -∗ … -∗ C` (a Coq Prop, i.e. `⊢ A -∗ B -∗ … -∗ C`) is
   stated `A ⊢ B -∗ … -∗ C` -- the tree's rule shape, equivalent by `wand_intro`/`wand_elim`.
3. The notation `l ↦ₛ⟨x⟩` is not declared; `symPt l x` is written out.
4. `BiAffine` ↦ `BIAffine`; `PROP : bi` ↦ `[BI PROP]`.

**Drift:** none (abstract BI; no SC dependency).

**Name map** (Rocq → Lean): `sym_pt`→`symPt`, `sym_pt_gate`→`symPt_gate`,
`sym_wp_addi`→`sym_wp_addi`, `sym_wp_ld`→`sym_wp_ld`, `sym_wp_sd`→`sym_wp_sd`,
`sym_wp_ret`→`sym_wp_ret`, `sym_epilogue`→`symEpilogue` (WP-rule names keep the tree's `wp_`
spelling, as `wp_uk_ecall_read_at`); the section hypotheses keep their Rocq names
(`provl_agree`, `provl_carry`, `instr_addi_carries`, `wp_addi_conc`, `wp_ld_forallv`, …) and the
abstract predicates likewise (`pt`, `provl`, `valid`, `data_instr`, `instr_addi`, `instr_ld`,
`instr_sd`, `instr_ret`, `pc_at`, `ret_pc`, `addv`).

**Not ported:** none.

**Statements checked** (by hand against Rocq): `symPt`, `symPt_gate`, `sym_wp_addi`, `sym_wp_ld`,
`sym_wp_sd`, `sym_wp_ret`, `symEpilogue`.
-/
import Iris.BI
import Iris.ProofMode

namespace Weak

open Iris Iris.BI Iris.ProofMode

section AxSymReg

variable {PROP : Type _} [BI PROP] [BIAffine PROP]

/-! The ambient continuation goal every leaf lemma below proves into -- i.e.
`WP (Loop : expr riscv_lang)` in the real development (`WpMmodeLoad.wp_ld_gpr`'s own
`WP (Loop : expr riscv_lang)`).  Treating it as an opaque section variable rather than importing
`RiscvLang`/`WeakLang` keeps this prototype self-contained: nothing below inspects `Goal`'s
structure, so instantiating `Goal := WP (Loop)` recovers the real rule verbatim. -/
variable (Goal : PROP)

/-! ## 1. The abstract surface: locations, values, provenance -/

variable {loc val prov : Type _}

/-! THE CONCRETE SURFACE every existing SC leaf lemma already has: `pt l v` is `r ↦ᵣ v`
(register) or `a ↦ₘ v` (memory) -- EXCLUSIVE ownership of `l`'s content, unmodified by anything
below. -/
variable (pt : loc → val → PROP)

/-! THE WEAK-MEMORY ADDITION.  `provl l P` records that `l`'s current content was deposited under
provenance token `P` -- an owned read's graph position (item 4's "prov r"), or, for a value
derived by a data-only instruction (ALU/move/CSR/spill), the SOURCE's own provenance carried
forward (section 2 below).  It is PERSISTENT: a record of history, not an exclusive resource, so
propagating it is free.  `valid` is item (4)'s "annots(P) ⇒ …" turned into a name: a bare Prop,
established elsewhere (AxGate's `dt_ctl` ordering + AxCov's C6 coverage) -- nothing about ITS
proof is needed here. -/
variable (provl : loc → prov → PROP) (valid : prov → Prop)
variable [provl_persistent : ∀ l P, Persistent (provl l P)]
variable (provl_agree : ∀ l P1 P2, provl l P1 ⊢ provl l P2 -∗ ⌜P1 = P2⌝)

/-- THE SYMBOLIC POINTS-TO -- item (4), verbatim, generalized from register names to `loc`
(Rocq `l ↦ₛ⟨x⟩`). -/
def symPt (l : loc) (x : val) : PROP :=
  iprop(∃ v P, pt l v ∗ provl l P ∗ ⌜valid P → v = x⌝)

include provl_agree in
/-- THE GATE (item 2/3: "an operation that turns `r ↦ᵣ⟨x⟩` with its provenance validated into the
concrete `r ↦ᵣ x`").  `P` is supplied externally (agreed against `symPt`'s own hidden witness
via `provl_agree`) because `valid` is a bare Prop about a SPECIFIC token, not a global truth --
this is exactly why the gate is a real proof step (AxGate/AxCov), not a rewrite. -/
theorem symPt_gate (l : loc) (x : val) (P : prov) (HvP : valid P) :
    provl l P ⊢ symPt pt provl valid l x -∗ pt l x := by
  unfold symPt
  iintro #HP Hsym
  icases Hsym with ⟨%v, %P', Hv, #HP', %Hi⟩
  ihave %Heq := provl_agree l P P' $$ HP HP'
  subst Heq
  rw [Hi HvP]
  iexact Hv

/-! ## 2. Provenance propagation

The ONE rule every data-only instruction (ALU, move, CSR, spill/reload -- item 4's list) needs,
stated once and reused by every leaf below instead of duplicated per instruction class.
`data_instr dst src` witnesses "the leaf just run deterministically carried `src`'s content into
`dst`"; it is PERSISTENT program-text-level knowledge (like `instr`/`kernel_text` in the real
leaves), supplied per-instruction in section 3. -/

variable (data_instr : loc → loc → PROP)
variable [data_instr_persistent : ∀ dst src, Persistent (data_instr dst src)]
variable (provl_carry : ∀ dst src P, data_instr dst src ⊢ provl src P -∗ provl dst P)

/-! ## 3. The leaf specs

Each concrete hypothesis (`wp_*_conc`/`wp_ld_forallv`) is stated in EXACTLY the real leaf lemmas'
own CPS shape (`WpMmodeLoad.wp_ld_gpr` -- pre resources ⊢ instr resource ⊢ (post resources -∗
Goal) ⊢ Goal).  `wp_ld_forallv` is the one place that differs: it is the "underlying ∀v-read WP
rule" itself (task item 3) -- the continuation is quantified over an ARBITRARY `v`, with only the
CONDITIONAL fact crossing, faithfully modelling AxSL's angelic owned read (review-fetch Q1:
"AxSL itself gives nothing for owned bytes … the fact must come from the project's L2 read rule
… validated at the read's own gmo position"; `x` here is whatever `AxGraph.owned_read`/C1 --
already proved, out of this file's scope -- names as the address's last-write value). -/

/-! ### 3a. ADDI (design item 4: "⟨x⟩ ↦ ⟨x+imm⟩, provenance propagated") -/

variable (instr_addi : loc → loc → val → PROP)
variable [instr_addi_persistent : ∀ rd rs1 imm, Persistent (instr_addi rd rs1 imm)]
variable (instr_addi_carries : ∀ rd rs1 imm, instr_addi rd rs1 imm ⊢ data_instr rd rs1)
variable (addv : val → val → val)
variable (wp_addi_conc : ∀ (rd rs1 : loc) (imm v : val),
  pt rs1 v ⊢ instr_addi rd rs1 imm -∗ (pt rs1 v -∗ pt rd (addv v imm) -∗ Goal) -∗ Goal)

include provl_carry instr_addi_carries wp_addi_conc in
theorem sym_wp_addi (rd rs1 : loc) (imm x : val) :
    symPt pt provl valid rs1 x ⊢ instr_addi rd rs1 imm -∗
      (symPt pt provl valid rs1 x -∗ symPt pt provl valid rd (addv x imm) -∗ Goal) -∗ Goal := by
  unfold symPt
  iintro Hrs1 #Hinstr Hcont
  icases Hrs1 with ⟨%v, %P, Hv, #HP, %Hi⟩
  ihave #Hcarry := instr_addi_carries rd rs1 imm $$ Hinstr
  ihave #HPrd := provl_carry rd rs1 P $$ Hcarry HP
  iapply wp_addi_conc rd rs1 imm v $$ Hv Hinstr
  iintro Hv Hrd
  iapply Hcont $$ [Hv] [Hrd]
  · iexists v, P
    iframe Hv HP
    ipureintro
    exact Hi
  · iexists addv v imm, P
    iframe Hrd HPrd
    ipureintro
    intro Hvalid
    rw [Hi Hvalid]

/-! ### 3b. LD (design item 3: "result register gets ⟨x⟩ where x is the expected owned value") -/

-- rd, rs1 (base reg), ea
variable (instr_ld : loc → loc → loc → PROP)
variable [instr_ld_persistent : ∀ rd rs1 ea, Persistent (instr_ld rd rs1 ea)]
variable (instr_ld_carries : ∀ rd rs1 ea, instr_ld rd rs1 ea ⊢ data_instr rd ea)
variable (wp_ld_forallv : ∀ (rd rs1 ea : loc) (base x : val) (P : prov),
  pt rs1 base ⊢ provl ea P -∗ instr_ld rd rs1 ea -∗
    (∀ v, pt rs1 base -∗ pt rd v -∗ ⌜valid P → v = x⌝ -∗ Goal) -∗ Goal)

include provl_carry instr_ld_carries wp_ld_forallv in
theorem sym_wp_ld (rd rs1 ea : loc) (base x : val) :
    pt rs1 base ⊢ symPt pt provl valid ea x -∗ instr_ld rd rs1 ea -∗
      (pt rs1 base -∗ symPt pt provl valid rd x -∗ symPt pt provl valid ea x -∗ Goal) -∗ Goal := by
  unfold symPt
  iintro Hrs1 Hea #Hinstr Hcont
  icases Hea with ⟨%vm, %P, Hvm, #HP, %Hi⟩
  ihave #Hcarry := instr_ld_carries rd rs1 ea $$ Hinstr
  ihave #HPrd := provl_carry rd ea P $$ Hcarry HP
  iapply wp_ld_forallv rd rs1 ea base x P $$ Hrs1 HP Hinstr
  iintro %v Hrs1 Hrd %Hj
  iapply Hcont $$ Hrs1 [Hrd] [Hvm]
  · iexists v, P
    iframe Hrd HPrd
    ipureintro
    exact Hj
  · iexists vm, P
    iframe Hvm HP
    ipureintro
    exact Hi

/-! ### 3c. SD (design item 3: "store data from ⟨x⟩ -- data check uses the fact") -/

-- rd (data reg), rs1 (base), ea
variable (instr_sd : loc → loc → loc → PROP)
variable [instr_sd_persistent : ∀ rd rs1 ea, Persistent (instr_sd rd rs1 ea)]
variable (instr_sd_carries : ∀ rd rs1 ea, instr_sd rd rs1 ea ⊢ data_instr ea rd)
variable (wp_sd_conc : ∀ (rd rs1 ea : loc) (base v vold : val),
  pt rs1 base ⊢ pt rd v -∗ pt ea vold -∗ instr_sd rd rs1 ea -∗
    (pt rs1 base -∗ pt rd v -∗ pt ea v -∗ Goal) -∗ Goal)

include provl_carry instr_sd_carries wp_sd_conc in
theorem sym_wp_sd (rd rs1 ea : loc) (base vold x : val) :
    pt rs1 base ⊢ symPt pt provl valid rd x -∗ pt ea vold -∗ instr_sd rd rs1 ea -∗
      (pt rs1 base -∗ symPt pt provl valid rd x -∗ symPt pt provl valid ea x -∗ Goal) -∗
        Goal := by
  unfold symPt
  iintro Hrs1 Hrd Hea #Hinstr Hcont
  icases Hrd with ⟨%v, %P, Hv, #HP, %Hi⟩
  ihave #Hcarry := instr_sd_carries rd rs1 ea $$ Hinstr
  ihave #HPea := provl_carry ea rd P $$ Hcarry HP
  iapply wp_sd_conc rd rs1 ea base v vold $$ Hrs1 Hv Hea Hinstr
  iintro Hrs1 Hv Hea
  iapply Hcont $$ Hrs1 [Hv] [Hea]
  · iexists v, P
    iframe Hv HP
    ipureintro
    exact Hi
  · iexists v, P
    iframe Hea HPea
    ipureintro
    exact Hi

/-! ### 3d. JALR/RET -- THE GATE

(design item 3: "continuation assumes x = value, target concrete").  `Hgate` is item (2)'s
WP-step form for a `dt_ctl` node, specialized to "whatever provenance `ra` actually carries is
validated" (AxGate's `dt_ctl` ordering + AxCov's C6 coverage discharge this for a real `ret`; it
is the ONE place in this whole file `valid` is ever invoked). -/

variable (instr_ret : loc → PROP)
variable [instr_ret_persistent : ∀ ra, Persistent (instr_ret ra)]
variable (pc_at : val → PROP) (ret_pc : val → val)
variable (wp_ret_conc : ∀ (ra : loc) (x : val),
  pt ra x ⊢ instr_ret ra -∗ (pt ra x -∗ pc_at (ret_pc x) -∗ Goal) -∗ Goal)

include wp_ret_conc in
theorem sym_wp_ret (ra : loc) (x : val) :
    (∀ P, provl ra P -∗ ⌜valid P⌝) ⊢
      symPt pt provl valid ra x -∗ instr_ret ra -∗
        (pt ra x -∗ pc_at (ret_pc x) -∗ Goal) -∗ Goal := by
  unfold symPt
  iintro Hgate Hra Hinstr Hcont
  icases Hra with ⟨%v, %P, Hv, #HP, %Hi⟩
  ihave %HvP := Hgate $$ %P HP
  rw [Hi HvP]
  iapply wp_ret_conc ra x $$ Hv Hinstr Hcont

/-! ## 4. The deciding part

`sd ra,…(sp); <arbitrary register-only code>; ld ra,…(sp); ret` -- `ProofConsputc.wp_consputc_epi`'s
own shape (`c.sdsp ra`/`c.ldsp ra`/`c.jr ra` around an arm's body), with the LOGICAL variable `x`
standing in for `ra`'s entry value exactly the way that proof already threads `m !!! Regidx
ra_idx` as an arbitrary, never-forced-concrete value.  `R`/`R'`/`Hmid` abstract "the arbitrary
register-only code" as an ALREADY-PROVED, ordinary CPS-shaped WP lemma for whatever it is: its
TYPE mentions neither `provl` nor `valid`, so no weak-memory bookkeeping crosses it --
mechanically, that code is proved exactly as it is today. -/

include provl_carry instr_sd_carries wp_sd_conc instr_ld_carries wp_ld_forallv wp_ret_conc in
theorem symEpilogue (ra frame sp : loc) (R R' : PROP) (spv x vold : val) :
    pt sp spv ⊢
    symPt pt provl valid ra x -∗
    pt frame vold -∗
    instr_sd ra sp frame -∗
    R -∗
    (R -∗ (R' -∗ Goal) -∗ Goal) -∗
    instr_ld ra sp frame -∗
    (∀ P, provl ra P -∗ ⌜valid P⌝) -∗
    instr_ret ra -∗
    (R' -∗ pt sp spv -∗ pc_at (ret_pc x) -∗ Goal) -∗
    Goal := by
  iintro Hsp Hra Hframe Hsd HR Hmid Hld Hgate Hret Hcont
  -- spill: ra's fact moves to the frame slot.
  iapply sym_wp_sd Goal pt provl valid data_instr provl_carry instr_sd instr_sd_carries wp_sd_conc
    ra sp frame spv vold x $$ Hsp Hra Hframe Hsd
  iintro Hsp _ Hframe
  -- arbitrary register-only code: ordinary SC-shaped framing, nothing below this line is
  -- weak-memory-specific.
  iapply Hmid $$ HR
  iintro HR'
  -- reload: ra gets ⟨x⟩ back, the SAME x the spill deposited.
  iapply sym_wp_ld Goal pt provl valid data_instr provl_carry instr_ld instr_ld_carries wp_ld_forallv
    ra sp frame spv x $$ Hsp Hframe Hld
  iintro Hsp Hra _
  -- ret: THE GATE. x becomes concrete; the target is `ret_pc x`.
  iapply sym_wp_ret Goal pt provl valid instr_ret pc_at ret_pc wp_ret_conc ra x $$ Hgate Hra Hret
  iintro Hra Hpc
  iapply Hcont $$ HR' Hsp Hpc

end AxSymReg

end Weak
