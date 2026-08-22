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
 *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Values.
Require Import WeakMem.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. Bit surgery on the announced word *)

(** The announce carries a [bvn] (16 bits for an RVC halfword, 32 for a base
    word); the language ZERO-EXTENDS it to [mword 32].  That is lossless and
    unambiguous: an RVC halfword has [bits[1:0] <> 0b11], which is exactly
    the test [ib_compressed] below uses. *)
Definition ib_z (w : mword 32) : Z := bv_unsigned w.

(** bits [hi:lo] of the word, as a nonnegative [Z]. *)
Definition ibits (w : mword 32) (hi lo : Z) : Z :=
  Z.land (Z.shiftr (ib_z w) lo) (Z.ones (hi - lo + 1)).

Definition ib_compressed (w : mword 32) : bool :=
  bool_decide (ibits w 1 0 <> 3).

(* ====================================================================== *)
(** ** 2. The roles *)

(** A register NUMBER in [0..31]; [0] means "x0", i.e. no dependency. *)
Notation rnum := Z (only parsing).

Inductive op_roles :=
| ORnone
| ORload   (rd rs1 : rnum)
| ORstore  (rs1 rs2 : rnum)
| ORamo    (rd rs1 rs2 : rnum)
| ORbranch (rs1 rs2 : rnum)
| ORjalr   (rd rs1 : rnum)
| ORjal    (rd : rnum)
| ORalu    (rd : rnum) (srcs : list rnum).

Global Instance op_roles_eq_dec : EqDecision op_roles.
Proof. solve_decision. Defined.

(** [x0] IS NEVER A SOURCE AND NEVER A DESTINATION.  Every consumer goes
    through these two, so the rule is implemented once. *)
Definition wreg_of_num (n : rnum) : option wreg :=
  if bool_decide (n = 0) then None else Some (Z.to_nat n).

Definition dsrc_of_num (n : rnum) : list dsrc :=
  match wreg_of_num n with Some r => [DReg r] | None => [] end.

Definition dsrcs_of_nums (l : list rnum) : list dsrc :=
  mjoin (dsrc_of_num <$> l).

(** THE [satp] PSEUDO-REGISTER (DEC-5).  [32] is one past [x31]; [wreg] is
    [nat] and every consumer of it ([WeakMem.w_regv], [WeakRvwmoConf.ds_prov])
    is a [gmap] read through a default, so the number is simply a fresh key —
    there is no 32-entry structure anywhere to overflow. *)
Definition SATP : rnum := 32.
Definition wsatp : wreg := 32%nat.

Lemma wreg_of_num_satp : wreg_of_num SATP = Some wsatp.
Proof. reflexivity. Qed.

Lemma dsrc_of_num_satp : dsrc_of_num SATP = [DReg wsatp].
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 3. The four projections the language uses

    Each is a total function of the role; [ORnone] gives the empty answer
    everywhere, which is why an unrecognised word costs nothing. *)

(** ppo 11 — the CONTROL sources: a conditional branch's two comparands and
    an indirect jump's base register.  Emitted at the ANNOUNCE node
    ([LInstr]), so it fires on the TAKEN AND THE NOT-TAKEN arm alike (PARM's
    [step_if] is likewise unconditional). *)
Definition deps_ctrl (r : op_roles) : list dsrc :=
  match r with
  | ORbranch rs1 rs2 => dsrcs_of_nums [rs1; rs2]
  | ORjalr _ rs1 => dsrc_of_num rs1
  | _ => []
  end.

(** THE ADDRESS SOURCES of a memory access — the ONE place a base register
    is read as such, for EVERY memory role (load, store, AMO alike).  Two
    consumers sit on top of it and they want different halves of D-8:
    [deps_asrc] (the ppo-9 operand list that goes on the memory LABEL) masks
    the load arm off, [deps_rd] (F5', below) uses it raw. *)
Definition deps_addr (r : op_roles) : list dsrc :=
  match r with
  | ORload _ rs1 | ORstore rs1 _ | ORamo _ rs1 _ => dsrc_of_num rs1
  | _ => []
  end.

(** ppo 9 — the ADDRESS sources that go on the memory access's own label.
    See deviation D-8: the LOAD arm is masked to [[]] (a load's data read and
    the page walker's PTE read are indistinguishable at the node), only
    stores and the fused RMW carry it. *)
Definition deps_asrc (r : op_roles) : list dsrc :=
  match r with
  | ORload _ _ => []                        (* D-8 — see [deps_addr] *)
  | _ => deps_addr r
  end.

(** ppo 10 — the DATA sources of a store. *)
Definition deps_vsrc (r : op_roles) : list dsrc :=
  match r with
  | ORstore _ rs2 => dsrc_of_num rs2
  | ORamo _ _ rs2 => dsrc_of_num rs2
  | _ => []
  end.

(** PARM's [step_assign] — the destination register and the sources whose
    views it inherits.  [None] means "this instruction has no dependency
    destination", in which case every [RegWrite] of it stays [LSilent]. *)
Definition deps_rd (r : op_roles) : option (wreg * list dsrc) :=
  match r with
  | ORload rd rs1 =>
      (* F5' — TRANSITIVE PROVENANCE THROUGH LOAD ADDRESSES.  RVWMO rule 9
         orders a load after the registers its ADDRESS was computed from, and
         rules 9/10 order a later store after the load's RESULT; composing
         them, the store depends on the address registers too.  D-8 keeps
         those sources OFF the [LLoad] label (the PTE read is
         indistinguishable there), so the composition has to be recorded on
         the RESULT REGISTER instead: [rd]'s provenance is the load event
         PLUS the load's address sources — the very list [deps_addr] hands a
         store.  Composing rules 9 and 10 is RVWMO-honest, so this only
         raises a dependency view / adds a dep edge, never removes one. *)
      match wreg_of_num rd with
      | Some w => Some (w, DLdRes :: deps_addr (ORload rd rs1))
      | None => None
      end
  | ORamo rd _ _ =>
      (* An AMO needs no such patch: its address sources are already on the
         [LRmw] LABEL ([deps_asrc]), so a chain through an AMO's [rd] is
         pinned by two dep edges and gmo's transitivity. *)
      match wreg_of_num rd with Some w => Some (w, [DLdRes]) | None => None end
  | ORjal rd | ORjalr rd _ =>
      (* D-4/DEC-3: the link value is PC-derived, so no source — but the
         write still OVERWRITES [rd]'s view, which is PARM's [step_assign]. *)
      match wreg_of_num rd with Some w => Some (w, []) | None => None end
  | ORalu rd srcs =>
      match wreg_of_num rd with
      | Some w => Some (w, dsrcs_of_nums srcs)
      | None => None
      end
  | ORnone | ORstore _ _ | ORbranch _ _ => None
  end.

(* ====================================================================== *)
(** ** 4. The decoder *)

(** *** 4a0. THE ONE SYSTEM FORM THAT HAS A ROLE: the [satp] CSR (DEC-5).

    [funct3] (bits [14:12]) selects the Zicsr form: [001] csrrw, [010] csrrs,
    [011] csrrc, [101] csrrwi, [110] csrrsi, [111] csrrci; [000] is
    [ecall]/[ebreak]/[sret]/[wfi]/[sfence.vma], which are not CSR accesses at
    all.  A [csrrs]/[csrrc] with a ZERO source field performs NO write (that
    is [csrr]); with a nonzero one it writes [satp] from the old [satp] and
    the source.  The immediate forms take their operand from the [rs1] FIELD,
    so they have no register source.

    A [csrrw rd, satp, rs1] with [rd <> x0] writes BOTH [satp] and [rd]; the
    role vocabulary has one destination, and [satp] is the one that carries
    the ordering claim, so [rd]'s provenance is left alone.  That is the same
    (pre-existing, D-4) under-modelling every unrecognised destination-writing
    instruction already gets, and xv6's image has no such form. *)
Definition csr_satp : Z := 0x180.

Definition deps_of_csr_satp (w : mword 32) : op_roles :=
  let rd  := ibits w 11 7 in
  let rs1 := ibits w 19 15 in
  match ibits w 14 12 with
  | 1 => ORalu SATP [rs1]                    (* csrrw  — xv6's [csrw satp,rs1] *)
  | 5 => ORalu SATP []                       (* csrrwi — an immediate, no source *)
  | 2 | 3 =>                                 (* csrrs / csrrc                   *)
      if bool_decide (rs1 = 0)
      then ORalu rd [SATP]                   (*   [csrr rd,satp] — a pure read  *)
      else ORalu SATP [rs1; SATP]            (*   a read-modify-write of satp   *)
  | 6 | 7 =>                                 (* csrrsi / csrrci                 *)
      if bool_decide (rs1 = 0)
      then ORalu rd [SATP]
      else ORalu SATP [SATP]
  | _ => ORnone                              (* funct3 = 000/100: not Zicsr     *)
  end.

(** *** 4a. The base (32-bit) formats. *)
Definition deps_of_base (w : mword 32) : op_roles :=
  let rd  := ibits w 11 7 in
  let rs1 := ibits w 19 15 in
  let rs2 := ibits w 24 20 in
  match ibits w 6 0 with
  | 3  => ORload rd rs1                      (* LOAD:      lb/lh/lw/ld/... *)
  | 35 => ORstore rs1 rs2                    (* STORE:     sb/sh/sw/sd    *)
  | 99 => ORbranch rs1 rs2                   (* BRANCH                    *)
  | 103 => ORjalr rd rs1                     (* JALR                      *)
  | 111 => ORjal rd                          (* JAL                       *)
  | 55 => ORalu rd []                        (* LUI                       *)
  | 23 => ORalu rd []                        (* AUIPC                     *)
  | 19 => ORalu rd [rs1]                     (* OP-IMM                    *)
  | 27 => ORalu rd [rs1]                     (* OP-IMM-32                 *)
  | 51 => ORalu rd [rs1; rs2]                (* OP     (incl. M)          *)
  | 59 => ORalu rd [rs1; rs2]                (* OP-32  (incl. M)          *)
  | 47 =>                                    (* AMO (A extension)         *)
      if bool_decide (ibits w 31 27 = 2)
      then ORload rd rs1                     (*   lr.w / lr.d             *)
      else ORamo rd rs1 rs2                  (*   sc.*, amo*.*            *)
  | 115 =>                                   (* SYSTEM                    *)
      (* D-4 holds for EVERY CSR but [satp] — see DEC-5. *)
      if bool_decide (ibits w 31 20 = csr_satp)
      then deps_of_csr_satp w else ORnone
  | _ => ORnone       (* MISC-MEM (fence), F/D, anything unrecognised     *)
  end.

(** *** 4b. The C extension.

    The three quadrants, by [op = bits[1:0]] and [funct3 = bits[15:13]].
    A primed register field [rd']/[rs1']/[rs2'] denotes [x8 + field]. *)
Definition creg (n : Z) : rnum := 8 + n.

Definition deps_of_c0 (w : mword 32) : op_roles :=
  let rd_  := creg (ibits w 4 2) in
  let rs1_ := creg (ibits w 9 7) in
  match ibits w 15 13 with
  | 0 => (* c.addi4spn rd', sp, nzuimm.  [nzuimm = 0] (bits [12:5]) is the
            RESERVED encoding — in particular the all-zero halfword, which is
            the canonical illegal instruction — so it takes no role. *)
      if bool_decide (ibits w 12 5 = 0) then ORnone else ORalu rd_ [2]
  | 2 => ORload rd_ rs1_                     (* c.lw  *)
  | 3 => ORload rd_ rs1_                     (* c.ld  *)
  | 6 => ORstore rs1_ rd_                    (* c.sw  *)
  | 7 => ORstore rs1_ rd_                    (* c.sd  *)
  | _ => ORnone                              (* c.fld/c.fsd/reserved *)
  end.

Definition deps_of_c1 (w : mword 32) : op_roles :=
  let rd   := ibits w 11 7 in
  let rd_  := creg (ibits w 9 7) in
  let rs2_ := creg (ibits w 4 2) in
  match ibits w 15 13 with
  | 0 => ORalu rd [rd]                       (* c.addi (c.nop at rd = 0)  *)
  | 1 => ORalu rd [rd]                       (* c.addiw (RV64; DEC-1)     *)
  | 2 => ORalu rd []                         (* c.li                      *)
  | 3 => if bool_decide (rd = 2)
         then ORalu 2 [2]                    (* c.addi16sp                *)
         else ORalu rd []                    (* c.lui                     *)
  | 4 =>
      match ibits w 11 10 with
      | 0 => ORalu rd_ [rd_]                 (* c.srli                    *)
      | 1 => ORalu rd_ [rd_]                 (* c.srai                    *)
      | 2 => ORalu rd_ [rd_]                 (* c.andi                    *)
      | _ =>
          if bool_decide (ibits w 12 12 = 0)
          then ORalu rd_ [rd_; rs2_]         (* c.sub/c.xor/c.or/c.and    *)
          else if bool_decide (ibits w 6 5 <= 1)
               then ORalu rd_ [rd_; rs2_]    (* c.subw/c.addw             *)
               else ORnone                   (* reserved                  *)
      end
  | 5 => ORnone                              (* c.j — jal x0, no rd       *)
  | 6 => ORbranch rd_ 0                      (* c.beqz                    *)
  | 7 => ORbranch rd_ 0                      (* c.bnez                    *)
  | _ => ORnone
  end.

Definition deps_of_c2 (w : mword 32) : op_roles :=
  let rd  := ibits w 11 7 in
  let rs2 := ibits w 6 2 in
  match ibits w 15 13 with
  | 0 => ORalu rd [rd]                       (* c.slli                    *)
  | 2 => ORload rd 2                         (* c.lwsp                    *)
  | 3 => ORload rd 2                         (* c.ldsp                    *)
  | 4 =>
      if bool_decide (ibits w 12 12 = 0)
      then (if bool_decide (rs2 = 0)
            then ORjalr 0 rd                 (* c.jr rs1                  *)
            else ORalu rd [rs2])             (* c.mv                      *)
      else (if bool_decide (rs2 = 0)
            then (if bool_decide (rd = 0)
                  then ORnone                (* c.ebreak                  *)
                  else ORjalr 1 rd)          (* c.jalr — link is x1       *)
            else ORalu rd [rd; rs2])         (* c.add                     *)
  | 6 => ORstore 2 rs2                       (* c.swsp                    *)
  | 7 => ORstore 2 rs2                       (* c.sdsp                    *)
  | _ => ORnone                              (* c.fldsp/c.fsdsp/reserved  *)
  end.

Definition deps_of_bits (w : mword 32) : op_roles :=
  match ibits w 1 0 with
  | 0 => deps_of_c0 w
  | 1 => deps_of_c1 w
  | 2 => deps_of_c2 w
  | _ => deps_of_base w
  end.

(** THE TOTAL FORM the language uses: no announced word yet (the hart is at
    an instruction boundary, or the fetch has not been announced) means NO
    dependency role — the safe under-approximation again. *)
Definition deps_of_ib (ib : option (mword 32)) : op_roles :=
  match ib with Some w => deps_of_bits w | None => ORnone end.

Lemma deps_of_ib_none : deps_of_ib None = ORnone.
Proof. reflexivity. Qed.

(** The four projections at [ORnone] — all empty, BY CONVERSION.  This is
    what makes a hart with no announced instruction behave exactly like the
    D2 (dependency-free) machine. *)
Lemma deps_ctrl_none : deps_ctrl ORnone = [].
Proof. reflexivity. Qed.
Lemma deps_asrc_none : deps_asrc ORnone = [].
Proof. reflexivity. Qed.
Lemma deps_vsrc_none : deps_vsrc ORnone = [].
Proof. reflexivity. Qed.
Lemma deps_rd_none : deps_rd ORnone = None.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(** ** 5. THE TESTS — real words out of the kernel image, by [vm_compute]

    Recorded as lemmas so that a regression in the bit surgery cannot pass
    the build.  Each word below is a genuine [rv64] encoding; the comment
    gives the assembly. *)

Definition dbits (z : Z) : mword 32 := Z_to_bv 32 z.

(* --- base formats ------------------------------------------------------ *)

(* lw a5,0(a5)   = 0x0007a783 : rd = x15, rs1 = x15 *)
Example deps_lw : deps_of_bits (dbits 0x0007a783) = ORload 15 15.
Proof. vm_compute. reflexivity. Qed.

(* ld a5,0(a5)   = 0x0007b783 *)
Example deps_ld : deps_of_bits (dbits 0x0007b783) = ORload 15 15.
Proof. vm_compute. reflexivity. Qed.

(* F5': the load's RESULT REGISTER carries the load AND its address source.
   [lw a5,0(a5)] is the degenerate case rs1 = rd; [ld a4,0(a5)] = 0x0007b703
   separates them. *)
Example deps_lw_rd :
  deps_rd (deps_of_bits (dbits 0x0007a783)) = Some (15%nat, [DLdRes; DReg 15%nat]).
Proof. vm_compute. reflexivity. Qed.
Example deps_ld_a4_a5_rd :
  deps_rd (deps_of_bits (dbits 0x0007b703)) = Some (14%nat, [DLdRes; DReg 15%nat]).
Proof. vm_compute. reflexivity. Qed.

(* ... and D-8 is UNCHANGED: nothing lands on the load's own label. *)
Example deps_lw_asrc : deps_asrc (deps_of_bits (dbits 0x0007a783)) = [].
Proof. vm_compute. reflexivity. Qed.

(* [ld a5,0(x0)] = 0x00003783 — an x0 base contributes no source, so the
   result register is back to the pre-F5' shape. *)
Example deps_ld_x0_rd :
  deps_rd (deps_of_bits (dbits 0x00003783)) = Some (15%nat, [DLdRes]).
Proof. vm_compute. reflexivity. Qed.

(* sw a4,0(a5)   = 0x00e7a023 : rs1 = x15 (base), rs2 = x14 (data) *)
Example deps_sw : deps_of_bits (dbits 0x00e7a023) = ORstore 15 14.
Proof. vm_compute. reflexivity. Qed.

(* sd a4,0(a5)   = 0x00e7b023 *)
Example deps_sd : deps_of_bits (dbits 0x00e7b023) = ORstore 15 14.
Proof. vm_compute. reflexivity. Qed.

(* beq a5,zero,. = 0x00078063 : rs1 = x15, rs2 = x0 -> x0 dropped *)
Example deps_beq : deps_of_bits (dbits 0x00078063) = ORbranch 15 0.
Proof. vm_compute. reflexivity. Qed.
Example deps_beq_ctrl : deps_ctrl (deps_of_bits (dbits 0x00078063)) = [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* bne a5,a4,.   = 0x00e79063 : rs1 = x15, rs2 = x14 *)
Example deps_bne_ctrl :
  deps_ctrl (deps_of_bits (dbits 0x00e79063)) = [DReg 15%nat; DReg 14%nat].
Proof. vm_compute. reflexivity. Qed.

(* jal ra,.      = 0x000000ef : rd = x1 *)
Example deps_jal : deps_of_bits (dbits 0x000000ef) = ORjal 1.
Proof. vm_compute. reflexivity. Qed.

(* jalr ra,0(a5) = 0x000780e7 : rd = x1, rs1 = x15 *)
Example deps_jalr : deps_of_bits (dbits 0x000780e7) = ORjalr 1 15.
Proof. vm_compute. reflexivity. Qed.
Example deps_jalr_ctrl :
  deps_ctrl (deps_of_bits (dbits 0x000780e7)) = [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* ret = jalr x0,0(x1) = 0x00008067 : rd = x0 -> no destination *)
Example deps_ret_rd : deps_rd (deps_of_bits (dbits 0x00008067)) = None.
Proof. vm_compute. reflexivity. Qed.

(* lui a5,0x8    = 0x000087b7 *)
Example deps_lui : deps_of_bits (dbits 0x000087b7) = ORalu 15 [].
Proof. vm_compute. reflexivity. Qed.

(* auipc a5,0x0  = 0x00000797 *)
Example deps_auipc : deps_of_bits (dbits 0x00000797) = ORalu 15 [].
Proof. vm_compute. reflexivity. Qed.

(* addi a5,a5,1  = 0x00178793 *)
Example deps_addi : deps_of_bits (dbits 0x00178793) = ORalu 15 [15].
Proof. vm_compute. reflexivity. Qed.

(* addiw a5,a5,1 = 0x0017879b *)
Example deps_addiw : deps_of_bits (dbits 0x0017879b) = ORalu 15 [15].
Proof. vm_compute. reflexivity. Qed.

(* add a5,a5,a4  = 0x00e787b3 *)
Example deps_add : deps_of_bits (dbits 0x00e787b3) = ORalu 15 [15; 14].
Proof. vm_compute. reflexivity. Qed.

(* addw a5,a5,a4 = 0x00e787bb *)
Example deps_addw : deps_of_bits (dbits 0x00e787bb) = ORalu 15 [15; 14].
Proof. vm_compute. reflexivity. Qed.

(* mul a5,a5,a4  = 0x02e787b3 : an M-extension OP, same role as [add] *)
Example deps_mul : deps_of_bits (dbits 0x02e787b3) = ORalu 15 [15; 14].
Proof. vm_compute. reflexivity. Qed.

(* fence rw,rw   = 0x0ff0000f : no role (D-4) *)
Example deps_fence : deps_of_bits (dbits 0x0ff0000f) = ORnone.
Proof. vm_compute. reflexivity. Qed.

(* csrr a5,sstatus = csrrs a5,sstatus,x0 = 0x100027f3 : no role (D-4) *)
Example deps_csrr : deps_of_bits (dbits 0x100027f3) = ORnone.
Proof. vm_compute. reflexivity. Qed.

(* --- DEC-5: THE [satp] FORMS, and only they ---------------------------- *)

(* [csrw satp,a5] = csrrw x0,satp,a5 = 0x18079073 — [kvminithart]'s write,
   and [trampoline.S]'s.  The destination is the PSEUDO-REGISTER [SATP]. *)
Example deps_csrw_satp_a5 : deps_of_bits (dbits 0x18079073) = ORalu SATP [15].
Proof. vm_compute. reflexivity. Qed.
Example deps_csrw_satp_a5_rd :
  deps_rd (deps_of_bits (dbits 0x18079073)) = Some (wsatp, [DReg 15%nat]).
Proof. vm_compute. reflexivity. Qed.

(* [csrw satp,t1] = 0x18031073 and [csrw satp,a0] = 0x18051073 — the other
   two sites in the image (trampoline). *)
Example deps_csrw_satp_t1_rd :
  deps_rd (deps_of_bits (dbits 0x18031073)) = Some (wsatp, [DReg 6%nat]).
Proof. vm_compute. reflexivity. Qed.
Example deps_csrw_satp_a0_rd :
  deps_rd (deps_of_bits (dbits 0x18051073)) = Some (wsatp, [DReg 10%nat]).
Proof. vm_compute. reflexivity. Qed.

(* [csrr a4,satp] = csrrs a4,satp,x0 = 0x18002773 — the image's read site;
   it TRANSFERS the translation context's provenance into [a4]. *)
Example deps_csrr_satp : deps_of_bits (dbits 0x18002773) = ORalu 14 [SATP].
Proof. vm_compute. reflexivity. Qed.
Example deps_csrr_satp_rd :
  deps_rd (deps_of_bits (dbits 0x18002773)) = Some (14%nat, [DReg wsatp]).
Proof. vm_compute. reflexivity. Qed.

(* A satp form carries NO memory operands — it is an [ORalu]. *)
Example deps_csrw_satp_asrc : deps_asrc (deps_of_bits (dbits 0x18079073)) = [].
Proof. vm_compute. reflexivity. Qed.
Example deps_csrw_satp_vsrc : deps_vsrc (deps_of_bits (dbits 0x18079073)) = [].
Proof. vm_compute. reflexivity. Qed.
Example deps_csrw_satp_ctrl : deps_ctrl (deps_of_bits (dbits 0x18079073)) = [].
Proof. vm_compute. reflexivity. Qed.

(* D-4 IS UNTOUCHED FOR EVERY OTHER CSR: [csrw sstatus,a5] = 0x10079073. *)
Example deps_csrw_sstatus : deps_of_bits (dbits 0x10079073) = ORnone.
Proof. vm_compute. reflexivity. Qed.

(* ... and for the non-Zicsr SYSTEM forms: [sfence.vma] = 0x12000073 (whose
   [31:20] field is 0x120, not a CSR number at all) and [ecall] = 0x73. *)
Example deps_sfence_vma : deps_of_bits (dbits 0x12000073) = ORnone.
Proof. vm_compute. reflexivity. Qed.
Example deps_ecall : deps_of_bits (dbits 0x00000073) = ORnone.
Proof. vm_compute. reflexivity. Qed.

(* amoswap.w.aq a5,a4,(a3) = 0x0ce6a7af : rd = x15, rs1 = x13, rs2 = x14 *)
Example deps_amoswap : deps_of_bits (dbits 0x0ce6a7af) = ORamo 15 13 14.
Proof. vm_compute. reflexivity. Qed.
Example deps_amoswap_a :
  deps_asrc (deps_of_bits (dbits 0x0ce6a7af)) = [DReg 13%nat].
Proof. vm_compute. reflexivity. Qed.
Example deps_amoswap_v :
  deps_vsrc (deps_of_bits (dbits 0x0ce6a7af)) = [DReg 14%nat].
Proof. vm_compute. reflexivity. Qed.
Example deps_amoswap_rd :
  deps_rd (deps_of_bits (dbits 0x0ce6a7af)) = Some (15%nat, [DLdRes]).
Proof. vm_compute. reflexivity. Qed.

(* amoadd.w a5,a4,(a3) = 0x00e6a7af *)
Example deps_amoadd : deps_of_bits (dbits 0x00e6a7af) = ORamo 15 13 14.
Proof. vm_compute. reflexivity. Qed.

(* lr.w a5,(a3)  = 0x1006a7af : rd = x15, rs1 = x13, funct5 = 00010 *)
Example deps_lr : deps_of_bits (dbits 0x1006a7af) = ORload 15 13.
Proof. vm_compute. reflexivity. Qed.

(* sc.w a5,a4,(a3) = 0x18e6a7af *)
Example deps_sc : deps_of_bits (dbits 0x18e6a7af) = ORamo 15 13 14.
Proof. vm_compute. reflexivity. Qed.

(* --- the C extension ---------------------------------------------------- *)

(* c.nop  = 0x0001 : c.addi with rd = x0 -> no destination *)
Example deps_cnop : deps_rd (deps_of_bits (dbits 0x0001)) = None.
Proof. vm_compute. reflexivity. Qed.

(* c.addi a5,1 = 0x0785 *)
Example deps_caddi : deps_of_bits (dbits 0x0785) = ORalu 15 [15].
Proof. vm_compute. reflexivity. Qed.

(* c.addiw a5,1 = 0x2785 *)
Example deps_caddiw : deps_of_bits (dbits 0x2785) = ORalu 15 [15].
Proof. vm_compute. reflexivity. Qed.

(* c.li a5,0 = 0x4781 *)
Example deps_cli : deps_of_bits (dbits 0x4781) = ORalu 15 [].
Proof. vm_compute. reflexivity. Qed.

(* c.lui a5,0x1 = 0x6785 *)
Example deps_clui : deps_of_bits (dbits 0x6785) = ORalu 15 [].
Proof. vm_compute. reflexivity. Qed.

(* c.addi16sp sp,16 = 0x6141 *)
Example deps_caddi16sp : deps_of_bits (dbits 0x6141) = ORalu 2 [2].
Proof. vm_compute. reflexivity. Qed.

(* c.addi4spn a0,sp,16 = 0x0808 : rd' = x8 + 2 = x10 *)
Example deps_caddi4spn : deps_of_bits (dbits 0x0808) = ORalu 10 [2].
Proof. vm_compute. reflexivity. Qed.

(* c.mv a5,a4 = 0x87ba *)
Example deps_cmv : deps_of_bits (dbits 0x87ba) = ORalu 15 [14].
Proof. vm_compute. reflexivity. Qed.

(* c.add a5,a4 = 0x97ba *)
Example deps_cadd : deps_of_bits (dbits 0x97ba) = ORalu 15 [15; 14].
Proof. vm_compute. reflexivity. Qed.

(* c.slli a5,1 = 0x0786 *)
Example deps_cslli : deps_of_bits (dbits 0x0786) = ORalu 15 [15].
Proof. vm_compute. reflexivity. Qed.

(* c.srli a3,1 = 0x8285 : rd' = x8 + 5 = x13 *)
Example deps_csrli : deps_of_bits (dbits 0x8285) = ORalu 13 [13].
Proof. vm_compute. reflexivity. Qed.

(* c.srai a3,1 = 0x8685 *)
Example deps_csrai : deps_of_bits (dbits 0x8685) = ORalu 13 [13].
Proof. vm_compute. reflexivity. Qed.

(* c.andi a3,1 = 0x8a85 *)
Example deps_candi : deps_of_bits (dbits 0x8a85) = ORalu 13 [13].
Proof. vm_compute. reflexivity. Qed.

(* c.sub a3,a4 = 0x8e99 : rd' = x13, rs2' = x8 + 6 = x14 *)
Example deps_csub : deps_of_bits (dbits 0x8e99) = ORalu 13 [13; 14].
Proof. vm_compute. reflexivity. Qed.

(* c.xor a3,a4 = 0x8eb9 *)
Example deps_cxor : deps_of_bits (dbits 0x8eb9) = ORalu 13 [13; 14].
Proof. vm_compute. reflexivity. Qed.

(* c.or  a3,a4 = 0x8ed9 *)
Example deps_cor : deps_of_bits (dbits 0x8ed9) = ORalu 13 [13; 14].
Proof. vm_compute. reflexivity. Qed.

(* c.and a3,a4 = 0x8ef9 *)
Example deps_cand : deps_of_bits (dbits 0x8ef9) = ORalu 13 [13; 14].
Proof. vm_compute. reflexivity. Qed.

(* c.subw a3,a4 = 0x9e99 *)
Example deps_csubw : deps_of_bits (dbits 0x9e99) = ORalu 13 [13; 14].
Proof. vm_compute. reflexivity. Qed.

(* c.addw a3,a4 = 0x9eb9 *)
Example deps_caddw : deps_of_bits (dbits 0x9eb9) = ORalu 13 [13; 14].
Proof. vm_compute. reflexivity. Qed.

(* c.lw a4,0(a5) = 0x4398 : rd' = x8 + 6 = x14, rs1' = x8 + 7 = x15 *)
Example deps_clw : deps_of_bits (dbits 0x4398) = ORload 14 15.
Proof. vm_compute. reflexivity. Qed.

(* c.ld a4,0(a5) = 0x6398 *)
Example deps_cld : deps_of_bits (dbits 0x6398) = ORload 14 15.
Proof. vm_compute. reflexivity. Qed.
Example deps_cld_rd :
  deps_rd (deps_of_bits (dbits 0x6398)) = Some (14%nat, [DLdRes; DReg 15%nat]).
Proof. vm_compute. reflexivity. Qed.
Example deps_cld_asrc : deps_asrc (deps_of_bits (dbits 0x6398)) = [].
Proof. vm_compute. reflexivity. Qed.

(* c.sw a4,0(a5) = 0xc398 — the [started] publisher's store *)
Example deps_csw : deps_of_bits (dbits 0xc398) = ORstore 15 14.
Proof. vm_compute. reflexivity. Qed.
Example deps_csw_a : deps_asrc (deps_of_bits (dbits 0xc398)) = [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.
Example deps_csw_v : deps_vsrc (deps_of_bits (dbits 0xc398)) = [DReg 14%nat].
Proof. vm_compute. reflexivity. Qed.
Example deps_csw_rd : deps_rd (deps_of_bits (dbits 0xc398)) = None.
Proof. vm_compute. reflexivity. Qed.

(* c.sd a4,0(a5) = 0xe398 *)
Example deps_csd : deps_of_bits (dbits 0xe398) = ORstore 15 14.
Proof. vm_compute. reflexivity. Qed.

(* c.lwsp a5,0(sp) = 0x4782 *)
Example deps_clwsp : deps_of_bits (dbits 0x4782) = ORload 15 2.
Proof. vm_compute. reflexivity. Qed.

(* c.ldsp a5,0(sp) = 0x6782 *)
Example deps_cldsp : deps_of_bits (dbits 0x6782) = ORload 15 2.
Proof. vm_compute. reflexivity. Qed.

(* c.swsp a5,0(sp) = 0xc03e *)
Example deps_cswsp : deps_of_bits (dbits 0xc03e) = ORstore 2 15.
Proof. vm_compute. reflexivity. Qed.

(* c.sdsp a5,0(sp) = 0xe03e *)
Example deps_csdsp : deps_of_bits (dbits 0xe03e) = ORstore 2 15.
Proof. vm_compute. reflexivity. Qed.

(* c.beqz a5,. = 0xc781 : rs1' = x8 + 7 = x15 *)
Example deps_cbeqz : deps_of_bits (dbits 0xc781) = ORbranch 15 0.
Proof. vm_compute. reflexivity. Qed.
Example deps_cbeqz_ctrl : deps_ctrl (deps_of_bits (dbits 0xc781)) = [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.

(* c.bnez a5,. = 0xe781 *)
Example deps_cbnez : deps_of_bits (dbits 0xe781) = ORbranch 15 0.
Proof. vm_compute. reflexivity. Qed.

(* c.j . = 0xa001 : no rd, no control source we model (unconditional) *)
Example deps_cj : deps_of_bits (dbits 0xa001) = ORnone.
Proof. vm_compute. reflexivity. Qed.

(* c.jr a5 = 0x8782 : an INDIRECT jump, hence a control source (D-3) *)
Example deps_cjr : deps_of_bits (dbits 0x8782) = ORjalr 0 15.
Proof. vm_compute. reflexivity. Qed.
Example deps_cjr_ctrl : deps_ctrl (deps_of_bits (dbits 0x8782)) = [DReg 15%nat].
Proof. vm_compute. reflexivity. Qed.
Example deps_cjr_rd : deps_rd (deps_of_bits (dbits 0x8782)) = None.
Proof. vm_compute. reflexivity. Qed.

(* c.jalr a5 = 0x9782 : links into x1 *)
Example deps_cjalr : deps_of_bits (dbits 0x9782) = ORjalr 1 15.
Proof. vm_compute. reflexivity. Qed.
Example deps_cjalr_rd : deps_rd (deps_of_bits (dbits 0x9782)) = Some (1%nat, []).
Proof. vm_compute. reflexivity. Qed.

(* c.ret = c.jr ra = 0x8082 *)
Example deps_cret : deps_of_bits (dbits 0x8082) = ORjalr 0 1.
Proof. vm_compute. reflexivity. Qed.

(* c.ebreak = 0x9002 : no role *)
Example deps_cebreak : deps_of_bits (dbits 0x9002) = ORnone.
Proof. vm_compute. reflexivity. Qed.

(* --- the ZERO word: not an instruction, and no role ---------------------- *)
Example deps_zero : deps_of_bits (dbits 0) = ORnone.
Proof. vm_compute. reflexivity. Qed.
