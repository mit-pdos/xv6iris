(* KernelSitesDef.v -- the STATIC MEMORY-ORDERING DISCIPLINE of the kernel
   image, as a decidable checker plus one reflection fact.

   HAND-WRITTEN.  tools/gen_sites.py is the AUDIT tool that produced the site
   tables quoted below (and iris/KernelSites.v, which cross-checks a handful of
   them against the Sail decoder); this file is the formal object.

   Everything here is a pure computation over the tracked image bytes
   (Kernel.KernelInstrs.kernel_bytes) and the tracked symbol table
   (Kernel.KernelSyms).  There is deliberately NO Iris, NO Sail model and NO
   decode-layer import: the whole point of the artifact is that it is a fact
   about the IMAGE, checkable by [vm_compute], with the same trust shape as the
   generated [kd_<word>] decode catalogue.  (See the bridging writeup at the
   bottom of this file for what that trust shape does and does not buy.) *)

From Stdlib Require Import ZArith List Bool.
From stdpp Require Import gmap.
From stdpp.bitvector Require Import definitions.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ===================================================================== *)
(* 1.  The image, as words                                                *)
(* ===================================================================== *)

(* A byte of the tracked text image; 0 outside it.  The [text_end] guard in
   [image_disciplineb] is what keeps that default from silently swallowing a
   re-dump that moved the image's end. *)
Definition kbyte (a : Z) : Z :=
  match KernelInstrs.kernel_bytes !! a with
  | Some b => bv_unsigned b
  | None => 0
  end.

(* The 4-byte little-endian fetch window at [a].  For a compressed
   instruction only the low half is the instruction; every classifier below
   that reads a base field is guarded by [negb (w_is_rvc w)], so the high half
   of a compressed window is never consulted.  This mirrors
   [KernelText.kb_word_at], which is the same window as an [mword 32].
   (That correspondence is not proved here -- nothing in this file mentions
   [mword]; it is noted so a reader knows the two agree by construction.) *)
Definition kw (a : Z) : Z :=
  kbyte a
  + 256 * kbyte (a + 1)
  + 65536 * kbyte (a + 2)
  + 16777216 * kbyte (a + 3).

(* ===================================================================== *)
(* 2.  Word-level instruction classification                              *)
(* ===================================================================== *)

Definition wfield (w hi lo : Z) : Z := Z.land (Z.shiftr w lo) (Z.ones (hi - lo + 1)).

Definition w_is_rvc (w : Z) : bool := negb (Z.land w 3 =? 3).
Definition w_size   (w : Z) : Z    := if w_is_rvc w then 2 else 4.

Definition w_op (w : Z) : Z := Z.land w 127.        (* bits  6:0, base only *)
Definition w_f3 (w : Z) : Z := wfield w 14 12.      (* bits 14:12, base only *)

(* ---- FENCE (opcode 0001111, funct3 = 000) ---- *)
Definition w_is_fence (w : Z) : bool :=
  negb (w_is_rvc w) && (w_op w =? 15) && (w_f3 w =? 0).
Definition w_fence_pred (w : Z) : Z := wfield w 27 24.   (* PI PO PR PW *)
Definition w_fence_succ (w : Z) : Z := wfield w 23 20.   (* SI SO SR SW *)

Definition w_fence_pr (w : Z) : bool := Z.testbit (w_fence_pred w) 1.
Definition w_fence_pw (w : Z) : bool := Z.testbit (w_fence_pred w) 0.
Definition w_fence_sr (w : Z) : bool := Z.testbit (w_fence_succ w) 1.
Definition w_fence_sw (w : Z) : bool := Z.testbit (w_fence_succ w) 0.

(* The two DISCIPLINE fences, spelled EXACTLY -- not "has the pr/sw bits".
   [fence iorw,iorw] (0x0ff0000f, gcc's __sync_synchronize, four sites in the
   virtio driver) also has pr, pw and sw set, and it is deliberately NOT a
   discipline site: a full fence orders everything around it and imposes no
   adjacency requirement on its neighbours.  Folding it into the acquire /
   release classes would make [image_disciplineb] false for this image and
   would be the wrong claim anyway. *)
Definition w_is_acq_fence (w : Z) : bool :=      (* fence r,rw   = 0x0230000f *)
  w_is_fence w && (w_fence_pred w =? 2) && (w_fence_succ w =? 3).
Definition w_is_rel_fence (w : Z) : bool :=      (* fence rw,w   = 0x0310000f *)
  w_is_fence w && (w_fence_pred w =? 3) && (w_fence_succ w =? 1).
Definition w_is_full_fence (w : Z) : bool :=     (* fence iorw,iorw          *)
  w_is_fence w && (w_fence_pred w =? 15) && (w_fence_succ w =? 15).

(* ---- AMO / LR / SC (opcode 0101111) ---- *)
Definition w_is_amoop (w : Z) : bool := negb (w_is_rvc w) && (w_op w =? 47).
Definition w_amo_funct5 (w : Z) : Z := wfield w 31 27.
Definition w_amo_aq (w : Z) : bool := Z.testbit w 26.
Definition w_amo_rl (w : Z) : bool := Z.testbit w 25.
Definition w_is_lr (w : Z) : bool := w_is_amoop w && (w_amo_funct5 w =? 2).
Definition w_is_sc (w : Z) : bool := w_is_amoop w && (w_amo_funct5 w =? 3).
Definition w_is_amo (w : Z) : bool :=
  w_is_amoop w && negb (w_is_lr w) && negb (w_is_sc w).

(* ---- plain (non-atomic, non-ordered) integer loads and stores ----
   Base: LOAD (0000011) / STORE (0100011).  Compressed: quadrant 0 and 2 of
   the C extension, funct3 2/3 = word/doubleword load, 6/7 = word/doubleword
   store (C.LW / C.LD / C.LWSP / C.LDSP / C.SW / C.SD / C.SWSP / C.SDSP).
   Deliberately STRICT: floating-point loads/stores (0000111 / 0100111,
   and the C.FLD / C.FSD family) are NOT in these classes.  Strict is the safe direction --
   a wider class would let the checker ACCEPT a discipline fence whose
   neighbour is not an integer access.  xv6 has no kernel FP, so nothing is
   lost; if that ever changes the checker reports it as a violation rather
   than passing silently. *)
Definition c_quad (w : Z) : Z := Z.land w 3.
Definition c_f3   (w : Z) : Z := wfield w 15 13.

Definition w_is_plain_load (w : Z) : bool :=
  if w_is_rvc w
  then ((c_quad w =? 0) || (c_quad w =? 2)) && ((c_f3 w =? 2) || (c_f3 w =? 3))
  else (w_op w =? 3).

Definition w_is_plain_store (w : Z) : bool :=
  if w_is_rvc w
  then ((c_quad w =? 0) || (c_quad w =? 2)) && ((c_f3 w =? 6) || (c_f3 w =? 7))
  else (w_op w =? 35).

(* ===================================================================== *)
(* 3.  The per-position discipline check                                  *)
(* ===================================================================== *)

(* [site_okb prev w next]: the discipline obligation of ONE instruction, given
   its PROGRAM-ORDER neighbours' words ([None] at the ends of the text).

   The neighbours are the stream predecessor/successor, NOT the words at
   pc-4 / pc+4.  That is a deviation from the design sketch in
   design/weak-memory-phi-upgrade.md 2, and it is forced by the image: BOTH
   racy loads in this kernel are COMPRESSED (c.lw, 2 bytes), so their acquire
   fence sits at pc+2.  The release stores happen to be at fence_pc+4 because
   FENCE is always 4 bytes -- so [release_site] below can and does use the
   pc-4 spelling, while [racy_load_site] must use [pc + w_size (kw pc)].

   Three clauses, one per site class:
     (acq)  an [fence r,rw] is immediately PRECEDED by a plain load
            -- i.e. every acquire fence in the image is the tail of a
               racy-read site, so a racy read cannot be "the load with no
               fence after it";
     (rel)  an [fence rw,w] is immediately FOLLOWED by a plain store
            -- every release fence in the image is the head of a
               release-flag site;
     (amo)  every atomic memory operation carries .aq, and no LR/SC pair
            occurs in the image at all (xv6 locks with amoswap, and the
            page-table walker's CAS is the hardware's, not the kernel's).

   What this does NOT say -- and cannot, at word level -- is that every store
   to a racy byte is at a release site: which bytes a load/store touches is
   not a function of the encoding word.  That direction is covered by the
   source-level audit in tools/gen_sites.py (see the writeup at the bottom). *)
Definition site_okb (prev : option Z) (w : Z) (next : option Z) : bool :=
  (if w_is_acq_fence w
   then match prev with Some p => w_is_plain_load p | None => false end
   else true)
  && (if w_is_rel_fence w
      then match next with Some n => w_is_plain_store n | None => false end
      else true)
  && (if w_is_amoop w then w_amo_aq w && negb (w_is_lr w) && negb (w_is_sc w)
      else true).

(* ===================================================================== *)
(* 4.  The whole-image fold                                              *)
(* ===================================================================== *)

(* The text image's bounds, from the tracked dump's own header
   (kernel-rocq/KernelInstrs.v: "Address range: 0x80000000 .. 0x80006124").
   [text_hi] is checked, not assumed: the walk below must land on it exactly,
   which is the [text_end =? text_hi] conjunct of [image_disciplineb].  A
   re-dump that grows, shrinks or re-aligns the image fails that conjunct
   rather than silently checking a prefix. *)
Definition text_lo : Z := 0x80000000.
Definition text_hi : Z := 0x80006124.

(* Fuel: an upper bound on the number of 2-byte steps in the text.  The walk
   is exact for the real instruction stream (see below); the slack covers the
   .rodata gap at 0x80005a1e..0x80005fff, which the walk steps through in
   2-byte increments reading zero words.
   Spelled through [Z.to_nat] rather than as a [nat] literal: durable-notes'
   rule that a large [nat] literal elaborates to an opaque [of_num_uint]
   application (and, in the wrong place, to a stack-overflowing unary chain). *)
Definition walk_fuel : nat := Z.to_nat 12000.

(* The instruction addresses of the text, in stream order.  A flat walk from
   [text_lo] stepping by the decoded width visits a SUPERSET of the real
   instruction boundaries (verified by tools/gen_sites.py against the
   per-symbol walk gen_code.py uses: 9215 flat positions, of which all 8457
   real instruction addresses; the 758 extra are the inter-function alignment
   nops and the .rodata gap, none of which classify as a fence, an AMO, a load
   or a store).  A superset is the SOUND direction: the checker imposes the
   discipline at at least every instruction the machine can fetch. *)
Fixpoint text_addrs (fuel : nat) (a : Z) : list Z :=
  match fuel with
  | O => []
  | S f => if a <? text_hi then a :: text_addrs f (a + w_size (kw a)) else []
  end.

Definition text_pcs : list Z := text_addrs walk_fuel text_lo.
Definition text_stream : list Z := map kw text_pcs.

(* Where the walk stopped.  If the fuel ran out, or a mis-sized step desynced
   the walk, this is not [text_hi]. *)
Definition text_end : Z :=
  match rev text_pcs with
  | [] => text_lo
  | a :: _ => a + w_size (kw a)
  end.

Fixpoint chain (prev : option Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | w :: rest => site_okb prev w (hd_error rest) && chain (Some w) rest
  end.

(* ===================================================================== *)
(* 5.  The site predicates, the enumerated sites, the reflection facts    *)
(* ===================================================================== *)

(* The predicates a weak-memory LEAF RULE takes as its pure side condition.
   Boolean-valued, so a leaf instantiated at a concrete pc discharges its
   premise by [vm_compute] over four byte lookups. *)

Definition racy_load_siteb (pc : Z) : bool :=
  w_is_plain_load (kw pc) && w_is_acq_fence (kw (pc + w_size (kw pc))).
Definition racy_load_site (pc : Z) : Prop := racy_load_siteb pc = true.

Definition release_siteb (pc : Z) : bool :=
  w_is_rel_fence (kw (pc - 4)) && w_is_plain_store (kw pc).
Definition release_site (pc : Z) : Prop := release_siteb pc = true.

Definition amo_siteb (pc : Z) : bool := w_is_amo (kw pc) && w_amo_aq (kw pc).
Definition amo_site (pc : Z) : Prop := amo_siteb pc = true.

Definition acq_fence_siteb (pc : Z) : bool := w_is_acq_fence (kw pc).
Definition rel_fence_siteb (pc : Z) : bool := w_is_rel_fence (kw pc).

(* ---- the enumerated sites (tools/gen_sites.py; see tools/sites.md) ---- *)

(* Racy reads: the two acquire-loads of a publication flag.
     main+0x16      c.lw a5,0(a4)   ; started        (main.c, the boot spin)
     forkret+0x1c   c.lw a5,0(a5)   ; first.1        (proc.c, __atomic_load_n
                                                      .. __ATOMIC_ACQUIRE)   *)
Definition racy_load_pcs : list Z :=
  [ KernelSyms.main + 0x16
  ; KernelSyms.forkret + 0x1c ].

(* Release-flag stores: the plain store immediately after a [fence rw,w].
     release+0x1a   sw   zero,0(s1) ; lk->locked = 0   (spinlock.c)
     main+0xb0      c.sw a4,0(a5)   ; started = 1
     forkret+0x38   sw   zero,0(a5) ; first = 0                             *)
Definition release_pcs : list Z :=
  [ KernelSyms.release + 0x1a
  ; KernelSyms.main + 0xb0
  ; KernelSyms.forkret + 0x38 ].

(* Atomics: the ONE atomic memory operation in the whole image.
     acquire+0x1c   amoswap.w.aq a5,a5,(s1)                                 *)
Definition amo_pcs : list Z :=
  [ KernelSyms.acquire + 0x1c ].

(* The discipline fences themselves. *)
Definition acq_fence_pcs : list Z :=
  [ KernelSyms.main + 0x18
  ; KernelSyms.forkret + 0x1e ].
Definition rel_fence_pcs : list Z :=
  [ KernelSyms.release + 0x16
  ; KernelSyms.main + 0xac
  ; KernelSyms.forkret + 0x34 ].

(* [image_disciplineb] is the WHOLE-IMAGE walk; the five [forallb]s below are
   the per-class enumerations.  They are SEPARATE [Qed]s on purpose even
   though one conjoined boolean would be tidier: each expensive [Qed] costs
   ~0.6 s to rebuild [KernelInstrs.kernel_bytes]' 23362-entry [list_to_map] in
   the VM, but PEELING a conjoined boolean apart afterwards is much worse --
   [unfold]ing it into a hypothesis and splitting with [andb_prop] leaves a
   proof term whose kernel recheck reduces the 9215-step [text_addrs] fixpoint
   LAZILY and overflows the stack (measured: 60 s, 2.9 GB, "Stack overflow" at
   the peeling lemma's [Qed]).  Assembly is cheap, disassembly is not --
   [kernel_sites_ok] at the end of this section bundles them the safe way. *)
Definition image_disciplineb : bool :=
  (text_end =? text_hi) && chain None text_stream.

(* [vm_cast_no_check] rather than [vm_compute; reflexivity]: durable-notes'
   rule that a [vm_compute]-closed equation leaves a bare [eq_refl] which the
   kernel's LAZY evaluator re-reduces at [Qed] -- on a walk over the whole
   image that is exactly the stack overflow described above. *)
Lemma kernel_discipline : image_disciplineb = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* ---- the whole-image summary lemmas, one per class ---- *)

Lemma racy_load_pcs_ok : forallb racy_load_siteb racy_load_pcs = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma release_pcs_ok : forallb release_siteb release_pcs = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma amo_pcs_ok : forallb amo_siteb amo_pcs = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma acq_fence_pcs_ok : forallb acq_fence_siteb acq_fence_pcs = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma rel_fence_pcs_ok : forallb rel_fence_siteb rel_fence_pcs = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* The single fact a consumer cites.  Pure assembly of the six above: no
   [unfold], no conversion into any of the bodies, so it costs nothing. *)
Lemma kernel_sites_ok :
  image_disciplineb = true
  /\ forallb racy_load_siteb racy_load_pcs = true
  /\ forallb release_siteb release_pcs = true
  /\ forallb amo_siteb amo_pcs = true
  /\ forallb acq_fence_siteb acq_fence_pcs = true
  /\ forallb rel_fence_siteb rel_fence_pcs = true.
Proof.
  repeat apply conj.
  - exact kernel_discipline.
  - exact racy_load_pcs_ok.
  - exact release_pcs_ok.
  - exact amo_pcs_ok.
  - exact acq_fence_pcs_ok.
  - exact rel_fence_pcs_ok.
Qed.

(* The pointwise forms a consumer actually applies.  These are pure list
   plumbing over the reflection facts above -- no image computation, so they
   cost nothing at [Qed]. *)
Lemma racy_load_sites : forall pc, In pc racy_load_pcs -> racy_load_site pc.
Proof. exact (proj1 (forallb_forall _ _) racy_load_pcs_ok). Qed.

Lemma release_sites : forall pc, In pc release_pcs -> release_site pc.
Proof. exact (proj1 (forallb_forall _ _) release_pcs_ok). Qed.

Lemma amo_sites : forall pc, In pc amo_pcs -> amo_site pc.
Proof. exact (proj1 (forallb_forall _ _) amo_pcs_ok). Qed.

(* ===================================================================== *)
(* 6.  BRIDGING DESIGN -- how these facts discharge the Layer-1 premises  *)
(* ===================================================================== *)

(* This is the design writeup for the premise-discharge split recorded as
   D-M6-8 in completed/weak-memory-m6.md, and for the "site predicates +
   whole-image enumeration" item in design/weak-memory-phi-upgrade.md 2.  It
   lives here rather than in claude-notes/ because it is the contract of THIS
   file: what a consumer may conclude from [kernel_discipline] and the five
   enumeration lemmas, and -- at least as important -- what it may not.

   6.1  WHERE THIS SITS IN D-M6-8
   ------------------------------
   D-M6-8 splits each Layer-1 premise (rf_edges_ok, ee_ok, byte_ok) into
     (a) MACHINE-side facts -- EXT/COH/view arithmetic, [covered], the
         waw-cover inequality: statements about the traced wstates, provable
         per-trace;
     (b) VALUE-INDEPENDENT SITE facts -- "the reading instruction's aq bit",
         "the fence is the instruction immediately after the racy load /
         immediately before the release store": functions of the PC alone,
         which arm (b) makes available at pcs the minimal-cycle structure
         shows to be Iris-supported;
     (c) the RESIDUE -- the same site facts at positions po-after an
         unsupported read, where no Iris-derived export can reach, and only a
         static, value-independent property of the image can help.

   This file mechanizes (c) and, in doing so, supplies (b) for free.  Its
   value over any interp export is that it is SUPPORT-INDEPENDENT: a
   value-blind forall-over-the-text statement, true at every pc in the image
   whether or not that pc is pf-reachable, whether or not Iris ever visits it.
   That is exactly the shape (c) needs and exactly the shape a state-interp
   conjunct cannot have.

   6.2  WHICH PREMISE CONSUMES WHICH SITE CLASS
   --------------------------------------------
   * [edges_split]'s DISCIPLINED arm (the WRITER side) consumes
     [release_pcs] / [rel_fence_pcs].  M6's fenced arm (ii) needs: a
     certifiable promise of a release-fenced store already has all of that
     writer's pre-fence stores below it in the log.  The PC-level input to
     that argument is precisely [release_site pc] -- the [fence rw,w] is the
     instruction immediately before the flag store in program order, so every
     earlier write of the agent is fence-ordered before the flag write.
     [release_pcs_ok] gives it at all three sites; [kernel_discipline]'s (rel)
     clause gives the converse closure (no [fence rw,w] anywhere in the image
     fails to head a store), which is what rules out a fourth, unenumerated
     release shape appearing after a re-dump.

   * [ee_ok]'s FENCE-COVER arm (the READER side) consumes [racy_load_pcs] /
     [acq_fence_pcs] and [amo_pcs].  A racy read at [pc] has [fence r,rw] as
     its po-successor, so every later access of that agent is ordered after
     the read -- the cover [ee_ok] asks for.  An AMO read gets the same cover
     with no fence at all, from its own .aq bit: [amo_pcs_ok] is that fact,
     and [kernel_discipline]'s (amo) clause extends it to EVERY atomic in the
     image (there is exactly one, [acquire]'s amoswap.w.aq) and records that
     the image contains no LR/SC, so no reservation-based discipline is owed.

   * [byte_ok] is NOT consumed here.  Per design/weak-memory-phi-upgrade.md 2
     it becomes structural from the C/D/S points-to (S-bytes ARE the sync
     bytes).  What this effort contributes to it is the AUDIT that the S-byte
     set is the one the design assumes: tools/sites.md's racy-byte reference
     audit shows the only bytes a discipline site touches are [started] and
     [first.1], each referenced exactly twice in the whole image -- once by
     its own acquire-load site, once by its own release-store site.  Lock
     words stay CLEAN by the landed C/D/S decision (nothing racy-READS them;
     the spin is [ak_latest] through the AMO), so they are not S bytes and
     need no release-site membership beyond [release+0x1a].

   6.3  DELIVERY: HOW A SITE FACT REACHES A LEAF PROOF
   ---------------------------------------------------
   NOT by threading a standalone side condition down through the leaf
   interfaces.  Delivery rides the persistent instruction facts that every
   kernel-code proof already holds:

     * [KernelText.kernel_text] is persistent and hart-independent (its
       points-to are [DfracDiscarded]), so any proof that has it can extract
       [instr pc rvc ast] at any text pc, at any hart, without borrowing.
     * The site classification is a fact about THE SAME BYTES.  A leaf
       instantiated at a concrete pc discharges [racy_load_siteb pc = true]
       by [vm_compute] over four byte lookups -- no new hypothesis crosses the
       interface, and no caller has to supply anything.
     * For a pc the Iris proof never names, the whole-image lemmas do the
       work instead.  That is the division of labour: [instr] carries the
       site fact where a proof is standing, [kernel_discipline] carries it
       everywhere else.

   6.4  THE TWO DYNAMIC STATE-INTERP CONJUNCTS (post-L0, weak side)
   ----------------------------------------------------------------
   To be added to the weak state interpretation -- NOT here; this file must
   stay free of Weak* imports.  For each hart c, with [ws c] its discipline
   flags:

     w_relp  (ws c) = true  ->  sstatus.SIE c = 0 /\ release_siteb   (pc c) = true
     w_racyp (ws c) = true  ->  sstatus.SIE c = 0 /\ racy_load_siteb (pcprev c) = true

   ("armed" = the flag is set; the writer flag is armed by the release fence
   and consumed by the flag store, the reader flag is armed by the racy load
   and consumed by the acquire fence.)  Preservation:

     ESTABLISH  the fence leaf (resp. the racy-load leaf) sets the flag and
                establishes both conjuncts: the site conjunct from
                [rel_fence_pcs_ok] / [acq_fence_pcs_ok] plus the adjacency
                the site predicate itself states, and SIE = 0 from the
                resource the site's region already carries (push_off's
                interrupt-disable, or the pre-scheduler boot state).
     CONSUME    the flag store (resp. the acquire fence) clears it.
     NO TRAP    trap entry cannot fire while armed: an interrupt needs
                sstatus.SIE = 1 and the conjunct says it is 0.  (A
                synchronous exception at the flag access is excluded
                separately, by kpt_inv's residency/permission facts for the
                accessed byte -- not by this conjunct.)
     NO DRIFT   no OTHER instruction can run while armed, by adjacency: the
                site predicate says the very next (resp. previous)
                instruction is the paired access, so the flag cannot survive
                an unrelated step.

   The point of the SIE = 0 conjunct is that it makes
   preemption-between-the-fence-and-the-access UNREPRESENTABLE rather than
   merely unlikely, which is what ingredient (2) of the transfer theorem
   below needs.  Two facts make it discharge-able for THIS kernel:

     * every enumerated site is in an interrupts-off region.  The audit is in
       tools/sites.md; the arguments are push_off brackets (acquire, release,
       virtio_disk_rw, virtio_disk_intr), the pre-scheduler boot path (main:
       start() sets sie.SEIE/STIE but never sstatus.SIE, and the kernel's
       FIRST intr_on() is inside scheduler(), which main reaches only after
       the [started] publication), and -- the one delicate case -- forkret.
     * FORKRET IS THE FRAGILE ONE, AND IT IS FRAGILE IN THE SOURCE, NOT HERE.
       forkret's two [first] sites sit AFTER [release(&p->lock)], i.e. after
       a pop_off.  They are nonetheless interrupts-off only because
       scheduler() does [intr_on(); intr_off();] before [acquire(&p->lock)],
       so the matching push_off recorded intena = 0 and forkret's pop_off
       does not re-enable.  An xv6 revision that drops that intr_off() (the
       classic scheduler has only intr_on()) would leave forkret's
       acquire-load and release-store INTERRUPTIBLE and would break the
       conjunct above -- with no change to the image discipline this file
       checks.  Re-audit on any xv6 bump.
     * the timer is sstc (S-mode stimecmp), so SIE = 0 genuinely excludes
       interposition: there is no M-mode timervec that stores to a scratch
       area behind the hart's back while S-mode interrupts are masked.

   6.5  THE TRANSFER THEOREM (STATED, NOT PROVED)
   ----------------------------------------------
   The skeleton the above is aimed at.  Informally, over a full-machine
   behavior b of the weak model:

     image_disciplineb = true ->
     forall e in events(b), pc_of e in text ->
          (plain_read e  /\ racy e      -> ee_ok's fence-cover component at e)
       /\ (plain_write e /\ published e -> edges_split's disciplined
                                            component at e)

   with NO hypothesis that e is pf-supported -- that absence is the whole
   point.  It has exactly three ingredients:

     (1) TEXT FETCH DETERMINISM.  The word fetched at pc is [kw pc].  On the
         SC side this is immediate: the text points-to are [DfracDiscarded],
         so no agent can hold the write permission.  On the weak side it is
         the statement that no write message ever targets a text byte, i.e.
         the text bytes are never in any [w] footprint -- an invariant of the
         same family as [sail_shaped], and the reason Decision 4's fetch
         reads fixed text rides this same sweep.
     (2) ARMED => SIE-OFF ADJACENCY (6.4).  Without it, "the next instruction
         is the fence" is a statement about the program text that a trap
         between the two could falsify at the EVENT level.
     (3) LABEL-FROM-WORD DECODE.  The bitmask classification in section 2 must
         agree with the Sail decoder's label for the same word.  PRIMARY
         ROUTE: the CATALOGUE.  KernelDecode*.v already holds a [kd_<word>]
         lemma for every word of the covered set, so a generated companion
         (iris/KernelSites.v, from tools/gen_sites.py --emit-coq) derives the
         per-pc decode fact by LOOKUP -- every proof there is [exact kd_<w>],
         zero new decode computation -- and the forall-over-text statement is
         the enumeration of those.  FALLBACK, recorded and deliberately not
         taken first: generic "mask implies decode" lemmas over all words.
         Those are where the decode-bridge trap lives -- FENCE, FENCEI, CSR
         and SHIFTIWOP words need [decode_bridge_ms_bv] rather than
         [decode_bridge_ms], because their AST field is NARROWER than the
         encoded field it is sliced from, and the failure prints two sides
         that look identical (durable-notes, gen_code.py's bridge selection).

   And note what is NOT an ingredient: [pc_of e in text] is MACHINE-ENFORCED,
   not assumed.  A fetch goes through address translation; [kpt_inv]
   (completed/kpt-share.md, KptShare.v) pins the kernel page table's leaves,
   and [check_PTE_permission] rejects a fetch from a page without X
   (design/tlb-translation.md).  Only the text range is executable, so an
   event with a pc outside the image has no fetch to speak of.

   6.6  WHAT ENUMERATION ALONE DOES NOT GIVE
   -----------------------------------------
   Honestly, and in the order they would bite:

     1. THE CLASSIFIER IS NOT THE DECODER.  Section 2 is a hand-written
        bitmask reading of the RISC-V encoding.  It is validated against the
        Sail decoder at the 15 enumerated sites (iris/KernelSites.v) and
        nowhere else.  Image-wide, "w_is_plain_load w = true iff the model
        decodes w to a load" is an unproven correspondence.  This is
        ingredient (3) above and it is the largest single gap here.
     2. THE BYTE DIRECTION IS NOT DECIDABLE FROM THE WORD.  Nothing in this
        file says "every store to a racy byte is at a release site" -- which
        byte an access touches is not a function of its encoding.  That
        direction is a SOURCE-LEVEL audit (tools/sites.md), and it is clean
        for this image (each publication flag is referenced exactly twice,
        by its own site).  A register-indirect store to a racy byte would be
        invisible to both the checker and the audit.
     3. THE INTERRUPTS-OFF ARGUMENT IS SOURCE-LEVEL.  6.4's SIE = 0 conjunct
        has to be re-established in the weak state interp from the actual
        push_off/boot resources; the audit only says the claim is TRUE of
        this kernel, and flags forkret as the one that depends on a
        scheduler() detail.
     4. THE WALK IS A SUPERSET, AND THAT IS A PYTHON FACT.  [text_addrs]
        visits every real instruction boundary (checked by tools/gen_sites.py
        against gen_code.py's per-symbol walk: 8457 real, 9215 visited,
        containment exact) -- but that containment is not itself a Coq
        theorem.  What IS a Coq theorem is that the walk ends exactly at
        [text_hi], which is what catches a desync.
     5. D-M6-8 ARM (b) STILL OWES ITS COMBINATORIAL ARGUMENT.  The
        minimal-cycle/segment-head reasoning that makes a pc Iris-supported
        is untouched by this file.  What this file removes is the NEED for it
        at positions po-after an unsupported read -- there, the
        forall-over-text lemma stands in for support.
     6. FENCE.I AND SFENCE.VMA CARRY NO CLAIM.  They are enumerated (one
        fence.i, at userret+0x0) and deliberately outside the discipline: they
        order instruction fetch and translation, not data. *)
