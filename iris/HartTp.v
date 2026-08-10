(* HartTp.v -- the hart identity as it appears in the register file.

   THE RULE THIS FILE ESTABLISHES: [tp] is not carried by a register map, it
   is PINNED to the hart.  A register-file resource held at hart [CID] owns
   [tp] at [cid_word_of cpu_id], and the map's [tp] slot is IGNORED.

   Why: with interrupts enabled a kernel thread can be preempted, yielded and
   re-scheduled on a DIFFERENT hart, and xv6's [swtch] does not save or
   restore [tp] -- the resumed thread simply inherits the resuming hart's.
   So a contract cannot promise [tp] is preserved, and [callee_saved] does not
   claim it.  What IS true, always, is [tp = cid_word_of <the hart we are on>],
   and pinning it here makes that true BY CONSTRUCTION at both ends of a
   migration: the continuation of a leaf hands back the SAME map [m] at the
   new hart, and the register tower does not grow a layer per instruction.

   Consequences for leaf statements:
   - a leaf that WRITES [rd] needs [rd <> Rtp] (else the pin is a lie); this
     rides in [rd_ok] (IntrDefs.v, where [csp_rs1] is in scope), which replaces
     the [rd <> csp_rs1] premise IN PLACE, so no call site changes arity.
   - a leaf that READS [rs] reads [rget m rs], which is correct for EVERY
     register including [tp] AT A FIXED HART -- so no unconditional
     [rs <> Rtp] premise anywhere, and the inlined [mycpu] tp-reads in sched /
     scheduler / push_off need no special leaf family.  For any literal
     [k <> 4], [rget m k] is [m !!! Regidx k] by one [upd_ne] ([rget_ne]
     below).  What a read DOES need, once a leaf's continuation can be
     instantiated at a DIFFERENT hart, is that its value not depend on WHICH
     hart -- and by [rget_hart_indep] below that holds at every register
     except [tp].  That residual side condition is [IntrDefs.src_ok], guarded
     on the SIE index because at interrupts-off the hart cannot move at all
     ([WpNext.wp_next_off]) and even a tp read is safe.

   Code that legitimately writes [tp] -- boot ([start]'s [w_tp]) and the
   trampoline ([uservec] restoring the kernel hartid, [userret] restoring the
   user's) -- runs with interrupts OFF and uses the UNPINNED [gpr_file]
   directly; [tp_pin_id] is the bridge at the two points where the value
   is known to be the hart id. *)
From Stdlib Require Import ZArith FunctionalExtensionality.
From stdpp Require Import gmap finite bitvector.definitions.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvLang RegFile.
Local Open Scope Z_scope.

(* the thread pointer *)
Notation Rtp := (mword_of_int 4 : mword 5).

(* The hart id as the kernel keeps it in [tp].  Defined here (rather than in
   ProcGeom.v, which sits far above the leaf layer) because every register-file
   resource now mentions it. *)
Definition cid_word_of (i : CPU) : mword 64 :=
  mword_of_int (Z.of_nat (fin_to_nat i)).

Definition cid_word `{CID : CpuId} : mword 64 := cid_word_of cpu_id.

(* [tp_pin m] is the map a hart's register file ACTUALLY holds: [m] with the
   [tp] slot overwritten by this hart's id. *)
Definition tp_pin `{CID : CpuId} (m : regfile) : regfile :=
  <[Regidx Rtp := cid_word_of cpu_id]> m.

(* [rget m k] is the true value of register [k] at this hart. *)
Definition rget `{CID : CpuId} (m : regfile) (k : mword 5) : mword 64 :=
  tp_pin m !!! Regidx k.

(* Away from tp, [rget] is the plain lookup -- this is the rewrite that keeps
   every consumer's existing register-value facts usable. *)
Lemma rget_ne `{CID : CpuId} (m : regfile) (k : mword 5) :
  Regidx k <> Regidx Rtp -> rget m k = m !!! Regidx k.
Proof. intros Hk. unfold rget, tp_pin. by apply upd_ne. Qed.

Lemma rget_tp `{CID : CpuId} (m : regfile) : rget m Rtp = cid_word_of cpu_id.
Proof. unfold rget, tp_pin. by apply upd_eq. Qed.

(* tp reads the SAME value at every map -- it is the hart's id, not anything the
   map carries.  This is what an interrupts-off proof actually needs: the
   contract names [rget m0 Rtp] (the entry map) while the instruction reads
   [rget mk Rtp] several instructions later, and they agree because BOTH are
   this hart's id.  Without it every push_off'd caller hand-rolls the same
   [assert (forall mm, rget mm Rtp = cid_word)]. *)
Lemma rget_tp_agree `{CID : CpuId} (m1 m2 : regfile) : rget m1 Rtp = rget m2 Rtp.
Proof. by rewrite !rget_tp. Qed.

Lemma rget_tp_all `{CID : CpuId} : forall m : regfile, rget m Rtp = cid_word_of cpu_id.
Proof. exact rget_tp. Qed.

(* AWAY FROM tp, A REGISTER READ DOES NOT DEPEND ON WHICH HART WE ARE ON --
   and at tp it does, by construction ([rget_tp]: the value IS the hart id).
   This is the whole content of the pin, stated as the fact CONSUMERS need
   rather than as a rewrite: [rget] is a lookup in [tp_pin m], and the pin
   touches exactly one slot, so the hart argument is dead everywhere else.

   WHY IT IS HERE.  A leaf's σ-obligation is spelled at the hart whose
   [CpuId] instance is ambient when the callback is instantiated.  Today that
   is always the caller's hart, so this lemma has no user.  A later change
   moves [WpSmodeIntr.wp_instr_s_sconf]'s callback INSIDE [WpNext.wp_next b p]
   so that an instruction can execute on the hart a trap returned to; from
   then on a leaf must reconcile [rget (CID := C1) m rs] against a caller's
   fact about [rget (CID := C0) m rs], and THIS is the reconciliation.  The
   side condition it needs is [IntrDefs.src_ok] / [ops_ok], which is landed
   in the same commit -- see [IntrDefs.rget_src_indep], which is this lemma
   under that guard, and which is what makes the new premise a proved
   obligation rather than an asserted one. *)
Lemma rget_hart_indep (m : regfile) (rs : mword 5) :
  Regidx rs <> Regidx Rtp ->
  forall c1 c2 : CpuId, rget (CID := c1) m rs = rget (CID := c2) m rs.
Proof.
  intros Hrs c1 c2.
  by rewrite (rget_ne (CID := c1) m rs Hrs), (rget_ne (CID := c2) m rs Hrs).
Qed.

(* A map already carrying this hart's id at tp is its own pin: the bridge for
   the boot / trampoline code that owns [tp] explicitly. *)
Lemma tp_pin_id `{CID : CpuId} (m : regfile) :
  m !!! Regidx Rtp = cid_word_of cpu_id -> tp_pin m = m.
Proof.
  intros Hm. unfold tp_pin, insert, regfile_insert, rf_upd.
  apply functional_extensionality. intros j.
  case_bool_decide as Hj; [ subst j; symmetry; exact Hm | reflexivity ].
Qed.

(* A pinned write commutes with the pin, which is what lets a leaf restate the
   engine's output [<[rd:=v]> (tp_pin m)] as [tp_pin (<[rd:=v]> m)]. *)
Lemma tp_pin_upd `{CID : CpuId} (m : regfile) (rd : mword 5) (v : mword 64) :
  Regidx rd <> Regidx Rtp ->
  <[Regidx rd := v]> (tp_pin m) = tp_pin (<[Regidx rd := v]> m).
Proof.
  intros Hrd. unfold tp_pin, insert, regfile_insert, rf_upd.
  apply functional_extensionality. intros j.
  repeat case_bool_decide; congruence.
Qed.
