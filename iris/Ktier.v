(* Ktier.v -- the KERNEL-TRANSLATION TIER of a datum, and the ambient tier
   class.  A pure file: no project imports, nothing but the two-point
   lattice, its order class, and the ambient-tier class the notations
   elaborate through (claude-notes/projects/sp-migration.md, design §1/§4/§6).

   THE CONCEPT.  A kernel memory datum ([RiscvPtsto.mem_pointsto] and the
   towers over it) owns the byte at the PHYSICAL address the kernel mapping
   takes its va to.  Whether that ownership can DRIVE a load or store
   depends on the translation regime the accessing hart is running:

   - [KT0] -- usable through the BOOT IDENTITY MAP.  The datum carries a
     PIN ([RiscvPtsto.ktier_pin]) saying its va translates to itself, so a
     hart running with translation OFF (Bare -- every hart before its own
     [kvminithart], which for a secondary is the whole printk/console/uart/
     lock cone) reads exactly the byte the datum owns.  Every [↦ₘ] in the
     tree is at a statically classified address today, so the whole tree is
     KT0 and the identity pin is the conjunct it has always carried.
   - [KT1] -- requires the FULL KERNEL TABLE.  No pin at all: the datum's va
     may map anywhere (a KSTACK page, the trampoline).  Driving a leaf with
     it needs the per-hart witness that this hart has published the kernel
     table ([SRegime.sr_kwit] / [IntrDefs.kpt_on]); that is phase D.

   So the tier is a LOWER BOUND on the accessing hart's translation
   generation, and [KtierLe] is the order: [KT0] facts are usable
   everywhere, a KT1 hart honours every claim.

   THE AMBIENT TIER.  [CurKtier] is the "which tier does an unadorned [↦ₘ]
   mean here" class: the family's ordinary spellings ([a ↦ₘ v], [a ↦₈ w],
   [stack_own sp n], ...) take it as an instance-implicit argument, so a
   file selects its tier ONCE, with a [Local Instance], and its spec text
   is unchanged.  Explicit-tier statements use the bracket spellings
   ([a ↦ₘ[KT1] v]) or the named argument [(KTR := kt)].

   DELIBERATE DEVIATION from the weak-memory branch's [CurCtx], which has
   ZERO instances by design: [CurKtier] carries a GLOBAL DEFAULT [KT0] at
   LOW priority (100), so any local pin beats it regardless of declaration
   order and the ~430 use-only consumer files need no annotation at all.
   This is sound because the default's failure direction is UNPROVABILITY,
   never unsoundness: a file that should have said KT1 and forgot gets a
   KT0 datum, whose pin it then cannot establish -- a stuck goal, not a bad
   proof.  (The reverse -- a KT1 default -- WOULD be unsound-shaped: it
   would silently drop the identity pin the Bare arm's [sr_adm] discharge
   rests on.  Do not flip it.)

   BINDER NAMING: the section/lemma binder for a [CurKtier] is [KTR].
   NEVER [GEN] -- [GEN : GenId] (the kexec era index) is pre-existing and
   widely threaded. *)

(* the two-point lattice.  Kept a dedicated type (not [bool]) so the
   weak-memory merge can grow it without re-spelling every site; if it ever
   does grow, replace the three [KtierLe] instances below with a decision
   procedure -- {bot, top, refl} is complete for TWO points only. *)
Inductive ktier : Set := KT0 | KT1.

Definition ktier_eq_dec (t1 t2 : ktier) : {t1 = t2} + {t1 <> t2}.
Proof. destruct t1, t2; (left; reflexivity) || (right; discriminate). Defined.

(* the order, as a decidable encoding: only KT1 </= KT0 *)
Definition ktier_leb (t1 t2 : ktier) : bool :=
  match t1, t2 with
  | KT1, KT0 => false
  | _, _ => true
  end.

Class KtierLe (t1 t2 : ktier) : Prop := ktier_le_holds : ktier_leb t1 t2 = true.

(* the three instances the two-point lattice needs.  All heads are
   premise-free, so typeclass search cannot diverge; the closed-corner
   overlap ([KtierLe KT0 KT1] matches two) is benign for a [Prop] class. *)
Global Instance ktier_le_bot t : KtierLe KT0 t.
Proof. destruct t; reflexivity. Qed.
Global Instance ktier_le_top t : KtierLe t KT1.
Proof. destruct t; reflexivity. Qed.
Global Instance ktier_le_refl t : KtierLe t t.
Proof. destruct t; reflexivity. Qed.

(* the eliminator the datum's monotonicity lemma runs on *)
Lemma ktier_le_cases (t1 t2 : ktier) :
  KtierLe t1 t2 -> t1 = t2 \/ (t1 = KT0 /\ t2 = KT1).
Proof.
  destruct t1, t2; intro H;
    solve [ left; reflexivity | right; split; reflexivity | discriminate H ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The AMBIENT tier.                                                       *)
(* ---------------------------------------------------------------------- *)
Class CurKtier := cur_ktier : ktier.
Global Typeclasses Opaque cur_ktier.

(* THE LOW-PRIORITY GLOBAL DEFAULT (see the header).  Priority 100 is the
   whole mechanism: a [Local Instance : CurKtier := KT1] in a post-boot file
   resolves first, whether it is declared before or after this one. *)
Global Instance curktier_default : CurKtier | 100 := KT0.
