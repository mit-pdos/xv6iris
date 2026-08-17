(* WpDecodeBridge.v -- the per-word concrete/symbolic decode bridge.

   Decoding a 32-bit word over a SYMBOLIC system state is slow: the decoder's
   Zicfilp / Zihintpause / extension-gate probes read symbolic config registers,
   so [vm_compute] gets stuck and the decode must be peeled clause-by-clause by
   hand (decode_any: ~4-11s per instruction).  Over a FULLY CONCRETE state every
   probe read resolves, so [vm_compute] reduces the whole decoder in one pass
   (~0.02-0.05s -- two orders of magnitude faster).

   This file makes the concrete result usable for the symbolic proofs.  It proves
   a generic read-frame congruence ([exec_goodb_congr], by induction on the monad
   -- NOT by traversing the decoder), packages the concrete reference state
   [dstate], and exposes the transport as [decode_state_bridge].

   The transport condition is PER WORD: [s] must agree with [dstate] on exactly
   the registers THAT word's decode reads -- the set [D]; its complement is the
   per-word DON'T-CARE set.  Both dst-side obligations ([goodb D (ext_decode w)
   dstate] and the concrete decode) are single [vm_compute]s.  A decode lemma reads

     Lemma decode_foo s : agree_on D_foo s (dstate Machine) ->
                          exec (ext_decode w_foo) s = Some (i, s).

   The concrete register values are chosen CONSISTENT with [hw_config]
   (RiscvFetchExec.v): [misa] has S/C/U/M/A set, and [mseccfg]'s PMM field is
   Disabled with MLPE clear (both hold of the all-zero / [MISA_C] choices here).*)
From Stdlib Require Import ZArith.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvExec RiscvFetchExec.
From stdpp Require Import gmap.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* 1. goodb: a read-only, reads-within-[D] witness, following the actual  *)
(*    (state-resolved) execution path -- fully [vm_compute]-able over a    *)
(*    concrete state.                                                      *)
(* ===================================================================== *)
Fixpoint goodb (D : register -> bool) {X} (m : M X) (s : mstate) {struct m} : bool :=
  match m with
  | Interface.Ret _ => true
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> bool with
       | Interface.RegRead r _ => fun k => andb (D r) (goodb D (k (register_lookup r s.(sregs))) s)
       | Interface.InstrAnnounce _   => fun k => goodb D (k tt) s
       | Interface.BranchAnnounce _ _=> fun k => goodb D (k tt) s
       | Interface.Barrier _         => fun k => goodb D (k tt) s
       | Interface.CacheOp _         => fun k => goodb D (k tt) s
       | Interface.TlbOp _           => fun k => goodb D (k tt) s
       | Interface.TakeException _   => fun k => goodb D (k tt) s
       | Interface.ReturnException _ => fun k => goodb D (k tt) s
       | Interface.TranslationStart _=> fun k => goodb D (k tt) s
       | Interface.TranslationEnd _  => fun k => goodb D (k tt) s
       | Interface.CycleCount        => fun k => goodb D (k tt) s
       | Interface.Message _         => fun k => goodb D (k tt) s
       | Interface.GetCycleCount     => fun k => goodb D (k 0%Z) s
       | _ => fun _ => false
       end) k
  end.

(* ===================================================================== *)
(* [goodb] COMPOSES ALONG A BIND -- and this is what makes a certificate     *)
(* affordable for a stretch that carries SYMBOLIC DATA.                      *)
(*                                                                          *)
(* [goodb] is normally discharged by [vm_compute] at the concrete reference   *)
(* state.  That works only when the whole term is data-free: measured,        *)
(* [goodb D_m (legalize_menvcfg o v) dstateM] with [o]/[v] FREE finishes      *)
(* under none of vm_compute / cbv / lazy, because the evaluators normalise    *)
(* the symbolic bitvector expressions even though goodb's ANSWER cannot       *)
(* depend on them.                                                           *)
(*                                                                          *)
(* With this lemma the certificate is assembled instead of computed: each     *)
(* sub-stretch of such a chain ([currentlyEnabled X], [hartSupports X]) takes *)
(* no argument and IS data-free, so each piece is one cheap [vm_compute], and *)
(* the symbolic data only ever sits in [Ret] positions, where [goodb] returns *)
(* [true] without looking.                                                   *)
(*                                                                          *)
(* [exec m s = Some (x, s)] is not an extra burden: [goodb] already forbids   *)
(* writes, so any [goodb]-certified stretch preserves the state, and that     *)
(* fact is exactly what [exec_goodb_congr] hands back.                        *)
(* ===================================================================== *)
Lemma goodb_bind (D : register -> bool) {X Y} (m : M X) (f : X -> M Y)
    (s : mstate) (x : X) :
  goodb D m s = true -> exec m s = Some (x, s) ->
  goodb D (Defs.bind m f) s = goodb D (f x) s.
Proof.
  revert x. induction m as [y | T oc k IH]; intros x Hg He.
  - cbn [exec] in He. assert (Hx : x = y) by congruence. subst x. reflexivity.
  - destruct oc; cbn [goodb exec Defs.bind Interface.iMon_bind] in Hg, He |- *;
      try discriminate Hg.
    all: first
      [ (apply andb_prop in Hg as [HDr Hg']; rewrite HDr;
         by apply (IH _ x Hg' He))
      | by apply (IH tt x Hg He)
      | by apply (IH 0%Z x Hg He) ].
Qed.

Lemma goodb_bind0 (D : register -> bool) {Y} (m : M unit) (n : M Y)
    (s : mstate) :
  goodb D m s = true -> exec m s = Some (tt, s) ->
  goodb D (Defs.bind0 m n) s = goodb D n s.
Proof. intros Hg He. exact (goodb_bind D m (fun _ => n) s tt Hg He). Qed.

(* ===================================================================== *)
(* 2. The generic read-frame congruence (proved ONCE, by induction on the *)
(*    monad).  If [m] run from [s1] only reads [D]-registers (goodb) and    *)
(*    [s1],[s2] agree on every [D]-register, then [m] yields the same value *)
(*    from both states, each leaving its own state untouched.              *)
(* ===================================================================== *)
Lemma exec_goodb_congr (D : register -> bool) {X} (m : M X) (s1 s2 : mstate) :
  (forall r, D r = true -> register_lookup r s1.(sregs) = register_lookup r s2.(sregs)) ->
  goodb D m s1 = true ->
  exists x, exec m s1 = Some (x, s1) /\ exec m s2 = Some (x, s2).
Proof.
  intros Hagree. revert s2 Hagree.
  induction m as [y | T oc k IH]; intros s2 Hagree Hgood.
  - exists y. split; reflexivity.
  - destruct oc; cbn [goodb exec] in Hgood |- *; try discriminate Hgood;
      try (apply (IH _ s2 Hagree Hgood)).
    apply andb_prop in Hgood as [HDr Hgood'].
    match goal with
    | HDr : D ?rr = true |- _ =>
      pose proof (Hagree _ HDr) as Hr; rewrite <- Hr;
      apply (IH (register_lookup rr s1.(sregs)) s2 Hagree Hgood')
    end.
Qed.

(* register_beq reflects equality -- to discharge the per-register agreement. *)
Lemma register_beq_eq (r r' : register) : register_beq r r' = true -> r = r'.
Proof.
  destruct r, r'; simpl; try discriminate; intro H;
    autorewrite with register_beq_iffs in H; subst; reflexivity.
Qed.

(* ===================================================================== *)
(* 3. The concrete reference state (privilege-parametric) and the single   *)
(*    agreement predicate.                                                 *)
(* ===================================================================== *)

(* [MISA_C] (platform misa) and [MENVCFG_S] (post-boot S-mode menvcfg) are the
   shared reference-config constants defined in RiscvFetchExec.

   The concrete register file [dregs mv p]: [misa] = MISA_C, [menvcfg] = [mv],
   every other config CSR (mseccfg/senvcfg/...) = 0.  The [menvcfg] value is a
   PARAMETER because the landing-pad probe reads it (its value is discarded via
   [_ && false], but the read-frame witness [goodb] compares WHOLE values, so
   [dregs]'s menvcfg must MATCH the symbolic state's).  Machine-mode decode reads
   [mseccfg]=0 (not menvcfg) so [mv] is irrelevant there; Supervisor-mode decode
   reads [menvcfg], so [mv] must be the actual S-mode value [MENVCFG_S]. *)
Definition dregs (mv : mword 64) (p : Privilege) : regstate :=
  {[ {[ init_regstate with Privilege_s := fun _ => p ]}
       with bitvector_64_s :=
         fun r => if register_bitvector_64_beq r misa then MISA_C
                  else if register_bitvector_64_beq r menvcfg then mv
                  else mword_of_int 0 ]}.
Definition dstate (mv : mword 64) (p : Privilege) : mstate :=
  MState (dregs mv p) ∅ dev0_state.

(* The two reference states the kernel decodes against: Machine (menvcfg
   irrelevant -> 0) and Supervisor (menvcfg = the post-boot [MENVCFG_S]). *)
Notation dstateM := (dstate (mword_of_int 0) Machine).
Notation dstateS := (dstate MENVCFG_S Supervisor).

(* [agree_on D s dst]: [s] coincides with the concrete reference [dst] on the
   D-part of the register file -- the SOLE state-side precondition of the bridge. *)
Definition agree_on (D : register -> bool) (s dst : mstate) : Prop :=
  forall r, D r = true -> register_lookup r s.(sregs) = register_lookup r dst.(sregs).

(* ===================================================================== *)
(* 4. The generic per-word bridge.  Given that [m] reads only [D] on the    *)
(*    concrete [dst] ([goodb]) and [s] agrees with [dst] on [D], the         *)
(*    concrete decode result transports to [s].  Proved via the read-frame   *)
(*    congruence -- never traverses the decoder.                             *)
(* ===================================================================== *)
Lemma decode_state_bridge (D : register -> bool) {X} (m : M X) (dst s : mstate) (i : X) :
  agree_on D s dst ->
  goodb D m dst = true ->
  exec m dst = Some (i, dst) ->
  exec m s = Some (i, s).
Proof.
  intros Hag Hgood Hdst.
  destruct (exec_goodb_congr D m dst s (fun r HD => eq_sym (Hag r HD)) Hgood) as [x [Hd Hs]].
  rewrite Hdst in Hd. injection Hd as <-. exact Hs.
Qed.

(* Discharge the two dst-side obligations ([goodb] + concrete decode) by
   [vm_compute]; the agreement hypothesis is left to the caller ([assumption]). *)
Ltac decode_bridge D dst :=
  apply (decode_state_bridge D _ dst _ _);
  [ assumption | vm_compute; reflexivity | vm_compute; reflexivity ].

(* ===================================================================== *)
(* 5. The config-fact interface used by the [instr] decode obligation.     *)
(*                                                                          *)
(* The landing-pad probe reads mseccfg in Machine but menvcfg in Supervisor *)
(* (get_xLPE dispatches on cur_privilege); its value is discarded either way *)
(* ([_ && false]) but the read-frame witness compares WHOLE values, so each  *)
(* must MATCH the reference state.  CSR/extension-gated words additionally   *)
(* read misa (Zicsr / Ext_* gates).  Hence the two per-privilege read-sets:  *)
(*   [D_m] = {cur_privilege, mseccfg, misa}   (Machine)                      *)
(*   [D_s] = {cur_privilege, menvcfg, misa}   (Supervisor)                   *)
(* (superset of what any single word reads; [goodb] verifies the actual read *)
(* set is CONTAINED, and the extra members are cheap to agree on).           *)
(* ===================================================================== *)
Definition D_m (r : register) : bool :=
  register_beq r (R_Privilege cur_privilege) ||
  register_beq r (R_bitvector_64 mseccfg) ||
  register_beq r (R_bitvector_64 misa).
Definition D_s (r : register) : bool :=
  register_beq r (R_Privilege cur_privilege) ||
  register_beq r (R_bitvector_64 menvcfg) ||
  register_beq r (R_bitvector_64 misa).

(* Build [agree_on] from the config facts the [instr] obligation supplies.
   Machine: cur_privilege = Machine, mseccfg = 0, misa = MISA_C.
   Supervisor: cur_privilege = Supervisor, menvcfg = MENVCFG_S, misa = MISA_C. *)
Lemma agree_m (s : mstate) :
  register_lookup cur_privilege s.(sregs) = Machine ->
  register_lookup mseccfg s.(sregs) = mword_of_int 0 ->
  register_lookup misa s.(sregs) = MISA_C ->
  agree_on D_m s dstateM.
Proof.
  intros Hp Hms Hmi r Hr. unfold D_m in Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; [apply orb_true_elim in Hr as [Hr|Hr]|];
    apply register_beq_eq in Hr; subst r; [rewrite Hp|rewrite Hms|rewrite Hmi];
    vm_compute; reflexivity.
Qed.
Lemma agree_s (s : mstate) :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup menvcfg s.(sregs) = MENVCFG_S ->
  register_lookup misa s.(sregs) = MISA_C ->
  agree_on D_s s dstateS.
Proof.
  intros Hp Hme Hmi r Hr. unfold D_s in Hr.
  apply orb_true_elim in Hr as [Hr|Hr]; [apply orb_true_elim in Hr as [Hr|Hr]|];
    apply register_beq_eq in Hr; subst r; [rewrite Hp|rewrite Hme|rewrite Hmi];
    vm_compute; reflexivity.
Qed.

(* [cfg_ok] (RiscvFetchExec) is the config precondition the [instr] decode
   obligation hands the producer; with misa = MISA_C it is exactly what
   [agree_m]/[agree_s] need.

   THE per-word decode tactic: from [misa = MISA_C] and [cfg_ok] in the goal's
   hypotheses, discharge [exec (ext_decode w) s = Some (<explicit AST>, s)] via
   the concrete bridge (the two [vm_compute]s verify the read-set and that the
   AST matches the concrete decode -- for BOTH the Machine and Supervisor
   reference states).  ~0.02s/word vs ~3-11s for [decode_any]. *)
Ltac decode_bridge_ms :=
  let Hmisa := fresh "Hmisa" in let Hcfg := fresh "Hcfg" in
  intros Hmisa Hcfg;
  destruct Hcfg as [[? ?]|[? ?]];
  [ apply (decode_state_bridge D_m _ dstateM);
      [ apply agree_m; assumption | vm_compute; reflexivity | vm_compute; reflexivity ]
  | apply (decode_state_bridge D_s _ dstateS);
      [ apply agree_s; assumption | vm_compute; reflexivity | vm_compute; reflexivity ] ].

(* [decode_bridge_ms] closes its concrete-decode obligation with a bare
   [vm_compute; reflexivity], which needs the two sides' bitvector
   WELL-FORMEDNESS PROOF TERMS to coincide.  For some words they do not: a CSRImm
   word's 5-bit uimm arrives as a SLICE of the instruction word while the CSR
   leaves (WpSconfCsr.v) phrase it as [mword_of_int 2], and a virtio MMIO word's
   immediate likewise.  Only [bv_eq] closes such a pair.  [decode_bridge_ms_bv]
   is the same bridge with the leafwise closing [rvc_oneshot] uses: descend the
   AST with [f_equal] and close each field by [reflexivity] or [bv_eq].

   [bv_eq] is spelled QUALIFIED: this file deliberately does not [Import]
   stdpp's bitvector.definitions (it is already loaded transitively, but
   importing it here would change the namespace of every file that imports the
   bridge). *)
Ltac decode_bridge_ms_bv :=
  let Hmisa := fresh "Hmisa" in let Hcfg := fresh "Hcfg" in
  intros Hmisa Hcfg;
  destruct Hcfg as [[? ?]|[? ?]];
  [ apply (decode_state_bridge D_m _ dstateM);
      [ apply agree_m; assumption | vm_compute; reflexivity
      | vm_compute;
        repeat first [ reflexivity | (apply bitvector.definitions.bv_eq; vm_compute; reflexivity) | f_equal ] ]
  | apply (decode_state_bridge D_s _ dstateS);
      [ apply agree_s; assumption | vm_compute; reflexivity
      | vm_compute;
        repeat first [ reflexivity | (apply bitvector.definitions.bv_eq; vm_compute; reflexivity) | f_equal ] ] ].
