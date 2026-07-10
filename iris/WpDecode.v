From Stdlib Require Import ZArith.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec.

(* cE Zicsr = hartSupports Zicsr = true, at any Acc level. *)
Lemma exec_rec_cE_Zicsr_any (k : Z) (acc : Acc (Zwf 0) k) s :
  Z.geb k 0 = true ->
  exec (_rec_currentlyEnabled Ext_Zicsr k acc) s = Some (true, s).
Proof.
  intro Hk. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  rewrite Hk. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  apply exec_hartSupports_Zicsr.
Qed.

Lemma exec_hartSupports_Zicfilp s : exec (hartSupports Ext_Zicfilp) s = Some (true, s).
Proof.
  unfold hartSupports. destruct (Defs.Zwf_guarded _).
  cbn [_rec_hartSupports]. unfold Defs.assert_exp'.
  replace (Z.geb (hartSupports_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). apply exec_returnM.
Qed.

(* currentlyEnabled Ext_S = (misa.S bit), at Acc level 1 (stated with a [k = 1]
   equation so the call site's syntactic level [measure - 1 - 1] unifies).
   The reduced-budget twin of RiscvFetchExec's [exec_currentlyEnabled_S],
   needed inside [get_xLPE]'s User arm.  (The level cannot be left symbolic:
   the Ext_S arm's inner recursion consumes the assert_exp' PROOF, so the
   [k >=? 0] guard cannot be rewritten dependently -- with a concrete level,
   [replace ... by reflexivity] goes through by conversion.) *)
Lemma exec_rec_cE_S_1 (k : Z) (acc : Acc (Zwf 0) k) s :
  k = 1 ->
  exec (_rec_currentlyEnabled Ext_S k acc) s
    = Some (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1"), s).
Proof.
  intro Hk. subst k. destruct acc. cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb 1 0) with true by reflexivity. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_S s)).
  rewrite (exec_and_boolM_Some _ _ s
             (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) s).
  2:{ rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg misa s)). apply exec_returnM. }
  destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")) eqn:Hb.
  - apply exec_rec_cE_Zicsr_any. vm_compute; reflexivity.
  - reflexivity.
Qed.

(* read_senvcfg is three register reads + returnM: always succeeds, no state
   change (the value is irrelevant to the decode walker). *)
Lemma exec_read_senvcfg_any s :
  exists v : mword 64, exec (read_senvcfg tt) s = Some (v, s).
Proof.
  unfold read_senvcfg.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg senvcfg s)).
  eexists. apply exec_returnM.
Qed.

(* currentlyEnabled Ext_Zicfilp reduces (to SOME boolean, state unchanged) in
   ANY non-virtualized privilege: [get_xLPE] is a plain register read in M
   (mseccfg) and S (menvcfg), and in U it is currentlyEnabled Ext_S followed by
   a senvcfg-or-menvcfg read -- all total.  The VALUE is irrelevant to every
   non-lpad decode (the guard's and_boolM result is [b && false = false]). *)
Lemma exec_cE_zicfilp_mSU s :
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exists b, exec (currentlyEnabled Ext_Zicfilp) s = Some (b, s).
Proof.
  intro Hpriv.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  (* outer and_boolM: cE Zicsr = true *)
  rewrite (exec_and_boolM_Some _ _ _ _ _
            (exec_rec_cE_Zicsr_any (currentlyEnabled_measure Ext_Zicfilp - 1) _ s
               ltac:(vm_compute; reflexivity))).
  cbn match.
  (* inner and_boolM: hartSupports Zicfilp = true *)
  rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_hartSupports_Zicfilp s)). cbn match.
  (* read cur_privilege, then dispatch get_xLPE on the (non-virtual) value *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  destruct (register_lookup cur_privilege (sregs s)) eqn:Hp;
    try discriminate Hpriv.
  - (* User: get_xLPE = cE Ext_S >>= (senvcfg | menvcfg read) *)
    match goal with |- context[_rec_get_xLPE User _ ?acc] => destruct acc end.
    cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_rec_cE_S_1 (currentlyEnabled_measure Ext_Zicfilp - 1 - 1) _ s
                 ltac:(vm_compute; reflexivity))).
    cbn beta.
    destruct (eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1")).
    + destruct (exec_read_senvcfg_any s) as [v Hv].
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      eexists. apply exec_returnM.
    + rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn match beta.
      eexists. apply exec_returnM.
  - (* Supervisor: get_xLPE = read menvcfg >>= returnM (LPE bit) *)
    match goal with |- context[_rec_get_xLPE Supervisor _ ?acc] => destruct acc end.
    cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn match beta.
    eexists. apply exec_returnM.
  - (* Machine: get_xLPE = read mseccfg >>= returnM (MLPE bit) *)
    match goal with |- context[_rec_get_xLPE Machine _ ?acc] => destruct acc end.
    cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
    replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
    cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). cbn match beta.
    eexists. apply exec_returnM.
Qed.


Lemma exec_cE_pause s : exists b, exec (currentlyEnabled Ext_Zihintpause) s = Some (b, s).
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  cbn [_rec_currentlyEnabled]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zihintpause) 0) with true by reflexivity.
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  eexists; reflexivity.
Qed.

(* One-shot elimination of the shared PAUSE/Zicfilp prefix (mirrors the RVC
   one-shot bridge in WpRvcBridge.v, applied to the two stateful gates that
   sit unconditionally at the head of the BASE decoder). Proven ONCE, fully
   symbolic in [THEN1]/[THEN2]/[INNER]/[K]: for any non-PAUSE/non-LPAD word
   (R1/R2 = false) and non-virtual privilege, the whole gated prefix collapses
   to just running [INNER] (and then the caller's continuation [K]). Each
   [decode_any] call site then does ONE [erewrite] instead of
   [decode_pause_prefix]'s ~7 tactic steps, each of which used to retype the
   entire (still-concrete, ~4000-line) decoder tail -- that retyping, not
   [decode_finish]'s own [vm_compute] (already ~0.07s, opcode-depth-independent),
   was the real cost (measured ~2.4-3.4s/call; see build-perf-profile memory). *)
Lemma exec_bind_assoc {A B C} (m : M A) (f : A -> M B) (g : B -> M C) s :
  exec (Defs.bind (Defs.bind m f) g) s = exec (Defs.bind m (fun a => Defs.bind (f a) g)) s.
Proof.
  rewrite !exec_bind. destruct (exec m s) as [[a s1]|]; [rewrite exec_bind|]; reflexivity.
Qed.

Lemma decode_prefix_elim {U} (R1 R2 : bool) (THEN1 THEN2 INNER : M (option instruction))
    (K : option instruction -> M U) s :
  R1 = false -> R2 = false ->
  priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (Defs.bind (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM R1))
          (fun w10 => Defs.bind
                        (if w10 then THEN1
                         else Defs.bind (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM R2))
                                (fun w12 => if w12 then THEN2 else INNER))
                        K)) s
  = exec (Defs.bind INNER K) s.
Proof.
  intros HR1 HR2 Hpriv. subst R1 R2.
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_pause s) as [bp Hbp].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp).
    destruct bp; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA1); cbn match.
  rewrite exec_bind_assoc.
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)).
  { destruct (exec_cE_zicfilp_mSU s Hpriv) as [bz Hbz].
    rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz).
    destruct bz; [apply exec_returnm | reflexivity]. }
  rewrite (exec_bind_Some _ _ _ _ _ HA2); cbn match.
  reflexivity.
Qed.

Definition w_auipc : mword 32 := mword_of_int 0xa117.

(* Head-only clause skip: when the head decoder clause's guard is concretely
   false, drop that clause AND its [match]-on-None continuation in ONE rewrite,
   WITHOUT traversing the ~4000-clause tail.  This collapses the O(#clauses^2)
   cost of a [repeat skip_pure_clause] walk (which re-[cbn]s / re-[context]-
   matches the whole remaining decoder per clause) down to O(#clauses).
   The resulting goal [exec REST s = _] is definitionally identical to what the
   old context-based [skip_pure_clause] produced, so it is a drop-in. *)
Lemma skip_clause_head (c : M (option instruction)) (g : bool) (REST : M instruction) s :
  g = false ->
  exec (Defs.bind (if g then c else returnM None)
          (fun w => match w with Some r => returnM r | None => REST end)) s
    = exec REST s.
Proof.
  intros ->.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None instruction) s)). reflexivity.
Qed.


(* Batched forms: one [erewrite] per 16 (resp. 4) false-guard clauses.  The
   per-clause walk retypes the O(#clauses) decoder tail at every step (Ltac
   profiling: 47% of WpGprMretWp); batching makes that retyping happen
   ~log-many times.  [skip_pure_clauses] tries 16, then 4, then 1. *)
Lemma skip_clause_head16 (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 : M (option instruction)) (g1 : bool) (g2 : bool) (g3 : bool) (g4 : bool) (g5 : bool) (g6 : bool) (g7 : bool) (g8 : bool) (g9 : bool) (g10 : bool) (g11 : bool) (g12 : bool) (g13 : bool) (g14 : bool) (g15 : bool) (g16 : bool)
    (REST : M instruction) s :
  g1 = false -> g2 = false -> g3 = false -> g4 = false -> g5 = false -> g6 = false -> g7 = false -> g8 = false -> g9 = false -> g10 = false -> g11 = false -> g12 = false -> g13 = false -> g14 = false -> g15 = false -> g16 = false ->
  exec (Defs.bind (if g1 then c1 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g2 then c2 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g3 then c3 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g4 then c4 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g5 then c5 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g6 then c6 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g7 then c7 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g8 then c8 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g9 then c9 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g10 then c10 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g11 then c11 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g12 then c12 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g13 then c13 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g14 then c14 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g15 then c15 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g16 then c16 else returnM None)
          (fun w => match w with Some r => returnM r | None => REST end) end) end) end) end) end) end) end) end) end) end) end) end) end) end) end)) s
    = exec REST s.
Proof.
  intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.
  repeat (erewrite skip_clause_head by reflexivity). reflexivity.
Qed.

Lemma skip_clause_head4 (c1 c2 c3 c4 : M (option instruction)) (g1 : bool) (g2 : bool) (g3 : bool) (g4 : bool)
    (REST : M instruction) s :
  g1 = false -> g2 = false -> g3 = false -> g4 = false ->
  exec (Defs.bind (if g1 then c1 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g2 then c2 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g3 then c3 else returnM None)
          (fun w => match w with Some r => returnM r | None => Defs.bind (if g4 then c4 else returnM None)
          (fun w => match w with Some r => returnM r | None => REST end) end) end) end)) s
    = exec REST s.
Proof.
  intros -> -> -> ->.
  repeat (erewrite skip_clause_head by reflexivity). reflexivity.
Qed.

Ltac skip_pure_clause :=
  first
  [ erewrite skip_clause_head by (vm_compute; reflexivity)
  | match goal with
    | |- context[if ?g then _ else returnM None] =>
        replace g with false by (vm_compute; reflexivity)
    end;
    cbn match;
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (@None instruction) _));
    cbn match ].

Ltac skip_pure_clauses :=
  repeat (erewrite skip_clause_head16 by (vm_compute; reflexivity));
  repeat (erewrite skip_clause_head4 by (vm_compute; reflexivity));
  repeat skip_pure_clause.

(* [decode_finish s]: for an instruction that is NOT extension-gated, the
   remaining decoder is a read-free pure function of the (concrete) word, so a
   single reduction collapses ALL of its clause guards at once -- replacing the
   O(#clauses^2) goal re-traversal of a clause-by-clause [repeat skip_pure_clause]
   walk (e.g. decode_ld 6.5s -> ~0s).  We first [vm_compute] the decoder term [d]
   in isolation and splice it back ([change_no_check] is sound: [r] is by
   construction the vm-normal form of [d]); pre-normalizing the small term makes
   the closing [vm_compute] cheap.  The [try] lets it also work when the goal
   isn't yet in [exec d s] head form (then the closing reduction does it all). *)
Ltac decode_finish s :=
  try (match goal with
       | |- exec ?d s = _ =>
           let r := eval vm_compute in d in change_no_check (exec d s) with (exec r s)
       end);
  vm_compute; reflexivity.

(* the shared PAUSE/Zicfilp prefix: 2 pure skips + the two currentlyEnabled
   and_boolM clauses (both collapse to [false] for any non-LPAD/PAUSE word).
   These two clauses are the ONLY stateful part of the 32-bit decoder for a
   non-extension-gated instruction: [currentlyEnabled Zihintpause] and
   [currentlyEnabled Zicfilp] read state (the latter needs a NON-VIRTUAL
   privilege, hence [Hpriv]), so [vm_compute] cannot step through them.
   [Hpriv] may be EITHER the membership fact
   [priv_mSU (register_lookup cur_privilege (sregs s)) = true] itself OR a
   value equation [register_lookup cur_privilege (sregs s) = Machine/
   Supervisor/User] (converted on the fly). *)
Ltac decode_pause_prefix s Hpriv :=
  unfold ext_decode, encdec_backwards; cbv beta; cbn zeta;
  skip_pure_clause; skip_pure_clause;
  match goal with |- context[eq_vec ?w ?c] =>
    replace (eq_vec w c) with false by (vm_compute; reflexivity) end;
  match goal with |- context[eq_vec (subrange_vec_dec ?w 11 0) ?c] =>
    replace (eq_vec (subrange_vec_dec w 11 0) c) with false by (vm_compute; reflexivity) end;
  let HA1 := fresh "HA1" in
  assert (HA1 : exec (Defs.and_boolM (currentlyEnabled Ext_Zihintpause) (returnM false)) s
                = Some (false, s)) by
    (let bp := fresh in let Hbp := fresh in
     destruct (exec_cE_pause s) as [bp Hbp];
     rewrite (exec_and_boolM_Some _ _ _ _ _ Hbp); destruct bp; [apply exec_returnm | reflexivity]);
  rewrite (exec_bind_Some _ _ _ _ _ HA1); cbn match; clear HA1;
  rewrite exec_bind;
  let HA2 := fresh "HA2" in
  assert (HA2 : exec (Defs.and_boolM (currentlyEnabled Ext_Zicfilp) (returnM false)) s
                = Some (false, s)) by
    (let bz := fresh in let Hbz := fresh in
     destruct (exec_cE_zicfilp_mSU s
                 ltac:(first [exact Hpriv | rewrite Hpriv; reflexivity])) as [bz Hbz];
     rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]);
  rewrite (exec_bind_Some _ _ _ _ _ HA2); cbn match; clear HA2.

(* ONE-SHOT decoder for (almost) any 32-bit instruction word: peel the shared
   stateful PAUSE/Zicfilp prefix via the [decode_prefix_elim] bridge (one
   [erewrite] instead of [decode_pause_prefix]'s ~7 tactic steps -- see the
   comment there), then [decode_finish] collapses the entire read-free
   remainder in a single [vm_compute].  Works for ALL of base RV64I +
   Zicsr -- lui/auipc, loads/stores, branches, jal/jalr, the OP-IMM/OP arithmetic
   family, and csrr/csrw/csrrs -- with no per-opcode clause stepping.
   LIMITATION: it does NOT handle instructions sitting behind a *misa-gated*
   extension clause (M mul/div, A atomics, C compressed, F/D), because their
   [currentlyEnabled Ext_*] reads the misa register and [vm_compute] gets stuck on
   it (just like Zicfilp).  Those still need the relevant misa hypothesis to peel
   their gate before finishing.
   [unshelve] keeps the two [R1 = false]/[R2 = false] side conditions as
   ordinary trailing goals (rather than silently shelved, which [decode_finish]
   would then never discharge); [decode_finish] closes those goals too, since
   its [try] step is a no-op on a non-[exec]-headed goal and it falls through
   to plain [vm_compute; reflexivity]. *)
Ltac decode_any s Hpriv :=
  lazymatch goal with
  | |- exec (ext_decode ?w) s = _ =>
      unfold ext_decode, encdec_backwards; cbv beta; cbn zeta;
      skip_pure_clause; skip_pure_clause;
      unshelve erewrite (decode_prefix_elim _ _ _ _ _ _ s _ _ Hpriv);
      decode_finish s
  end.

Definition imm_auipc : mword 20 := subrange_vec_dec w_auipc 31 12.
Definition i_auipc : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_auipc 11 7) (regidx_bit_width - 1) 0).

(* decode_auipc / decode_ld now live in WpEntryNew.v (their only user), to
   keep this shared-prefix file cheap. *)

(* [ld sp, N(sp)] loading the boot stack pointer via a GOT-relative offset
   from _entry's auipc; N tracks wherever the linker places the GOT/stack0
   data, so this literal must be re-synced whenever the kernel image's data
   segment shifts (last synced: N = 0x208, i.e. stack0's current GOT slot). *)
Definition w_ld : mword 32 := mword_of_int 0x20813103.

Definition imm_ld : mword 12 := subrange_vec_dec w_ld 31 20.
Definition i_ld : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_ld 11 7) (regidx_bit_width - 1) 0).

