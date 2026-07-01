From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec WpAdd WpFetch.

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

Lemma exec_cE_zicfilp_M s :
  register_lookup cur_privilege (sregs s) = Machine ->
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
  (* read cur_privilege = Machine *)
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  (* get_xLPE Machine = read mseccfg >>= returnM (MLPE bit) *)
  match goal with |- context[_rec_get_xLPE Machine _ ?acc] => destruct acc end.
  cbn [_rec_get_xLPE]. unfold Defs.assert_exp'.
  replace (Z.geb (currentlyEnabled_measure Ext_Zicfilp - 1) 0) with true by (vm_compute; reflexivity).
  cbn match. rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM eq_refl s)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mseccfg s)). cbn match.
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
   [currentlyEnabled Zicfilp] read state (the latter needs cur_privilege=Machine,
   hence [Hpriv]), so [vm_compute] cannot step through them. *)
Ltac decode_pause_prefix s Hpriv :=
  unfold ext_decode, encdec_backwards; cbv beta; cbn zeta;
  skip_pure_clause; skip_pure_clause;
  match goal with |- context[eq_vec ?w (?c : mword 32)] =>
    replace (eq_vec w c) with false by (vm_compute; reflexivity) end;
  match goal with |- context[eq_vec (subrange_vec_dec ?w 11 0) (?c : mword 12)] =>
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
     destruct (exec_cE_zicfilp_M s Hpriv) as [bz Hbz];
     rewrite (exec_and_boolM_Some _ _ _ _ _ Hbz); destruct bz; [apply exec_returnm | reflexivity]);
  rewrite (exec_bind_Some _ _ _ _ _ HA2); cbn match; clear HA2.

(* ONE-SHOT decoder for (almost) any 32-bit instruction word: peel the shared
   stateful PAUSE/Zicfilp prefix, then [decode_finish] collapses the entire
   read-free remainder in a single [vm_compute].  Works for ALL of base RV64I +
   Zicsr -- lui/auipc, loads/stores, branches, jal/jalr, the OP-IMM/OP arithmetic
   family, and csrr/csrw/csrrs -- with no per-opcode clause stepping.
   LIMITATION: it does NOT handle instructions sitting behind a *misa-gated*
   extension clause (M mul/div, A atomics, C compressed, F/D), because their
   [currentlyEnabled Ext_*] reads the misa register and [vm_compute] gets stuck on
   it (just like Zicfilp).  Those still need the relevant misa hypothesis to peel
   their gate before finishing. *)
Ltac decode_any s Hpriv := decode_pause_prefix s Hpriv; decode_finish s.

Definition imm_auipc : mword 20 := subrange_vec_dec w_auipc 31 12.
Definition i_auipc : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_auipc 11 7) (regidx_bit_width - 1) 0).

(* decode_auipc / decode_ld moved to KernelBoot.v (their only user)
   to keep this shared-prefix file cheap. *)

Definition w_ld : mword 32 := mword_of_int 0x1d813103.

Definition imm_ld : mword 12 := subrange_vec_dec w_ld 31 20.
Definition i_ld : mword 5 :=
  autocast (subrange_vec_dec (subrange_vec_dec w_ld 11 7) (regidx_bit_width - 1) 0).

