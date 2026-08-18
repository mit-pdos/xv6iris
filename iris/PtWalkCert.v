(* ====================================================================== *)
(* PtWalkCert.v -- THE FOOTPRINT CERTIFICATES OF THE Sv39 PAGE WALK.       *)
(*                                                                        *)
(* Package P3 of the user-tier port (claude-notes/projects/user-tier-port  *)
(* section 4.3, rows [CommonWalk] and [PtTreeAdue]): for every [exec_X]    *)
(* the walk layer already has, the twin [goodmb_X] with the SAME binders   *)
(* and hypotheses, generic in [(Dr Dw : register -> bool)] with one        *)
(* [Dr r = true] per register the stretch reads, and at an ARBITRARY byte  *)
(* map [mm] with the two pure obligations a memory node owes               *)
(* ([bytes_owned mm pa 8 = true] and [dev_addr pa = false]) -- both        *)
(* projections of [UserBytes.u_mem_wf] at the caller                       *)
(* ([u_mem_wf_owned] / [u_mem_wf_not_dev]).                                *)
(*                                                                        *)
(* The assembly toolkit is [HartMemAsm]'s [gm_*] / [gmm_*] family: a twin  *)
(* here is its [exec] lemma's proof node for node, with each [exec_bind_*] *)
(* replaced by the [gm_*] of the same shape and the head's [exec] fact     *)
(* PAIRED with the head's own certificate.                                 *)
(*                                                                        *)
(* WHY THIS IS A SEPARATE FILE AND NOT [CommonWalk.v] / [PtTreeAdue.v].    *)
(* Those two carry 769 and 763 dependents; an ADDITIVE change to either    *)
(* costs that cone on every iteration and breaks every sibling lane's      *)
(* single-file [coqc] loop (durable-notes: an additive change to a shared  *)
(* file belongs in a NEW LEAF FILE, folded back at a milestone).  This is  *)
(* the same call [HartStepFull.v] made against [HartStepAny.v].  FOLD THE  *)
(* SECTIONS BACK beside their exec twins at the milestone -- section 1     *)
(* into [SmodePte.v], section 2 into [CommonWalk.v], section 3 into        *)
(* [PtTreeAdue.v].                                                         *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpDecodeBridge HartGoodb HartMemRun HartMemAsm PtBytes.
Require Import MemAccessGen WpLoad SmodePte CommonWalk.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 0. TWO PEELS [HartMemAsm] DOES NOT HAVE, AND WHY THE PMP/PMA CHAIN      *)
(*    NEEDS THEM.  (FOLD BACK into [HartMemAsm] sections 2 and 5.)         *)
(*                                                                        *)
(* [pmpCheck]'s body is [(H >>= K) >>= L >> Tail] -- Sail's [foreach] loop *)
(* wrapped in an early-return region -- i.e. a LEFT nest THREE deep, and   *)
(* [HartMemAsm]'s [_nest] family peels only one level.  Two things fix it: *)
(*   - [bindR_ret] / [bindm_ret]: a [returnm]/[returnR] head is a          *)
(*     CONVERSION, so the loop's [if i >? 0 then ... else returnR ...]     *)
(*     prologue is rewritten away rather than peeled;                      *)
(*   - the depth-2 twins below, which are [goodmb_cer_bind_nest]'s          *)
(*     induction with one more [bind] layer.                               *)
(* ===================================================================== *)

Lemma bindR_ret {R E X Y} (x : X) (f : X -> Defs.monadR R E Y) :
  Defs.bind (Defs.returnR R x) f = f x.
Proof. reflexivity. Qed.

Lemma bindm_ret {E X Y} (x : X) (f : X -> Defs.monad E Y) :
  Defs.bind (Defs.returnm x) f = f x.
Proof. reflexivity. Qed.

Lemma goodmb_cer_bind_nest2 (Dr Dw : register -> bool) {X Y Z W : Type}
    (m : Defs.monadR X exception Y) (h : Y -> Defs.monadR X exception Z)
    (g : Z -> Defs.monadR X exception W) (f : W -> Defs.monadR X exception X)
    (s s' : mstate) (mm : pamap) (y : Y) :
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr y, s') ->
  goodmb Dr Dw
    (Defs.catch_early_return (Defs.bind (Defs.bind (Defs.bind m h) g) f)) s mm
  = goodmb Dr Dw
      (Defs.catch_early_return (Defs.bind (Defs.bind (h y) g) f)) s'
      (mm_after m s mm).
Proof.
  revert s mm. induction m as [y0 | T oc k IH]; intros s mm Hg He.
  - cbn [execR] in He.
    assert (Hx : y = y0) by congruence. assert (Hs : s' = s) by congruence.
    subst y s'. reflexivity.
  - destruct oc as [ reg ak | reg ak regval | nb rreq | nb wreq | opc
                   | bsz bpa | bar | cop | tlbo | flt | rpa | tst | ten
                   | A ao | gmsg | | | cty | | msg ];
      cbn [goodmb execR mm_after Defs.bind Interface.iMon_bind
           Defs.catch_early_return Defs.try_catch] in Hg, He |- *;
      try discriminate Hg.
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH _ s mm). }
    { apply andb_prop in Hg as [HD Hg]. rewrite HD. cbn [andb].
      by apply (IH tt _ mm). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He. rewrite Hdev.
      rewrite Hfp. cbn [negb andb] in Hg2 |- *.
      destruct (read_bytes s.(mem) (Interface.ReadReq.pa rreq) nb) as [w|];
        [|discriminate Hg2].
      cbn beta iota in He. by apply (IH _ s mm). }
    { apply andb_prop in Hg as [Hg1 Hg2]. apply andb_prop in Hg1 as [Hdev Hfp].
      apply negb_true_iff in Hdev. rewrite Hdev in He |- *. rewrite Hfp.
      cbn [negb andb]. cbn beta iota in He. by apply (IH (inl None) _ _). }
    all: first [ by apply (IH tt s mm) | by apply (IH 0%Z s mm) ].
Qed.

Lemma gm_cer_bind_nest2 (Dr Dw : register -> bool) {X Y Z W : Type}
    (m : Defs.monadR X exception Y) (h : Y -> Defs.monadR X exception Z)
    (g : Z -> Defs.monadR X exception W) (f : W -> Defs.monadR X exception X)
    (s s' : mstate) (mm : pamap) (y : Y) :
  goodmb Dr Dw m s mm = true ->
  execR m s = Some (inr y, s') ->
  goodmb Dr Dw
    (Defs.catch_early_return (Defs.bind (Defs.bind (Defs.bind m h) g) f)) s mm
  = goodmb Dr Dw
      (Defs.catch_early_return (Defs.bind (Defs.bind (h y) g) f)) s' mm.
Proof.
  intros Hg He. rewrite (goodmb_cer_bind_nest2 Dr Dw m h g f s s' mm y Hg He).
  exact (goodmb_after_dom Dr Dw m
           (Defs.catch_early_return (Defs.bind (Defs.bind (h y) g) f)) s s' mm Hg).
Qed.

Lemma gm_cer_liftR_nest2 (Dr Dw : register -> bool) {X Y Z W : Type}
    (m : M Y) (h : Y -> Defs.monadR X exception Z)
    (g : Z -> Defs.monadR X exception W) (f : W -> Defs.monadR X exception X)
    (s s' : mstate) (mm : pamap) (y : Y) :
  goodmb Dr Dw m s mm = true ->
  exec m s = Some (y, s') ->
  goodmb Dr Dw
    (Defs.catch_early_return
       (Defs.bind (Defs.bind (Defs.bind (Defs.liftR m) h) g) f)) s mm
  = goodmb Dr Dw
      (Defs.catch_early_return (Defs.bind (Defs.bind (h y) g) f)) s' mm.
Proof.
  intros Hg He.
  exact (gm_cer_bind_nest2 Dr Dw (Defs.liftR m) h g f s s' mm y
           (goodmb_liftR Dr Dw m s mm Hg) (goodmb_liftR_execR m s s' y He)).
Qed.

Ltac gmm_peelT tacg tace :=
  first
    [ erewrite gm_bind0;  [ | tacg | tace ]
    | erewrite gm_bind;   [ | tacg | tace ]
    | erewrite gm_bind0R; [ | tacg | tace ]
    | erewrite gm_bindR;  [ | tacg | tace ]
    | ( unfold Defs.bind0;
        first [ erewrite gm_bind_nest; [ | tacg | tace ]
              | erewrite gm_bind;      [ | tacg | tace ] ] ) ].

(* [HartMemAsm.gmm_lift] taking TACTICS for the head's two facts, which is
   what a head whose arguments are not determined until the goal is matched
   needs (a term with a hole elaborated in argument position cannot infer it) *)
Ltac gmm_liftT tacg tace :=
  first
    [ erewrite gm_liftR_seq0;     [ | tacg | tace ]
    | erewrite gm_liftR_seq;      [ | tacg | tace ]
    | erewrite gm_cer_liftR_seq0; [ | tacg | tace ]
    | erewrite gm_cer_liftR_seq;  [ | tacg | tace ]
    | erewrite gm_cer_liftR_nest; [ | tacg | tace ] ].

(* [HartMemAsm.gmm_lift] extended with the depth-2 shapes *)
Ltac gmm_lift2 Hg He :=
  first [ gmm_lift Hg He
        | erewrite gm_cer_liftR_nest2; [ | exact Hg | exact He ]
        | ( unfold Defs.bind0;
            first [ gmm_lift Hg He
                  | erewrite gm_cer_liftR_nest2; [ | exact Hg | exact He ] ] ) ].

(* ===================================================================== *)
(* 1. THE ACCESS-CHECK BRICKS, and the 8-byte PTE read.                   *)
(*                                                                        *)
(* Every one of these mirrors the [exec_X] of the same name in            *)
(* [RiscvExtras] / [SmodePte] / [PtTreeAdue], with the same premises plus  *)
(* the [Dr] entries for the registers it reads.  The PTE path reads        *)
(* exactly four: [pma_regions] (the PMA table), [pmpcfg_n] / [pmpaddr_n]   *)
(* (the PMP entry-0 grant) and [htif_tohost_base] (the MMIO test).         *)
(* ===================================================================== *)

(* [mag_pma_check] at an aligned access: the applicability probe is a
   [returnM] and the alignment test then decides.  The probe's certificate
   is a premise for the same reason its [exec] fact is -- the access type is
   abstract here and the probe is a [match] on it. *)
Lemma goodmb_mag_pma_check_aligned (Dr Dw : register -> bool) (pma : PMA)
    (acc : MemoryAccessType mem_payload) (paddr : physaddr) (width : Z)
    (b : bool) (s : mstate) (mm : pamap) :
  goodmb Dr Dw (is_mag_applicable_access acc width) s mm = true ->
  exec (is_mag_applicable_access acc width) s = Some (b, s) ->
  is_aligned_paddr paddr width = true ->
  goodmb Dr Dw (mag_pma_check pma acc paddr width) s mm = true.
Proof.
  intros Hg Hma Halign. unfold mag_pma_check.
  erewrite (gm_bind Dr Dw _ _ s s mm b Hg Hma).
  rewrite Halign. cbn [orb]. apply goodmb_returnm.
Qed.

(* THE PMA CHECK, as [RiscvExtras.pma_ok_peel] certifies it: the same six
   steps down [pmaCheck]'s early-return body, with the [execR] equations
   replaced by their [gm_] twins.  Stated at the two PTE arms the walk uses. *)
Lemma goodmb_pmaCheck_pte_read (Dr Dw : register -> bool) (addr : mword 64)
    (region : PMA_Region) (roc : bool) (s : mstate) (mm : pamap) :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read)
    = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) 8 (Load PageTableEntry) PBMT_PMA roc)
    s mm = true.
Proof.
  intros HD Hmatch Halign Hfield.
  destruct region as [rbase rsize rattr rdtree].
  assert (Hrg : goodmb Dr Dw (Defs.read_reg pma_regions : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HD).
  unfold pmaCheck. apply goodmb_cer.
  gmm_lift Hrg (exec_read_reg pma_regions s).
  rewrite Hmatch. cbn [PMA_Region_attributes] in Hfield |- *. cbn match.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  cbn match beta.
  erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
  rewrite Hfield. cbn [Riscv.rv64d.not negb].
  gmm_lift (goodmb_mag_pma_check_aligned Dr Dw (override_PMA rattr PBMT_PMA)
              (Load PageTableEntry) (Physaddr addr) 8 false s mm
              (goodmb_returnm Dr Dw false s mm)
              (exec_is_mag_applicable_load_pte 8 s) Halign)
           (exec_mag_pma_check_aligned (override_PMA rattr PBMT_PMA)
              (Load PageTableEntry) (Physaddr addr) 8 false s
              (exec_is_mag_applicable_load_pte 8 s) Halign).
  cbn match beta. reflexivity.
Qed.

(* the early-return TAIL, one nest in: [HartMemAsm.mcer_early_return] is a
   conversion at [cer (bind (early_return r) K)], and it is still one when the
   throw sits under a further [bind] (Sail's [foreach] loop leaves exactly
   that shape).  (FOLD BACK beside [mcer_early_return].) *)
Lemma mcer_early_return_nest {X Y Z : Type} (r : X)
    (L : Y -> Defs.monadR X exception Z) (K : Z -> Defs.monadR X exception X) :
  Defs.catch_early_return (Defs.bind (Defs.bind (Defs.early_return r) L) K)
  = (Defs.returnm r : M X).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 1b. THE PMP ENTRY-0 GRANT.                                              *)
(*                                                                        *)
(* ONE lemma for every [exec_pmpCheck_*_grant_*] in the tree: the access    *)
(* type and the privilege enter only through [pmpCheckRWX] and through the  *)
(* [or_boolM]'s unevaluated right operand, so the certificate takes the     *)
(* RWX probe's own pair and is otherwise access- and privilege-generic.     *)
(* The stretch reads exactly [pmpcfg_n] and [pmpaddr_n].                    *)
(* ---------------------------------------------------------------------- *)
Lemma goodmb_pmpMatchAddr_TOR_match (Dr Dw : register -> bool)
    (addr width : mword 64) (ent : mword 8) (pmpaddr prev : mword 64)
    (s : mstate) (mm : pamap) :
  pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = TOR ->
  zopz0zKzJ_u prev pmpaddr = false ->
  pmpRangeMatch (Z.mul (uint prev) 4) (Z.mul (uint pmpaddr) 4) (uint addr)
    (uint width) = PMP_Match ->
  goodmb Dr Dw (pmpMatchAddr (Physaddr addr) width ent pmpaddr prev) s mm = true.
Proof.
  intros HA Hord Hrange. unfold pmpMatchAddr. cbn zeta.
  rewrite HA. cbn match. rewrite Hord. rewrite Hrange. apply goodmb_returnm.
Qed.

Lemma goodmb_pmpReadAddrReg (Dr Dw : register -> bool) (n : Z)
    (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  goodmb Dr Dw (pmpReadAddrReg n) s mm = true.
Proof.
  intros Hc Ha. unfold pmpReadAddrReg. cbn zeta.
  gmm_rr pmpcfg_n Hc. cbn beta.
  gmm_rr pmpaddr_n Ha. cbn beta.
  replace (andb (Z.geb sys_pmp_grain 2)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"1")))
    with false by (vm_compute; reflexivity).
  replace (andb (Z.geb sys_pmp_grain 1)
             (eq_vec (access_vec_dec (_get_Pmpcfg_ent_A
                (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) n)) 1) ('b"0")))
    with false by (vm_compute; reflexivity).
  cbn match. apply goodmb_returnm.
Qed.

Lemma goodmb_pmpCheck_grant (Dr Dw : register -> bool) (a : mword 64)
    (width : Z) (acc : MemoryAccessType mem_payload) (priv : Privilege)
    (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  exec (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0) acc) s
    = Some (true, s) ->
  goodmb Dr Dw
    (pmpCheckRWX (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0) acc) s mm
    = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width acc priv) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HrwxE HrwxG.
  assert (Hcfg : goodmb Dr Dw (Defs.read_reg pmpcfg_n : M _) s mm = true)
    by (rewrite goodmb_read_reg; exact HDc).
  unfold pmpCheck.
  replace (Z.eqb sys_pmp_count 0) with false by (vm_compute; reflexivity). cbn zeta.
  unfold foreach_ZM_up. cbn [foreach_ZM_up'].
  replace (0 <=? sys_pmp_count - 1) with true by (vm_compute; reflexivity).
  change (0 >? 0) with false. cbn match.
  rewrite bindR_ret.
  gmm_lift2 Hcfg (exec_read_reg pmpcfg_n s). cbn beta.
  gmm_lift2 (goodmb_pmpReadAddrReg Dr Dw 0 s mm HDc HDa)
            (exec_pmpReadAddrReg_val 0 s). cbn beta.
  gmm_lift2 (goodmb_pmpMatchAddr_TOR_match Dr Dw a (to_bits 64 width)
               (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
               (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
               (zeros' 64) s mm HA Hord Hrange)
            (exec_pmpMatchAddr_TOR_match a (to_bits 64 width)
               (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)
               (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)
               (zeros' 64) s HA Hord Hrange).
  cbn match.
  match goal with |- context[Defs.or_boolM ?L ?R] =>
    set (Aor := Defs.or_boolM L R) end.
  assert (HorG : goodmb Dr Dw Aor s mm = true).
  { subst Aor. unfold Defs.or_boolM.
    erewrite gm_bindR; [ | apply goodmb_liftR; exact HrwxG
                        | apply goodmb_liftR_execR; exact HrwxE ].
    cbn match. apply goodmb_returnm. }
  assert (HorE : execR Aor s = Some (inr true, s)).
  { subst Aor. unfold Defs.or_boolM.
    rewrite (execR_bind_Some _ _ _ _ _ (goodmb_liftR_execR _ _ _ _ HrwxE)).
    cbn match. apply execR_returnR_fwd. }
  erewrite gm_cer_bind_nest2; [ | exact HorG | exact HorE ].
  cbn match beta. rewrite bindR_ret.
  rewrite mcer_early_return_nest. reflexivity.
Qed.

(* the two instances the PTE path uses ([SmodePte.exec_pmpCheck_supervisor_
   grant_load] / [PtTreeAdue.exec_pmpCheck_supervisor_grant_wpte]) *)
Lemma goodmb_pmpCheck_supervisor_grant_load (Dr Dw : register -> bool)
    (a : mword 64) (width : Z) (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (Load PageTableEntry) Supervisor) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HR.
  apply (goodmb_pmpCheck_grant Dr Dw a width (Load PageTableEntry) Supervisor
           s mm HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. rewrite HR. apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. apply goodmb_returnm.
Qed.

Lemma goodmb_pmpCheck_supervisor_grant_wpte (Dr Dw : register -> bool)
    (a : mword 64) (width : Z) (s : mstate) (mm : pamap) :
  Dr pmpcfg_n = true -> Dr pmpaddr_n = true ->
  pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR ->
  zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false ->
  pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 width)) = PMP_Match ->
  eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true ->
  goodmb Dr Dw (pmpCheck (Physaddr a) width (Store PageTableEntry) Supervisor) s mm = true.
Proof.
  intros HDc HDa HA Hord Hrange HW.
  apply (goodmb_pmpCheck_grant Dr Dw a width (Store PageTableEntry) Supervisor
           s mm HDc HDa HA Hord Hrange).
  - unfold pmpCheckRWX. cbn match. rewrite HW. apply exec_returnm.
  - unfold pmpCheckRWX. cbn match. apply goodmb_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1c. THE MMIO WINDOW TESTS.  [within_clint] / [within_sig] read nothing   *)
(* (the platform bases are compile-time constants), so their certificates   *)
(* are unconditional; [within_htif_readable] reads [htif_tohost_base].      *)
(* ---------------------------------------------------------------------- *)
Lemma goodmb_within_clint (Dr Dw : register -> bool) (a : Arch.pa) (w : Z)
    (s : mstate) (mm : pamap) :
  goodmb Dr Dw (within_clint (Physaddr a) w) s mm = true.
Proof.
  unfold within_clint, plat_have_clint, __id. cbn [Riscv.rv64d.not negb].
  apply goodmb_returnm.
Qed.

Lemma goodmb_within_sig (Dr Dw : register -> bool) (a : Arch.pa) (w : Z)
    (s : mstate) (mm : pamap) :
  goodmb Dr Dw (within_sig (Physaddr a) w) s mm = true.
Proof.
  unfold within_sig, plat_have_sig, __id. cbn [Riscv.rv64d.not negb].
  apply goodmb_returnm.
Qed.

Lemma goodmb_within_htif_readable (Dr Dw : register -> bool) (a : Arch.pa)
    (w : Z) (s : mstate) (mm : pamap) :
  Dr htif_tohost_base = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  goodmb Dr Dw (within_htif_readable (Physaddr a) w) s mm = true.
Proof.
  intros HD Hn. unfold within_htif_readable, within_htif_writable.
  gmm_rr htif_tohost_base HD. rewrite Hn. cbn match. apply goodmb_returnm.
Qed.

Lemma goodmb_within_mmio_readable (Dr Dw : register -> bool) (a : Arch.pa)
    (w : Z) (s : mstate) (mm : pamap) :
  Dr htif_tohost_base = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (within_clint (Physaddr a) w) s = Some (false, s) ->
  exec (within_sig (Physaddr a) w) s = Some (false, s) ->
  goodmb Dr Dw (within_mmio_readable (Physaddr a) w) s mm = true.
Proof.
  intros HD Hn Hc Hsig. unfold within_mmio_readable. cbn [get_config_rvfi].
  erewrite gm_or_boolM; [ | apply goodmb_within_clint | exact Hc ]. cbn match.
  erewrite gm_or_boolM; [ | apply goodmb_within_sig | exact Hsig ]. cbn match.
  erewrite gm_and_boolM;
    [ | exact (goodmb_within_htif_readable Dr Dw a w s mm HD Hn)
      | exact (within_htif_false a w s Hn) ].
  cbn match. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1d. THE ONE-ITERATION SPLIT LOOP, [RiscvFetchExec.execR_untilMT_1]'s     *)
(* twin: every access these proofs make is naturally aligned, so            *)
(* [checked_mem_read] / [checked_mem_write]'s loop runs its body once.      *)
(* ---------------------------------------------------------------------- *)
Lemma gm_untilMT_1 (Dr Dw : register -> bool) {R Vars} (vars vars' : Vars)
    (measure : Vars -> Z) (cond : Vars -> Defs.monadR R exception bool)
    (body : Vars -> Defs.monadR R exception Vars) (s s' : mstate) (mm : pamap) :
  measure vars = 1 ->
  goodmb Dr Dw (body vars) s mm = true ->
  execR (body vars) s = Some (inr vars', s') ->
  goodmb Dr Dw (cond vars') s' mm = true ->
  execR (cond vars') s' = Some (inr true, s') ->
  goodmb Dr Dw (Defs.untilMT vars measure cond body) s mm = true.
Proof.
  intros Hm Hbg Hb Hcg Hc. unfold Defs.untilMT.
  destruct (Defs.Zwf_guarded (measure vars)).
  cbn [Defs.untilMT'].
  destruct (Z_ge_dec (measure vars) 0) as [Hge|Hge];
    [| exfalso; rewrite Hm in Hge; lia ].
  erewrite (gm_bindR Dr Dw _ _ s s' mm vars' Hbg Hb).
  erewrite (gm_bindR Dr Dw _ _ s' s' mm true Hcg Hc).
  cbn match. apply goodmb_returnm.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1e. THE 8-BYTE PTE READ, [SmodePte.exec_read_pte_S]'s twin -- and the    *)
(* EXCLUSIVE read's, which differs only in the flag triple and the read     *)
(* kind, so both come out of ONE section generic in them.                   *)
(*                                                                        *)
(* The two obligations a certified RAM read owes -- the address is not a    *)
(* device and its whole 8-byte footprint is owned -- are the only NEW       *)
(* premises; everything else is the exec lemma's own list.  The [exec]      *)
(* facts of the intermediate nodes are re-proved here because [SmodePte]    *)
(* keeps them as local [assert]s; at the fold-back the twin sits beside     *)
(* its exec lemma and shares them.                                          *)
(* ---------------------------------------------------------------------- *)
Lemma goodmb_assert_exp'_true (Dr Dw : register -> bool) (msg : string)
    (s : mstate) (mm : pamap) :
  goodmb Dr Dw (Defs.assert_exp' true msg : M _) s mm = true.
Proof. unfold Defs.assert_exp'. cbn match. apply goodmb_returnm. Qed.

Lemma goodmb_split_misaligned_unsplit (Dr Dw : register -> bool)
    (addr : mword 64) (width g : Z) (s : mstate) (mm : pamap) :
  goodmb Dr Dw (split_misaligned (Physaddr addr) width g CannotSplit) s mm = true.
Proof.
  unfold split_misaligned.
  change (generic_eq CannotSplit CannotSplit) with true.
  cbn [orb]. apply goodmb_returnm.
Qed.

Lemma goodmb_check_pma_with_pmp_priority (Dr Dw : register -> bool)
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (priv : Privilege) (paddr : physaddr) (width : Z) (roc : bool)
    (plan : Phys_Mem_Access_Info) (s : mstate) (mm : pamap) :
  goodmb Dr Dw (pmaCheck paddr width acc pbmt roc) s mm = true ->
  exec (pmaCheck paddr width acc pbmt roc) s = Some (Ok plan, s) ->
  goodmb Dr Dw (check_pma_with_pmp_priority acc pbmt priv paddr width roc) s mm
    = true.
Proof.
  intros Hg He. unfold check_pma_with_pmp_priority.
  gmm_peel Hg He. cbn match. apply goodmb_returnm.
Qed.

Section PteRead.
  Context (Dr Dw : register -> bool).
  Context (addr : mword 64) (region : PMA_Region) (w : bv 64).
  Context (s : mstate) (mm : pamap).

  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint addr) (uint (to_bits 64 8)) = PMP_Match.
  Hypothesis HR : eq_vec (_get_Pmpcfg_ent_R
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr addr) 8 = Some region.
  Hypothesis Halign : is_aligned_paddr (Physaddr addr) 8 = true.
  Hypothesis Hread : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true.
  Hypothesis Hc : exec (within_clint (Physaddr addr) 8) s = Some (false, s).
  Hypothesis Hsig : exec (within_sig (Physaddr addr) 8) s = Some (false, s).
  Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hdev : dev_addr addr = false.
  Hypothesis Hown : bytes_owned mm addr 8 = true.
  Hypothesis Hbytes : forall j : nat, (N.of_nat j < 8)%N ->
    s.(mem) !! (pa_add addr j) = Some (nth_byte w j).

  (* --- the shared prefix: the PMA plan, and the MMIO answer --- *)
  Lemma pr_exec_pma (roc : bool) :
    exec (pmaCheck (Physaddr addr) 8 (Load PageTableEntry) PBMT_PMA roc) s
      = Some (Ok pma_ok_aligned, s).
  Proof.
    destruct region as [rbase rsize rattr rdtree].
    pma_ok_peel Hmatch Hread (exec_is_mag_applicable_load_pte 8 s) Halign.
  Qed.

  Lemma pr_exec_cp (roc : bool) :
    exec (check_pma_with_pmp_priority (Load PageTableEntry) PBMT_PMA Supervisor
            (Physaddr addr) 8 roc) s = Some (Ok pma_ok_aligned, s).
  Proof.
    unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ (pr_exec_pma roc)). cbn match.
    apply exec_returnM.
  Qed.

  Lemma pr_good_cp (roc : bool) :
    goodmb Dr Dw (check_pma_with_pmp_priority (Load PageTableEntry) PBMT_PMA
                    Supervisor (Physaddr addr) 8 roc) s mm = true.
  Proof.
    exact (goodmb_check_pma_with_pmp_priority Dr Dw _ _ Supervisor _ _ roc _ s mm
             (goodmb_pmaCheck_pte_read Dr Dw addr region roc s mm HDp Hmatch Halign Hread)
             (pr_exec_pma roc)).
  Qed.

  Lemma pr_exec_mmio :
    exec (within_mmio_readable (Physaddr addr) 8) s = Some (false, s).
  Proof.
    unfold within_mmio_readable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hc). cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hsig). cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_false addr 8 s Hhtif)).
    cbn match. reflexivity.
  Qed.

  (* --- the loop body, both halves --- *)
  Section Flags.
    Context (aq rl res : bool) (rk : read_kind).
    Hypothesis Hrkf : exec (read_kind_of_flags aq rl res) s = Some (rk, s).
    Hypothesis Hrkg : goodmb Dr Dw (read_kind_of_flags aq rl res) s mm = true.
    Hypothesis Hrkok : rk_ram_ok rk = true.
    Hypothesis Hram : exec (read_ram rk (Physaddr addr) 8 false) s
                      = Some ((w, default_meta), s).

    Lemma pr_exec_chk :
      exec (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor
              (Physaddr addr) 8 aq rl res false) s = Some (Ok (w, default_meta), s).
    Proof.
      unfold checked_mem_read. rewrite exec_catch_early_return.
      rewrite (execR_liftR_seq _ _ _ _ _ (pr_exec_cp _)). cbn beta. cbn match.
      rewrite execR_bind. rewrite execR_returnR. cbn match beta.
      rewrite pma_ok_aligned_splittable; rewrite pma_ok_aligned_granule.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit addr 8 0 s)).
      cbn beta. rewrite misaligned_order_1. cbn zeta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hrkf). cbn beta.
      match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
        assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s)) end.
      { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite avi0_mul8.
        rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR)).
        cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
          assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite pr_exec_mmio. reflexivity. }
        rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?pa ?wd ?mt)) ?k1) _] =>
          assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 pa wd mt)) k1) s
                        = Some (inr w, s)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ Hram). cbn beta match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
        rewrite autocast_id. rewrite usvd_zeros_full_64. apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
      rewrite autocast_id. rewrite execR_returnR. reflexivity.
    Qed.

    Lemma pr_good_chk :
      goodmb Dr Dw (checked_mem_read (Load PageTableEntry) PBMT_PMA Supervisor
               (Physaddr addr) 8 aq rl res false) s mm = true.
    Proof.
      unfold checked_mem_read. apply goodmb_cer.
      erewrite gm_liftR_seq; [ | apply pr_good_cp | apply pr_exec_cp ].
      cbn beta. cbn match.
      erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
      cbn match beta.
      rewrite pma_ok_aligned_splittable; rewrite pma_ok_aligned_granule.
      gmm_lift (goodmb_split_misaligned_unsplit Dr Dw addr 8 0 s mm)
               (exec_split_misaligned_unsplit addr 8 0 s). cbn beta.
      cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
      gmm_lift Hrkg Hrkf. cbn beta.
      match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m ?c ?b) _] =>
        assert (Hu : execR (Defs.untilMT vs m c b) s = Some (inr (w, true, 0), s));
        [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m c b) s mm = true) ] end.
      { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr addr)) with addr.
        rewrite avi0_mul8.
        rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR)).
        cbn beta. cbn match.
        match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
          assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
        { rewrite execR_bind0. rewrite execR_returnR. cbn match.
          rewrite execR_liftR. rewrite pr_exec_mmio. reflexivity. }
        rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?pa ?wd ?mt)) ?k1) _] =>
          assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 pa wd mt)) k1) s
                        = Some (inr w, s)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ Hram). cbn beta match.
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
        rewrite autocast_id. rewrite usvd_zeros_full_64. apply execR_returnR_fwd.
      }
      { eapply gm_untilMT_1; [ reflexivity | | | | ].
        - gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                    ltac:(apply exec_assert_exp'_true). cbn beta.
          change (bits_of_physaddr (Physaddr addr)) with addr.
          rewrite avi0_mul8.
          gmm_lift (goodmb_pmpCheck_supervisor_grant_load Dr Dw addr 8 s mm
                      HDc HDa HA Hord Hrange HR)
                   (exec_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR).
          cbn beta. cbn match.
          match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
            assert (Hseqg : goodmb Dr Dw (Defs.bind0 a b) s mm = true);
            [ | assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) ] end.
          { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
            apply goodmb_liftR.
            exact (goodmb_within_mmio_readable Dr Dw addr 8 s mm HDh Hhtif Hc Hsig). }
          { rewrite execR_bind0. rewrite execR_returnR. cbn match.
            rewrite execR_liftR. rewrite pr_exec_mmio. reflexivity. }
          erewrite (gm_bindR Dr Dw _ _ s s mm false Hseqg Hseq). cbn beta. cbn match.
          match goal with
            |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?pa ?wd ?mt)) ?k1) _] =>
            assert (Hrdg : goodmb Dr Dw
                      (Defs.bind (Defs.liftR (read_ram rk0 pa wd mt)) k1) s mm = true);
            [ | assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 pa wd mt)) k1) s
                              = Some (inr w, s)) ] end.
          { erewrite gm_liftR_seq;
              [ | exact (goodmb_read_ram Dr Dw rk 8 addr false s mm Hrkok Hdev Hown
                           (read_bytes_ne s.(mem) addr (Z.to_N 8) w Hbytes))
                | exact Hram ].
            cbn beta match. apply goodmb_returnm. }
          { rewrite (execR_liftR_seq _ _ _ _ _ Hram). cbn beta match.
            apply execR_returnR_fwd. }
          erewrite (gm_bindR Dr Dw _ _ s s mm w Hrdg Hrd). cbn beta zeta.
          rewrite autocast_id. rewrite usvd_zeros_full_64. apply goodmb_returnm.
        - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
          change (bits_of_physaddr (Physaddr addr)) with addr.
          rewrite avi0_mul8.
          rewrite (execR_liftR_seq _ _ _ _ _
                     (exec_pmpCheck_supervisor_grant_load addr 8 s HA Hord Hrange HR)).
          cbn beta. cbn match.
          match goal with |- context[Defs.bind (Defs.bind0 ?a ?b) _] =>
            assert (Hseq : execR (Defs.bind0 a b) s = Some (inr false, s)) end.
          { rewrite execR_bind0. rewrite execR_returnR. cbn match.
            rewrite execR_liftR. rewrite pr_exec_mmio. reflexivity. }
          rewrite (execR_bind_Some _ _ _ _ _ Hseq). cbn beta. cbn match.
          match goal with
            |- context[Defs.bind (Defs.bind (Defs.liftR (read_ram ?rk0 ?pa ?wd ?mt)) ?k1) _] =>
            assert (Hrd : execR (Defs.bind (Defs.liftR (read_ram rk0 pa wd mt)) k1) s
                          = Some (inr w, s)) end.
          { rewrite (execR_liftR_seq _ _ _ _ _ Hram). cbn beta match.
            apply execR_returnR_fwd. }
          rewrite (execR_bind_Some _ _ _ _ _ Hrd). cbn beta zeta.
          rewrite autocast_id. rewrite usvd_zeros_full_64. apply execR_returnR_fwd.
        - reflexivity.
        - apply execR_returnR_fwd. }
      erewrite (gm_bindR Dr Dw _ _ s s mm (w, true, 0) Hug Hu).
      cbn beta zeta. rewrite autocast_id. apply goodmb_returnm.
    Qed.
  End Flags.

  Lemma goodmb_read_pte_S :
    goodmb Dr Dw (read_pte (Physaddr addr) 8) s mm = true.
  Proof.
    assert (Hrkf : exec (read_kind_of_flags false false false) s
                   = Some (rv64d_types.Read_plain, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    pose proof (pr_good_chk false false false rv64d_types.Read_plain Hrkf eq_refl
                  eq_refl (exec_read_ram_plain_8 addr w s Hdev Hbytes)) as Hchkg.
    pose proof (pr_exec_chk false false false rv64d_types.Read_plain Hrkf
                  (exec_read_ram_plain_8 addr w s Hdev Hbytes)) as Hchk.
    unfold read_pte, mem_read_priv.
    assert (Hmrg : goodmb Dr Dw (mem_read_priv_meta (Load PageTableEntry) PBMT_PMA
                     Supervisor (Physaddr addr) 8 false false false false) s mm = true).
    { unfold mem_read_priv_meta. cbn [orb andb].
      gmm_peel Hchkg Hchk. cbn match. unfold mem_read_callback.
      apply goodmb_returnm. }
    assert (Hmr : exec (mem_read_priv_meta (Load PageTableEntry) PBMT_PMA Supervisor
                    (Physaddr addr) 8 false false false false) s
                  = Some (Ok (w, default_meta), s)).
    { unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
      unfold mem_read_callback. apply exec_returnM. }
    gmm_peel Hmrg Hmr. cbn [MemoryOpResult_drop_meta]. apply goodmb_returnm.
  Qed.

  Lemma goodmb_read_pte_exclusive_S :
    goodmb Dr Dw (read_pte_exclusive (Physaddr addr) 8) s mm = true.
  Proof.
    assert (Hrkf : exec (read_kind_of_flags false false true) s
                   = Some (rv64d_types.Read_RISCV_reserved, s))
      by (unfold read_kind_of_flags; apply exec_returnM).
    pose proof (pr_good_chk false false true rv64d_types.Read_RISCV_reserved Hrkf
                  eq_refl eq_refl (exec_read_ram_resv_8 addr w s Hdev Hbytes)) as Hchkg.
    pose proof (pr_exec_chk false false true rv64d_types.Read_RISCV_reserved Hrkf
                  (exec_read_ram_resv_8 addr w s Hdev Hbytes)) as Hchk.
    unfold read_pte_exclusive, mem_read_priv.
    assert (Hmrg : goodmb Dr Dw (mem_read_priv_meta (Load PageTableEntry) PBMT_PMA
                     Supervisor (Physaddr addr) 8 false false true false) s mm = true).
    { unfold mem_read_priv_meta. cbn [orb andb].
      gmm_peel Hchkg Hchk. cbn match. unfold mem_read_callback.
      apply goodmb_returnm. }
    assert (Hmr : exec (mem_read_priv_meta (Load PageTableEntry) PBMT_PMA Supervisor
                    (Physaddr addr) 8 false false true false) s
                  = Some (Ok (w, default_meta), s)).
    { unfold mem_read_priv_meta. cbn [orb andb].
      rewrite (exec_bind_Some _ _ _ _ _ Hchk). cbn match.
      unfold mem_read_callback. apply exec_returnM. }
    gmm_peel Hmrg Hmr. cbn [MemoryOpResult_drop_meta]. apply goodmb_returnm.
  Qed.

End PteRead.

(* ===================================================================== *)
(* 2. THE WALK ITSELF ([CommonWalk] section UserWalk's twins).             *)
(*                                                                        *)
(* The walk's registers are exactly [D_leafchk]'s -- [misa] (the Svnapot   *)
(* gate) and [menvcfg] (the PBMTE gate) -- plus [tlb] for the fill, plus   *)
(* whatever the PTE read needs, which arrives through the read's own       *)
(* certificate premise.  So each twin's NEW premises are the two [Dr]      *)
(* entries and one [goodmb ... (read_pte ...) ...] beside each existing    *)
(* [exec (read_pte ...)] premise: exactly the plan's 3 PTE reads          *)
(* certified by [bytes_owned mm pa 8] premises, plus one tlb write.           *)
(* ===================================================================== *)

Lemma D_leafchk_sub (Dr : register -> bool) :
  Dr misa = true -> Dr menvcfg = true ->
  forall r : register, D_leafchk r = true -> Dr r = true.
Proof.
  intros Hmi Hme r Hr. unfold D_leafchk in Hr.
  apply orb_prop in Hr as [Hr | Hr]; apply register_beq_eq in Hr; subst r;
    assumption.
Qed.

Lemma goodmb_currentlyEnabled_Svnapot (Dr Dw : register -> bool) (s : mstate)
    (mm : pamap) :
  Dr misa = true ->
  register_lookup misa s.(sregs) = MISA_C ->
  goodmb Dr Dw (currentlyEnabled Ext_Svnapot) s mm = true.
Proof.
  intros HD Hmisa.
  apply (goodmb_mono D_misa Dw Dr Dw _
           (fun r Hr => ltac:(unfold D_misa in Hr; apply register_beq_eq in Hr;
                              subst r; exact HD))
           (fun r Hr => Hr) s mm).
  exact (goodmb_of_goodb D_misa Dw _ s mm (goodb_currentlyEnabled_Svnapot s Hmisa)).
Qed.

Lemma goodmb_currentlyEnabled_Svadu (Dr Dw : register -> bool) (s : mstate)
    (mm : pamap) :
  goodmb Dr Dw (currentlyEnabled Ext_Svadu) s mm = true.
Proof.
  unfold currentlyEnabled. destruct (Defs.Zwf_guarded _).
  vm_compute. reflexivity.
Qed.

Section WalkCert.
  (* the SAME context and hypothesis list as [CommonWalk]'s [UserWalk], so
     each twin's premises are its exec lemma's premises verbatim *)
  Context (vpn : mword 27) (root : mword 44).
  Context (pte2 pte1 pte0 : mword 64).
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).

  Let addr2 : mword 64 := u_pte_addr root (subrange_vec_dec vpn 26 18).
  Let addr1 : mword 64 := u_pte_addr (u_next_base pte2) (subrange_vec_dec vpn 17 9).
  Let addr0 : mword 64 := u_pte_addr (u_next_base pte1) (subrange_vec_dec vpn 8 0).

  Hypothesis H2i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                                     (ext_bits_of_PTE pte2)) s = Some (false, s).
  Hypothesis H2nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte2 7 0)) = true.
  Hypothesis H1i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                                     (ext_bits_of_PTE pte1)) s = Some (false, s).
  Hypothesis H1nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte1 7 0)) = true.
  Hypothesis H0i : forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                                     (ext_bits_of_PTE pte0)) s = Some (false, s).
  Hypothesis H0nl : pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte0 7 0)) = false.
  Hypothesis Hchk0 : forall s, exec (check_PTE_permission acc p mxr do_sum
                                       (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                                       (ext_bits_of_PTE pte0) tt) s
                               = Some (PTE_Check_Success tt, s).
  Hypothesis H0N : eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE pte0)) ('b"1") = false.
  Hypothesis H1ig : forall (Db : register -> bool) s,
    goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte1 7 0))
                (ext_bits_of_PTE pte1)) s = true.
  Hypothesis H2ig : forall (Db : register -> bool) s,
    goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte2 7 0))
                (ext_bits_of_PTE pte2)) s = true.
  Hypothesis H0ig : forall (Db : register -> bool) s,
    goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                (ext_bits_of_PTE pte0)) s = true.
  Hypothesis Hchk0g : forall (Db : register -> bool) s,
    goodb Db (check_PTE_permission acc p mxr do_sum
                (Mk_PTE_Flags (subrange_vec_dec pte0 7 0))
                (ext_bits_of_PTE pte0) tt) s = true.

  Context (Dr Dw : register -> bool).
  Hypothesis HDmi : Dr misa = true.
  Hypothesis HDme : Dr menvcfg = true.

  Lemma goodmb_check_leaf_pte_leaf0 (pa : physaddr) (menvcfg0 : mword 64)
      (s : mstate) (mm : pamap) :
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    goodmb Dr Dw (check_leaf_pte 39 vpn acc p mxr do_sum pte0 pa 0 tt) s mm = true.
  Proof.
    intros Hmisa Hmenv HPBMTE.
    apply (goodmb_mono D_leafchk Dw Dr Dw _ (D_leafchk_sub Dr HDmi HDme)
             (fun r Hr => Hr) s mm).
    apply (goodmb_of_goodb D_leafchk Dw _ s mm).
    exact (goodb_check_leaf_pte_leaf0 vpn pte0 acc p mxr do_sum
             H0i H0nl Hchk0 H0N H0ig Hchk0g pa menvcfg0 s Hmisa Hmenv HPBMTE).
  Qed.

  (* level 0: the leaf.  ONE new premise beside the read's exec fact. *)
  Lemma goodmb_rec_walk_leaf (g : bool) (menvcfg0 : mword 64)
      (wfacc : Acc (Zwf 0) 0) (s : mstate) (mm : pamap) :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr0) 8) s mm = true ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte1) 0 g tt 0 wfacc)
      s mm = true.
  Proof.
    intros Hmisa Hrd0 Hrd0g Hmenv HPBMTE.
    destruct wfacc as [a0].
    cbn [_rec_pt_walk].
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr0 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrd0g Hrd0. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec (Defs.and_boolM A B) s = Some (false, s));
      [ | assert (Hnlg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (H0i s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      change (0 >? 0) with false. rewrite andb_false_r. apply exec_returnM. }
    { apply (goodmb_mono D_leafchk Dw Dr Dw _ (D_leafchk_sub Dr HDmi HDme)
               (fun r Hr => Hr) s mm).
      apply (goodmb_of_goodb D_leafchk Dw _ s mm).
      unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb D_leafchk (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) ] end.
      { rewrite (goodb_bind D_leafchk _ _ s false (H0ig D_leafchk s) (H0i s)).
        reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (H0i s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind D_leafchk _ E s true Hvg Hv) end.
      reflexivity. }
    gmm_peel Hnlg Hnl. cbn match beta.
    gmm_peel (goodmb_check_leaf_pte_leaf0 (Physaddr addr0) menvcfg0 s mm
                Hmisa Hmenv HPBMTE)
             (exec_check_leaf_pte_leaf0 vpn pte0 acc p mxr do_sum
                H0i H0nl Hchk0 H0N (Physaddr addr0) menvcfg0 s Hmisa Hmenv HPBMTE).
    cbn match beta zeta. apply goodmb_returnm.
  Qed.

  (* level 1: a valid non-leaf step into the leaf *)
  Lemma goodmb_rec_walk_l1 (g : bool) (menvcfg0 : mword 64)
      (wfacc : Acc (Zwf 0) 1) (s : mstate) (mm : pamap) :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr1) 8) s mm = true ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr0) 8) s mm = true ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte2) 1 g tt 1 wfacc)
      s mm = true.
  Proof.
    intros Hmisa Hrd1 Hrd1g Hrd0 Hrd0g Hmenv HPBMTE.
    destruct wfacc as [a1].
    cbn [_rec_pt_walk].
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr1 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrd1g Hrd1. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec (Defs.and_boolM A B) s = Some (true, s));
      [ | assert (Hnlg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (H1i s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      match goal with |- context[pte_is_non_leaf ?X] =>
        replace (pte_is_non_leaf X) with true by (symmetry; exact H1nl) end.
      change (1 >? 0) with true. cbn [andb]. apply exec_returnM. }
    { apply (goodmb_mono D_leafchk Dw Dr Dw _ (D_leafchk_sub Dr HDmi HDme)
               (fun r Hr => Hr) s mm).
      apply (goodmb_of_goodb D_leafchk Dw _ s mm).
      unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb D_leafchk (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) ] end.
      { rewrite (goodb_bind D_leafchk _ _ s false (H1ig D_leafchk s) (H1i s)).
        reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (H1i s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind D_leafchk _ E s true Hvg Hv) end.
      reflexivity. }
    gmm_peel Hnlg Hnl. cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (1 - 1)] =>
      change (1 - 1) with 0 end.
    match goal with
      |- context[_rec_pt_walk 39 vpn acc p mxr do_sum ?b 0 ?g0 tt 0 ?wf] =>
      pose proof (goodmb_rec_walk_leaf g0 menvcfg0 wf s mm
                    Hmisa Hrd0 Hrd0g Hmenv HPBMTE) as Hlg;
      pose proof (exec_rec_walk_leaf vpn pte1 pte0 acc p mxr do_sum
                    H0i H0nl Hchk0 H0N g0 menvcfg0 wf s
                    Hmisa Hrd0 Hmenv HPBMTE) as Hle end.
    first [ exact Hlg | gmm_peel Hlg Hle; cbn; apply goodmb_returnm ].
  Qed.

  (* level 2 = the whole walk *)
  Lemma goodmb_pt_walk_user (menvcfg0 : mword 64) (s : mstate) (mm : pamap) :
    register_lookup misa s.(sregs) = MISA_C ->
    exec (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr2) 8) s mm = true ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr1) 8) s mm = true ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr0) 8) s mm = true ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    goodmb Dr Dw (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s mm = true.
  Proof.
    intros Hmisa Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hmenv HPBMTE.
    unfold pt_walk. destruct (Defs.Zwf_guarded _) as [a2].
    cbn [_rec_pt_walk].
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with addr2 by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrd2g Hrd2. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hnl : exec (Defs.and_boolM A B) s = Some (true, s));
      [ | assert (Hnlg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (H2i s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      match goal with |- context[pte_is_non_leaf ?X] =>
        replace (pte_is_non_leaf X) with true by (symmetry; exact H2nl) end.
      change (2 >? 0) with true. cbn [andb]. apply exec_returnM. }
    { apply (goodmb_mono D_leafchk Dw Dr Dw _ (D_leafchk_sub Dr HDmi HDme)
               (fun r Hr => Hr) s mm).
      apply (goodmb_of_goodb D_leafchk Dw _ s mm).
      unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb D_leafchk (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) ] end.
      { rewrite (goodb_bind D_leafchk _ _ s false (H2ig D_leafchk s) (H2i s)).
        reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (H2i s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind D_leafchk _ E s true Hvg Hv) end.
      reflexivity. }
    gmm_peel Hnlg Hnl. cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (2 - 1)] =>
      change (2 - 1) with 1 end.
    match goal with
      |- context[_rec_pt_walk 39 vpn acc p mxr do_sum ?b 1 ?g0 tt 1 ?wf] =>
      pose proof (goodmb_rec_walk_l1 g0 menvcfg0 wf s mm
                    Hmisa Hrd1 Hrd1g Hrd0 Hrd0g Hmenv HPBMTE) as Hlg;
      pose proof (exec_rec_walk_l1 vpn pte2 pte1 pte0 acc p mxr do_sum
                    H1i H1nl H0i H0nl Hchk0 H0N g0 menvcfg0 wf s
                    Hmisa Hrd1 Hrd0 Hmenv HPBMTE) as Hle end.
    first [ exact Hlg | gmm_peel Hlg Hle; cbn; apply goodmb_returnm ].
  Qed.

  (* the TLB fill: the ONE register write the walk performs *)
  Lemma goodmb_add_to_TLB_user (asid : mword 16) (s : mstate) (mm : pamap) :
    Dr tlb = true -> Dw tlb = true ->
    goodmb Dr Dw
      (add_to_TLB 39 asid vpn
         (autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE pte0)) : mword 44))
         (autocast (T := mword) pte0) (Physaddr addr0) 0 (u_global pte2 pte1 pte0))
      s mm = true.
  Proof.
    intros HDt HWt. unfold add_to_TLB. cbn zeta.
    gmm_rr tlb HDt.
    unfold Defs.bind0. gmm_wr tlb HWt.
    gmm_rr tlb HDt.
    apply goodmb_returnm.
  Qed.

  (* the MISS: the walk, the declining A/D update, and the fill *)
  Lemma goodmb_translate_TLB_miss_user (asid : mword 16) (menvcfg0 : mword 64)
      (s : mstate) (mm : pamap) :
    Dr tlb = true -> Dw tlb = true ->
    register_lookup misa s.(sregs) = MISA_C ->
    update_PTE_Bits (autocast (T := mword) pte0 : mword 64) acc = None ->
    exec (read_pte (Physaddr addr2) 8) s = Some (Ok pte2, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr2) 8) s mm = true ->
    exec (read_pte (Physaddr addr1) 8) s = Some (Ok pte1, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr1) 8) s mm = true ->
    exec (read_pte (Physaddr addr0) 8) s = Some (Ok pte0, s) ->
    goodmb Dr Dw (read_pte (Physaddr addr0) 8) s mm = true ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    goodmb Dr Dw (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s mm = true.
  Proof.
    intros HDt HWt Hmisa Hnoupd Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hmenv HPBMTE.
    unfold translate_TLB_miss. cbn zeta.
    gmm_peel (goodmb_pt_walk_user menvcfg0 s mm Hmisa Hrd2 Hrd2g Hrd1 Hrd1g
                Hrd0 Hrd0g Hmenv HPBMTE)
             (exec_pt_walk_user vpn root pte2 pte1 pte0 acc p mxr do_sum
                H2i H2nl H1i H1nl H0i H0nl Hchk0 H0N menvcfg0 s
                Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
    cbn match.
    match goal with |- context[update_and_write_pte ?w ?vp ?a ?pv ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hupd : exec (update_and_write_pte w vp a pv lv ac pr mx ds e) s
                     = Some (Ok (None, tt), s));
      [ | assert (Hupdg : goodmb Dr Dw
                    (update_and_write_pte w vp a pv lv ac pr mx ds e) s mm = true) ] end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] => change w with 64 end.
      rewrite Hnoupd. cbn match. apply exec_returnM. }
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv ?ac] => change w with 64 end.
      rewrite Hnoupd. reflexivity. }
    gmm_peel Hupdg Hupd. cbn match.
    gmm_peel (goodmb_add_to_TLB_user asid s mm HDt HWt)
             (exec_add_to_TLB_user vpn pte2 pte1 pte0 asid s).
    apply goodmb_returnm.
  Qed.

End WalkCert.
