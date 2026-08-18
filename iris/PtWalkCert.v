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
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpDecodeBridge HartGoodb HartMemRun HartMemAsm PtBytes.
Require Import MemAccessGen WpLoad WpMmodeLeafBase SmodePte CommonWalk PtAdBits Pt4kWalk PtreeType KptPt PtTree PtTreeAdue KptTree.
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

Lemma goodmb_pmaCheck_pte_write (Dr Dw : register -> bool) (addr : mword 64)
    (region : PMA_Region) (roc : bool) (s : mstate) (mm : pamap) :
  Dr pma_regions = true ->
  matching_pma_region (register_lookup pma_regions s.(sregs)) (Physaddr addr) 8
    = Some region ->
  is_aligned_paddr (Physaddr addr) 8 = true ->
  (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_write)
    = true ->
  goodmb Dr Dw (pmaCheck (Physaddr addr) 8 (Store PageTableEntry) PBMT_PMA roc)
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
              (Store PageTableEntry) (Physaddr addr) 8 false s mm
              (goodmb_returnm Dr Dw false s mm)
              (exec_is_mag_applicable_store_pte 8 s) Halign)
           (exec_mag_pma_check_aligned (override_PMA rattr PBMT_PMA)
              (Store PageTableEntry) (Physaddr addr) 8 false s
              (exec_is_mag_applicable_store_pte 8 s) Halign).
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

(* ===================================================================== *)
(* 3. THE FAULT WALKS ([CommonWalk] section UserWalkFault's twins).        *)
(*                                                                        *)
(* Same shape as section 2, and the same two new premises per lemma: the   *)
(* [goodb] companion of each pure PTE test (which the tier's instances     *)
(* already have, being [vm_compute]s at a concrete flag byte) and the      *)
(* [goodmb] of each PTE read.  The [check_leaf_pte] arms THROW, so they    *)
(* keep the [catch_early_return] wrapper on and end at                     *)
(* [HartMemAsm.mcer_early_return]'s conversion.                            *)
(* ===================================================================== *)
Section WalkFaultCert.
  Context (vpn : mword 27).
  Context (acc : MemoryAccessType mem_payload) (p : Privilege) (mxr do_sum : bool).
  Context (Dr Dw : register -> bool).

  Lemma goodmb_check_leaf_pte_invalid (pte : mword 64) (pa : physaddr) (lvl : Z)
      (s : mstate) (mm : pamap) :
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    goodmb Dr Dw (check_leaf_pte 39 vpn acc p mxr do_sum pte pa lvl tt) s mm = true.
  Proof.
    intros Hinvg Hinv. unfold check_leaf_pte.
    erewrite gm_cer_liftR_seq;
      [ | apply (goodmb_of_goodb Dr Dw _ s mm); apply Hinvg | apply Hinv ].
    cbv iota beta. reflexivity.
  Qed.

  Lemma goodmb_check_leaf_pte_noperm0 (pte : mword 64) (pa : physaddr)
      (f : pte_check_failure) (s : mstate) (mm : pamap) :
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = false ->
    (forall (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc p mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte) tt) s0 = true) ->
    (forall s0, exec (check_PTE_permission acc p mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte) tt) s0
       = Some (PTE_Check_Failure (tt, f), s0)) ->
    goodmb Dr Dw (check_leaf_pte 39 vpn acc p mxr do_sum pte pa 0 tt) s mm = true.
  Proof.
    intros Hinvg Hinv Hnl Hchkg Hchk. unfold check_leaf_pte.
    erewrite gm_cer_liftR_seq;
      [ | apply (goodmb_of_goodb Dr Dw _ s mm); apply Hinvg | apply Hinv ].
    cbv iota beta.
    match goal with |- context[pte_is_non_leaf ?X] =>
      replace (pte_is_non_leaf X) with false by (symmetry; exact Hnl) end.
    cbv iota beta.
    change (0 >? 0) with false. cbv iota beta.
    match goal with |- context[Defs.bind0 ?A ?B] =>
      assert (HAB : execR (Defs.bind0 A B) s = Some (inr (PTE_Check_Failure (tt, f)), s));
      [ | assert (HABg : goodmb Dr Dw (Defs.bind0 A B) s mm = true) ] end.
    { rewrite execR_bind0. rewrite execR_returnR. cbn match.
      rewrite execR_liftR.
      match goal with |- context[check_PTE_permission ?a ?b ?c ?d ?e ?g ?h] =>
        replace (check_PTE_permission a b c d e g h)
          with (check_PTE_permission acc p mxr do_sum
                  (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                  (ext_bits_of_PTE pte) tt) by reflexivity end.
      rewrite (Hchk s). cbn match. reflexivity. }
    { erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
      apply goodmb_liftR. apply (goodmb_of_goodb Dr Dw _ s mm). apply Hchkg. }
    erewrite gm_cer_bind; [ | exact HABg | exact HAB ].
    cbv iota beta. cbn match. reflexivity.
  Qed.

  (* level 0: the leaf slot holds an INVALID pte *)
  Lemma goodmb_rec_walk_leaf_invalid (base : mword 44) (pte : mword 64)
      (g : bool) (wfacc : Acc (Zwf 0) 0) (s : mstate) (mm : pamap) :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok pte, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8)
      s mm = true ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum base 0 g tt 0 wfacc) s mm = true.
  Proof.
    intros Hrd Hrdg Hinvg Hinv.
    destruct wfacc as [a0].
    cbn [_rec_pt_walk]. change (0 >=? 0) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    change ((39 =? 32) || (xlen =? 64)) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrdg Hrd. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (false, s));
      [ | assert (Habg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta. apply exec_returnM. }
    { apply (goodmb_of_goodb Dr Dw _ s mm). unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb Dr (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) ] end.
      { rewrite (goodb_bind Dr _ _ s true (Hinvg Dr s) (Hinv s)). reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind Dr _ E s false Hvg Hv) end.
      reflexivity. }
    gmm_peel Habg Hab. cbn match beta.
    gmm_peel (goodmb_check_leaf_pte_invalid pte
                (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 0 s mm
                Hinvg Hinv)
             (exec_check_leaf_pte_invalid vpn acc p mxr do_sum pte
                (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 0 s Hinv).
    cbn match beta zeta. apply goodmb_returnm.
  Qed.

  (* level 0: a valid leaf that FAILS the permission check (e.g. U = 0) *)
  Lemma goodmb_rec_walk_leaf_noperm (base : mword 44) (pte : mword 64)
      (g : bool) (f : pte_check_failure) (wfacc : Acc (Zwf 0) 0)
      (s : mstate) (mm : pamap) :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok pte, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) 8)
      s mm = true ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = false ->
    (forall (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc p mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte) tt) s0 = true) ->
    (forall s0, exec (check_PTE_permission acc p mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                        (ext_bits_of_PTE pte) tt) s0
       = Some (PTE_Check_Failure (tt, f), s0)) ->
    goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum base 0 g tt 0 wfacc) s mm = true.
  Proof.
    intros Hrd Hrdg Hinvg Hinv Hnl Hchkg Hchk.
    destruct wfacc as [a0].
    cbn [_rec_pt_walk]. change (0 >=? 0) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    change ((39 =? 32) || (xlen =? 64)) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 8 0)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrdg Hrd. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (false, s));
      [ | assert (Habg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      match goal with |- context[pte_is_non_leaf ?X] =>
        replace (pte_is_non_leaf X) with false by (symmetry; exact Hnl) end.
      cbn [andb]. apply exec_returnM. }
    { apply (goodmb_of_goodb Dr Dw _ s mm). unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb Dr (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) ] end.
      { rewrite (goodb_bind Dr _ _ s false (Hinvg Dr s) (Hinv s)). reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind Dr _ E s true Hvg Hv) end.
      reflexivity. }
    gmm_peel Habg Hab. cbn match beta.
    gmm_peel (goodmb_check_leaf_pte_noperm0 pte
                (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) f s mm
                Hinvg Hinv Hnl Hchkg Hchk)
             (exec_check_leaf_pte_noperm0 vpn acc p mxr do_sum pte
                (Physaddr (u_pte_addr base (subrange_vec_dec vpn 8 0))) f s
                Hinv Hnl Hchk).
    cbn match beta zeta. apply goodmb_returnm.
  Qed.

  (* level 1: the mid slot holds an INVALID pte *)
  Lemma goodmb_rec_walk_l1_invalid (base : mword 44) (pte : mword 64)
      (g : bool) (wfacc : Acc (Zwf 0) 1) (s : mstate) (mm : pamap) :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok pte, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8)
      s mm = true ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum base 1 g tt 1 wfacc) s mm = true.
  Proof.
    intros Hrd Hrdg Hinvg Hinv.
    destruct wfacc as [a1].
    cbn [_rec_pt_walk]. change (1 >=? 0) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    change ((39 =? 32) || (xlen =? 64)) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrdg Hrd. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (false, s));
      [ | assert (Habg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta. apply exec_returnM. }
    { apply (goodmb_of_goodb Dr Dw _ s mm). unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb Dr (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) ] end.
      { rewrite (goodb_bind Dr _ _ s true (Hinvg Dr s) (Hinv s)). reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind Dr _ E s false Hvg Hv) end.
      reflexivity. }
    gmm_peel Habg Hab. cbn match beta.
    gmm_peel (goodmb_check_leaf_pte_invalid pte
                (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 1 s mm
                Hinvg Hinv)
             (exec_check_leaf_pte_invalid vpn acc p mxr do_sum pte
                (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 1 s Hinv).
    cbn match beta zeta. apply goodmb_returnm.
  Qed.

  (* level 1: a valid non-leaf step whose LEVEL-0 sub-walk is certified *)
  Lemma goodmb_rec_walk_l1_sub (base : mword 44) (pte : mword 64) (g : bool)
      (wfacc : Acc (Zwf 0) 1) (s : mstate) (mm : pamap) :
    exec (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok pte, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr base (subrange_vec_dec vpn 17 9))) 8)
      s mm = true ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = true ->
    (forall (g' : bool) (a : Acc (Zwf 0) 0),
       goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte) 0 g' tt 0 a)
         s mm = true) ->
    goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum base 1 g tt 1 wfacc) s mm = true.
  Proof.
    intros Hrd Hrdg Hinvg Hinv Hnl Hsubg.
    destruct wfacc as [a1].
    cbn [_rec_pt_walk]. change (1 >=? 0) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    change ((39 =? 32) || (xlen =? 64)) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr base (subrange_vec_dec vpn 17 9)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrdg Hrd. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (true, s));
      [ | assert (Habg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      match goal with |- context[pte_is_non_leaf ?X] =>
        replace (pte_is_non_leaf X) with true by (symmetry; exact Hnl) end.
      change (1 >? 0) with true. cbn [andb]. apply exec_returnM. }
    { apply (goodmb_of_goodb Dr Dw _ s mm). unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb Dr (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) ] end.
      { rewrite (goodb_bind Dr _ _ s false (Hinvg Dr s) (Hinv s)). reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind Dr _ E s true Hvg Hv) end.
      reflexivity. }
    gmm_peel Habg Hab. cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (1 - 1)] =>
      change (1 - 1) with 0 end.
    apply Hsubg.
  Qed.

  (* level 2 (= the full [pt_walk]): the root slot holds an INVALID pte *)
  Lemma goodmb_pt_walk_user_l2_invalid (root : mword 44) (pte : mword 64)
      (s : mstate) (mm : pamap) :
    exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok pte, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
      s mm = true ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (true, s0)) ->
    goodmb Dr Dw (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s mm = true.
  Proof.
    intros Hrd Hrdg Hinvg Hinv.
    unfold pt_walk. destruct (Defs.Zwf_guarded _) as [a2].
    cbn [_rec_pt_walk]. change (2 >=? 0) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    change ((39 =? 32) || (xlen =? 64)) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrdg Hrd. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (false, s));
      [ | assert (Habg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta. apply exec_returnM. }
    { apply (goodmb_of_goodb Dr Dw _ s mm). unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb Dr (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (false, s)) ] end.
      { rewrite (goodb_bind Dr _ _ s true (Hinvg Dr s) (Hinv s)). reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind Dr _ E s false Hvg Hv) end.
      reflexivity. }
    gmm_peel Habg Hab. cbn match beta.
    gmm_peel (goodmb_check_leaf_pte_invalid pte
                (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 2 s mm
                Hinvg Hinv)
             (exec_check_leaf_pte_invalid vpn acc p mxr do_sum pte
                (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 2 s Hinv).
    cbn match beta zeta. apply goodmb_returnm.
  Qed.

  (* level 2: a valid non-leaf step whose LEVEL-1 sub-walk is certified *)
  Lemma goodmb_pt_walk_user_sub (root : mword 44) (pte : mword 64)
      (s : mstate) (mm : pamap) :
    exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok pte, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
      s mm = true ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                   (ext_bits_of_PTE pte)) s0 = true) ->
    (forall s0, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec pte 7 0))
                       (ext_bits_of_PTE pte)) s0 = Some (false, s0)) ->
    pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec pte 7 0)) = true ->
    (forall (g' : bool) (a : Acc (Zwf 0) 1),
       goodmb Dr Dw (_rec_pt_walk 39 vpn acc p mxr do_sum (u_next_base pte) 1 g' tt 1 a)
         s mm = true) ->
    goodmb Dr Dw (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s mm = true.
  Proof.
    intros Hrd Hrdg Hinvg Hinv Hnl Hsubg.
    unfold pt_walk. destruct (Defs.Zwf_guarded _) as [a2].
    cbn [_rec_pt_walk]. change (2 >=? 0) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    change ((39 =? 32) || (xlen =? 64)) with true.
    gmm_peelT ltac:(apply goodmb_assert_exp'_true)
              ltac:(apply exec_assert_exp'_true). cbn beta zeta.
    match goal with |- context[read_pte (Physaddr ?a) ?wd] =>
      replace a with (u_pte_addr root (subrange_vec_dec vpn 26 18)) by reflexivity;
      replace wd with 8 by (vm_compute; reflexivity) end.
    gmm_peel Hrdg Hrd. cbn match beta zeta.
    match goal with |- context[Defs.and_boolM ?A ?B] =>
      assert (Hab : exec (Defs.and_boolM A B) s = Some (true, s));
      [ | assert (Habg : goodmb Dr Dw (Defs.and_boolM A B) s mm = true) ] end.
    { unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      rewrite (exec_bind_Some _ _ _ _ _ Hv). cbn match beta.
      match goal with |- context[pte_is_non_leaf ?X] =>
        replace (pte_is_non_leaf X) with true by (symmetry; exact Hnl) end.
      change (2 >? 0) with true. cbn [andb]. apply exec_returnM. }
    { apply (goodmb_of_goodb Dr Dw _ s mm). unfold Defs.and_boolM.
      match goal with |- context[Defs.bind (Defs.bind (pte_is_invalid ?a ?b) ?k1) _] =>
        assert (Hvg : goodb Dr (Defs.bind (pte_is_invalid a b) k1) s = true);
        [ | assert (Hv : exec (Defs.bind (pte_is_invalid a b) k1) s = Some (true, s)) ] end.
      { rewrite (goodb_bind Dr _ _ s false (Hinvg Dr s) (Hinv s)). reflexivity. }
      { rewrite (exec_bind_Some _ _ _ _ _ (Hinv s)). cbn match beta.
        apply exec_returnM. }
      match goal with |- goodb _ (Defs.bind _ ?E) _ = true =>
        rewrite (goodb_bind Dr _ E s true Hvg Hv) end.
      reflexivity. }
    gmm_peel Habg Hab. cbn match beta.
    match goal with |- context[_rec_pt_walk ?a ?b ?c ?d ?e ?f ?g0 (2 - 1)] =>
      change (2 - 1) with 1 end.
    apply Hsubg.
  Qed.

  (* a faulting walk propagates through [translate_TLB_miss] unchanged --
     no TLB write on the fault path, so no register is written at all *)
  Lemma goodmb_translate_TLB_miss_user_walk_err (asid : mword 16) (root : mword 44)
      (f : PTW_Error) (s : mstate) (mm : pamap) :
    exec (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s = Some (Err (f, tt), s) ->
    goodmb Dr Dw (pt_walk 39 vpn acc p mxr do_sum root 2 false tt) s mm = true ->
    goodmb Dr Dw (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s mm = true.
  Proof.
    intros Hwalk Hwalkg. unfold translate_TLB_miss. cbn zeta.
    gmm_peel Hwalkg Hwalk. cbn match. apply goodmb_returnm.
  Qed.

  (* the TLB lookup itself: one read of [tlb], whatever it answers *)
  Lemma goodmb_lookup_TLB (asid : mword 16) (s : mstate) (mm : pamap) :
    Dr tlb = true -> goodmb Dr Dw (lookup_TLB 39 asid vpn) s mm = true.
  Proof.
    intros HD. unfold lookup_TLB. gmm_rr tlb HD. apply goodmb_returnm.
  Qed.

  (* ...and through [translate], given a TLB miss (empty or colliding slot) *)
  Lemma goodmb_translate_walk_user_err (asid : mword 16) (root : mword 44)
      (s : mstate) (mm : pamap) :
    Dr tlb = true ->
    exec (lookup_TLB 39 asid vpn) s = Some (None, s) ->
    goodmb Dr Dw (translate_TLB_miss 39 asid root vpn acc p mxr do_sum tt) s mm = true ->
    goodmb Dr Dw (translate 39 asid root vpn acc p mxr do_sum tt) s mm = true.
  Proof.
    intros HD Hlk Hmiss. unfold translate.
    gmm_peel (goodmb_lookup_TLB asid s mm HD) Hlk. cbn match. exact Hmiss.
  Qed.

End WalkFaultCert.

(* ===================================================================== *)
(* 4. THE PTE WRITE ([PtTreeAdue] section 1's twins).                      *)
(*                                                                        *)
(* The plain and the CONDITIONAL write differ only in the flag triple and  *)
(* the write kind (the interpreter routes by address and ignores the       *)
(* access kind), so both come out of one section generic in them -- the    *)
(* same factoring section 1e used for the two reads.  This is the ONE      *)
(* node of the whole walk that moves the byte map; [HartMemAsm.gm_MemWrite]*)
(* reads the continuation's certificate back at the ORIGINAL map, so       *)
(* nothing about [mm_after] appears here either.                           *)
(* ===================================================================== *)
Lemma goodmb_within_htif_writable (Dr Dw : register -> bool) (a : Arch.pa)
    (w : Z) (s : mstate) (mm : pamap) :
  Dr htif_tohost_base = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  goodmb Dr Dw (within_htif_writable (Physaddr a) w) s mm = true.
Proof.
  intros HD Hn. unfold within_htif_writable.
  gmm_rr htif_tohost_base HD. rewrite Hn. cbn match. apply goodmb_returnm.
Qed.

Lemma goodmb_within_mmio_writable (Dr Dw : register -> bool) (a : Arch.pa)
    (w : Z) (s : mstate) (mm : pamap) :
  Dr htif_tohost_base = true ->
  register_lookup htif_tohost_base s.(sregs) = None ->
  exec (within_clint (Physaddr a) w) s = Some (false, s) ->
  exec (within_sig (Physaddr a) w) s = Some (false, s) ->
  goodmb Dr Dw (within_mmio_writable (Physaddr a) w) s mm = true.
Proof.
  intros HD Hn Hc Hsig. unfold within_mmio_writable. cbn [get_config_rvfi].
  erewrite gm_or_boolM; [ | apply goodmb_within_clint | exact Hc ]. cbn match.
  erewrite gm_or_boolM; [ | apply goodmb_within_sig | exact Hsig ]. cbn match.
  erewrite gm_and_boolM;
    [ | exact (goodmb_within_htif_writable Dr Dw a w s mm HD Hn)
      | exact (within_htif_writable_false a w s Hn) ].
  cbn match. reflexivity.
Qed.

Section PteWrite.
  Context (Dr Dw : register -> bool).
  Context (a : mword 64) (w' : mword 64) (region : PMA_Region).
  Context (s : mstate) (mm : pamap).

  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.
  Hypothesis Hram : addr_is_ram a.
  Hypothesis Hram7 : addr_is_ram (pa_add a 7).
  Hypothesis Halign : is_aligned_paddr (Physaddr a) 8 = true.
  Hypothesis HA : pmpAddrMatchType_encdec_backwards
    (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) = TOR.
  Hypothesis Hord : zopz0zKzJ_u (zeros' 64)
    (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) = false.
  Hypothesis HW : eq_vec (_get_Pmpcfg_ent_W
    (vec_access_dec (register_lookup pmpcfg_n s.(sregs)) 0)) ('b"1") = true.
  Hypothesis Hcov : (ram_base + ram_size
    <= uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0) * 4)%Z.
  Hypothesis Hmatch : matching_pma_region (register_lookup pma_regions s.(sregs))
    (Physaddr a) 8 = Some region.
  Hypothesis Hwr : (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_write) = true.
  Hypothesis Hhtif : register_lookup htif_tohost_base s.(sregs) = None.
  Hypothesis Hown : bytes_owned mm a 8 = true.

  Let sw : mstate := MState s.(sregs) (write_bytes s.(mem) a 8 w') s.(mdev).

  Lemma pw_fit : (uint a + 8 <= ram_base + ram_size)%Z.
  Proof.
    assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
    { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
      change (Z.of_nat 7) with 7. lia. }
    pose proof (uint_pa_add a 7 Hnw) as Heq.
    destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7.
    change (Z.of_nat 7) with 7 in Hhi7.
    unfold ram_base, ram_size in *. lia.
  Qed.

  Lemma pw_range : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
    (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n s.(sregs)) 0)) 4)
    (uint a) (uint (to_bits 64 8)) = PMP_Match.
  Proof.
    apply (ram_pmp_match_w a _ 8);
      [ lia | vm_compute; reflexivity | | exact pw_fit | exact Hcov ].
    destruct Hram as [Hlo _]. exact Hlo.
  Qed.

  Lemma pw_exec_mmio : exec (within_mmio_writable (Physaddr a) 8) s = Some (false, s).
  Proof.
    unfold within_mmio_writable. cbn [get_config_rvfi].
    rewrite (exec_or_boolM_Some _ _ _ _ _
               (within_clint_false a 8 s (addr_is_ram_not_in_clint _ Hram) ltac:(lia))).
    cbn match.
    rewrite (exec_or_boolM_Some _ _ _ _ _
               (within_sig_false a 8 s (addr_is_ram_not_in_sig _ Hram) ltac:(lia))).
    cbn match.
    rewrite (exec_and_boolM_Some _ _ _ _ _ (within_htif_writable_false a 8 s Hhtif)).
    cbn match. reflexivity.
  Qed.

  Lemma pw_exec_pma (roc : bool) :
    exec (pmaCheck (Physaddr a) 8 (Store PageTableEntry) PBMT_PMA roc) s
      = Some (Ok pma_ok_aligned, s).
  Proof.
    destruct region as [rbase rsize rattr rdtree].
    pma_ok_peel Hmatch Hwr (exec_is_mag_applicable_store_pte 8 s) Halign.
  Qed.

  Lemma pw_exec_cp (roc : bool) :
    exec (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA Supervisor
            (Physaddr a) 8 roc) s = Some (Ok pma_ok_aligned, s).
  Proof.
    unfold check_pma_with_pmp_priority.
    rewrite (exec_bind_Some _ _ _ _ _ (pw_exec_pma roc)). cbn match.
    apply exec_returnM.
  Qed.

  Lemma pw_good_cp (roc : bool) :
    goodmb Dr Dw (check_pma_with_pmp_priority (Store PageTableEntry) PBMT_PMA
                    Supervisor (Physaddr a) 8 roc) s mm = true.
  Proof.
    exact (goodmb_check_pma_with_pmp_priority Dr Dw _ _ Supervisor _ _ roc _ s mm
             (goodmb_pmaCheck_pte_write Dr Dw a region roc s mm HDp Hmatch Halign Hwr)
             (pw_exec_pma roc)).
  Qed.

  Section WFlags.
    Context (aq rl con : bool) (wk : write_kind).
    Hypothesis Hwkf : exec (write_kind_of_flags aq rl con) s = Some (wk, s).
    Hypothesis Hwkg : goodmb Dr Dw (write_kind_of_flags aq rl con) s mm = true.
    Hypothesis Hwkok : wk_ram_ok wk = true.
    Hypothesis Hwram : exec (write_ram wk (Physaddr a) 8 (w' : mword (8 * 8)) tt) s
                       = Some (true, sw).

    Lemma pw_exec_chk :
      exec (checked_mem_write (Physaddr a) 8 (w' : mword 64) (Store PageTableEntry)
              PBMT_PMA Supervisor tt aq rl con) s = Some (Ok true, sw).
    Proof.
      unfold checked_mem_write. rewrite exec_catch_early_return.
      rewrite (execR_liftR_seq _ _ _ _ _ (pw_exec_cp _)). cbn beta. cbn match.
      rewrite execR_bind. rewrite execR_returnR. cbn match beta.
      rewrite pma_ok_aligned_splittable; rewrite pma_ok_aligned_granule.
      rewrite (execR_liftR_seq _ _ _ _ _ (exec_split_misaligned_unsplit a 8 0 s)).
      cbn beta. cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
      rewrite (execR_liftR_seq _ _ _ _ _ Hwkf). cbn beta.
      match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?b) _] =>
        assert (Hu : execR (Defs.untilMT vs m0 c b) s = Some (inr (true, 0, true), sw)) end.
      { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr a)) with a.
        rewrite avi0_mul8.
        rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant_wpte a 8 s HA Hord pw_range HW)).
        cbn beta. cbn match.
        rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
        rewrite (execR_liftR_seq _ _ _ _ _ pw_exec_mmio). cbn beta. cbn match.
        rewrite autocast_id.
        change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
        rewrite subrange_full_64.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?pa ?wd ?dt ?mt)) ?k1) _] =>
          assert (Hwr2 : execR (Defs.bind (Defs.liftR (write_ram wk0 pa wd dt mt)) k1) s
                         = Some (inr true, sw)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ Hwram). cbn beta. cbn [andb].
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwr2). cbn beta zeta.
        apply execR_returnR_fwd. }
      rewrite (execR_bind_Some _ _ _ _ _ Hu). cbn beta zeta.
      rewrite execR_returnR. reflexivity.
    Qed.

    Lemma pw_good_chk :
      goodmb Dr Dw (checked_mem_write (Physaddr a) 8 (w' : mword 64)
               (Store PageTableEntry) PBMT_PMA Supervisor tt aq rl con) s mm = true.
    Proof.
      unfold checked_mem_write. apply goodmb_cer.
      erewrite gm_liftR_seq; [ | apply pw_good_cp | apply pw_exec_cp ].
      cbn beta. cbn match.
      erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
      cbn match beta.
      rewrite pma_ok_aligned_splittable; rewrite pma_ok_aligned_granule.
      gmm_lift (goodmb_split_misaligned_unsplit Dr Dw a 8 0 s mm)
               (exec_split_misaligned_unsplit a 8 0 s). cbn beta.
      cbn match beta. rewrite misaligned_order_1. cbn match zeta beta.
      gmm_lift Hwkg Hwkf. cbn beta.
      match goal with |- context[Defs.bind (Defs.untilMT ?vs ?m0 ?c ?b) _] =>
        assert (Hu : execR (Defs.untilMT vs m0 c b) s = Some (inr (true, 0, true), sw));
        [ | assert (Hug : goodmb Dr Dw (Defs.untilMT vs m0 c b) s mm = true) ] end.
      { eapply execR_untilMT_1; [ reflexivity | | apply execR_returnR_fwd ].
        rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
        change (bits_of_physaddr (Physaddr a)) with a.
        rewrite avi0_mul8.
        rewrite (execR_liftR_seq _ _ _ _ _
                   (exec_pmpCheck_supervisor_grant_wpte a 8 s HA Hord pw_range HW)).
        cbn beta. cbn match.
        rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
        rewrite (execR_liftR_seq _ _ _ _ _ pw_exec_mmio). cbn beta. cbn match.
        rewrite autocast_id.
        change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
        rewrite subrange_full_64.
        match goal with
          |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?pa ?wd ?dt ?mt)) ?k1) _] =>
          assert (Hwr2 : execR (Defs.bind (Defs.liftR (write_ram wk0 pa wd dt mt)) k1) s
                         = Some (inr true, sw)) end.
        { rewrite (execR_liftR_seq _ _ _ _ _ Hwram). cbn beta. cbn [andb].
          apply execR_returnR_fwd. }
        rewrite (execR_bind_Some _ _ _ _ _ Hwr2). cbn beta zeta.
        apply execR_returnR_fwd. }
      { eapply gm_untilMT_1; [ reflexivity | | | | ].
        - gmm_liftT ltac:(apply goodmb_assert_exp'_true)
                    ltac:(apply exec_assert_exp'_true). cbn beta.
          change (bits_of_physaddr (Physaddr a)) with a.
          rewrite avi0_mul8.
          gmm_lift (goodmb_pmpCheck_supervisor_grant_wpte Dr Dw a 8 s mm
                      HDc HDa HA Hord pw_range HW)
                   (exec_pmpCheck_supervisor_grant_wpte a 8 s HA Hord pw_range HW).
          cbn beta. cbn match.
          erewrite gm_bind0R; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
          cbn match zeta.
          gmm_lift (goodmb_within_mmio_writable Dr Dw a 8 s mm HDh Hhtif
                      (within_clint_false a 8 s (addr_is_ram_not_in_clint _ Hram)
                         ltac:(lia))
                      (within_sig_false a 8 s (addr_is_ram_not_in_sig _ Hram)
                         ltac:(lia)))
                   pw_exec_mmio.
          cbn beta. cbn match.
          rewrite autocast_id.
          change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
          rewrite subrange_full_64.
          match goal with
            |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?pa ?wd ?dt ?mt)) ?k1) _] =>
            assert (Hwr2g : goodmb Dr Dw
                      (Defs.bind (Defs.liftR (write_ram wk0 pa wd dt mt)) k1) s mm = true);
            [ | assert (Hwr2 : execR (Defs.bind (Defs.liftR (write_ram wk0 pa wd dt mt)) k1) s
                               = Some (inr true, sw)) ] end.
          { erewrite gm_liftR_seq;
              [ | exact (goodmb_write_ram Dr Dw wk 8 a (w' : mword (8 * 8)) s mm
                           Hwkok (addr_is_ram_not_dev _ Hram) Hown)
                | exact Hwram ].
            cbn beta. cbn [andb]. apply goodmb_returnm. }
          { rewrite (execR_liftR_seq _ _ _ _ _ Hwram). cbn beta. cbn [andb].
            apply execR_returnR_fwd. }
          erewrite (gm_bindR Dr Dw _ _ s sw mm true Hwr2g Hwr2). cbn beta zeta.
          apply goodmb_returnm.
        - rewrite (execR_liftR_seq _ _ _ _ _ (exec_assert_exp'_true _ s)). cbn beta.
          change (bits_of_physaddr (Physaddr a)) with a.
          rewrite avi0_mul8.
          rewrite (execR_liftR_seq _ _ _ _ _
                     (exec_pmpCheck_supervisor_grant_wpte a 8 s HA Hord pw_range HW)).
          cbn beta. cbn match.
          rewrite execR_bind0. rewrite execR_returnR. cbn match zeta.
          rewrite (execR_liftR_seq _ _ _ _ _ pw_exec_mmio). cbn beta. cbn match.
          rewrite autocast_id.
          change (8 * (0 + 1) * 8 - 1) with 63. change (8 * 0 * 8) with 0.
          rewrite subrange_full_64.
          match goal with
            |- context[Defs.bind (Defs.bind (Defs.liftR (write_ram ?wk0 ?pa ?wd ?dt ?mt)) ?k1) _] =>
            assert (Hwr2 : execR (Defs.bind (Defs.liftR (write_ram wk0 pa wd dt mt)) k1) s
                           = Some (inr true, sw)) end.
          { rewrite (execR_liftR_seq _ _ _ _ _ Hwram). cbn beta. cbn [andb].
            apply execR_returnR_fwd. }
          rewrite (execR_bind_Some _ _ _ _ _ Hwr2). cbn beta zeta.
          apply execR_returnR_fwd.
        - reflexivity.
        - apply execR_returnR_fwd. }
      erewrite (gm_bindR Dr Dw _ _ s sw mm (true, 0, true) Hug Hu).
      cbn beta zeta. apply goodmb_returnm.
    Qed.
  End WFlags.

  Lemma goodmb_write_pte_ram :
    goodmb Dr Dw (write_pte (Physaddr a) 8 (w' : mword 64)) s mm = true.
  Proof.
    assert (Hwkf : exec (write_kind_of_flags false false false) s
                   = Some (rv64d_types.Write_plain, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    pose proof (pw_good_chk false false false rv64d_types.Write_plain Hwkf eq_refl
                  eq_refl (exec_write_ram_plain_8 a w' s
                             (addr_is_ram_not_dev _ Hram))) as Hchkg.
    pose proof (pw_exec_chk false false false rv64d_types.Write_plain Hwkf
                  (exec_write_ram_plain_8 a w' s
                     (addr_is_ram_not_dev _ Hram))) as Hchk.
    unfold write_pte, mem_write_value_priv, mem_write_value_priv_meta.
    cbn [orb andb].
    gmm_peel Hchkg Hchk. cbn match. unfold mem_write_callback.
    apply goodmb_returnm.
  Qed.

  Lemma goodmb_write_pte_conditional_ram :
    goodmb Dr Dw (write_pte_conditional (Physaddr a) 8 (w' : mword 64)) s mm = true.
  Proof.
    assert (Hwkf : exec (write_kind_of_flags false false true) s
                   = Some (rv64d_types.Write_RISCV_conditional, s))
      by (unfold write_kind_of_flags; cbn match; apply exec_returnM).
    pose proof (pw_good_chk false false true rv64d_types.Write_RISCV_conditional
                  Hwkf eq_refl eq_refl
                  (exec_write_ram_cond_8 a w' s (addr_is_ram_not_dev _ Hram))) as Hchkg.
    pose proof (pw_exec_chk false false true rv64d_types.Write_RISCV_conditional
                  Hwkf (exec_write_ram_cond_8 a w' s
                          (addr_is_ram_not_dev _ Hram))) as Hchk.
    unfold write_pte_conditional, mem_write_value_priv, mem_write_value_priv_meta.
    cbn [orb andb Riscv.rv64d.not negb].
    gmm_peel Hchkg Hchk. cbn match. unfold mem_write_callback.
    apply goodmb_returnm.
  Qed.

End PteWrite.

(* ===================================================================== *)
(* 5. THE Svadu A/D WRITE-BACK, and the three [translate] outcomes.        *)
(*                                                                        *)
(* [PtTreeAdue] sections 2-4's twins.  Each takes its exec lemma's premise *)
(* list with a certificate BESIDE each monadic premise -- the exclusive    *)
(* re-read, the leaf re-check, the conditional write -- so no page-table   *)
(* or PMP reasoning is restated here: section 1 and section 2 supply those *)
(* certificates at the call site.                                          *)
(* ===================================================================== *)
Section PtAdue.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pv : Privilege) (mxr do_sum : bool).
  Hypothesis HDt : Dr tlb = true.
  Hypothesis HWt : Dw tlb = true.
  Hypothesis HDme : Dr menvcfg = true.

  (* the generic TLB fill / refresh: read tlb, write tlb, read tlb *)
  Lemma goodmb_add_to_TLB_pt (asid : mword 16) (vpn : mword 27) (pp : mword 44)
      (pte : mword 64) (ptea : physaddr) (g : bool) (s : mstate) (mm : pamap) :
    goodmb Dr Dw (add_to_TLB 39 asid vpn pp pte ptea 0 g) s mm = true.
  Proof.
    unfold add_to_TLB. cbn zeta.
    gmm_rr tlb HDt.
    unfold Defs.bind0. gmm_wr tlb HWt.
    gmm_rr tlb HDt.
    apply goodmb_returnm.
  Qed.

  Lemma goodmb_write_TLB (idx : Z) (en : TLB_Entry) (s : mstate) (mm : pamap) :
    goodmb Dr Dw (write_TLB idx en) s mm = true.
  Proof.
    unfold write_TLB. gmm_rr tlb HDt. try unfold Defs.bind0.
    first [ gmm_wr tlb HWt; apply goodmb_returnm
          | etransitivity; [ apply goodmb_write_reg | exact HWt ] ].
  Qed.

  Lemma goodmb_uwe_pbmt (vpn : mword 27) (q2 q1 q0 : mword 64) (asid : mword 16)
      (s : mstate) (mm : pamap) :
    pte_pbmt0 q0 ->
    goodmb Dr Dw (tlb_get_pbmt (u_walk_entry vpn q2 q1 q0 asid)) s mm = true.
  Proof.
    intros Hpb. unfold tlb_get_pbmt, u_walk_entry. cbn [TLB_Entry_pte]. cbn zeta.
    rewrite zero_extend64_id. rewrite autocast_id.
    unfold pte_pbmt0 in Hpb. rewrite Hpb.
    vm_compute (page_based_mem_type_forwards _). apply goodmb_returnm.
  Qed.

  (* the shared A/D gate certificate, taken off the goal so the exec
     lemma's own spelling of [or_boolM] is the one that is certified *)
  Ltac gm_adue_gate Hmenv HADUE :=
    match goal with |- context[Defs.bind (Defs.or_boolM ?A ?B) _] =>
      assert (Hgt : exec (Defs.or_boolM A B) _ = Some (true, _));
      [ | assert (Hgtg : goodmb Dr Dw (Defs.or_boolM A B) _ _ = true) ] end.

  (* HIT + write-back: the cached word wants A/D, and so does the word in
     memory, so the re-read word is written back and the entry refreshed *)
  Lemma goodmb_translate_TLB_hit_pt_upd (vpn : mword 27)
      (q2 q1 q0 q0g m0 m0' : mword 64) (menvcfg0 : mword 64) (asid : mword 16)
      (idx : Z) (sw : mstate) (s : mstate) (mm : pamap) :
    pte_check_ok acc pv mxr do_sum q0 ->
    (forall (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec q0 7 0))
                   (ext_bits_of_PTE q0) tt) s0 = true) ->
    update_PTE_Bits (q0 : mword 64) acc = Some q0g ->
    pte_pbmt0 q0 ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok m0, s) ->
    goodmb Dr Dw
      (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8)
      s mm = true ->
    pte_valid m0 -> pte_leaf m0 -> pte_no_napot m0 ->
    pte_check_ok acc pv mxr do_sum m0 ->
    goodmb Dr Dw
      (check_leaf_pte 39 vpn acc pv mxr do_sum m0
         (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 0 tt) s mm
      = true ->
    register_lookup misa s.(sregs) = MISA_C ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (exists a2 d2 : mword 1, m0 = pte_set_ad q0 a2 d2) ->
    update_PTE_Bits (m0 : mword 64) acc = Some m0' ->
    exec (write_pte_conditional (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8
            (m0' : mword 64)) s = Some (Ok true, sw) ->
    goodmb Dr Dw
      (write_pte_conditional (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8
         (m0' : mword 64)) s mm = true ->
    sw.(sregs) = s.(sregs) ->
    goodmb Dr Dw (translate_TLB_hit 39 asid vpn acc pv mxr do_sum tt idx
                    (u_walk_entry vpn q2 q1 q0 asid)) s mm = true.
  Proof.
    intros Hchk Hchkg Hgate Hpb Hmenv HADUE Hrdx Hrdxg Hv0 Hl0 Hnap Hchkm Hlfg
           Hmisa HPBMTE Hvar Hupd Hwrite Hwriteg Hswregs.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte. rewrite autocast_id.
    gmm_peel (goodmb_of_goodb Dr Dw _ s mm (Hchkg Dr s)) (Hchk s). cbn match.
    match goal with |- context[update_and_write_pte ?w ?vp0 ?aa ?pv0 ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec (update_and_write_pte w vp0 aa pv0 lv ac pr mx ds e) s
                   = Some (Ok (Some m0', tt), sw));
      [ | assert (Hug : goodmb Dr Dw
                    (update_and_write_pte w vp0 aa pv0 lv ac pr mx ds e) s mm = true) ] end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hgate' : @update_PTE_Bits w pv0 ac = Some q0g) by exact Hgate end.
      rewrite Hgate'. cbn match.
      match goal with |- context[Defs.bind (Defs.or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (Defs.or_boolM A B) s = Some (true, s)) end.
      { match goal with |- exec (Defs.or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        unfold Defs.or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hgt). cbn match zeta.
      rewrite (exec_bind_Some _ _ _ _ _ Hrdx). cbn match beta.
      rewrite autocast_id.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_check_leaf_pte_leaf0 vpn m0 acc pv mxr do_sum Hv0 Hl0 Hchkm Hnap
                    (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                    menvcfg0 s Hmisa Hmenv HPBMTE)).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv0 ac = Some m0') by exact Hupd end.
      rewrite Hupd'. cbn match. rewrite autocast_id.
      match goal with |- context[Defs.bind (write_pte_conditional ?aa' ?wd' ?pv') ?k] =>
        assert (Hwrite' : exec (write_pte_conditional aa' wd' pv') s = Some (Ok true, sw))
          by exact Hwrite end.
      rewrite (exec_bind_Some _ _ _ _ _ Hwrite'). cbn match. apply exec_returnm. }
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hgate' : @update_PTE_Bits w pv0 ac = Some q0g) by exact Hgate end.
      rewrite Hgate'. cbn match.
      match goal with |- context[Defs.bind (Defs.or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (Defs.or_boolM A B) s = Some (true, s));
        [ | assert (Hgtg : goodmb Dr Dw (Defs.or_boolM A B) s mm = true) ] end.
      { match goal with |- exec (Defs.or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        unfold Defs.or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnm. }
      { match goal with |- goodmb _ _ (Defs.or_boolM ?A ?B) _ _ = true =>
          assert (Handg : goodmb Dr Dw A s mm = true);
          [ | assert (Hand : exec A s = Some (true, s)) ] end.
        { erewrite gm_and_boolM;
            [ | apply goodmb_currentlyEnabled_Svadu
              | apply exec_currentlyEnabled_Svadu ].
          cbn match. gmm_rr menvcfg HDme. cbn beta. apply goodmb_returnm. }
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        erewrite gm_or_boolM; [ | exact Handg | exact Hand ]. cbn match. reflexivity. }
      gmm_peel Hgtg Hgt. cbn match zeta.
      gmm_peel Hrdxg Hrdx. cbn match beta.
      rewrite autocast_id.
      gmm_peel Hlfg
               (exec_check_leaf_pte_leaf0 vpn m0 acc pv mxr do_sum Hv0 Hl0 Hchkm Hnap
                  (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                  menvcfg0 s Hmisa Hmenv HPBMTE).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv0 ac = Some m0') by exact Hupd end.
      rewrite Hupd'. cbn match. rewrite autocast_id.
      gmm_peel Hwriteg Hwrite. cbn match. apply goodmb_returnm. }
    gmm_peel Hug Hu. cbn match.
    match goal with |- context[write_TLB ?ix ?en] =>
      assert (Hwt : exec (write_TLB ix en) sw
                    = Some (tt, set_reg sw tlb
                                  (vec_update_dec (register_lookup tlb sw.(sregs)) ix
                                     (Some en)))) end.
    { unfold write_TLB.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb sw)).
      try unfold Defs.bind0.
      first [ rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ sw));
              apply exec_returnm
            | apply (exec_write_reg tlb _ sw) ]. }
    match goal with |- context[write_TLB ?ix ?en] =>
      gmm_peel (goodmb_write_TLB ix en sw mm) Hwt end.
    match goal with |- context[goodmb _ _ _ ?st _] =>
      gmm_peel (goodmb_uwe_pbmt vpn q2 q1 q0 asid st mm Hpb)
               (uwe_pbmt vpn q2 q1 q0 asid st Hpb) end.
    rewrite uwe_ppn. apply goodmb_returnm.
  Qed.

  (* HIT, A/D already sufficient: free off [PtTree.goodb_translate_TLB_hit_pt] *)
  Lemma goodmb_translate_TLB_hit_pt (vpn : mword 27) (q2 q1 q0 : mword 64)
      (asid : mword 16) (idx : Z) (s : mstate) (mm : pamap) :
    pte_check_ok acc pv mxr do_sum q0 ->
    pte_check_pure acc pv mxr do_sum Dr q0 ->
    update_PTE_Bits (autocast (T := mword) q0 : mword 64) acc = None ->
    pte_pbmt0 q0 ->
    goodmb Dr Dw (translate_TLB_hit 39 asid vpn acc pv mxr do_sum tt idx
                    (u_walk_entry vpn q2 q1 q0 asid)) s mm = true.
  Proof.
    intros Hchk Hpure Hupd Hpb.
    apply (goodmb_of_goodb Dr Dw _ s mm).
    exact (goodb_translate_TLB_hit_pt acc pv mxr do_sum Dr vpn q2 q1 q0 asid idx s
             Hchk Hpure Hupd Hpb).
  Qed.

  (* HIT + refresh: memory ALREADY has the bits, so nothing is written and
     the stale entry is merely refreshed with the memory word *)
  Lemma goodmb_translate_TLB_hit_pt_refresh (vpn : mword 27)
      (q2 q1 q0 q0g m0 : mword 64) (menvcfg0 : mword 64) (asid : mword 16)
      (idx : Z) (s : mstate) (mm : pamap) :
    pte_check_ok acc pv mxr do_sum q0 ->
    (forall (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec q0 7 0))
                   (ext_bits_of_PTE q0) tt) s0 = true) ->
    update_PTE_Bits (q0 : mword 64) acc = Some q0g ->
    pte_pbmt0 q0 ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok m0, s) ->
    goodmb Dr Dw
      (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 8)
      s mm = true ->
    pte_valid m0 -> pte_leaf m0 -> pte_no_napot m0 ->
    pte_check_ok acc pv mxr do_sum m0 ->
    goodmb Dr Dw
      (check_leaf_pte 39 vpn acc pv mxr do_sum m0
         (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0))) 0 tt) s mm
      = true ->
    register_lookup misa s.(sregs) = MISA_C ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    (exists a2 d2 : mword 1, m0 = pte_set_ad q0 a2 d2) ->
    update_PTE_Bits (m0 : mword 64) acc = None ->
    goodmb Dr Dw (translate_TLB_hit 39 asid vpn acc pv mxr do_sum tt idx
                    (u_walk_entry vpn q2 q1 q0 asid)) s mm = true.
  Proof.
    intros Hchk Hchkg Hgate Hpb Hmenv HADUE Hrdx Hrdxg Hv0 Hl0 Hnap Hchkm Hlfg
           Hmisa HPBMTE Hvar Hupd.
    unfold translate_TLB_hit. cbn zeta.
    match goal with |- context[tlb_get_pte ?sz ?e] => change sz with 8 end.
    rewrite uwe_pte. rewrite autocast_id.
    gmm_peel (goodmb_of_goodb Dr Dw _ s mm (Hchkg Dr s)) (Hchk s). cbn match.
    match goal with |- context[update_and_write_pte ?w ?vp0 ?aa ?pv0 ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec (update_and_write_pte w vp0 aa pv0 lv ac pr mx ds e) s
                   = Some (Ok (Some m0, tt), s));
      [ | assert (Hug : goodmb Dr Dw
                    (update_and_write_pte w vp0 aa pv0 lv ac pr mx ds e) s mm = true) ] end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hgate' : @update_PTE_Bits w pv0 ac = Some q0g) by exact Hgate end.
      rewrite Hgate'. cbn match.
      match goal with |- context[Defs.bind (Defs.or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (Defs.or_boolM A B) s = Some (true, s)) end.
      { match goal with |- exec (Defs.or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        unfold Defs.or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hgt). cbn match zeta.
      rewrite (exec_bind_Some _ _ _ _ _ Hrdx). cbn match beta.
      rewrite autocast_id.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_check_leaf_pte_leaf0 vpn m0 acc pv mxr do_sum Hv0 Hl0 Hchkm Hnap
                    (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                    menvcfg0 s Hmisa Hmenv HPBMTE)).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv0 ac = None) by exact Hupd end.
      rewrite Hupd'. cbn match. rewrite ?autocast_id. apply exec_returnm. }
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hgate' : @update_PTE_Bits w pv0 ac = Some q0g) by exact Hgate end.
      rewrite Hgate'. cbn match.
      match goal with |- context[Defs.bind (Defs.or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (Defs.or_boolM A B) s = Some (true, s));
        [ | assert (Hgtg : goodmb Dr Dw (Defs.or_boolM A B) s mm = true) ] end.
      { match goal with |- exec (Defs.or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        unfold Defs.or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnm. }
      { match goal with |- goodmb _ _ (Defs.or_boolM ?A ?B) _ _ = true =>
          assert (Handg : goodmb Dr Dw A s mm = true);
          [ | assert (Hand : exec A s = Some (true, s)) ] end.
        { erewrite gm_and_boolM;
            [ | apply goodmb_currentlyEnabled_Svadu
              | apply exec_currentlyEnabled_Svadu ].
          cbn match. gmm_rr menvcfg HDme. cbn beta. apply goodmb_returnm. }
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        erewrite gm_or_boolM; [ | exact Handg | exact Hand ]. cbn match. reflexivity. }
      gmm_peel Hgtg Hgt. cbn match zeta.
      gmm_peel Hrdxg Hrdx. cbn match beta.
      rewrite autocast_id.
      gmm_peel Hlfg
               (exec_check_leaf_pte_leaf0 vpn m0 acc pv mxr do_sum Hv0 Hl0 Hchkm Hnap
                  (Physaddr (u_pte_addr (u_next_base q1) (subrange_vec_dec vpn 8 0)))
                  menvcfg0 s Hmisa Hmenv HPBMTE).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv0 ac = None) by exact Hupd end.
      rewrite Hupd'. cbn match. rewrite ?autocast_id. apply goodmb_returnm. }
    gmm_peel Hug Hu. cbn match.
    match goal with |- context[write_TLB ?ix ?en] =>
      assert (Hwt : exec (write_TLB ix en) s
                    = Some (tt, set_reg s tlb
                                  (vec_update_dec (register_lookup tlb s.(sregs)) ix
                                     (Some en)))) end.
    { unfold write_TLB.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg tlb s)).
      try unfold Defs.bind0.
      first [ rewrite (exec_bind_Some _ _ _ _ _ (exec_write_reg tlb _ s));
              apply exec_returnm
            | apply (exec_write_reg tlb _ s) ]. }
    match goal with |- context[write_TLB ?ix ?en] =>
      gmm_peel (goodmb_write_TLB ix en s mm) Hwt end.
    match goal with |- context[goodmb _ _ _ ?st _] =>
      gmm_peel (goodmb_uwe_pbmt vpn q2 q1 q0 asid st mm Hpb)
               (uwe_pbmt vpn q2 q1 q0 asid st Hpb) end.
    rewrite uwe_ppn. apply goodmb_returnm.
  Qed.

  (* the MISS with a write-back: the walk, then the atomic A/D update that
     actually writes, then the fill *)
  Lemma goodmb_translate_TLB_miss_pt_upd (vpn : mword 27) (root : mword 44)
      (p2 p1 p0 p0' : mword 64) (menvcfg0 : mword 64) (asid : mword 16)
      (sw : mstate) (s : mstate) (mm : pamap) :
    Dr misa = true ->
    pte_valid p2 -> pte_ptr p2 ->
    pte_valid p1 -> pte_ptr p1 ->
    pte_valid p0 -> pte_leaf p0 -> pte_no_napot p0 ->
    pte_check_ok acc pv mxr do_sum p0 ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                   (ext_bits_of_PTE p2)) s0 = true) ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                   (ext_bits_of_PTE p1)) s0 = true) ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p0 7 0))
                   (ext_bits_of_PTE p0)) s0 = true) ->
    (forall (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec p0 7 0))
                   (ext_bits_of_PTE p0) tt) s0 = true) ->
    update_PTE_Bits (p0 : mword 64) acc = Some p0' ->
    exec (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8) s
      = Some (Ok p2, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr root (subrange_vec_dec vpn 26 18))) 8)
      s mm = true ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8) s
      = Some (Ok p1, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr (u_next_base p2) (subrange_vec_dec vpn 17 9))) 8)
      s mm = true ->
    exec (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s) ->
    goodmb Dr Dw (read_pte (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8)
      s mm = true ->
    exec (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8) s
      = Some (Ok p0, s) ->
    goodmb Dr Dw (read_pte_exclusive (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8)
      s mm = true ->
    register_lookup misa s.(sregs) = MISA_C ->
    register_lookup menvcfg s.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (write_pte_conditional (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
            (p0' : mword 64)) s = Some (Ok true, sw) ->
    goodmb Dr Dw (write_pte_conditional (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0))) 8
            (p0' : mword 64)) s mm = true ->
    sw.(sregs) = s.(sregs) ->
    goodmb Dr Dw (translate_TLB_miss 39 asid root vpn acc pv mxr do_sum tt) s mm = true.
  Proof.
    intros HDmi Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hchk Hg2 Hg1 Hg0 Hgchk Hupd
           Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hrdx Hrdxg
           Hmisa Hmenv HPBMTE HADUE Hwrite Hwriteg Hswregs.
    unfold translate_TLB_miss. cbn zeta.
    match goal with |- context[pt_walk 39 _ _ _ _ _ _ ?l false ?e] =>
      change l with 2 end.
    gmm_peel (goodmb_pt_walk_user vpn root p2 p1 p0 acc pv mxr do_sum
                Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk Hnap Hg1 Hg2 Hg0 Hgchk Dr Dw HDmi HDme
                menvcfg0 s mm Hmisa Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hmenv HPBMTE)
             (exec_pt_walk_user vpn root p2 p1 p0 acc pv mxr do_sum
                Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hchk Hnap menvcfg0 s
                Hmisa Hrd2 Hrd1 Hrd0 Hmenv HPBMTE).
    cbn match. cbn zeta.
    match goal with |- context[update_and_write_pte ?w ?vp0 ?aa ?pv0 ?lv ?ac ?pr ?mx ?ds ?e] =>
      assert (Hu : exec (update_and_write_pte w vp0 aa pv0 lv ac pr mx ds e) s
                   = Some (Ok (Some p0', tt), sw));
      [ | assert (Hug : goodmb Dr Dw
                    (update_and_write_pte w vp0 aa pv0 lv ac pr mx ds e) s mm = true) ] end.
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv0 ac = Some p0') by exact Hupd end.
      rewrite Hupd'. cbn match.
      match goal with |- context[Defs.bind (Defs.or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (Defs.or_boolM A B) s = Some (true, s)) end.
      { match goal with |- exec (Defs.or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        unfold Defs.or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hgt). cbn match zeta.
      rewrite (exec_bind_Some _ _ _ _ _ Hrdx). cbn match beta. rewrite autocast_id.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum Hv0 Hl0 Hchk Hnap
                    (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)))
                    menvcfg0 s Hmisa Hmenv HPBMTE)).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w0 ?pv1 ?ac0] =>
        replace (@update_PTE_Bits w0 pv1 ac0) with (Some p0')
          by (symmetry; exact Hupd) end.
      cbn match. rewrite autocast_id.
      match goal with |- context[Defs.bind (write_pte_conditional ?aa' ?wd' ?pv') ?k] =>
        assert (Hwrite' : exec (write_pte_conditional aa' wd' pv') s = Some (Ok true, sw))
          by exact Hwrite end.
      rewrite (exec_bind_Some _ _ _ _ _ Hwrite'). cbn match. apply exec_returnm. }
    { unfold update_and_write_pte.
      match goal with |- context[@update_PTE_Bits ?w ?pv0 ?ac] =>
        assert (Hupd' : @update_PTE_Bits w pv0 ac = Some p0') by exact Hupd end.
      rewrite Hupd'. cbn match.
      match goal with |- context[Defs.bind (Defs.or_boolM ?A ?B) ?k] =>
        assert (Hgt : exec (Defs.or_boolM A B) s = Some (true, s));
        [ | assert (Hgtg : goodmb Dr Dw (Defs.or_boolM A B) s mm = true) ] end.
      { match goal with |- exec (Defs.or_boolM ?A ?B) s = _ =>
          assert (Hand : exec A s = Some (true, s)) end.
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        unfold Defs.or_boolM.
        rewrite (exec_bind_Some _ _ _ _ _ Hand). cbn match. apply exec_returnm. }
      { match goal with |- goodmb _ _ (Defs.or_boolM ?A ?B) _ _ = true =>
          assert (Handg : goodmb Dr Dw A s mm = true);
          [ | assert (Hand : exec A s = Some (true, s)) ] end.
        { erewrite gm_and_boolM;
            [ | apply goodmb_currentlyEnabled_Svadu
              | apply exec_currentlyEnabled_Svadu ].
          cbn match. gmm_rr menvcfg HDme. cbn beta. apply goodmb_returnm. }
        { unfold Defs.and_boolM.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_currentlyEnabled_Svadu s)). cbn match.
          rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)). cbn beta.
          rewrite Hmenv. rewrite HADUE. apply exec_returnm. }
        erewrite gm_or_boolM; [ | exact Handg | exact Hand ]. cbn match. reflexivity. }
      gmm_peel Hgtg Hgt. cbn match zeta.
      gmm_peel Hrdxg Hrdx. cbn match beta. rewrite autocast_id.
      gmm_peel (goodmb_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum
                  Hv0 Hl0 Hchk Hnap Hg0 Hgchk Dr Dw HDmi HDme
                  (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)))
                  menvcfg0 s mm Hmisa Hmenv HPBMTE)
               (exec_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum Hv0 Hl0 Hchk Hnap
                  (Physaddr (u_pte_addr (u_next_base p1) (subrange_vec_dec vpn 8 0)))
                  menvcfg0 s Hmisa Hmenv HPBMTE).
      cbn match beta.
      match goal with |- context[@update_PTE_Bits ?w0 ?pv1 ?ac0] =>
        replace (@update_PTE_Bits w0 pv1 ac0) with (Some p0')
          by (symmetry; exact Hupd) end.
      cbn match. rewrite autocast_id.
      gmm_peel Hwriteg Hwrite. cbn match. apply goodmb_returnm. }
    gmm_peel Hug Hu. cbn match.
    match goal with |- context[add_to_TLB 39 asid vpn ?pp ?pte ?ptea 0 ?g] =>
      gmm_peel (goodmb_add_to_TLB_pt asid vpn pp pte ptea g sw mm)
               (exec_add_to_TLB_pt asid vpn pp pte ptea g sw) end.
    apply goodmb_returnm.
  Qed.

End PtAdue.

(* ===================================================================== *)
(* 6. THE [translateAddr] FRONT MATTER ([PtTreeAdue] section 5's twin).    *)
(*                                                                        *)
(* [exec_translateAddr_pt_front] factored the mstatus/priv reads, the Sv39 *)
(* dispatch, canonicality and the satp -> root/asid decode once over an    *)
(* arbitrary successful [translate]; the certificate factors exactly the   *)
(* same way.  The three monadic ingredients arrive as exec fact PLUS       *)
(* [goodb] certificate (the shape [swp_translateAddr_pt_front] already     *)
(* uses), and [translate]'s own certificate is the fourth premise.         *)
(* ===================================================================== *)
Section TranslateFront.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pv : Privilege).
  Hypothesis HDms : Dr mstatus = true.
  Hypothesis HDcp : Dr cur_privilege = true.
  Hypothesis HDsatp : Dr satp = true.

  Lemma goodmb_translateAddr_pt_front (vpn : mword 27) (root : mword 44)
      (ppnv : mword 44) (satp0 va : mword 64) (s : mstate) (mm : pamap) :
    exec (effectivePrivilege acc (register_lookup mstatus s.(sregs)) pv) s
      = Some (pv, s) ->
    goodb Dr (effectivePrivilege acc (register_lookup mstatus s.(sregs)) pv) s
      = true ->
    exec (is_shadow_stack_access acc) s = Some (false, s) ->
    goodb Dr (is_shadow_stack_access acc) s = true ->
    register_lookup cur_privilege s.(sregs) = pv ->
    exec (translationMode pv) s = Some (Sv39, s) ->
    goodb Dr (translationMode pv) s = true ->
    register_lookup satp s.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0))
      = false ->
    autocast (T := mword) (subrange_vec_dec
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)
      (Z.sub 39 1) pagesize_bits) = vpn ->
    (exists s' : mstate,
       forall mxr do_sum,
         exec (translate 39 (mword_of_int 0 : mword 16) root vpn acc pv mxr do_sum tt) s
         = Some (Ok (ppnv, PBMT_PMA, tt), s')) ->
    (forall mxr do_sum,
       goodmb Dr Dw
         (translate 39 (mword_of_int 0 : mword 16) root vpn acc pv mxr do_sum tt)
         s mm = true) ->
    goodmb Dr Dw (translateAddr (Virtaddr va) acc) s mm = true.
  Proof.
    intros Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon Hvpn_def
           [s' Htr] Htrg.
    unfold translateAddr. apply goodmb_cer.
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDms)
              ltac:(apply (exec_read_reg mstatus)).
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDcp)
              ltac:(apply (exec_read_reg cur_privilege)).
    rewrite Hcp.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Heffg) Heff.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Htmg) Htm.
    gmm_lift (goodmb_of_goodb Dr Dw _ s mm Hssg) Hss.
    unfold Defs.bind0.
    replace (generic_eq Sv39 Bare) with false by (vm_compute; reflexivity).
    erewrite gm_bindR; [ | apply goodmb_returnm | apply execR_returnR_fwd ].
    cbn match.
    assert (Hwidth : exec (satp_mode_width_forwards Sv39) s = Some (39, s))
      by (cbn; apply exec_returnm).
    gmm_lift (goodmb_returnm Dr Dw (E := exception) 39 s mm) Hwidth.
    assert (Hgs : exec (get_satp 39) s = Some (autocast (T := mword) satp0, s)).
    { unfold get_satp.
      assert (Hae : exec (Defs.assert_exp' (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64))
                            "sys/vmem.sail:395.30-395.31") s = Some (eq_refl, s)).
      { replace (orb (Z.eqb (__id 39) 32) (Z.eqb xlen 64)) with true
          by (vm_compute; reflexivity).
        unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
      rewrite (exec_bind_Some _ _ _ _ _ Hae).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg satp s)).
      rewrite Hsatp. apply exec_returnm. }
    assert (Hgsg : goodmb Dr Dw (get_satp 39) s mm = true).
    { unfold get_satp.
      gmm_peelT ltac:(apply goodmb_assert_exp'_true)
                ltac:(apply exec_assert_exp'_true).
      change (Z.eqb 39 32) with false. cbn match.
      unfold autocast_m.
      gmm_rr satp HDsatp. apply goodmb_returnm. }
    gmm_lift Hgsg Hgs.
    assert (Hae2 : exec (Defs.assert_exp' (orb (Z.eqb 39 32) (Z.eqb xlen 64))
                          "sys/vmem.sail:431.36-431.37") s = Some (eq_refl, s)).
    { replace (orb (Z.eqb 39 32) (Z.eqb xlen 64)) with true
        by (vm_compute; reflexivity).
      unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    gmm_liftT ltac:(apply goodmb_assert_exp'_true) ltac:(exact Hae2).
    rewrite Hcanon. cbn match.
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDms)
              ltac:(apply (exec_read_reg mstatus)).
    gmm_liftT ltac:(rewrite goodmb_read_reg; exact HDms)
              ltac:(apply (exec_read_reg mstatus)).
    match goal with |- context[translate 39 ?asidx ?bppn ?vpnx _ _ _ _ _] =>
      replace vpnx with vpn by (symmetry; exact Hvpn_def);
      replace bppn with root by (symmetry; exact Hppn);
      replace asidx with (mword_of_int 0 : mword 16) by (symmetry; exact Hasid) end.
    match goal with |- context[translate 39 _ _ _ _ _ ?mx ?ds _] =>
      gmm_lift (Htrg mx ds) (Htr mx ds) end.
    cbn match. apply goodmb_returnm.
  Qed.

End TranslateFront.

(* ===================================================================== *)
(* 7. THE PER-SLOT ACCESS CERTIFICATES ([PtTree.pt_read_pte_slot]'s        *)
(* twins): a page-table slot recorded by [pt_slot_mem] and OWNED in [mm]   *)
(* is readable, exclusively readable and conditionally writable, with the  *)
(* PMP/PMA side conditions derived exactly as the exec lemmas derive them. *)
(* ===================================================================== *)
Section SlotCert.
  Context (Dr Dw : register -> bool).
  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.

  Lemma slot_pmp_range (sg : mstate) (a w : mword 64) :
    pt_slot_mem sg a w ->
    (ram_base + ram_size
       <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
      (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0)) 4)
      (uint a) (uint (to_bits 64 8)) = PMP_Match.
  Proof.
    intros (Hbytes & Hram & Hram7 & Halign) Hcov.
    assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
    { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
      change (Z.of_nat 7) with 7. lia. }
    assert (Hfit : (uint a + 8 <= ram_base + ram_size)%Z).
    { pose proof (uint_pa_add a 7 Hnw) as Heq.
      destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7.
      change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    apply (ram_pmp_match_w a _ 8);
      [ lia | vm_compute; reflexivity | | exact Hfit | exact Hcov ].
    destruct Hram as [Hlo _]. exact Hlo.
  Qed.

  Lemma goodmb_read_pte_slot (sg : mstate) (mm : pamap) (a w : mword 64)
      (region : PMA_Region) :
    pt_slot_mem sg a w ->
    bytes_owned mm a 8 = true ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    matching_pma_region (register_lookup pma_regions sg.(sregs)) (Physaddr a) 8 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    goodmb Dr Dw (read_pte (Physaddr a) 8) sg mm = true.
  Proof.
    intros Hsm Hown HA Hord HR Hcov Hmatch Hpma Hhtif.
    pose proof (slot_pmp_range sg a w Hsm Hcov) as Hrange.
    destruct Hsm as (Hbytes & Hram & Hram7 & Halign).
    exact (goodmb_read_pte_S Dr Dw a region w sg mm HDc HDa HDp HDh
             HA Hord Hrange HR Hmatch Halign Hpma
             (within_clint_false a 8 sg (addr_is_ram_not_in_clint _ Hram) ltac:(lia))
             (within_sig_false a 8 sg (addr_is_ram_not_in_sig _ Hram) ltac:(lia))
             Hhtif (addr_is_ram_not_dev _ Hram) Hown Hbytes).
  Qed.

  Lemma goodmb_read_pte_exclusive_slot (sg : mstate) (mm : pamap) (a w : mword 64)
      (region : PMA_Region) :
    pt_slot_mem sg a w ->
    bytes_owned mm a 8 = true ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    matching_pma_region (register_lookup pma_regions sg.(sregs)) (Physaddr a) 8 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_read) = true ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    goodmb Dr Dw (read_pte_exclusive (Physaddr a) 8) sg mm = true.
  Proof.
    intros Hsm Hown HA Hord HR Hcov Hmatch Hpma Hhtif.
    pose proof (slot_pmp_range sg a w Hsm Hcov) as Hrange.
    destruct Hsm as (Hbytes & Hram & Hram7 & Halign).
    exact (goodmb_read_pte_exclusive_S Dr Dw a region w sg mm HDc HDa HDp HDh
             HA Hord Hrange HR Hmatch Halign Hpma
             (within_clint_false a 8 sg (addr_is_ram_not_in_clint _ Hram) ltac:(lia))
             (within_sig_false a 8 sg (addr_is_ram_not_in_sig _ Hram) ltac:(lia))
             Hhtif (addr_is_ram_not_dev _ Hram) Hown Hbytes).
  Qed.

  Lemma goodmb_write_pte_conditional_slot (sg : mstate) (mm : pamap)
      (a w w' : mword 64) (region : PMA_Region) :
    pt_slot_mem sg a w ->
    bytes_owned mm a 8 = true ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    matching_pma_region (register_lookup pma_regions sg.(sregs)) (Physaddr a) 8 = Some region ->
    (override_PMA (PMA_Region_attributes region) PBMT_PMA).(PMA_supports_pte_write) = true ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    goodmb Dr Dw (write_pte_conditional (Physaddr a) 8 (w' : mword 64)) sg mm = true.
  Proof.
    intros Hsm Hown HA Hord HW Hcov Hmatch Hpma Hhtif.
    destruct Hsm as (Hbytes & Hram & Hram7 & Halign).
    exact (goodmb_write_pte_conditional_ram Dr Dw a w' region sg mm HDc HDa HDp HDh
             Hram Hram7 Halign HA Hord HW Hcov Hmatch Hpma Hhtif Hown).
  Qed.

End SlotCert.

(* ===================================================================== *)
(* 8. THE TOP OF THE WALK: [KptTree.ptree_translateAddr_cases]'s twin.     *)
(*                                                                        *)
(* One certificate for the whole of [translateAddr] over an owned ptree,   *)
(* with the SAME five-way case analysis the exec lemma makes -- TLB hit    *)
(* with no update / with a refresh / with a write-back, a foreign entry,   *)
(* an empty slot -- because a certificate follows the STATE-RESOLVED path  *)
(* and therefore has to know which one the machine takes.                  *)
(*                                                                        *)
(* The new premises over the exec lemma's are: the [Dr]/[Dw] entries for   *)
(* the ten cells the walk touches, the [goodb] companion of each pure PTE  *)
(* test (which the tier's instances discharge by [vm_compute] at a         *)
(* concrete flag byte, exactly where they discharge the exec versions),    *)
(* and [bytes_owned mm <slot> 8 = true] for the three slots -- the         *)
(* projection of [UserBytes.u_mem_wf] that says the hart OWNS its table.   *)
(* ===================================================================== *)
Section PtreeTranslateCert.
  Context (Dr Dw : register -> bool).
  Context (acc : MemoryAccessType mem_payload) (pv : Privilege).
  Hypothesis HDmi : Dr misa = true.
  Hypothesis HDme : Dr menvcfg = true.
  Hypothesis HDms : Dr mstatus = true.
  Hypothesis HDcp : Dr cur_privilege = true.
  Hypothesis HDsatp : Dr satp = true.
  Hypothesis HDt : Dr tlb = true.
  Hypothesis HWt : Dw tlb = true.
  Hypothesis HDc : Dr pmpcfg_n = true.
  Hypothesis HDa : Dr pmpaddr_n = true.
  Hypothesis HDp : Dr pma_regions = true.
  Hypothesis HDh : Dr htif_tohost_base = true.

  (* the shared miss path, certified *)
  Lemma goodmb_ptree_translate_miss_core (root_ppn : mword 44) (va w : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6)) (p2 p1 : mword 64)
      (a0 d0 : mword 1) (mxr do_sum : bool) (sg : mstate) (mm : pamap) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr0 do_sum0 : bool),
       pte_check_ok acc pv mxr0 do_sum0 (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr0 do_sum0 : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr0 do_sum0
                   (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true) ->
    pte_valid p2 -> pte_ptr p2 ->
    pte_valid p1 -> pte_ptr p1 ->
    pte_valid p0 -> pte_leaf p0 -> pte_no_napot p0 ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                   (ext_bits_of_PTE p2)) s0 = true) ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                   (ext_bits_of_PTE p1)) s0 = true) ->
    (forall (a d : mword 1) (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true) ->
    pt_slot_mem sg (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2 ->
    pt_slot_mem sg (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    bytes_owned mm (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8 = true ->
    bytes_owned mm (pt_addr1 p2 vpn) 8 = true ->
    bytes_owned mm (pt_addr0 p1 vpn) 8 = true ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup tlb sg.(sregs) = tlbvec ->
    exec (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg) ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions sg.(sregs)) ->
    goodmb Dr Dw (translate 39 (mword_of_int 0 : mword 16) root_ppn vpn acc pv mxr do_sum tt)
      sg mm = true.
  Proof.
    intros vpn p0 Hchk Hgchk Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hg2 Hg1 Hg0
           Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
           Hmisa Hmenv Hhtif Htlb Hlk HA Hord HR HW Hcov Hpmar Hpmaw.
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    (* the three slot reads, exec side and certificate side *)
    destruct (Hpmar (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) (pt_slot_ram_access _ _ _ Hsm2))
      as (region2 & Hm2 & Hs2).
    destruct (Hpmar (pt_addr1 p2 vpn) (pt_slot_ram_access _ _ _ Hsm1))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_slot sg _ p2 region2 Hsm2 HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2.
    pose proof (pt_read_pte_slot sg _ p1 region1 Hsm1 HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1.
    pose proof (pt_read_pte_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0.
    pose proof (pt_read_pte_exclusive_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    pose proof (goodmb_read_pte_slot Dr Dw HDc HDa HDp HDh sg mm _ p2 region2
                  Hsm2 Hown2 HA Hord HR Hcov Hm2 Hs2 Hhtif) as Hrd2g.
    pose proof (goodmb_read_pte_slot Dr Dw HDc HDa HDp HDh sg mm _ p1 region1
                  Hsm1 Hown1 HA Hord HR Hcov Hm1 Hs1 Hhtif) as Hrd1g.
    pose proof (goodmb_read_pte_slot Dr Dw HDc HDa HDp HDh sg mm _ p0 region0
                  Hsm0 Hown0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrd0g.
    pose proof (goodmb_read_pte_exclusive_slot Dr Dw HDc HDa HDp HDh sg mm _ p0 region0
                  Hsm0 Hown0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrdxg.
    unfold translate.
    gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlk.
    cbn match. try rewrite <- Htlb.
    destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hup.
    - (* the walk writes the A/D-updated leaf back *)
      destruct (Hpmaw (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
        as (regionw & Hmw & Hww).
      pose proof (goodmb_write_pte_conditional_slot Dr Dw HDc HDa HDp HDh sg mm
                    _ p0 p0' regionw Hsm0 Hown0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwrg.
      destruct Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
      pose proof (exec_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw sg
                    Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwr.
      exact (goodmb_translate_TLB_miss_pt_upd Dr Dw acc pv mxr do_sum HDt HWt HDme
               vpn root_ppn p2 p1 p0 p0' MENVCFG_S (mword_of_int 0) _ sg mm
               HDmi Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
               Hg2 Hg1 (Hg0 a0 d0) (Hgchk a0 d0 mxr do_sum) Hup
               Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hrdx Hrdxg
               Hmisa Hmenv HPBMTE HADUE Hwr Hwrg eq_refl).
    - (* clean fill *)
      assert (Hupd : update_PTE_Bits (autocast (T := mword) p0 : mword 64) acc = None)
        by exact Hup.
      exact (goodmb_translate_TLB_miss_user vpn root_ppn p2 p1 p0 acc pv mxr do_sum
               Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap
               Hg1 Hg2 (Hg0 a0 d0) (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
               (mword_of_int 0) MENVCFG_S sg mm HDt HWt Hmisa Hupd
               Hrd2 Hrd2g Hrd1 Hrd1g Hrd0 Hrd0g Hmenv HPBMTE).
  Qed.

  (* THE WHOLE OF [translateAddr] OVER AN OWNED PTREE, certified.  Same
     five-way split as [KptTree.ptree_translateAddr_cases]. *)
  Lemma goodmb_ptree_translateAddr (root_ppn : mword 44) (t : ptree)
      (va w pa satp0 : mword 64) (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (p2 p1 : mword 64) (a0 d0 : mword 1) (sg : mstate) (mm : pamap) :
    let vpn := svpn_of va in
    let p0 := pte_set_ad w a0 d0 in
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc pv mxr do_sum (pte_set_ad w a d)) ->
    (forall (a d : mword 1) (mxr do_sum : bool) (Db : register -> bool) s0,
       goodb Db (check_PTE_permission acc pv mxr do_sum
                   (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec
        ((autocast (T := mword) ((autocast (T := mword) (PPN_of_PTE (w : mword 64))) : mword 44)) : mword 44)
        (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa ->
    (forall a d : mword 1, pte_pbmt0 (pte_set_ad w a d)) ->
    pt_base t = root_ppn ->
    ptree_maps t vpn p2 p1 p0 ->
    tlb_ok_pt (mword_of_int 0) t tlbvec ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                   (ext_bits_of_PTE p2)) s0 = true) ->
    (forall (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                   (ext_bits_of_PTE p1)) s0 = true) ->
    (forall (a d : mword 1) (Db : register -> bool) s0,
       goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                   (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true) ->
    pt_slot_mem sg (pt_addr2 t vpn) p2 ->
    pt_slot_mem sg (pt_addr1 p2 vpn) p1 ->
    pt_slot_mem sg (pt_addr0 p1 vpn) p0 ->
    bytes_owned mm (pt_addr2 t vpn) 8 = true ->
    bytes_owned mm (pt_addr1 p2 vpn) 8 = true ->
    bytes_owned mm (pt_addr0 p1 vpn) 8 = true ->
    register_lookup misa sg.(sregs) = MISA_C ->
    register_lookup menvcfg sg.(sregs) = MENVCFG_S ->
    register_lookup htif_tohost_base sg.(sregs) = None ->
    register_lookup cur_privilege sg.(sregs) = pv ->
    exec (translationMode pv) sg = Some (Sv39, sg) ->
    goodb Dr (translationMode pv) sg = true ->
    exec (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) pv) sg
      = Some (pv, sg) ->
    goodb Dr (effectivePrivilege acc (register_lookup mstatus sg.(sregs)) pv) sg = true ->
    exec (is_shadow_stack_access acc) sg = Some (false, sg) ->
    goodb Dr (is_shadow_stack_access acc) sg = true ->
    register_lookup satp sg.(sregs) = satp0 ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64)) = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64)) = (mword_of_int 0 : mword 16) ->
    register_lookup tlb sg.(sregs) = tlbvec ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec (register_lookup pmpcfg_n sg.(sregs)) 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec (register_lookup pmpaddr_n sg.(sregs)) 0) * 4)%Z ->
    pma_allows_pte_read (register_lookup pma_regions sg.(sregs)) ->
    pma_allows_pte_write (register_lookup pma_regions sg.(sregs)) ->
    goodmb Dr Dw (translateAddr (Virtaddr va) acc) sg mm = true.
  Proof.
    intros vpn p0 Hchk Hgchk Hcanon Hout Hvarp Hbase Hmaps Htlbok Hg2 Hg1 Hg0
           Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
           Hmisa Hmenv Hhtif Hcp Htm Htmg Heff Heffg Hss Hssg
           Hsatp Hppn Hasid Htlb HA Hord HR HW Hcov Hpmar Hpmaw.
    pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                         Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
    assert (Hsm2' : pt_slot_mem sg (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) p2).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hsm2. exact Hsm2. }
    assert (Hown2' : bytes_owned mm (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)) 8 = true).
    { assert (Ha2 : pt_addr2 t vpn = u_pte_addr root_ppn (subrange_vec_dec vpn 26 18)).
      { unfold pt_addr2. rewrite Hbase. reflexivity. }
      rewrite Ha2 in Hown2. exact Hown2. }
    destruct (Hpmar (u_pte_addr root_ppn (subrange_vec_dec vpn 26 18))
                (pt_slot_ram_access _ _ _ Hsm2')) as (region2 & Hm2 & Hs2).
    destruct (Hpmar (pt_addr1 p2 vpn) (pt_slot_ram_access _ _ _ Hsm1))
      as (region1 & Hm1 & Hs1).
    destruct (Hpmar (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
      as (region0 & Hm0r & Hs0).
    pose proof (pt_read_pte_exclusive_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
      as Hrdx.
    pose proof (goodmb_read_pte_exclusive_slot Dr Dw HDc HDa HDp HDh sg mm _ p0 region0
                  Hsm0 Hown0 HA Hord HR Hcov Hm0r Hs0 Hhtif) as Hrdxg.
    assert (HPBMTE : eq_vec (_get_MEnvcfg_PBMTE MENVCFG_S) ('b"0") = true)
      by (vm_compute; reflexivity).
    assert (HADUE : eq_vec (_get_MEnvcfg_ADUE MENVCFG_S) ('b"1") = true)
      by (vm_compute; reflexivity).
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) vpn)) as [ent|] eqn:Hslot.
    - destruct (Htlbok vpn ent Hslot) as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & ->).
      destruct (decide (vpn0 = vpn)) as [-> | Hne].
      + (* HIT on this vpn's own entry *)
        destruct (ptree_maps_det t vpn q2 q1 qp0 p2 p1 p0 Hm0 Hmaps) as (-> & -> & ->).
        assert (Habs : pte_set_ad p0 a' d' = pte_set_ad w a' d')
          by exact (pte_set_ad_absorb w a0 d0 a' d').
        assert (Hchkc : forall mxr do_sum,
                  pte_check_ok acc pv mxr do_sum (pte_set_ad p0 a' d')).
        { intros mxr do_sum. rewrite Habs. exact (Hchk a' d' mxr do_sum). }
        assert (Hchkcg : forall (mxr do_sum : bool) (Db : register -> bool) s0,
                  goodb Db (check_PTE_permission acc pv mxr do_sum
                              (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad p0 a' d') 7 0))
                              (ext_bits_of_PTE (pte_set_ad p0 a' d')) tt) s0 = true).
        { intros mxr do_sum Db s0. rewrite Habs. exact (Hgchk a' d' mxr do_sum Db s0). }
        assert (Hpbc : pte_pbmt0 (pte_set_ad p0 a' d'))
          by (rewrite Habs; apply Hvarp).
        assert (Hidc : zero_extend' 64 (concat_vec
                  ((autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44)) : mword 44)
                  (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub pagesize_bits 1) 0)) = pa).
        { rewrite pte_set_ad_ppn. unfold p0. rewrite pte_set_ad_ppn. exact Hout. }
        assert (Hlkh : exec (lookup_TLB 39 (mword_of_int 0) vpn) sg
                       = Some (Some (tlb_hash (__id 39) vpn,
                                     u_walk_entry vpn p2 p1 (pte_set_ad p0 a' d')
                                       (mword_of_int 0)), sg))
          by exact (exec_lookup_TLB_hit_ent vpn (mword_of_int 0) tlbvec _ sg Htlb Hslot
                      (uwe_match_self vpn p2 p1 (pte_set_ad p0 a' d'))).
        destruct (update_PTE_Bits (pte_set_ad p0 a' d' : mword 64) acc) as [q0'|] eqn:Hupq.
        * destruct (update_PTE_Bits (p0 : mword 64) acc) as [p0'|] eqn:Hupm.
          -- (* memory needs the update too: write it back *)
             assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
             { exists a0, d0. rewrite pte_set_ad_absorb.
               unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
             destruct (Hpmaw (pt_addr0 p1 vpn) (pt_slot_ram_access _ _ _ Hsm0))
               as (regionw & Hmw & Hww).
             pose proof (goodmb_write_pte_conditional_slot Dr Dw HDc HDa HDp HDh sg mm
                           _ p0 p0' regionw Hsm0 Hown0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwrg.
             pose proof Hsm0 as (Hbytes0 & Hram0 & Hram0' & Hal0).
             pose proof (exec_write_pte_conditional_ram (pt_addr0 p1 vpn) p0' regionw sg
                           Hram0 Hram0' Hal0 HA Hord HW Hcov Hmw Hww Hhtif) as Hwr.
             apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                      vpn root_ppn
                      (autocast (T := mword) ((autocast (T := mword)
                         (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                      satp0 va sg mm
                      Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
             ++ eexists. intros mxr do_sum. unfold translate.
                rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
                apply (exec_translate_TLB_hit_pt_upd acc pv mxr do_sum
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) _ sg
                         (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                         Hvarm Hupm Hwr eq_refl).
             ++ intros mxr do_sum. unfold translate.
                gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
                cbn match.
                apply (goodmb_translate_TLB_hit_pt_upd Dr Dw acc pv mxr do_sum HDt HWt HDme
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 p0' MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) _ sg mm
                         (Hchkc mxr do_sum) (Hchkcg mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hrdxg Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
                         (goodmb_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum
                            Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap (Hg0 a0 d0)
                            (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
                            (Physaddr (pt_addr0 p1 vpn)) MENVCFG_S sg mm
                            Hmisa Hmenv HPBMTE)
                         Hmisa HPBMTE Hvarm Hupm Hwr Hwrg eq_refl).
          -- (* memory ALREADY has them: no write, the entry is refreshed *)
             assert (Hvarm : exists a2 d2 : mword 1, p0 = pte_set_ad (pte_set_ad p0 a' d') a2 d2).
             { exists a0, d0. rewrite pte_set_ad_absorb.
               unfold p0. rewrite pte_set_ad_absorb. reflexivity. }
             apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                      vpn root_ppn
                      (autocast (T := mword) ((autocast (T := mword)
                         (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                      satp0 va sg mm
                      Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
             ++ eexists. intros mxr do_sum. unfold translate.
                rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
                apply (exec_translate_TLB_hit_pt_refresh acc pv mxr do_sum
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) sg
                         (Hchkc mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum) Hmisa HPBMTE
                         Hvarm Hupm).
             ++ intros mxr do_sum. unfold translate.
                gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
                cbn match.
                apply (goodmb_translate_TLB_hit_pt_refresh Dr Dw acc pv mxr do_sum
                         HDt HWt HDme
                         vpn p2 p1 (pte_set_ad p0 a' d') q0' p0 MENVCFG_S
                         (mword_of_int 0) (tlb_hash (__id 39) vpn) sg mm
                         (Hchkc mxr do_sum) (Hchkcg mxr do_sum) Hupq Hpbc Hmenv HADUE
                         Hrdx Hrdxg Hv0 Hl0 Hnap (Hchk a0 d0 mxr do_sum)
                         (goodmb_check_leaf_pte_leaf0 vpn p0 acc pv mxr do_sum
                            Hv0 Hl0 (Hchk a0 d0 mxr do_sum) Hnap (Hg0 a0 d0)
                            (Hgchk a0 d0 mxr do_sum) Dr Dw HDmi HDme
                            (Physaddr (pt_addr0 p1 vpn)) MENVCFG_S sg mm
                            Hmisa Hmenv HPBMTE)
                         Hmisa HPBMTE Hvarm Hupm).
        * (* hit, A/D already sufficient *)
          assert (Hupq' : update_PTE_Bits
                    (autocast (T := mword) (pte_set_ad p0 a' d') : mword 64) acc = None)
            by exact Hupq.
          apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                   vpn root_ppn
                   (autocast (T := mword) ((autocast (T := mword)
                      (PPN_of_PTE (pte_set_ad p0 a' d' : mword 64))) : mword 44))
                   satp0 va sg mm
                   Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl).
          -- exists sg. intros mxr do_sum. unfold translate.
             rewrite (exec_bind_Some _ _ _ _ _ Hlkh). cbn match.
             apply (exec_translate_TLB_hit_pt acc pv mxr do_sum
                      vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                      (tlb_hash (__id 39) vpn) sg (Hchkc mxr do_sum) Hupq' Hpbc).
          -- intros mxr do_sum. unfold translate.
             gmm_peel (goodmb_lookup_TLB vpn Dr Dw (mword_of_int 0) sg mm HDt) Hlkh.
             cbn match.
             apply (goodmb_translate_TLB_hit_pt Dr Dw acc pv mxr do_sum
                      vpn p2 p1 (pte_set_ad p0 a' d') (mword_of_int 0)
                      (tlb_hash (__id 39) vpn) sg mm (Hchkc mxr do_sum)
                      (fun s0 => Hchkcg mxr do_sum Dr s0) Hupq' Hpbc).
      + (* foreign entry: rejected by the tag, so the walk runs *)
        assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg))
          by exact (exec_lookup_TLB_nomatch_s vpn (mword_of_int 0) _ tlbvec sg Htlb Hslot
                      (uwe_match_other vpn0 vpn q2 q1 (pte_set_ad qp0 a' d')
                         (mword_of_int 0) Hne)).
        destruct (ptree_translate_miss_core acc pv root_ppn va w tlbvec p2 p1 a0 d0 sg Hchk
                    Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                    (pt_read_pte_slot sg _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif)
                    (pt_read_pte_slot sg _ p1 region1 Hsm1 HA Hord HR Hcov Hm1 Hs1 Hhtif)
                    (pt_read_pte_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
                    Hrdx Hmisa Hmenv Hhtif Htlb Hlk HA Hord HW Hcov Hpmaw)
          as (sg' & Htr & _).
        apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
                 vpn root_ppn
                 (autocast (T := mword) ((autocast (T := mword)
                    (PPN_of_PTE (p0 : mword 64))) : mword 44))
                 satp0 va sg mm
                 Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl
                 (ex_intro _ sg' Htr)).
        intros mxr do_sum.
        exact (goodmb_ptree_translate_miss_core root_ppn va w tlbvec p2 p1 a0 d0
                 mxr do_sum sg mm Hchk Hgchk Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hg2 Hg1 Hg0
                 Hsm2' Hsm1 Hsm0 Hown2' Hown1 Hown0
                 Hmisa Hmenv Hhtif Htlb Hlk HA Hord HR HW Hcov Hpmar Hpmaw).
    - (* empty slot: the walk runs *)
      assert (Hlk : exec (lookup_TLB 39 (mword_of_int 0) vpn) sg = Some (None, sg))
        by exact (exec_lookup_TLB_miss vpn (mword_of_int 0) tlbvec sg Htlb Hslot).
      destruct (ptree_translate_miss_core acc pv root_ppn va w tlbvec p2 p1 a0 d0 sg Hchk
                  Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hsm0
                  (pt_read_pte_slot sg _ p2 region2 Hsm2' HA Hord HR Hcov Hm2 Hs2 Hhtif)
                  (pt_read_pte_slot sg _ p1 region1 Hsm1 HA Hord HR Hcov Hm1 Hs1 Hhtif)
                  (pt_read_pte_slot sg _ p0 region0 Hsm0 HA Hord HR Hcov Hm0r Hs0 Hhtif)
                  Hrdx Hmisa Hmenv Hhtif Htlb Hlk HA Hord HW Hcov Hpmaw)
        as (sg' & Htr & _).
      apply (goodmb_translateAddr_pt_front Dr Dw acc pv HDms HDcp HDsatp
               vpn root_ppn
               (autocast (T := mword) ((autocast (T := mword)
                  (PPN_of_PTE (p0 : mword 64))) : mword 44))
               satp0 va sg mm
               Heff Heffg Hss Hssg Hcp Htm Htmg Hsatp Hppn Hasid Hcanon eq_refl
               (ex_intro _ sg' Htr)).
      intros mxr do_sum.
      exact (goodmb_ptree_translate_miss_core root_ppn va w tlbvec p2 p1 a0 d0
               mxr do_sum sg mm Hchk Hgchk Hv2 Hn2 Hv1 Hn1 Hv0 Hl0 Hnap Hg2 Hg1 Hg0
               Hsm2' Hsm1 Hsm0 Hown2' Hown1 Hown0
               Hmisa Hmenv Hhtif Htlb Hlk HA Hord HR HW Hcov Hpmar Hpmaw).
  Qed.

End PtreeTranslateCert.
