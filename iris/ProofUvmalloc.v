(* ProofUvmalloc.v -- uvmalloc() over the SIE-agnostic sconf world.

     uint64 uvmalloc(pagetable_t pagetable, uint64 oldsz, uint64 newsz,
                     int xperm) {
       if (newsz < oldsz) return oldsz;
       oldsz = PGROUNDUP(oldsz);
       for (a = oldsz; a < newsz; a += PGSIZE) {
         mem = kalloc();
         if (mem == 0) { uvmdealloc(pagetable, a, oldsz); return 0; }
         memset(mem, 0, PGSIZE);
         if (mappages(pagetable, a, PGSIZE, (uint64)mem,
                      PTE_R | PTE_U | xperm) != 0) {
           kfree(mem); uvmdealloc(pagetable, a, oldsz); return 0;
         }
       }
       return newsz;
     }

   Spec of record: SpecUvmalloc.v -- stated at the [proc_pt] altitude.

   THREE STRUCTURAL POINTS.

   1. THE FRAMELESS EARLY RETURN.  +0x00 is a 4-byte [bltu] taken BEFORE the
      push, so the [newsz < oldsz] arm at +0xa2 returns with sp untouched and
      never meets the epilogue.

   2. THE SHRINK-WRAPPED FRAME.  Ten slots are pushed at +0x04; ra/s0/s2/s4/s5
      /s7 are stored immediately, s1/s3/s6 only at +0x2a..+0x2e once the loop
      is known to run.  So the epilogue continuation [EPI] (an [iAssert] taken
      before the first branch) OWNS the seven always-live cells and takes the
      three shrink-wrapped ones as an EXISTENTIAL wand argument: the "nothing
      to do" arm hands back the junk the push produced, each long arm the
      values it has just reloaded s1/s3/s6 from.

   3. THE LOOP counts DOWN by one per iteration -- [a] runs from
      PGROUNDUP(oldsz) by PGSIZE while [a < newsz] -- so [ua_loop] is a plain
      induction on the remaining count, no fuel parameter.  Its exits (loop
      finished, kalloc failed, mappages failed) all join at +0x78, which is
      why the loop lemma takes [ua_exit] as a wand argument. *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import PtBuild.
Require Import PtreeType.
Require Import UptTree UserPtTree.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import ByteCursor.
Require Import ProcPt ProcPtOwn.
Require Import UmCovered.
Require Import CodeUvmalloc.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecKalloc SpecMemsetPage SpecMappages SpecKfree SpecUvmdealloc.
Require Import SpecUvmalloc.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* §1  uvmalloc's OWN pure [Z] arithmetic -- the loop-trip characterisation *)
(*     and the vpn/range facts that mention this function's constants.     *)
(*                                                                        *)
(*   Kept STRICTLY [mword]-free: this file's transitive [bitvector.tactics] *)
(*   import installs a zify hook that makes [lia] answer Cannot-find-      *)
(*   witness on any goal mentioning [bv_unsigned] (durable-notes.md).      *)
(*                                                                        *)
(*   The SHARED half lives at its own altitude: the PGROUNDUP / run-length *)
(*   arithmetic and the run vocabulary in ProcPtOwn.v §3d ([z_pgu_*],      *)
(*   [uvm_maxsz_val], [vpn_run_*], [dom_run_*]), the leaf-insert moves in  *)
(*   §2b ([uvm_run1], [uptd_ext_insert_perm]), [uvm_perm_ori18] in §2c,    *)
(*   [aligned_low12] / [pgroundup_id] / [vpn_lt_ne] in §3c-d, the cursor   *)
(*   bump [ByteCursor.bc_add_moi], and [RiscvExtras.or_vec64_unsigned].    *)
(* ===================================================================== *)

(* the run length is 0 exactly on the two arms where the C does nothing *)
Lemma ua_z_np_zero (nz pu : Z) : nz <= pu -> Z.to_nat ((nz - pu + 4095) / 4096) = 0%nat.
Proof.
  intros H.
  assert (H0 : 4095 / 4096 = 0) by (vm_compute; reflexivity).
  assert (Hq : (nz - pu + 4095) / 4096 <= 0).
  { rewrite <- H0. apply Z.div_le_mono; lia. }
  lia.
Qed.

(* [a = pu + 4096*j] is below [nz] exactly for the first [(nz-pu+4095)/4096]
   values of [j] -- the loop-trip characterisation *)
Lemma ua_z_iter (pu nz j : Z) :
  (pu + 4096 * j < nz) <-> (j < (nz - pu + 4095) / 4096).
Proof.
  pose proof (Z_div_mod_eq_full (nz - pu + 4095) 4096) as Heq.
  assert (Hp : 0 < 4096) by lia.
  pose proof (Z.mod_pos_bound (nz - pu + 4095) 4096 Hp) as Hmod.
  split; intros H; lia.
Qed.

Lemma ua_z_nchar (pu nz : Z) (j : nat) :
  0 <= (nz - pu + 4095) / 4096 ->
  ((pu + 4096 * Z.of_nat j < nz) <-> (j < Z.to_nat ((nz - pu + 4095) / 4096))%nat).
Proof. intros Hq. rewrite (ua_z_iter pu nz (Z.of_nat j)). lia. Qed.

Lemma ua_z_np_pos (pu nz : Z) : pu < nz -> 0 <= (nz - pu + 4095) / 4096.
Proof. intros H. apply Z.div_pos; lia. Qed.

(* uvmdealloc's run length between two page-aligned sizes *)
Lemma ua_z_npd (pu k : Z) : (pu + 4096 * k - pu) / 4096 = k.
Proof.
  assert (Hr : pu + 4096 * k - pu = k * 4096) by ring.
  rewrite Hr. apply Z.div_mul. lia.
Qed.

(* mappages' one-page range side conditions *)
Lemma ua_z_run_pa (x : Z) : x < 2281701376 -> x + Z.of_nat 1 * 4096 < 72057594037927936.
Proof. lia. Qed.

(* the vpn of [pu + 4096*k] is the vpn of [pu] plus [k] *)
Lemma ua_z_svpn (pu k : Z) :
  0 <= pu -> 0 <= k -> pu + 4096 * k < 274877906944 ->
  ((pu + 4096 * k) / 4096) mod 134217728 = (pu / 4096) mod 134217728 + k.
Proof.
  intros H0 Hk Hb.
  assert (Hd : (pu + 4096 * k) / 4096 = pu / 4096 + k).
  { assert (Hr : pu + 4096 * k = pu + k * 4096) by ring.
    rewrite Hr. apply Z.div_add. lia. }
  assert (Hpq0 : 0 <= pu / 4096) by (apply Z.div_pos; lia).
  assert (Hsum : pu / 4096 + k < 67108864).
  { rewrite <- Hd. apply Z.div_lt_upper_bound; lia. }
  rewrite Hd. rewrite (Z.mod_small (pu / 4096) 134217728); [| lia].
  apply Z.mod_small. lia.
Qed.

(* the view's PGROUNDUP is the identity on the loop's cursor, which is a
   multiple of 4096 by construction -- so the invariant's live set is
   literally [0, pu + 4096*i). *)
Lemma ua_pgu_exact (pu : Z) (i : nat) :
  pu mod 4096 = 0 -> (0 <= pu)%Z ->
  UserPtTree.pgroundup (pu + 4096 * Z.of_nat i)%Z = (pu + 4096 * Z.of_nat i)%Z.
Proof.
  intros Hmod Hpu0. unfold UserPtTree.pgroundup.
  pose proof (Z.div_mod (pu + 4096 * Z.of_nat i + 4095) 4096 ltac:(lia)) as Hd.
  assert (Hm : ((pu + 4096 * Z.of_nat i + 4095) mod 4096 = 4095)%Z).
  { replace (pu + 4096 * Z.of_nat i + 4095)%Z
      with (pu + 4095 + Z.of_nat i * 4096)%Z by lia.
    rewrite Z_mod_plus_full. rewrite Zplus_mod Hmod.
    change (0 + 4095 mod 4096)%Z with 4095%Z.
    apply Z.mod_small. lia. }
  rewrite Hm in Hd. lia.
Qed.

(* an address inside the run belongs to one of the run's vpns -- the
   converse of [ua_z_svpn], and what says [P] maps nothing the loop has
   grown into (so the rollback really does give [M] back). *)
Lemma ua_vpn_of_addr (pu : Z) (vpn0 v : mword 27) (jj i : nat) :
  pu mod 4096 = 0 -> (0 <= pu)%Z ->
  (bv_unsigned vpn0 * 4096 = pu)%Z ->
  (bv_unsigned vpn0 + Z.of_nat i < 134217728)%Z ->
  (jj < 4096)%nat ->
  (pu <= bv_unsigned v * 4096 + Z.of_nat jj < pu + 4096 * Z.of_nat i)%Z ->
  exists k, (k < i)%nat /\ v = vpn_at vpn0 k.
Proof.
  intros Hmod Hpu0 Hv0 Hbnd Hjj Hin.
  pose proof (bv_unsigned_in_range 27 v) as [Hv0' _].
  assert (Hm : ((bv_unsigned v * 4096 - pu) mod 4096 = 0)%Z).
  { rewrite Zminus_mod Hmod.
    rewrite (Z.mod_mul (bv_unsigned v) 4096 ltac:(lia)). reflexivity. }
  pose proof (Z.div_mod (bv_unsigned v * 4096 - pu) 4096 ltac:(lia)) as Hdm.
  assert (Hlo : (pu <= bv_unsigned v * 4096)%Z) by lia.
  assert (Hhi : (bv_unsigned v * 4096 < pu + 4096 * Z.of_nat i)%Z) by lia.
  set (k := Z.to_nat ((bv_unsigned v * 4096 - pu) / 4096)).
  assert (Hkz : (Z.of_nat k * 4096 = bv_unsigned v * 4096 - pu)%Z).
  { unfold k. rewrite Z2Nat.id; [lia | apply Z.div_pos; lia]. }
  assert (Hklt : (k < i)%nat) by lia.
  exists k. split; [exact Hklt |].
  apply bv_eq. rewrite (vpn_at_unsigned vpn0 k ltac:(lia)). lia.
Qed.

Lemma ua_z_avmod (pu k : Z) : pu mod 4096 = 0 -> (pu + 4096 * k) mod 4096 = 0.
Proof.
  intros H. assert (Hr : (pu + 4096 * k)%Z = (pu + k * 4096)%Z) by ring.
  rewrite Hr. rewrite Z.mod_add; [exact H | lia].
Qed.

Lemma ua_z_vpn0_bnd (pu k : Z) :
  0 <= pu -> 0 <= k -> pu + 4096 * k < 274877906944 ->
  (pu / 4096) mod 134217728 + k < 134217728.
Proof.
  intros H0 Hk Hb.
  assert (Hpq0 : 0 <= pu / 4096) by (apply Z.div_pos; lia).
  assert (Hlt : pu / 4096 + k < 67108864).
  { assert (Hd : (pu + 4096 * k) / 4096 = pu / 4096 + k).
    { assert (Hr : pu + 4096 * k = pu + k * 4096) by ring.
      rewrite Hr. apply Z.div_add. lia. }
    rewrite <- Hd. apply Z.div_lt_upper_bound; lia. }
  rewrite (Z.mod_small (pu / 4096) 134217728); lia.
Qed.

(* AN ALIGNED CURSOR BELOW THE REGION HAS A WHOLE PAGE OF ROOM.  With the
   size premise relaxed to [<= uvm_maxsz] this replaces what [lia] used to
   get for free: [pu + 4096*i] is page-aligned and strictly below [nz], and
   both [nz] and TRAPFRAME are too, so the cursor is a full page below it. *)
Lemma ua_z_avfit (x nz : Z) :
  x mod 4096 = 0 -> x < nz -> nz <= 274877898752 -> x + 4096 <= 274877898752.
Proof.
  intros Hm Hx Hnz.
  pose proof (Z_div_mod_eq_full x 4096) as Hd.
  assert (Hq : x = 4096 * (x / 4096)) by lia.
  assert (Hlt : 4096 * (x / 4096) < 4096 * 67108862) by lia.
  assert (Hql : x / 4096 < 67108862) by nia.
  lia.
Qed.

(* a page below TRAPFRAME has a vpn strictly below [tf_vpn] = 2^26 - 2 *)
Lemma ua_z_vpn_lt (x : Z) :
  0 <= x -> x + 4096 <= 274877898752 -> (x / 4096) mod 134217728 < 67108862.
Proof.
  intros H0 Hb.
  assert (Hq : 0 <= x / 4096 < 134217728)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (x / 4096) 134217728); [| lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

(* ===================================================================== *)
(* §2  The postcondition payload and the +0x78 join contract.             *)
(* ===================================================================== *)

Local Notation URra := (mword_of_int 1 : mword 5).
Local Notation URtp := (mword_of_int 4 : mword 5).
Local Notation URs0 := (mword_of_int 8 : mword 5).
Local Notation URs1 := (mword_of_int 9 : mword 5).
Local Notation URa0 := (mword_of_int 10 : mword 5).
Local Notation URa1 := (mword_of_int 11 : mword 5).
Local Notation URa2 := (mword_of_int 12 : mword 5).
Local Notation URa3 := (mword_of_int 13 : mword 5).
Local Notation URa4 := (mword_of_int 14 : mword 5).
Local Notation URa5 := (mword_of_int 15 : mword 5).
Local Notation URs2 := (mword_of_int 18 : mword 5).
Local Notation URs3 := (mword_of_int 19 : mword 5).
Local Notation URs4 := (mword_of_int 20 : mword 5).
Local Notation URs5 := (mword_of_int 21 : mword 5).
Local Notation URs6 := (mword_of_int 22 : mword 5).
Local Notation URs7 := (mword_of_int 23 : mword 5).

Section UvmallocDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* SpecUvmalloc's post disjunction, at an abstract return value *)
  Definition ua_pay (P : uptd) (M : gmap Z (bv 8))
      (vpn0 : mword 27) (n : nat) (xperm : Z)
      (oldsz newsz res : mword 64) : iProp Σ :=
    ((⌜res = (mword_of_int 0 : mword 64)⌝ ∗ proc_ptm P (uint oldsz) M)
     ∨ (∃ P' : uptd,
          ⌜uptd_ext P P'⌝ ∗
          ⌜dom P'.(ud_um) = dom P.(ud_um) ∪ vpn_run vpn0 n⌝ ∗
          (* WHAT THE NEW LEAVES ARE.  The domain alone is not enough for a
             caller that then EDITS one of them: exec's uvmclear on the stack
             guard page needs that leaf's FLAG BYTE, and nothing else in the
             tier can supply it.  mappages builds every page of the run as
             [uvm_pte (xperm|18) r] with no A/D bit set, so saying so costs
             the loop one invariant conjunct and closes the gap. *)
          ⌜forall v : mword 27, v ∈ vpn_run vpn0 n ->
             ∃ r : mword 64,
               P'.(ud_um) !! v = Some (uvm_pte (Z.lor xperm 18) r)⌝ ∗
          ⌜ ((uint newsz < uint oldsz)%Z /\ res = oldsz)
            \/ ((uint oldsz <= uint newsz)%Z /\ res = newsz) ⌝ ∗
          proc_ptm P' (uint res) (umem_grow M (uint res))))%I.

  (* what every long arm hands the epilogue at +0x78.  EXPLICIT-CPUID: this
     is a DECOMPOSED helper in the sense of the porting guide -- different
     callers (the loop's back-edge exit, the two short-circuit returns) reach
     +0x78 at different harts, so [ua_exit] carries its own fresh [CID0]
     binder and wraps its whole body in [wp_next], exactly like [frepi] in
     ProofFreerange. *)
  Definition ua_exit `{GEN : GenId} `{CID0 : CpuId} (mm : regfile)
      (P : uptd) (M : gmap Z (bv 8))
      (vpn0 : mword 27) (n : nat) (xperm : Z) (K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) (sp0 spr oldsz newsz : mword 64) : iProp Σ :=
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ∀ (mj : regfile) (res : mword 64),
      ⌜ mj !!! Regidx csp_rs1 = spr
        /\ mj !!! Regidx URa0 = res
        /\ (forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> URs0 -> c <> URs2 -> c <> URs4 ->
              c <> URs5 -> c <> URs7 ->
              mj !!! Regidx c = mm !!! Regidx c) ⌝ -∗
      sie_cap_gpr KT1 mj (K - 10)%nat b p -∗
      cpu_own 0%nat eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.uvmalloc + 0x78) : mword 64) -∗
      (∃ w1 w3 w6 : mword 64,
         pa_stk sp0 3 ↦₈[KT1] w1 ∗ pa_stk sp0 5 ↦₈[KT1] w3 ∗ pa_stk sp0 8 ↦₈[KT1] w6) -∗
      ua_pay P M vpn0 n xperm oldsz newsz res -∗
      WP (Loop : expr riscv_lang) )%I.

End UvmallocDefs.

(* ===================================================================== *)
(* §3  THE WHOLE FUNCTION.                                                *)
(* ===================================================================== *)

Module UvmallocProof (Kalloc : KALLOC) (MemsetPage : MEMSETPAGE)
                     (Mappages : MAPPAGES) (Kfree : KFREE)
                     (Uvmdealloc : UVMDEALLOC)
  : UVMALLOC.

Section ProofUvmalloc.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  Notation Rra := URra.
  Notation Rtp := URtp.
  Notation Rs0 := URs0.
  Notation Rs1 := URs1.
  Notation Ra0 := URa0.
  Notation Ra1 := URa1.
  Notation Ra2 := URa2.
  Notation Ra3 := URa3.
  Notation Ra4 := URa4.
  Notation Ra5 := URa5.
  Notation Rs2 := URs2.
  Notation Rs3 := URs3.
  Notation Rs4 := URs4.
  Notation Rs5 := URs5.
  Notation Rs6 := URs6.
  Notation Rs7 := URs7.

  Ltac reg_neq :=
    lazymatch goal with
    | |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate)
    end.

  (* peel via the upd_eq/upd_ne LEMMAS, one layer at a time (values stay
     opaque): optimization.md's [peel_reg]. *)
  Ltac peel_reg_step :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  (* the callee-saved-agreement peel: every layer of the chain writes either a
     caller-saved register (killed by [is_cs_idx]) or one the caller has
     excluded by hypothesis (killed by [congruence] against [c <> Rsk]). *)
  Ltac ua_thr_ne :=
    first
      [ lazymatch goal with
        | Hcs : is_cs_idx _ = true |- _ =>
            refine (not_eq_sym (is_cs_idx_true_neq _ _ _ Hcs));
            vm_compute; reflexivity
        end
      | intros Hx; injection Hx as Hx2; subst;
        lazymatch goal with H : ?a <> ?a |- _ => exact (H eq_refl) end ].

  Ltac ua_thr_peel :=
    repeat first
      [ rewrite upd_ne; [| ua_thr_ne]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  (* ------------------------------------------------------------------ *)
  (* THE ROLLBACK, as a pure [proc_pt] move: uvmdealloc deleted exactly   *)
  (* the run the loop had added, and the run was fresh in [P] to begin    *)
  (* with, so what comes back IS [P] -- not a weaker descriptor.          *)
  (* ------------------------------------------------------------------ *)
  Local Lemma ua_restore (P Pi : uptd) (vpn0 : mword 27) (i : nat) :
    uptd_ext P Pi ->
    dom Pi.(ud_um) = dom P.(ud_um) ∪ vpn_run vpn0 i ->
    (forall j : nat, (j < i)%nat -> P.(ud_um) !! vpn_at vpn0 j = None) ->
    proc_pt (uptd_del_run Pi vpn0 i) ⊢ proc_pt P.
  Proof.
    intros (Hr & Ht & Hsub) Hdom Hfr.
    assert (Hum : um_del_run Pi.(ud_um) vpn0 i = P.(ud_um))
      by exact (um_del_run_restore P.(ud_um) Pi.(ud_um) vpn0 i Hsub Hdom Hfr).
    assert (Heq : proc_pt (uptd_del_run Pi vpn0 i) ⊣⊢ proc_pt P).
    { apply proc_pt_data_irrel; unfold uptd_del_run;
        cbn [ud_root ud_tfp ud_um]; assumption. }
    rewrite Heq. reflexivity.
  Qed.

  (* ...and at the contents-indexed altitude, where the SIZE also has to
     come back: uvmdealloc leaves the process at PGROUNDUP(oldsz), which
     has the same live set as [oldsz] itself. *)
  Local Lemma ua_restore_mem (P Pi : uptd) (vpn0 : mword 27) (i : nat)
      (sz sz' : Z) (Mv : gmap Z (bv 8)) :
    uptd_ext P Pi ->
    dom Pi.(ud_um) = dom P.(ud_um) ∪ vpn_run vpn0 i ->
    (forall j : nat, (j < i)%nat -> P.(ud_um) !! vpn_at vpn0 j = None) ->
    (forall a : Z, uva_live sz a <-> uva_live sz' a) ->
    proc_ptm (uptd_del_run Pi vpn0 i) sz Mv ⊢ proc_ptm P sz' Mv.
  Proof.
    intros (Hr & Ht & Hsub) Hdom Hfr Hlv.
    assert (Hum : um_del_run Pi.(ud_um) vpn0 i = P.(ud_um))
      by exact (um_del_run_restore P.(ud_um) Pi.(ud_um) vpn0 i Hsub Hdom Hfr).
    rewrite (proc_ptm_data_irrel (uptd_del_run Pi vpn0 i) P sz Mv
               ltac:(unfold uptd_del_run; cbn [ud_root]; assumption)
               ltac:(unfold uptd_del_run; cbn [ud_tfp]; assumption)
               ltac:(unfold uptd_del_run; cbn [ud_um]; assumption)).
    rewrite (proc_ptm_sz_cong P sz sz' Mv Hlv). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE LOOP, at its head +0x36, with [i] iterations already done.       *)
  (* ------------------------------------------------------------------ *)
  Local Lemma ua_loop (γa : gname) (mm : regfile)
      (P : uptd) (Mv : gmap Z (bv 8)) (xperm : Z) (K : nat) (eb : bool)
      (p : mword 64)
      (sp0 spr oldsz newsz : mword 64) (pu nz : Z) (n : nat) (b : bool) (lks : gset string) :
    (42 <= K)%nat ->
    (0 <= xperm < 512)%Z ->
    uvm_perm_ok (Z.lor xperm 18) ->
    add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
      = pa_stk sp0 3 ->
    add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
      = pa_stk sp0 5 ->
    add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
      = pa_stk sp0 8 ->
    bv_unsigned (pgroundup oldsz) = pu ->
    bv_unsigned newsz = nz ->
    (pu mod 4096 = 0)%Z ->
    (0 <= pu)%Z ->
    (* THE ADDRESS BOUND, per iteration.  It used to be [nz <= uvm_maxsz]
       -- one bound on the argument, uniform in [j].  It is a PREMISE ABOUT
       THE DESCRIPTOR REACHED instead, because kexec's [newsz] comes out of a
       file and cannot be bounded: what bounds [a] there
       is that every page below it is already MAPPED, and physical memory is
       finite ([UmCovered.uvma_addr_bound]).  The caller proves this from
       whichever disjunct of the contract's premise it holds. *)
    (forall (Pj : uptd) (j : nat), proc_pt_wf Pj -> (j < n)%nat ->
       dom Pj.(ud_um) = dom P.(ud_um) ∪ vpn_run (svpn_of (pgroundup oldsz)) j ->
       (pu + 4096 * Z.of_nat j + 4096 <= 274877898752)%Z) ->
    (uint oldsz <= uint newsz)%Z ->
    (* THE VIEW WE WERE HANDED, as a pure fact: its domain law.  It is what
       pins the rollback -- the range the loop grows into is exactly the
       range [Mv] does not already record, so deleting it gives [Mv] back. *)
    (forall x : Z, is_Some (Mv !! x)
       <-> (uva_mapped P x \/ uva_live (uint oldsz) x)) ->
    (UserPtTree.pgroundup (uint oldsz) = pu)%Z ->
    (forall j : nat, (pu + 4096 * Z.of_nat j < nz)%Z <-> (j < n)%nat) ->
    (* GUARDED, exactly as the contract states it: freshness is needed at
       the iterations the loop REACHES, and [Habi] below is the bound at
       each of them.  See SpecUvmalloc.v's note. *)
    (forall j : nat, (j < n)%nat ->
       (pu + 4096 * Z.of_nat j + 4096 <= 274877898752)%Z ->
       P.(ud_um) !! vpn_at (svpn_of (pgroundup oldsz)) j = None) ->
    (* every iteration's kalloc/kfree is balanced against "kmem" (13); the
       loop's own body touches nothing lower.  One premise for the whole
       cone, fixed across every iteration since [lks] never changes. *)
    locks_below lks "kmem" ->
    forall (rem i : nat) `(CID0 : CpuId) (Pi : uptd) (M : regfile) (av : mword 64),
    (i + rem = n)%nat -> (1 <= rem)%nat ->
    bv_unsigned av = (pu + 4096 * Z.of_nat i)%Z ->
    uptd_ext P Pi ->
    dom Pi.(ud_um) = dom P.(ud_um) ∪ vpn_run (svpn_of (pgroundup oldsz)) i ->
    (* the run mapped SO FAR is at the permission the caller asked for --
       the invariant half of [ua_pay]'s new leaf conjunct *)
    (forall v : mword 27,
       v ∈ vpn_run (svpn_of (pgroundup oldsz)) i ->
       ∃ r : mword 64,
         Pi.(ud_um) !! v = Some (uvm_pte (Z.lor xperm 18) r)) ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx Rs2 = av ->
    M !!! Regidx Rs3 = (mword_of_int 4096 : mword 64) ->
    M !!! Regidx Rs4 = newsz ->
    M !!! Regidx Rs5 = page_base P.(ud_root) ->
    M !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64) ->
    M !!! Regidx Rs7 = pgroundup oldsz ->
    (forall c : mword 5, is_cs_idx c = true ->
       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
       c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
       M !!! Regidx c = mm !!! Regidx c) ->
    sie_cap_gpr KT1 (CID:=CID0) M (K - 10)%nat b p -∗
    cpu_own (CID:=CID0) 0%nat eb p b lks -∗
    kernel_text -∗
    pc_is (CID:=CID0) (mword_of_int (KernelSyms.uvmalloc + 0x36) : mword 64) -∗
    proc_ptm Pi (pu + 4096 * Z.of_nat i)%Z
      (umem_grow Mv (pu + 4096 * Z.of_nat i)%Z) -∗
    kalloc_env γa None -∗
    pa_stk sp0 3 ↦₈[KT1] (mm !!! Regidx Rs1) -∗
    pa_stk sp0 5 ↦₈[KT1] (mm !!! Regidx Rs3) -∗
    pa_stk sp0 8 ↦₈[KT1] (mm !!! Regidx Rs6) -∗
    ua_exit (CID0 := CID0) mm P Mv (svpn_of (pgroundup oldsz)) n xperm K eb p b lks sp0 spr oldsz newsz -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hxrng Hperm Hb3 Hb5 Hb8 Hpu Hnz Hpumod Hpu0 Hab Hoin
           HMdom Hpgo Hnchar Hfresh Hbelow.
    assert (HKka : (14 <= K - 10)%nat) by (clear -HK; lia).
    assert (HKms : (2 <= K - 10)%nat) by (clear -HK; lia).
    assert (HKmp : (32 <= K - 10)%nat) by (clear -HK; lia).
    assert (HKud : (26 <= K - 10)%nat) by (clear -HK; lia).
    intro rem.
    induction rem as [| rem IH];
      intros i CID0 Pi M av Hsum Hrem Hav Hext Hdom Hleaf Hsp Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hthr;
      [ exfalso; clear -Hrem; lia |].
    iIntros "Hcg Hcnt #Htext Hpc Hpt #Henv Hk3 Hk5 Hk8 Hexit".
    iDestruct "Henv" as (γk) "(#Hlock & #Havail)".
    (* mappages names the free-list pair now ([KvmSpec.kalloc_env_at]); this
       caller is at [None] and needs no PARTICULAR name, only one, which its
       own bundle supplies.  Both forms are kept: the callees stated at the
       bundle (uvmdealloc, kfree) still take that one. *)
    iAssert (kalloc_env γa None) as "#Henv".
    { iExists γk. iSplitR; [iExact "Hlock" |]. iExact "Havail". }
    iAssert (kalloc_env_at γa γk None) as "#Henvn".
    { iApply (kalloc_env_at_intro with "Hlock Havail"). }
    (* ---- the arithmetic of THIS iteration, all up front ---- *)
    assert (Hin : (i < n)%nat) by (clear -Hsum Hrem; lia).
    pose proof (proj2 (Hnchar i) Hin) as Hain.
    (* the well-formedness of the CURRENT descriptor -- what [Hab] reads.
       [iDestruct … as %_] on a PURE conclusion does not spend the resource,
       so no keep-the-hypothesis accessor is needed. *)
    iDestruct (proc_ptm_wf Pi (pu + 4096 * Z.of_nat i)%Z
                 (umem_grow Mv (pu + 4096 * Z.of_nat i)%Z) with "Hpt") as %Hwfi.
    pose proof (Hab Pi i Hwfi Hin Hdom) as Habi.
    assert (Hbnd38 : (pu + 4096 * Z.of_nat i < 274877906944)%Z)
      by (clear -Habi; lia).
    assert (Havmod : (bv_unsigned av mod 4096 = 0)%Z)
      by (rewrite Hav; exact (ua_z_avmod pu (Z.of_nat i) Hpumod)).
    assert (Havb : (bv_unsigned av + 4096 <= 274877898752)%Z)
      by (rewrite Hav; clear -Habi; lia).
    assert (Hpgav : pgroundup av = av).
    { apply pgroundup_id; [exact Havmod |].
      rewrite Hav. change (2 ^ 64)%Z with 18446744073709551616%Z.
      clear -Habi. lia. }
    assert (Hpgpu : pgroundup (pgroundup oldsz) = pgroundup oldsz).
    { apply pgroundup_id; [rewrite Hpu; exact Hpumod |].
      rewrite Hpu. change (2 ^ 64)%Z with 18446744073709551616%Z.
      clear -Habi. lia. }
    (* [uvmd_np]'s guard splits here: on the FIRST iteration the rollback
       range is empty and the guard closes it; from the second on it is the
       ordinary quotient. *)
    assert (Hnpd : uvmd_np av (pgroundup oldsz) = i).
    { unfold uvmd_np. rewrite Hav Hpu.
      destruct i as [| i'].
      - rewrite bool_decide_eq_false_2; [reflexivity | lia].
      - rewrite bool_decide_eq_true_2; [| lia].
        rewrite Hpgav Hpgpu Hav Hpu. rewrite ua_z_npd. apply Nat2Z.id. }
    assert (Hvb : (bv_unsigned (svpn_of (pgroundup oldsz)) + Z.of_nat i < 134217728)%Z).
    { rewrite svpn_of_unsigned_gen Hpu.
      exact (ua_z_vpn0_bnd pu (Z.of_nat i) Hpu0 (Nat2Z.is_nonneg i) Hbnd38). }
    (* ---- THE ROLLBACK, as a fact about the view ---- *)
    assert (Havu : (uint av = pu + 4096 * Z.of_nat i)%Z)
      by (rewrite uint_unsigned; exact Hav).
    assert (Hnotin : forall x : Z, is_Some (Mv !! x) ->
              ~ (pu <= x < pu + 4096 * Z.of_nat i)%Z).
    { intros x Hs Hrng. destruct (proj1 (HMdom x) Hs) as [Hmap | Hlv].
      - destruct Hmap as (v0 & w0 & j0 & Hl0 & Hj0 & ->).
        destruct (ua_vpn_of_addr pu (svpn_of (pgroundup oldsz)) v0 j0 i
                    Hpumod Hpu0
                    ltac:(rewrite svpn_of_unsigned_gen Hpu;
                          rewrite (Z.mod_small (pu / 4096) 134217728
                            ltac:(split;
                              [apply Z.div_pos; clear -Hpu0; lia
                              | apply Z.div_lt_upper_bound;
                                [lia | clear -Hbnd38 Hpu0; lia]]));
                          pose proof (Z.div_mod pu 4096 ltac:(lia)) as Hdd;
                          rewrite Hpumod in Hdd; clear -Hdd; lia)
                    ltac:(clear -Hvb; lia) Hj0 Hrng)
          as (k & Hk & ->).
        rewrite (Hfresh k ltac:(clear -Hk Hin; lia)
                   ltac:(clear -Habi Hk; lia)) in Hl0. discriminate.
      - rewrite /uva_live Hpgo in Hlv. clear -Hlv Hrng. lia. }
    assert (Hrszd : uvmd_rsz av (pgroundup oldsz) = pgroundup oldsz).
    { unfold uvmd_rsz.
      destruct (bool_decide (bv_unsigned (pgroundup oldsz)
                             < bv_unsigned av)%Z) eqn:Hbd; [reflexivity |].
      apply bool_decide_eq_false in Hbd.
      rewrite Hav Hpu in Hbd. apply bv_eq. rewrite Hav Hpu.
      clear -Hbd. lia. }
    assert (Hlvsame : forall a : Z,
              uva_live (uint (pgroundup oldsz)) a <-> uva_live (uint oldsz) a).
    { intros a. rewrite /uva_live Hpgo.
      rewrite (uint_unsigned (pgroundup oldsz)).
      rewrite (pgroundup_live (pgroundup oldsz)
                 ltac:(rewrite Hpu; change (2 ^ 64)%Z with 18446744073709551616%Z;
                       clear -Habi Hpu0; lia)).
      rewrite Hpgpu. rewrite Hpu. reflexivity. }
    assert (Hgrowdel : umem_del (umem_grow Mv (uint av))
                         (uint (pgroundup oldsz)) (4096 * i)%nat = Mv).
    { rewrite (uint_unsigned (pgroundup oldsz)). rewrite Hpu.
      apply (umem_grow_del Mv (uint oldsz) (uint av) pu (4096 * i)%nat).
      - intros x Hlv. apply HMdom. by right.
      - intros x Hs Hrng. apply (Hnotin x Hs).
        clear -Hrng. rewrite Nat2Z.inj_mul in Hrng. lia.
      - intros x. rewrite /uva_live Hpgo Havu (ua_pgu_exact pu i Hpumod Hpu0).
        rewrite Nat2Z.inj_mul. clear -Hpu0. lia. }
    assert (Hvpn : svpn_of av = vpn_at (svpn_of (pgroundup oldsz)) i).
    { apply bv_eq. rewrite (vpn_at_unsigned _ i Hvb).
      rewrite !svpn_of_unsigned_gen. rewrite Hav Hpu.
      exact (ua_z_svpn pu (Z.of_nat i) Hpu0 (Nat2Z.is_nonneg i) Hbnd38). }
    assert (Hvpnb : (bv_unsigned (svpn_of av) < 67108862)%Z).
    { rewrite svpn_of_unsigned_gen. apply ua_z_vpn_lt.
      - rewrite Hav. clear -Hain Hpu0. lia.
      - clear -Havb Hav. lia. }
    assert (Hvpnb26 : (bv_unsigned (svpn_of av) < 67108864)%Z).
    { assert (Hx : (67108862 < 67108864)%Z) by lia.
      exact (Z.lt_trans _ _ _ Hvpnb Hx). }
    assert (Hfreshi : forall j : nat, (j < i)%nat ->
              P.(ud_um) !! vpn_at (svpn_of (pgroundup oldsz)) j = None).
    { intros j Hj. apply Hfresh; [clear -Hj Hin; lia | clear -Habi Hj; lia]. }
    (* uvmdealloc's ONE range premise, about its [oldsz] argument (= av);
       it asks nothing about the [newsz] it is handed. *)
    assert (Hudold : (uint av <= uvm_maxsz)%Z).
    { rewrite uint_unsigned uvm_maxsz_val. clear -Havb. lia. }
    assert (Hrooti : Pi.(ud_root) = P.(ud_root)) by exact (proj1 Hext).
    (* ---- +0x36 jal ra,kalloc ---- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x36)) Rra
              (mword_of_int 2095146 : mword 21) M (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (uai_36 with "Htext"). }
    iIntros (CIDu1 Hsu1) "Hcg Hpc".
    iDestruct (cpu_own_transport CID0 CIDu1 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    set (B1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x36) : mword 64) 4)]> M).
    assert (Htgtka : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x36) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095146 : mword 21))
                     = mword_of_int KernelSyms.kalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtka) in "Hpc".
    assert (HB1ra : B1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x36) : mword 64) 4)
      by (rewrite /B1 upd_eq; reflexivity).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = spr)
      by (rewrite /B1; rewrite upd_ne; [exact Hsp | reg_neq]).
    assert (HB1s2 : B1 !!! Regidx Rs2 = av)
      by (rewrite /B1; rewrite upd_ne; [exact Hs2 | reg_neq]).
    assert (HB1s3 : B1 !!! Regidx Rs3 = (mword_of_int 4096 : mword 64))
      by (rewrite /B1; rewrite upd_ne; [exact Hs3 | reg_neq]).
    assert (HB1s4 : B1 !!! Regidx Rs4 = newsz)
      by (rewrite /B1; rewrite upd_ne; [exact Hs4 | reg_neq]).
    assert (HB1s5 : B1 !!! Regidx Rs5 = page_base P.(ud_root))
      by (rewrite /B1; rewrite upd_ne; [exact Hs5 | reg_neq]).
    assert (HB1s6 : B1 !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64))
      by (rewrite /B1; rewrite upd_ne; [exact Hs6 | reg_neq]).
    assert (HB1s7 : B1 !!! Regidx Rs7 = pgroundup oldsz)
      by (rewrite /B1; rewrite upd_ne; [exact Hs7 | reg_neq]).
    assert (HB1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              B1 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite /B1. rewrite upd_ne; [| ua_thr_ne]. apply Hthr; assumption. }
    iApply (Kalloc.wp_kalloc_sconf KT1 γa γk (mword_of_int (KernelSyms.kmem + 24))
              B1 None 0%nat eb p (K - 10)%nat b
              _ HKka ltac:(reflexivity) ltac:(vm_compute; reflexivity)
              Hbelow
              with "Hcg Hcnt Htext Hpc Hlock Havail").
    all: try lkbelow.
    iIntros (CIDu2 Hsu2 mk) "Hcg Hcnt Hpc %Hkcs Hkpost".
    assert (Hret3a : ret_pc (B1 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmalloc + 0x3a)).
    { rewrite HB1ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret3a) in "Hpc".
    assert (Hmksp : mk !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HB1sp. }
    assert (Hmks2 : mk !!! Regidx Rs2 = av).
    { rewrite (callee_saved_lookup Hkcs Rs2 ltac:(vm_compute; reflexivity)). exact HB1s2. }
    assert (Hmks3 : mk !!! Regidx Rs3 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hkcs Rs3 ltac:(vm_compute; reflexivity)). exact HB1s3. }
    assert (Hmks4 : mk !!! Regidx Rs4 = newsz).
    { rewrite (callee_saved_lookup Hkcs Rs4 ltac:(vm_compute; reflexivity)). exact HB1s4. }
    assert (Hmks5 : mk !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hkcs Rs5 ltac:(vm_compute; reflexivity)). exact HB1s5. }
    assert (Hmks6 : mk !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64)).
    { rewrite (callee_saved_lookup Hkcs Rs6 ltac:(vm_compute; reflexivity)). exact HB1s6. }
    assert (Hmks7 : mk !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite (callee_saved_lookup Hkcs Rs7 ltac:(vm_compute; reflexivity)). exact HB1s7. }
    assert (Hmkthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              mk !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hkcs c Hc). apply HB1thr; assumption. }
    (* ---- +0x3a c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x3a)) Rs1 Ra0 mk (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_3a with "Htext"). }
    iIntros (CIDu3 Hsu3) "Hcg Hpc".
    set (B2 := <[Regidx Rs1 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Ra0))]> mk).
    assert (HB2a0 : B2 !!! Regidx Ra0 = mk !!! Regidx Ra0)
      by (rewrite /B2; rewrite upd_ne; [reflexivity | reg_neq]).
    assert (HB2s1 : B2 !!! Regidx Rs1 = mk !!! Regidx Ra0)
      by (rewrite /B2 upd_eq; apply add_vec_zero_l).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spr)
      by (rewrite /B2; rewrite upd_ne; [exact Hmksp | reg_neq]).
    assert (HB2s2 : B2 !!! Regidx Rs2 = av)
      by (rewrite /B2; rewrite upd_ne; [exact Hmks2 | reg_neq]).
    assert (HB2s3 : B2 !!! Regidx Rs3 = (mword_of_int 4096 : mword 64))
      by (rewrite /B2; rewrite upd_ne; [exact Hmks3 | reg_neq]).
    assert (HB2s4 : B2 !!! Regidx Rs4 = newsz)
      by (rewrite /B2; rewrite upd_ne; [exact Hmks4 | reg_neq]).
    assert (HB2s5 : B2 !!! Regidx Rs5 = page_base P.(ud_root))
      by (rewrite /B2; rewrite upd_ne; [exact Hmks5 | reg_neq]).
    assert (HB2s6 : B2 !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64))
      by (rewrite /B2; rewrite upd_ne; [exact Hmks6 | reg_neq]).
    assert (HB2s7 : B2 !!! Regidx Rs7 = pgroundup oldsz)
      by (rewrite /B2; rewrite upd_ne; [exact Hmks7 | reg_neq]).
    assert (HB2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              B2 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite /B2. rewrite upd_ne; [| ua_thr_ne]. apply Hmkthr; assumption. }
    assert (Hp3c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x3a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x3c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3c) in "Hpc".
    iDestruct "Hkpost" as "[(%Hnull & _ & _) | (%Hpv & Hpage & _)]".
    { (* ================= kalloc failed: roll back, return 0 ============ *)
      assert (Htgt66 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x3c) : mword 64)
                (sign_extend' 64
                   (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.uvmalloc + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
      assert (Hzt : eq_vec (B2 !!! Regidx Ra0) zero_reg = true)
        by (rewrite HB2a0 Hnull; vm_compute; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x3c))
                (mword_of_int 21 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                B2 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hzt)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (uai_3c with "Htext"). }
      iApply bi.later_intro. iIntros (CIDu4 Hsu4) "Hcg Hpc".
      iEval (rewrite Htgt66) in "Hpc".
      (* +0x66 c.mv a2,s7 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x66)) Ra2 Rs7 B2 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (uai_66 with "Htext"). }
      iIntros (CIDu5 Hsu5) "Hcg Hpc".
      set (N1 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (B2 !!! Regidx Rs7))]> B2).
      assert (Hq68 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x66) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq68) in "Hpc".
      (* +0x68 c.mv a1,s2 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x68)) Ra1 Rs2 N1 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (uai_68 with "Htext"). }
      iIntros (CIDu6 Hsu6) "Hcg Hpc".
      set (N2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (N1 !!! Regidx Rs2))]> N1).
      assert (Hq6a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x68) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x6a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq6a) in "Hpc".
      (* +0x6a c.mv a0,s5 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x6a)) Ra0 Rs5 N2 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (uai_6a with "Htext"). }
      iIntros (CIDu7 Hsu7) "Hcg Hpc".
      set (N3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (N2 !!! Regidx Rs5))]> N2).
      assert (Hq6c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x6a) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq6c) in "Hpc".
      (* +0x6c jal ra,uvmdealloc *)
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x6c)) Rra
                (mword_of_int 2096976 : mword 21) N3 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (uai_6c with "Htext"). }
      iIntros (CIDu8 Hsu8) "Hcg Hpc".
      iDestruct (cpu_own_transport CIDu2 CIDu8 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      set (N4 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x6c) : mword 64) 4)]> N3).
      assert (Htgtud : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x6c) : mword 64)
                         (sign_extend' 64 (mword_of_int 2096976 : mword 21))
                       = mword_of_int KernelSyms.uvmdealloc)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtud) in "Hpc".
      assert (HN4ra : N4 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x6c) : mword 64) 4)
        by (rewrite /N4 upd_eq; reflexivity).
      assert (HN4a0 : N4 !!! Regidx Ra0 = page_base Pi.(ud_root)).
      { rewrite Hrooti. rewrite /N4. rewrite upd_ne; [| reg_neq].
        rewrite /N3 upd_eq. rewrite add_vec_zero_l.
        rewrite /N2. rewrite upd_ne; [| reg_neq].
        rewrite /N1. rewrite upd_ne; [| reg_neq]. exact HB2s5. }
      assert (HN4a1 : N4 !!! Regidx Ra1 = av).
      { rewrite /N4. rewrite upd_ne; [| reg_neq].
        rewrite /N3. rewrite upd_ne; [| reg_neq].
        rewrite /N2 upd_eq. rewrite add_vec_zero_l.
        rewrite /N1. rewrite upd_ne; [| reg_neq]. exact HB2s2. }
      assert (HN4a2 : N4 !!! Regidx Ra2 = pgroundup oldsz).
      { rewrite /N4. rewrite upd_ne; [| reg_neq].
        rewrite /N3. rewrite upd_ne; [| reg_neq].
        rewrite /N2. rewrite upd_ne; [| reg_neq].
        rewrite /N1 upd_eq. rewrite add_vec_zero_l. exact HB2s7. }
      assert (HN4sp : N4 !!! Regidx csp_rs1 = spr).
      { rewrite /N4 /N3 /N2 /N1. repeat (rewrite upd_ne; [| reg_neq]). exact HB2sp. }
      assert (HN4thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
                N4 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
        ua_thr_peel. apply Hmkthr; assumption. }
      (* EXPLICIT-CPUID: [SpecUvmdealloc.v]'s entry-side tp premise is gone
         (HartTp.v -- the map's tp slot is IGNORED, the true tp is
         [cid_word_of <the hart we are on>] by construction), so [N4] is
         handed to [Uvmdealloc] as-is; no [tp_pin] re-tagging needed. *)
      assert (Hudo : (uint (N4 !!! Regidx Ra1) <= uvm_maxsz)%Z)
        by (rewrite HN4a1; exact Hudold).
      iEval (rewrite <- Havu) in "Hpt".
      iEval (rewrite <- HN4a1) in "Hpt".
      iApply (Uvmdealloc.wp_uvmdealloc_mem_sconf γa N4 Pi
                (umem_grow Mv (uint (N4 !!! Regidx Ra1))) (K - 10)%nat eb p b
                _ HKud HN4a0 Hudo
                with "Hcg Hcnt Htext Hpc Hpt Henv").
      all: try lkbelow.
      iIntros (CIDu9 Hsu9 md) "Hcg Hcnt Hpc %Hdcs _ Hpt".
      iEval (rewrite HN4a1 HN4a2 Hpgpu Hnpd Hrszd Hgrowdel) in "Hpt".
      assert (Hret70 : ret_pc (N4 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmalloc + 0x70)).
      { rewrite HN4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hret70) in "Hpc".
      assert (Hmdsp : md !!! Regidx csp_rs1 = spr).
      { rewrite (callee_saved_lookup Hdcs csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HN4sp. }
      assert (Hmdthr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
                md !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
        rewrite (callee_saved_lookup Hdcs c Hc).
        apply HN4thr; assumption. }
      (* +0x70 c.li a0,0 *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x70)) Ra0 (mword_of_int 0 : mword 6)
                (mword_of_int 0 : mword 64) md (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (uai_70 with "Htext"). }
      iIntros (CIDu10 Hsu10) "Hcg Hpc".
      set (N5 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> md).
      assert (HN5sp : N5 !!! Regidx csp_rs1 = spr)
        by (rewrite /N5; rewrite upd_ne; [exact Hmdsp | reg_neq]).
      assert (Hq72 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x70) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq72) in "Hpc".
      (* +0x72 c.ldsp s1,56(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x72)) (mword_of_int 7 : mword 6) Rs1
                N5 (K - 10)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk3]").
      { iApply (uai_72 with "Htext"). }
      { iEval (rewrite HN5sp Hb3). iExact "Hk3". }
      iIntros (CIDu11 Hsu11) "Hcg Hpc Hk3". iEval (rewrite HN5sp Hb3) in "Hk3".
      set (N6 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> N5).
      assert (HN6sp : N6 !!! Regidx csp_rs1 = spr)
        by (rewrite /N6; rewrite upd_ne; [exact HN5sp | reg_neq]).
      assert (Hq74 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x72) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq74) in "Hpc".
      (* +0x74 c.ldsp s3,40(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x74)) (mword_of_int 5 : mword 6) Rs3
                N6 (K - 10)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk5]").
      { iApply (uai_74 with "Htext"). }
      { iEval (rewrite HN6sp Hb5). iExact "Hk5". }
      iIntros (CIDu12 Hsu12) "Hcg Hpc Hk5". iEval (rewrite HN6sp Hb5) in "Hk5".
      set (N7 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> N6).
      assert (HN7sp : N7 !!! Regidx csp_rs1 = spr)
        by (rewrite /N7; rewrite upd_ne; [exact HN6sp | reg_neq]).
      assert (Hq76 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x74) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq76) in "Hpc".
      (* +0x76 c.ldsp s6,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x76)) (mword_of_int 2 : mword 6) Rs6
                N7 (K - 10)%nat (mm !!! Regidx Rs6) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk8]").
      { iApply (uai_76 with "Htext"). }
      { iEval (rewrite HN7sp Hb8). iExact "Hk8". }
      iIntros (CIDu13 Hsu13) "Hcg Hpc Hk8". iEval (rewrite HN7sp Hb8) in "Hk8".
      set (N8 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> N7).
      assert (Hq78 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x76) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq78) in "Hpc".
      iDestruct (ua_restore_mem P Pi (svpn_of (pgroundup oldsz)) i
                   (uint (pgroundup oldsz)) (uint oldsz) Mv
                   Hext Hdom Hfreshi Hlvsame
                   with "Hpt") as "Hpt".
      iEval (rewrite /ua_exit) in "Hexit".
      iSpecialize ("Hexit" $! CIDu13 with "[%]"); [wp_next_chain|].
      iDestruct (cpu_own_transport CIDu9 CIDu13 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("Hexit" $! N8 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk5 Hk8] [Hpt]").
      { split_and!.
        - rewrite /N8. rewrite upd_ne; [exact HN7sp | reg_neq].
        - rewrite /N8 /N7 /N6. repeat (rewrite upd_ne; [| reg_neq]).
          rewrite /N5 upd_eq. reflexivity.
        - intros c Hc H2 H8 H18 H20 H21 H23.
          destruct (decide (c = Rs1)) as [->|H9].
          { rewrite /N8. rewrite upd_ne; [| reg_neq].
            rewrite /N7. rewrite upd_ne; [| reg_neq]. rewrite /N6 upd_eq. reflexivity. }
          destruct (decide (c = Rs3)) as [->|H19].
          { rewrite /N8. rewrite upd_ne; [| reg_neq]. rewrite /N7 upd_eq. reflexivity. }
          destruct (decide (c = Rs6)) as [->|H22].
          { rewrite /N8 upd_eq. reflexivity. }
          ua_thr_peel. apply Hmdthr; assumption. }
      { iExists _, _, _. iSplitL "Hk3"; [iExact "Hk3"|]. iSplitL "Hk5"; [iExact "Hk5"|]. iExact "Hk8". }
      { rewrite /ua_pay. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. } }
    (* ================= kalloc returned a page r ======================= *)
    set (r := (mk !!! Regidx Ra0 : mword 64)).
    pose proof Hpv as Hpvd. destruct Hpvd as [Hral Hrrng].
    unfold page_in_range, kmem_lo, kmem_hi in Hrrng.
    assert (Hnzr : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hilt : (Z.of_nat i < 134217728)%Z) by (clear -Hbnd38 Hpu0; lia).
    assert (Hnn : eq_vec (B2 !!! Regidx Ra0) zero_reg = false).
    { rewrite HB2a0. apply eq_vec_false_iff. rewrite Hnzr.
      exact (page_valid_ne_null _ Hpv). }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x3c))
              (mword_of_int 21 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              B2 (K - 10)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) ltac:(rgne; exact Hnn) with "Hcg Hpc []").
    { iApply (uai_3c with "Htext"). }
    iIntros (CIDu14 Hsu14) "Hcg Hpc".
    assert (Hq3e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x3c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq3e) in "Hpc".
    (* +0x3e c.mv a2,s3 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x3e)) Ra2 Rs3 B2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_3e with "Htext"). }
    iIntros (CIDu15 Hsu15) "Hcg Hpc".
    set (B3 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (B2 !!! Regidx Rs3))]> B2).
    assert (Hq40 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x3e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq40) in "Hpc".
    (* +0x40 c.li a1,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x40)) Ra1 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) B3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (uai_40 with "Htext"). }
    iIntros (CIDu16 Hsu16) "Hcg Hpc".
    set (B4 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> B3).
    assert (Hq42 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x40) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x42)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq42) in "Hpc".
    (* +0x42 jal ra,memset *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x42)) Rra
              (mword_of_int 2095544 : mword 21) B4 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (uai_42 with "Htext"). }
    iIntros (CIDu17 Hsu17) "Hcg Hpc".
    set (B5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x42) : mword 64) 4)]> B4).
    assert (Htgtms : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x42) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095544 : mword 21))
                     = mword_of_int KernelSyms.memset)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtms) in "Hpc".
    assert (HB5ra : B5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x42) : mword 64) 4)
      by (rewrite /B5 upd_eq; reflexivity).
    assert (HB5a0 : B5 !!! Regidx Ra0 = r).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2a0. }
    assert (HB5a1 : B5 !!! Regidx Ra1 = (mword_of_int 0 : mword 64)).
    { rewrite /B5. rewrite upd_ne; [| reg_neq]. rewrite /B4 upd_eq. reflexivity. }
    assert (HB5a2 : B5 !!! Regidx Ra2 = (mword_of_int 4096 : mword 64)).
    { rewrite /B5. rewrite upd_ne; [| reg_neq].
      rewrite /B4. rewrite upd_ne; [| reg_neq].
      rewrite /B3 upd_eq. rewrite add_vec_zero_l. exact HB2s3. }
    assert (HB5sp : B5 !!! Regidx csp_rs1 = spr).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2sp. }
    assert (HB5s1 : B5 !!! Regidx Rs1 = r).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2s1. }
    assert (HB5s2 : B5 !!! Regidx Rs2 = av).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2s2. }
    assert (HB5s3 : B5 !!! Regidx Rs3 = (mword_of_int 4096 : mword 64)).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2s3. }
    assert (HB5s4 : B5 !!! Regidx Rs4 = newsz).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2s4. }
    assert (HB5s5 : B5 !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2s5. }
    assert (HB5s6 : B5 !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64)).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2s6. }
    assert (HB5s7 : B5 !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite /B5 /B4 /B3. repeat (rewrite upd_ne; [| reg_neq]). exact HB2s7. }
    assert (HB5thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              B5 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      ua_thr_peel. apply Hmkthr; assumption. }
    assert (Hmspv : page_valid (B5 !!! Regidx Ra0)) by (rewrite HB5a0; exact Hpv).
    iApply (MemsetPage.wp_memset_page_val_sconf KT1 B5 (K - 10)%nat
              (mword_of_int 0 : mword 64) b p
              HKms Hmspv HB5a1 HB5a2 with "Hcg Htext Hpc [Hpage]").
    { iEval (rewrite HB5a0). iExact "Hpage". }
    iIntros (CIDu18 Hsu18 ms) "Hcg Hpc Hpage %Hmscs".
    (* the page really READS AS ZERO now -- what the lazily-backed vas at
       these addresses already claimed, and what makes the view's growth
       honest rather than vacuous *)
    assert (Hcb : nth_byte (autocast (T := mword)
                    (subrange_vec_dec (mword_of_int 0 : mword 64)
                       (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 = bv_0 8)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hcb) in "Hpage".
    (* [MemsetPage] doesn't thread [cpu_own] at all (SpecMemsetPage.v), so
       ["Hcnt"] rides through the call framed but stranded at [CIDu2]; bring
       it up to date here before it is needed again (at Mappages). *)
    iDestruct (cpu_own_transport CIDu2 CIDu18 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iEval (rewrite HB5a0) in "Hpage".
    assert (Hret46 : ret_pc (B5 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmalloc + 0x46)).
    { rewrite HB5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret46) in "Hpc".
    assert (Hmssp : ms !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hmscs csp_rs1 ltac:(vm_compute; reflexivity)). exact HB5sp. }
    assert (Hmss1 : ms !!! Regidx Rs1 = r).
    { rewrite (callee_saved_lookup Hmscs Rs1 ltac:(vm_compute; reflexivity)). exact HB5s1. }
    assert (Hmss2 : ms !!! Regidx Rs2 = av).
    { rewrite (callee_saved_lookup Hmscs Rs2 ltac:(vm_compute; reflexivity)). exact HB5s2. }
    assert (Hmss3 : ms !!! Regidx Rs3 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hmscs Rs3 ltac:(vm_compute; reflexivity)). exact HB5s3. }
    assert (Hmss4 : ms !!! Regidx Rs4 = newsz).
    { rewrite (callee_saved_lookup Hmscs Rs4 ltac:(vm_compute; reflexivity)). exact HB5s4. }
    assert (Hmss5 : ms !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hmscs Rs5 ltac:(vm_compute; reflexivity)). exact HB5s5. }
    assert (Hmss6 : ms !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64)).
    { rewrite (callee_saved_lookup Hmscs Rs6 ltac:(vm_compute; reflexivity)). exact HB5s6. }
    assert (Hmss7 : ms !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite (callee_saved_lookup Hmscs Rs7 ltac:(vm_compute; reflexivity)). exact HB5s7. }
    assert (Hmsthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              ms !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hmscs c Hc). apply HB5thr; assumption. }
    (* +0x46 c.mv a4,s6 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x46)) Ra4 Rs6 ms (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_46 with "Htext"). }
    iIntros (CIDu19 Hsu19) "Hcg Hpc".
    set (B6 := <[Regidx Ra4 := regval_into_reg (add_vec zero_reg (ms !!! Regidx Rs6))]> ms).
    assert (Hq48 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x46) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq48) in "Hpc".
    (* +0x48 c.mv a3,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x48)) Ra3 Rs1 B6 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_48 with "Htext"). }
    iIntros (CIDu20 Hsu20) "Hcg Hpc".
    set (B7 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (B6 !!! Regidx Rs1))]> B6).
    assert (Hq4a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x48) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x4a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq4a) in "Hpc".
    (* +0x4a c.mv a2,s3 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x4a)) Ra2 Rs3 B7 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_4a with "Htext"). }
    iIntros (CIDu21 Hsu21) "Hcg Hpc".
    set (B8 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (B7 !!! Regidx Rs3))]> B7).
    assert (Hq4c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x4a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq4c) in "Hpc".
    (* +0x4c c.mv a1,s2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x4c)) Ra1 Rs2 B8 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_4c with "Htext"). }
    iIntros (CIDu22 Hsu22) "Hcg Hpc".
    set (B9 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (B8 !!! Regidx Rs2))]> B8).
    assert (Hq4e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x4c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq4e) in "Hpc".
    (* +0x4e c.mv a0,s5 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x4e)) Ra0 Rs5 B9 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_4e with "Htext"). }
    iIntros (CIDu23 Hsu23) "Hcg Hpc".
    set (B10 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B9 !!! Regidx Rs5))]> B9).
    assert (Hq50 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x4e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq50) in "Hpc".
    (* +0x50 jal ra,mappages *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x50)) Rra
              (mword_of_int 2096404 : mword 21) B10 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (uai_50 with "Htext"). }
    iIntros (CIDu24 Hsu24) "Hcg Hpc".
    iDestruct (cpu_own_transport CIDu18 CIDu24 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    set (B11 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x50) : mword 64) 4)]> B10).
    assert (Htgtmp : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x50) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096404 : mword 21))
                     = mword_of_int KernelSyms.mappages)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtmp) in "Hpc".
    assert (HB11ra : B11 !!! Regidx Rra
                     = add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x50) : mword 64) 4)
      by (rewrite /B11 upd_eq; reflexivity).
    assert (HB11a0 : B11 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /B11. rewrite upd_ne; [| reg_neq].
      rewrite /B10 upd_eq. rewrite add_vec_zero_l.
      rewrite /B9 /B8 /B7 /B6. repeat (rewrite upd_ne; [| reg_neq]). exact Hmss5. }
    assert (HB11a1 : B11 !!! Regidx Ra1 = av).
    { rewrite /B11. rewrite upd_ne; [| reg_neq].
      rewrite /B10. rewrite upd_ne; [| reg_neq].
      rewrite /B9 upd_eq. rewrite add_vec_zero_l.
      rewrite /B8 /B7 /B6. repeat (rewrite upd_ne; [| reg_neq]). exact Hmss2. }
    assert (HB11a2 : B11 !!! Regidx Ra2 = (mword_of_int 4096 : mword 64)).
    { rewrite /B11. rewrite upd_ne; [| reg_neq].
      rewrite /B10. rewrite upd_ne; [| reg_neq].
      rewrite /B9. rewrite upd_ne; [| reg_neq].
      rewrite /B8 upd_eq. rewrite add_vec_zero_l.
      rewrite /B7 /B6. repeat (rewrite upd_ne; [| reg_neq]). exact Hmss3. }
    assert (HB11a3 : B11 !!! Regidx Ra3 = r).
    { rewrite /B11. rewrite upd_ne; [| reg_neq].
      rewrite /B10. rewrite upd_ne; [| reg_neq].
      rewrite /B9. rewrite upd_ne; [| reg_neq].
      rewrite /B8. rewrite upd_ne; [| reg_neq].
      rewrite /B7 upd_eq. rewrite add_vec_zero_l.
      rewrite /B6. rewrite upd_ne; [| reg_neq]. exact Hmss1. }
    assert (HB11a4 : B11 !!! Regidx Ra4 = (mword_of_int (Z.lor xperm 18) : mword 64)).
    { rewrite /B11. rewrite upd_ne; [| reg_neq].
      rewrite /B10. rewrite upd_ne; [| reg_neq].
      rewrite /B9. rewrite upd_ne; [| reg_neq].
      rewrite /B8. rewrite upd_ne; [| reg_neq].
      rewrite /B7. rewrite upd_ne; [| reg_neq].
      rewrite /B6 upd_eq. rewrite add_vec_zero_l. exact Hmss6. }
    assert (HB11sp : B11 !!! Regidx csp_rs1 = spr).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmssp. }
    assert (HB11s1 : B11 !!! Regidx Rs1 = r).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmss1. }
    assert (HB11s2 : B11 !!! Regidx Rs2 = av).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmss2. }
    assert (HB11s3 : B11 !!! Regidx Rs3 = (mword_of_int 4096 : mword 64)).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmss3. }
    assert (HB11s4 : B11 !!! Regidx Rs4 = newsz).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmss4. }
    assert (HB11s5 : B11 !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmss5. }
    assert (HB11s6 : B11 !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64)).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmss6. }
    assert (HB11s7 : B11 !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite /B11 /B10 /B9 /B8 /B7 /B6.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hmss7. }
    assert (HB11thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              B11 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      ua_thr_peel. apply Hmsthr; assumption. }
    (* ---- open the table into the exact represented view ---- *)
    iDestruct (proc_ptm_acc_rep0 Pi (pu + 4096 * Z.of_nat i)%Z
                 (umem_grow Mv (pu + 4096 * Z.of_nat i)%Z) with "Hpt") as
      (t m_ad) "(%Hrep & %Hview & %Hbase & %Hwf & Hptree & Hown)".
    assert (Humnone : Pi.(ud_um) !! svpn_of av = None).
    { rewrite Hvpn. apply not_elem_of_dom. rewrite Hdom. intros Hin2.
      apply elem_of_union in Hin2. destruct Hin2 as [Hin2 | Hin2].
      - assert (Hnd2 : vpn_at (svpn_of (pgroundup oldsz)) i ∉ dom P.(ud_um))
          by (apply not_elem_of_dom;
              exact (Hfresh i Hin ltac:(clear -Habi; lia))).
        exact (Hnd2 Hin2).
      - apply elem_of_vpn_run in Hin2. destruct Hin2 as (j & Hj & Hje).
        exact (vpn_at_ne (svpn_of (pgroundup oldsz)) j i Hj Hilt (eq_sym Hje)). }
    assert (Hmadnone : m_ad !! svpn_of av = None).
    { apply (proj1 Hview (svpn_of av)). split_and!.
      - apply vpn_lt_ne. rewrite tramp_vpn_unsigned.
        assert (Hx1 : (67108862 < 67108863)%Z) by lia.
        exact (Z.lt_trans _ _ _ Hvpnb Hx1).
      - apply vpn_lt_ne. rewrite tf_vpn_unsigned. exact Hvpnb.
      - exact Humnone. }
    assert (HB11root : B11 !!! Regidx Ra0
                       = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))).
    { rewrite HB11a0 Hbase Hrooti. reflexivity. }
    assert (Hmpva : subrange_vec_dec (B11 !!! Regidx Ra1) 11 0 = (zeros' 12 : mword 12))
      by (rewrite HB11a1; exact (aligned_low12 av Havmod)).
    assert (Hmppa : subrange_vec_dec (B11 !!! Regidx Ra3) 11 0 = (zeros' 12 : mword 12)).
    { rewrite HB11a3. apply aligned_low12. rewrite <- uint_unsigned.
      unfold page_aligned, PGSIZE in Hral. exact Hral. }
    assert (Hmpsz : B11 !!! Regidx Ra2 = mword_of_int (Z.of_nat 1 * 4096))
      by (rewrite HB11a2; apply bv_eq; vm_compute; reflexivity).
    assert (Hmpvab : (uint (B11 !!! Regidx Ra1) + Z.of_nat 1 * 4096 <= 2 ^ 38)%Z).
    { rewrite HB11a1 uint_unsigned. change (2 ^ 38)%Z with 274877906944%Z.
      clear -Havb. lia. }
    assert (Hmppab : (uint (B11 !!! Regidx Ra3) + Z.of_nat 1 * 4096 < 2 ^ 56)%Z).
    { rewrite HB11a3. change (2 ^ 56)%Z with 72057594037927936%Z.
      exact (ua_z_run_pa _ (proj2 Hrrng)). }
    assert (Hmpfresh : forall j : nat, (j < 1)%nat ->
              m_ad !! vpn_at (svpn_of (B11 !!! Regidx Ra1)) j = None).
    { intros j Hj. assert (Hj0 : j = 0%nat) by (clear -Hj; lia). subst j.
      rewrite vpn_at_0 HB11a1. exact Hmadnone. }
    iApply (Mappages.wp_mappages_sconf KT1 γa γk B11 t m_ad 1%nat (Z.lor xperm 18) 0%nat
              (K - 10)%nat eb p None b _
              ltac:(reflexivity) HKmp HB11root Hmpva Hmppa Hmpsz ltac:(clear; lia)
              HB11a4 (proj1 Hperm) Hmpvab Hmppab Hrep Hmpfresh
              with "Hcg Hcnt Htext Hpc Hptree Henvn").
    all: try lkbelow.
    iIntros (CIDu25 Hsu25 mg t' k g) "Hcg Hcnt Hpc Hptree %Hnodes _ %Hgcs %Hbase' %Hrep' %Hmono %Hmiss %Hmpay".
    rewrite HB11a1 in Hrep'. rewrite HB11a3 in Hrep'.
    assert (Hret54 : ret_pc (B11 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmalloc + 0x54)).
    { rewrite HB11ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret54) in "Hpc".
    assert (Hbase'' : pt_base t' = Pi.(ud_root)) by (rewrite Hbase'; exact Hbase).
    assert (Hmgsp : mg !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hgcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HB11sp. }
    assert (Hmgs1 : mg !!! Regidx Rs1 = r).
    { rewrite (callee_saved_lookup Hgcs Rs1 ltac:(vm_compute; reflexivity)). exact HB11s1. }
    assert (Hmgs2 : mg !!! Regidx Rs2 = av).
    { rewrite (callee_saved_lookup Hgcs Rs2 ltac:(vm_compute; reflexivity)). exact HB11s2. }
    assert (Hmgs3 : mg !!! Regidx Rs3 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hgcs Rs3 ltac:(vm_compute; reflexivity)). exact HB11s3. }
    assert (Hmgs4 : mg !!! Regidx Rs4 = newsz).
    { rewrite (callee_saved_lookup Hgcs Rs4 ltac:(vm_compute; reflexivity)). exact HB11s4. }
    assert (Hmgs5 : mg !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hgcs Rs5 ltac:(vm_compute; reflexivity)). exact HB11s5. }
    assert (Hmgs6 : mg !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64)).
    { rewrite (callee_saved_lookup Hgcs Rs6 ltac:(vm_compute; reflexivity)). exact HB11s6. }
    assert (Hmgs7 : mg !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite (callee_saved_lookup Hgcs Rs7 ltac:(vm_compute; reflexivity)). exact HB11s7. }
    assert (Hmgthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              mg !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hgcs c Hc). apply HB11thr; assumption. }
    destruct Hmpay as [(Hk1 & Hga0) | (Hklt & Hga0 & _)].
    { (* =========== mappages SUCCEEDED: one more page mapped =========== *)
      subst k. rewrite uvm_run1 in Hrep'.
      iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
      iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
        "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb & _)".
      assert (Hvpnu : (bv_unsigned (svpn_of av) * 4096 = bv_unsigned av)%Z).
      { rewrite (svpn_of_unsigned_lo av
                   ltac:(rewrite uint_unsigned; clear -Hbnd38 Hav; lia)).
        rewrite uint_unsigned. rewrite Z.shiftr_div_pow2; [| lia].
        change (2 ^ 12)%Z with 4096%Z.
        pose proof (Z.div_mod (bv_unsigned av) 4096 ltac:(lia)) as Hdm.
        rewrite Havmod in Hdm. lia. }
      (* THE VIEW GROWS BY EXACTLY THIS PAGE.  [av] is page-aligned and
         [svpn_of av] is its vpn, so the vas that become live going from
         [av] to [av + 4096] are precisely that page's. *)
      assert (Hlvstep : forall x : Z,
                uva_live (pu + 4096 * Z.of_nat (S i))%Z x
                <-> (uva_live (pu + 4096 * Z.of_nat i)%Z x
                     \/ x ∈ upage_dom (svpn_of av))).
      { intros x. rewrite upage_dom_range. rewrite /uva_live.
        rewrite (ua_pgu_exact pu i Hpumod Hpu0).
        rewrite (ua_pgu_exact pu (S i) Hpumod Hpu0).
        rewrite Hvpnu Hav. rewrite Nat2Z.inj_succ. lia. }
      iDestruct (proc_ptm_grow_uvm Pi (Z.lor xperm 18)
                   (pu + 4096 * Z.of_nat i)%Z
                   (pu + 4096 * Z.of_nat (S i))%Z
                   (umem_grow Mv (pu + 4096 * Z.of_nat i)%Z)
                   (svpn_of av) r t' m_ad
                   (fun _ => bv_0 8)
                   Hperm Hwf Hview Hmadnone Hvpnb26 Hrep' Hbase'' Hpv
                   Hlvstep ltac:(intros jj Hjj; reflexivity)
                   with "Hkmapb Hptree Hpage Hown") as "Hpt".
      iEval (rewrite <- (umem_grow_step Mv (pu + 4096 * Z.of_nat i)%Z
                           (pu + 4096 * Z.of_nat (S i))%Z
                           (upage_dom (svpn_of av)) Hlvstep)) in "Hpt".
      set (Pj := uptd_insert_perm Pi (Z.lor xperm 18) (svpn_of av) r).
      assert (Hextj : uptd_ext P Pj)
        by (exact (uptd_ext_trans P Pi Pj Hext
                     (uptd_ext_insert_perm Pi (Z.lor xperm 18) (svpn_of av) r Humnone))).
      assert (Hdomj : dom Pj.(ud_um)
                      = dom P.(ud_um) ∪ vpn_run (svpn_of (pgroundup oldsz)) (S i)).
      { rewrite /Pj /uptd_insert_perm. cbn [ud_um].
        rewrite dom_insert_L Hdom Hvpn vpn_run_S. apply dom_run_step. }
      assert (Hleafj : forall v : mword 27,
                v ∈ vpn_run (svpn_of (pgroundup oldsz)) (S i) ->
                ∃ r0 : mword 64,
                  Pj.(ud_um) !! v = Some (uvm_pte (Z.lor xperm 18) r0)).
      { intros v Hv. rewrite /Pj /uptd_insert_perm. cbn [ud_um].
        destruct (decide (v = svpn_of av)) as [-> | Hvne].
        - exists r. apply lookup_insert.
        - rewrite lookup_insert_ne; [| exact (not_eq_sym Hvne)].
          apply Hleaf. rewrite vpn_run_S in Hv.
          apply elem_of_union in Hv as [Hv | Hv]; [exact Hv |].
          exfalso. apply elem_of_singleton in Hv. rewrite <- Hvpn in Hv.
          exact (Hvne Hv). }
      (* +0x54 c.bnez a0 FALLS (a0 = 0) *)
      assert (Hbnf : neq_vec (mg !!! Regidx Ra0) zero_reg = false)
        by (rewrite Hga0; vm_compute; reflexivity).
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x54))
                (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mg (K - 10)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) ltac:(rgne; exact Hbnf) with "Hcg Hpc []").
      { iApply (uai_54 with "Htext"). }
      iIntros (CIDu26 Hsu26) "Hcg Hpc".
      assert (Hq56 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x54) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq56) in "Hpc".
      (* +0x56 c.add s2,s2,s3  --  a += PGSIZE *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x56)) Rs2 Rs3 mg (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (uai_56 with "Htext"). }
      iIntros (CIDu27 Hsu27) "Hcg Hpc".
      set (B12 := <[Regidx Rs2 := regval_into_reg
                     (add_vec (mg !!! Regidx Rs2) (mg !!! Regidx Rs3))]> mg).
      assert (Hav0b : (0 <= pu + 4096 * Z.of_nat i)%Z) by (clear -Hpu0; lia).
      assert (Hav1b : (pu + 4096 * Z.of_nat i + 4096 < 18446744073709551616)%Z)
        by (clear -Habi; lia).
      assert (Havs : bv_unsigned (add_vec av (mword_of_int 4096))
                     = (pu + 4096 * Z.of_nat (S i))%Z).
      { rewrite (bc_add_moi av (pu + 4096 * Z.of_nat i) 4096 Hav Hav0b
                            ltac:(vm_compute; discriminate) Hav1b).
        rewrite Nat2Z.inj_succ. unfold Z.succ. ring. }
      assert (HB12s2 : B12 !!! Regidx Rs2 = add_vec av (mword_of_int 4096)).
      { rewrite /B12 upd_eq. rewrite Hmgs2 Hmgs3. reflexivity. }
      assert (HB12sp : B12 !!! Regidx csp_rs1 = spr)
        by (rewrite /B12; rewrite upd_ne; [exact Hmgsp | reg_neq]).
      assert (HB12s3 : B12 !!! Regidx Rs3 = (mword_of_int 4096 : mword 64))
        by (rewrite /B12; rewrite upd_ne; [exact Hmgs3 | reg_neq]).
      assert (HB12s4 : B12 !!! Regidx Rs4 = newsz)
        by (rewrite /B12; rewrite upd_ne; [exact Hmgs4 | reg_neq]).
      assert (HB12s5 : B12 !!! Regidx Rs5 = page_base P.(ud_root))
        by (rewrite /B12; rewrite upd_ne; [exact Hmgs5 | reg_neq]).
      assert (HB12s6 : B12 !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64))
        by (rewrite /B12; rewrite upd_ne; [exact Hmgs6 | reg_neq]).
      assert (HB12s7 : B12 !!! Regidx Rs7 = pgroundup oldsz)
        by (rewrite /B12; rewrite upd_ne; [exact Hmgs7 | reg_neq]).
      assert (HB12thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
                B12 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
        rewrite /B12. rewrite upd_ne; [| ua_thr_ne]. apply Hmgthr; assumption. }
      assert (Hq58 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x56) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq58) in "Hpc".
      (* +0x58 bltu s2,s4 : the back edge *)
      destruct (zopz0zI_u (B12 !!! Regidx Rs2) (B12 !!! Regidx Rs4)) eqn:Hbk.
      { (* another iteration *)
        assert (Hnext : (S i < n)%nat).
        { assert (Hb := Hbk). rewrite HB12s2 HB12s4 in Hb. unfold zopz0zI_u in Hb.
          apply Z.ltb_lt in Hb. rewrite !uint_unsigned Havs Hnz in Hb.
          exact (proj1 (Hnchar (S i)) Hb). }
        assert (Hsum' : (S i + rem = n)%nat) by (clear -Hsum; lia).
        assert (Hrem' : (1 <= rem)%nat) by (clear -Hsum Hnext; lia).
        assert (Htgt36 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x58) : mword 64)
                  (sign_extend' 64 (mword_of_int 8158 : mword 13))
                = mword_of_int (KernelSyms.uvmalloc + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
        iApply (wp_bltu_taken_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x58))
                  (mword_of_int 8158 : mword 13) Rs4 Rs2 B12 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hbk)
                  ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
        { iApply (uai_58 with "Htext"). }
        iApply bi.later_intro. iIntros (CIDu28 Hsu28) "Hcg Hpc".
        iEval (rewrite Htgt36) in "Hpc".
        (* re-anchor ["Hexit"] from this iteration's entry [CID0] to the next
           iteration's entry [CIDu28], and transport ["Hcnt"] there too (its
           last known-good anchor was [CIDu25], Mappages' own return hart). *)
        assert (Hshiftrec : b = false \/ p = zero_reg -> (CIDu28 : CPU) = (CID0 : CPU)) by wp_next_chain.
        assert (Hexit_shift1 :
                  ⊢ (ua_exit (CID0 := CID0) mm P Mv (svpn_of (pgroundup oldsz)) n xperm K eb p b lks sp0 spr oldsz newsz -∗
                     ua_exit (CID0 := CIDu28) mm P Mv (svpn_of (pgroundup oldsz)) n xperm K eb p b lks sp0 spr oldsz newsz)).
        { rewrite /ua_exit. exact (wp_next_shift Hshiftrec). }
        iDestruct (Hexit_shift1 with "Hexit") as "Hexit".
        iDestruct (cpu_own_transport CIDu25 CIDu28 0%nat eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        iApply (IH (S i) CIDu28 Pj B12 (add_vec av (mword_of_int 4096)) Hsum' Hrem' Havs
                  Hextj Hdomj Hleafj HB12sp HB12s2 HB12s3 HB12s4 HB12s5 HB12s6 HB12s7
                  HB12thr with "Hcg Hcnt Htext Hpc Hpt Henv Hk3 Hk5 Hk8 Hexit"). }
      (* the loop is done: return newsz *)
      assert (Hlast : (S i = n)%nat).
      { assert (Hb := Hbk). rewrite HB12s2 HB12s4 in Hb. unfold zopz0zI_u in Hb.
        apply Z.ltb_ge in Hb. rewrite !uint_unsigned Havs Hnz in Hb.
        assert (Hnn2 : ~ (S i < n)%nat).
        { intro Hx. exact (Z.lt_irrefl _ (Z.lt_le_trans _ _ _ (proj2 (Hnchar (S i)) Hx) Hb)). }
        clear -Hsum Hnn2. lia. }
      iApply (wp_bltu_fall_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x58))
                (mword_of_int 8158 : mword 13) Rs4 Rs2 B12 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hbk)
                with "Hcg Hpc []").
      { iApply (uai_58 with "Htext"). }
      iIntros (CIDu29 Hsu29) "Hcg Hpc".
      assert (Hq5c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x58) : mword 64) 4
                     = mword_of_int (KernelSyms.uvmalloc + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq5c) in "Hpc".
      (* +0x5c c.mv a0,s4 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x5c)) Ra0 Rs4 B12 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (uai_5c with "Htext"). }
      iIntros (CIDu30 Hsu30) "Hcg Hpc".
      set (X1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (B12 !!! Regidx Rs4))]> B12).
      assert (HX1sp : X1 !!! Regidx csp_rs1 = spr)
        by (rewrite /X1; rewrite upd_ne; [exact HB12sp | reg_neq]).
      assert (Hq5e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x5c) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq5e) in "Hpc".
      (* +0x5e c.ldsp s1,56(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x5e)) (mword_of_int 7 : mword 6) Rs1
                X1 (K - 10)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk3]").
      { iApply (uai_5e with "Htext"). }
      { iEval (rewrite HX1sp Hb3). iExact "Hk3". }
      iIntros (CIDu31 Hsu31) "Hcg Hpc Hk3". iEval (rewrite HX1sp Hb3) in "Hk3".
      set (X2 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> X1).
      assert (HX2sp : X2 !!! Regidx csp_rs1 = spr)
        by (rewrite /X2; rewrite upd_ne; [exact HX1sp | reg_neq]).
      assert (Hq60 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x5e) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq60) in "Hpc".
      (* +0x60 c.ldsp s3,40(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x60)) (mword_of_int 5 : mword 6) Rs3
                X2 (K - 10)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk5]").
      { iApply (uai_60 with "Htext"). }
      { iEval (rewrite HX2sp Hb5). iExact "Hk5". }
      iIntros (CIDu32 Hsu32) "Hcg Hpc Hk5". iEval (rewrite HX2sp Hb5) in "Hk5".
      set (X3 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> X2).
      assert (HX3sp : X3 !!! Regidx csp_rs1 = spr)
        by (rewrite /X3; rewrite upd_ne; [exact HX2sp | reg_neq]).
      assert (Hq62 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x60) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq62) in "Hpc".
      (* +0x62 c.ldsp s6,16(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x62)) (mword_of_int 2 : mword 6) Rs6
                X3 (K - 10)%nat (mm !!! Regidx Rs6) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk8]").
      { iApply (uai_62 with "Htext"). }
      { iEval (rewrite HX3sp Hb8). iExact "Hk8". }
      iIntros (CIDu33 Hsu33) "Hcg Hpc Hk8". iEval (rewrite HX3sp Hb8) in "Hk8".
      set (X4 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> X3).
      assert (Hq64 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x62) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq64) in "Hpc".
      (* +0x64 c.j +0x14 *)
      assert (Hjt64 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x64) : mword 64)
                (sign_extend' 64
                   (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0"))))
              = mword_of_int (KernelSyms.uvmalloc + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x64))
                (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0")))
                X4 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (uai_64 with "Htext"). }
      iIntros (CIDu34 Hsu34). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Hjt64) in "Hpc".
      iEval (rewrite /ua_exit) in "Hexit".
      iSpecialize ("Hexit" $! CIDu34 with "[%]"); [wp_next_chain|].
      iDestruct (cpu_own_transport CIDu25 CIDu34 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("Hexit" $! X4 newsz with "[%] Hcg Hcnt Hpc [Hk3 Hk5 Hk8] [Hpt]").
      { split_and!.
        - rewrite /X4. rewrite upd_ne; [| reg_neq].
          rewrite /X3. rewrite upd_ne; [exact HX2sp | reg_neq].
        - rewrite /X4 /X3 /X2. repeat (rewrite upd_ne; [| reg_neq]).
          rewrite /X1 upd_eq. rewrite add_vec_zero_l. exact HB12s4.
        - intros c Hc H2 H8 H18 H20 H21 H23.
          destruct (decide (c = Rs1)) as [->|H9].
          { rewrite /X4. rewrite upd_ne; [| reg_neq].
            rewrite /X3. rewrite upd_ne; [| reg_neq]. rewrite /X2 upd_eq. reflexivity. }
          destruct (decide (c = Rs3)) as [->|H19].
          { rewrite /X4. rewrite upd_ne; [| reg_neq]. rewrite /X3 upd_eq. reflexivity. }
          destruct (decide (c = Rs6)) as [->|H22].
          { rewrite /X4 upd_eq. reflexivity. }
          ua_thr_peel. apply Hmgthr; assumption. }
      { iExists _, _, _. iSplitL "Hk3"; [iExact "Hk3"|]. iSplitL "Hk5"; [iExact "Hk5"|]. iExact "Hk8". }
      { rewrite /ua_pay. iRight. iExists Pj.
        iSplitR; [iPureIntro; exact Hextj |].
        iSplitR; [iPureIntro; rewrite <- Hlast; exact Hdomj |].
        iSplitR; [iPureIntro; rewrite <- Hlast; exact Hleafj |].
        iSplitR; [iPureIntro; right; split; [exact Hoin | reflexivity] |].
        (* THE LOOP ENDED AT PGROUNDUP(newsz): the cursor is a multiple of
           4096 that the exit test just failed on, so it IS the view's
           rounded size, and the invariant's live set is the final one. *)
        assert (Hlvend : forall a : Z,
                  uva_live (pu + 4096 * Z.of_nat (S i))%Z a
                  <-> uva_live (uint newsz) a).
        { intros a. rewrite /uva_live (ua_pgu_exact pu (S i) Hpumod Hpu0).
          rewrite uint_unsigned. rewrite Hnz.
          assert (Hpe : (UserPtTree.pgroundup nz
                         = pu + 4096 * Z.of_nat (S i))%Z).
          { unfold UserPtTree.pgroundup.
            pose proof (proj2 (Hnchar i) Hin) as Hlo.
            assert (Hhi : (nz <= pu + 4096 * Z.of_nat (S i))%Z).
            { destruct (Z_le_gt_dec nz (pu + 4096 * Z.of_nat (S i))%Z)
                as [Hle | Hgt]; [exact Hle |].
              exfalso.
              assert (Hc : (S i < n)%nat)
                by (apply Hnchar; clear -Hgt; lia).
              clear -Hc Hlast. lia. }
            pose proof (Z.div_mod (nz + 4095) 4096 ltac:(lia)) as Hd.
            pose proof (Z.mod_pos_bound (nz + 4095) 4096 ltac:(lia)) as Hmb.
            pose proof (Z.div_mod pu 4096 ltac:(lia)) as Hdp.
            rewrite Hpumod in Hdp. clear -Hd Hmb Hdp Hlo Hhi Hpu0. lia. }
          rewrite Hpe. reflexivity. }
        iEval (rewrite (proc_ptm_sz_cong Pj (pu + 4096 * Z.of_nat (S i))%Z
                          (uint newsz)
                          (umem_grow Mv (pu + 4096 * Z.of_nat (S i))%Z)
                          Hlvend)) in "Hpt".
        iEval (rewrite (umem_grow_cong Mv (pu + 4096 * Z.of_nat (S i))%Z
                          (uint newsz) Hlvend)) in "Hpt".
        iExact "Hpt". } }
    (* =========== mappages FAILED: kfree the page and roll back ======== *)
    assert (Hk0 : k = 0%nat) by (clear -Hklt; lia). subst k.
    cbn [pt_insert_run] in Hrep'.
    iDestruct (proc_ptm_rebuild Pi (pu + 4096 * Z.of_nat i)%Z
                 (umem_grow Mv (pu + 4096 * Z.of_nat i)%Z) t' m_ad
                 Hwf Hview Hrep' Hbase'' with "Hptree Hown") as "Hpt".
    assert (Hbnt : neq_vec (mg !!! Regidx Ra0) zero_reg = true)
      by (rewrite Hga0; vm_compute; reflexivity).
    assert (Htgt88 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x54) : mword 64)
              (sign_extend' 64
                 (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.uvmalloc + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x54))
              (mword_of_int 26 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              mg (K - 10)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) ltac:(rgne; exact Hbnt) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (uai_54 with "Htext"). }
    iApply bi.later_intro. iIntros (CIDu35 Hsu35) "Hcg Hpc".
    iEval (rewrite Htgt88) in "Hpc".
    (* +0x88 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x88)) Ra0 Rs1 mg (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_88 with "Htext"). }
    iIntros (CIDu36 Hsu36) "Hcg Hpc".
    set (F1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mg !!! Regidx Rs1))]> mg).
    assert (Hq8a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x88) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq8a) in "Hpc".
    (* +0x8a jal ra,kfree *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x8a)) Rra
              (mword_of_int 2094830 : mword 21) F1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (uai_8a with "Htext"). }
    iIntros (CIDu37 Hsu37) "Hcg Hpc".
    iDestruct (cpu_own_transport CIDu25 CIDu37 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    set (F2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x8a) : mword 64) 4)]> F1).
    assert (Htgtkf : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x8a) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094830 : mword 21))
                     = mword_of_int KernelSyms.kfree)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtkf) in "Hpc".
    assert (HF2ra : F2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x8a) : mword 64) 4)
      by (rewrite /F2 upd_eq; reflexivity).
    assert (HF2a0 : F2 !!! Regidx Ra0 = r).
    { rewrite /F2. rewrite upd_ne; [| reg_neq].
      rewrite /F1 upd_eq. rewrite add_vec_zero_l. exact Hmgs1. }
    assert (HF2sp : F2 !!! Regidx csp_rs1 = spr).
    { rewrite /F2. rewrite upd_ne; [| reg_neq].
      rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmgsp. }
    assert (HF2s2 : F2 !!! Regidx Rs2 = av).
    { rewrite /F2. rewrite upd_ne; [| reg_neq].
      rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmgs2. }
    assert (HF2s5 : F2 !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite /F2. rewrite upd_ne; [| reg_neq].
      rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmgs5. }
    assert (HF2s7 : F2 !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite /F2. rewrite upd_ne; [| reg_neq].
      rewrite /F1. rewrite upd_ne; [| reg_neq]. exact Hmgs7. }
    assert (HF2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              F2 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      ua_thr_peel. apply Hmgthr; assumption. }
    iApply (Kfree.wp_kfree_sconf KT1 γa γk (mword_of_int KernelSyms.kmem)
              (mword_of_int (KernelSyms.kmem + 24)) F2 None 0%nat eb p (K - 10)%nat b
              _
              HKka ltac:(reflexivity) ltac:(reflexivity)
              ltac:(vm_compute; reflexivity)
              Hbelow
              with "Hcg Hcnt Htext Hpc Hlock [Hpage] Havail").
    all: try lkbelow.
    { rewrite /kfree_pre HF2a0.
      iSplitR; [iPureIntro; exact Hpv |].
      (* kfree is contents-blind AND view-blind (§0.26′): forget the
         zeros, then forget that they were ever determinate *)
      iApply page_own_free. rewrite /page_own /byte_any.
      iApply (big_sepL_impl with "Hpage"). iIntros "!>" (kk x Hx) "Hj".
      iExists _. iExact "Hj". }
    iIntros (CIDu38 Hsu38 mfk) "Hcg Hcnt Hpc %Hfcs _".
    assert (Hret8e : ret_pc (F2 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmalloc + 0x8e)).
    { rewrite HF2ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret8e) in "Hpc".
    assert (Hfsp : mfk !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hfcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HF2sp. }
    assert (Hfs2 : mfk !!! Regidx Rs2 = av).
    { rewrite (callee_saved_lookup Hfcs Rs2 ltac:(vm_compute; reflexivity)). exact HF2s2. }
    assert (Hfs5 : mfk !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite (callee_saved_lookup Hfcs Rs5 ltac:(vm_compute; reflexivity)). exact HF2s5. }
    assert (Hfs7 : mfk !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite (callee_saved_lookup Hfcs Rs7 ltac:(vm_compute; reflexivity)). exact HF2s7. }
    assert (Hfthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              mfk !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hfcs c Hc). apply HF2thr; assumption. }
    (* +0x8e c.mv a2,s7 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x8e)) Ra2 Rs7 mfk (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_8e with "Htext"). }
    iIntros (CIDu39 Hsu39) "Hcg Hpc".
    set (G1 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (mfk !!! Regidx Rs7))]> mfk).
    assert (Hq90 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x8e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq90) in "Hpc".
    (* +0x90 c.mv a1,s2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x90)) Ra1 Rs2 G1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_90 with "Htext"). }
    iIntros (CIDu40 Hsu40) "Hcg Hpc".
    set (G2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (G1 !!! Regidx Rs2))]> G1).
    assert (Hq92 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x90) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq92) in "Hpc".
    (* +0x92 c.mv a0,s5 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x92)) Ra0 Rs5 G2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_92 with "Htext"). }
    iIntros (CIDu41 Hsu41) "Hcg Hpc".
    set (G3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (G2 !!! Regidx Rs5))]> G2).
    assert (Hq94 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x92) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq94) in "Hpc".
    (* +0x94 jal ra,uvmdealloc *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x94)) Rra
              (mword_of_int 2096936 : mword 21) G3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (uai_94 with "Htext"). }
    iIntros (CIDu42 Hsu42) "Hcg Hpc".
    iDestruct (cpu_own_transport CIDu38 CIDu42 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    set (G4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x94) : mword 64) 4)]> G3).
    assert (Htgtud2 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x94) : mword 64)
                        (sign_extend' 64 (mword_of_int 2096936 : mword 21))
                      = mword_of_int KernelSyms.uvmdealloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtud2) in "Hpc".
    assert (HG4ra : G4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x94) : mword 64) 4)
      by (rewrite /G4 upd_eq; reflexivity).
    assert (HG4a0 : G4 !!! Regidx Ra0 = page_base Pi.(ud_root)).
    { rewrite Hrooti. rewrite /G4. rewrite upd_ne; [| reg_neq].
      rewrite /G3 upd_eq. rewrite add_vec_zero_l.
      rewrite /G2. rewrite upd_ne; [| reg_neq].
      rewrite /G1. rewrite upd_ne; [| reg_neq]. exact Hfs5. }
    assert (HG4a1 : G4 !!! Regidx Ra1 = av).
    { rewrite /G4. rewrite upd_ne; [| reg_neq].
      rewrite /G3. rewrite upd_ne; [| reg_neq].
      rewrite /G2 upd_eq. rewrite add_vec_zero_l.
      rewrite /G1. rewrite upd_ne; [| reg_neq]. exact Hfs2. }
    assert (HG4a2 : G4 !!! Regidx Ra2 = pgroundup oldsz).
    { rewrite /G4. rewrite upd_ne; [| reg_neq].
      rewrite /G3. rewrite upd_ne; [| reg_neq].
      rewrite /G2. rewrite upd_ne; [| reg_neq].
      rewrite /G1 upd_eq. rewrite add_vec_zero_l. exact Hfs7. }
    assert (HG4sp : G4 !!! Regidx csp_rs1 = spr).
    { rewrite /G4 /G3 /G2 /G1. repeat (rewrite upd_ne; [| reg_neq]). exact Hfsp. }
    assert (HG4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              G4 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      ua_thr_peel. apply Hfthr; assumption. }
    (* EXPLICIT-CPUID: [SpecUvmdealloc.v]'s entry-side tp premise is gone
       (same reasoning as the first [Uvmdealloc] call above); no [tp_pin]
       re-tagging needed. *)
    assert (Hudo2 : (uint (G4 !!! Regidx Ra1) <= uvm_maxsz)%Z)
      by (rewrite HG4a1; exact Hudold).
    iEval (rewrite <- Havu) in "Hpt".
    iEval (rewrite <- HG4a1) in "Hpt".
    iApply (Uvmdealloc.wp_uvmdealloc_mem_sconf γa G4 Pi
              (umem_grow Mv (uint (G4 !!! Regidx Ra1))) (K - 10)%nat eb p b
              _ HKud HG4a0 Hudo2
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    all: try lkbelow.
    iIntros (CIDu43 Hsu43 md2) "Hcg Hcnt Hpc %Hd2cs _ Hpt".
    iEval (rewrite HG4a1 HG4a2 Hpgpu Hnpd Hrszd Hgrowdel) in "Hpt".
    assert (Hret98 : ret_pc (G4 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmalloc + 0x98)).
    { rewrite HG4ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret98) in "Hpc".
    assert (Hd2sp : md2 !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hd2cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HG4sp. }
    assert (Hd2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              md2 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hd2cs c Hc).
      apply HG4thr; assumption. }
    (* +0x98 c.li a0,0 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x98)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) md2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (uai_98 with "Htext"). }
    iIntros (CIDu44 Hsu44) "Hcg Hpc".
    set (G5 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> md2).
    assert (HG5sp : G5 !!! Regidx csp_rs1 = spr)
      by (rewrite /G5; rewrite upd_ne; [exact Hd2sp | reg_neq]).
    assert (Hq9a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x98) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x9a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq9a) in "Hpc".
    (* +0x9a c.ldsp s1,56(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x9a)) (mword_of_int 7 : mword 6) Rs1
              G5 (K - 10)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hk3]").
    { iApply (uai_9a with "Htext"). }
    { iEval (rewrite HG5sp Hb3). iExact "Hk3". }
    iIntros (CIDu45 Hsu45) "Hcg Hpc Hk3". iEval (rewrite HG5sp Hb3) in "Hk3".
    set (G6 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> G5).
    assert (HG6sp : G6 !!! Regidx csp_rs1 = spr)
      by (rewrite /G6; rewrite upd_ne; [exact HG5sp | reg_neq]).
    assert (Hq9c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x9a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x9c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq9c) in "Hpc".
    (* +0x9c c.ldsp s3,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x9c)) (mword_of_int 5 : mword 6) Rs3
              G6 (K - 10)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hk5]").
    { iApply (uai_9c with "Htext"). }
    { iEval (rewrite HG6sp Hb5). iExact "Hk5". }
    iIntros (CIDu46 Hsu46) "Hcg Hpc Hk5". iEval (rewrite HG6sp Hb5) in "Hk5".
    set (G7 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> G6).
    assert (HG7sp : G7 !!! Regidx csp_rs1 = spr)
      by (rewrite /G7; rewrite upd_ne; [exact HG6sp | reg_neq]).
    assert (Hq9e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x9c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x9e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq9e) in "Hpc".
    (* +0x9e c.ldsp s6,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x9e)) (mword_of_int 2 : mword 6) Rs6
              G7 (K - 10)%nat (mm !!! Regidx Rs6) b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hk8]").
    { iApply (uai_9e with "Htext"). }
    { iEval (rewrite HG7sp Hb8). iExact "Hk8". }
    iIntros (CIDu47 Hsu47) "Hcg Hpc Hk8". iEval (rewrite HG7sp Hb8) in "Hk8".
    set (G8 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> G7).
    assert (Hqa0 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x9e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0xa0)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hqa0) in "Hpc".
    (* +0xa0 c.j -0x28 *)
    assert (Hjta0 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0xa0) : mword 64)
              (sign_extend' 64
                 (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.uvmalloc + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0xa0))
              (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")))
              G8 (K - 10)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (uai_a0 with "Htext"). }
    iIntros (CIDu48 Hsu48). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hjta0) in "Hpc".
    iDestruct (ua_restore_mem P Pi (svpn_of (pgroundup oldsz)) i
                   (uint (pgroundup oldsz)) (uint oldsz) Mv
                   Hext Hdom Hfreshi Hlvsame
                 with "Hpt") as "Hpt".
    iEval (rewrite /ua_exit) in "Hexit".
    iSpecialize ("Hexit" $! CIDu48 with "[%]"); [wp_next_chain|].
    iDestruct (cpu_own_transport CIDu43 CIDu48 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply ("Hexit" $! G8 (mword_of_int 0) with "[%] Hcg Hcnt Hpc [Hk3 Hk5 Hk8] [Hpt]").
    { split_and!.
      - rewrite /G8. rewrite upd_ne; [exact HG7sp | reg_neq].
      - rewrite /G8 /G7 /G6. repeat (rewrite upd_ne; [| reg_neq]).
        rewrite /G5 upd_eq. reflexivity.
      - intros c Hc H2 H8 H18 H20 H21 H23.
        destruct (decide (c = Rs1)) as [->|H9].
        { rewrite /G8. rewrite upd_ne; [| reg_neq].
          rewrite /G7. rewrite upd_ne; [| reg_neq]. rewrite /G6 upd_eq. reflexivity. }
        destruct (decide (c = Rs3)) as [->|H19].
        { rewrite /G8. rewrite upd_ne; [| reg_neq]. rewrite /G7 upd_eq. reflexivity. }
        destruct (decide (c = Rs6)) as [->|H22].
        { rewrite /G8 upd_eq. reflexivity. }
        ua_thr_peel. apply Hd2thr; assumption. }
    { iExists _, _, _. iSplitL "Hk3"; [iExact "Hk3"|]. iSplitL "Hk5"; [iExact "Hk5"|]. iExact "Hk8". }
    { rewrite /ua_pay. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. }
  Qed.

  Lemma wp_uvmalloc_mem_sconf
      (γa : gname) (mm : regfile)
      (P : uptd) (Mv : gmap Z (bv 8)) (xperm : Z) (K : nat) (eb : bool)
      (p : mword 64) (b : bool) (lks : gset string)
    : wp_uvmalloc_mem_sconf_body γa mm P Mv xperm K eb p b lks.
  Proof.
    cbv beta delta [wp_uvmalloc_mem_sconf_body].
    intros pcE oldsz newsz vpn0 n ret_tgt HK Htp Hroot Hxp Hxrng Hperm Hobd Hnbd Hfr Hbelow.
    assert (Hnd : n = uvma_np oldsz newsz) by reflexivity.
    assert (HK10 : (10 <= K)%nat) by (clear -HK; lia).
    assert (HKback : ((K - 10) + 10)%nat = K) by (clear -HK; lia).
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc Hpt #Henv Hcont".
    iDestruct (proc_ptm_dom P (uint oldsz) Mv with "Hpt") as %HMdom.
    (* everything live at [oldsz] is already recorded, so growing TO
       [oldsz] is the identity -- what the two do-nothing arms need *)
    assert (Hgrow0 : umem_grow Mv (uint oldsz) = Mv)
      by (apply umem_grow_id; intros a Ha; apply HMdom; by right).
    (* ---- the PGROUNDUP arithmetic, kept over plain [Z] (the zify rule) --- *)
    rewrite uint_unsigned in Hobd. rewrite uvm_maxsz_val in Hobd.
    (* the [newsz] premise is a DISJUNCTION now (SpecUvmalloc.v); put its
       left arm over plain [Z] so the [remember]s below abstract it too. *)
    assert (Hnbd2 : (bv_unsigned newsz <= 274877898752)%Z
                    \/ um_covered oldsz P.(ud_um)).
    { destruct Hnbd as [Hb | Hc]; [left | right; exact Hc].
      rewrite uint_unsigned in Hb. rewrite uvm_maxsz_val in Hb. exact Hb. }
    clear Hnbd.
    pose proof (proj1 (bv_unsigned_in_range _ oldsz)) as Hov0.
    pose proof (proj1 (bv_unsigned_in_range _ newsz)) as Hnz0.
    remember (bv_unsigned oldsz) as ov eqn:Hov.
    remember (bv_unsigned newsz) as nz eqn:Hnz.
    assert (Hovb : (ov + 4095 < 2 ^ 64)%Z).
    { clear -Hobd Hov0. change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
    assert (Hpuv : bv_unsigned (pgroundup oldsz)
                   = ((ov + 4095) - (ov + 4095) mod 4096)%Z).
    { rewrite Hov. apply pgroundup_unsigned. rewrite <- Hov. exact Hovb. }
    remember ((ov + 4095) - (ov + 4095) mod 4096)%Z as pu eqn:Hpud.
    assert (Hpuge : (ov <= pu)%Z) by (rewrite Hpud; apply z_pgu_ge).
    assert (Hpumod : (pu mod 4096 = 0)%Z)
      by (rewrite Hpud; exact (z_pgd_mod (ov + 4095))).
    assert (Hpu0 : (0 <= pu)%Z) by (clear -Hov0 Hpuge; lia).
    destruct (zopz0zI_u (mm !!! Regidx Ra2) (mm !!! Regidx Ra1)) eqn:Hcmp0.
    { (* ============ newsz < oldsz: return oldsz, NO FRAME ============= *)
      assert (Hlt0 : (uint newsz < uint oldsz)%Z)
        by (unfold zopz0zI_u in Hcmp0; apply Z.ltb_lt; exact Hcmp0).
      assert (Hlt0' : (nz < ov)%Z).
      { rewrite Hnz Hov. rewrite <- !uint_unsigned. exact Hlt0. }
      assert (Hn0 : n = 0%nat).
      { rewrite Hnd. unfold uvma_np. rewrite Hpuv. rewrite <- Hnz.
        apply ua_z_np_zero. clear -Hlt0' Hpuge. lia. }
      assert (Hala2 : eq_vec (access_vec_dec
                 (add_vec (pcE : mword 64) (sign_extend' 64 (mword_of_int 162 : mword 13))) 0)
                 ('b"0") = true) by (vm_compute; reflexivity).
      assert (Htgta2 : add_vec (pcE : mword 64)
                         (sign_extend' 64 (mword_of_int 162 : mword 13))
                       = mword_of_int (KernelSyms.uvmalloc + 0xa2))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bltu_taken_s_sconf pcE (mword_of_int 162 : mword 13) Ra1 Ra2 mm K b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hcmp0)
                Hala2 with "Hcg Hpc []").
      { iApply (uai_00 with "Htext"). }
      iApply bi.later_intro. iIntros (CIDu49 Hsu49) "Hcg Hpc".
      iEval (rewrite Htgta2) in "Hpc".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0xa2)) Ra0 Ra1 mm K b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (uai_a2 with "Htext"). }
      iIntros (CIDu50 Hsu50) "Hcg Hpc".
      set (Y1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mm !!! Regidx Ra1))]> mm).
      assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0xa2) : mword 64) 2
                      = mword_of_int (KernelSyms.uvmalloc + 0xa4))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hppa4) in "Hpc".
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0xa4)) Rra Y1 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc []").
      { iApply (uai_a4 with "Htext"). }
      iIntros (CIDu51 Hsu51) "Hcg Hpc".
      assert (HY1ra : Y1 !!! Regidx Rra = mm !!! Regidx Rra)
        by (rewrite /Y1; rewrite upd_ne; [reflexivity | reg_neq]).
      assert (Hretf : ret_pc (Y1 !!! Regidx Rra) = ret_tgt) by (rewrite HY1ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iSpecialize ("Hcont" $! CIDu51 with "[%]"); [wp_next_chain|].
      iDestruct (cpu_own_transport CID CIDu51 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("Hcont" $! Y1 with "Hcg Hcnt Hpc [%] [Hpt]").
      { unfold callee_saved. split_and!;
          (rewrite /Y1; rewrite upd_ne; [reflexivity | reg_neq]). }
      iRight. iExists P, oldsz.
      iSplitR; [iPureIntro; apply uptd_ext_refl |].
      iSplitR; [iPureIntro; rewrite Hn0; apply dom_run_0 |].
      iSplitR.
      { iPureIntro. rewrite Hn0 vpn_run_0. intros v Hv.
        exfalso. exact (not_elem_of_empty v Hv). }
      iSplitR; [iPureIntro; left; split; [exact Hlt0 | reflexivity] |].
      iSplitR.
      { iPureIntro. rewrite /Y1 upd_eq. rewrite add_vec_zero_l. reflexivity. }
      rewrite Hgrow0. iExact "Hpt". }

    (* ================= newsz >= oldsz: push the frame ================== *)
    assert (Hoin : (uint oldsz <= uint newsz)%Z)
      by (unfold zopz0zI_u in Hcmp0; apply Z.ltb_ge; exact Hcmp0).
    assert (Hovnz : (ov <= nz)%Z).
    { rewrite Hnz Hov. rewrite <- !uint_unsigned. exact Hoin. }
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 10).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp04 : add_vec_int (pcE : mword 64) 4 = mword_of_int (KernelSyms.uvmalloc + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_bltu_fall_s_sconf pcE (mword_of_int 162 : mword 13) Ra1 Ra2 mm K b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hcmp0)
              with "Hcg Hpc []").
    { iApply (uai_00 with "Htext"). }
    iIntros (CIDu52 Hsu52) "Hcg Hpc".
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x04))
              (mword_of_int 59 : mword 6) mm K 10 b HK10 Hpush
              with "Hcg Hpc []").
    { iApply (uai_04 with "Htext"). }
    iIntros (CIDu53 Hsu53) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    set (spr := add_vec (mm !!! Regidx csp_rs1 : mword 64)
                  (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))).
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (mm !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> mm).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (mm !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> mm) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
    iDestruct "S1" as (u72) "Hk1". iDestruct "S2" as (u64) "Hk2".
    iDestruct "S3" as (u56) "Hk3". iDestruct "S4" as (u48) "Hk4".
    iDestruct "S5" as (u40) "Hk5". iDestruct "S6" as (u32) "Hk6".
    iDestruct "S7" as (u24) "Hk7". iDestruct "S8" as (u16) "Hk8".
    iDestruct "S9" as (u8)  "Hk9". iDestruct "S10" as (u0) "Hk10".
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk sp0 7).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk sp0 8).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk sp0 9).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hsprstk : pa_stk sp0 10 = spr).
    { rewrite /pa_stk /spr /sp0 /add_vec_int. f_equal;
        try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    (* +0x06 c.sdsp ra,72(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x06)) (mword_of_int 9 : mword 6) Rra
              R1 (K - 10)%nat u72 b with "Hcg Hpc [] [Hk1]").
    { iApply (uai_06 with "Htext"). }
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros (CIDu54 Hsu54) "Hcg Hpc Hk1". iEval (rewrite HspR1 Hb1) in "Hk1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HR1ra) in "Hk1".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    (* +0x08 c.sdsp s0,64(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x08)) (mword_of_int 8 : mword 6) Rs0
              R1 (K - 10)%nat u64 b with "Hcg Hpc [] [Hk2]").
    { iApply (uai_08 with "Htext"). }
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros (CIDu55 Hsu55) "Hcg Hpc Hk2". iEval (rewrite HspR1 Hb2) in "Hk2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HR1s0) in "Hk2".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x08) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    (* +0x0a c.sdsp s2,48(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x0a)) (mword_of_int 6 : mword 6) Rs2
              R1 (K - 10)%nat u48 b with "Hcg Hpc [] [Hk4]").
    { iApply (uai_0a with "Htext"). }
    { iEval (rewrite HspR1 Hb4). iExact "Hk4". }
    iIntros (CIDu56 Hsu56) "Hcg Hpc Hk4". iEval (rewrite HspR1 Hb4) in "Hk4".
    assert (HR1s2 : R1 !!! Regidx Rs2 = mm !!! Regidx Rs2)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HR1s2) in "Hk4".
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x0a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c c.sdsp s4,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x0c)) (mword_of_int 4 : mword 6) Rs4
              R1 (K - 10)%nat u32 b with "Hcg Hpc [] [Hk6]").
    { iApply (uai_0c with "Htext"). }
    { iEval (rewrite HspR1 Hb6). iExact "Hk6". }
    iIntros (CIDu57 Hsu57) "Hcg Hpc Hk6". iEval (rewrite HspR1 Hb6) in "Hk6".
    assert (HR1s4 : R1 !!! Regidx Rs4 = mm !!! Regidx Rs4)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HR1s4) in "Hk6".
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x0c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    (* +0x0e c.sdsp s5,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x0e)) (mword_of_int 3 : mword 6) Rs5
              R1 (K - 10)%nat u24 b with "Hcg Hpc [] [Hk7]").
    { iApply (uai_0e with "Htext"). }
    { iEval (rewrite HspR1 Hb7). iExact "Hk7". }
    iIntros (CIDu58 Hsu58) "Hcg Hpc Hk7". iEval (rewrite HspR1 Hb7) in "Hk7".
    assert (HR1s5 : R1 !!! Regidx Rs5 = mm !!! Regidx Rs5)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HR1s5) in "Hk7".
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x0e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    (* +0x10 c.sdsp s7,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x10)) (mword_of_int 1 : mword 6) Rs7
              R1 (K - 10)%nat u8 b with "Hcg Hpc [] [Hk9]").
    { iApply (uai_10 with "Htext"). }
    { iEval (rewrite HspR1 Hb9). iExact "Hk9". }
    iIntros (CIDu59 Hsu59) "Hcg Hpc Hk9". iEval (rewrite HspR1 Hb9) in "Hk9".
    assert (HR1s7 : R1 !!! Regidx Rs7 = mm !!! Regidx Rs7)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rgne; rewrite HR1s7) in "Hk9".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x10) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    (* +0x12 c.addi4spn s0,sp,80 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x12)) (Cregidx (mword_of_int 0))
              (mword_of_int 20 : mword 8) Rs0 R1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc []").
    { iApply (uai_12 with "Htext"). }
    iIntros (CIDu60 Hsu60) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x12) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    (* +0x14 c.mv s5,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x14)) Rs5 Ra0 R2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_14 with "Htext"). }
    iIntros (CIDu61 Hsu61) "Hcg Hpc".
    set (R3 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x14) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* +0x16 c.mv s4,a2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x16)) Rs4 Ra2 R3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_16 with "Htext"). }
    iIntros (CIDu62 Hsu62) "Hcg Hpc".
    set (R4 := <[Regidx Rs4 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra2))]> R3).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x16) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* +0x18 c.lui a5,0x1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x18)) Ra5
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              R4 (K - 10)%nat b ltac:(vm_compute; discriminate)
              ltac:(rdok) lui_4096 with "Hcg Hpc []").
    { iApply (uai_18 with "Htext"). }
    iIntros (CIDu63 Hsu63) "Hcg Hpc".
    set (R5 := <[Regidx Ra5 := regval_into_reg (mword_of_int 4096 : mword 64)]> R4).
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x18) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* +0x1a c.addi a5,a5,-1 *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x1a)) Ra5 (mword_of_int 63 : mword 6)
              R5 (K - 10)%nat b ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc []").
    { iApply (uai_1a with "Htext"). }
    iIntros (CIDu64 Hsu64) "Hcg Hpc".
    set (R6 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (R5 !!! Regidx Ra5)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6))))]> R5).
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x1a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    (* +0x1c c.add a1,a1,a5 *)
    iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x1c)) Ra1 Ra5 R6 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_1c with "Htext"). }
    iIntros (CIDu65 Hsu65) "Hcg Hpc".
    set (R7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (R6 !!! Regidx Ra1) (R6 !!! Regidx Ra5))]> R6).
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x1c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    (* +0x1e c.lui a5,0xfffff *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x1e)) Ra5
              (sign_extend' 20 (mword_of_int 63 : mword 6)) (mword_of_int (-4096) : mword 64)
              R7 (K - 10)%nat b ltac:(vm_compute; discriminate)
              ltac:(rdok) lui_m4096 with "Hcg Hpc []").
    { iApply (uai_1e with "Htext"). }
    iIntros (CIDu66 Hsu66) "Hcg Hpc".
    set (R8 := <[Regidx Ra5 := regval_into_reg (mword_of_int (-4096) : mword 64)]> R7).
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x1e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    (* +0x20 and s2,a1,a5  --  s2 := PGROUNDUP(oldsz) *)
    assert (H4095 : add_vec (mword_of_int 4096 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))
                    = (mword_of_int 4095 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    assert (HR6a1 : R6 !!! Regidx Ra1 = oldsz).
    { rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq].
      rewrite /R4. rewrite upd_ne; [| reg_neq].
      rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [reflexivity | reg_neq]. }
    assert (HR6a5 : R6 !!! Regidx Ra5 = (mword_of_int 4095 : mword 64)).
    { rewrite /R6 upd_eq. rewrite /R5 upd_eq. exact H4095. }
    assert (HR8a5 : R8 !!! Regidx Ra5 = (mword_of_int (-4096) : mword 64))
      by (rewrite /R8 upd_eq; reflexivity).
    assert (HR8a1 : R8 !!! Regidx Ra1 = add_vec oldsz (mword_of_int 4095)).
    { rewrite /R8. rewrite upd_ne; [| reg_neq].
      rewrite /R7 upd_eq. rewrite HR6a1 HR6a5. reflexivity. }
    assert (HR8and : and_vec (R8 !!! Regidx Ra1) (R8 !!! Regidx Ra5) = pgroundup oldsz)
      by (rewrite HR8a1 HR8a5; reflexivity).
    iApply (wp_and_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x20)) Rs2 Ra1 Ra5 (pgroundup oldsz)
              R8 (K - 10)%nat b ltac:(vm_compute; discriminate)
              ltac:(rdok) ltac:(rgne; rgne; exact HR8and) with "Hcg Hpc []").
    { iApply (uai_20 with "Htext"). }
    iIntros (CIDu67 Hsu67) "Hcg Hpc".
    set (R9 := <[Regidx Rs2 := regval_into_reg (pgroundup oldsz)]> R8).
    assert (Hp24 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x20) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmalloc + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp24) in "Hpc".
    (* +0x24 c.mv s7,s2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x24)) Rs7 Rs2 R9 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (uai_24 with "Htext"). }
    iIntros (CIDu68 Hsu68) "Hcg Hpc".
    set (R10 := <[Regidx Rs7 := regval_into_reg (add_vec zero_reg (R9 !!! Regidx Rs2))]> R9).
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x24) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* --- the register facts that hold at +0x26 --- *)
    assert (HR10s2 : R10 !!! Regidx Rs2 = pgroundup oldsz).
    { rewrite /R10. rewrite upd_ne; [| reg_neq]. rewrite /R9 upd_eq. reflexivity. }
    assert (HR10s7 : R10 !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite /R10 upd_eq. rewrite add_vec_zero_l. exact HR10s2. }
    assert (HR10a2 : R10 !!! Regidx Ra2 = newsz).
    { rewrite /R10. rewrite upd_ne; [| reg_neq].
      rewrite /R9. rewrite upd_ne; [| reg_neq].
      rewrite /R8. rewrite upd_ne; [| reg_neq].
      rewrite /R7. rewrite upd_ne; [| reg_neq].
      rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq].
      rewrite /R4. rewrite upd_ne; [| reg_neq].
      rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [reflexivity | reg_neq]. }
    assert (HR10s4 : R10 !!! Regidx Rs4 = newsz).
    { rewrite /R10. rewrite upd_ne; [| reg_neq].
      rewrite /R9. rewrite upd_ne; [| reg_neq].
      rewrite /R8. rewrite upd_ne; [| reg_neq].
      rewrite /R7. rewrite upd_ne; [| reg_neq].
      rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq].
      rewrite /R4 upd_eq. rewrite add_vec_zero_l.
      rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [reflexivity | reg_neq]. }
    assert (HR10s5 : R10 !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite /R10. rewrite upd_ne; [| reg_neq].
      rewrite /R9. rewrite upd_ne; [| reg_neq].
      rewrite /R8. rewrite upd_ne; [| reg_neq].
      rewrite /R7. rewrite upd_ne; [| reg_neq].
      rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq].
      rewrite /R4. rewrite upd_ne; [| reg_neq].
      rewrite /R3 upd_eq. rewrite add_vec_zero_l.
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [| reg_neq]. exact Hroot. }
    assert (HR10a3 : R10 !!! Regidx Ra3 = (mword_of_int xperm : mword 64)).
    { rewrite /R10 /R9 /R8 /R7 /R6 /R5 /R4 /R3 /R2 /R1.
      repeat (rewrite upd_ne; [| reg_neq]). exact Hxp. }
    assert (HR10sp : R10 !!! Regidx csp_rs1 = spr).
    { rewrite /R10 /R9 /R8 /R7 /R6 /R5 /R4 /R3 /R2.
      repeat (rewrite upd_ne; [| reg_neq]). exact HspR1. }
    assert (HR10thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs4 -> c <> Rs5 -> c <> Rs7 ->
              R10 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H18 H20 H21 H23.
      ua_thr_peel. reflexivity. }
    (* ================================================================= *)
    (*  THE EPILOGUE / JOIN at +0x78, taken before the second branch.     *)
    (* ================================================================= *)
    iAssert (ua_exit (CID0 := CID) mm P Mv vpn0 n xperm K eb p b lks sp0 spr oldsz newsz)
      with "[Hcont Hk1 Hk2 Hk4 Hk6 Hk7 Hk9 Hk10]" as "Hepi".
    { rewrite /ua_exit.
      iIntros (CIDu86) "%Hsu86".
      iIntros (mj res) "(%Hjsp & %Hja0 & %Hjthr) Hcg Hcnt Hpc Hjunk Hpost".
      iDestruct "Hjunk" as (w1 w3 w6) "(Hk3 & Hk5 & Hk8)".
      (* +0x78 c.ldsp ra,72(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x78)) (mword_of_int 9 : mword 6) Rra
                mj (K - 10)%nat (mm !!! Regidx Rra) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk1]").
      { iApply (uai_78 with "Htext"). }
      { iEval (rewrite Hjsp Hb1). iExact "Hk1". }
      iIntros (CIDu69 Hsu69) "Hcg Hpc Hk1". iEval (rewrite Hjsp Hb1) in "Hk1".
      set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mj).
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spr)
        by (rewrite /E1; rewrite upd_ne; [exact Hjsp | reg_neq]).
      assert (Hq7a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x78) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x7a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq7a) in "Hpc".
      (* +0x7a c.ldsp s0,64(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x7a)) (mword_of_int 8 : mword 6) Rs0
                E1 (K - 10)%nat (mm !!! Regidx Rs0) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk2]").
      { iApply (uai_7a with "Htext"). }
      { iEval (rewrite HE1sp Hb2). iExact "Hk2". }
      iIntros (CIDu70 Hsu70) "Hcg Hpc Hk2". iEval (rewrite HE1sp Hb2) in "Hk2".
      set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spr)
        by (rewrite /E2; rewrite upd_ne; [exact HE1sp | reg_neq]).
      assert (Hq7c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x7a) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq7c) in "Hpc".
      (* +0x7c c.ldsp s2,48(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x7c)) (mword_of_int 6 : mword 6) Rs2
                E2 (K - 10)%nat (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk4]").
      { iApply (uai_7c with "Htext"). }
      { iEval (rewrite HE2sp Hb4). iExact "Hk4". }
      iIntros (CIDu71 Hsu71) "Hcg Hpc Hk4". iEval (rewrite HE2sp Hb4) in "Hk4".
      set (E3 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E2).
      assert (HE3sp : E3 !!! Regidx csp_rs1 = spr)
        by (rewrite /E3; rewrite upd_ne; [exact HE2sp | reg_neq]).
      assert (Hq7e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x7c) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq7e) in "Hpc".
      (* +0x7e c.ldsp s4,32(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x7e)) (mword_of_int 4 : mword 6) Rs4
                E3 (K - 10)%nat (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk6]").
      { iApply (uai_7e with "Htext"). }
      { iEval (rewrite HE3sp Hb6). iExact "Hk6". }
      iIntros (CIDu72 Hsu72) "Hcg Hpc Hk6". iEval (rewrite HE3sp Hb6) in "Hk6".
      set (E4 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> E3).
      assert (HE4sp : E4 !!! Regidx csp_rs1 = spr)
        by (rewrite /E4; rewrite upd_ne; [exact HE3sp | reg_neq]).
      assert (Hq80 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x7e) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq80) in "Hpc".
      (* +0x80 c.ldsp s5,24(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x80)) (mword_of_int 3 : mword 6) Rs5
                E4 (K - 10)%nat (mm !!! Regidx Rs5) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk7]").
      { iApply (uai_80 with "Htext"). }
      { iEval (rewrite HE4sp Hb7). iExact "Hk7". }
      iIntros (CIDu73 Hsu73) "Hcg Hpc Hk7". iEval (rewrite HE4sp Hb7) in "Hk7".
      set (E5 := <[Regidx Rs5 := regval_into_reg (mm !!! Regidx Rs5)]> E4).
      assert (HE5sp : E5 !!! Regidx csp_rs1 = spr)
        by (rewrite /E5; rewrite upd_ne; [exact HE4sp | reg_neq]).
      assert (Hq82 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x80) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq82) in "Hpc".
      (* +0x82 c.ldsp s7,8(sp) *)
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x82)) (mword_of_int 1 : mword 6) Rs7
                E5 (K - 10)%nat (mm !!! Regidx Rs7) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hk9]").
      { iApply (uai_82 with "Htext"). }
      { iEval (rewrite HE5sp Hb9). iExact "Hk9". }
      iIntros (CIDu74 Hsu74) "Hcg Hpc Hk9". iEval (rewrite HE5sp Hb9) in "Hk9".
      set (E6 := <[Regidx Rs7 := regval_into_reg (mm !!! Regidx Rs7)]> E5).
      assert (HE6sp : E6 !!! Regidx csp_rs1 = spr)
        by (rewrite /E6; rewrite upd_ne; [exact HE5sp | reg_neq]).
      assert (Hq84 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x82) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq84) in "Hpc".
      (* +0x84 c.addi16sp sp,80 -- trade the frame back *)
      set (E7 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (E6 !!! Regidx csp_rs1)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E6).
      assert (Hwv : add_vec (E6 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0).
      { rewrite HE6sp. unfold spr, sp0. apply frame_cancel_80. }
      assert (Hpop : E6 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E6 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10).
      { rewrite Hwv HE6sp. symmetry. exact Hsprstk. }
      iAssert (stack_own (KTR := KT1) sp0 10) with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10]"
        as "Hframe10".
      { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
        iSplitL "Hk1"; [iExists _; iExact "Hk1" |].
        iSplitL "Hk2"; [iExists _; iExact "Hk2" |].
        iSplitL "Hk3"; [iExists _; iExact "Hk3" |].
        iSplitL "Hk4"; [iExists _; iExact "Hk4" |].
        iSplitL "Hk5"; [iExists _; iExact "Hk5" |].
        iSplitL "Hk6"; [iExists _; iExact "Hk6" |].
        iSplitL "Hk7"; [iExists _; iExact "Hk7" |].
        iSplitL "Hk8"; [iExists _; iExact "Hk8" |].
        iSplitL "Hk9"; [iExists _; iExact "Hk9" |].
        iSplitL "Hk10"; [iExists _; iExact "Hk10" |].
        done. }
      iEval (rewrite -Hwv) in "Hframe10".
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x84))
                (mword_of_int 5 : mword 6) E6 (K - 10)%nat 10 b Hpop
                with "Hcg Hpc [] Hframe10").
      { iApply (uai_84 with "Htext"). }
      iIntros (CIDu75 Hsu75) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E6 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E6) with E7.
      iEval (rewrite HKback) in "Hcg".
      assert (Hq86 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x84) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq86) in "Hpc".
      (* +0x86 c.ret *)
      assert (HE7ra : E7 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E7. rewrite upd_ne; [| reg_neq].
        rewrite /E6. rewrite upd_ne; [| reg_neq].
        rewrite /E5. rewrite upd_ne; [| reg_neq].
        rewrite /E4. rewrite upd_ne; [| reg_neq].
        rewrite /E3. rewrite upd_ne; [| reg_neq].
        rewrite /E2. rewrite upd_ne; [| reg_neq].
        rewrite /E1 upd_eq. reflexivity. }
      assert (HE7a0 : E7 !!! Regidx Ra0 = res).
      { rewrite /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hja0. }
      assert (HE7thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs2 -> c <> Rs4 -> c <> Rs5 -> c <> Rs7 ->
                E7 !!! Regidx c = mm !!! Regidx c).
      { intros c Hc H2 H8 H18 H20 H21 H23.
        ua_thr_peel.
        apply Hjthr; assumption. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x86)) Rra E7 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc []").
      { iApply (uai_86 with "Htext"). }
      iIntros (CIDu76 Hsu76) "Hcg Hpc".
      assert (Hretf : ret_pc (E7 !!! Regidx Rra) = ret_tgt) by (rewrite HE7ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iSpecialize ("Hcont" $! CIDu76 with "[%]"); [wp_next_chain|].
      iDestruct (cpu_own_transport CIDu86 CIDu76 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("Hcont" $! E7 with "Hcg Hcnt Hpc [%] [Hpost]").
      2:{ rewrite /ua_pay. rewrite HE7a0.
          iDestruct "Hpost" as "[(%Hz & Hp) | Hs]".
          - iLeft. iSplitR; [iPureIntro; exact Hz | iExact "Hp"].
          - (* the contract names the returned size existentially; the
               loop's payout has it fixed at [res] *)
            iRight. iDestruct "Hs" as (P') "(%Hx & %Hd & %Hl & %Hr & Hp)".
            iExists P', res.
            iSplitR; [iPureIntro; exact Hx |].
            iSplitR; [iPureIntro; exact Hd |].
            iSplitR; [iPureIntro; exact Hl |].
            iSplitR; [iPureIntro; exact Hr |].
            iSplitR; [iPureIntro; reflexivity |].
            iExact "Hp". }
      { unfold callee_saved.
        assert (Hc2 : E7 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1).
        { rewrite /E7 upd_eq. exact Hwv. }
        assert (Hc8 : E7 !!! Regidx Rs0 = mm !!! Regidx Rs0).
        { rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3. rewrite upd_ne; [| reg_neq].
          rewrite /E2 upd_eq. reflexivity. }
        assert (Hc18 : E7 !!! Regidx Rs2 = mm !!! Regidx Rs2).
        { rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4. rewrite upd_ne; [| reg_neq].
          rewrite /E3 upd_eq. reflexivity. }
        assert (Hc20 : E7 !!! Regidx Rs4 = mm !!! Regidx Rs4).
        { rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5. rewrite upd_ne; [| reg_neq].
          rewrite /E4 upd_eq. reflexivity. }
        assert (Hc21 : E7 !!! Regidx Rs5 = mm !!! Regidx Rs5).
        { rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6. rewrite upd_ne; [| reg_neq].
          rewrite /E5 upd_eq. reflexivity. }
        assert (Hc23 : E7 !!! Regidx Rs7 = mm !!! Regidx Rs7).
        { rewrite /E7. rewrite upd_ne; [| reg_neq].
          rewrite /E6 upd_eq. reflexivity. }
        split_and!;
          first [ exact Hc2 | exact Hc8 | exact Hc18 | exact Hc20 | exact Hc21 | exact Hc23
                | apply HE7thr; vm_compute; first [reflexivity | discriminate] ]. } }

    (* ================= +0x26 bgeu s2,a2 ================================ *)
    destruct (zopz0zKzJ_u (R10 !!! Regidx Rs2) (R10 !!! Regidx Ra2)) eqn:Hbg.
    { (* ---- PGROUNDUP(oldsz) >= newsz: nothing to do, return newsz ---- *)
      assert (Hnzle : (nz <= pu)%Z).
      { rewrite HR10s2 HR10a2 in Hbg. unfold zopz0zKzJ_u in Hbg.
        rewrite Z.geb_leb in Hbg. apply Z.leb_le in Hbg.
        rewrite !uint_unsigned in Hbg. rewrite Hnz. rewrite <- Hpuv. exact Hbg. }
      assert (Hn0 : n = 0%nat).
      { rewrite Hnd. unfold uvma_np. rewrite Hpuv. rewrite <- Hnz.
        apply ua_z_np_zero. exact Hnzle. }
      assert (Halta6 : eq_vec (access_vec_dec (add_vec (mword_of_int (KernelSyms.uvmalloc + 0x26) : mword 64)
                 (sign_extend' 64 (mword_of_int 128 : mword 13))) 0) ('b"0") = true)
        by (vm_compute; reflexivity).
      assert (Htgta6 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0x26) : mword 64)
                         (sign_extend' 64 (mword_of_int 128 : mword 13))
                       = mword_of_int (KernelSyms.uvmalloc + 0xa6))
        by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x26))
                (mword_of_int 128 : mword 13) Ra2 Rs2 R10 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hbg)
                Halta6 with "Hcg Hpc []").
      { iApply (uai_26 with "Htext"). }
      iApply bi.later_intro. iIntros (CIDu77 Hsu77) "Hcg Hpc".
      iEval (rewrite Htgta6) in "Hpc".
      (* +0xa6 c.mv a0,a2 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0xa6)) Ra0 Ra2 R10 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (uai_a6 with "Htext"). }
      iIntros (CIDu78 Hsu78) "Hcg Hpc".
      set (Z1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (R10 !!! Regidx Ra2))]> R10).
      assert (Hpa8 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0xa6) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmalloc + 0xa8)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpa8) in "Hpc".
      assert (Hjta8 : add_vec (mword_of_int (KernelSyms.uvmalloc + 0xa8) : mword 64)
                (sign_extend' 64
                   (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0"))))
              = mword_of_int (KernelSyms.uvmalloc + 0x78)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0xa8))
                (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0")))
                Z1 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (uai_a8 with "Htext"). }
      iIntros (CIDu79 Hsu79). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Hjta8) in "Hpc".
      iEval (rewrite /ua_exit) in "Hepi".
      iSpecialize ("Hepi" $! CIDu79 with "[%]"); [wp_next_chain|].
      iDestruct (cpu_own_transport CID CIDu79 0%nat eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iApply ("Hepi" $! Z1 newsz with "[%] Hcg Hcnt Hpc [Hk3 Hk5 Hk8] [Hpt]").
      { split_and!.
        - rewrite /Z1. rewrite upd_ne; [exact HR10sp | reg_neq].
        - rewrite /Z1 upd_eq. rewrite add_vec_zero_l. exact HR10a2.
        - intros c Hc H2 H8 H18 H20 H21 H23.
          rewrite /Z1. rewrite upd_ne; [| ua_thr_ne].
          apply HR10thr; assumption. }
      { iExists u56, u40, u16. iSplitL "Hk3"; [iExact "Hk3"|]. iSplitL "Hk5"; [iExact "Hk5"|]. iExact "Hk8". }
      { rewrite /ua_pay. iRight. iExists P.
        iSplitR; [iPureIntro; apply uptd_ext_refl |].
        iSplitR; [iPureIntro; rewrite Hn0; apply dom_run_0 |].
        iSplitR;
          [ iPureIntro; rewrite Hn0 vpn_run_0; intros v Hv;
            exfalso; exact (not_elem_of_empty v Hv) |].
        iSplitR; [iPureIntro; right; split; [exact Hoin | reflexivity] |].
        (* the loop never ran, and it never would have: [newsz] rounds to
           the same page as [oldsz], so the live set -- and the view --
           does not move even though the returned size does *)
        assert (Hlvn : forall a : Z,
                  uva_live (uint oldsz) a <-> uva_live (uint newsz) a).
        { intros a. rewrite /uva_live !uint_unsigned.
          unfold UserPtTree.pgroundup.
          assert (Hpuq : (pu = ((bv_unsigned oldsz + 4095) / 4096) * 4096)%Z).
          { rewrite <- Hpuv.
            rewrite (pgroundup_unsigned oldsz
                       ltac:(change (2 ^ 64)%Z with 18446744073709551616%Z;
                             lia)).
            pose proof (Z.div_mod (bv_unsigned oldsz + 4095) 4096
                          ltac:(lia)) as Hd. lia. }
          assert (Hpe : (((bv_unsigned newsz + 4095) / 4096) * 4096
                         = ((bv_unsigned oldsz + 4095) / 4096) * 4096)%Z).
          { pose proof (Z.div_mod (bv_unsigned newsz + 4095) 4096
                          ltac:(lia)) as Hd2.
            pose proof (Z.mod_pos_bound (bv_unsigned newsz + 4095) 4096
                          ltac:(lia)) as Hbb2.
            pose proof (Z.div_mod (bv_unsigned oldsz + 4095) 4096
                          ltac:(lia)) as Hd1.
            pose proof (Z.mod_pos_bound (bv_unsigned oldsz + 4095) 4096
                          ltac:(lia)) as Hbb1.
            assert (Hoinz : (bv_unsigned oldsz <= bv_unsigned newsz)%Z)
              by (rewrite !uint_unsigned in Hoin; exact Hoin).
            pose proof (Z.div_le_mono (bv_unsigned oldsz + 4095)
                          (bv_unsigned newsz + 4095) 4096 ltac:(lia)
                          ltac:(lia)) as Hm.
            clear -Hd1 Hd2 Hbb1 Hbb2 Hm Hnzle Hpuq Hnz. lia. }
          rewrite Hpe. reflexivity. }
        iEval (rewrite (proc_ptm_sz_cong P (uint oldsz) (uint newsz) Mv Hlvn))
          in "Hpt".
        rewrite (umem_grow_id Mv (uint newsz)
                   ltac:(intros a Ha; apply HMdom; right; by apply Hlvn)).
        iExact "Hpt". } }

    (* ---- PGROUNDUP(oldsz) < newsz: the loop runs ---- *)
    assert (Hpultnz : (pu < nz)%Z).
    { rewrite HR10s2 HR10a2 in Hbg. unfold zopz0zKzJ_u in Hbg.
      rewrite Z.geb_leb in Hbg. apply Z.leb_gt in Hbg.
      rewrite !uint_unsigned in Hbg. rewrite Hnz. rewrite <- Hpuv. exact Hbg. }
    assert (Hnval : n = Z.to_nat ((nz - pu + 4095) / 4096)).
    { rewrite Hnd. unfold uvma_np. rewrite Hpuv. rewrite <- Hnz. reflexivity. }
    assert (Hnchar : forall j : nat, (pu + 4096 * Z.of_nat j < nz)%Z <-> (j < n)%nat).
    { intros j. rewrite Hnval. apply ua_z_nchar. apply ua_z_np_pos. exact Hpultnz. }
    assert (Hn1 : (1 <= n)%nat).
    { assert (Hz0 : (pu + 4096 * Z.of_nat 0 < nz)%Z)
        by (clear -Hpultnz; change (Z.of_nat 0) with 0%Z; lia).
      pose proof (proj1 (Hnchar 0%nat) Hz0) as Hx. clear -Hx. lia. }
    assert (Hsum0 : (0 + n = n)%nat) by (clear -Hn1; lia).
    iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x26))
              (mword_of_int 128 : mword 13) Ra2 Rs2 R10 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) ltac:(rgne; rgne; exact Hbg)
              with "Hcg Hpc []").
    { iApply (uai_26 with "Htext"). }
    iIntros (CIDu80 Hsu80) "Hcg Hpc".
    assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x26) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmalloc + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2a) in "Hpc".
    (* +0x2a c.sdsp s1,56(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x2a)) (mword_of_int 7 : mword 6) Rs1
              R10 (K - 10)%nat u56 b with "Hcg Hpc [] [Hk3]").
    { iApply (uai_2a with "Htext"). }
    { iEval (rewrite HR10sp Hb3). iExact "Hk3". }
    iIntros (CIDu81 Hsu81) "Hcg Hpc Hk3". iEval (rewrite HR10sp Hb3) in "Hk3".
    assert (HR10s1 : R10 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (apply HR10thr; vm_compute; first [reflexivity | discriminate]).
    iEval (rgne; rewrite HR10s1) in "Hk3".
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x2a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* +0x2c c.sdsp s3,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x2c)) (mword_of_int 5 : mword 6) Rs3
              R10 (K - 10)%nat u40 b with "Hcg Hpc [] [Hk5]").
    { iApply (uai_2c with "Htext"). }
    { iEval (rewrite HR10sp Hb5). iExact "Hk5". }
    iIntros (CIDu82 Hsu82) "Hcg Hpc Hk5". iEval (rewrite HR10sp Hb5) in "Hk5".
    assert (HR10s3 : R10 !!! Regidx Rs3 = mm !!! Regidx Rs3)
      by (apply HR10thr; vm_compute; first [reflexivity | discriminate]).
    iEval (rgne; rewrite HR10s3) in "Hk5".
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x2c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    (* +0x2e c.sdsp s6,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x2e)) (mword_of_int 2 : mword 6) Rs6
              R10 (K - 10)%nat u16 b with "Hcg Hpc [] [Hk8]").
    { iApply (uai_2e with "Htext"). }
    { iEval (rewrite HR10sp Hb8). iExact "Hk8". }
    iIntros (CIDu83 Hsu83) "Hcg Hpc Hk8". iEval (rewrite HR10sp Hb8) in "Hk8".
    assert (HR10s6 : R10 !!! Regidx Rs6 = mm !!! Regidx Rs6)
      by (apply HR10thr; vm_compute; first [reflexivity | discriminate]).
    iEval (rgne; rewrite HR10s6) in "Hk8".
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x2e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    (* +0x30 c.lui s3,0x1 *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x30)) Rs3
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              R10 (K - 10)%nat b ltac:(vm_compute; discriminate)
              ltac:(rdok) lui_4096 with "Hcg Hpc []").
    { iApply (uai_30 with "Htext"). }
    iIntros (CIDu84 Hsu84) "Hcg Hpc".
    set (R11 := <[Regidx Rs3 := regval_into_reg (mword_of_int 4096 : mword 64)]> R10).
    assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x30) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmalloc + 0x32)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp32) in "Hpc".
    (* +0x32 ori s6,a3,18 *)
    assert (HR11ori : or_vec (R11 !!! Regidx Ra3)
                        (sign_extend' 64 (mword_of_int 18 : mword 12))
                      = (mword_of_int (Z.lor xperm 18) : mword 64)).
    { rewrite /R11. rewrite upd_ne; [| reg_neq]. rewrite HR10a3.
      apply uvm_perm_ori18. exact Hxrng. }
    iApply (wp_ori_s_sconf (mword_of_int (KernelSyms.uvmalloc + 0x32)) Rs6 Ra3
              (mword_of_int 18 : mword 12) (mword_of_int (Z.lor xperm 18) : mword 64)
              R11 (K - 10)%nat b ltac:(vm_compute; discriminate)
              ltac:(rdok) ltac:(rgne; exact HR11ori) with "Hcg Hpc []").
    { iApply (uai_32 with "Htext"). }
    iIntros (CIDu85 Hsu85) "Hcg Hpc".
    set (R12 := <[Regidx Rs6 := regval_into_reg
                   (mword_of_int (Z.lor xperm 18) : mword 64)]> R11).
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.uvmalloc + 0x32) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmalloc + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    (* ---- the loop-head invariant at i = 0 ---- *)
    assert (HR12sp : R12 !!! Regidx csp_rs1 = spr).
    { rewrite /R12 /R11. repeat (rewrite upd_ne; [| reg_neq]). exact HR10sp. }
    assert (HR12s2 : R12 !!! Regidx Rs2 = pgroundup oldsz).
    { rewrite /R12 /R11. repeat (rewrite upd_ne; [| reg_neq]). exact HR10s2. }
    assert (HR12s3 : R12 !!! Regidx Rs3 = (mword_of_int 4096 : mword 64)).
    { rewrite /R12. rewrite upd_ne; [| reg_neq]. rewrite /R11 upd_eq. reflexivity. }
    assert (HR12s4 : R12 !!! Regidx Rs4 = newsz).
    { rewrite /R12 /R11. repeat (rewrite upd_ne; [| reg_neq]). exact HR10s4. }
    assert (HR12s5 : R12 !!! Regidx Rs5 = page_base P.(ud_root)).
    { rewrite /R12 /R11. repeat (rewrite upd_ne; [| reg_neq]). exact HR10s5. }
    assert (HR12s6 : R12 !!! Regidx Rs6 = (mword_of_int (Z.lor xperm 18) : mword 64))
      by (rewrite /R12 upd_eq; reflexivity).
    assert (HR12s7 : R12 !!! Regidx Rs7 = pgroundup oldsz).
    { rewrite /R12 /R11. repeat (rewrite upd_ne; [| reg_neq]). exact HR10s7. }
    assert (HR12thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 ->
              R12 !!! Regidx c = mm !!! Regidx c).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite /R12. rewrite upd_ne; [| ua_thr_ne].
      rewrite /R11. rewrite upd_ne; [| ua_thr_ne].
      apply HR10thr; assumption. }
    assert (Hav0 : bv_unsigned (pgroundup oldsz) = (pu + 4096 * Z.of_nat 0)%Z).
    { rewrite Hpuv. change (Z.of_nat 0) with 0%Z.
      rewrite Z.mul_0_r Z.add_0_r. reflexivity. }
    assert (Hshiftepi : b = false \/ p = zero_reg -> (CIDu85 : CPU) = (CID : CPU)) by wp_next_chain.
    assert (Hexit_shift0 : ⊢ (ua_exit (CID0 := CID) mm P Mv vpn0 n xperm K eb p b lks sp0 spr oldsz newsz -∗
                              ua_exit (CID0 := CIDu85) mm P Mv vpn0 n xperm K eb p b lks sp0 spr oldsz newsz)).
    { rewrite /ua_exit. exact (wp_next_shift Hshiftepi). }
    iDestruct (Hexit_shift0 with "Hepi") as "Hepi".
    iDestruct (cpu_own_transport CID CIDu85 0%nat eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    (* ---- THE ADDRESS BOUND the loop now takes, from whichever disjunct ---- *)
    assert (Hobz : (bv_unsigned oldsz <= uvm_maxsz)%Z).
    { rewrite uvm_maxsz_val. rewrite <- Hov. exact Hobd. }
    assert (Hab : forall (Pj : uptd) (j : nat), proc_pt_wf Pj -> (j < n)%nat ->
              dom Pj.(ud_um) = dom P.(ud_um)
                               ∪ vpn_run (svpn_of (pgroundup oldsz)) j ->
              (pu + 4096 * Z.of_nat j + 4096 <= 274877898752)%Z).
    { intros Pj j Hwfj Hjn Hdomj.
      destruct Hnbd2 as [Hb | Hc].
      - (* TESTED: [a < newsz <= TRAPFRAME], and both ends are page-aligned *)
        apply (ua_z_avfit _ nz).
        + exact (ua_z_avmod pu (Z.of_nat j) Hpumod).
        + exact (proj2 (Hnchar j) Hjn).
        + exact Hb.
      - (* COUNTED: every page below [a] is mapped, and there are only so
           many pages ([UmCovered.v]) *)
        pose proof (uvma_addr_bound P Pj oldsz j Hobz Hwfj Hc Hdomj) as Hbnd.
        rewrite Hpuv in Hbnd. pose proof kmem_maxppn_val. lia. }
    (* the contract's guard is spelled over [bv_unsigned (pgroundup oldsz)]
       and [uvm_maxsz]; the loop's over [pu] and the literal.  One bridge
       rather than a spelling change on either side. *)
    assert (Hfrg : forall j : nat, (j < n)%nat ->
              (pu + 4096 * Z.of_nat j + 4096 <= 274877898752)%Z ->
              P.(ud_um) !! vpn_at (svpn_of (pgroundup oldsz)) j = None).
    { intros j Hj Hb. apply (Hfr j Hj). rewrite Hpuv uvm_maxsz_val. exact Hb. }
    assert (Hpgo : (UserPtTree.pgroundup (uint oldsz) = pu)%Z).
    { rewrite uint_unsigned.
      rewrite (pgroundup_live oldsz
                 ltac:(change (2 ^ 64)%Z with 18446744073709551616%Z; lia)).
      exact Hpuv. }
    (* the invariant starts at [PGROUNDUP(oldsz)]: same live set as [oldsz],
       and everything live there is already recorded, so the grown view IS
       the one we were handed *)
    assert (Hlv0 : forall a : Z,
              uva_live (uint oldsz) a <-> uva_live (pu + 4096 * Z.of_nat 0)%Z a).
    { intros a. rewrite /uva_live Hpgo (ua_pgu_exact pu 0%nat Hpumod Hpu0).
      cbn [Z.of_nat]. rewrite Z.mul_0_r Z.add_0_r. reflexivity. }
    iEval (rewrite (proc_ptm_sz_cong P (uint oldsz) (pu + 4096 * Z.of_nat 0)%Z
                      Mv Hlv0)) in "Hpt".
    assert (Hgrow00 : umem_grow Mv (pu + 4096 * Z.of_nat 0)%Z = Mv)
      by (apply umem_grow_id; intros a Ha; apply HMdom; right; by apply Hlv0).
    iAssert (proc_ptm P (pu + 4096 * Z.of_nat 0)%Z
               (umem_grow Mv (pu + 4096 * Z.of_nat 0)%Z)) with "[Hpt]" as "Hpt".
    { rewrite Hgrow00. iExact "Hpt". }
    iApply (ua_loop γa mm P Mv xperm K eb p sp0 spr oldsz newsz pu nz n b lks
              HK Hxrng Hperm Hb3 Hb5 Hb8 Hpuv (eq_sym Hnz) Hpumod Hpu0 Hab Hoin
              HMdom Hpgo Hnchar Hfrg
              Hbelow
              n 0%nat CIDu85 P R12 (pgroundup oldsz) Hsum0 Hn1 Hav0
              (uptd_ext_refl P) (dom_run_0 (dom P.(ud_um)) (svpn_of (pgroundup oldsz)))
              ltac:(rewrite vpn_run_0; intros v Hv;
                    exfalso; exact (not_elem_of_empty v Hv))
              HR12sp HR12s2 HR12s3 HR12s4 HR12s5 HR12s6 HR12s7 HR12thr
              with "Hcg Hcnt Htext Hpc Hpt Henv Hk3 Hk5 Hk8 Hepi").
  Qed.

  (* ...and the EXISTENTIAL-[M] corollary: every current caller speaks it,
     and none of them cares what the new pages read as. *)
  Lemma wp_uvmalloc_sconf
      (γa : gname) (mm : regfile)
      (P : uptd) (xperm : Z) (K : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string)
    : wp_uvmalloc_sconf_body γa mm P xperm K eb p b lks.
  Proof.
    cbv beta delta [wp_uvmalloc_sconf_body].
    intros pcE oldsz newsz vpn0 n ret_tgt HK Htp Hroot Hxp Hxrng Hperm
           Hobd Hnbd Hfr Hbelow.
    iIntros "Hcg Hcnt #Htext Hpc Hpt #Henv Hcont".
    iEval (rewrite (proc_pt_ptm P (uint oldsz))) in "Hpt".
    iDestruct "Hpt" as (Mv) "Hpt".
    iApply (wp_uvmalloc_mem_sconf γa mm P Mv xperm K eb p b lks
              HK Htp Hroot Hxp Hxrng Hperm Hobd Hnbd Hfr Hbelow
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    rewrite /wp_next. iIntros (CIDx) "%Hsx".
    iSpecialize ("Hcont" $! CIDx with "[]"); [iPureIntro; exact Hsx|].
    iIntros (mr) "Hcg Hcnt Hpc %Hcs Hpay".
    iApply ("Hcont" $! mr with "Hcg Hcnt Hpc [%] [Hpay]"); [exact Hcs |].
    iDestruct "Hpay" as "[(%Hz & Hp) | Hs]".
    - iLeft. iSplitR; [iPureIntro; exact Hz |].
      iApply (proc_ptm_pt with "Hp").
    - iRight. iDestruct "Hs" as (P' rsz) "(%Hx & %Hd & %Hl & %Hr & %Ha & Hp)".
      iExists P'.
      iSplitR; [iPureIntro; exact Hx |].
      iSplitR; [iPureIntro; exact Hd |].
      iSplitR; [iPureIntro; exact Hl |].
      iSplitR.
      { iPureIntro. rewrite Ha. exact Hr. }
      iApply (proc_ptm_pt with "Hp").
  Qed.

End ProofUvmalloc.

End UvmallocProof.
