(* ProofUvmcopy.v -- uvmcopy() over the SIE-agnostic sconf world.

     int uvmcopy(pagetable_t old, pagetable_t new, uint64 sz)
     {
       for (i = 0; i < sz; i += PGSIZE) {
         if ((pte = walk(old, i, 0)) == 0)  continue;
         if (( *pte & PTE_V) == 0)          continue;
         pa    = PTE2PA( *pte);
         flags = PTE_FLAGS( *pte);
         if ((mem = kalloc()) == 0) goto err;
         memmove(mem, (char * )pa, PGSIZE);
         if (mappages(new, i, PGSIZE, (uint64)mem, flags) != 0) {
           kfree(mem); goto err;
         }
       }
       return 0;
     err:
       uvmunmap(new, 0, i / PGSIZE, 1);
       return -1;
     }

   Spec of record: SpecUvmcopy.v -- the ONE function taking TWO tables, both
   at the [proc_pt] altitude.  Read its header for the design (the copied
   permission, the pointwise success arm and the A/D subtlety).

   FOUR STRUCTURAL POINTS.

   1. THE FRAMELESS EARLY RETURN.  +0x00 is a 2-byte [c.beqz a2] taken BEFORE
      the push, so the [sz == 0] arm at +0x96 returns 0 with sp untouched and
      never meets the epilogue.  That is the success arm at [n = 0].

   2. THE LOOP IS ENTERED AT ITS HEAD, not at its test: +0x22 is a [c.j] to
      the head +0x2a, and the exit test at +0x26 is only reached through the
      back edge at +0x24.  Since [sz != 0] on this path, [n >= 1], so
      [uc_loop] is a plain induction on the remaining count (no fuel -- the
      cursor advances by exactly one page per iteration).

   3. TWO JOINS PER ITERATION, ONE PER FUNCTION.  Inside the body, three arms
      reach the back edge at +0x24 (walk found no slot, the slot is invalid,
      mappages succeeded), so the loop body holds ONE [iAssert]ed [TAIL]
      continuation.  Outside, the epilogue at +0x80 is reached by the error
      arm (+0x7c) and by the success arm (+0x7e); that is [uc_exit], taken
      as an [iAssert] in the wrapper and threaded into the loop as a wand
      ARGUMENT.

   4. THE err BLOCK IS ONE LEMMA.  gcc emitted it once (+0x6c..+0x7c) but it
      is reached from TWO places -- kalloc returned 0 (+0x46 taken) and
      mappages failed (+0x64 falls through into the kfree at +0x66..+0x68,
      whose return address IS +0x6c).  [uc_err] is that block, [Qed]-sealed,
      taking [uc_exit] as a wand argument; the two entries differ only in
      whether [mem] was freed first.

   THE A/D BRIDGE ([uc_ad_bridge], SS1) is the one genuinely new pure step:
   the code copies the flag byte of [ *pte], i.e. of [pte_set_ad w a d] for
   the parent's canonical leaf [w], so what mappages inserts is
   [uvm_pte (pte_flags10 (pte_set_ad w a d)) r] while the contract records
   [pte_set_ad (uvm_pte (pte_flags10 w) r) a d].  Those are EQUAL (both are
   [mk_pte (ppn r)] at the flag byte of [w] masked at bits 6/7 and re-or'ed
   with a<<6 | d<<7). *)
Set Printing Depth 40.
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import IntrDefs WpSmodeIntr.
Require Import WpNext.
Require Import WpLock.
Require Import KallocInv.
Require Import ByteCursor ByteBuf.
Require Import PtAdBits.
Require Import CommonWalk PtTree.
Require Import KptExecMap TrampPt.
Require Import KptTree.
Require Import PtBuild.
Require Import UptTree UserPtTree.
Require Import CpuOwn.
Require Import KvmSpec.
Require Import ProcPt ProcPtOwn.
Require Import CodeUvmcopy.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import SpecWalk SpecKalloc SpecMemmove SpecMappages SpecKfree SpecUvmunmap.
Require Import SpecUvmcopy.
Require Import KernelRvcDecode.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* SS1  uvmcopy's OWN pure arithmetic, and the A/D bridge.                *)
(*                                                                        *)
(*   Kept STRICTLY [mword]-free where it is [Z] arithmetic: this file's    *)
(*   transitive [bitvector.tactics] import installs a zify hook that makes *)
(*   [lia] answer Cannot-find-witness on any goal mentioning              *)
(*   [bv_unsigned] (durable-notes.md).                                    *)
(* ===================================================================== *)

(* the loop-trip characterisation.  [i = 4096*j] is below [sz] exactly for
   the first [(sz+4095)/4096 = uvm_np sz] values of [j]. *)
Lemma uc_z_iter (nz j : Z) : (4096 * j < nz) <-> (j < (nz + 4095) / 4096).
Proof.
  pose proof (Z_div_mod_eq_full (nz + 4095) 4096) as Heq.
  assert (Hp : 0 < 4096) by lia.
  pose proof (Z.mod_pos_bound (nz + 4095) 4096 Hp) as Hmod.
  split; intros H; lia.
Qed.

Lemma uc_z_np_pos (nz : Z) : 0 <= nz -> 0 <= (nz + 4095) / 4096.
Proof. intros H. apply Z.div_pos; lia. Qed.

Lemma uc_z_nchar (nz : Z) (j : nat) :
  0 <= (nz + 4095) / 4096 ->
  ((4096 * Z.of_nat j < nz) <-> (j < Z.to_nat ((nz + 4095) / 4096))%nat).
Proof. intros Hq. rewrite (uc_z_iter nz (Z.of_nat j)). lia. Qed.

(* the run never exceeds the user region: [ceil(uvm_maxsz/4096) = tf_vpn] *)
Lemma uc_z_np_bound (nz : Z) : nz <= 274877898752 -> (nz + 4095) / 4096 < 67108863.
Proof. intros H. apply Z.div_lt_upper_bound; lia. Qed.

Lemma uc_z_np_zero : Z.to_nat ((0 + 4095) / 4096) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma uc_z_div4096 (j : Z) : 4096 * j / 4096 = j.
Proof.
  assert (Hr : 4096 * j = j * 4096) by ring.
  rewrite Hr. apply Z.div_mul. lia.
Qed.

Lemma uc_z_svpn (j : Z) :
  0 <= j -> j < 134217728 -> (4096 * j / 4096) mod 134217728 = j.
Proof. intros H0 H1. rewrite uc_z_div4096. apply Z.mod_small. lia. Qed.

Lemma uc_z_mod4096 (j : Z) : (4096 * j) mod 4096 = 0.
Proof.
  assert (Hr : 4096 * j = 0 + j * 4096) by ring.
  rewrite Hr. rewrite Z.mod_add; [| lia]. reflexivity.
Qed.

(* a page below TRAPFRAME has a vpn strictly below [tf_vpn] = 2^26 - 2 *)
Lemma uc_z_vpn_lt (j : Z) : 0 <= j -> 4096 * j < 274877898752 -> j < 67108862.
Proof. intros H0 H1. lia. Qed.

Lemma uc_z_small (x : Z) : 0 <= x < 1024 -> 0 <= x < 18446744073709551616.
Proof. lia. Qed.

(* mappages' one-page pa range side condition *)
Lemma uc_z_run_pa (x : Z) : x < 2281701376 -> x + Z.of_nat 1 * 4096 < 72057594037927936.
Proof. lia. Qed.

Lemma uc_z_va_bnd (j : Z) :
  0 <= j -> 4096 * j < 274877898752 -> 4096 * j + Z.of_nat 1 * 4096 <= 274877906944.
Proof. lia. Qed.

Lemma uc_z_no_wrap (j : Z) :
  0 <= j -> 4096 * j < 274877898752 -> 4096 * j + 4096 < 18446744073709551616.
Proof. lia. Qed.

(* ---- the vpn of the loop cursor ------------------------------------- *)

Lemma uc_vpn0_unsigned : bv_unsigned (svpn_of (mword_of_int 0 : mword 64)) = 0.
Proof. rewrite svpn_of_unsigned_gen. rewrite moi64_unsigned. vm_compute. reflexivity. Qed.

(* ---- PTE_FLAGS( *pte) is the [andi rd,rs,1023] the code emits -------- *)

Lemma uc_andi1023 (w : mword 64) :
  and_vec w (sign_extend' 64 (mword_of_int 1023 : mword 12))
  = (mword_of_int (pte_flags10 w) : mword 64).
Proof.
  pose proof (pte_flags10_range w) as Hr. unfold pte_flags10 in Hr.
  assert (Hm : bv_modulus 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (H1023 : bv_unsigned (sign_extend' 64 (mword_of_int 1023 : mword 12) : mword 64)
                  = 1023) by (vm_compute; reflexivity).
  assert (Hsm : (0 <= Z.land (bv_unsigned w) 1023 < bv_modulus 64)%Z)
    by (rewrite Hm; exact (uc_z_small _ Hr)).
  apply bv_eq. rewrite and_vec64_unsigned. rewrite H1023.
  rewrite moi64_unsigned. unfold pte_flags10.
  rewrite (bv_wrap_small 64 _ Hsm). reflexivity.
Qed.

(* ===================================================================== *)
(* SS1b  THE A/D BRIDGE.                                                  *)
(*                                                                        *)
(*   What mappages inserts is [uvm_pte (pte_flags10 ( *pte)) r] where      *)
(*   [ *pte = pte_set_ad w a d]; what the contract records is             *)
(*   [pte_set_ad (uvm_pte (pte_flags10 w) r) a d].  They are equal.        *)
(* ===================================================================== *)

(* [pte_set_ad] on a [mk_pte] rewrites the flag CONSTANT (the [uvm_flags]
   transform), for a flag byte that already has V set. *)
Lemma uc_mkpte_ad (p : mword 44) (f : Z) (a d : mword 1) :
  (0 <= f < 1024)%Z -> Z.lor f 1 = f ->
  pte_set_ad (mk_pte p f) a d = mk_pte p (uvm_flags f a d).
Proof.
  intros Hf H1. unfold uvm_flags. rewrite H1. unfold mk_pte.
  apply pte_set_ad_zext_concat. exact Hf.
Qed.

Lemma uc_flags_ad_mk (p : mword 44) (f : Z) (a d : mword 1) :
  (0 <= f < 1024)%Z -> Z.lor f 1 = f ->
  pte_flags10 (pte_set_ad (mk_pte p f) a d) = uvm_flags f a d.
Proof.
  intros Hf H1. rewrite (uc_mkpte_ad p f a d Hf H1).
  apply pte_flags10_mk. exact (uvm_flags_bound f a d Hf).
Qed.

Lemma uc_ad_bridge (w r : mword 64) (a d : mword 1) :
  pte_valid w -> (bv_unsigned w < 18014398509481984)%Z ->
  pte_valid (pte_set_ad w a d) ->
  uvm_pte (pte_flags10 (pte_set_ad w a d)) r
  = pte_set_ad (uvm_pte (pte_flags10 w) r) a d.
Proof.
  intros Hv Hlt Hv'.
  pose proof (pte_flags10_range w) as Hg.
  pose proof (pte_flags10_lor1 w Hv) as H1.
  assert (Hg1 : (0 <= Z.lor (pte_flags10 w) 1 < 1024)%Z) by (rewrite H1; exact Hg).
  assert (Hfe : pte_flags10 (pte_set_ad w a d) = uvm_flags (pte_flags10 w) a d).
  { transitivity (pte_flags10 (pte_set_ad (mk_pte (pte_ppn w) (pte_flags10 w)) a d)).
    - rewrite <- (mk_pte_eta w Hlt). reflexivity.
    - exact (uc_flags_ad_mk (pte_ppn w) (pte_flags10 w) a d Hg H1). }
  rewrite (uvm_variant_mk (pte_flags10 w) r a d Hg1).
  rewrite uvm_pte_mk. rewrite (pte_flags10_lor1 _ Hv'). rewrite Hfe. reflexivity.
Qed.

(* THE PERMISSION CONTRACT for the flag byte the code actually reads: the
   invariant states its clauses about the CANONICAL leaf [w], the code reads
   [pte_set_ad w a d], and A/D write-backs absorb ([pte_set_ad_absorb]). *)
Lemma uc_perm_ok (w : mword 64) (a d : mword 1) :
  (forall a' d' : mword 1,
     pte_valid (pte_set_ad w a' d') /\ pte_leaf (pte_set_ad w a' d') /\
     pte_no_napot (pte_set_ad w a' d') /\ pte_pbmt0 (pte_set_ad w a' d')) ->
  (forall acc : MemoryAccessType mem_payload,
     u_acc acc -> uleaf_ok acc w \/ uleaf_denied acc w) ->
  uvm_perm_ok (pte_flags10 (pte_set_ad w a d)).
Proof.
  intros H1 H2. apply uvm_perm_ok_of_leaf.
  - intros a' d'. rewrite pte_set_ad_absorb. exact (H1 a' d').
  - intros acc Hu. destruct (H2 acc Hu) as [H | H]; [left | right];
      intros a' d' mxr ds; rewrite pte_set_ad_absorb; exact (H a' d' mxr ds).
Qed.

(* ===================================================================== *)
(* SS1c  The map-shape bookkeeping the loop invariant carries.            *)
(* ===================================================================== *)

(* the callee-saved registers uvmcopy never touches: all nine saved ones
   (sp, s0..s7) are written, so they are all excluded. *)
Definition uc_thr (mm m : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) -> c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) -> c <> (mword_of_int 19 : mword 5) ->
    c <> (mword_of_int 20 : mword 5) -> c <> (mword_of_int 21 : mword 5) ->
    c <> (mword_of_int 22 : mword 5) -> c <> (mword_of_int 23 : mword 5) ->
    m !!! Regidx c = mm !!! Regidx c.

(* the per-vpn shape of the success postcondition, at ONE index *)
Definition uc_at (Pold Pnew P' : uptd) (vpn0 : mword 27) (i : nat) : Prop :=
  match Pold.(ud_um) !! vpn_at vpn0 i with
  | None => P'.(ud_um) !! vpn_at vpn0 i = Pnew.(ud_um) !! vpn_at vpn0 i
  | Some w => exists (r w' : mword 64) (a d : mword 1),
      page_valid r /\
      P'.(ud_um) !! vpn_at vpn0 i = Some w' /\
      w' = pte_set_ad (uvm_pte (pte_flags10 w) r) a d
  end.

(* "the child's map agrees with the one we were given outside the prefix"
   is what supplies [um_del_run_restore_sub]'s domain premise *)
Lemma uc_dom_sub (um um' : gmap (mword 27) (mword 64)) (vpn0 : mword 27) (j : nat) :
  (forall v, v ∉ vpn_run vpn0 j -> um' !! v = um !! v) ->
  dom um' ⊆ dom um ∪ vpn_run vpn0 j.
Proof.
  intros Hout v Hv. apply elem_of_dom in Hv.
  destruct (decide (v ∈ vpn_run vpn0 j)) as [Hin | Hnin].
  - apply elem_of_union_r. exact Hin.
  - apply elem_of_union_l. apply elem_of_dom.
    rewrite <- (Hout v Hnin). exact Hv.
Qed.

(* ===================================================================== *)
(* SS2  The postcondition payload and the +0x80 join contract.            *)
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

Section UvmcopyDefs.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* SpecUvmcopy's post disjunction, at an abstract return value *)
  Definition uc_pay (Pold Pnew : uptd) (vpn0 : mword 27) (n : nat)
      (res : mword 64) : iProp Σ :=
    ((⌜res = (mword_of_int (-1) : mword 64)⌝ ∗ proc_pt Pnew)
     ∨ (∃ P' : uptd,
          ⌜res = (mword_of_int 0 : mword 64)⌝ ∗
          ⌜uptd_ext Pnew P'⌝ ∗
          ⌜forall vpn, vpn ∉ vpn_run vpn0 n ->
             P'.(ud_um) !! vpn = Pnew.(ud_um) !! vpn⌝ ∗
          ⌜forall i, (i < n)%nat -> uc_at Pold Pnew P' vpn0 i⌝ ∗
          proc_pt P'))%I.

  (* what both long arms hand the epilogue at +0x80.  Threaded across the
     recursion exactly like the top-level [Hcont]: it is a [wp_next]-shaped
     resource carrying its OWN entry hart [CID0] (not the section's ambient
     one), re-anchored at each call site via [wp_next_shift] rather than
     being consumed at the hart it was built at. *)
  Definition uc_exit `{CID0 : CpuId} (mm : regfile)
      (Pold Pnew : uptd) (vpn0 : mword 27) (n K : nat) (eb : bool)
      (p : mword 64) (spr : mword 64) (ilvl : nat) (b : bool) (lks : gset string) : iProp Σ :=
    wp_next (CID0 := CID0) b p (fun (CID : CpuId) =>
      ( ∀ (mj : regfile) (res : mword 64),
      ⌜ mj !!! Regidx csp_rs1 = spr
        /\ mj !!! Regidx URa0 = res
        /\ uc_thr mm mj ⌝ -∗
      sie_cap_gpr kt mj (K - 10)%nat b p -∗
      cpu_own ilvl eb p b lks -∗
      pc_is (mword_of_int (KernelSyms.uvmcopy + 0x80) : mword 64) -∗
      proc_pt Pold -∗
      uc_pay Pold Pnew vpn0 n res -∗
      WP (Loop : expr riscv_lang) )%I).

End UvmcopyDefs.

(* ===================================================================== *)
(* SS3  THE WHOLE FUNCTION.                                               *)
(* ===================================================================== *)

Module UvmcopyProof (WalkNoalloc : WALK_NOALLOC) (Kalloc : KALLOC)
                    (Memmove : MEMMOVE) (Mappages : MAPPAGES)
                    (Kfree : KFREE) (Uvmunmap : UVMUNMAP)
  : UVMCOPY.

Section ProofUvmcopy.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
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

  (* peel a register lookup through the insert tower via the [upd_eq]/[upd_ne]
     LEMMAS, one layer at a time (optimization.md's [peel_reg]). *)
  Ltac lkp :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l;
    first [ reflexivity | assumption ].

  Ltac lkp0 :=
    repeat first
      [ rewrite upd_eq
      | rewrite upd_ne; [| reg_neq]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ];
    repeat rewrite add_vec_zero_l.

  (* the callee-saved-agreement peel (optimization.md: NEVER [congruence] in a
     [repeat]-driven peel). *)
  Ltac uc_thr_ne :=
    first
      [ lazymatch goal with
        | Hcs : is_cs_idx _ = true |- _ =>
            refine (not_eq_sym (is_cs_idx_true_neq _ _ _ Hcs));
            vm_compute; reflexivity
        end
      | lazymatch goal with
        | |- Regidx ?x <> Regidx ?y =>
            match goal with
            | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
            end
        end ].

  Ltac uc_thr_peel :=
    repeat first
      [ rewrite upd_ne; [| uc_thr_ne]
      | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ].

  (* ------------------------------------------------------------------ *)
  (* THE ROLLBACK, as a pure [proc_pt] move: uvmunmap deleted exactly the *)
  (* run the loop had mapped -- a SUBSET of [vpn_run] (only the vpns the   *)
  (* parent had), which is why the SUBSET restore law is the one needed.   *)
  (* ------------------------------------------------------------------ *)
  Local Lemma uc_restore (Pnew Pj : uptd) (vpn0 : mword 27) (j : nat) :
    uptd_ext Pnew Pj ->
    (forall v, v ∉ vpn_run vpn0 j -> Pj.(ud_um) !! v = Pnew.(ud_um) !! v) ->
    (forall i, (i < j)%nat -> Pnew.(ud_um) !! vpn_at vpn0 i = None) ->
    proc_pt (uptd_del_run Pj vpn0 j) ⊢ proc_pt Pnew.
  Proof.
    intros (Hr & Ht & Hsub) Hout Hfr.
    assert (Hum : um_del_run Pj.(ud_um) vpn0 j = Pnew.(ud_um))
      by exact (um_del_run_restore_sub Pnew.(ud_um) Pj.(ud_um) vpn0 j Hsub
                  (uc_dom_sub Pnew.(ud_um) Pj.(ud_um) vpn0 j Hout) Hfr).
    assert (Heq : proc_pt (uptd_del_run Pj vpn0 j) ⊣⊢ proc_pt Pnew).
    { apply proc_pt_data_irrel; unfold uptd_del_run;
        cbn [ud_root ud_tfp ud_um]; assumption. }
    rewrite Heq. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* THE err BLOCK (+0x6c .. +0x7c), reached from BOTH failure arms.      *)
  (* ------------------------------------------------------------------ *)
  (* DECOMPOSED: takes its OWN [CID0] (the hart uc_loop's callers reach it
     at), not the section's ambient one.  [SpecUvmunmap.v]'s entry-side tp
     premise is gone (HartTp.v -- the map's tp slot is IGNORED), so no
     re-tagging is needed before the Uvmunmap call below. *)
  Local Lemma uc_err `{CID0 : CpuId} (γa : gname) (mm : regfile)
      (Pold Pnew Pj : uptd) (vpn0 : mword 27) (n j : nat) (K : nat)
      (eb : bool) (p : mword 64) (spr iv : mword 64)
      (M : regfile) (ilvl : nat) (b : bool) (lks : gset string) :
    (42 <= K)%nat ->
    (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
    svpn_of (mword_of_int 0 : mword 64) = vpn0 ->
    bv_unsigned iv = (4096 * Z.of_nat j)%Z ->
    (4096 * Z.of_nat j <= 274877898752)%Z ->
    uptd_ext Pnew Pj ->
    (forall v, v ∉ vpn_run vpn0 j -> Pj.(ud_um) !! v = Pnew.(ud_um) !! v) ->
    (forall i, (i < j)%nat -> Pnew.(ud_um) !! vpn_at vpn0 i = None) ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx Rs1 = iv ->
    M !!! Regidx Rs7 = page_base Pnew.(ud_root) ->
    uc_thr mm M ->
    (* uc_err's one callee is uvmunmap, whose do_free-!=0 call bottoms out
       at kfree's "kmem" (13) bound; nothing else here touches a lock. *)
    locks_below lks "kmem" ->
    sie_cap_gpr kt M (K - 10)%nat b p -∗
    cpu_own ilvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uvmcopy + 0x6c) : mword 64) -∗
    proc_pt Pold -∗
    proc_pt Pj -∗
    kalloc_env γa None -∗
    uc_exit (kt := kt) mm Pold Pnew vpn0 n K eb p spr ilvl b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hilvl Hvpn0 Hiv Hjb Hext Hout Hfr Hsp Hs1 Hs7 Hthr Hbelow.
    assert (HKuu : (22 <= K - 10)%nat) by (clear -HK; lia).
    iIntros "Hcg Hcnt #Htext Hpc Hpo Hpt #Henv Hexit".
    iPoseProof (uci_6c with "Htext") as "Hi6c".
    iPoseProof (uci_6e with "Htext") as "Hi6e".
    iPoseProof (uci_72 with "Htext") as "Hi72".
    iPoseProof (uci_74 with "Htext") as "Hi74".
    iPoseProof (uci_76 with "Htext") as "Hi76".
    iPoseProof (uci_7a with "Htext") as "Hi7a".
    iPoseProof (uci_7c with "Htext") as "Hi7c".
    (* --- +0x6c c.li a3,1 --- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x6c)) Ra3
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64) M (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi6c").
    iIntros (CIDe1 Hse1) "Hcg Hpc".
    set (N1 := <[Regidx Ra3 := regval_into_reg (mword_of_int 1 : mword 64)]> M).
    assert (Hq6e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x6c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x6e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq6e) in "Hpc".
    (* --- +0x6e srli a2,s1,0xc --- *)
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x6e)) Ra2 Rs1
              (mword_of_int 12 : mword 6) N1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6e").
    iIntros (CIDe2 Hse2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Ra2 := regval_into_reg
                  (shift_bits_right (N1 !!! Regidx Rs1)
                     (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> N1).
    assert (Hq72 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x6e) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmcopy + 0x72)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq72) in "Hpc".
    (* --- +0x72 c.li a1,0 --- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x72)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) N2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi72").
    iIntros (CIDe3 Hse3) "Hcg Hpc".
    set (N3 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> N2).
    assert (Hq74 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x72) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x74)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq74) in "Hpc".
    (* --- +0x74 c.mv a0,s7 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x74)) Ra0 Rs7 N3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi74").
    iIntros (CIDe4 Hse4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (N3 !!! Regidx Rs7))]> N3).
    assert (Hq76 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x74) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x76)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq76) in "Hpc".
    (* --- +0x76 jal ra,uvmunmap --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x76)) Rra
              (mword_of_int 2096516 : mword 21) N4 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi76").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x76) : mword 64) 4)]> N4).
    assert (Htgtuu : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x76) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096516 : mword 21))
                     = mword_of_int KernelSyms.uvmunmap)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtuu) in "Hpc".
    (* --- the uvmunmap argument facts --- *)
    assert (HN5ra : N5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x76) : mword 64) 4)
      by (rewrite /N5 upd_eq; reflexivity).
    assert (HN5a0 : N5 !!! Regidx Ra0 = page_base Pj.(ud_root)).
    { rewrite (proj1 Hext). rewrite /N5. rewrite upd_ne; [| reg_neq].
      rewrite /N4 upd_eq. rewrite add_vec_zero_l.
      rewrite /N3. rewrite upd_ne; [| reg_neq].
      rewrite /N2. rewrite upd_ne; [| reg_neq].
      rewrite /N1. rewrite upd_ne; [| reg_neq]. exact Hs7. }
    assert (HN5a1 : N5 !!! Regidx Ra1 = (mword_of_int 0 : mword 64)).
    { rewrite /N5. rewrite upd_ne; [| reg_neq].
      rewrite /N4. rewrite upd_ne; [| reg_neq].
      rewrite /N3 upd_eq. reflexivity. }
    assert (HN5a2 : N5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat j) : mword 64)).
    { rewrite /N5. rewrite upd_ne; [| reg_neq].
      rewrite /N4. rewrite upd_ne; [| reg_neq].
      rewrite /N3. rewrite upd_ne; [| reg_neq].
      rewrite /N2 upd_eq. rewrite srli12_div4096.
      assert (HN1s1 : N1 !!! Regidx Rs1 = iv)
        by (rewrite /N1; rewrite upd_ne; [exact Hs1 | reg_neq]).
      rewrite HN1s1 Hiv uc_z_div4096. reflexivity. }
    assert (HN5a3 : N5 !!! Regidx Ra3 = (mword_of_int 1 : mword 64)).
    { rewrite /N5. rewrite upd_ne; [| reg_neq].
      rewrite /N4. rewrite upd_ne; [| reg_neq].
      rewrite /N3. rewrite upd_ne; [| reg_neq].
      rewrite /N2. rewrite upd_ne; [| reg_neq].
      rewrite /N1 upd_eq. reflexivity. }
    assert (HN5sp : N5 !!! Regidx csp_rs1 = spr).
    { rewrite /N5 /N4 /N3 /N2 /N1. repeat (rewrite upd_ne; [| reg_neq]). exact Hsp. }
    assert (HN5thr : uc_thr mm N5).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      uc_thr_peel. apply Hthr; assumption. }
    iDestruct (cpu_own_transport CID0 CIDe5 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    assert (Hual : subrange_vec_dec (N5 !!! Regidx Ra1) 11 0 = (zeros' 12 : mword 12)).
    { rewrite HN5a1. apply bv_eq. vm_compute. reflexivity. }
    assert (Hua3 : N5 !!! Regidx Ra3 <> (mword_of_int 0 : mword 64)).
    { rewrite HN5a3. intro He. apply (f_equal bv_unsigned) in He.
      vm_compute in He. discriminate. }
    assert (Hurng : (uint (N5 !!! Regidx Ra1) + Z.of_nat j * 4096 <= uvm_maxsz)%Z).
    { rewrite HN5a1 uvm_maxsz_val.
      assert (Hu0 : uint (mword_of_int 0 : mword 64) = 0%Z) by (vm_compute; reflexivity).
      rewrite Hu0. clear -Hjb. lia. }
    iApply (Uvmunmap.wp_uvmunmap_sconf kt γa N5 Pj j (K - 10)%nat eb p ilvl b
              _ HKuu Hilvl HN5a0 Hual HN5a2 Hua3 Hurng Hbelow
              with "Hcg Hcnt Htext Hpc Hpt Henv").
    all: try lkbelow.
    iIntros (CIDe6 Hse6 mu) "Hcg Hcnt Hpc %Hucs Hpt".
    iEval (rewrite HN5a1 Hvpn0) in "Hpt".
    assert (Hret7a : ret_pc (N5 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmcopy + 0x7a)).
    { rewrite HN5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret7a) in "Hpc".
    assert (Husp : mu !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hucs csp_rs1 ltac:(vm_compute; reflexivity)). exact HN5sp. }
    assert (Huthr : uc_thr mm mu).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hucs c Hc). apply HN5thr; assumption. }
    iDestruct (uc_restore Pnew Pj vpn0 j Hext Hout Hfr with "Hpt") as "Hpt".
    (* --- +0x7a c.li a0,-1 --- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x7a)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64) mu (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi7a").
    iIntros (CIDe7 Hse7) "Hcg Hpc".
    set (N6 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> mu).
    assert (Hq7c : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x7a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x7c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hq7c) in "Hpc".
    (* --- +0x7c c.j +0x04 --- *)
    assert (Hjt7c : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x7c) : mword 64)
              (sign_extend' 64
                 (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.uvmcopy + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x7c))
              (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")))
              N6 (K - 10)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi7c").
    iIntros (CIDe8 Hse8). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hjt7c) in "Hpc".
    iDestruct (cpu_own_transport CIDe6 CIDe8 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    assert (Hshift : b = false \/ p = zero_reg -> (CIDe8 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshift with "Hexit") as "Hexit".
    iSpecialize ("Hexit" $! CIDe8 with "[%]"); [wp_next_chain|].
    iApply ("Hexit" $! N6 (mword_of_int (-1)) with "[%] Hcg Hcnt Hpc Hpo [Hpt]").
    { split_and!.
      - rewrite /N6. rewrite upd_ne; [exact Husp | reg_neq].
      - rewrite /N6 upd_eq. reflexivity.
      - intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
        rewrite /N6. rewrite upd_ne; [| uc_thr_ne]. apply Huthr; assumption. }
    { rewrite /uc_pay. iLeft. iSplitR; [iPureIntro; reflexivity | iExact "Hpt"]. }
  Qed.


  (* ------------------------------------------------------------------ *)
  (* THE LOOP, at its head +0x2a, with [j] pages already handled.         *)
  (* ------------------------------------------------------------------ *)
  (* DECOMPOSED, RECURSIVE: [CID0] sits in the SAME forall clause as the
     other per-iteration state ([rem j Pj M iv]), so [induction rem] below
     auto-generalizes it -- the fuel/index induction recipe from the porting
     guide.  [b] stays a plain outer argument: it never changes across
     iterations.  No [Rtp = cid_word] entry premise: see [sie_cap_gpr_settp]
     above [uc_err] -- nothing in this loop's own body needs it any more. *)
  Local Lemma uc_loop (γa : gname) (mm : regfile)
      (Pold Pnew : uptd) (vpn0 : mword 27) (n K : nat) (eb : bool)
      (p : mword 64) (spr sz : mword 64) (nz : Z) (ilvl : nat) (b : bool) (lks : gset string) :
    (42 <= K)%nat ->
    (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
    svpn_of (mword_of_int 0 : mword 64) = vpn0 ->
    bv_unsigned sz = nz ->
    (nz <= 274877898752)%Z ->
    (forall k : nat, (4096 * Z.of_nat k < nz)%Z <-> (k < n)%nat) ->
    (Z.of_nat n < 67108863)%Z ->
    (forall i, (i < n)%nat -> Pnew.(ud_um) !! vpn_at vpn0 i = None) ->
    forall (rem j : nat) (Pj : uptd) (M : regfile) (iv : mword 64) (CID0 : CpuId),
    (j + rem = n)%nat -> (1 <= rem)%nat ->
    bv_unsigned iv = (4096 * Z.of_nat j)%Z ->
    uptd_ext Pnew Pj ->
    (forall v, v ∉ vpn_run vpn0 j -> Pj.(ud_um) !! v = Pnew.(ud_um) !! v) ->
    (forall i, (i < j)%nat -> uc_at Pold Pnew Pj vpn0 i) ->
    M !!! Regidx csp_rs1 = spr ->
    M !!! Regidx Rs1 = iv ->
    M !!! Regidx Rs4 = (mword_of_int 4096 : mword 64) ->
    M !!! Regidx Rs5 = sz ->
    M !!! Regidx Rs6 = page_base Pold.(ud_root) ->
    M !!! Regidx Rs7 = page_base Pnew.(ud_root) ->
    uc_thr mm M ->
    (* uc_loop's cone reaches kalloc/kfree directly (both bound at "kmem",
       13) and, via [uc_err], kfree again through uvmunmap.  mappages is
       also in the cone but carries no order premise of its own to pass
       (SpecMappages.v/SpecWalk.v -- outside this pass's file list). *)
    locks_below lks "kmem" ->
    sie_cap_gpr kt M (K - 10)%nat b p -∗
    cpu_own ilvl eb p b lks -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.uvmcopy + 0x2a) : mword 64) -∗
    proc_pt Pold -∗
    proc_pt Pj -∗
    kalloc_env γa None -∗
    uc_exit (kt := kt) mm Pold Pnew vpn0 n K eb p spr ilvl b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hilvl Hvpn0 Hsz Hszb Hnchar Hnb Hfresh.
    assert (HKka : (14 <= K - 10)%nat) by (clear -HK; lia).
    assert (HKmm : (2 <= K - 10)%nat) by (clear -HK; lia).
    assert (HKmp : (32 <= K - 10)%nat) by (clear -HK; lia).
    assert (HKwk : (8 <= K - 10)%nat) by (clear -HK; lia).
    assert (Hv0u : bv_unsigned vpn0 = 0%Z) by (rewrite <- Hvpn0; exact uc_vpn0_unsigned).
    intro rem.
    induction rem as [| rem IH];
      intros j Pj M iv CID0 Hsum Hrem Hiv Hext Hout Hfacts
             Hsp Hs1 Hs4 Hs5 Hs6 Hs7 Hthr Hbelow;
      [ exfalso; clear -Hrem; lia |].
    iIntros "Hcg Hcnt #Htext Hpc Hpo Hpt #Henv Hexit".
    iDestruct "Henv" as (γk) "(#Hlock & #Havail)".
    iAssert (kalloc_env γa None) as "#Henv2".
    { iExists γk. iSplitR; [iExact "Hlock" |]. iExact "Havail". }
    iDestruct (sie_cap_gpr_dup_hw_config with "Hcg") as "[Hhwc Hcg]".
    iDestruct "Hhwc" as (hwmisa0 hwmseccfg0 hwpmar0 hwelp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & #Hkmapb)".
    (* ---- the iteration's arithmetic, all up front ---- *)
    assert (Hjn : (j < n)%nat) by (clear -Hsum Hrem; lia).
    pose proof (proj2 (Hnchar j) Hjn) as Hjlt.
    pose proof (Nat2Z.is_nonneg j) as Hj0.
    assert (Hjb : (4096 * Z.of_nat j < 274877898752)%Z) by (clear -Hjlt Hszb; lia).
    pose proof (uc_z_vpn_lt (Z.of_nat j) Hj0 Hjb) as Hvpnlt.
    assert (Hjsmall : (bv_unsigned vpn0 + Z.of_nat j < 134217728)%Z)
      by (rewrite Hv0u; clear -Hvpnlt; lia).
    assert (Hvju : bv_unsigned (vpn_at vpn0 j) = Z.of_nat j).
    { rewrite (vpn_at_unsigned vpn0 j Hjsmall) Hv0u. clear; lia. }
    assert (Hvj : svpn_of iv = vpn_at vpn0 j).
    { apply bv_eq. rewrite svpn_of_unsigned_gen Hiv Hvju.
      apply uc_z_svpn; [exact Hj0 | clear -Hvpnlt; lia]. }
    assert (Hntr : vpn_at vpn0 j <> tramp_vpn).
    { apply vpn_lt_ne. rewrite Hvju tramp_vpn_unsigned. clear -Hvpnlt; lia. }
    assert (Hntf : vpn_at vpn0 j <> tf_vpn).
    { apply vpn_lt_ne. rewrite Hvju tf_vpn_unsigned. clear -Hvpnlt; lia. }
    assert (Hvj26 : (bv_unsigned (vpn_at vpn0 j) < 67108864)%Z)
      by (rewrite Hvju; clear -Hvpnlt; lia).
    assert (Hjrun : Z.of_nat j < 134217728) by (clear -Hvpnlt; lia).
    assert (Hnotin : vpn_at vpn0 j ∉ vpn_run vpn0 j).
    { intros Hin. apply elem_of_vpn_run in Hin. destruct Hin as (i & Hi & He).
      exact (vpn_at_ne vpn0 i j Hi Hjrun (eq_sym He)). }
    assert (Hsubrun : forall v, v ∉ vpn_run vpn0 (S j) -> v ∉ vpn_run vpn0 j).
    { intros v Hv Hin. apply Hv. rewrite vpn_run_S. apply elem_of_union_l. exact Hin. }
    assert (Hpjnone : Pj.(ud_um) !! vpn_at vpn0 j = None).
    { rewrite (Hout _ Hnotin). exact (Hfresh j Hjn). }
    assert (Hivmod : (bv_unsigned iv mod 4096 = 0)%Z)
      by (rewrite Hiv; exact (uc_z_mod4096 (Z.of_nat j))).
    (* ---- the instruction facts ---- *)
    iPoseProof (uci_2a with "Htext") as "Hi2a".
    iPoseProof (uci_2c with "Htext") as "Hi2c".
    iPoseProof (uci_2e with "Htext") as "Hi2e".
    iPoseProof (uci_30 with "Htext") as "Hi30".
    iPoseProof (uci_34 with "Htext") as "Hi34".
    iPoseProof (uci_36 with "Htext") as "Hi36".
    iPoseProof (uci_3a with "Htext") as "Hi3a".
    iPoseProof (uci_3e with "Htext") as "Hi3e".
    iPoseProof (uci_40 with "Htext") as "Hi40".
    iPoseProof (uci_44 with "Htext") as "Hi44".
    iPoseProof (uci_46 with "Htext") as "Hi46".
    iPoseProof (uci_48 with "Htext") as "Hi48".
    iPoseProof (uci_4c with "Htext") as "Hi4c".
    iPoseProof (uci_4e with "Htext") as "Hi4e".
    iPoseProof (uci_50 with "Htext") as "Hi50".
    iPoseProof (uci_54 with "Htext") as "Hi54".
    iPoseProof (uci_58 with "Htext") as "Hi58".
    iPoseProof (uci_5a with "Htext") as "Hi5a".
    iPoseProof (uci_5c with "Htext") as "Hi5c".
    iPoseProof (uci_5e with "Htext") as "Hi5e".
    iPoseProof (uci_60 with "Htext") as "Hi60".
    iPoseProof (uci_64 with "Htext") as "Hi64".
    iPoseProof (uci_66 with "Htext") as "Hi66".
    iPoseProof (uci_68 with "Htext") as "Hi68".
    (* ================================================================ *)
    (*  THE +0x24 JOIN: the back edge and the exit test.                 *)
    (* ================================================================ *)
    iAssert (∀ (CIDt : CpuId) (mt : regfile) (Pk : uptd),
        ⌜ mt !!! Regidx csp_rs1 = spr
          /\ mt !!! Regidx Rs1 = iv
          /\ mt !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)
          /\ mt !!! Regidx Rs5 = sz
          /\ mt !!! Regidx Rs6 = page_base Pold.(ud_root)
          /\ mt !!! Regidx Rs7 = page_base Pnew.(ud_root)
          /\ uc_thr mm mt
          /\ uptd_ext Pnew Pk
          /\ (forall v, v ∉ vpn_run vpn0 (S j) ->
                Pk.(ud_um) !! v = Pnew.(ud_um) !! v)
          /\ (forall i, (i < S j)%nat -> uc_at Pold Pnew Pk vpn0 i) ⌝ -∗
        sie_cap_gpr kt mt (K - 10)%nat b p -∗
        cpu_own ilvl eb p b lks -∗
        pc_is (mword_of_int (KernelSyms.uvmcopy + 0x24) : mword 64) -∗
        proc_pt Pold -∗
        proc_pt Pk -∗
        uc_exit (kt := kt) mm Pold Pnew vpn0 n K eb p spr ilvl b lks -∗
        WP (Loop : expr riscv_lang))%I with "[]" as "TAIL".
    { iIntros (CIDt mt Pk).
      iIntros "(%Htsp & %Hts1 & %Hts4 & %Hts5 & %Hts6 & %Hts7 & %Htthr
                & %Htext2 & %Htout & %Htfacts) Hcg Hcnt Hpc Hpo Hpt Hexit".
      iPoseProof (uci_24 with "Htext") as "Hi24".
      iPoseProof (uci_26 with "Htext") as "Hi26".
      (* --- +0x24 c.add s1,s1,s4 : i += PGSIZE --- *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x24)) Rs1 Rs4 mt (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24").
      iIntros (CIDt1 Hst1) "Hcg Hpc". iEval (rgne; rgne) in "Hcg".
      set (T1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (mt !!! Regidx Rs1) (mt !!! Regidx Rs4))]> mt).
      assert (Hivs : bv_unsigned (add_vec iv (mword_of_int 4096))
                     = (4096 * Z.of_nat (S j))%Z).
      { rewrite (bc_add_moi iv (4096 * Z.of_nat j) 4096 Hiv
                   ltac:(clear -Hj0; lia) ltac:(clear; lia)
                   ltac:(exact (uc_z_no_wrap (Z.of_nat j) Hj0 Hjb))).
        rewrite Nat2Z.inj_succ. unfold Z.succ. ring. }
      assert (HT1s1 : T1 !!! Regidx Rs1 = add_vec iv (mword_of_int 4096)).
      { rewrite /T1 upd_eq. rewrite Hts1 Hts4. reflexivity. }
      assert (HT1sp : T1 !!! Regidx csp_rs1 = spr) by lkp.
      assert (HT1s4 : T1 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
      assert (HT1s5 : T1 !!! Regidx Rs5 = sz) by lkp.
      assert (HT1s6 : T1 !!! Regidx Rs6 = page_base Pold.(ud_root)) by lkp.
      assert (HT1s7 : T1 !!! Regidx Rs7 = page_base Pnew.(ud_root)) by lkp.
      assert (HT1thr : uc_thr mm T1).
      { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
        rewrite /T1. rewrite upd_ne; [| uc_thr_ne]. apply Htthr; assumption. }
      assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x24) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x26)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp26) in "Hpc".
      (* --- +0x26 bgeu s1,s5 : the exit test --- *)
      destruct (Nat.eq_dec rem 0) as [Hr0 | Hrne].
      { (* the run is finished: return 0 at +0x7e *)
        assert (Hlast : (S j = n)%nat) by (clear -Hsum Hr0; lia).
        assert (Hnl : ~ (4096 * Z.of_nat (S j) < nz)%Z).
        { intro Hx. pose proof (proj1 (Hnchar (S j)) Hx) as Hy.
          clear -Hy Hlast; lia. }
        assert (Hcmp : zopz0zKzJ_u (T1 !!! Regidx Rs1) (T1 !!! Regidx Rs5) = true).
        { rewrite HT1s1 HT1s5. apply bc_geu. rewrite Hivs Hsz. clear -Hnl; lia. }
        iPoseProof (uci_7e with "Htext") as "Hi7e".
        iApply (wp_bgeu_taken_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x26))
                  (mword_of_int 88 : mword 13) Rs5 Rs1 T1 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi26").
        iApply bi.later_intro. iIntros (CIDt2 Hst2) "Hcg Hpc".
        assert (Htgt7e : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x26) : mword 64)
                  (sign_extend' 64 (mword_of_int 88 : mword 13))
                = mword_of_int (KernelSyms.uvmcopy + 0x7e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt7e) in "Hpc".
        (* --- +0x7e c.li a0,0 --- *)
        iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x7e)) Ra0
                  (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) T1 (K - 10)%nat b
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi7e").
        iIntros (CIDt3 Hst3) "Hcg Hpc".
        set (T2 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> T1).
        assert (Hq80 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x7e) : mword 64) 2
                       = mword_of_int (KernelSyms.uvmcopy + 0x80)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hq80) in "Hpc".
        iDestruct (cpu_own_transport CIDt CIDt3 ilvl eb p b ltac:(wp_next_chain)
                     with "Hcnt") as "Hcnt".
        assert (Hshiftexit : b = false \/ p = zero_reg -> (CIDt3 : CPU) = (CIDt : CPU)) by wp_next_chain.
        iDestruct (wp_next_shift Hshiftexit with "Hexit") as "Hexit".
        iSpecialize ("Hexit" $! CIDt3 with "[%]"); [wp_next_chain|].
        iApply ("Hexit" $! T2 (mword_of_int 0) with "[%] Hcg Hcnt Hpc Hpo [Hpt]").
        { split_and!.
          - rewrite /T2. rewrite upd_ne; [exact HT1sp | reg_neq].
          - rewrite /T2 upd_eq. reflexivity.
          - intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
            rewrite /T2. rewrite upd_ne; [| uc_thr_ne]. apply HT1thr; assumption. }
        { rewrite /uc_pay. iRight. iExists Pk.
          iSplitR; [iPureIntro; reflexivity |].
          iSplitR; [iPureIntro; exact Htext2 |].
          iSplitR; [iPureIntro; rewrite <- Hlast; exact Htout |].
          iSplitR; [iPureIntro; rewrite <- Hlast; exact Htfacts |].
          iExact "Hpt". } }
      (* more pages to go: fall through to the loop head *)
      assert (Hnext : (S j < n)%nat) by (clear -Hsum Hrne; lia).
      assert (Hcmp : zopz0zKzJ_u (T1 !!! Regidx Rs1) (T1 !!! Regidx Rs5) = false).
      { rewrite HT1s1 HT1s5. apply bc_ltu. rewrite Hivs Hsz.
        exact (proj2 (Hnchar (S j)) Hnext). }
      iApply (wp_bgeu_fall_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x26))
                (mword_of_int 88 : mword 13) Rs5 Rs1 T1 (K - 10)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc Hi26").
      iIntros (CIDt4 Hst4) "Hcg Hpc".
      assert (Hp2a : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x26) : mword 64) 4
                     = mword_of_int (KernelSyms.uvmcopy + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp2a) in "Hpc".
      iDestruct (cpu_own_transport CIDt CIDt4 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      assert (Hshiftrec : b = false \/ p = zero_reg -> (CIDt4 : CPU) = (CIDt : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftrec with "Hexit") as "Hexit".
      iApply (IH (S j) Pk T1 (add_vec iv (mword_of_int 4096)) CIDt4
                ltac:(clear -Hsum; lia) ltac:(clear -Hrne; lia) Hivs
                Htext2 Htout Htfacts HT1sp HT1s1 HT1s4 HT1s5 HT1s6 HT1s7 HT1thr Hbelow
                with "Hcg Hcnt Htext Hpc Hpo Hpt Henv2 Hexit"). }
    (* ================================================================ *)
    (*  THE BODY.  walk(old, i, 0) on the PARENT.                        *)
    (* ================================================================ *)
    (* --- +0x2a c.li a2,0 --- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x2a)) Ra2
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) M (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi2a").
    iIntros (CIDl1 Hsl1) "Hcg Hpc".
    set (L1 := <[Regidx Ra2 := regval_into_reg (mword_of_int 0 : mword 64)]> M).
    assert (Hp2c : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x2a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2c) in "Hpc".
    (* --- +0x2c c.mv a1,s1 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x2c)) Ra1 Rs1 L1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c").
    iIntros (CIDl2 Hsl2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L2 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (L1 !!! Regidx Rs1))]> L1).
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x2c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    (* --- +0x2e c.mv a0,s6 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x2e)) Ra0 Rs6 L2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2e").
    iIntros (CIDl3 Hsl3) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (L3 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (L2 !!! Regidx Rs6))]> L2).
    assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x2e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x30)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp30) in "Hpc".
    (* --- +0x30 jal ra,walk --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x30)) Rra
              (mword_of_int 2095912 : mword 21) L3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi30").
    iIntros (CIDl4 Hsl4) "Hcg Hpc".
    set (L4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x30) : mword 64) 4)]> L3).
    assert (Htgtwk : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x30) : mword 64)
              (sign_extend' 64 (mword_of_int 2095912 : mword 21))
            = mword_of_int KernelSyms.walk) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwk) in "Hpc".
    (* open the PARENT's table into its exact represented view *)
    iDestruct (proc_pt_acc_rep0 Pold with "Hpo") as
      (to m_o) "(%Hrepo & %Hviewo & %Hbaseo & %Hwfo & Hptreeo & Howno)".
    assert (HL4a0 : L4 !!! Regidx Ra0
                    = zero_extend' 64 (concat_vec (pt_base to) (zeros' 12 : mword 12))).
    { lkp0. rewrite Hs6 Hbaseo. reflexivity. }
    assert (HL4a1 : L4 !!! Regidx Ra1 = iv) by lkp.
    assert (HL4a2 : L4 !!! Regidx Ra2 = (mword_of_int 0 : mword 64)) by lkp.
    assert (HL4sp : L4 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HL4s1 : L4 !!! Regidx Rs1 = iv) by lkp.
    assert (HL4s4 : L4 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HL4s5 : L4 !!! Regidx Rs5 = sz) by lkp.
    assert (HL4s6 : L4 !!! Regidx Rs6 = page_base Pold.(ud_root)) by lkp.
    assert (HL4s7 : L4 !!! Regidx Rs7 = page_base Pnew.(ud_root)) by lkp.
    assert (HL4thr : uc_thr mm L4).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      uc_thr_peel. apply Hthr; assumption. }
    assert (Hwkva : (uint (L4 !!! Regidx Ra1) < 2 ^ 38)%Z).
    { rewrite HL4a1 uint_unsigned Hiv.
      change (2 ^ 38)%Z with 274877906944%Z. clear -Hjb; lia. }
    assert (Hret34 : ret_pc (L4 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmcopy + 0x34)).
    { rewrite /L4 upd_eq. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iApply (WalkNoalloc.wp_walk_noalloc_sconf kt L4 to m_o (K - 10)%nat (DfracOwn 1) b p
              HKwk HL4a0 HL4a2 Hwkva Hrepo with "Hcg Htext Hpc Hptreeo").
    iIntros (CIDl5 Hsl5 mw) "Hcg Hpc Hptreeo %Hwcs %Hpay".
    iEval (rewrite Hret34) in "Hpc".
    assert (Hvv : svpn_of (L4 !!! Regidx Ra1) = vpn_at vpn0 j)
      by (rewrite HL4a1; exact Hvj).
    rewrite Hvv in Hpay.
    assert (Hmwsp : mw !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hwcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HL4sp. }
    assert (Hmws1 : mw !!! Regidx Rs1 = iv).
    { rewrite (callee_saved_lookup Hwcs Rs1 ltac:(vm_compute; reflexivity)). exact HL4s1. }
    assert (Hmws4 : mw !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hwcs Rs4 ltac:(vm_compute; reflexivity)). exact HL4s4. }
    assert (Hmws5 : mw !!! Regidx Rs5 = sz).
    { rewrite (callee_saved_lookup Hwcs Rs5 ltac:(vm_compute; reflexivity)). exact HL4s5. }
    assert (Hmws6 : mw !!! Regidx Rs6 = page_base Pold.(ud_root)).
    { rewrite (callee_saved_lookup Hwcs Rs6 ltac:(vm_compute; reflexivity)). exact HL4s6. }
    assert (Hmws7 : mw !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite (callee_saved_lookup Hwcs Rs7 ltac:(vm_compute; reflexivity)). exact HL4s7. }
    assert (Hmwthr : uc_thr mm mw).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hwcs c Hc). apply HL4thr; assumption. }
    assert (Htgt24 : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x34) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 248 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.uvmcopy + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hpay as [(Ha0z & Hnone) | (p2 & p1 & w0 & Hl0 & Ha0v & Hverd)].
    { (* ========== walk found no level-0 slot: skip this page ========== *)
      iDestruct (proc_pt_rebuild Pold to m_o Hwfo Hviewo Hrepo Hbaseo
                   with "Hptreeo Howno") as "Hpo".
      assert (Hbz : eq_vec (mw !!! Regidx Ra0) zero_reg = true).
      { rewrite Ha0z. vm_compute; reflexivity. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x34))
                (mword_of_int 248 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mw (K - 10)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi34").
      iIntros (CIDl6 Hsl6). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt24) in "Hpc".
      assert (Holdnone : Pold.(ud_um) !! vpn_at vpn0 j = None)
        by exact (proj2 (proj2 (proj1 (proj1 Hviewo (vpn_at vpn0 j)) Hnone))).
      iDestruct (cpu_own_transport CID0 CIDl6 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      assert (Hshiftl6 : b = false \/ p = zero_reg -> (CIDl6 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftl6 with "Hexit") as "Hexit".
      iApply ("TAIL" $! CIDl6 mw Pj with "[%] Hcg Hcnt Hpc Hpo Hpt Hexit").
      split_and!; try assumption.
      - intros v Hv. exact (Hout v (Hsubrun v Hv)).
      - intros i Hi. destruct (Nat.eq_dec i j) as [-> | Hne].
        + unfold uc_at. rewrite Holdnone. exact (Hout _ Hnotin).
        + exact (Hfacts i ltac:(clear -Hi Hne; lia)). }
    (* ========== walk reached the level-0 slot ========== *)
    iDestruct (ptree_own_level0_ro (DfracOwn 1) to (vpn_at vpn0 j) p2 p1 w0 Hl0
                 with "Hptreeo") as "(#Hcl0 & Hcell & Hclose)".
    iDestruct (phys_word_pointsto_ram with "Hcell") as %Hslotram.
    iDestruct (pt_slot_phys_to_mem (u_next_base p1) (vpn_idx 0 (vpn_at vpn0 j))
                 (DfracOwn 1) w0 with "Hcl0 Hcell") as "Hcell".
    assert (Ha0nz : mw !!! Regidx Ra0 <> (mword_of_int 0 : mword 64)).
    { rewrite Ha0v. intro Heq. rewrite Heq in Hslotram.
      unfold addr_is_ram in Hslotram. destruct Hslotram as [Hlo _].
      apply (proj2 (Z.leb_le _ _)) in Hlo. vm_compute in Hlo. discriminate. }
    assert (Hbnz : eq_vec (mw !!! Regidx Ra0) zero_reg = false).
    { apply eq_vec_false_iff. intro He. apply Ha0nz.
      rewrite He. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x34))
              (mword_of_int 248 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              mw (K - 10)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hbnz with "Hcg Hpc Hi34").
    iIntros (CIDl6 Hsl6) "Hcg Hpc".
    assert (Hp36 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x34) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x36)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp36) in "Hpc".
    (* --- +0x36 ld s3,0(a0) : s3 := *pte --- *)
    assert (Hzoff : forall X : mword 64,
        add_vec X (sign_extend' 64 (mword_of_int 0 : mword 12)) = X).
    { intro X.
      replace (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
        with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
      apply kv_addv_zero. }
    iApply (wp_ld_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x36)) Rs3 Ra0
              (mword_of_int 0 : mword 12) mw (K - 10)%nat w0 b (dqm:=DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi36 [Hcell]").
    { iEval (rgne; rewrite Hzoff Ha0v). iExact "Hcell". }
    iIntros (CIDl7 Hsl7) "Hcg Hpc Hcell".
    iEval (rgne; rewrite Hzoff Ha0v) in "Hcell".
    set (B1 := <[Regidx Rs3 := regval_into_reg w0]> mw).
    iDestruct (pt_slot_mem_to_phys (u_next_base p1) (vpn_idx 0 (vpn_at vpn0 j))
                 (DfracOwn 1) w0 with "Hcl0 Hcell") as "Hcell".
    iDestruct ("Hclose" with "Hcell") as "Hptreeo".
    iDestruct (proc_pt_rebuild Pold to m_o Hwfo Hviewo Hrepo Hbaseo
                 with "Hptreeo Howno") as "Hpo".
    assert (HB1s3 : B1 !!! Regidx Rs3 = w0) by (rewrite /B1 upd_eq; reflexivity).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB1s1 : B1 !!! Regidx Rs1 = iv) by lkp.
    assert (HB1s4 : B1 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HB1s5 : B1 !!! Regidx Rs5 = sz) by lkp.
    assert (HB1s6 : B1 !!! Regidx Rs6 = page_base Pold.(ud_root)) by lkp.
    assert (HB1s7 : B1 !!! Regidx Rs7 = page_base Pnew.(ud_root)) by lkp.
    assert (HB1thr : uc_thr mm B1).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite /B1. rewrite upd_ne; [| uc_thr_ne]. apply Hmwthr; assumption. }
    assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x36) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmcopy + 0x3a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3a) in "Hpc".
    (* --- +0x3a andi a5,s3,1 : PTE_V --- *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x3a)) Ra5 Rs3
              (mword_of_int 1 : mword 12)
              (and_vec w0 (sign_extend' 64 (mword_of_int 1 : mword 12)))
              B1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite HB1s3; reflexivity) with "Hcg Hpc Hi3a").
    iIntros (CIDl8 Hsl8) "Hcg Hpc".
    set (B2 := <[Regidx Ra5 := regval_into_reg
                  (and_vec w0 (sign_extend' 64 (mword_of_int 1 : mword 12)))]> B1).
    assert (HB2a5 : B2 !!! Regidx Ra5
                    = and_vec w0 (sign_extend' 64 (mword_of_int 1 : mword 12)))
      by (rewrite /B2 upd_eq; reflexivity).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB2s1 : B2 !!! Regidx Rs1 = iv) by lkp.
    assert (HB2s3 : B2 !!! Regidx Rs3 = w0) by lkp.
    assert (HB2s4 : B2 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HB2s5 : B2 !!! Regidx Rs5 = sz) by lkp.
    assert (HB2s6 : B2 !!! Regidx Rs6 = page_base Pold.(ud_root)) by lkp.
    assert (HB2s7 : B2 !!! Regidx Rs7 = page_base Pnew.(ud_root)) by lkp.
    assert (HB2thr : uc_thr mm B2).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite /B2. rewrite upd_ne; [| uc_thr_ne]. apply HB1thr; assumption. }
    assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x3a) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmcopy + 0x3e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp3e) in "Hpc".
    assert (Htgt24' : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x3e) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 243 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.uvmcopy + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hverd as [Hsome | (Hw0z & Hnone)].
    2:{ (* ---- the slot holds the literal zero: skip this page ---- *)
      assert (Hbz : eq_vec (B2 !!! Regidx Ra5) zero_reg = true).
      { rewrite HB2a5 Hw0z. vm_compute; reflexivity. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x3e))
                (mword_of_int 243 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                B2 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi3e").
      iIntros (CIDl9 Hsl9). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt24') in "Hpc".
      assert (Holdnone : Pold.(ud_um) !! vpn_at vpn0 j = None)
        by exact (proj2 (proj2 (proj1 (proj1 Hviewo (vpn_at vpn0 j)) Hnone))).
      iDestruct (cpu_own_transport CID0 CIDl9 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      assert (Hshiftl9 : b = false \/ p = zero_reg -> (CIDl9 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftl9 with "Hexit") as "Hexit".
      iApply ("TAIL" $! CIDl9 B2 Pj with "[%] Hcg Hcnt Hpc Hpo Hpt Hexit").
      split_and!; try assumption.
      - intros v Hv. exact (Hout v (Hsubrun v Hv)).
      - intros i Hi. destruct (Nat.eq_dec i j) as [-> | Hne].
        + unfold uc_at. rewrite Holdnone. exact (Hout _ Hnotin).
        + exact (Hfacts i ltac:(clear -Hi Hne; lia)). }
    (* ---- the parent HAS a leaf here: copy it ---- *)
    destruct (upt_ad_view_um Pold.(ud_tfp) Pold.(ud_um) m_o (vpn_at vpn0 j) w0
                Hviewo Hsome Hntr Hntf) as (wu & au & du & Humsome & Hw0ad).
    destruct (proj1 Hwfo (vpn_at vpn0 j) wu Humsome) as (_ & Hleafwu).
    pose proof (proj1 (proj2 Hwfo) (vpn_at vpn0 j) wu Humsome) as Haccwu.
    destruct (Hleafwu au du) as (Hvw0 & Hlw0 & Hnw0 & Hpw0).
    rewrite <- Hw0ad in Hvw0. rewrite <- Hw0ad in Hnw0. rewrite <- Hw0ad in Hpw0.
    assert (Hlt54 : (bv_unsigned w0 < 18014398509481984)%Z)
      by exact (pte_hi_zero w0 Hvw0 Hnw0 Hpw0).
    destruct (pte_set_ad_refl wu) as (a1r & d1r & Hselfwu).
    destruct (Hleafwu a1r d1r) as (Hvwu0 & _ & Hnwu0 & Hpwu0).
    rewrite <- Hselfwu in Hvwu0. rewrite <- Hselfwu in Hnwu0.
    rewrite <- Hselfwu in Hpwu0.
    assert (Hltwu : (bv_unsigned wu < 18014398509481984)%Z)
      by exact (pte_hi_zero wu Hvwu0 Hnwu0 Hpwu0).
    assert (Hperm : uvm_perm_ok (pte_flags10 w0)).
    { rewrite Hw0ad. exact (uc_perm_ok wu au du Hleafwu Haccwu). }
    assert (Hppn : pte_ppn w0 = pte_ppn wu)
      by (rewrite Hw0ad; apply pte_ppn_set_ad).
    assert (Hbnz5 : eq_vec (B2 !!! Regidx Ra5) zero_reg = false).
    { rewrite HB2a5. rewrite (pte_valid_bit0 w0 Hvw0). vm_compute; reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x3e))
              (mword_of_int 243 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              B2 (K - 10)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hbnz5 with "Hcg Hpc Hi3e").
    iIntros (CIDl10 Hsl10) "Hcg Hpc".
    assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x3e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x40)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp40) in "Hpc".
    (* --- +0x40 jal ra,kalloc --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x40)) Rra
              (mword_of_int 2094824 : mword 21) B2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi40").
    iIntros (CIDl11 Hsl11) "Hcg Hpc".
    set (B3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x40) : mword 64) 4)]> B2).
    assert (Htgtka : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x40) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094824 : mword 21))
                     = mword_of_int KernelSyms.kalloc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtka) in "Hpc".
    assert (HB3ra : B3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x40) : mword 64) 4)
      by (rewrite /B3 upd_eq; reflexivity).
    assert (HB3sp : B3 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HB3s1 : B3 !!! Regidx Rs1 = iv) by lkp.
    assert (HB3s3 : B3 !!! Regidx Rs3 = w0) by lkp.
    assert (HB3s4 : B3 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HB3s5 : B3 !!! Regidx Rs5 = sz) by lkp.
    assert (HB3s6 : B3 !!! Regidx Rs6 = page_base Pold.(ud_root)) by lkp.
    assert (HB3s7 : B3 !!! Regidx Rs7 = page_base Pnew.(ud_root)) by lkp.
    assert (HB3thr : uc_thr mm B3).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite /B3. rewrite upd_ne; [| uc_thr_ne]. apply HB2thr; assumption. }
    iDestruct (cpu_own_transport CID0 CIDl11 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Kalloc.wp_kalloc_sconf kt γa γk (mword_of_int (KernelSyms.kmem + 24))
              B3 None ilvl eb p (K - 10)%nat b
              _ HKka ltac:(reflexivity) Hilvl Hbelow
              with "Hcg Hcnt Htext Hpc Hlock Havail").
    all: try lkbelow.
    iIntros (CIDl12 Hsl12 mk) "Hcg Hcnt Hpc %Hkcs Hkpost".
    assert (Hret44 : ret_pc (B3 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmcopy + 0x44)).
    { rewrite HB3ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret44) in "Hpc".
    assert (Hmksp : mk !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hkcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HB3sp. }
    assert (Hmks1 : mk !!! Regidx Rs1 = iv).
    { rewrite (callee_saved_lookup Hkcs Rs1 ltac:(vm_compute; reflexivity)). exact HB3s1. }
    assert (Hmks3 : mk !!! Regidx Rs3 = w0).
    { rewrite (callee_saved_lookup Hkcs Rs3 ltac:(vm_compute; reflexivity)). exact HB3s3. }
    assert (Hmks4 : mk !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hkcs Rs4 ltac:(vm_compute; reflexivity)). exact HB3s4. }
    assert (Hmks5 : mk !!! Regidx Rs5 = sz).
    { rewrite (callee_saved_lookup Hkcs Rs5 ltac:(vm_compute; reflexivity)). exact HB3s5. }
    assert (Hmks6 : mk !!! Regidx Rs6 = page_base Pold.(ud_root)).
    { rewrite (callee_saved_lookup Hkcs Rs6 ltac:(vm_compute; reflexivity)). exact HB3s6. }
    assert (Hmks7 : mk !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite (callee_saved_lookup Hkcs Rs7 ltac:(vm_compute; reflexivity)). exact HB3s7. }
    assert (Hmkthr : uc_thr mm mk).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hkcs c Hc). apply HB3thr; assumption. }
    (* --- +0x44 c.mv s2,a0 : mem --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x44)) Rs2 Ra0 mk (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi44").
    iIntros (CIDl13 Hsl13) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C1 := <[Regidx Rs2 := regval_into_reg (add_vec zero_reg (mk !!! Regidx Ra0))]> mk).
    assert (HC1a0 : C1 !!! Regidx Ra0 = mk !!! Regidx Ra0) by lkp.
    assert (HC1s2 : C1 !!! Regidx Rs2 = mk !!! Regidx Ra0).
    { rewrite /C1 upd_eq. apply add_vec_zero_l. }
    assert (HC1sp : C1 !!! Regidx csp_rs1 = spr) by lkp.
    assert (HC1s1 : C1 !!! Regidx Rs1 = iv) by lkp.
    assert (HC1s3 : C1 !!! Regidx Rs3 = w0) by lkp.
    assert (HC1s4 : C1 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)) by lkp.
    assert (HC1s5 : C1 !!! Regidx Rs5 = sz) by lkp.
    assert (HC1s6 : C1 !!! Regidx Rs6 = page_base Pold.(ud_root)) by lkp.
    assert (HC1s7 : C1 !!! Regidx Rs7 = page_base Pnew.(ud_root)) by lkp.
    assert (HC1thr : uc_thr mm C1).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite /C1. rewrite upd_ne; [| uc_thr_ne]. apply Hmkthr; assumption. }
    assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x44) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x46)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp46) in "Hpc".
    assert (Htgt6c : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x46) : mword 64)
              (sign_extend' 64 (sign_extend' 13
                 (concat_vec (mword_of_int 19 : mword 8) ('b"0"))))
            = mword_of_int (KernelSyms.uvmcopy + 0x6c)) by (apply bv_eq; vm_compute; reflexivity).
    iDestruct "Hkpost" as "[(%Hnull & _ & _) | (%Hpv & Hpage & _)]".
    { (* ========== kalloc failed: unwind ========== *)
      assert (Hbz : eq_vec (C1 !!! Regidx Ra0) zero_reg = true).
      { rewrite HC1a0 Hnull. vm_compute; reflexivity. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x46))
                (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                C1 (K - 10)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi46").
      iIntros (CIDl14 Hsl14). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt6c) in "Hpc".
      iDestruct (cpu_own_transport CIDl12 CIDl14 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      assert (Hshiftl14 : b = false \/ p = zero_reg -> (CIDl14 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftl14 with "Hexit") as "Hexit".
      iApply (uc_err (CID0 := CIDl14) γa mm Pold Pnew Pj vpn0 n j K eb p spr iv C1 ilvl b lks
                HK Hilvl Hvpn0 Hiv ltac:(clear -Hjb; lia) Hext Hout
                ltac:(intros i Hi; apply Hfresh; clear -Hi Hjn; lia)
                HC1sp HC1s1 HC1s7 HC1thr Hbelow
                with "Hcg Hcnt Htext Hpc Hpo Hpt Henv2 Hexit"). }
    (* ========== kalloc returned a page ========== *)
    set (r := (mk !!! Regidx Ra0 : mword 64)).
    pose proof Hpv as Hpvd. destruct Hpvd as [Hral Hrrng].
    unfold page_in_range, kmem_lo, kmem_hi in Hrrng.
    assert (Hnzr : (zero_reg : mword 64) = nullp) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hnn : eq_vec (C1 !!! Regidx Ra0) zero_reg = false).
    { rewrite HC1a0. apply eq_vec_false_iff. rewrite Hnzr.
      exact (page_valid_ne_null _ Hpv). }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x46))
              (mword_of_int 19 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              C1 (K - 10)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hnn with "Hcg Hpc Hi46").
    iIntros (CIDl14 Hsl14) "Hcg Hpc".
    assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x46) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp48) in "Hpc".
    (* --- +0x48 srli a1,s3,0xa / +0x4e c.slli a1,a1,0xc : PTE2PA --- *)
    iApply (wp_srli4_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x48)) Ra1 Rs3
              (mword_of_int 10 : mword 6) C1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48").
    iIntros (CIDl15 Hsl15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C2 := <[Regidx Ra1 := regval_into_reg
        (shift_bits_right (C1 !!! Regidx Rs3)
           (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0))]> C1).
    assert (HC2a1 : C2 !!! Regidx Ra1
                    = shift_bits_right w0
                        (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0)).
    { rewrite /C2 upd_eq. rewrite HC1s3. reflexivity. }
    assert (Hp4c : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x48) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmcopy + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4c) in "Hpc".
    (* --- +0x4c c.mv a2,s4 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x4c)) Ra2 Rs4 C2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c").
    iIntros (CIDl16 Hsl16) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C3 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (C2 !!! Regidx Rs4))]> C2).
    assert (Hp4e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x4c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4e) in "Hpc".
    (* --- +0x4e c.slli a1,a1,0xc --- *)
    iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x4e)) (Regidx Ra1) Ra1
              (mword_of_int 12 : mword 6) C3 (K - 10)%nat b
              ltac:(reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi4e").
    iIntros (CIDl17 Hsl17) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (C4 := <[Regidx Ra1 := regval_into_reg
        (shift_bits_left (C3 !!! Regidx Ra1)
           (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0))]> C3).
    assert (Hs10 : int_of_mword false
              (subrange_vec_dec (mword_of_int 10 : mword 6) (Z.sub log2_xlen 1) 0) = 10)
      by (vm_compute; reflexivity).
    assert (Hs12 : int_of_mword false
              (subrange_vec_dec (mword_of_int 12 : mword 6) (Z.sub log2_xlen 1) 0) = 12)
      by (vm_compute; reflexivity).
    assert (HC4a1 : C4 !!! Regidx Ra1 = page_base (pte_ppn wu)).
    { rewrite /C4 upd_eq. rewrite /C3. rewrite upd_ne; [| reg_neq].
      rewrite HC2a1. rewrite <- Hppn.
      apply pte2pa; [exact Hs10 | exact Hs12 | exact Hlt54]. }
    assert (Hp50 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x4e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x50)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp50) in "Hpc".
    (* --- +0x50 jal ra,memmove --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x50)) Rra
              (mword_of_int 2095314 : mword 21) C4 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi50").
    iIntros (CIDl18 Hsl18) "Hcg Hpc".
    set (C5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x50) : mword 64) 4)]> C4).
    assert (Htgtmm : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x50) : mword 64)
                       (sign_extend' 64 (mword_of_int 2095314 : mword 21))
                     = mword_of_int KernelSyms.memmove)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtmm) in "Hpc".
    assert (HC5ra : C5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x50) : mword 64) 4)
      by (rewrite /C5 upd_eq; reflexivity).
    assert (HC5a0 : C5 !!! Regidx Ra0 = r).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1a0. }
    assert (HC5a1 : C5 !!! Regidx Ra1 = page_base (pte_ppn wu)).
    { rewrite /C5. rewrite upd_ne; [| reg_neq]. exact HC4a1. }
    assert (HC5a2 : C5 !!! Regidx Ra2 = (mword_of_int 4096 : mword 64)).
    { rewrite /C5. rewrite upd_ne; [| reg_neq].
      rewrite /C4. rewrite upd_ne; [| reg_neq].
      rewrite /C3 upd_eq. rewrite add_vec_zero_l.
      rewrite /C2. rewrite upd_ne; [| reg_neq]. exact HC1s4. }
    assert (HC5sp : C5 !!! Regidx csp_rs1 = spr).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1sp. }
    assert (HC5s1 : C5 !!! Regidx Rs1 = iv).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1s1. }
    assert (HC5s2 : C5 !!! Regidx Rs2 = r).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1s2. }
    assert (HC5s3 : C5 !!! Regidx Rs3 = w0).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1s3. }
    assert (HC5s4 : C5 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1s4. }
    assert (HC5s5 : C5 !!! Regidx Rs5 = sz).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1s5. }
    assert (HC5s6 : C5 !!! Regidx Rs6 = page_base Pold.(ud_root)).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1s6. }
    assert (HC5s7 : C5 !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite /C5 /C4 /C3 /C2. repeat (rewrite upd_ne; [| reg_neq]). exact HC1s7. }
    assert (HC5thr : uc_thr mm C5).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      uc_thr_peel. apply Hmkthr; assumption. }
    assert (Hmmlen : C5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 4096) : mword 64))
      by (rewrite HC5a2; apply bv_eq; vm_compute; reflexivity).
    (* borrow the PARENT's page at the byte tier *)
    iDestruct (proc_pt_page_acc Pold (vpn_at vpn0 j) wu Humsome with "Hkmapb Hpo")
      as "[Hsrc Hsrcback]".
    iDestruct (bb_page_named (page_base (pte_ppn wu)) with "Hsrc") as (fsrc) "Hsrc".
    iDestruct (bb_page_named r with "Hpage") as (fdst) "Hdst".
    iApply (Memmove.wp_memmove_sconf kt C5 (K - 10)%nat 4096%nat fsrc fdst b p
              HKmm ltac:(vm_compute; reflexivity) Hmmlen
              with "Hcg Htext Hpc [Hsrc] [Hdst]").
    { iEval (rewrite HC5a1). iExact "Hsrc". }
    { iEval (rewrite HC5a0). iExact "Hdst". }
    iIntros (CIDl19 Hsl19 mv) "Hcg Hpc Hsrc Hdst %Hmva0 %Hmvcs".
    iEval (rewrite HC5a1) in "Hsrc".
    iEval (rewrite HC5a0) in "Hdst".
    iDestruct (bb_page_of_named (page_base (pte_ppn wu)) fsrc with "Hsrc") as "Hsrc".
    iDestruct (bb_page_of_named r fsrc with "Hdst") as "Hpage".
    iDestruct ("Hsrcback" with "Hsrc") as "Hpo".
    assert (Hret54 : ret_pc (C5 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmcopy + 0x54)).
    { rewrite HC5ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret54) in "Hpc".
    assert (Hmvsp : mv !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hmvcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HC5sp. }
    assert (Hmvs1 : mv !!! Regidx Rs1 = iv).
    { rewrite (callee_saved_lookup Hmvcs Rs1 ltac:(vm_compute; reflexivity)). exact HC5s1. }
    assert (Hmvs2 : mv !!! Regidx Rs2 = r).
    { rewrite (callee_saved_lookup Hmvcs Rs2 ltac:(vm_compute; reflexivity)). exact HC5s2. }
    assert (Hmvs3 : mv !!! Regidx Rs3 = w0).
    { rewrite (callee_saved_lookup Hmvcs Rs3 ltac:(vm_compute; reflexivity)). exact HC5s3. }
    assert (Hmvs4 : mv !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hmvcs Rs4 ltac:(vm_compute; reflexivity)). exact HC5s4. }
    assert (Hmvs5 : mv !!! Regidx Rs5 = sz).
    { rewrite (callee_saved_lookup Hmvcs Rs5 ltac:(vm_compute; reflexivity)). exact HC5s5. }
    assert (Hmvs6 : mv !!! Regidx Rs6 = page_base Pold.(ud_root)).
    { rewrite (callee_saved_lookup Hmvcs Rs6 ltac:(vm_compute; reflexivity)). exact HC5s6. }
    assert (Hmvs7 : mv !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite (callee_saved_lookup Hmvcs Rs7 ltac:(vm_compute; reflexivity)). exact HC5s7. }
    assert (Hmvthr : uc_thr mm mv).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hmvcs c Hc). apply HC5thr; assumption. }
    (* --- +0x54 andi a4,s3,1023 : flags := PTE_FLAGS( *pte ) --- *)
    iApply (wp_andi_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x54)) Ra4 Rs3
              (mword_of_int 1023 : mword 12)
              (mword_of_int (pte_flags10 w0) : mword 64) mv (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(rgne; rewrite Hmvs3; apply uc_andi1023) with "Hcg Hpc Hi54").
    iIntros (CIDl20 Hsl20) "Hcg Hpc".
    set (D1 := <[Regidx Ra4 := regval_into_reg
                  (mword_of_int (pte_flags10 w0) : mword 64)]> mv).
    assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x54) : mword 64) 4
                   = mword_of_int (KernelSyms.uvmcopy + 0x58)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp58) in "Hpc".
    (* --- +0x58 c.mv a3,s2 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x58)) Ra3 Rs2 D1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58").
    iIntros (CIDl21 Hsl21) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (D2 := <[Regidx Ra3 := regval_into_reg (add_vec zero_reg (D1 !!! Regidx Rs2))]> D1).
    assert (Hp5a : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x58) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5a) in "Hpc".
    (* --- +0x5a c.mv a2,s4 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x5a)) Ra2 Rs4 D2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a").
    iIntros (CIDl22 Hsl22) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (D3 := <[Regidx Ra2 := regval_into_reg (add_vec zero_reg (D2 !!! Regidx Rs4))]> D2).
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x5a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    (* --- +0x5c c.mv a1,s1 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x5c)) Ra1 Rs1 D3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c").
    iIntros (CIDl23 Hsl23) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (D4 := <[Regidx Ra1 := regval_into_reg (add_vec zero_reg (D3 !!! Regidx Rs1))]> D3).
    assert (Hp5e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x5c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5e) in "Hpc".
    (* --- +0x5e c.mv a0,s7 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x5e)) Ra0 Rs7 D4 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5e").
    iIntros (CIDl24 Hsl24) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (D5 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (D4 !!! Regidx Rs7))]> D4).
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x5e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    (* --- +0x60 jal ra,mappages --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x60)) Rra
              (mword_of_int 2096076 : mword 21) D5 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi60").
    iIntros (CIDl25 Hsl25) "Hcg Hpc".
    set (D6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x60) : mword 64) 4)]> D5).
    assert (Htgtmp : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x60) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096076 : mword 21))
                     = mword_of_int KernelSyms.mappages)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtmp) in "Hpc".
    assert (HD6ra : D6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x60) : mword 64) 4)
      by (rewrite /D6 upd_eq; reflexivity).
    assert (HD6a0 : D6 !!! Regidx Ra0 = page_base Pnew.(ud_root)).
    { rewrite /D6. rewrite upd_ne; [| reg_neq].
      rewrite /D5 upd_eq. rewrite add_vec_zero_l.
      rewrite /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs7. }
    assert (HD6a1 : D6 !!! Regidx Ra1 = iv).
    { rewrite /D6. rewrite upd_ne; [| reg_neq].
      rewrite /D5. rewrite upd_ne; [| reg_neq].
      rewrite /D4 upd_eq. rewrite add_vec_zero_l.
      rewrite /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs1. }
    assert (HD6a2 : D6 !!! Regidx Ra2 = (mword_of_int 4096 : mword 64)).
    { rewrite /D6. rewrite upd_ne; [| reg_neq].
      rewrite /D5. rewrite upd_ne; [| reg_neq].
      rewrite /D4. rewrite upd_ne; [| reg_neq].
      rewrite /D3 upd_eq. rewrite add_vec_zero_l.
      rewrite /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs4. }
    assert (HD6a3 : D6 !!! Regidx Ra3 = r).
    { rewrite /D6. rewrite upd_ne; [| reg_neq].
      rewrite /D5. rewrite upd_ne; [| reg_neq].
      rewrite /D4. rewrite upd_ne; [| reg_neq].
      rewrite /D3. rewrite upd_ne; [| reg_neq].
      rewrite /D2 upd_eq. rewrite add_vec_zero_l.
      rewrite /D1. rewrite upd_ne; [| reg_neq]. exact Hmvs2. }
    assert (HD6a4 : D6 !!! Regidx Ra4 = (mword_of_int (pte_flags10 w0) : mword 64)).
    { rewrite /D6 /D5 /D4 /D3 /D2. repeat (rewrite upd_ne; [| reg_neq]).
      rewrite /D1 upd_eq. reflexivity. }
    assert (HD6sp : D6 !!! Regidx csp_rs1 = spr).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvsp. }
    assert (HD6s1 : D6 !!! Regidx Rs1 = iv).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs1. }
    assert (HD6s2 : D6 !!! Regidx Rs2 = r).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs2. }
    assert (HD6s3 : D6 !!! Regidx Rs3 = w0).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs3. }
    assert (HD6s4 : D6 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs4. }
    assert (HD6s5 : D6 !!! Regidx Rs5 = sz).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs5. }
    assert (HD6s6 : D6 !!! Regidx Rs6 = page_base Pold.(ud_root)).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs6. }
    assert (HD6s7 : D6 !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite /D6 /D5 /D4 /D3 /D2 /D1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmvs7. }
    assert (HD6thr : uc_thr mm D6).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      uc_thr_peel. apply Hmvthr; assumption. }
    (* open the CHILD's table *)
    iDestruct (proc_pt_acc_rep0 Pj with "Hpt") as
      (tc m_c) "(%Hrepc & %Hviewc & %Hbasec & %Hwfc & Hptreec & Hownc)".
    assert (Hmcnone : m_c !! vpn_at vpn0 j = None).
    { apply (proj1 Hviewc (vpn_at vpn0 j)). split_and!.
      - exact Hntr.
      - exact Hntf.
      - exact Hpjnone. }
    assert (HD6root : D6 !!! Regidx Ra0
                      = zero_extend' 64 (concat_vec (pt_base tc) (zeros' 12 : mword 12))).
    { rewrite HD6a0 Hbasec. rewrite (proj1 Hext). reflexivity. }
    assert (Hmpva : subrange_vec_dec (D6 !!! Regidx Ra1) 11 0 = (zeros' 12 : mword 12))
      by (rewrite HD6a1; exact (aligned_low12 iv Hivmod)).
    assert (Hmppa : subrange_vec_dec (D6 !!! Regidx Ra3) 11 0 = (zeros' 12 : mword 12)).
    { rewrite HD6a3. apply aligned_low12. rewrite <- uint_unsigned.
      unfold page_aligned, PGSIZE in Hral. exact Hral. }
    assert (Hmpsz : D6 !!! Regidx Ra2 = mword_of_int (Z.of_nat 1 * 4096))
      by (rewrite HD6a2; apply bv_eq; vm_compute; reflexivity).
    assert (Hmpvab : (uint (D6 !!! Regidx Ra1) + Z.of_nat 1 * 4096 <= 2 ^ 38)%Z).
    { rewrite HD6a1 uint_unsigned Hiv. change (2 ^ 38)%Z with 274877906944%Z.
      exact (uc_z_va_bnd (Z.of_nat j) Hj0 Hjb). }
    assert (Hmppab : (uint (D6 !!! Regidx Ra3) + Z.of_nat 1 * 4096 < 2 ^ 56)%Z).
    { rewrite HD6a3. change (2 ^ 56)%Z with 72057594037927936%Z.
      exact (uc_z_run_pa _ (proj2 Hrrng)). }
    assert (Hmpfresh : forall i, (i < 1)%nat ->
              m_c !! vpn_at (svpn_of (D6 !!! Regidx Ra1)) i = None).
    { intros i Hi. assert (Hi0 : i = 0%nat) by (clear -Hi; lia). subst i.
      rewrite vpn_at_0 HD6a1 Hvj. exact Hmcnone. }
    iDestruct (cpu_own_transport CIDl12 CIDl25 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Mappages.wp_mappages_sconf kt γa D6 tc m_c 1%nat (pte_flags10 w0) ilvl
              (K - 10)%nat eb p None b
              _ Hilvl HKmp HD6root Hmpva Hmppa Hmpsz ltac:(clear; lia)
              HD6a4 (proj1 Hperm) Hmpvab Hmppab Hrepc Hmpfresh
              with "Hcg Hcnt Htext Hpc Hptreec Henv2").
    all: try lkbelow.
    iIntros (CIDl26 Hsl26 mg tc' k g) "Hcg Hcnt Hpc Hptreec %Hnodes _ %Hgcs %Hbase' %Hrep' %Hmono %Hmiss %Hmpay".
    rewrite HD6a1 in Hrep'. rewrite HD6a3 in Hrep'. rewrite Hvj in Hrep'.
    assert (Hret64 : ret_pc (D6 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmcopy + 0x64)).
    { rewrite HD6ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret64) in "Hpc".
    assert (Hbase'' : pt_base tc' = Pj.(ud_root)) by (rewrite Hbase'; exact Hbasec).
    assert (Hmgsp : mg !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hgcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HD6sp. }
    assert (Hmgs1 : mg !!! Regidx Rs1 = iv).
    { rewrite (callee_saved_lookup Hgcs Rs1 ltac:(vm_compute; reflexivity)). exact HD6s1. }
    assert (Hmgs2 : mg !!! Regidx Rs2 = r).
    { rewrite (callee_saved_lookup Hgcs Rs2 ltac:(vm_compute; reflexivity)). exact HD6s2. }
    assert (Hmgs4 : mg !!! Regidx Rs4 = (mword_of_int 4096 : mword 64)).
    { rewrite (callee_saved_lookup Hgcs Rs4 ltac:(vm_compute; reflexivity)). exact HD6s4. }
    assert (Hmgs5 : mg !!! Regidx Rs5 = sz).
    { rewrite (callee_saved_lookup Hgcs Rs5 ltac:(vm_compute; reflexivity)). exact HD6s5. }
    assert (Hmgs6 : mg !!! Regidx Rs6 = page_base Pold.(ud_root)).
    { rewrite (callee_saved_lookup Hgcs Rs6 ltac:(vm_compute; reflexivity)). exact HD6s6. }
    assert (Hmgs7 : mg !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite (callee_saved_lookup Hgcs Rs7 ltac:(vm_compute; reflexivity)). exact HD6s7. }
    assert (Hmgthr : uc_thr mm mg).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hgcs c Hc). apply HD6thr; assumption. }
    destruct Hmpay as [(Hk1 & Hga0) | (Hklt & Hga0 & _)].
    { (* ========== mappages SUCCEEDED: one more page mirrored ========== *)
      subst k. rewrite uvm_run1 in Hrep'.
      iDestruct (proc_pt_grow_uvm Pj (pte_flags10 w0) (vpn_at vpn0 j) r tc' m_c
                   Hperm Hwfc Hviewc Hmcnone Hvj26 Hrep' Hbase'' Hpv
                   with "Hkmapb Hptreec Hpage Hownc") as "Hpt".
      set (Pk := uptd_insert_perm Pj (pte_flags10 w0) (vpn_at vpn0 j) r).
      assert (Hextk : uptd_ext Pnew Pk)
        by (exact (uptd_ext_trans Pnew Pj Pk Hext
                     (uptd_ext_insert_perm Pj (pte_flags10 w0) (vpn_at vpn0 j) r Hpjnone))).
      assert (Hpklook : Pk.(ud_um) !! vpn_at vpn0 j = Some (uvm_pte (pte_flags10 w0) r)).
      { rewrite /Pk /uptd_insert_perm. cbn [ud_um]. apply lookup_insert. }
      assert (Hpkne : forall v, v <> vpn_at vpn0 j -> Pk.(ud_um) !! v = Pj.(ud_um) !! v).
      { intros v Hv. rewrite /Pk /uptd_insert_perm. cbn [ud_um].
        apply lookup_insert_ne. exact (not_eq_sym Hv). }
      assert (Hbridge : uvm_pte (pte_flags10 w0) r
                        = pte_set_ad (uvm_pte (pte_flags10 wu) r) au du).
      { rewrite Hw0ad. exact (uc_ad_bridge wu r au du Hvwu0 Hltwu (proj1 (Hleafwu au du))). }
      assert (Hkout : forall v, v ∉ vpn_run vpn0 (S j) ->
                Pk.(ud_um) !! v = Pnew.(ud_um) !! v).
      { intros v Hv.
        assert (Hvne : v <> vpn_at vpn0 j).
        { intro He. apply Hv. rewrite vpn_run_S. apply elem_of_union_r.
          apply elem_of_singleton. exact He. }
        rewrite (Hpkne v Hvne). exact (Hout v (Hsubrun v Hv)). }
      assert (Hkfacts : forall i, (i < S j)%nat -> uc_at Pold Pnew Pk vpn0 i).
      { intros i Hi. destruct (Nat.eq_dec i j) as [-> | Hne].
        - unfold uc_at. rewrite Humsome.
          exists r, (uvm_pte (pte_flags10 w0) r), au, du.
          split_and!; [exact Hpv | exact Hpklook | exact Hbridge].
        - assert (Hij : (i < j)%nat) by (clear -Hi Hne; lia).
          assert (Hvne : vpn_at vpn0 i <> vpn_at vpn0 j)
            by exact (vpn_at_ne vpn0 i j Hij Hjrun).
          pose proof (Hfacts i Hij) as Hfi. unfold uc_at in Hfi |- *.
          rewrite (Hpkne _ Hvne). exact Hfi. }
      assert (Hbz : eq_vec (mg !!! Regidx Ra0) zero_reg = true).
      { rewrite Hga0. vm_compute; reflexivity. }
      assert (Htgt24'' : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x64) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 224 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.uvmcopy + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x64))
                (mword_of_int 224 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                mg (K - 10)%nat b ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; discriminate) Hbz ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi64").
      iIntros (CIDl27 Hsl27). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt24'') in "Hpc".
      iDestruct (cpu_own_transport CIDl26 CIDl27 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      assert (Hshiftl27 : b = false \/ p = zero_reg -> (CIDl27 : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftl27 with "Hexit") as "Hexit".
      iApply ("TAIL" $! CIDl27 mg Pk with "[%] Hcg Hcnt Hpc Hpo Hpt Hexit").
      split_and!; assumption. }
    (* ========== mappages FAILED: free the page and unwind ========== *)
    assert (Hk0 : k = 0%nat) by (clear -Hklt; lia). subst k.
    cbn [pt_insert_run] in Hrep'.
    iDestruct (proc_pt_rebuild Pj tc' m_c Hwfc Hviewc Hrep' Hbase''
                 with "Hptreec Hownc") as "Hpt".
    assert (Hbnz0 : eq_vec (mg !!! Regidx Ra0) zero_reg = false).
    { rewrite Hga0. vm_compute; reflexivity. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x64))
              (mword_of_int 224 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              mg (K - 10)%nat b ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hbnz0 with "Hcg Hpc Hi64").
    iIntros (CIDl27 Hsl27) "Hcg Hpc".
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x64) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    (* --- +0x66 c.mv a0,s2 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x66)) Ra0 Rs2 mg (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66").
    iIntros (CIDl28 Hsl28) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (F1 := <[Regidx Ra0 := regval_into_reg (add_vec zero_reg (mg !!! Regidx Rs2))]> mg).
    assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x66) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* --- +0x68 jal ra,kfree --- *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x68)) Rra
              (mword_of_int 2094552 : mword 21) F1 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi68").
    iIntros (CIDl29 Hsl29) "Hcg Hpc".
    set (F2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x68) : mword 64) 4)]> F1).
    assert (Htgtkf : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x68) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094552 : mword 21))
                     = mword_of_int KernelSyms.kfree)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtkf) in "Hpc".
    assert (HF2ra : F2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x68) : mword 64) 4)
      by (rewrite /F2 upd_eq; reflexivity).
    assert (HF2a0 : F2 !!! Regidx Ra0 = r).
    { rewrite /F2. rewrite upd_ne; [| reg_neq].
      rewrite /F1 upd_eq. rewrite add_vec_zero_l. exact Hmgs2. }
    assert (HF2sp : F2 !!! Regidx csp_rs1 = spr).
    { rewrite /F2 /F1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmgsp. }
    assert (HF2s1 : F2 !!! Regidx Rs1 = iv).
    { rewrite /F2 /F1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmgs1. }
    assert (HF2s7 : F2 !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite /F2 /F1. repeat (rewrite upd_ne; [| reg_neq]). exact Hmgs7. }
    assert (HF2thr : uc_thr mm F2).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      uc_thr_peel. apply Hmgthr; assumption. }
    iDestruct (cpu_own_transport CIDl26 CIDl29 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (Kfree.wp_kfree_sconf kt γa γk (mword_of_int KernelSyms.kmem)
              (mword_of_int (KernelSyms.kmem + 24)) F2 None ilvl eb p (K - 10)%nat b
              _ HKka ltac:(reflexivity) ltac:(reflexivity)
              Hilvl Hbelow
              with "Hcg Hcnt Htext Hpc Hlock [Hpage] Havail").
    all: try lkbelow.
    { rewrite /kfree_pre HF2a0.
      iSplitR; [iPureIntro; exact Hpv | iExact "Hpage"]. }
    iIntros (CIDl30 Hsl30 mf) "Hcg Hcnt Hpc %Hfcs _".
    assert (Hret6c : ret_pc (F2 !!! Regidx Rra) = mword_of_int (KernelSyms.uvmcopy + 0x6c)).
    { rewrite HF2ra. unfold ret_pc. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret6c) in "Hpc".
    assert (Hfsp : mf !!! Regidx csp_rs1 = spr).
    { rewrite (callee_saved_lookup Hfcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HF2sp. }
    assert (Hfs1 : mf !!! Regidx Rs1 = iv).
    { rewrite (callee_saved_lookup Hfcs Rs1 ltac:(vm_compute; reflexivity)). exact HF2s1. }
    assert (Hfs7 : mf !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite (callee_saved_lookup Hfcs Rs7 ltac:(vm_compute; reflexivity)). exact HF2s7. }
    assert (Hfthr : uc_thr mm mf).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      rewrite (callee_saved_lookup Hfcs c Hc). apply HF2thr; assumption. }
    assert (Hshiftl30 : b = false \/ p = zero_reg -> (CIDl30 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshiftl30 with "Hexit") as "Hexit".
    iApply (uc_err (CID0 := CIDl30) γa mm Pold Pnew Pj vpn0 n j K eb p spr iv mf ilvl b lks
              HK Hilvl Hvpn0 Hiv ltac:(clear -Hjb; lia) Hext Hout
              ltac:(intros i Hi; apply Hfresh; clear -Hi Hjn; lia)
              Hfsp Hfs1 Hfs7 Hfthr Hbelow
              with "Hcg Hcnt Htext Hpc Hpo Hpt Henv2 Hexit").
  Qed.


  (* ------------------------------------------------------------------ *)
  (* THE WHOLE FUNCTION.                                                 *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_uvmcopy_sconf
      (γa : gname) (mm : regfile)
      (Pold Pnew : uptd) (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string)
    : wp_uvmcopy_sconf_body kt γa mm Pold Pnew K eb p ilvl b lks.
  Proof.
    cbv beta delta [wp_uvmcopy_sconf_body].
    intros pcE sz vpn0 n ret_tgt HK Hilvl Htp Hroot Hrootn Hszb Hfresh Hbelow.
    assert (Hvpn0 : svpn_of (mword_of_int 0 : mword 64) = vpn0) by reflexivity.
    assert (Hnd : n = uvm_np sz) by reflexivity.
    assert (HK10 : (10 <= K)%nat) by (clear -HK; lia).
    assert (HKback : ((K - 10) + 10)%nat = K) by (clear -HK; lia).
    pose (sp0 := (mm !!! Regidx csp_rs1 : mword 64)).
    iIntros "Hcg Hcnt #Htext Hpc Hpo Hpt #Henv Hcont".
    rewrite uint_unsigned in Hszb. rewrite uvm_maxsz_val in Hszb.
    iPoseProof (uci_00 with "Htext") as "Hi00".
    destruct (eq_vec (mm !!! Regidx Ra2) zero_reg) eqn:Hz0.
    { (* ============ sz == 0: return 0 with NO FRAME ================== *)
      iPoseProof (uci_96 with "Htext") as "Hi96".
      iPoseProof (uci_98 with "Htext") as "Hi98".
      assert (Hszz : sz = (zero_reg : mword 64))
        by (apply eq_vec_true_iff; exact Hz0).
      assert (Hn0 : n = 0%nat).
      { rewrite Hnd. unfold uvm_np. rewrite Hszz.
        assert (Hu : uint (zero_reg : mword 64) = 0%Z) by (vm_compute; reflexivity).
        rewrite Hu. exact uc_z_np_zero. }
      assert (Htgt96 : add_vec (pcE : mword 64)
                (sign_extend' 64
                   (sign_extend' 13 (concat_vec (mword_of_int 75 : mword 8) ('b"0"))))
              = mword_of_int (KernelSyms.uvmcopy + 0x96)) by (apply bv_eq; vm_compute; reflexivity).
      iApply (wp_cbeqz_taken_s_sconf pcE (mword_of_int 75 : mword 8)
                (Cregidx (mword_of_int 4)) Ra2 mm K b
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                Hz0 ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi00").
      iIntros (CIDz1 Hsz1). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt96) in "Hpc".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x96)) Ra0
                (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64) mm K b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi96").
      iIntros (CIDz2 Hsz2) "Hcg Hpc".
      set (Y1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> mm).
      assert (Hp98 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x96) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x98)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp98) in "Hpc".
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x98)) Rra Y1 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi98").
      iIntros (CIDz3 Hsz3) "Hcg Hpc".
      assert (HY1ra : Y1 !!! Regidx Rra = mm !!! Regidx Rra)
        by (rewrite /Y1; rewrite upd_ne; [reflexivity | reg_neq]).
      assert (Hretf : ret_pc (Y1 !!! Regidx Rra) = ret_tgt) by (rewrite HY1ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CID CIDz3 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDz3 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! Y1 with "Hcg Hcnt Hpc [%] Hpo [Hpt]").
      { unfold callee_saved. split_and!;
          (rewrite /Y1; rewrite upd_ne; [reflexivity | reg_neq]). }
      iRight. iExists Pnew.
      iSplitR; [iPureIntro; rewrite /Y1 upd_eq; reflexivity |].
      iSplitR; [iPureIntro; apply uptd_ext_refl |].
      iSplitR; [iPureIntro; intros v _; reflexivity |].
      iSplitR; [iPureIntro; intros i Hi; rewrite Hn0 in Hi; exfalso; clear -Hi; lia |].
      iExact "Hpt". }

    (* ================= sz != 0: push the 80-byte frame ================ *)
    assert (Hszne : sz <> (zero_reg : mword 64))
      by (apply eq_vec_false_iff; exact Hz0).
    pose proof (proj1 (bv_unsigned_in_range _ sz)) as Hszlo.
    assert (Hszpos : (0 < bv_unsigned sz)%Z).
    { destruct (Z.eq_dec (bv_unsigned sz) 0) as [He | He].
      - exfalso. apply Hszne. apply bv_eq. rewrite He. vm_compute. reflexivity.
      - clear -He Hszlo. lia. }
    assert (Hnchar : forall k : nat,
              (4096 * Z.of_nat k < bv_unsigned sz)%Z <-> (k < n)%nat).
    { intros k. rewrite Hnd. unfold uvm_np. rewrite uint_unsigned.
      apply uc_z_nchar. apply uc_z_np_pos. clear -Hszpos; lia. }
    assert (Hnb : (Z.of_nat n < 67108863)%Z).
    { rewrite Hnd. unfold uvm_np. rewrite uint_unsigned.
      rewrite Z2Nat.id;
        [ apply uc_z_np_bound; exact Hszb
        | apply uc_z_np_pos; clear -Hszpos; lia ]. }
    assert (Hn1 : (1 <= n)%nat).
    { assert (Hz : (4096 * Z.of_nat 0 < bv_unsigned sz)%Z)
        by (change (Z.of_nat 0) with 0%Z; clear -Hszpos; lia).
      pose proof (proj1 (Hnchar 0%nat) Hz) as Hx. clear -Hx. lia. }
    iPoseProof (uci_02 with "Htext") as "Hi02".
    iPoseProof (uci_04 with "Htext") as "Hi04".
    iPoseProof (uci_06 with "Htext") as "Hi06".
    iPoseProof (uci_08 with "Htext") as "Hi08".
    iPoseProof (uci_0a with "Htext") as "Hi0a".
    iPoseProof (uci_0c with "Htext") as "Hi0c".
    iPoseProof (uci_0e with "Htext") as "Hi0e".
    iPoseProof (uci_10 with "Htext") as "Hi10".
    iPoseProof (uci_12 with "Htext") as "Hi12".
    iPoseProof (uci_14 with "Htext") as "Hi14".
    iPoseProof (uci_16 with "Htext") as "Hi16".
    iPoseProof (uci_18 with "Htext") as "Hi18".
    iPoseProof (uci_1a with "Htext") as "Hi1a".
    iPoseProof (uci_1c with "Htext") as "Hi1c".
    iPoseProof (uci_1e with "Htext") as "Hi1e".
    iPoseProof (uci_20 with "Htext") as "Hi20".
    iPoseProof (uci_22 with "Htext") as "Hi22".
    assert (Hspm : mm !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (mm !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                    = pa_stk (mm !!! Regidx csp_rs1) 10).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.uvmcopy + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cbeqz_fall_s_sconf pcE (mword_of_int 75 : mword 8)
              (Cregidx (mword_of_int 4)) Ra2 mm K b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) Hz0
              with "Hcg Hpc Hi00").
    iIntros (CIDr1 Hsr1) "Hcg Hpc".
    iEval (rewrite Hp02) in "Hpc".
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x02))
              (mword_of_int 59 : mword 6) mm K 10 b HK10 Hpush
              with "Hcg Hpc Hi02").
    iIntros (CIDr2 Hsr2) "Hcg Hframe Hpc".
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
    iEval (rewrite (stack_own_slots (KTR := kt)); cbn [seq]) in "Hframe".
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
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x02) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    (* --- the nine pushes --- *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x04)) (mword_of_int 9 : mword 6) Rra
              R1 (K - 10)%nat u72 b with "Hcg Hpc Hi04 [Hk1]").
    { iEval (rewrite HspR1 Hb1). iExact "Hk1". }
    iIntros (CIDr3 Hsr3) "Hcg Hpc Hk1". iEval (rgne; rewrite HspR1 Hb1) in "Hk1".
    assert (HR1ra : R1 !!! Regidx Rra = mm !!! Regidx Rra)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1ra) in "Hk1".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x04) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x06)) (mword_of_int 8 : mword 6) Rs0
              R1 (K - 10)%nat u64 b with "Hcg Hpc Hi06 [Hk2]").
    { iEval (rewrite HspR1 Hb2). iExact "Hk2". }
    iIntros (CIDr4 Hsr4) "Hcg Hpc Hk2". iEval (rgne; rewrite HspR1 Hb2) in "Hk2".
    assert (HR1s0 : R1 !!! Regidx Rs0 = mm !!! Regidx Rs0)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s0) in "Hk2".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x06) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x08)) (mword_of_int 7 : mword 6) Rs1
              R1 (K - 10)%nat u56 b with "Hcg Hpc Hi08 [Hk3]").
    { iEval (rewrite HspR1 Hb3). iExact "Hk3". }
    iIntros (CIDr5 Hsr5) "Hcg Hpc Hk3". iEval (rgne; rewrite HspR1 Hb3) in "Hk3".
    assert (HR1s1 : R1 !!! Regidx Rs1 = mm !!! Regidx Rs1)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s1) in "Hk3".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x08) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x0a)) (mword_of_int 6 : mword 6) Rs2
              R1 (K - 10)%nat u48 b with "Hcg Hpc Hi0a [Hk4]").
    { iEval (rewrite HspR1 Hb4). iExact "Hk4". }
    iIntros (CIDr6 Hsr6) "Hcg Hpc Hk4". iEval (rgne; rewrite HspR1 Hb4) in "Hk4".
    assert (HR1s2 : R1 !!! Regidx Rs2 = mm !!! Regidx Rs2)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s2) in "Hk4".
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x0a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x0c)) (mword_of_int 5 : mword 6) Rs3
              R1 (K - 10)%nat u40 b with "Hcg Hpc Hi0c [Hk5]").
    { iEval (rewrite HspR1 Hb5). iExact "Hk5". }
    iIntros (CIDr7 Hsr7) "Hcg Hpc Hk5". iEval (rgne; rewrite HspR1 Hb5) in "Hk5".
    assert (HR1s3 : R1 !!! Regidx Rs3 = mm !!! Regidx Rs3)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s3) in "Hk5".
    assert (Hp0e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x0c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0e) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x0e)) (mword_of_int 4 : mword 6) Rs4
              R1 (K - 10)%nat u32 b with "Hcg Hpc Hi0e [Hk6]").
    { iEval (rewrite HspR1 Hb6). iExact "Hk6". }
    iIntros (CIDr8 Hsr8) "Hcg Hpc Hk6". iEval (rgne; rewrite HspR1 Hb6) in "Hk6".
    assert (HR1s4 : R1 !!! Regidx Rs4 = mm !!! Regidx Rs4)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s4) in "Hk6".
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x0e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x10)) (mword_of_int 3 : mword 6) Rs5
              R1 (K - 10)%nat u24 b with "Hcg Hpc Hi10 [Hk7]").
    { iEval (rewrite HspR1 Hb7). iExact "Hk7". }
    iIntros (CIDr9 Hsr9) "Hcg Hpc Hk7". iEval (rgne; rewrite HspR1 Hb7) in "Hk7".
    assert (HR1s5 : R1 !!! Regidx Rs5 = mm !!! Regidx Rs5)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s5) in "Hk7".
    assert (Hp12 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x10) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp12) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x12)) (mword_of_int 2 : mword 6) Rs6
              R1 (K - 10)%nat u16 b with "Hcg Hpc Hi12 [Hk8]").
    { iEval (rewrite HspR1 Hb8). iExact "Hk8". }
    iIntros (CIDr10 Hsr10) "Hcg Hpc Hk8". iEval (rgne; rewrite HspR1 Hb8) in "Hk8".
    assert (HR1s6 : R1 !!! Regidx Rs6 = mm !!! Regidx Rs6)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s6) in "Hk8".
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x12) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x14)) (mword_of_int 1 : mword 6) Rs7
              R1 (K - 10)%nat u8 b with "Hcg Hpc Hi14 [Hk9]").
    { iEval (rewrite HspR1 Hb9). iExact "Hk9". }
    iIntros (CIDr11 Hsr11) "Hcg Hpc Hk9". iEval (rgne; rewrite HspR1 Hb9) in "Hk9".
    assert (HR1s7 : R1 !!! Regidx Rs7 = mm !!! Regidx Rs7)
      by (rewrite /R1; rewrite upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite HR1s7) in "Hk9".
    assert (Hp16 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x14) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp16) in "Hpc".
    (* --- +0x16 c.addi4spn s0,sp,80 --- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x16)) (Cregidx (mword_of_int 0))
              (mword_of_int 20 : mword 8) Rs0 R1 (K - 10)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi16").
    iIntros (CIDr12 Hsr12) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> R1).
    assert (Hp18 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x16) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp18) in "Hpc".
    (* --- +0x18 c.mv s6,a0 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x18)) Rs6 Ra0 R2 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18").
    iIntros (CIDr13 Hsr13) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R3 := <[Regidx Rs6 := regval_into_reg (add_vec zero_reg (R2 !!! Regidx Ra0))]> R2).
    assert (Hp1a : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x18) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1a) in "Hpc".
    (* --- +0x1a c.mv s7,a1 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x1a)) Rs7 Ra1 R3 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a").
    iIntros (CIDr14 Hsr14) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R4 := <[Regidx Rs7 := regval_into_reg (add_vec zero_reg (R3 !!! Regidx Ra1))]> R3).
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x1a) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    (* --- +0x1c c.mv s5,a2 --- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x1c)) Rs5 Ra2 R4 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iIntros (CIDr15 Hsr15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R5 := <[Regidx Rs5 := regval_into_reg (add_vec zero_reg (R4 !!! Regidx Ra2))]> R4).
    assert (Hp1e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x1c) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1e) in "Hpc".
    (* --- +0x1e c.li s1,0 --- *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x1e)) Rs1 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) R5 (K - 10)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity) with "Hcg Hpc Hi1e").
    iIntros (CIDr16 Hsr16) "Hcg Hpc".
    set (R6 := <[Regidx Rs1 := regval_into_reg (mword_of_int 0 : mword 64)]> R5).
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x1e) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    (* --- +0x20 c.lui s4,0x1 --- *)
    iApply (wp_clui_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x20)) Rs4
              (sign_extend' 20 (mword_of_int 1 : mword 6)) (mword_of_int 4096 : mword 64)
              R6 (K - 10)%nat b ltac:(vm_compute; discriminate)
              ltac:(rdok) lui_4096 with "Hcg Hpc Hi20").
    iIntros (CIDr17 Hsr17) "Hcg Hpc".
    set (R7 := <[Regidx Rs4 := regval_into_reg (mword_of_int 4096 : mword 64)]> R6).
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x20) : mword 64) 2
                   = mword_of_int (KernelSyms.uvmcopy + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* --- the register facts at the loop head --- *)
    assert (HR7sp : R7 !!! Regidx csp_rs1 = spr).
    { rewrite /R7 /R6 /R5 /R4 /R3 /R2. repeat (rewrite upd_ne; [| reg_neq]). exact HspR1. }
    assert (HR7s1 : R7 !!! Regidx Rs1 = (mword_of_int 0 : mword 64)).
    { rewrite /R7. rewrite upd_ne; [| reg_neq]. rewrite /R6 upd_eq. reflexivity. }
    assert (HR7s4 : R7 !!! Regidx Rs4 = (mword_of_int 4096 : mword 64))
      by (rewrite /R7 upd_eq; reflexivity).
    assert (HR7s5 : R7 !!! Regidx Rs5 = sz).
    { rewrite /R7. rewrite upd_ne; [| reg_neq].
      rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5 upd_eq. rewrite add_vec_zero_l.
      rewrite /R4. rewrite upd_ne; [| reg_neq].
      rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [reflexivity | reg_neq]. }
    assert (HR7s6 : R7 !!! Regidx Rs6 = page_base Pold.(ud_root)).
    { rewrite /R7. rewrite upd_ne; [| reg_neq].
      rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq].
      rewrite /R4. rewrite upd_ne; [| reg_neq].
      rewrite /R3 upd_eq. rewrite add_vec_zero_l.
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [| reg_neq]. exact Hroot. }
    assert (HR7s7 : R7 !!! Regidx Rs7 = page_base Pnew.(ud_root)).
    { rewrite /R7. rewrite upd_ne; [| reg_neq].
      rewrite /R6. rewrite upd_ne; [| reg_neq].
      rewrite /R5. rewrite upd_ne; [| reg_neq].
      rewrite /R4 upd_eq. rewrite add_vec_zero_l.
      rewrite /R3. rewrite upd_ne; [| reg_neq].
      rewrite /R2. rewrite upd_ne; [| reg_neq].
      rewrite /R1. rewrite upd_ne; [| reg_neq]. exact Hrootn. }
    assert (HR7thr : uc_thr mm R7).
    { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
      uc_thr_peel. reflexivity. }
    (* ================================================================= *)
    (*  THE EPILOGUE / JOIN at +0x80, taken before entering the loop.     *)
    (* ================================================================= *)
    iPoseProof (uci_80 with "Htext") as "Hi80".
    iPoseProof (uci_82 with "Htext") as "Hi82".
    iPoseProof (uci_84 with "Htext") as "Hi84".
    iPoseProof (uci_86 with "Htext") as "Hi86".
    iPoseProof (uci_88 with "Htext") as "Hi88".
    iPoseProof (uci_8a with "Htext") as "Hi8a".
    iPoseProof (uci_8c with "Htext") as "Hi8c".
    iPoseProof (uci_8e with "Htext") as "Hi8e".
    iPoseProof (uci_90 with "Htext") as "Hi90".
    iPoseProof (uci_92 with "Htext") as "Hi92".
    iPoseProof (uci_94 with "Htext") as "Hi94".
    iAssert (uc_exit (kt := kt) (CID0 := CIDr17) mm Pold Pnew vpn0 n K eb p spr ilvl b lks)
      with "[Hcont Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10]" as "Hepi".
    { rewrite /uc_exit.
      iIntros (CIDep Hsep mj res) "(%Hjsp & %Hja0 & %Hjthr) Hcg Hcnt Hpc Hpo Hpost".
      assert (Hshiftep : b = false \/ p = zero_reg -> (CIDep : CPU) = (CID : CPU)) by wp_next_chain.
      iDestruct (wp_next_shift Hshiftep with "Hcont") as "Hcont".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x80)) (mword_of_int 9 : mword 6) Rra
                mj (K - 10)%nat (mm !!! Regidx Rra) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi80 [Hk1]").
      { iEval (rewrite Hjsp Hb1). iExact "Hk1". }
      iIntros (CIDf1 Hsf1) "Hcg Hpc Hk1". iEval (rewrite Hjsp Hb1) in "Hk1".
      set (E1 := <[Regidx Rra := regval_into_reg (mm !!! Regidx Rra)]> mj).
      assert (HE1sp : E1 !!! Regidx csp_rs1 = spr)
        by (rewrite /E1; rewrite upd_ne; [exact Hjsp | reg_neq]).
      assert (Hq82 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x80) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x82)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq82) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x82)) (mword_of_int 8 : mword 6) Rs0
                E1 (K - 10)%nat (mm !!! Regidx Rs0) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi82 [Hk2]").
      { iEval (rewrite HE1sp Hb2). iExact "Hk2". }
      iIntros (CIDf2 Hsf2) "Hcg Hpc Hk2". iEval (rewrite HE1sp Hb2) in "Hk2".
      set (E2 := <[Regidx Rs0 := regval_into_reg (mm !!! Regidx Rs0)]> E1).
      assert (HE2sp : E2 !!! Regidx csp_rs1 = spr)
        by (rewrite /E2; rewrite upd_ne; [exact HE1sp | reg_neq]).
      assert (Hq84 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x82) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x84)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq84) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x84)) (mword_of_int 7 : mword 6) Rs1
                E2 (K - 10)%nat (mm !!! Regidx Rs1) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi84 [Hk3]").
      { iEval (rewrite HE2sp Hb3). iExact "Hk3". }
      iIntros (CIDf3 Hsf3) "Hcg Hpc Hk3". iEval (rewrite HE2sp Hb3) in "Hk3".
      set (E3 := <[Regidx Rs1 := regval_into_reg (mm !!! Regidx Rs1)]> E2).
      assert (HE3sp : E3 !!! Regidx csp_rs1 = spr)
        by (rewrite /E3; rewrite upd_ne; [exact HE2sp | reg_neq]).
      assert (Hq86 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x84) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x86)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq86) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x86)) (mword_of_int 6 : mword 6) Rs2
                E3 (K - 10)%nat (mm !!! Regidx Rs2) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi86 [Hk4]").
      { iEval (rewrite HE3sp Hb4). iExact "Hk4". }
      iIntros (CIDf4 Hsf4) "Hcg Hpc Hk4". iEval (rewrite HE3sp Hb4) in "Hk4".
      set (E4 := <[Regidx Rs2 := regval_into_reg (mm !!! Regidx Rs2)]> E3).
      assert (HE4sp : E4 !!! Regidx csp_rs1 = spr)
        by (rewrite /E4; rewrite upd_ne; [exact HE3sp | reg_neq]).
      assert (Hq88 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x86) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x88)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq88) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x88)) (mword_of_int 5 : mword 6) Rs3
                E4 (K - 10)%nat (mm !!! Regidx Rs3) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi88 [Hk5]").
      { iEval (rewrite HE4sp Hb5). iExact "Hk5". }
      iIntros (CIDf5 Hsf5) "Hcg Hpc Hk5". iEval (rewrite HE4sp Hb5) in "Hk5".
      set (E5 := <[Regidx Rs3 := regval_into_reg (mm !!! Regidx Rs3)]> E4).
      assert (HE5sp : E5 !!! Regidx csp_rs1 = spr)
        by (rewrite /E5; rewrite upd_ne; [exact HE4sp | reg_neq]).
      assert (Hq8a : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x88) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x8a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq8a) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x8a)) (mword_of_int 4 : mword 6) Rs4
                E5 (K - 10)%nat (mm !!! Regidx Rs4) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi8a [Hk6]").
      { iEval (rewrite HE5sp Hb6). iExact "Hk6". }
      iIntros (CIDf6 Hsf6) "Hcg Hpc Hk6". iEval (rewrite HE5sp Hb6) in "Hk6".
      set (E6 := <[Regidx Rs4 := regval_into_reg (mm !!! Regidx Rs4)]> E5).
      assert (HE6sp : E6 !!! Regidx csp_rs1 = spr)
        by (rewrite /E6; rewrite upd_ne; [exact HE5sp | reg_neq]).
      assert (Hq8c : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x8a) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x8c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq8c) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x8c)) (mword_of_int 3 : mword 6) Rs5
                E6 (K - 10)%nat (mm !!! Regidx Rs5) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi8c [Hk7]").
      { iEval (rewrite HE6sp Hb7). iExact "Hk7". }
      iIntros (CIDf7 Hsf7) "Hcg Hpc Hk7". iEval (rewrite HE6sp Hb7) in "Hk7".
      set (E7 := <[Regidx Rs5 := regval_into_reg (mm !!! Regidx Rs5)]> E6).
      assert (HE7sp : E7 !!! Regidx csp_rs1 = spr)
        by (rewrite /E7; rewrite upd_ne; [exact HE6sp | reg_neq]).
      assert (Hq8e : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x8c) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x8e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq8e) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x8e)) (mword_of_int 2 : mword 6) Rs6
                E7 (K - 10)%nat (mm !!! Regidx Rs6) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi8e [Hk8]").
      { iEval (rewrite HE7sp Hb8). iExact "Hk8". }
      iIntros (CIDf8 Hsf8) "Hcg Hpc Hk8". iEval (rewrite HE7sp Hb8) in "Hk8".
      set (E8 := <[Regidx Rs6 := regval_into_reg (mm !!! Regidx Rs6)]> E7).
      assert (HE8sp : E8 !!! Regidx csp_rs1 = spr)
        by (rewrite /E8; rewrite upd_ne; [exact HE7sp | reg_neq]).
      assert (Hq90 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x8e) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x90)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq90) in "Hpc".
      iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x90)) (mword_of_int 1 : mword 6) Rs7
                E8 (K - 10)%nat (mm !!! Regidx Rs7) b (dqm:=DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi90 [Hk9]").
      { iEval (rewrite HE8sp Hb9). iExact "Hk9". }
      iIntros (CIDf9 Hsf9) "Hcg Hpc Hk9". iEval (rewrite HE8sp Hb9) in "Hk9".
      set (E9 := <[Regidx Rs7 := regval_into_reg (mm !!! Regidx Rs7)]> E8).
      assert (HE9sp : E9 !!! Regidx csp_rs1 = spr)
        by (rewrite /E9; rewrite upd_ne; [exact HE8sp | reg_neq]).
      assert (Hq92 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x90) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x92)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq92) in "Hpc".
      (* --- +0x92 c.addi16sp sp,80 : trade the frame back --- *)
      set (E10 := <[Regidx csp_rs1 := regval_into_reg
                     (add_vec (E9 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9).
      assert (Hwv : add_vec (E9 !!! Regidx csp_rs1)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))) = sp0).
      { rewrite HE9sp. unfold spr, sp0. apply frame_cancel_80. }
      assert (Hpop : E9 !!! Regidx csp_rs1
                     = pa_stk (add_vec (E9 !!! Regidx csp_rs1)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10).
      { rewrite Hwv HE9sp. symmetry. exact Hsprstk. }
      iAssert (stack_own (KTR := kt) sp0 10) with "[Hk1 Hk2 Hk3 Hk4 Hk5 Hk6 Hk7 Hk8 Hk9 Hk10]"
        as "Hframe10".
      { rewrite (stack_own_slots (KTR := kt)). cbn [seq].
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
      iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x92))
                (mword_of_int 5 : mword 6) E9 (K - 10)%nat 10 b Hpop
                with "Hcg Hpc Hi92 Hframe10").
      iIntros (CIDf10 Hsf10) "Hcg Hpc".
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (E9 !!! Regidx csp_rs1)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> E9) with E10.
      iEval (rewrite HKback) in "Hcg".
      assert (Hq94 : add_vec_int (mword_of_int (KernelSyms.uvmcopy + 0x92) : mword 64) 2
                     = mword_of_int (KernelSyms.uvmcopy + 0x94)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hq94) in "Hpc".
      (* --- +0x94 c.ret --- *)
      assert (HE10ra : E10 !!! Regidx Rra = mm !!! Regidx Rra).
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2.
        repeat (rewrite upd_ne; [| reg_neq]). rewrite /E1 upd_eq. reflexivity. }
      assert (HE10a0 : E10 !!! Regidx Ra0 = res).
      { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (rewrite upd_ne; [| reg_neq]). exact Hja0. }
      assert (HE10thr : uc_thr mm E10).
      { intros c Hc H2 H8 H9 H18 H19 H20 H21 H22 H23.
        uc_thr_peel. apply Hjthr; assumption. }
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x94)) Rra E10 K b
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hi94").
      iIntros (CIDf11 Hsf11) "Hcg Hpc".
      assert (Hretf : ret_pc (E10 !!! Regidx Rra) = ret_tgt) by (rewrite HE10ra; reflexivity).
      iEval (rewrite Hretf) in "Hpc".
      iDestruct (cpu_own_transport CIDep CIDf11 ilvl eb p b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont" $! CIDf11 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! E10 with "Hcg Hcnt Hpc [%] Hpo [Hpost]").
      2:{ rewrite /uc_pay. rewrite HE10a0.
          iDestruct "Hpost" as "[(%Hz & Hp) | Hs]".
          - iLeft. iSplitR; [iPureIntro; exact Hz | iExact "Hp"].
          - iRight. iExact "Hs". }
      { unfold callee_saved.
        assert (Hc2 : E10 !!! Regidx csp_rs1 = mm !!! Regidx csp_rs1).
        { rewrite /E10 upd_eq. exact Hwv. }
        assert (Hc8 : E10 !!! Regidx Rs0 = mm !!! Regidx Rs0).
        { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4 /E3.
          repeat (rewrite upd_ne; [| reg_neq]). rewrite /E2 upd_eq. reflexivity. }
        assert (Hc9 : E10 !!! Regidx Rs1 = mm !!! Regidx Rs1).
        { rewrite /E10 /E9 /E8 /E7 /E6 /E5 /E4.
          repeat (rewrite upd_ne; [| reg_neq]). rewrite /E3 upd_eq. reflexivity. }
        assert (Hc18 : E10 !!! Regidx Rs2 = mm !!! Regidx Rs2).
        { rewrite /E10 /E9 /E8 /E7 /E6 /E5.
          repeat (rewrite upd_ne; [| reg_neq]). rewrite /E4 upd_eq. reflexivity. }
        assert (Hc19 : E10 !!! Regidx Rs3 = mm !!! Regidx Rs3).
        { rewrite /E10 /E9 /E8 /E7 /E6.
          repeat (rewrite upd_ne; [| reg_neq]). rewrite /E5 upd_eq. reflexivity. }
        assert (Hc20 : E10 !!! Regidx Rs4 = mm !!! Regidx Rs4).
        { rewrite /E10 /E9 /E8 /E7.
          repeat (rewrite upd_ne; [| reg_neq]). rewrite /E6 upd_eq. reflexivity. }
        assert (Hc21 : E10 !!! Regidx Rs5 = mm !!! Regidx Rs5).
        { rewrite /E10 /E9 /E8.
          repeat (rewrite upd_ne; [| reg_neq]). rewrite /E7 upd_eq. reflexivity. }
        assert (Hc22 : E10 !!! Regidx Rs6 = mm !!! Regidx Rs6).
        { rewrite /E10 /E9. repeat (rewrite upd_ne; [| reg_neq]).
          rewrite /E8 upd_eq. reflexivity. }
        assert (Hc23 : E10 !!! Regidx Rs7 = mm !!! Regidx Rs7).
        { rewrite /E10. rewrite upd_ne; [| reg_neq]. rewrite /E9 upd_eq. reflexivity. }
        split_and!;
          first [ exact Hc2 | exact Hc8 | exact Hc9 | exact Hc18 | exact Hc19
                | exact Hc20 | exact Hc21 | exact Hc22 | exact Hc23
                | apply HE10thr; vm_compute; first [reflexivity | discriminate] ]. } }
    (* --- +0x22 c.j +0x08 : enter the loop at its head --- *)
    assert (Hjt22 : add_vec (mword_of_int (KernelSyms.uvmcopy + 0x22) : mword 64)
              (sign_extend' 64
                 (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0"))))
            = mword_of_int (KernelSyms.uvmcopy + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.uvmcopy + 0x22))
              (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")))
              R7 (K - 10)%nat b ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22").
    iIntros (CIDr18 Hsr18). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hjt22) in "Hpc".
    assert (Hiv0 : bv_unsigned (mword_of_int 0 : mword 64) = (4096 * Z.of_nat 0)%Z)
      by (vm_compute; reflexivity).
    assert (Hshiftr18 : b = false \/ p = zero_reg -> (CIDr18 : CPU) = (CIDr17 : CPU)) by wp_next_chain.
    iDestruct (wp_next_shift Hshiftr18 with "Hepi") as "Hepi".
    iDestruct (cpu_own_transport CID CIDr18 ilvl eb p b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iApply (uc_loop γa mm Pold Pnew vpn0 n K eb p spr sz (bv_unsigned sz) ilvl b lks
              HK Hilvl Hvpn0 ltac:(reflexivity) Hszb Hnchar Hnb Hfresh
              n 0%nat Pnew R7 (mword_of_int 0) CIDr18
              ltac:(clear -Hn1; lia) Hn1 Hiv0 (uptd_ext_refl Pnew)
              ltac:(intros v _; reflexivity) ltac:(intros i Hi; exfalso; clear -Hi; lia)
              HR7sp HR7s1 HR7s4 HR7s5 HR7s6 HR7s7 HR7thr Hbelow
              with "Hcg Hcnt Htext Hpc Hpo Hpt Henv Hepi").
  Qed.

End ProofUvmcopy.
End UvmcopyProof.
