(* WpUmodeStore.v -- THE MEMORY-WRITING LEAF of the verified user-execution
   tier (claude-notes/projects/user-verified.md, user-sh.md): the generic
   [wp_uv_store], instantiated at [sd] / [sw] / [sb] / [c.sd] / [c.sw] /
   [c.sdsp].  The exact mirror of WpUmodeLoad.v, section for section.

   Every other leaf (WpUmodeLeaf.v) rides the retire funnel [wp_uv_retire],
   whose post-execute state is a PURE register tower ([uv_post] = an
   optional nextPC redirect then an optional gpr write) reached at the
   EMPTY byte map.  A store leaves that tower behind twice over: it writes
   MEMORY, and -- because the store's own [translateAddr] may fill the TLB
   or write back A/D -- its post state is not even a function of the pre
   state.  So this file adds, ALONGSIDE the funnel (nothing in
   WpUmodeStep.v is restructured):

   §0 [ustore_width] -- the per-width side conditions bundled as ONE
      premise ([ustore_width_1] / [_2] / [_4] / [_8] discharge it): the ISA
      width itself, plus the ONE width-TYPED byte-level brick the model's
      [write_ram] reduction bottoms out in.  WpUmodeLoad's [uload_width] is
      the load twin.

   §1 [uM_store M a k v] -- the image-level effect: the low [k]
      little-endian bytes of the register word [v] land at [a .. a+k-1].
      Spelled as the same [foldr]-of-inserts the model's [write_bytes] is,
      which is what makes [upa_map_store] -- the re-keyed image after the
      store IS the model's [write_bytes] of the re-keyed image before --
      an insert-by-insert induction rather than a pointwise argument.
      [uM_store8 M a v := uM_store M a 8 v] and the whole [uM_store8_*]
      family are its k = 8 readings, kept verbatim for the UProof* files.

   §2 THE PORT'S CENTRE.  Per-node semantics own the process image as the
      hart's own BYTE MAP [uv_mm t (upa_map pt M)], so a store is no longer
      a [gen_heap_interp] update behind an Iris composer: it is a PURE
      [exec]-plus-[goodmb] pair over that map, and the ghost half is the
      map equation of §1.  [uv_walk_data] is WpUmodeStep's [uv_walk_fetch]
      at a DATA access type -- the safety tier's [UserMemCert.u_walk_pure]
      says the same thing but only at [u_mem_wf] (it owns every mapped data
      byte) and pins the landing map by its DOMAIN, and this tier has
      neither.  [uv_store_mm] is the store on top of it, landing on
      [write_bytes] of the named map.

   §3 [exec_execute_STORE_k_u_walk] / [goodmb_execute_STORE_k_u_walk] --
      the value-precise execute at User privilege with MPRV = 0, and its
      certificate, both assembled from the safety tier's U-mode memory
      arms.  THE AUTOCAST TRAP lives here: the model hands [vmem_write] the
      width-typed [ustore_data k v] (an [autocast] of a [subrange] of rs2)
      and the split loop projects a chunk at the index expressions
      [8*(0+1)*k-1] / [8*0*k]; the leading factors are closed, so a
      [change] to the reduced indices makes [subrange_full_gen_cast] fire
      at symbolic [k].  [nth_byte_ustore_data] is the bridge back to the
      image.

   §4 [uv_res_reimg] / [uv_swp_exec_mem] -- the two things the funnel's
      tail cannot do.  The engine's residue [uv_res pt M t] closes back to
      [umem pt M] at the image it was OPENED at, and a store's image is a
      different one; but the residue's only RESOURCE is the persistent
      [pt_claims], so the residue at ANY image is rebuilt from it plus the
      two pure pins ([upt_satp_ok_pt] / [pmp_ent0_ok]) that [u_exec_pins]
      already carries.  [uv_swp_exec_mem] is [WpUmodeStep.uv_swp_exec] with
      the byte map REAL and MOVING instead of empty and fixed.

   §5 [uv_store_post_fetch] -- the geometry-agnostic middle, the store's
      [uv_retire_post_fetch]: from the fetched file, write nextPC, run the
      store, and hand [uv_psi_active] the payload at the NEW image and the
      UNCHANGED register file.

   §6 [wp_uv_store] -- ONE width-generic leaf over all four fetch
      geometries, plus the six instances. *)
From Stdlib Require Import ZArith Bool Lia List FunctionalExtensionality.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants gen_heap.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import WpGpr RegFile InstrBytes.
Require Import SmodeCore.
Require Import WpDecodeBridge DecodeTotalU.
Require Import CommonWalk.
Require Import PtreeType PtAdBits PtTree PtTreeAdue KptPt KptTree.
Require Import SRegime UptTree UptWalkPt.
Require Import UserBits UserPtTree UserTranslate.
Require Import HartSwp HartLift HartSpan HartGoodb HartMemRun HartMCycle
        HartStepFull HartRunFull HartRunGen.
Require Import PtBytes UserBytes UserFrame UserClassifyAsm.
Require Import UserFetchCert PtWalkCert.
Require Import UserExec.
Require UserTotalU.
Require Import UserActiveClass.
Require Import MemAccessGen WpMmodeLeafBase.
Require Import UserMemPt UserMemArms UserMemClassify UserMemAccess UserMemMis.
Require Import UserMemCert UserMemArmsBase UserMemArmsC.
Require Import UmodeMem UmodeCap UmodeFetch.
Require Import WpUmodeStep.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* ===================================================================== *)
(* §0 The per-width side conditions.                                      *)
(* ===================================================================== *)

(* RELOCATION DEBT: these three read naturally beside [vmem_width] itself
   (RiscvExtras.v).  WpUmodeLoad.v carries its own copies under the names
   [vmem_width_le8] / [_dvd] / [_uint]; that file sits ABOVE this one and
   cannot be imported here, so the readings are spelled again with local
   names.  Retire both copies into RiscvExtras at the next sweep. *)
Lemma uvw_le8 (k : Z) : vmem_width k -> k <= 8.
Proof. intros [-> | [-> | [-> | ->]]]; lia. Qed.

Lemma uvw_dvd (k : Z) : vmem_width k -> (k | 4096).
Proof.
  intros [-> | [-> | [-> | ->]]];
    [ exists 4096 | exists 2048 | exists 1024 | exists 512 ]; reflexivity.
Qed.

Lemma uvw_uint (k : Z) : vmem_width k -> uint (to_bits 64 k) = k.
Proof. intros [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. Qed.

(* Everything a store leaf needs to know about its access width: the ISA
   width itself, plus the ONE width-TYPED byte-level brick the model's
   [write_ram] reduction bottoms out in (the exact mirror of WpUmodeLoad's
   [uload_width], and the [Hwrite_plain] half of UserMemPt's width-generic
   section). *)
Definition ustore_width (k : Z) : Prop :=
  vmem_width k /\
  (forall (addr : mword 64) (data : mword (8 * k)) (s : mstate),
     dev_addr addr = false ->
     exec (write_ram rv64d_types.Write_plain (Physaddr addr) k data tt) s
     = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

Lemma ustore_width_1 : ustore_width 1.
Proof. split; [ left; reflexivity | exact exec_write_ram_plain_1 ]. Qed.

Lemma ustore_width_2 : ustore_width 2.
Proof. split; [ right; left; reflexivity | exact exec_write_ram_plain_2 ]. Qed.

Lemma ustore_width_4 : ustore_width 4.
Proof. split; [ right; right; left; reflexivity | exact exec_write_ram_plain_4 ]. Qed.

Lemma ustore_width_8 : ustore_width 8.
Proof.
  split; [ right; right; right; reflexivity | exact exec_write_ram_plain_8 ].
Qed.

(* ===================================================================== *)
(* §1 The image-level effect of a k-byte store.                           *)
(* ===================================================================== *)

(* [M] with the low [k] little-endian bytes of the register value [v]
   written at [a .. a+k-1].  Spelled as the same [foldr]-of-inserts the
   model's [write_bytes] is, so the re-keying equation below is an
   insert-by-insert induction.

   The value stays a WHOLE 64-bit register word at every width: that is
   what a call site holds ([m !!! Regidx rs2]), and the model's own
   truncation to [mword (8*k)] agrees with it byte for byte on the [k]
   bytes that are written ([nth_byte_ustore_data], §3). *)
Definition uM_store (M : gmap Z (bv 8)) (a k : Z) (v : mword 64) : gmap Z (bv 8) :=
  foldr (fun (j : nat) (acc : gmap Z (bv 8)) => <[a + Z.of_nat j := nth_byte v j]> acc)
        M (seq 0 (Z.to_nat k)).

Definition uM_store8 (M : gmap Z (bv 8)) (a : Z) (v : mword 64) : gmap Z (bv 8) :=
  uM_store M a 8 v.

(* an insert run never removes a key *)
Lemma uM_fold_is_Some (a : Z) (v : mword 64) (l : list nat)
    (M : gmap Z (bv 8)) (k : Z) :
  is_Some (M !! k) ->
  is_Some (foldr (fun (j : nat) (acc : gmap Z (bv 8)) =>
                    <[a + Z.of_nat j := nth_byte v j]> acc) M l !! k).
Proof.
  induction l as [ | x xs IH ]; cbn [foldr]; [ tauto | ].
  intro H. destruct (decide (k = a + Z.of_nat x)) as [-> | Hne].
  - rewrite lookup_insert. exact (mk_is_Some _ _ eq_refl).
  - rewrite lookup_insert_ne; [ apply IH; exact H | congruence ].
Qed.

Lemma uM_store_is_Some (M : gmap Z (bv 8)) (a k : Z) (v : mword 64) (key : Z) :
  is_Some (M !! key) -> is_Some (uM_store M a k v !! key).
Proof. apply uM_fold_is_Some. Qed.

Lemma uM_store8_is_Some (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  is_Some (M !! k) -> is_Some (uM_store8 M a v !! k).
Proof. apply uM_fold_is_Some. Qed.

(* the run's own keys *)
Lemma uM_fold_lookup (a : Z) (v : mword 64) (l : list nat)
    (M : gmap Z (bv 8)) (j : nat) :
  In j l ->
  foldr (fun (jj : nat) (acc : gmap Z (bv 8)) =>
           <[a + Z.of_nat jj := nth_byte v jj]> acc) M l !! (a + Z.of_nat j)
  = Some (nth_byte v j).
Proof.
  induction l as [ | x xs IH ]; cbn [foldr]; [ intros [] | ].
  intro Hin. destruct (decide (j = x)) as [-> | Hne].
  - apply lookup_insert.
  - rewrite lookup_insert_ne; [ | intro He; apply Hne; lia ].
    apply IH. destruct Hin as [-> | Hin]; [ exfalso; exact (Hne eq_refl) | exact Hin ].
Qed.

Lemma uM_store_lookup (M : gmap Z (bv 8)) (a k : Z) (v : mword 64) (j : nat) :
  (j < Z.to_nat k)%nat ->
  uM_store M a k v !! (a + Z.of_nat j) = Some (nth_byte v j).
Proof.
  intro Hj. unfold uM_store. apply uM_fold_lookup. apply in_seq. lia.
Qed.

(* ... in the [uM_bytes] shape the fetch/ABI layer speaks *)
Lemma uM_store_bytes (M : gmap Z (bv 8)) (a k : Z) (v : mword 64) :
  uM_bytes (uM_store M a k v) a (Z.to_nat k) v.
Proof. intros j Hj. exact (uM_store_lookup M a k v j Hj). Qed.

(* the eight width-8 keys, spelled out (the shape three proof files use) *)
Lemma uM_store8_lookup (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_store8 M a v !! (a + 0) = Some (nth_byte v 0) /\
  uM_store8 M a v !! (a + 1) = Some (nth_byte v 1) /\
  uM_store8 M a v !! (a + 2) = Some (nth_byte v 2) /\
  uM_store8 M a v !! (a + 3) = Some (nth_byte v 3) /\
  uM_store8 M a v !! (a + 4) = Some (nth_byte v 4) /\
  uM_store8 M a v !! (a + 5) = Some (nth_byte v 5) /\
  uM_store8 M a v !! (a + 6) = Some (nth_byte v 6) /\
  uM_store8 M a v !! (a + 7) = Some (nth_byte v 7).
Proof.
  unfold uM_store8, uM_store. change (Z.to_nat 8) with 8%nat. cbn [seq foldr].
  split_and!;
    repeat (rewrite lookup_insert_ne; [ | lia ]);
    apply lookup_insert.
Qed.

Lemma uM_store8_bytes (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_bytes (uM_store8 M a v) a 8 v.
Proof. exact (uM_store_bytes M a 8 v). Qed.

(* keys off the run are untouched *)
Lemma uM_fold_lookup_ne (a : Z) (v : mword 64) (l : list nat)
    (M : gmap Z (bv 8)) (key : Z) :
  (forall j : nat, In j l -> key <> a + Z.of_nat j) ->
  foldr (fun (jj : nat) (acc : gmap Z (bv 8)) =>
           <[a + Z.of_nat jj := nth_byte v jj]> acc) M l !! key = M !! key.
Proof.
  induction l as [ | x xs IH ]; cbn [foldr]; [ reflexivity | ].
  intro Hne. rewrite lookup_insert_ne.
  - apply IH. intros j Hj. apply Hne. right. exact Hj.
  - intro He. exact (Hne x (or_introl eq_refl) (eq_sym He)).
Qed.

Lemma uM_store_lookup_ne (M : gmap Z (bv 8)) (a k : Z) (v : mword 64) (key : Z) :
  (forall j : nat, (j < Z.to_nat k)%nat -> key <> a + Z.of_nat j) ->
  uM_store M a k v !! key = M !! key.
Proof.
  intro Hne. unfold uM_store. apply uM_fold_lookup_ne.
  intros j Hj. apply Hne. apply in_seq in Hj. lia.
Qed.

Lemma uM_store8_lookup_ne (M : gmap Z (bv 8)) (a : Z) (v : mword 64) (k : Z) :
  (forall j : nat, (j < 8)%nat -> k <> a + Z.of_nat j) ->
  uM_store8 M a v !! k = M !! k.
Proof. exact (uM_store_lookup_ne M a 8 v k). Qed.

(* ---- the image / model byte-window bridges -------------------------- *)

Lemma nat_of_N_of_Z (k : Z) : N.to_nat (Z.to_N k) = Z.to_nat k.
Proof. destruct k; reflexivity. Qed.

(* [write_bytes] reads only the [n] low bytes of its value, so two values
   that agree there write the same window.  This is what lets the ghost
   image be stated over the WHOLE register word while the model writes its
   width-[k] truncation. *)
Lemma write_bytes_ext {w1 w2 : N} (v1 : bv w1) (v2 : bv w2)
    (mm : _) (pa : Arch.pa) (n : N) :
  (forall j : nat, (N.of_nat j < n)%N -> nth_byte v1 j = nth_byte v2 j) ->
  write_bytes mm pa n v1 = write_bytes mm pa n v2.
Proof.
  intro H. unfold write_bytes.
  assert (Hl : forall l : list nat,
            (forall j : nat, In j l -> nth_byte v1 j = nth_byte v2 j) ->
            foldr (fun j acc => <[pa_add pa j := nth_byte v1 j]> acc) mm l
            = foldr (fun j acc => <[pa_add pa j := nth_byte v2 j]> acc) mm l).
  { induction l as [ | x xs IH ]; cbn [foldr]; [ reflexivity | ].
    intro Hj. rewrite (Hj x (or_introl eq_refl)).
    rewrite (IH ltac:(intros j Hjj; apply Hj; right; exact Hjj)). reflexivity. }
  apply Hl. intros j Hj. apply in_seq in Hj. apply H. lia.
Qed.

(* the in-page bound at the STORE width (UmodeFetch's [uinpage_nc] is the
   4-byte fetch-window version) *)
Lemma uinpage_nc_k (va : mword 64) (k d : Z) :
  Z.rem (uint va) 4096 <= 4096 - k -> 0 <= d < k ->
  bv_unsigned va mod 4096 + d < 4096.
Proof.
  intros Hpg Hd.
  rewrite uint_unsigned in Hpg.
  rewrite Z.rem_mod_nonneg in Hpg;
    [ | exact (proj1 (bv_unsigned_in_range _ va)) | lia ].
  lia.
Qed.

(* ... and the same premise as [UserMemMis.in_one_page] *)
Lemma uinpage_one (va : mword 64) (k : Z) :
  Z.rem (uint va) 4096 <= 4096 - k -> in_one_page va k.
Proof.
  intro Hpg. unfold in_one_page.
  rewrite uint_unsigned in Hpg.
  rewrite Z.rem_mod_nonneg in Hpg;
    [ | exact (proj1 (bv_unsigned_in_range _ va)) | lia ].
  lia.
Qed.

(* a 1-byte access never crosses a page: its in-page premise is discharged
   from the address alone (WpUmodeLoad's [uinpage_1] is the load twin). *)
Lemma uinpage_byte (va : mword 64) : Z.rem (uint va) 4096 <= 4096 - 1.
Proof.
  rewrite uint_unsigned.
  rewrite Z.rem_mod_nonneg;
    [ | exact (proj1 (bv_unsigned_in_range _ va)) | lia ].
  pose proof (Z.mod_pos_bound (bv_unsigned va) 4096 ltac:(lia)). lia.
Qed.

(* ---- THE RE-KEYING EQUATION ----------------------------------------- *)

(* the domain of an insert run whose keys are already present *)
Lemma uM_fold_dom (a : Z) (v : mword 64) (l : list nat) (M : gmap Z (bv 8)) :
  (forall j : nat, In j l -> is_Some (M !! (a + Z.of_nat j))) ->
  dom (foldr (fun (j : nat) (acc : gmap Z (bv 8)) =>
                <[a + Z.of_nat j := nth_byte v j]> acc) M l) = dom M.
Proof.
  induction l as [ | x xs IH ]; cbn [foldr]; intro HM; [ reflexivity | ].
  rewrite dom_insert_L.
  rewrite (IH ltac:(intros j Hj; apply HM; right; exact Hj)).
  apply subseteq_union_L. apply singleton_subseteq_l. apply elem_of_dom.
  exact (HM x (or_introl eq_refl)).
Qed.

Lemma uM_store_dom (M : gmap Z (bv 8)) (a k : Z) (v : mword 64) :
  (forall j : nat, (j < Z.to_nat k)%nat -> is_Some (M !! (a + Z.of_nat j))) ->
  dom (uM_store M a k v) = dom M.
Proof.
  intro HM. unfold uM_store. apply uM_fold_dom.
  intros j Hj. apply HM. apply in_seq in Hj. lia.
Qed.

(* the injectivity of the re-keying is a fact about the DOMAIN alone *)
Lemma uva_inj_dom (pt : uptd) (M1 M2 : gmap Z (bv 8)) :
  dom M1 = dom M2 -> uva_inj pt M1 -> uva_inj pt M2.
Proof.
  intros Hd Hinj va1 va2 H1 H2 Heq.
  apply Hinj; [ rewrite Hd; exact H1 | rewrite Hd; exact H2 | exact Heq ].
Qed.

(* one insert, re-keyed *)
Lemma upa_map_insert (pt : uptd) (M : gmap Z (bv 8)) (key : Z) (b : bv 8) :
  uva_inj pt M ->
  is_Some (M !! key) ->
  upa_map pt (<[key := b]> M) = <[uva_pa pt key := b]> (upa_map pt M).
Proof.
  intros Hinj Hs.
  assert (Hd : dom (<[key := b]> M) = dom M).
  { rewrite dom_insert_L. apply subseteq_union_L, singleton_subseteq_l,
      elem_of_dom, Hs. }
  pose proof (uva_inj_dom pt M (<[key := b]> M) (eq_sym Hd) Hinj) as Hinj'.
  apply map_eq. intro x.
  destruct (decide (x = uva_pa pt key)) as [-> | Hne].
  - rewrite lookup_insert.
    exact (upa_map_lookup pt (<[key := b]> M) key b Hinj' (lookup_insert _ _ _)).
  - rewrite (lookup_insert_ne _ _ x b (fun H => Hne (eq_sym H))).
    destruct (upa_map pt M !! x) as [c | ] eqn:Hx2.
    + rewrite Hx2.
      destruct (upa_map_lookup_inv pt M x c Hx2) as (va & Hva & Hlk).
      assert (Hvk : va <> key) by (intro; subst va; apply Hne; by rewrite <- Hva).
      assert (Hlk' : <[key := b]> M !! va = Some c)
        by (rewrite (lookup_insert_ne M key va b (fun H => Hvk (eq_sym H)));
            exact Hlk).
      rewrite <- Hva.
      exact (upa_map_lookup pt (<[key := b]> M) va c Hinj' Hlk').
    + rewrite Hx2.
      destruct (upa_map pt (<[key := b]> M) !! x) as [c | ] eqn:Hx;
        [ exfalso | exact Hx ].
      destruct (upa_map_lookup_inv pt _ x c Hx) as (va & Hva & Hlk).
      assert (Hvk : va <> key) by (intro; subst va; apply Hne; by rewrite <- Hva).
      rewrite (lookup_insert_ne M key va b (fun H => Hvk (eq_sym H))) in Hlk.
      rewrite <- Hva in Hx2.
      rewrite (upa_map_lookup pt M va c Hinj Hlk) in Hx2.
      discriminate Hx2.
Qed.

(* the run, re-keyed: the same [foldr], one insert at a time *)
Lemma upa_map_fold (pt : uptd) (M : gmap Z (bv 8)) (a : Z) (v : mword 64)
    (pa : Arch.pa) (l : list nat) :
  uva_inj pt M ->
  (forall j : nat, In j l -> is_Some (M !! (a + Z.of_nat j))) ->
  (forall j : nat, In j l -> uva_pa pt (a + Z.of_nat j) = pa_add pa j) ->
  upa_map pt (foldr (fun (j : nat) (acc : gmap Z (bv 8)) =>
                       <[a + Z.of_nat j := nth_byte v j]> acc) M l)
  = foldr (fun j acc => <[pa_add pa j := nth_byte v j]> acc) (upa_map pt M) l.
Proof.
  intro Hinj.
  induction l as [ | x xs IH ]; cbn [foldr]; intros HM Hw; [ reflexivity | ].
  set (Mx := foldr (fun (j : nat) (acc : gmap Z (bv 8)) =>
                      <[a + Z.of_nat j := nth_byte v j]> acc) M xs).
  assert (Hdx : dom Mx = dom M)
    by (unfold Mx; apply uM_fold_dom;
        intros j Hj; apply HM; right; exact Hj).
  rewrite (upa_map_insert pt Mx (a + Z.of_nat x) (nth_byte v x)
             (uva_inj_dom pt M Mx (eq_sym Hdx) Hinj)
             ltac:(apply elem_of_dom; rewrite Hdx; apply elem_of_dom;
                   exact (HM x (or_introl eq_refl)))).
  rewrite (IH ltac:(intros j Hj; apply HM; right; exact Hj)
             ltac:(intros j Hj; apply Hw; right; exact Hj)).
  rewrite (Hw x (or_introl eq_refl)). reflexivity.
Qed.

Lemma upa_map_store (pt : uptd) (M : gmap Z (bv 8)) (a k : Z) (v : mword 64)
    (pa : Arch.pa) :
  uva_inj pt M ->
  (forall j : nat, (j < Z.to_nat k)%nat -> is_Some (M !! (a + Z.of_nat j))) ->
  (forall j : nat, (j < Z.to_nat k)%nat -> uva_pa pt (a + Z.of_nat j) = pa_add pa j) ->
  upa_map pt (uM_store M a k v)
  = write_bytes (upa_map pt M) pa (Z.to_N k) v.
Proof.
  intros Hinj HM Hw. unfold uM_store, write_bytes. rewrite nat_of_N_of_Z.
  apply upa_map_fold;
    [ exact Hinj
    | intros j Hj; apply HM; apply in_seq in Hj; lia
    | intros j Hj; apply Hw; apply in_seq in Hj; lia ].
Qed.

(* ===================================================================== *)
(* §2 The walk and the store, PURE, at the tier's own byte map.            *)
(* ===================================================================== *)

(* the image half is read through the union's right slot *)
Lemma uv_mm_img_some (t : ptree) (md : PtBytes.pamap) (x : Arch.pa) :
  is_Some (md !! x) -> is_Some (uv_mm t md !! x).
Proof. intro H. rewrite /uv_mm. apply lookup_union_is_Some. by right. Qed.

(* the tier's map at two image halves of the same domain -- the RIGHT-slot
   twin of [UserFetchCert.dom_union_shape], and written the same way for
   the same reason: **[dom_union_L] DOES NOT TERMINATE on a [gset Arch.pa]
   goal**.  It is not a context blow-up (this is a top-level lemma with an
   empty context and it still runs for tens of minutes with no output); it
   is the [gset (mword n)] instance divergence of durable-notes, reached
   through [dom_union_L]'s [LeibnizEquiv] side of the union.  Every domain
   fact in this file therefore goes through [elem_of_dom] and
   [lookup_union_*] by hand. *)
Lemma uv_mm_dom_img (t : ptree) (md1 md2 : PtBytes.pamap) :
  (dom md1 : gset Arch.pa) = dom md2 ->
  (dom (uv_mm t md1) : gset Arch.pa) = dom (uv_mm t md2).
Proof.
  intro Hd.
  assert (Hmem : forall a : Arch.pa,
            a ∈ (dom md1 : gset Arch.pa) <-> a ∈ (dom md2 : gset Arch.pa))
    by (apply set_eq; exact Hd).
  assert (Hab : forall a : Arch.pa, is_Some (md1 !! a) <-> is_Some (md2 !! a)).
  { intros a. split; intros Hx.
    - assert (H1 : a ∈ (dom md1 : gset Arch.pa)) by (apply elem_of_dom; exact Hx).
      assert (H2 : a ∈ (dom md2 : gset Arch.pa)) by (apply (proj1 (Hmem a)); exact H1).
      apply elem_of_dom in H2. exact H2.
    - assert (H1 : a ∈ (dom md2 : gset Arch.pa)) by (apply elem_of_dom; exact Hx).
      assert (H2 : a ∈ (dom md1 : gset Arch.pa)) by (apply (proj2 (Hmem a)); exact H1).
      apply elem_of_dom in H2. exact H2. }
  assert (Hu : forall (X Y : PtBytes.pamap) (a : Arch.pa),
            is_Some ((X ∪ Y) !! a) <-> is_Some (X !! a) \/ is_Some (Y !! a)).
  { intros X Y a. split.
    - intros [c Hc]. destruct (X !! a) as [b|] eqn:Hb.
      + left. exists b. reflexivity.
      + right. exists c. exact (eq_trans (eq_sym (lookup_union_r X Y a Hb)) Hc).
    - intros [[b Hb] | [c Hc]].
      + exists b. exact (lookup_union_Some_l X Y a b Hb).
      + destruct (X !! a) as [b|] eqn:Hb.
        * exists b. exact (lookup_union_Some_l X Y a b Hb).
        * exists c. exact (eq_trans (lookup_union_r X Y a Hb) Hc). }
  rewrite /uv_mm. apply set_eq. intros a. split; intros Ha;
    apply elem_of_dom; apply elem_of_dom in Ha;
    apply Hu; apply Hu in Ha;
    (destruct Ha as [Hx | Hx];
     [ left; exact Hx
     | right; first [ apply (proj1 (Hab a)); exact Hx
                    | apply (proj2 (Hab a)); exact Hx ] ]).
Qed.

Lemma uv_mm_tree_none (t : ptree) (md : PtBytes.pamap) (x : Arch.pa) :
  ptree_bytes 2 t ##ₘ md -> is_Some (md !! x) -> ptree_bytes 2 t !! x = None.
Proof.
  intros Hdj [b Hb].
  destruct (ptree_bytes 2 t !! x) as [c | ] eqn:Hc; [ exfalso | reflexivity ].
  exact (proj1 (map_disjoint_spec _ _) Hdj x c b Hc Hb).
Qed.

(* WpUmodeStep's [uv_walk_fetch] at a DATA access type.  The safety tier's
   [UserMemCert.u_walk_pure] proves the same three arms, but only at
   [u_mem_wf] -- which claims every mapped data byte -- and pins the
   landing map by its DOMAIN alone; this tier owns a NAMED image and a
   strictly weaker map predicate, so the walk is re-derived with the
   landing map spelled [uv_mm t' md] at the same [md]. *)
Lemma uv_walk_data (acc : MemoryAccessType mem_payload) (pt : uptd) (t : ptree)
    (md : PtBytes.pamap) (rs : regstate) (w va : mword 64) :
  u_acc acc ->
  ud_um pt !! svpn_of va = Some w ->
  uleaf_ok acc w ->
  uva_canon va ->
  u_data_cfg rs ->
  u_exec_pins pt t rs ->
  uv_tree_ok pt md t ->
  exists (rs' : regstate) (t' : ptree),
    exec (translateAddr (Virtaddr va) acc) (u_state rs (uv_mm t md))
      = Some (Values.Ok (Physaddr (u_walk_pa w va), PBMT_PMA, init_ext_ptw),
              u_state rs' (uv_mm t' md)) /\
    goodmb Du_r Du_w (translateAddr (Virtaddr va) acc)
      (u_state rs (uv_mm t md)) (uv_mm t md) = true /\
    u_tlb_only rs rs' /\
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
    uv_tree_ok pt md t' /\
    pt_same_shape 2 t t'.
Proof.
  intros Hacc Hl Hleaf Hcanon Hcfg Hpins Htok.
  pose proof (uv_tree_mem_ok pt md t Htok) as Hokm.
  pose proof Htok as (Hdisj & Hdj & Hram & Hwfm & Hspec).
  pose proof Hcfg as (Lcp & Lms & Lmenv).
  destruct Lms as (Lsxl & Lmprv & _).
  pose proof Hpins as (Hhw & Hcfgp & Hpt & Htlbok).
  pose proof Hhw as (Hmisa & Hmseccfg & Hsenv & Hhtif & Hall & Help).
  pose proof Hpt as ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp).
  pose proof Hsatpok as (Hmode & Hasid & Hppn & Hpmaw_of).
  pose proof Hspec as (Hbase & _).
  destruct (upt_spec_maps (ud_root pt) (ud_tfp pt) (ud_um pt) t (svpn_of va) w
              Hspec (or_intror (or_intror Hl)))
    as (p2 & p1 & a0 & d0 & Hmaps).
  pose proof Hmaps as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                       Hv2 & Hn2 & Hv1 & Hn1 & Hv0 & Hl0 & Hnap & Hpb0).
  assert (Hvar : forall a d : mword 1,
            pte_valid (pte_set_ad w a d) /\ pte_leaf (pte_set_ad w a d) /\
            pte_no_napot (pte_set_ad w a d) /\ pte_pbmt0 (pte_set_ad w a d))
    by exact (upt_variant (ud_tfp pt) (ud_um pt) (svpn_of va) w Hwfm
                (or_intror (or_intror Hl))).
  assert (Hsm2 : pt_slot_mem (u_state rs (uv_mm t md)) (pt_addr2 t (svpn_of va)) p2)
    by exact (u_slot_mem_at pt t (uv_mm t md) rs (pt_base t)
                (vpn_idx 2 (svpn_of va)) p2 Hokm
                (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm1 : pt_slot_mem (u_state rs (uv_mm t md)) (pt_addr1 p2 (svpn_of va)) p1)
    by exact (u_slot_mem_at pt t (uv_mm t md) rs (u_next_base p2)
                (vpn_idx 1 (svpn_of va)) p1 Hokm
                (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hsm0 : pt_slot_mem (u_state rs (uv_mm t md)) (pt_addr0 p1 (svpn_of va))
                   (pte_set_ad w a0 d0))
    by exact (u_slot_mem_at pt t (uv_mm t md) rs (u_next_base p1)
                (vpn_idx 0 (svpn_of va)) _ Hokm
                (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown2 : bytes_owned (uv_mm t md) (pt_addr2 t (svpn_of va)) 8 = true)
    by exact (u_slot_owned pt t (uv_mm t md) _ p2 Hokm
                (ptree_maps_slot2 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown1 : bytes_owned (uv_mm t md) (pt_addr1 p2 (svpn_of va)) 8 = true)
    by exact (u_slot_owned pt t (uv_mm t md) _ p1 Hokm
                (ptree_maps_slot1 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Hown0 : bytes_owned (uv_mm t md) (pt_addr0 p1 (svpn_of va)) 8 = true)
    by exact (u_slot_owned pt t (uv_mm t md) _ _ Hokm
                (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps)).
  assert (Htm : exec (translationMode User) (u_state rs (uv_mm t md))
                = Some (Sv39, u_state rs (uv_mm t md)))
    by exact (exec_translationMode_U_sv39 usatp (u_state rs (uv_mm t md))
                Lsxl Hsatp Hmode).
  assert (Htmg : goodb Du_r (translationMode User) (u_state rs (uv_mm t md)) = true)
    by exact (goodb_translationMode_U Du_r usatp (u_state rs (uv_mm t md))
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                Lsxl Hsatp Hmode).
  assert (Heff : exec (effectivePrivilege acc
                        (register_lookup mstatus (u_state rs (uv_mm t md)).(sregs))
                        User) (u_state rs (uv_mm t md))
                 = Some (User, u_state rs (uv_mm t md)))
    by exact (exec_effectivePrivilege_mprv0 acc _ User (u_state rs (uv_mm t md)) Lmprv).
  assert (Heffg : goodb Du_r (effectivePrivilege acc
                        (register_lookup mstatus (u_state rs (uv_mm t md)).(sregs))
                        User) (u_state rs (uv_mm t md)) = true)
    by exact (goodb_effectivePrivilege_mprv0 Du_r acc _ User
                (u_state rs (uv_mm t md)) Lmprv).
  assert (Hssx : exec (is_shadow_stack_access acc) (u_state rs (uv_mm t md))
                 = Some (false, u_state rs (uv_mm t md)))
    by exact (exec_is_shadow_stack_u_acc acc (u_state rs (uv_mm t md)) Hacc).
  assert (Hssg : goodb Du_r (is_shadow_stack_access acc)
                   (u_state rs (uv_mm t md)) = true)
    by exact (goodb_is_shadow_stack_u_acc Du_r acc (u_state rs (uv_mm t md)) Hacc).
  assert (Hpmar : pma_allows_pte_read
                    (register_lookup pma_regions (u_state rs (uv_mm t md)).(sregs)))
    by exact (pma_allows_all_pte_read _ Hall).
  assert (Hpmaw : pma_allows_pte_write
                    (register_lookup pma_regions (u_state rs (uv_mm t md)).(sregs)))
    by exact (Hpmaw_of _ Hall).
  assert (Hgchk : forall (a d : mword 1) (mxr do_sum : bool)
                    (Db : register -> bool) (s0 : mstate),
            goodb Db (check_PTE_permission acc User mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d)) tt) s0 = true).
  { intros a d mxr do_sum Db s0.
    exact (goodb_check_PTE_permission_u acc (pte_set_ad w a d) mxr do_sum Db s0
             Hacc (Hleaf a d mxr do_sum)). }
  assert (Hg2 : forall (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p2 7 0))
                        (ext_bits_of_PTE p2)) s0 = true)
    by (intros Db s0; exact (goodb_pte_is_invalid_valid p2 Db s0 Hv2)).
  assert (Hg1 : forall (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec p1 7 0))
                        (ext_bits_of_PTE p1)) s0 = true)
    by (intros Db s0; exact (goodb_pte_is_invalid_valid p1 Db s0 Hv1)).
  assert (Hg0 : forall (a d : mword 1) (Db : register -> bool) (s0 : mstate),
            goodb Db (pte_is_invalid
                        (Mk_PTE_Flags (subrange_vec_dec (pte_set_ad w a d) 7 0))
                        (ext_bits_of_PTE (pte_set_ad w a d))) s0 = true)
    by (intros a d Db s0;
        exact (goodb_pte_is_invalid_valid _ Db s0 (proj1 (Hvar a d)))).
  destruct (KptTree.ptree_translateAddr_cases acc User
              (ud_root pt) va w (u_walk_pa w va) usatp t (register_lookup tlb rs)
              p2 p1 a0 d0 (u_state rs (uv_mm t md))
              Hleaf Hcanon eq_refl (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
              Hbase Hmaps Htlbok Hsm2 Hsm1 Hsm0
              Hmisa Lmenv Hhtif Lcp Htm Heff Hssx Hsatp Hppn Hasid eq_refl
              HA Hord HRp HWp Hcovp Hpmar Hpmaw)
    as (sf & Htr & Harms).
  assert (Htrg : goodmb Du_r Du_w (translateAddr (Virtaddr va) acc)
                   (u_state rs (uv_mm t md)) (uv_mm t md) = true).
  { apply (goodmb_ptree_translateAddr Du_r Du_w acc User
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
             ltac:(vm_compute; reflexivity)
             (ud_root pt) t va w (u_walk_pa w va) usatp (register_lookup tlb rs)
             p2 p1 a0 d0 (u_state rs (uv_mm t md)) (uv_mm t md)
             Hleaf Hgchk Hcanon eq_refl
             (fun a d => proj2 (proj2 (proj2 (Hvar a d))))
             Hbase Hmaps Htlbok Hg2 Hg1 Hg0 Hsm2 Hsm1 Hsm0 Hown2 Hown1 Hown0
             Hmisa Lmenv Hhtif Lcp Htm Htmg Heff Heffg Hssx Hssg
             Hsatp Hppn Hasid eq_refl HA Hord HRp HWp Hcovp Hpmar Hpmaw). }
  (* WHERE THE WALK LANDED, with the image half NAMED *)
  assert (Hland : exists (rs' : regstate) (t' : ptree),
            sf = u_state rs' (uv_mm t' md) /\
            (rs' = rs \/ exists tv, rs' = register_set tlb tv rs) /\
            tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
            pt_same_shape 2 t t' /\
            upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt) t' /\
            ptree_bytes 2 t' ##ₘ md).
  { destruct Harms as [-> | [-> | (a1 & d1 & ->)]].
    - exists rs, t. split_and!;
        [ reflexivity | left; reflexivity | exact Htlbok
        | apply pt_same_shape_refl | exact Hspec | exact Hdj ].
    - eexists _, t. split_and!.
      + reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0) t (register_lookup tlb rs)
                 (svpn_of va) p2 p1 _ Hmaps Htlbok).
      + apply pt_same_shape_refl.
      + exact Hspec.
      + exact Hdj.
    - assert (Habs : pte_set_ad (pte_set_ad w a0 d0) a1 d1 = pte_set_ad w a1 d1)
        by exact (pte_set_ad_absorb w a0 d0 a1 d1).
      assert (Hv' : pte_valid (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (Hvar a1 d1))).
      assert (Hlf' : pte_leaf (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (proj2 (Hvar a1 d1)))).
      assert (Hn' : pte_no_napot (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj1 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hp' : pte_pbmt0 (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by (rewrite Habs; exact (proj2 (proj2 (proj2 (Hvar a1 d1))))).
      assert (Hspec' : upt_tree_spec (ud_root pt) (ud_tfp pt) (ud_um pt)
                (ptree_set_leaf t (svpn_of va)
                   (pte_set_ad (pte_set_ad w a0 d0) a1 d1))).
      { rewrite Habs.
        exact (upt_tree_spec_set_leaf (ud_root pt) (ud_tfp pt) (ud_um pt) t
                 (svpn_of va) w p2 p1 a0 d0 a1 d1 Hwfm Hspec
                 (or_intror (or_intror Hl)) Hmaps). }
      assert (Heqt : ptree_bytes 2 (ptree_set_leaf t (svpn_of va)
                       (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
                     = write_bytes (ptree_bytes 2 t) (pt_addr0 p1 (svpn_of va)) 8
                         (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
        by exact (ptree_bytes_set_leaf t (svpn_of va) p2 p1 _ _ Hdisj Hmaps).
      assert (Hwdj : word_bytes (pt_addr0 p1 (svpn_of va))
                       (pte_set_ad (pte_set_ad w a0 d0) a1 d1) ##ₘ md).
      { apply map_disjoint_spec. intros x b1 b2 H1 H2.
        destruct (word_bytes_is_Some (pt_addr0 p1 (svpn_of va))
                    (pte_set_ad (pte_set_ad w a0 d0) a1 d1) (pte_set_ad w a0 d0)
                    x (mk_is_Some _ _ H1)) as [b0 Hb0].
        pose proof (maps_disj_subseteq (pt_maps 2 t)
                      (word_bytes (pt_addr0 p1 (svpn_of va)) (pte_set_ad w a0 d0))
                      Hdisj (ptree_maps_slot0 t (svpn_of va) p2 p1 _ Hmaps))
          as Hsubt.
        pose proof (lookup_weaken _ _ x b0 Hb0 Hsubt) as Hbt.
        exact (proj1 (map_disjoint_spec (ptree_bytes 2 t) md) Hdj x b0 b2 Hbt H2). }
      assert (Hdj' : ptree_bytes 2 (ptree_set_leaf t (svpn_of va)
                       (pte_set_ad (pte_set_ad w a0 d0) a1 d1)) ##ₘ md).
      { rewrite Heqt write_bytes_word. apply map_disjoint_union_l.
        split; [ exact Hwdj | exact Hdj ]. }
      eexists _,
        (ptree_set_leaf t (svpn_of va) (pte_set_ad (pte_set_ad w a0 d0) a1 d1)).
      split_and!.
      + rewrite /set_reg. cbn [sregs mem mdev]. rewrite /uv_mm.
        rewrite Heqt. rewrite <- write_bytes_union_l. reflexivity.
      + right. eexists. reflexivity.
      + rewrite register_lookup_set.
        exact (tlb_ok_pt_fill_self (mword_of_int 0)
                 (ptree_set_leaf t (svpn_of va)
                    (pte_set_ad (pte_set_ad w a0 d0) a1 d1))
                 (register_lookup tlb rs) (svpn_of va) p2 p1 _
                 (ptree_set_leaf_maps_self t (svpn_of va) p2 p1
                    (pte_set_ad w a0 d0) _ Hmaps Hv' Hlf' Hn' Hp')
                 (tlb_ok_pt_set_leaf (mword_of_int 0) t (register_lookup tlb rs)
                    (svpn_of va) p2 p1 (pte_set_ad w a0 d0) a1 d1
                    Hmaps Hv' Hlf' Hn' Hp' Htlbok)).
      + exact (pt_same_shape_set_leaf t (svpn_of va) p2 p1 _ _ Hmaps).
      + exact Hspec'.
      + exact Hdj'. }
  destruct Hland as (rs' & t' & Hsf & Hfile & Htlbok' & Hshape & Hspec' & Hdj').
  rewrite Hsf in Htr.
  exists rs', t'. split_and!.
  - exact Htr.
  - exact Htrg.
  - exact (u_tlb_only_land rs rs' Hfile).
  - exact Htlbok'.
  - exact (uv_tree_ok_shape pt md t t' Htok Hshape Hspec' Hdj').
  - exact Hshape.
Qed.

(* ---- the store on top of the walk, at the named map ------------------ *)

Section UvStorePure.
  Context (k : Z).
  Context (Hk : 0 < k) (Hk8 : k <= 8) (Hkdvd : (k | 4096)).
  Context (Huintk : uint (to_bits 64 k) = k).
  Context (Hwrite_plain : forall (addr : mword 64) (data : mword (8 * k)) (s : mstate),
      dev_addr addr = false ->
      exec (write_ram rv64d_types.Write_plain (Physaddr addr) k data tt) s
      = Some (true, MState s.(sregs) (write_bytes s.(mem) addr (Z.to_N k) data) s.(mdev))).

  (* [UserMemCert.u_store_pure]'s content at [u_mem_ok] and at the NAMED
     landing map: three model calls (the walk, the effective-address
     announcement, the value write), each with its certificate.  The
     window's ownership comes from the tier's OWN image ([Hwin]) rather
     than from the safety tier's whole-page coverage. *)
  Lemma uv_store_mm (pt : uptd) (t : ptree) (md : PtBytes.pamap) (rs : regstate)
      (w va : mword 64) (v : mword (8 * k)) :
    ud_um pt !! svpn_of va = Some w ->
    uleaf_ok (Store Data) w ->
    uva_canon va ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    in_one_page va k ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       is_Some (md !! pa_add (u_walk_pa w va) j)) ->
    u_data_cfg rs ->
    u_exec_pins pt t rs ->
    uv_tree_ok pt md t ->
    exists (rs' : regstate) (t' : ptree),
      exec (vmem_write_addr (Virtaddr va) k v (Store Data) false false false)
        (u_state rs (uv_mm t md))
        = Some (Ok true,
                u_state rs' (write_bytes (uv_mm t' md) (u_walk_pa w va) (Z.to_N k) v)) /\
      goodmb Du_r Du_w
        (vmem_write_addr (Virtaddr va) k v (Store Data) false false false)
        (u_state rs (uv_mm t md)) (uv_mm t md) = true /\
      u_tlb_only rs rs' /\
      tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rs') /\
      uv_tree_ok pt md t' /\
      pt_same_shape 2 t t'.
  Proof.
    intros Hl Hleaf Hcanon Hal Hin Hwin Hcfg Hpins Htok.
    destruct (uv_walk_data (Store Data) pt t md rs w va
                (or_intror (or_intror (or_introl eq_refl)))
                Hl Hleaf Hcanon Hcfg Hpins Htok)
      as (rs' & t' & Htr & Htrg & Tonly & Htlbok' & Htok' & Hshape).
    set (pa := u_walk_pa w va) in *.
    set (mm := uv_mm t md) in *.
    set (mm' := uv_mm t' md) in *.
    set (s' := u_state rs' mm').
    pose proof Htok' as (Hdisj' & Hdj' & Hram' & Hwfm' & Hspec').
    (* the store window, in the landing map *)
    assert (Hws : forall j : nat, (j < Z.to_nat k)%nat -> is_Some (mm' !! pa_add pa j))
      by (intros j Hj; apply uv_mm_img_some; exact (Hwin j Hj)).
    assert (Hown : bytes_owned mm' pa (Z.to_N k) = true).
    { apply bytes_owned_of_dom. intros j Hj. apply elem_of_dom.
      apply Hws. lia. }
    assert (Hramj : forall j : nat, (j < Z.to_nat k)%nat -> addr_is_ram (pa_add pa j))
      by (intros j Hj; apply Hram', elem_of_dom, (Hws j Hj)).
    assert (Hram0 : addr_is_ram pa)
      by (rewrite <- (pa_add_0 pa); apply Hramj; lia).
    assert (Hramk : addr_is_ram (pa_add pa (Z.to_nat k - 1)))
      by (apply Hramj; lia).
    assert (Hdev : dev_addr pa = false) by exact (addr_is_ram_not_dev _ Hram0).
    (* the cfg and the pins, at the landing file *)
    assert (Hcfg' : u_data_cfg rs').
    { destruct Hcfg as (Lcp & Lms & Lmenv). split_and!;
        [ rewrite (Tonly cur_privilege ltac:(vm_compute; reflexivity)); exact Lcp
        | rewrite (Tonly mstatus ltac:(vm_compute; reflexivity)); exact Lms
        | rewrite (Tonly menvcfg ltac:(vm_compute; reflexivity)); exact Lmenv ]. }
    assert (Hpins' : u_exec_pins pt t' rs').
    { unfold u_exec_pins, u_hw_pins, u_cfg_pins, u_pt_pins in Hpins |- *.
      destruct Hpins as ((Hmisa & Hsec & Hsenv & Hhtif & Hall & Help) &
                         (Hmste & Hsste) &
                         ((usatp & Hsatpok & Hsatp) & HA & Hord & HXp & HWp & HRp & Hcovp) &
                         _).
      split_and!;
        [ rewrite (Tonly misa ltac:(vm_compute; reflexivity)); exact Hmisa
        | rewrite (Tonly mseccfg ltac:(vm_compute; reflexivity)); exact Hsec
        | rewrite (Tonly senvcfg ltac:(vm_compute; reflexivity)); exact Hsenv
        | rewrite (Tonly htif_tohost_base ltac:(vm_compute; reflexivity)); exact Hhtif
        | rewrite (Tonly pma_regions ltac:(vm_compute; reflexivity)); exact Hall
        | rewrite (Tonly elp ltac:(vm_compute; reflexivity)); exact Help
        | rewrite (Tonly mstateen0 ltac:(vm_compute; reflexivity)); exact Hmste
        | rewrite (Tonly sstateen0 ltac:(vm_compute; reflexivity)); exact Hsste
        | exists usatp; split;
            [ exact Hsatpok
            | rewrite (Tonly satp ltac:(vm_compute; reflexivity)); exact Hsatp ]
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HA
        | rewrite (Tonly pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hord
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HXp
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HWp
        | rewrite (Tonly pmpcfg_n ltac:(vm_compute; reflexivity)); exact HRp
        | rewrite (Tonly pmpaddr_n ltac:(vm_compute; reflexivity)); exact Hcovp
        | exact Htlbok' ]. }
    pose proof Hcfg' as (Lcp & Lms & Lmenv).
    pose proof Lms as (Lsxl & Lmprv & Lmxr).
    pose proof Hpins' as ((Hmisa & Hsec & Hsenv & Hhtif & Hall & Help) & _ &
                          ((usatp & _ & Hsatp) & HA & Hord & _ & HW & _ & Hcovp) & _).
    destruct (pma_all_ram Hall pa k
                (pma_access_ram_at pa k (Z.to_nat k - 1) ltac:(clear -Hk; lia)
                   Hram0 Hramk (pma_width_le k 8 Hk Hk8 eq_refl)))
      as (region & Hpmam & _ & _ & Hwrb).
    assert (Hrange : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n rs') 0)) 4)
              (uint pa) (uint (to_bits 64 k)) = PMP_Match)
      by exact (ram_fetch_pmp pa _ k (Z.to_nat k - 1) Hk ltac:(lia) Huintk
                  ltac:(clear -Hk; lia) Hram0 Hramk Hcovp).
    assert (Halign : is_aligned_paddr (Physaddr pa) k = true)
      by exact (pa_aligned_div _ va k Hk Hkdvd Hal).
    assert (Hclint : exec (within_clint (Physaddr pa) k) s' = Some (false, s'))
      by exact (within_clint_false pa k s' (addr_is_ram_not_in_clint _ Hram0) Hk).
    assert (Hsig : exec (within_sig (Physaddr pa) k) s' = Some (false, s'))
      by exact (within_sig_false pa k s' (addr_is_ram_not_in_sig _ Hram0) Hk).
    assert (Hwp : forall d : mword (8 * k),
              exec (write_ram rv64d_types.Write_plain (Physaddr pa) k d tt) s'
              = Some (true, MState s'.(sregs) (write_bytes s'.(mem) pa (Z.to_N k) d)
                              s'.(mdev)))
      by (intro d; exact (Hwrite_plain pa d s' Hdev)).
    (* the effective-address announcement *)
    assert (Hcpe : exec (check_pma_with_pmp_priority (Store Data) PBMT_PMA User
                           (Physaddr pa) k false) s' = Some (Ok pma_ok_aligned, s')).
    { unfold check_pma_with_pmp_priority.
      rewrite (exec_bind_Some _ _ _ _ _
                 (exec_pmaCheck_ram_store_g k pa PBMT_PMA region s'
                    Hpmam Halign (proj1 Hwrb))).
      cbn match. apply exec_returnM. }
    assert (Hcpg : goodmb Du_r Du_w (check_pma_with_pmp_priority (Store Data) PBMT_PMA
                            User (Physaddr pa) k false) s' mm' = true)
      by exact (goodmb_check_pma_with_pmp_priority Du_r Du_w _ _ User _ _ false _ s' mm'
                  (goodmb_pmaCheck_ram_store_g Du_r Du_w k pa PBMT_PMA region s' mm'
                     ltac:(vm_compute; reflexivity) Hpmam Halign (proj1 Hwrb))
                  (exec_pmaCheck_ram_store_g k pa PBMT_PMA region s'
                     Hpmam Halign (proj1 Hwrb))).
    assert (Heffe : exec (effectivePrivilege (Store Data)
                            (register_lookup mstatus rs')
                            (register_lookup cur_privilege rs')) s'
                    = Some (User, s')).
    { rewrite Lcp.
      exact (exec_effectivePrivilege_mprv0 (Store Data)
               (register_lookup mstatus rs') User s' Lmprv). }
    assert (Hea : exec (mem_write_ea (Physaddr pa) k (Store Data) PBMT_PMA
                          false false false) s' = Some (Ok tt, s'))
      by exact (exec_mem_write_ea_g k pa (Store Data) PBMT_PMA User s'
                  Heffe Hcpe
                  (exec_pmpCheck_user_grant_store pa k s' HA Hord Hrange HW)).
    assert (Heag : goodmb Du_r Du_w (mem_write_ea (Physaddr pa) k (Store Data)
                            PBMT_PMA false false false) s' mm' = true)
      by exact (goodmb_mem_write_ea_g Du_r Du_w k pa (Store Data) PBMT_PMA User s' mm'
                  Hk ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data)
                     (register_lookup mstatus rs') (register_lookup cur_privilege rs')
                     s' mm' Lmprv)
                  Heffe Hcpg Hcpe
                  (goodmb_pmpCheck_user_grant_store Du_r Du_w pa k s' mm'
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                     HA Hord Hrange HW)
                  (exec_pmpCheck_user_grant_store pa k s' HA Hord Hrange HW)).
    (* the value write *)
    assert (Hwr : exec (mem_write_value (Physaddr pa) k v (Store Data) PBMT_PMA
                          false false false) s'
                  = Some (Ok true, u_state rs' (write_bytes mm' pa (Z.to_N k) v)))
      by exact (exec_mem_write_value_U k Hk Hwrite_plain PBMT_PMA pa region v s'
                  HA Hord Hrange HW Hpmam Halign (proj1 Hwrb) Hclint Hsig
                  (within_htif_writable_false pa k s' Hhtif) Hdev Lmprv Lcp).
    assert (Hchke : exec (checked_mem_write (Physaddr pa) k v (Store Data) PBMT_PMA
                            User tt false false false) s'
                    = Some (Ok true, MState s'.(sregs)
                              (write_bytes s'.(mem) pa (Z.to_N k) v) s'.(mdev)))
      by exact (exec_checked_mem_write_ram_U k Hk Hwrite_plain PBMT_PMA pa region v s'
                  HA Hord Hrange HW Hpmam Halign (proj1 Hwrb) Hclint Hsig
                  (within_htif_writable_false pa k s' Hhtif) Hdev).
    assert (Hchkg : goodmb Du_r Du_w (checked_mem_write (Physaddr pa) k v (Store Data)
                             PBMT_PMA User tt false false false) s' mm' = true)
      by exact (goodmb_checked_mem_write_ram_U Du_r Du_w k Hk PBMT_PMA pa region v s' mm'
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  HA Hord Hrange HW Hpmam Halign (proj1 Hwrb) Hclint Hsig Hhtif
                  Hdev Hown Hwp).
    assert (Hwrg : goodmb Du_r Du_w (mem_write_value (Physaddr pa) k v (Store Data)
                            PBMT_PMA false false false) s' mm' = true)
      by exact (goodmb_mem_write_value_U Du_r Du_w k PBMT_PMA pa v s' mm'
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  Lmprv Lcp Hchkg Hchke).
    (* ...and the certificates, read back at the ENTRY map *)
    assert (Hdomm : dom mm' = dom mm)
      by (unfold mm, mm'; symmetry; exact (uv_mm_dom t t' md Hshape)).
    assert (Heag' : goodmb Du_r Du_w (mem_write_ea (Physaddr pa) k (Store Data)
                             PBMT_PMA false false false) s' mm = true)
      by (rewrite (goodmb_dom Du_r Du_w _ s' mm mm' (eq_sym Hdomm)); exact Heag).
    assert (Hwrg' : goodmb Du_r Du_w (mem_write_value (Physaddr pa) k v (Store Data)
                             PBMT_PMA false false false) s' mm = true)
      by (rewrite (goodmb_dom Du_r Du_w _ s' mm mm' (eq_sym Hdomm)); exact Hwrg).
    (* the top: the aligned, in-one-page vmem write *)
    pose proof (exec_split_on_page_boundary_intra va k (u_state rs mm) Hk Hin) as Hsp.
    pose proof (goodmb_split_on_page_boundary_intra Du_r Du_w va k
                  (u_state rs mm) mm Hk Hin) as Hspg.
    pose proof (u_effectivePrivilege_pure (Store Data) rs mm Hcfg) as Heff0.
    pose proof (u_goodmb_effectivePrivilege_pure (Store Data) rs mm mm Hcfg) as Heff0g.
    pose proof (u_translationMode_pure pt t rs mm Hcfg Hpins) as Htm0.
    pose proof (u_goodmb_translationMode_pure pt t rs mm mm Hcfg Hpins) as Htm0g.
    exists rs', t'. split_and!;
      [ | | exact Tonly | exact Htlbok' | exact Htok' | exact Hshape ].
    - pose proof (exec_vmem_write_addr_intra k va pa v User Sv39
                    (u_state rs mm) s' (u_state rs' (write_bytes mm' pa (Z.to_N k) v))
                    Hk Hsp (or_introl Hal) Heff0 Htm0 Htr Hea) as H.
      change (@autocast mword (Z.sub (Z.mul 8 k) 1 - 0 + 1) (8 * k) _
                (@subrange_vec_dec (8 * k) v (Z.sub (Z.mul 8 k) 1) 0)
              : mword (8 * k))
        with (@autocast mword (8 * k - 1 - 0 + 1) (8 * k) _
                (@subrange_vec_dec (8 * k) v (8 * k - 1) 0) : mword (8 * k)) in H.
      rewrite (subrange_full_gen_cast (8 * k) v ltac:(lia)) in H.
      exact (H Hwr).
    - pose proof (goodmb_vmem_write_addr_intra Du_r Du_w k va pa v User Sv39
                    (u_state rs mm) s' (u_state rs' (write_bytes mm' pa (Z.to_N k) v)) mm
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    Hk Hsp Hspg (or_introl Hal) Heff0 Heff0g Htm0 Htm0g
                    Htr Htrg Hea Heag') as H.
      change (@autocast mword (Z.sub (Z.mul 8 k) 1 - 0 + 1) (8 * k) _
                (@subrange_vec_dec (8 * k) v (Z.sub (Z.mul 8 k) 1) 0)
              : mword (8 * k))
        with (@autocast mword (8 * k - 1 - 0 + 1) (8 * k) _
                (@subrange_vec_dec (8 * k) v (8 * k - 1) 0) : mword (8 * k)) in H.
      rewrite (subrange_full_gen_cast (8 * k) v ltac:(lia)) in H.
      exact (H Hwr Hwrg').
  Qed.

End UvStorePure.

(* ===================================================================== *)
(* §3 The value-precise k-byte STORE execute at User.                      *)
(* ===================================================================== *)

(* THE store data the model actually hands to [vmem_write]: the low [8*k]
   bits of the rs2 register word, under the [autocast] that transports the
   [subrange]'s [k*8-1-0+1] index to the [8*k] one [vmem_write] wants. *)
Definition ustore_data (k : Z) (v : mword 64) : mword (8 * k) :=
  autocast (T := mword) (subrange_vec_dec v (Z.sub (Z.mul k 8) 1) 0).

(* a low-window truncation does not move a byte inside the window *)
Local Lemma byte_of_mod (x n s : Z) :
  0 <= s -> s + 8 <= n ->
  ((x mod 2 ^ n) ≫ s) mod 2 ^ 8 = (x ≫ s) mod 2 ^ 8.
Proof.
  intros Hs Hn.
  apply Z.bits_inj_iff'. intros i Hi.
  destruct (Z_lt_le_dec i 8) as [Hlt | Hge].
  - rewrite (Z.mod_pow2_bits_low (Z.shiftr (x mod 2 ^ n) s) 8 i ltac:(lia)).
    rewrite (Z.mod_pow2_bits_low (Z.shiftr x s) 8 i ltac:(lia)).
    rewrite (Z.shiftr_spec (x mod 2 ^ n) s i ltac:(lia)).
    rewrite (Z.shiftr_spec x s i ltac:(lia)).
    rewrite (Z.mod_pow2_bits_low x n (i + s) ltac:(lia)). reflexivity.
  - rewrite (Z.mod_pow2_bits_high (Z.shiftr (x mod 2 ^ n) s) 8 i ltac:(lia)).
    rewrite (Z.mod_pow2_bits_high (Z.shiftr x s) 8 i ltac:(lia)). reflexivity.
Qed.

Lemma nth_byte_ustore_data (k : Z) (v : mword 64) (j : nat) :
  0 < k -> k <= 8 -> (j < Z.to_nat k)%nat ->
  nth_byte (ustore_data k v) j = nth_byte v j.
Proof.
  intros Hk Hk8 Hj.
  assert (Hjk : Z.of_nat j < k) by lia.
  apply bv_eq. rewrite !nth_byte_unsigned. unfold ustore_data.
  rewrite (autocast_unsigned (Z.sub (Z.mul k 8) 1 - 0 + 1) (8 * k) _ ltac:(lia)).
  rewrite (subrange_dec_unsigned_lo0 v (Z.sub (Z.mul k 8) 1) (2 ^ (8 * k))
             ltac:(lia) ltac:(f_equal; lia)).
  apply byte_of_mod; lia.
Qed.

Section UmodeStoreExec.
  Context (k : Z).
  Context (Hkw : vmem_width k).

  (* THE execute fact: [s{b,h,w,d} rs2, imm(rs1)] at User with MPRV = 0. *)
  Lemma exec_execute_STORE_k_u_walk (rs2 rs1 : mword 5) (imm : mword 12)
      (base v : mword 64) (md : SATPMode) (s sfin : mstate) :
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    exec (get_pmlen (Store Data) User) s = Some (0, s) ->
    exec (translationMode User) s = Some (md, s) ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)) = v ->
    exec (vmem_write_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (ustore_data k v) (Store Data) false false false) s
      = Some (Ok true, sfin) ->
    exec (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s
      = Some (RETIRE_SUCCESS, sfin).
  Proof.
    intros Hcp Heff Hpml Htm Hbase Hv Hvwa.
    apply (exec_execute_STORE_u_ok imm rs2 rs1 k true s sfin
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (uvw_le8 k Hkw))).
    rewrite Hv.
    apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) k (ustore_data k v) (Store Data)
             false false false md (Ok true) s sfin Hcp Heff Hpml Htm).
    rewrite Hbase. exact Hvwa.
  Qed.

  Lemma goodmb_execute_STORE_k_u_walk (rs2 rs1 : mword 5) (imm : mword 12)
      (base v : mword 64) (md : SATPMode) (s sfin : mstate) (mm : PtBytes.pamap) :
    register_lookup cur_privilege s.(sregs) = User ->
    exec (effectivePrivilege (Store Data) (register_lookup mstatus s.(sregs)) User) s
      = Some (User, s) ->
    goodmb Du_r Du_w (effectivePrivilege (Store Data)
             (register_lookup mstatus s.(sregs)) User) s mm = true ->
    exec (get_pmlen (Store Data) User) s = Some (0, s) ->
    goodmb Du_r Du_w (get_pmlen (Store Data) User) s mm = true ->
    exec (translationMode User) s = Some (md, s) ->
    goodmb Du_r Du_w (translationMode User) s mm = true ->
    (if Z.eqb (uint rs1) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s.(sregs)) = base ->
    (if Z.eqb (uint rs2) 0 then zero_reg
     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s.(sregs)) = v ->
    exec (vmem_write_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (ustore_data k v) (Store Data) false false false) s
      = Some (Ok true, sfin) ->
    goodmb Du_r Du_w (vmem_write_addr (Virtaddr (add_vec base (sign_extend' 64 imm))) k
            (ustore_data k v) (Store Data) false false false) s mm = true ->
    goodmb Du_r Du_w (execute (STORE (imm, Regidx rs2, Regidx rs1, k))) s mm = true.
  Proof.
    intros Hcp Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hv Hvwa Hvwag.
    apply (goodmb_execute_STORE_u_ok Du_r Du_w imm rs2 rs1 k true s sfin mm
             (fun H => Du_gpr_of_Z_r rs2 H)
             ltac:(change xlen_bytes with 8; apply Z.leb_le;
                   exact (uvw_le8 k Hkw))).
    - rewrite Hv.
      apply (exec_vmem_write_u rs1 (sign_extend' 64 imm) k (ustore_data k v) (Store Data)
               false false false md (Ok true) s sfin Hcp Heff Hpml Htm).
      rewrite Hbase. exact Hvwa.
    - rewrite Hv.
      apply (goodmb_vmem_write_u Du_r Du_w rs1 (sign_extend' 64 imm) k
               (ustore_data k v) (Store Data) false false false md (Ok true) s sfin mm
               (fun H => Du_gpr_of_Z_r rs1 H)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               Hcp Heff Heffg Hpml Hpmlg Htm Htmg);
        rewrite Hbase; [ exact Hvwa | exact Hvwag ].
  Qed.

End UmodeStoreExec.

(* ===================================================================== *)
(* §4 The two things the funnel's tail cannot do.                          *)
(* ===================================================================== *)

Section UvStoreRes.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* THE RESIDUE AT ANOTHER IMAGE.  [uv_res pt M t] closes back to
     [umem pt M] at the image it was OPENED at; a store's image is a
     different one.  But the residue's only RESOURCE is the persistent
     [pt_claims] -- everything else its closer captures is PURE -- so the
     residue at ANY image is rebuilt from the claims plus the two pins
     [u_exec_pins] already carries. *)
  Lemma uv_res_reimg (pt : uptd) (M : gmap Z (bv 8)) (t : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) :
    uva_inj pt M ->
    upt_satp_ok_pt (ud_root pt) usatp ->
    pmp_ent0_ok pcfg paddr ->
    pt_claims 2 t -∗ uv_res pt M t usatp pcfg paddr.
  Proof.
    intros Hinj Hsatpok Hpmpok.
    iIntros "#Hclaims". rewrite /uv_res. iFrame "Hclaims".
    iIntros (t' tlbv') "%Hshape %Htok' %Htlbok' Hsatp Htlb Hpcfg Hpaddr Hmm".
    pose proof Htok' as (Hdisj' & Hdj' & _ & Hwfm' & Hspec').
    rewrite /uv_mm (bytes_own_union _ _ Hdj').
    iDestruct "Hmm" as "[Hmt' HMb']".
    iSplitR "HMb'".
    - iApply (upt_swp_close (ud_root pt) (ud_tfp pt) (ud_um pt) usatp tlbv'
                pcfg paddr Hsatpok Hpmpok with "Hsatp Htlb Hpcfg Hpaddr").
      iExists t'. iSplitR; [ by iPureIntro |]. iSplitR; [ by iPureIntro |].
      iSplitR; [ by iPureIntro |].
      iApply (ptree_own_of_bytes 2 t' Hdisj' with "[] Hmt'").
      by iApply (pt_claims_shape 2 t t' Hshape).
    - iApply (bytes_to_umem pt M Hinj with "HMb'").
  Qed.

  (* [WpUmodeStep.uv_swp_exec] with the byte map REAL and MOVING.  The
     landing map is pinned exactly as [uv_swp_fetch] pins its own: a submap
     of the exec fact's memory with the full domain IS that memory
     ([UserClassifyAsm.u_map_eq]).  The wrapper's certificate is taken at
     [empty] and lifted by [HartMemRun.goodmb_map_mono] -- a redirect never
     reaches a memory node. *)
  Lemma uv_swp_exec_mem (dq : dfrac) (mm mm2 : PtBytes.pamap) (rsx rs_x : regstate)
      (i : instruction) (o : option instruction) (ib : mword 32)
      (Pe : ExecutionResult -> mword 32 -> iProp Σ) :
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    goodmb Du_r Du_w (execute (uv_exp i o)) (u_state rsx mm) mm = true ->
    exec (execute (uv_exp i o)) (u_state rsx mm)
      = Some (RETIRE_SUCCESS, u_state rs_x mm2) ->
    (dom mm2 : gset Arch.pa) = dom mm ->
    gen_cert -∗ resv_any cpu_id -∗
    hreg_frame rsx u_Drw -∗ hreg_frame_ro (u_Df dq) rsx u_Dro -∗
    bytes_own mm -∗
    (∀ rs2 : regstate,
       ⌜reg_agree_on (u_Drw ∪ u_Dro) rs2 rs_x⌝ -∗
       hreg_frame rs2 u_Drw -∗ hreg_frame_ro (u_Df dq) rs2 u_Dro -∗
       bytes_own mm2 -∗ resv_any cpu_id -∗ Pe RETIRE_SUCCESS ib) -∗
    swp (execute i) (run_exec_post Pe ib).
  Proof.
    intros Hred Hg1 Hg2 He Hdom.
    iIntros "#Hcert Hany Hrw Hro Hmm Hk".
    destruct o as [j | ].
    - iApply (swp_mono with "[Hk] [Hany Hrw Hro Hmm]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute i) (u_state rsx mm) (u_state rsx mm) (ExecuteAs j)
                    rsx mm u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) ltac:(reflexivity)
                    (Hg1 (u_state rsx mm) mm)
                    (Hred (u_state rsx mm))
                    with "Hcert Hany Hrw Hro Hmm"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs1 mm1) "(%Hag1 & %Hsub1 & %Hdom1 & Hrw & Hro & Hmm & Hany)".
      assert (Hmm1 : mm1 = mm) by (apply (u_map_eq mm1 mm Hsub1); exact Hdom1).
      subst mm1.
      iApply run_exec_post_redirect.
      iApply (swp_mono with "[Hk] [Hany Hrw Hro Hmm]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute j) (u_state rsx mm) (u_state rs_x mm2) RETIRE_SUCCESS
                    rs1 mm u_disj Du_r_sub Du_w_sub Hag1 ltac:(reflexivity)
                    Hg2 He
                    with "Hcert Hany Hrw Hro Hmm"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs2 mm3) "(%Hag & %Hsub & %Hdm & Hrw & Hro & Hmm & Hany)".
      assert (Hmm3 : mm3 = mm2)
        by (apply (u_map_eq mm3 mm2 Hsub); rewrite Hdm; exact (eq_sym Hdom)).
      subst mm3.
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hmm Hany"). exact Hag.
    - iApply (swp_mono with "[Hk] [Hany Hrw Hro Hmm]").
      2:{ iApply (swp_hmrun_of_exec Du_r Du_w u_Drw u_Dro (u_Df dq)
                    (execute i) (u_state rsx mm) (u_state rs_x mm2) RETIRE_SUCCESS
                    rsx mm u_disj Du_r_sub Du_w_sub
                    ltac:(intros q _; reflexivity) ltac:(reflexivity)
                    Hg2 He
                    with "Hcert Hany Hrw Hro Hmm"). }
      iIntros (v) "(-> & Hpost)".
      iDestruct "Hpost" as (rs2 mm3) "(%Hag & %Hsub & %Hdm & Hrw & Hro & Hmm & Hany)".
      assert (Hmm3 : mm3 = mm2)
        by (apply (u_map_eq mm3 mm2 Hsub); rewrite Hdm; exact (eq_sym Hdom)).
      subst mm3.
      iApply (run_exec_post_direct Pe ib RETIRE_SUCCESS I).
      iApply ("Hk" $! rs2 with "[%] Hrw Hro Hmm Hany"). exact Hag.
  Qed.

End UvStoreRes.

(* the pins ride the nextPC write (WpUmodeStep's [uv_pins_wpre] recipe) *)
Lemma uv_pins_set_nextPC (P : uptd) (t : ptree) (rs : regstate) (v : mword 64) :
  u_exec_pins P t rs -> u_exec_pins P t (register_set nextPC v rs).
Proof.
  intros H. unfold u_exec_pins, u_hw_pins, u_cfg_pins, u_pt_pins in H |- *.
  repeat (rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC));
          [ | vm_compute; reflexivity ]).
  exact H.
Qed.

(* the domain of the re-keyed image does not move under a store *)
Lemma upa_map_dom_eq (pt : uptd) (M1 M2 : gmap Z (bv 8)) :
  dom M1 = dom M2 -> (dom (upa_map pt M1) : gset Arch.pa) = dom (upa_map pt M2).
Proof.
  intro Hd. apply set_eq. intro a.
  rewrite !upa_map_dom_elem. split; intros (va & Hva & Heq); exists va.
  - split; [ rewrite <- Hd; exact Hva | exact Heq ].
  - split; [ rewrite Hd; exact Hva | exact Heq ].
Qed.

(* ===================================================================== *)
(* §5 The store's post-fetch middle, and the leaf.                         *)
(* ===================================================================== *)

(* EACH OF THE THREE LAYERS BELOW GETS ITS OWN SECTION, and that is not
   cosmetic: a lemma's [CpuId] SECTION variable is auto-applied and cannot
   be named at application (claude-notes/projects/user-verified.md §5), so
   a caller standing at the ∀-bound hart the engine hands it can only reach
   a callee whose [CpuId] is an ordinary implicit -- i.e. one declared in a
   DIFFERENT section.  WpUmodeStep splits [uv_retire_post_fetch] /
   [uv_obl_*] / [wp_uv_retire] the same way. *)
Section UvStorePostFetch.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* The geometry-agnostic middle: from the FETCHED file, write nextPC,    *)
  (* run the store, and hand [uv_psi_active] the payload at the NEW image  *)
  (* and the UNCHANGED register file.  The store-flavoured twin of         *)
  (* [WpUmodeStep.uv_retire_post_fetch].                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma uv_store_post_fetch (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (dpc kk : Z)
      (i : instruction) (o : option instruction)
      (imm : mword 12) (sr1 sr2 : mword 5)
      (w_st va wval : mword 64) (ib : mword 32) (t' : ptree)
      (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rsE rs2 : regstate) :
    ustore_width kk ->
    uv_redirect i o ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uva_inj pt M ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    u_exec_pins pt t' rs2 ->
    register_lookup (R_bitvector_64 PC) rs2 = pc ->
    register_lookup hart_state rs2 = HART_ACTIVE tt ->
    register_lookup cur_privilege rs2 = User ->
    user_mstatus_ok (register_lookup (R_bitvector_64 mstatus) rs2) ->
    u_gpr_agree m rs2 ->
    m (Regidx (mword_of_int 0)) = zero_reg ->
    register_lookup (R_bitvector_64 stvec) rs2 = uc_stvec C ->
    register_lookup (R_bitvector_64 mie) rs2 = uc_mie C ->
    register_lookup (R_bitvector_64 mideleg) rs2 = uc_mideleg C ->
    register_lookup (R_bitvector_64 medeleg) rs2 = uc_medeleg C ->
    register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S ->
    register_lookup (R_bitvector_64 mstateen0) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_32 sstateen0) rs2 = (mword_of_int 0 : mword 32) ->
    register_lookup (R_bitvector_64 senvcfg) rs2 = (mword_of_int 0 : mword 64) ->
    register_lookup (R_bitvector_64 satp) rs2 = usatp ->
    register_lookup pmpcfg_n rs2 = pcfg ->
    register_lookup pmpaddr_n rs2 = paddr ->
    register_lookup (R_bool minstret_increment) rs2
      = minstret_inc_flag (register_lookup (R_bitvector_32 mcountinhibit) rsE)
          (register_lookup (R_bitvector_64 minstretcfg) rsE)
          (register_lookup cur_privilege rsE) ->
    agree_on D_u (u_state rs2 ∅) dstateU ->
    uv_tree_ok pt (upa_map pt M) t' ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) kk wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc dpc) -∗
       WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    bytes_own (uv_mm t' (upa_map pt M)) -∗
    uv_res pt M t' usatp pcfg paddr -∗
    hreg_frame (register_set nextPC (add_vec_int pc dpc) rs2) u_Drw -∗
    hreg_frame_ro (u_Df (uc_dqc C))
      (register_set nextPC (add_vec_int pc dpc) rs2) u_Dro -∗
    swp (execute i)
      (run_exec_post (fun (r : ExecutionResult) (ib' : mword 32) =>
                        uv_step_post C R rsE (Step_Execute (r, ib'))) ib).
  Proof.
    intros Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
      Hpins2 Lpc2 Lhs2 Lcp2 Hms2 Hgag2 Hx0 Lstvec2 Lmie2 Lmdl2 Lmedl2 Lmenv2
      Lmste2 Lsste2 Lsenv2 Lsatp2 Lpcfg2 Lpaddr2 Lmi2 Hagd2 Htok'.
    destruct Hkw as (Hvw & Hwrite_plain).
    pose proof (vmem_width_pos kk Hvw) as Hk.
    pose proof (uvw_le8 kk Hvw) as Hk8.
    pose proof (uvw_dvd kk Hvw) as Hkdvd.
    pose proof (uvw_uint kk Hvw) as Huintk.
    set (md := upa_map pt M).
    set (rsx := register_set nextPC (add_vec_int pc dpc) rs2).
    set (pa := u_walk_pa w_st va).
    (* ---- the pins, transported across the nextPC write ---- *)
    assert (Tn : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_lookup r rsx = vv).
    { intros r vv Hv Hne. unfold rsx.
      rewrite irrelevant_register_set; [ exact Hv | exact Hne ]. }
    assert (Lpcx : register_lookup (R_bitvector_64 PC) rsx = pc)
      by (apply (Tn _ _ Lpc2); vm_compute; reflexivity).
    assert (Lnpcx : register_lookup (R_bitvector_64 nextPC) rsx
                    = add_vec_int pc dpc)
      by (unfold rsx; apply register_lookup_set).
    assert (Lcpx : register_lookup cur_privilege rsx = User)
      by (apply (Tn _ _ Lcp2); vm_compute; reflexivity).
    assert (Hmsx : register_lookup (R_bitvector_64 mstatus) rsx
                   = register_lookup (R_bitvector_64 mstatus) rs2)
      by (apply (Tn _ _ eq_refl); vm_compute; reflexivity).
    assert (Hagdx : agree_on D_u (u_state rsx ∅) dstateU)
      by exact (agree_u_set_nextPC (u_state rs2 ∅) (add_vec_int pc dpc) Hagd2).
    assert (Hgagx : u_gpr_agree m rsx).
    { intros q Hnz. unfold rsx.
      rewrite (irrelevant_register_set _ (R_bitvector_64 nextPC) rs2 _
                 (regbeq_gpr_nextPC (uint q))).
      exact (Hgag2 q Hnz). }
    assert (Hpinsx : u_exec_pins pt t' rsx)
      by exact (uv_pins_set_nextPC pt t' rs2 (add_vec_int pc dpc) Hpins2).
    assert (Hcfgx : u_data_cfg rsx)
      by (split_and!; [ exact Lcpx | rewrite Hmsx; exact Hms2 |
                        apply (Tn _ _ Lmenv2); vm_compute; reflexivity ]).
    (* ---- the store window, in the re-keyed image ---- *)
    assert (Hnc : forall j : nat, (j < Z.to_nat kk)%nat ->
              bv_unsigned va mod 4096 + Z.of_nat j < 4096).
    { intros j Hj. apply (uinpage_nc_k va kk (Z.of_nat j) Hpg). lia. }
    assert (Hwin : forall j : nat, (j < Z.to_nat kk)%nat ->
              uva_pa pt (uint va + Z.of_nat j) = pa_add pa j)
      by (intros j Hj; exact (uva_pa_window pt w_st va j Hl (Hnc j Hj))).
    assert (Hmdw : forall j : nat, (j < Z.to_nat kk)%nat ->
              is_Some (md !! pa_add pa j)).
    { intros j Hj. destruct (HMb j Hj) as (bb & Hbb). exists bb.
      rewrite <- (Hwin j Hj). exact (upa_map_lookup pt M _ bb Hinj Hbb). }
    (* ---- the store, pure ---- *)
    destruct (uv_store_mm kk Hk Hk8 Hkdvd Huintk Hwrite_plain pt t' md rsx
                w_st va (ustore_data kk wval)
                Hl Hchk Hcanon Hal (uinpage_one va kk Hpg) Hmdw Hcfgx Hpinsx Htok')
      as (rsw & t'' & Hvwa & Hvwag & Tonly & Htlbok'' & Htok'' & Hshape).
    (* ---- the execute, exec side and certificate side ---- *)
    pose proof (uv_gpr_vals m rsx Hgagx Hx0) as Hvals.
    assert (Hbase : (if Z.eqb (uint sr1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr1))) rsx)
                    = m !!! Regidx sr1) by exact (Hvals sr1).
    assert (Hvv : (if Z.eqb (uint sr2) 0 then zero_reg
                   else register_lookup (R_bitvector_64 (gpr_of_Z (uint sr2))) rsx)
                  = wval) by (rewrite Hwval; exact (Hvals sr2)).
    pose proof (agree_u_misa (u_state rsx ∅) Hagdx) as Lmisax.
    pose proof (agree_u_menvcfg (u_state rsx ∅) Hagdx) as Lmenvx.
    pose proof (agree_u_senvcfg (u_state rsx ∅) Hagdx) as Lsenvx.
    assert (Hmxrx : eq_vec (_get_Mstatus_MXR (register_lookup mstatus rsx))
                      ('b"0") = true)
      by (rewrite Hmsx; exact (proj1 (proj2 (proj2 Hms2)))).
    assert (Hpml : exec (get_pmlen (Store Data) User) (u_state rsx (uv_mm t' md))
                   = Some (0, u_state rsx (uv_mm t' md)))
      by exact (exec_get_pmlen_u (Store Data) (u_state rsx (uv_mm t' md))
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx).
    assert (Hpmlg : goodmb Du_r Du_w (get_pmlen (Store Data) User)
                      (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true)
      by (apply goodmb_of_goodb;
          exact (goodb_get_pmlen_u Du_r (Store Data) (u_state rsx (uv_mm t' md))
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity) Hmxrx Lmisax Lmenvx Lsenvx)).
    assert (Hmprvx : eq_vec (_get_Mstatus_MPRV
                       (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)))
                       ('b"1") = false)
      by (cbn [u_state sregs]; rewrite Hmsx; exact (proj1 (proj2 Hms2))).
    pose proof (exec_effectivePrivilege_mprv0 (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) Hmprvx) as Heff.
    pose proof (goodmb_effectivePrivilege_mprv0 Du_r Du_w (Store Data)
                  (register_lookup mstatus (u_state rsx (uv_mm t' md)).(sregs)) User
                  (u_state rsx (uv_mm t' md)) (uv_mm t' md) Hmprvx) as Heffg.
    pose proof (u_translationMode_pure pt t' rsx (uv_mm t' md) Hcfgx Hpinsx) as Htm.
    pose proof (u_goodmb_translationMode_pure pt t' rsx (uv_mm t' md)
                  (uv_mm t' md) Hcfgx Hpinsx) as Htmg.
    assert (Hex : exec (execute (uv_exp i o)) (u_state rsx (uv_mm t' md))
                  = Some (RETIRE_SUCCESS,
                          u_state rsw (write_bytes (uv_mm t'' md) pa (Z.to_N kk)
                                         (ustore_data kk wval)))).
    { rewrite Hexp.
      exact (exec_execute_STORE_k_u_walk kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 (u_state rsx (uv_mm t' md)) _
               Lcpx Heff Hpml Htm Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)). }
    assert (Hexg : goodmb Du_r Du_w (execute (uv_exp i o))
                     (u_state rsx (uv_mm t' md)) (uv_mm t' md) = true).
    { rewrite Hexp.
      exact (goodmb_execute_STORE_k_u_walk kk Hvw sr2 sr1 imm (m !!! Regidx sr1) wval
               Sv39 (u_state rsx (uv_mm t' md)) _ (uv_mm t' md)
               Lcpx Heff Heffg Hpml Hpmlg Htm Htmg Hbase Hvv
               ltac:(rewrite <- Hva; exact Hvwa)
               ltac:(rewrite <- Hva; exact Hvwag)). }
    (* ---- the landing map IS the re-keyed post-store image ---- *)
    set (M' := uM_store M (uint va) kk wval).
    assert (HMdom : dom M' = dom M)
      by (apply uM_store_dom; intros j Hj; destruct (HMb j Hj) as (bb & Hbb);
          exact (mk_is_Some _ _ Hbb)).
    assert (Hinj' : uva_inj pt M')
      by exact (uva_inj_dom pt M M' (eq_sym HMdom) Hinj).
    assert (Hmdeq : upa_map pt M' = write_bytes md pa (Z.to_N kk) wval)
      by (apply upa_map_store;
          [ exact Hinj
          | intros j Hj; destruct (HMb j Hj) as (bb & Hbb);
            exact (mk_is_Some _ _ Hbb)
          | exact Hwin ]).
    assert (Hdat : write_bytes md pa (Z.to_N kk) (ustore_data kk wval)
                   = write_bytes md pa (Z.to_N kk) wval).
    { apply write_bytes_ext. intros j Hj.
      apply nth_byte_ustore_data; [ exact Hk | exact Hk8 | lia ]. }
    pose proof Htok'' as (Hdisj'' & Hdj'' & Hram'' & Hwfm'' & Hspec'').
    assert (Hnt : forall j : nat, (N.of_nat j < Z.to_N kk)%N ->
              ptree_bytes 2 t'' !! pa_add pa j = None).
    { intros j Hj. apply (uv_mm_tree_none t'' md _ Hdj''). apply Hmdw. lia. }
    assert (Hmmeq : write_bytes (uv_mm t'' md) pa (Z.to_N kk) (ustore_data kk wval)
                    = uv_mm t'' (upa_map pt M')).
    { rewrite /uv_mm (write_bytes_union_r (ptree_bytes 2 t'') md pa (Z.to_N kk)
                        (ustore_data kk wval) Hnt).
      rewrite Hdat Hmdeq. reflexivity. }
    rewrite Hmmeq in Hex.
    (* ---- the post-store tree is well-formed at the NEW image ---- *)
    assert (Hdomimg : (dom (upa_map pt M') : gset Arch.pa) = dom md)
      by (unfold md; exact (upa_map_dom_eq pt M' M HMdom)).
    assert (Htokn : uv_tree_ok pt (upa_map pt M') t'').
    { split_and!; [ exact Hdisj'' | | | exact Hwfm'' | exact Hspec'' ].
      - rewrite Hmdeq. apply map_disjoint_spec. intros x b1 b2 H1 H2.
        assert (Hs : is_Some (md !! x)).
        { apply (write_bytes_is_Some_iff md pa (Z.to_N kk) wval x);
            [ intros j Hj; apply Hmdw; lia | exact (mk_is_Some _ _ H2) ]. }
        destruct Hs as (b3 & Hb3).
        exact (proj1 (map_disjoint_spec (ptree_bytes 2 t'') md) Hdj'' x b1 b3 H1 Hb3).
      - intros a Ha. apply Hram''.
        rewrite (uv_mm_dom_img t'' (upa_map pt M') md Hdomimg) in Ha.
        exact Ha. }
    (* ---- the domain of the whole map does not move ---- *)
    assert (Hdomall : (dom (uv_mm t'' (upa_map pt M')) : gset Arch.pa)
                      = dom (uv_mm t' md)).
    { rewrite (uv_mm_dom_img t'' (upa_map pt M') md Hdomimg).
      exact (eq_sym (uv_mm_dom t' t'' md Hshape)). }
    (* ---- the post-store file, from the pre-store one ---- *)
    assert (Tw : forall (r : register) (vv : type_of_register r),
              register_lookup r rs2 = vv ->
              register_beq r (R_bitvector_64 nextPC) = false ->
              register_beq r (tlb : register) = false ->
              register_lookup r rsw = vv).
    { intros r vv Hv Hne Hnt2. rewrite (Tonly r Hnt2). exact (Tn r vv Hv Hne). }
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hmm [#Hclaims Hcl] Hrw Hro".
    iApply (uv_swp_exec_mem (uc_dqc C) (uv_mm t' md) (uv_mm t'' (upa_map pt M'))
              rsx rsw i o ib _ Hred Hg1
              Hexg Hex Hdomall
              with "Hcert Hany Hrw Hro Hmm [Hk Hcl]").
    iIntros (rs3) "%Hag3 Hrw Hro Hmm Hany".
    rewrite /uv_step_post.
    iExists rsw.
    iSplitR.
    { iPureIntro. rewrite /uv_land. split_and!;
        [ exact (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity))
        | exact (Tw _ _ Lmi2 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; reflexivity))
        | exact I ]. }
    change RETIRE_SUCCESS with (Retire_Success tt). cbn match.
    rewrite /uv_arm_res.
    rewrite <- (hreg_frame_ext rs3 rsw u_Drw
                 ltac:(intros q Hq; apply Hag3, elem_of_union_l, Hq)).
    rewrite <- (hreg_frame_ro_ext (u_Df (uc_dqc C)) rs3 rsw u_Dro
                 ltac:(intros q Hq; apply Hag3, elem_of_union_r, Hq)).
    iFrame "Hrw Hro".
    iApply (uv_psi_active C pt R Ψ M' m (add_vec_int pc dpc) t'' usatp pcfg paddr
              rsw
              (Tw _ _ Lhs2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lcp2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              ltac:(rewrite (Tw (R_bitvector_64 mstatus) _ eq_refl
                               ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; reflexivity));
                    exact Hms2)
              ltac:(rewrite (Tonly (R_bitvector_64 nextPC)
                               ltac:(vm_compute; reflexivity)); exact Lnpcx)
              ltac:(intros q Hnz;
                    rewrite (Tonly (R_bitvector_64 (gpr_of_Z (uint q)))
                               (uv_gpr_ne_tlb (uint q)));
                    exact (Hgagx q Hnz))
              Hx0
              (Tw _ _ Lstvec2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmie2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmdl2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmedl2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmenv2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lmste2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsste2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsenv2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lsatp2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lpcfg2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              (Tw _ _ Lpaddr2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
              Htokn Htlbok''
              with "Hamb Hcap Hany Hmm [] Hk").
    iApply (uv_res_reimg pt M' t'' usatp pcfg paddr Hinj'
              ltac:(pose proof Hpins2 as (_ & _ & ((us & Hok & Hsa) & _) & _);
                    rewrite Lsatp2 in Hsa; rewrite Hsa; exact Hok)
              ltac:(pose proof Hpins2 as (_ & _ &
                      (_ & HA & Hord & HX & HW & HR & Hcov) & _);
                    rewrite Lpcfg2 in HA, HX, HW, HR;
                    rewrite Lpaddr2 in Hord, Hcov;
                    unfold pmp_ent0_ok; split_and!;
                    [ exact HA | exact Hord | exact HX | exact HW | exact HR
                    | exact Hcov ])
              with "[]").
    by iApply (pt_claims_shape 2 t' t'' Hshape).
  Qed.

End UvStorePostFetch.

Section UvStoreObl.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* §6 THE OBLIGATION, once per FETCH SHAPE -- the store twins of         *)
  (* WpUmodeStep's [uv_obl_base] / [uv_obl_rvc], differing from them only  *)
  (* in the tail they hand the fetched file to.                           *)
  (* ------------------------------------------------------------------- *)
  Lemma uv_store_obl_base (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (w : mword 32)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (sr1 sr2 : mword 5) (w_st va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_Base w, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_base w i ->
    ustore_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) kk wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗ WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hva Hwval
      Hl Hchk Hcanon Hpg Hal HMb.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_Base w) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_base.
    iExists rs2, i, pc, 8%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_base rs2 ∅ w i Hagd2
               (Hdec dstateU ltac:(intros r _; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uv_store_post_fetch C pt R Ψ M m pc 4 kk i o imm sr1 sr2 w_st va wval
              (zero_extend' 32 w) t' usatp pcfg paddr rs1 rs2
              Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
              Hpins2
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Hagd2 Htok'
              with "Hcert Hamb Hcap Hk Hany Hmm Hres Hrw Hro").
  Qed.

  Lemma uv_store_obl_rvc (R : iProp Σ) (Ψ : usys_protocol Σ)
      (M : gmap Z (bv 8)) (m : regfile) (pc : mword 64) (h : mword 16)
      (i : instruction) (o : option instruction) (kk : Z) (imm : mword 12)
      (sr1 sr2 : mword 5) (w_st va wval : mword 64)
      (t t' : ptree) (usatp : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rs1 rsA rsf : regstate) :
    uv_pre C pt M m pc t rs1 rsA usatp pcfg paddr ->
    exec (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      = Some (F_RVC h, u_state rsf (uv_mm t' (upa_map pt M))) ->
    goodmb Du_r Du_w (fetch tt) (u_state rsA (uv_mm t (upa_map pt M)))
      (uv_mm t (upa_map pt M)) = true ->
    u_tlb_only rsA rsf ->
    tlb_ok_pt (mword_of_int 0) t' (register_lookup tlb rsf) ->
    uv_tree_ok pt (upa_map pt M) t' ->
    pt_same_shape 2 t t' ->
    udecode_rvc h i ->
    ustore_width kk ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    uv_exp i o = STORE (imm, Regidx sr2, Regidx sr1, kk) ->
    va = add_vec (m !!! Regidx sr1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx sr2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - kk ->
    is_aligned_vaddr (Virtaddr va) kk = true ->
    (forall j : nat, (j < Z.to_nat kk)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    gen_cert -∗ uv_amb -∗ uv_cap C pt Ψ -∗
    (R -∗ ∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) kk wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗ WP (Loop : expr riscv_lang)) -∗
    resv_any cpu_id -∗
    hreg_frame rsA u_Drw -∗ hreg_frame_ro (u_Df (uc_dqc C)) rsA u_Dro -∗
    bytes_own (uv_mm t (upa_map pt M)) -∗
    uv_res pt M t usatp pcfg paddr -∗
    swp (fetch tt)
      (run_fetch_post u_Drw u_Dro (u_Df (uc_dqc C))
         (fun (r : ExecutionResult) (ib : mword 32) =>
            uv_step_post C R rs1 (Step_Execute (r, ib)))
         (fun (xv : mword 64) (e : ExceptionType) =>
            uv_step_post C R rs1 (Step_Fetch_Failure (Virtaddr xv, e)))
         (fun _ : ext_fetch_addr_error => False)).
  Proof.
    intros Hpre Hfe Hfg Tr Htlbok' Htok' Hshape Hdec Hkw Hred Hg1 Hexp Hva Hwval
      Hl Hchk Hcanon Hpg Hal HMb.
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    iIntros "#Hcert #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iApply (uv_swp_fetch pt M t t' (uc_dqc C) rsA rsf (F_RVC h) _ _ _
              Hfe Hfg Hshape with "Hcert Hany Hrw Hro Hmm [Hk Hres]").
    iIntros (rs2) "%Hag Hrw Hro Hmm Hany".
    iDestruct (uv_res_move pt M t t' usatp pcfg paddr Hshape with "Hres")
      as "Hres".
    assert (T2 : forall (r : register) (val : type_of_register r),
              r ∈ u_Drw ∪ u_Dro -> register_beq r tlb = false ->
              register_lookup r rsA = val -> register_lookup r rs2 = val).
    { intros r val Hin Hne Hv. rewrite (Hag r Hin) (Tr r Hne). exact Hv. }
    assert (Ltlb2 : register_lookup tlb rs2 = register_lookup tlb rsf)
      by exact (Hag _ u_in_tlb).
    assert (Hpins2 : u_exec_pins pt t' rs2).
    { apply (u_pins_move pt t t' rsA rs2);
        [ intros q Hq _;
          exact (T2 q _ (u_Dfix_sub q Hq) (u_fix_ne_tlb q Hq) eq_refl)
        | rewrite Ltlb2; exact Htlbok'
        | exact HpinsA ]. }
    pose proof Hpins2 as ((Hmisa2 & _ & Hsenv2 & _ & _ & Helpne2) &
                          (Hmste2 & Hsste2) & _ & Htlbok2).
    assert (Lcp2 : register_lookup cur_privilege rs2 = User)
      by exact (T2 _ _ u_in_priv ltac:(vm_compute; reflexivity) LcpA).
    assert (Lmenv2 : register_lookup (R_bitvector_64 menvcfg) rs2 = MENVCFG_S)
      by exact (T2 _ _ u_in_menv ltac:(vm_compute; reflexivity) LmenvA).
    assert (HmisaC2 : eq_vec (_get_Misa_C (register_lookup misa rs2)) ('b"1") = true)
      by (rewrite Hmisa2; vm_compute; reflexivity).
    assert (Hagd2 : agree_on D_u (u_state rs2 ∅) dstateU)
      by exact (UserTotalU.u_agree_decode rs2 ∅ Lcp2 Lmenv2
                  (proj1 Hpins2) (proj1 (proj2 Hpins2))).
    assert (Hgag2 : u_gpr_agree m rs2).
    { intros q Hnz. rewrite (HgagA q Hnz).
      exact (eq_sym (T2 _ _ (u_gpr_in_D q Hnz) (uv_gpr_ne_tlb (uint q)) eq_refl)). }
    rewrite /run_fetch_post /run_fetch_rvc.
    iExists rs2, i, pc, 8%nat, 4%nat.
    iSplitR.
    { iPureIntro.
      exact (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA). }
    iSplitR.
    { iPureIntro.
      exact (UserTotalU.u_hval_rvc rs2 ∅ h i Hagd2
               (Hdec dstateU ltac:(vm_compute; reflexivity))). }
    iSplitR.
    { iPureIntro. exact (hfrun_lpad (u_Drw ∪ u_Dro) u_Drw rs2 u_in_elp Helpne2). }
    iSplitR.
    { iPureIntro. apply (hfrun_cE_Zca (u_Drw ∪ u_Dro) u_Drw rs2 u_in_misa).
      exact HmisaC2. }
    iFrame "Hrw Hro".
    iIntros "Hrw Hro".
    iApply (uv_store_post_fetch C pt R Ψ M m pc 2 kk i o imm sr1 sr2 w_st va wval
              (zero_extend' 32 h) t' usatp pcfg paddr rs1 rs2
              Hkw Hred Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb Hinj Hg1
              Hpins2
              (T2 _ _ u_in_PC ltac:(vm_compute; reflexivity) LpcA)
              (T2 _ _ u_in_hart ltac:(vm_compute; reflexivity) LhsA)
              Lcp2
              ltac:(rewrite (T2 _ _ u_in_mst ltac:(vm_compute; reflexivity)
                               (eq_refl : register_lookup (R_bitvector_64 mstatus) rsA
                                          = register_lookup (R_bitvector_64 mstatus) rsA));
                    exact HmsokA)
              Hgag2 Hx0
              (T2 _ _ u_in_stvec ltac:(vm_compute; reflexivity) LstvecA)
              (T2 _ _ u_in_mie ltac:(vm_compute; reflexivity) LmieA)
              (T2 _ _ u_in_mdl ltac:(vm_compute; reflexivity) LmdlA)
              (T2 _ _ u_in_medl ltac:(vm_compute; reflexivity) LmedlA)
              Lmenv2 Hmste2 Hsste2 Hsenv2
              (T2 _ _ u_in_satp ltac:(vm_compute; reflexivity) LsatpA)
              (T2 _ _ u_in_pcfg ltac:(vm_compute; reflexivity) LpcfgA)
              (T2 _ _ u_in_paddr ltac:(vm_compute; reflexivity) LpaddrA)
              (T2 _ _ u_in_mi ltac:(vm_compute; reflexivity) LmiA)
              Hagd2 Htok'
              with "Hcert Hamb Hcap Hk Hany Hmm Hres Hrw Hro").
  Qed.

End UvStoreObl.

Section WpUmodeStore.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* THE STORE LEAF.                                                       *)
  (*                                                                       *)
  (* Width-generic: [k] is any [ustore_width] (1/2/4/8), so [sb/sh/sw/sd]  *)
  (* and every compressed store are ONE lemma.  It takes the same [uinstr] /*)
  (* [uv_redirect] pair the funnel does, so a compressed store names its   *)
  (* [ExecuteAs] expansion -- and, exactly as the ported funnel does, the  *)
  (* WRAPPER's [goodmb] certificate beside it (a redirect never reaches a  *)
  (* memory node, so it holds at every map; the STORE's own certificate is *)
  (* produced here from the catalogue).  No register is written; the image *)
  (* gains exactly the low [k] bytes of [wval = m !!! rs2].                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_store_later (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rs2 : mword 5) (k : Z)
      (w_st va wval : mword 64) :
    ustore_width k ->
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = STORE (imm, Regidx rs2, Regidx rs1, k) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    ▷ (∀ CID0 : CpuId,
         uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) k wval) m -∗
         pc_is (CID := CID0) (add_vec_int pc (if is_rvc then 2 else 4)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb.
    destruct Hui as [Hal2 Hcanonpc Hleaf Hinpage Hcode].
    destruct Hleaf as (w_leaf & Hum & Hlok).
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_step C pt _ Ψ M m pc with "Hcg Hpc [] Hcont").
    rewrite /uv_step_obl.
    iIntros (R CIDo t rs1s rsA usatp pcfg paddr)
      "%Hpre #Hamb #Hcap Hk Hany Hrw Hro Hmm Hres".
    iPoseProof "Hamb" as "(#Hhw & _ & _)".
    iPoseProof "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        #Hcert & _)".
    pose proof Hpre as (Hinj & Htok & HpinsA & LhsA & LcpA & HmsokA & LpcA &
                        HgagA & LstvecA & LmieA & LmdlA & LmedlA & LmenvA &
                        LsatpA & LpcfgA & LpaddrA & LmiA & Hx0).
    destruct is_rvc.
    - (* ================= COMPRESSED ================= *)
      destruct Hcode as (h & HisRVC & Hbytes & Hdecrvc & Hnext2).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (Hnext2 ltac:(first [ exact Hal4 | reflexivity ])) as (b2 & b3 & Hb2 & Hb3).
        assert (Hbytes4 : uM_bytes M (uint pc) 4 (urvc4_word h b2 b3)).
        { intros j Hj. rewrite (urvc4_byte h b2 b3 j Hj).
          destruct j as [ | [ | [ | [ | j ] ] ] ]; try lia;
            cbn [lookup_total list_lookup_total];
            [ exact (Hbytes 0%nat ltac:(lia)) | exact (Hbytes 1%nat ltac:(lia))
            | exact Hb2 | exact Hb3 ]. }
        destruct (uv_fetch_4 pt M t rsA w_leaf pc (urvc4_word h b2 b3)
                    Hinj Hum Hlok Hcanonpc Hinpage Hal4 Hbytes4 LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite urvc4_low HisRVC in Hfe.
        iApply (uv_store_obl_rvc C pt R Ψ M m pc h i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_rvc_2 pt M t rsA w_leaf pc h
                    Hinj Hum Hlok Hcanonpc Hinpage Hal2 Hal4 Hbytes HisRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uv_store_obl_rvc C pt R Ψ M m pc h i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecrvc Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
    - (* ================= BASE (4-byte) ================= *)
      destruct Hcode as (w & HnRVC & Hbytes & Hdecbase).
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + destruct (uv_fetch_4 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hinpage Hal4 Hbytes LpcA LcpA
                    (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        rewrite HnRVC in Hfe.
        iApply (uv_store_obl_base C pt R Ψ M m pc w i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
      + destruct (uv_fetch_base_2 pt M t rsA w_leaf pc w
                    Hinj Hum Hlok Hcanonpc Hinpage Hal2 Hal4 Hbytes HnRVC
                    LpcA LcpA (proj1 HmsokA) LmenvA HpinsA Htok)
          as (rsf & t' & Hfe & Hfg & Tr & Htlbok' & Htok' & Hshape).
        iApply (uv_store_obl_base C pt R Ψ M m pc w i o k imm rs1 rs2 w_st va wval
                  t t' usatp pcfg paddr rs1s rsA rsf Hpre Hfe Hfg Tr Htlbok'
                  Htok' Hshape Hdecbase Hkw Hred Hg1 Hexp Hva Hwval Hl Hchk
                  Hcanon Hpg Hal HMb
                  with "Hcert Hamb Hcap Hk Hany Hrw Hro Hmm Hres").
  Qed.

  (* the later-free restatement: the shape every instance takes *)
  Lemma wp_uv_store (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (imm : mword 12) (rs1 rs2 : mword 5) (k : Z)
      (w_st va wval : mword 64) :
    ustore_width k ->
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    match o with
    | Some _ => forall (s : mstate) (mb : PtBytes.pamap),
                  goodmb Du_r Du_w (execute i) s mb = true
    | None => True
    end ->
    is_lpad_instruction i = false ->
    uv_exp i o = STORE (imm, Regidx rs2, Regidx rs1, k) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4096 - k ->
    is_aligned_vaddr (Virtaddr va) k = true ->
    (forall j : nat, (j < Z.to_nat k)%nat ->
       exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) k wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_store_later Ψ M m pc is_rvc i o imm rs1 rs2 k w_st va wval
              Hkw Hui Hred Hg1 Hlpad Hexp Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
              with "Hcg Hpc [Hcont]").
    iNext. iExact "Hcont".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sd rs2, imm(rs1) -- the base 8-byte store.  Base geometry, no         *)
  (* [ExecuteAs] redirect, so [o := None].                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_sd (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rs2 : mword 5)
      (w_st va wval : mword 64) :
    uinstr pt M pc false (STORE (imm, Regidx rs2, Regidx rs1, 8)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store8 M (uint va) wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hl Hchk Hcanon Hpg Hal HMb.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_store Ψ M m pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 8)) None
              imm rs1 rs2 8 w_st va wval
              ustore_width_8 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sw rs2, imm(rs1) -- the base 4-byte store: the image gains the LOW    *)
  (* four bytes of [m !!! rs2].                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_sw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rs2 : mword 5)
      (w_st va wval : mword 64) :
    uinstr pt M pc false (STORE (imm, Regidx rs2, Regidx rs1, 4)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (forall j : nat, (j < 4)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) 4 wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hl Hchk Hcanon Hpg Hal HMb.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_store Ψ M m pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 4)) None
              imm rs1 rs2 4 w_st va wval
              ustore_width_4 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sb rs2, imm(rs1) -- the base 1-byte store.  A 1-byte access is        *)
  (* trivially aligned and can never cross a page, so BOTH the alignment   *)
  (* and the in-page premises are discharged HERE (as [wp_uv_lbu] does on  *)
  (* the load side) -- the call site supplies only the byte that is being  *)
  (* overwritten.                                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_sb (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rs2 : mword 5)
      (w_st va wval : mword 64) (bb : mword 8) :
    uinstr pt M pc false (STORE (imm, Regidx rs2, Regidx rs1, 1)) ->
    va = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    M !! (uint va) = Some bb ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) 1 wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hva Hwval Hl Hchk Hcanon Hbb.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_store Ψ M m pc false
              (STORE (imm, Regidx rs2, Regidx rs1, 1)) None
              imm rs1 rs2 1 w_st va wval
              ustore_width_1 Hui ltac:(intro s; exact I) I eq_refl eq_refl
              Hva Hwval Hl Hchk Hcanon (uinpage_byte va) (is_aligned_vaddr_1 va)
              ltac:(intros j Hj;
                    assert (Hj0 : j = 0%nat) by (clear -Hj; lia);
                    subst j; exists bb;
                    rewrite Z.add_0_r; exact Hbb)
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.sdsp rs2, uimm -- the compressed 8-byte store off sp.  The          *)
  (* [ExecuteAs] expansion is [STORE (zext(uimm ++ 000), rs2, sp, 8)]      *)
  (* ([exec_execute_C_SDSP]).                                              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_csdsp (Psi : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 6) (rs2 : mword 5)
      (w_st tgt wval : mword 64) :
    uinstr pt M pc true (C_SDSP (uimm, Regidx rs2)) ->
    tgt = add_vec (m !!! Regidx csp_rs1)
            (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of tgt = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon tgt ->
    Z.rem (uint tgt) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr tgt) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint tgt + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Psi M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Psi (uM_store8 M (uint tgt) wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htgt Hwval Hl Hchk Hcanon Hpg Hal HMb.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_store Psi M m pc true (C_SDSP (uimm, Regidx rs2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            Regidx rs2, Regidx csp_rs1, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              csp_rs1 rs2 8 w_st tgt wval
              ustore_width_8 Hui
              ltac:(intro s; apply exec_execute_C_SDSP)
              (fun s mb => goodmb_execute_C_SDSP_U Du_r Du_w uimm (Regidx rs2) s mb)
              eq_refl eq_refl
              Htgt Hwval Hl Hchk Hcanon Hpg Hal HMb
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.sd rs2', uimm(rs1') -- the compressed 8-byte register-relative      *)
  (* store.  Both register fields are COMPRESSED indices, so the leaf      *)
  (* takes the expanded ones with the decoder's expansion as pure          *)
  (* premises (one [vm_compute] apiece at the call), exactly as            *)
  (* [wp_uv_caddi4spn] does.                                               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_csd (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5)
      (w_st va wval : mword 64) :
    uinstr pt M pc true (C_SD (uimm, Cregidx cr1, Cregidx cr2)) ->
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"000")))) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4088 ->
    is_aligned_vaddr (Virtaddr va) 8 = true ->
    (forall j : nat, (j < 8)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store8 M (uint va) wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcr2 Hva Hwval Hl Hchk Hcanon Hpg Hal HMb.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_store Ψ M m pc true (C_SD (uimm, Cregidx cr1, Cregidx cr2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"000")),
                            Regidx rs2, Regidx rs1, 8)))
              (zero_extend' 12 (concat_vec uimm ('b"000")))
              rs1 rs2 8 w_st va wval
              ustore_width_8 Hui
              ltac:(intro s;
                    exact (exec_execute_C_SD_leaf uimm (Cregidx cr1) (Cregidx cr2)
                             (zero_extend' 12 (concat_vec uimm ('b"000")))
                             rs1 rs2 s eq_refl Hcr1 Hcr2))
              (fun s mb => goodmb_execute_C_SD_U Du_r Du_w uimm (Cregidx cr1)
                             (Cregidx cr2) s mb)
              eq_refl eq_refl
              Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
              with "Hcg Hpc Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.sw rs2', uimm(rs1') -- the compressed 4-byte store.                 *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_csw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (uimm : mword 5) (cr1 cr2 : mword 3) (rs1 rs2 : mword 5)
      (w_st va wval : mword 64) :
    uinstr pt M pc true (C_SW (uimm, Cregidx cr1, Cregidx cr2)) ->
    creg2reg_idx (Cregidx cr1) = Regidx rs1 ->
    creg2reg_idx (Cregidx cr2) = Regidx rs2 ->
    va = add_vec (m !!! Regidx rs1)
           (sign_extend' 64 (zero_extend' 12 (concat_vec uimm ('b"00")))) ->
    wval = m !!! Regidx rs2 ->
    ud_um pt !! svpn_of va = Some w_st ->
    uleaf_ok (Store Data) w_st ->
    uva_canon va ->
    Z.rem (uint va) 4096 <= 4092 ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    (forall j : nat, (j < 4)%nat -> exists bb : bv 8, M !! (uint va + Z.of_nat j) = Some bb) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ (uM_store M (uint va) 4 wval) m -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr1 Hcr2 Hva Hwval Hl Hchk Hcanon Hpg Hal HMb.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_store Ψ M m pc true (C_SW (uimm, Cregidx cr1, Cregidx cr2))
              (Some (STORE (zero_extend' 12 (concat_vec uimm ('b"00")),
                            Regidx rs2, Regidx rs1, 4)))
              (zero_extend' 12 (concat_vec uimm ('b"00")))
              rs1 rs2 4 w_st va wval
              ustore_width_4 Hui
              ltac:(intro s;
                    exact (exec_execute_C_SW_leaf uimm (Cregidx cr1) (Cregidx cr2)
                             (zero_extend' 12 (concat_vec uimm ('b"00")))
                             rs1 rs2 s eq_refl Hcr1 Hcr2))
              (fun s mb => goodmb_execute_C_SW_U Du_r Du_w uimm (Cregidx cr1)
                             (Cregidx cr2) s mb)
              eq_refl eq_refl
              Hva Hwval Hl Hchk Hcanon Hpg Hal HMb
              with "Hcg Hpc Hcont").
  Qed.

End WpUmodeStore.
