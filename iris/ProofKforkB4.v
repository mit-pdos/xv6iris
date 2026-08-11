(* ProofKforkB4.v -- kfork's idup / safestrcpy / pid-read stretch,
   +0xa4 .. +0xc0 (block ends at pc = +0xc2):

     +0xa4  ld a0,336(s5)          a0 := p->cwd
     +0xa8  jal ra,idup
     +0xac  sd a0,336(s4)          np->cwd := idup's result
     +0xb0  c.li a2,16             n := 16
     +0xb2  addi a1,s5,344         a1 := p->name
     +0xb6  addi a0,s4,344         a0 := np->name
     +0xba  jal ra,safestrcpy
     +0xbe  lw s1,48(s4)           s1 := np->pid  (THE RETURN VALUE)

   Interrupts are OFF throughout (the child's lock, taken by allocproc, is
   still held): every leaf and every callee's own [wp_next] collapses via
   [wp_next_off_intro] at the FIXED hart [CID0], so nothing here ever
   transports [cpu_own] or generates a fresh [CpuId].

   Straight line, two calls, no branches -- so this file never states
   [callee_saved] wrt the WHOLE FUNCTION's entry map, only wrt THIS block's
   own entry map [m].  [s1] is the one callee-saved register this block
   itself overwrites (with the child's pid); every other callee-saved
   register survives because idup and safestrcpy each promise their own
   [callee_saved] and neither touches [s1].

   THE RESOURCE STORY.  [p->cwd] names icache slot [ck] ([pv_cwd Vp = ientry
   ck], a premise of kfork's own contract because [ProcInv.cwd_ref] is [emp]
   and cannot produce idup's argument -- see SpecKfork.v's header).  idup
   hands back TWO halves of [inode_ref ck (cq/2) cdev cinum]; this block
   keeps one and drops the other (the child's [cwd_ref] is [emp], so there
   is nowhere to put it).  safestrcpy's precise characterisation of the
   child's new name bytes ([ssc_stop]/[ssc_post]) is dropped on the way out:
   kfork only needs the child's name array to be 16 bytes long again, not
   to know which bytes it holds, so the child's final block is handed back
   as an EXISTENTIAL [Vc'] agreeing with [Vc] on every field except [pv_cwd]
   (now [ientry ck]) and [pv_name] (now some list of length [PNAMELEN]).

   [ProcInv.v] has an accessor for [p->cwd] ([proc_priv_cwd]) but none for
   [p->name]; [kfk_name_open] below is the missing one, built by hand
   exactly the way [proc_priv_cwd] is (open [proc_fields], peel off
   [pname_cells], rebuild with the other six record fields carried
   through) -- see the header note on [kfk_name_open] for why a
   [ProcInv.proc_priv_name] accessor of this shape would be worth adding
   upstream. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import RegFile.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import FdSlots FileInv.
Require Import WpLock.
Require Import ProcInv.
Require Import InodeInv.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import SpecPanic.
Require Import SpecIdup.
Require Import SpecSafestrcpy.
Require Import ProofKforkParts.
Require Import CodeKfork.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal can carry a large [proc_priv]/[proc_pt_at]
   conjunction; durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KF := KernelSyms.kfork (only parsing).

(* ===================================================================== *)
(*  PURE HELPERS -- no [Σ], reusable regardless of the resource layer.    *)
(* ===================================================================== *)

(* [pprivate] is a plain record, so reassembling it from its own six
   projections is a no-op -- the [MkPPriv]-eta law every [upd_*] identity
   in this file reduces to. *)
Lemma pprivate_eta (V : pprivate) :
  MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (pv_ofile V) (pv_cwd V) (pv_name V) = V.
Proof. destruct V; reflexivity. Qed.

Lemma upd_cwd_id (V : pprivate) : upd_cwd V (pv_cwd V) = V.
Proof. rewrite /upd_cwd. apply pprivate_eta. Qed.

(* Turning a stored list into the [nat -> bv 8] naming function
   [SpecSafestrcpy.v]'s buffers are stated over, and back.  [default]'s
   fallback is never read: every use is guarded by [i < length bs]. *)
Definition kfk_name_fn (bs : list (bv 8)) : nat -> bv 8 :=
  fun i => default (bv_0 8) (bs !! i).

Lemma kfk_name_fn_spec (bs : list (bv 8)) (i : nat) :
  (i < length bs)%nat -> bs !! i = Some (kfk_name_fn bs i).
Proof.
  intro Hi. unfold kfk_name_fn.
  destruct (bs !! i) as [x |] eqn:E.
  - reflexivity.
  - exfalso. apply lookup_ge_None in E. lia.
Qed.

(* Stack budget: idup wants 14 below kfork's 8-slot frame, safestrcpy wants
   2.  Named lemmas over plain [nat], per durable-notes.md ("Cannot find
   witness" under the bitvector zify hook whenever a [bv_unsigned] is merely
   in context -- these have none, so plain [lia] is fine here). *)
Lemma kfk_b4_stack_idup (K : nat) : (22 <= K)%nat -> (14 <= K - 8)%nat.
Proof. lia. Qed.

Lemma kfk_b4_stack_ss (K : nat) : (22 <= K)%nat -> (2 <= K - 8)%nat.
Proof. lia. Qed.

(* The one-line bridge the brief calls for: [kfk_name_base] is stated over
   the bare 64-bit literal, while [addi a1,s5,344]'s leaf produces a
   sign-extended 12-bit one. *)
Lemma kfk_344_sext : (sign_extend' 64 (mword_of_int 344 : mword 12) : mword 64) = mword_of_int 344.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  THE MISSING ACCESSOR: [p->name], built exactly like [proc_priv_cwd].  *)
(* ===================================================================== *)
Section KforkB4Res.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* Worth adding to ProcInv.v as [proc_priv_name], next to [proc_priv_cwd]:
     same shape (open [proc_fields], hand out the one field, take back a
     REPLACEMENT of the same length), and every future name-writer (there is
     only kfork today) would want it. *)
  Lemma kfk_name_open (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) :
    proc_priv γf pa pid V -∗
    pname_cells pa (DfracOwn 1) (pv_name V) ∗
    ⌜length (pv_name V) = PNAMELEN⌝ ∗
    (∀ ns : list (bv 8), ⌜length ns = PNAMELEN⌝ -∗ pname_cells pa (DfracOwn 1) ns -∗
       proc_priv γf pa pid (MkPPriv (pv_sz V) (pv_upt V) (pv_tf V) (pv_ofile V) (pv_cwd V) ns)).
  Proof.
    iIntros "[(%Hszb & %Hbel & Hpid & Hf & Hpt & Htfp & Hc) Ho]".
    rewrite /proc_fields. iDestruct "Hf" as "(Hsz & Hcwd & %Hnl & Hnm)".
    iSplitL "Hnm"; [iExact "Hnm" |].
    iSplitR; [done |].
    iIntros (ns) "%Hnl' Hnm'".
    rewrite /proc_priv /proc_priv_core /proc_fields.
    cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd pv_name].
    iSplitR "Ho"; [| iExact "Ho"].
    iSplitR; [done|]. iSplitR; [done|]. iFrame "Hpid".
    iSplitL "Hsz Hcwd Hnm'".
    { iFrame "Hsz Hcwd Hnm'". iPureIntro. exact Hnl'. }
    iSplitL "Hpt"; [iExact "Hpt"|].
    iSplitL "Htfp"; [iExact "Htfp"|].
    iExact "Hc".
  Qed.

  (* THE CHILD'S OWN cwd REFERENCE, out of the reference idup MINTS.

     This is what the hole that used to sit here has become.  While
     [ProcInv.cwd_ref] was [emp] the child's reference could be conjured at
     any [v] and idup's result was dropped on the floor; now the two
     are the same predicate and the store at +0xac consumes it, which
     is the whole reason idup returns one.  No coherence premise is needed
     to tie the itable the caller holds the LOCK for to the authority
     [cwd_ref] is stated over: both are the same canonical
     [IcacheInv.iref_name] by construction ([InodeRef.v]'s header explains
     why). *)
  Lemma kfk_child_cwd (k : nat) (q : Qp) (inum : mword 32) :
    (k < NINODE)%nat ->
    bv_unsigned inum < 16 * Z.of_nat icfg_nib ->
    inode_ref k q icfg_dev inum -∗ cwd_ref (ientry k).
  Proof.
    iIntros (Hk Hinum) "Href". iApply cwd_ref_of_held.
    rewrite /inode_held. iExists k, q, inum. iFrame "Href".
    iSplitR; [done|]. iSplitR; [iPureIntro; exact Hk|].
    iPureIntro; exact Hinum.
  Qed.

End KforkB4Res.

(* ===================================================================== *)
(*  THE BLOCK ITSELF.                                                     *)
(* ===================================================================== *)
Module KforkB4 (ID : IDUP) (SS : SAFESTRCPY).

Section KforkB4Proof.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).

  Local Ltac regne :=
    first [ congruence
          | apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption] ].

  Lemma kfk_b4
      (γf γil γic : gname) (cn : ic_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (nib : nat)
      (pid_p pid_c : mword 32) (Vp Vc : pprivate)
      (pme npa : mword 64)
      (m : regfile) (K lvl : nat) (eb : bool) (C : iProp Σ) :
    (22 <= K)%nat ->
    (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
    (* the itable this block holds the lock for IS the one [cwd_ref] names,
       by construction: both are stated over the canonical
       [IcacheInv.iref_name].  This replaces the old [pv_cwd Vp = ientry ck]
       premise and the [inode_ref] that came with it: the parent's
       reference is inside its OWN block now, and the slot it names is read
       off it. *)
    m !!! Regidx Rs5 = pme ->
    m !!! Regidx Rs4 = npa ->
    (* THE PARENT HAS A WORKING DIRECTORY.  [ProcInv.cwd_ref] is two-armed
       on the pointer -- a process between [p->cwd = 0] and its next chdir
       owns no reference -- and xv6's fork does [np->cwd = idup(p->cwd)]
       with no null test, so this is the honest reading of the code. *)
    sie_cap_gpr m (K - 8)%nat false pme -∗
    cpu_own lvl eb pme C false -∗
    kernel_text -∗
    pc_is (mword_of_int (KF + 0xa4) : mword 64) -∗
    panic_wp_any -∗
    is_itable2 γil cn γfs γic cov logstart nib icfg_dev -∗
    itable_inv -∗
    (* the child's iref units: the [1] is what [idup] spends here, and
       [IREFSPARE] rides through to the park. *)
    iref_slots (1 + IREFSPARE) -∗
    proc_priv γf pme pid_p Vp -∗
    (* THE CHILD IS STILL IN THE CONSTRUCTION WINDOW: allocproc left
       [np->cwd] at 0 and nothing has set it, so there is no [proc_priv] at
       this [Vc].  The [sd a0,336(s4)] below is what closes the window. *)
    proc_priv_nocwd γf npa pid_c Vc -∗
    wp_next false pme (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜(forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
            mf !!! Regidx r = m !!! Regidx r) /\
         mf !!! Regidx Rs1 = sign_extend' 64 pid_c⌝ -∗
        sie_cap_gpr mf (K - 8)%nat false pme -∗
        cpu_own lvl eb pme C false -∗
        pc_is (mword_of_int (KF + 0xc2) : mword 64) -∗
        proc_priv γf pme pid_p Vp -∗
        (∃ Vc' : pprivate,
           ⌜pv_sz Vc' = pv_sz Vc /\ pv_upt Vc' = pv_upt Vc /\
            pv_tf Vc' = pv_tf Vc /\ pv_ofile Vc' = pv_ofile Vc /\
            pv_cwd Vc' = pv_cwd Vp /\ length (pv_name Vc') = PNAMELEN⌝ ∗
           proc_priv γf npa pid_c Vc') -∗
        iref_slots IREFSPARE -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlvl Hms5 Hms4.
    iIntros "Hcg Hown #Htext Hpc #Hpanic #Hitb #Hitinv Hir Hparent Hchild Hcont".
    iDestruct (iref_slots_split 1 IREFSPARE with "Hir") as "[Hirs Hirsp]".
    iPoseProof (kfk_0a4 with "Htext") as "Hi0a4".
    iPoseProof (kfk_0a8 with "Htext") as "Hi0a8".
    iPoseProof (kfk_0ac with "Htext") as "Hi0ac".
    iPoseProof (kfk_0b0 with "Htext") as "Hi0b0".
    iPoseProof (kfk_0b2 with "Htext") as "Hi0b2".
    iPoseProof (kfk_0b6 with "Htext") as "Hi0b6".
    iPoseProof (kfk_0ba with "Htext") as "Hi0ba".
    iPoseProof (kfk_0be with "Htext") as "Hi0be".
    (* ------------------------------------------------------------- *)
    (* +0xa4: ld a0,336(s5) -- a0 := p->cwd.                          *)
    (* ------------------------------------------------------------- *)
    (* THE PARENT'S OWN REFERENCE, out of its own block.  The slot index,
       the device and the inum come out with it -- [cwd_ref] hides them
       existentially and [IcacheInv.ientry_inj] is what makes hiding them
       lossless -- so [pv_cwd Vp = ientry ck] is now DERIVED here rather
       than premised on the caller. *)
    iDestruct (proc_priv_cwd γf pme pid_p Vp with "Hparent") as "(Hpcwd & Hpcref & Hpback)".
    (* the LIVE arm, picked out by the premise, and its three hidden data:
       the slot, the retained fraction and the inum.  The DEVICE is not
       hidden -- it is the cache's [icfg_dev] (design §13.11's
       single-device pin), which is what lets the itable this block holds
       the lock for be named without a coherence premise. *)
    iDestruct (cwd_ref_held (pv_cwd Vp) with "Hpcref") as "Hpcref".
    iDestruct "Hpcref" as (ck cq cinum) "(%Hcwd & %Hcklt & %Hcinumb & Hiref)".
    set (cdev := icfg_dev).
    (* THE PARENT SHEDS A SHARE (B3).  idup no longer takes a reference: it
       takes a count-0 share, hands it straight back and mints the child's
       reference from the table's retained slice (design §14.7(3)).  So the
       parent's own reference is never handed in and never halves -- it goes
       SHORT for the length of the call ([IcacheRef.inode_ref_shed], a pure
       resource split: no fupd, no invariant, no mask) and is made whole again
       by the gather below.
       IT CANNOT CLOSE ITS BLOCK ANY EARLIER THAN THAT, and that is what our
       algebra costs against the natR version this is ported from.  There
       [cwd_ref] could be re-formed from the reference the parent kept; here
       [cwd_ref] is [inode_held], which demands a CANONICAL pairing, and a
       short parent has none by construction -- being unspendable while a
       share is out is exactly what makes shares unable to outlive it. *)
    iEval (rewrite inode_ref_shed) in "Hiref".
    iDestruct "Hiref" as "[Hpkeep Hshr]".
    assert (Hpa0a4 : add_vec (rget m Rs5) (sign_extend' 64 (mword_of_int 336 : mword 12))
                     = p_cwd pme).
    { rewrite (rget_ne m Rs5 ltac:(vm_compute; discriminate)) Hms5. apply p_cwd_sext. }
    iEval (rewrite -Hpa0a4) in "Hpcwd".
    iApply (wp_ld_s_sconf (mword_of_int (KF + 0xa4)) Ra0 Rs5 (mword_of_int 336 : mword 12)
              m (K - 8)%nat (pv_cwd Vp) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a4 Hpcwd [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hpcwd".
    iEval (rewrite Hpa0a4) in "Hpcwd".
    (* the parent's block cannot close yet: its reference is on its way
       into idup.  It closes at [Hparent2] below, around idup's FIRST half
       -- the cell never changed, only the fraction, which [cwd_ref] hides. *)
    set (M0 := <[Regidx Ra0 := regval_into_reg (pv_cwd Vp)]> m).
    change (<[Regidx Ra0 := regval_into_reg (pv_cwd Vp)]> m) with M0.
    assert (HM0a0 : M0 !!! Regidx Ra0 = ientry ck) by (rewrite /M0 upd_eq; exact Hcwd).
    assert (HM0s4 : M0 !!! Regidx Rs4 = npa)
      by (rewrite /M0 upd_ne; [exact Hms4 | vm_compute; discriminate]).
    assert (HM0s5 : M0 !!! Regidx Rs5 = pme)
      by (rewrite /M0 upd_ne; [exact Hms5 | vm_compute; discriminate]).
    assert (Hpp0a8 : add_vec_int (mword_of_int (KF + 0xa4) : mword 64) 4 = mword_of_int (KF + 0xa8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a8) in "Hpc".
    (* ------------------------------------------------------------- *)
    (* +0xa8: jal ra,idup.                                            *)
    (* ------------------------------------------------------------- *)
    assert (Hjidup : add_vec (mword_of_int (KF + 0xa8) : mword 64)
                       (sign_extend' 64 (mword_of_int 5256 : mword 21))
                     = mword_of_int KernelSyms.idup)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xa8)) Rra (mword_of_int 5256 : mword 21)
              M0 (K - 8)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0a8 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hjidup) in "Hpc".
    set (M1 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xa8) : mword 64) 4)]> M0).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xa8) : mword 64) 4)]> M0)
      with M1.
    assert (HM1ra : M1 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xa8) : mword 64) 4)
      by (rewrite /M1; apply upd_eq).
    assert (HM1a0 : M1 !!! Regidx Ra0 = ientry ck)
      by (rewrite /M1 upd_ne; [exact HM0a0 | vm_compute; discriminate]).
    assert (HM1s4 : M1 !!! Regidx Rs4 = npa)
      by (rewrite /M1 upd_ne; [exact HM0s4 | vm_compute; discriminate]).
    assert (HM1s5 : M1 !!! Regidx Rs5 = pme)
      by (rewrite /M1 upd_ne; [exact HM0s5 | vm_compute; discriminate]).
    (* ------------------------------------------------------------- *)
    (* THE idup CALL.                                                 *)
    (* ------------------------------------------------------------- *)
    iApply (ID.wp_idup_sconf γil cn γfs γic cov logstart nib
              ck (cq/2)%Qp cdev cinum M1 lvl eb pme C (K - 8)%nat false
              (kfk_b4_stack_idup K HK) Hlvl Hcklt HM1a0
              with "Hcg Hown Htext Hpc Hitb Hitinv Hpanic Hirs Hshr [-]").
    iApply wp_next_off_intro.
    iIntros (mr) "Hcg Hown Hpc %Hidup_post Hshr (%qn & Href2)".
    (* THE GATHER: the share comes back at the fraction it left at (nothing
       in idup touches it), so it re-pairs with the short parent and the
       parent's block closes at the fraction it came in with -- no halving. *)
    iDestruct (inode_ref_gather ck (cq/2)%Qp (cq/2)%Qp cdev cinum
                 with "Hpkeep Hshr") as "Hiref".
    iEval (rewrite Qp.div_2) in "Hiref".
    iDestruct (kfk_child_cwd ck cq cinum Hcklt Hcinumb
                 with "Hiref") as "Hpcref1".
    iEval (rewrite -Hcwd) in "Hpcref1".
    iDestruct ("Hpback" $! (pv_cwd Vp) with "Hpcwd Hpcref1") as "Hparent2".
    iEval (rewrite upd_cwd_id) in "Hparent2".
    destruct Hidup_post as [Hcs_idup Hidup_a0].
    assert (Hpc0ac : ret_pc (M1 !!! Regidx Rra) = mword_of_int (KF + 0xac)).
    { rewrite HM1ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc0ac) in "Hpc".
    assert (Hmrs4 : mr !!! Regidx Rs4 = npa).
    { rewrite (callee_saved_lookup Hcs_idup Rs4 ltac:(vm_compute; reflexivity)). exact HM1s4. }
    assert (Hmrs5 : mr !!! Regidx Rs5 = pme).
    { rewrite (callee_saved_lookup Hcs_idup Rs5 ltac:(vm_compute; reflexivity)). exact HM1s5. }
    (* ------------------------------------------------------------- *)
    (* +0xac: sd a0,336(s4) -- np->cwd := a0 (= ientry ck).           *)
    (* ------------------------------------------------------------- *)
    iDestruct (proc_priv_nocwd_cwd γf npa pid_c Vc with "Hchild") as "(Hccwd & Hcback)".
    assert (Hpa0ac : add_vec (rget mr Rs4) (sign_extend' 64 (mword_of_int 336 : mword 12))
                     = p_cwd npa).
    { rewrite (rget_ne mr Rs4 ltac:(vm_compute; discriminate)) Hmrs4. apply p_cwd_sext. }
    iEval (rewrite -Hpa0ac) in "Hccwd".
    iApply (wp_sd_s_sconf (mword_of_int (KF + 0xac)) Ra0 Rs4 (mword_of_int 336 : mword 12)
              mr (K - 8)%nat (pv_cwd Vc) false
              with "Hcg Hpc Hi0ac Hccwd [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hccwd".
    iEval (rewrite Hpa0ac) in "Hccwd".
    assert (Hstoreval : rget mr Ra0 = ientry ck).
    { rewrite (rget_ne mr Ra0 ltac:(vm_compute; discriminate)). exact Hidup_a0. }
    iEval (rewrite Hstoreval) in "Hccwd".
    iDestruct (kfk_child_cwd ck qn cinum Hcklt Hcinumb
                 with "Href2") as "Hccref2".
    iDestruct ("Hcback" $! (ientry ck) with "Hccwd") as "Hchild2".
    (* THE WINDOW CLOSES HERE: cell + reference = the real block. *)
    iAssert (proc_priv γf npa pid_c (upd_cwd Vc (ientry ck))) with "[Hchild2 Hccref2]"
      as "Hchild2".
    { iApply proc_priv_split_cwd. iFrame "Hchild2".
      by cbn [upd_cwd pv_cwd]. }
    set (Vc2 := upd_cwd Vc (ientry ck)).
    (* the store touches no register *)
    set (M2 := mr).
    assert (HM2a1 : M2 !!! Regidx Ra1 = M2 !!! Regidx Ra1) by reflexivity.
    assert (Hpp0b0 : add_vec_int (mword_of_int (KF + 0xac) : mword 64) 4 = mword_of_int (KF + 0xb0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0b0) in "Hpc".
    (* ------------------------------------------------------------- *)
    (* +0xb0: c.li a2,16.                                             *)
    (* ------------------------------------------------------------- *)
    assert (Hwv16 : add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)))
                    = (mword_of_int 16 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cli_s_sconf (mword_of_int (KF + 0xb0)) Ra2 (mword_of_int 16 : mword 6)
              (mword_of_int 16 : mword 64) M2 (K - 8)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) Hwv16
              with "Hcg Hpc Hi0b0 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M3 := <[Regidx Ra2 := regval_into_reg (mword_of_int 16 : mword 64)]> M2).
    change (<[Regidx Ra2 := regval_into_reg (mword_of_int 16 : mword 64)]> M2) with M3.
    assert (HM3a2 : M3 !!! Regidx Ra2 = mword_of_int 16) by (rewrite /M3; apply upd_eq).
    assert (HM3s4 : M3 !!! Regidx Rs4 = npa)
      by (rewrite /M3 upd_ne; [exact Hmrs4 | vm_compute; discriminate]).
    assert (HM3s5 : M3 !!! Regidx Rs5 = pme)
      by (rewrite /M3 upd_ne; [exact Hmrs5 | vm_compute; discriminate]).
    assert (Hpp0b2 : add_vec_int (mword_of_int (KF + 0xb0) : mword 64) 2 = mword_of_int (KF + 0xb2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0b2) in "Hpc".
    (* ------------------------------------------------------------- *)
    (* +0xb2: addi a1,s5,344 -- a1 := p->name.                        *)
    (* ------------------------------------------------------------- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KF + 0xb2)) Ra1 Rs5 (mword_of_int 344 : mword 12)
              M3 (K - 8)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0b2 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M4 := <[Regidx Ra1 := regval_into_reg (add_vec (M3 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 344 : mword 12)))]> M3).
    change (<[Regidx Ra1 := regval_into_reg (add_vec (M3 !!! Regidx Rs5) (sign_extend' 64 (mword_of_int 344 : mword 12)))]> M3)
      with M4.
    assert (HM4a1 : M4 !!! Regidx Ra1 = kfk_name_base pme).
    { rewrite /M4 upd_eq HM3s5 kfk_344_sext. reflexivity. }
    assert (HM4s4 : M4 !!! Regidx Rs4 = npa)
      by (rewrite /M4 upd_ne; [exact HM3s4 | vm_compute; discriminate]).
    assert (HM4a2 : M4 !!! Regidx Ra2 = mword_of_int 16)
      by (rewrite /M4 upd_ne; [exact HM3a2 | vm_compute; discriminate]).
    assert (Hpp0b6 : add_vec_int (mword_of_int (KF + 0xb2) : mword 64) 4 = mword_of_int (KF + 0xb6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0b6) in "Hpc".
    (* ------------------------------------------------------------- *)
    (* +0xb6: addi a0,s4,344 -- a0 := np->name.                       *)
    (* ------------------------------------------------------------- *)
    iApply (wp_addi4_s_sconf (mword_of_int (KF + 0xb6)) Ra0 Rs4 (mword_of_int 344 : mword 12)
              M4 (K - 8)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0b6 [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (M5 := <[Regidx Ra0 := regval_into_reg (add_vec (M4 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 344 : mword 12)))]> M4).
    change (<[Regidx Ra0 := regval_into_reg (add_vec (M4 !!! Regidx Rs4) (sign_extend' 64 (mword_of_int 344 : mword 12)))]> M4)
      with M5.
    assert (HM5a0 : M5 !!! Regidx Ra0 = kfk_name_base npa).
    { rewrite /M5 upd_eq HM4s4 kfk_344_sext. reflexivity. }
    assert (HM5a1 : M5 !!! Regidx Ra1 = kfk_name_base pme)
      by (rewrite /M5 upd_ne; [exact HM4a1 | vm_compute; discriminate]).
    assert (HM5a2 : M5 !!! Regidx Ra2 = mword_of_int 16)
      by (rewrite /M5 upd_ne; [exact HM4a2 | vm_compute; discriminate]).
    assert (Hpp0ba : add_vec_int (mword_of_int (KF + 0xb6) : mword 64) 4 = mword_of_int (KF + 0xba))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0ba) in "Hpc".
    (* ------------------------------------------------------------- *)
    (* +0xba: jal ra,safestrcpy.                                      *)
    (* ------------------------------------------------------------- *)
    assert (Hjss : add_vec (mword_of_int (KF + 0xba) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093292 : mword 21))
                   = mword_of_int KernelSyms.safestrcpy)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_jal_s_sconf (mword_of_int (KF + 0xba)) Rra (mword_of_int 2093292 : mword 21)
              M5 (K - 8)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi0ba [-]").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hjss) in "Hpc".
    set (M6 := <[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xba) : mword 64) 4)]> M5).
    change (<[Regidx Rra := regval_into_reg (add_vec_int (mword_of_int (KF + 0xba) : mword 64) 4)]> M5)
      with M6.
    assert (HM6ra : M6 !!! Regidx Rra = add_vec_int (mword_of_int (KF + 0xba) : mword 64) 4)
      by (rewrite /M6; apply upd_eq).
    assert (HM6a0 : M6 !!! Regidx Ra0 = kfk_name_base npa)
      by (rewrite /M6 upd_ne; [exact HM5a0 | vm_compute; discriminate]).
    assert (HM6a1 : M6 !!! Regidx Ra1 = kfk_name_base pme)
      by (rewrite /M6 upd_ne; [exact HM5a1 | vm_compute; discriminate]).
    assert (HM6a2 : M6 !!! Regidx Ra2 = mword_of_int 16)
      by (rewrite /M6 upd_ne; [exact HM5a2 | vm_compute; discriminate]).
    assert (HM6s4 : M6 !!! Regidx Rs4 = npa)
      by (rewrite /M6 upd_ne; [exact HM4s4 | vm_compute; discriminate]).
    assert (HM6s5 : M6 !!! Regidx Rs5 = pme)
      by (rewrite /M6 upd_ne; [exact HM3s5 | vm_compute; discriminate]).
    (* open both name buffers *)
    iDestruct (kfk_name_open γf pme pid_p Vp with "Hparent2") as "(HnmP & %HnlP & HnmPback)".
    iDestruct (kfk_name_open γf npa pid_c Vc2 with "Hchild2") as "(HnmC & %HnlC & HnmCback)".
    iDestruct (kfk_pname_bytes pme (DfracOwn 1) (pv_name Vp) (kfk_name_fn (pv_name Vp))
                 (kfk_name_fn_spec (pv_name Vp)) with "HnmP") as "HnmPseq".
    iDestruct (kfk_pname_bytes npa (DfracOwn 1) (pv_name Vc2) (kfk_name_fn (pv_name Vc2))
                 (kfk_name_fn_spec (pv_name Vc2)) with "HnmC") as "HnmCseq".
    iEval (rewrite HnlP) in "HnmPseq".
    iEval (rewrite HnlC) in "HnmCseq".
    iEval (rewrite -HM6a1) in "HnmPseq".
    iEval (rewrite -HM6a0) in "HnmCseq".
    assert (HM6a2' : M6 !!! Regidx Ra2 = mword_of_int (Z.of_nat 16%nat))
      by (rewrite HM6a2; apply bv_eq; vm_compute; reflexivity).
    assert (Hn31 : (Z.of_nat 16%nat < 2 ^ 31)%Z) by (vm_compute; reflexivity).
    (* ------------------------------------------------------------- *)
    (* THE safestrcpy CALL.                                           *)
    (* ------------------------------------------------------------- *)
    iApply (SS.wp_safestrcpy_sconf M6 16%nat (kfk_name_fn (pv_name Vp)) (kfk_name_fn (pv_name Vc2))
              (K - 8)%nat (DfracOwn 1) false pme
              (kfk_b4_stack_ss K HK) HM6a2' Hn31
              with "Hcg Htext Hpc HnmPseq HnmCseq [-]").
    iApply wp_next_off_intro.
    iIntros (mr2 h) "Hcg Hpc HnmPseq' HnmCseq' %Hcs_ss %Ha0_ss %Hpostdisj".
    assert (Hpc0be : ret_pc (M6 !!! Regidx Rra) = mword_of_int (KF + 0xbe)).
    { rewrite HM6ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc0be) in "Hpc".
    assert (Hmr2s4 : mr2 !!! Regidx Rs4 = npa).
    { rewrite (callee_saved_lookup Hcs_ss Rs4 ltac:(vm_compute; reflexivity)). exact HM6s4. }
    assert (Hmr2s5 : mr2 !!! Regidx Rs5 = pme).
    { rewrite (callee_saved_lookup Hcs_ss Rs5 ltac:(vm_compute; reflexivity)). exact HM6s5. }
    (* re-fold the parent's name bytes back to EXACTLY [pv_name Vp] *)
    iEval (rewrite HM6a1) in "HnmPseq'".
    iDestruct (kfk_bytes_pname pme (DfracOwn 1) 16%nat (kfk_name_fn (pv_name Vp))
                 with "HnmPseq'") as "HnmPfold".
    assert (Hpname_eq : (kfk_name_fn (pv_name Vp)) <$> seq 0 16%nat = pv_name Vp).
    { pose proof (kfk_list_of_fn (pv_name Vp) (kfk_name_fn (pv_name Vp))
                    (kfk_name_fn_spec (pv_name Vp))) as Heq.
      rewrite HnlP in Heq. symmetry. exact Heq. }
    iEval (rewrite Hpname_eq) in "HnmPfold".
    iDestruct ("HnmPback" $! (pv_name Vp) HnlP with "HnmPfold") as "Hparent3".
    iEval (rewrite pprivate_eta) in "Hparent3".
    (* fold the child's new name bytes and close, at the EXISTENTIAL [Vc'] *)
    iEval (rewrite HM6a0) in "HnmCseq'".
    iDestruct (kfk_bytes_pname npa (DfracOwn 1) 16%nat h with "HnmCseq'") as "HnmCfold".
    assert (Hlen_hn : length (h <$> seq 0 16%nat) = PNAMELEN)
      by (rewrite (kfk_name_len 16%nat h); reflexivity).
    iDestruct ("HnmCback" $! (h <$> seq 0 16%nat) Hlen_hn with "HnmCfold") as "Hchild3".
    set (Vc3 := MkPPriv (pv_sz Vc2) (pv_upt Vc2) (pv_tf Vc2) (pv_ofile Vc2)
                  (pv_cwd Vc2) (h <$> seq 0 16%nat)).
    (* ------------------------------------------------------------- *)
    (* +0xbe: lw s1,48(s4) -- s1 := np->pid, THE RETURN VALUE.        *)
    (* ------------------------------------------------------------- *)
    iDestruct (proc_priv_pid γf npa pid_c Vc3 with "Hchild3") as "[Hcpid Hcpidback]".
    iApply (wp_lw_s_sconf (mword_of_int (KF + 0xbe)) Rs1 Rs4 (mword_of_int 48 : mword 12)
              mr2 (K - 8)%nat pid_c false (dqm := DfracOwn (1/4))
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0be [Hcpid] [-]").
    { iEval (rewrite (rget_ne mr2 Rs4 ltac:(vm_compute; discriminate)) Hmr2s4). iExact "Hcpid". }
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcpid".
    iEval (rewrite (rget_ne mr2 Rs4 ltac:(vm_compute; discriminate)) Hmr2s4) in "Hcpid".
    iDestruct ("Hcpidback" with "Hcpid") as "Hchild4".
    set (Mf := <[Regidx Rs1 := regval_into_reg (sign_extend' 64 pid_c)]> mr2).
    change (<[Regidx Rs1 := regval_into_reg (sign_extend' 64 pid_c)]> mr2) with Mf.
    assert (HMfs1 : Mf !!! Regidx Rs1 = sign_extend' 64 pid_c) by (rewrite /Mf; apply upd_eq).
    (* ------------------------------------------------------------- *)
    (* THE OVERALL callee-saved CHAIN, [m] -> [Mf], excluding [s1].   *)
    (* ------------------------------------------------------------- *)
    assert (HMfcs : forall r : mword 5, is_cs_idx r = true -> r <> Rs1 ->
                      Mf !!! Regidx r = m !!! Regidx r).
    { intros r Hr Hne.
      rewrite /Mf upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcs_ss r Hr).
      rewrite /M6 upd_ne; [| regne].
      rewrite /M5 upd_ne; [| regne].
      rewrite /M4 upd_ne; [| regne].
      rewrite /M3 upd_ne; [| regne].
      change (M2 !!! Regidx r) with (mr !!! Regidx r).
      rewrite (callee_saved_lookup Hcs_idup r Hr).
      rewrite /M1 upd_ne; [| regne].
      rewrite /M0 upd_ne; [| regne].
      reflexivity. }
    assert (Hpp0c2 : add_vec_int (mword_of_int (KF + 0xbe) : mword 64) 4 = mword_of_int (KF + 0xc2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c2) in "Hpc".
    (* ------------------------------------------------------------- *)
    (* Package the child's final block as the existential [Vc'].     *)
    (* ------------------------------------------------------------- *)
    iAssert (∃ Vc' : pprivate,
               ⌜pv_sz Vc' = pv_sz Vc /\ pv_upt Vc' = pv_upt Vc /\
                pv_tf Vc' = pv_tf Vc /\ pv_ofile Vc' = pv_ofile Vc /\
                pv_cwd Vc' = pv_cwd Vp /\ length (pv_name Vc') = PNAMELEN⌝ ∗
               proc_priv γf npa pid_c Vc')%I
      with "[Hchild4]" as "HchildFinal".
    { iExists Vc3.
      iSplitR.
      - iPureIntro. rewrite /Vc3 /Vc2 /upd_cwd. cbn [pv_sz pv_upt pv_tf pv_ofile pv_cwd].
        rewrite Hcwd. repeat split; reflexivity.
      - iExact "Hchild4". }
    iSpecialize ("Hcont" $! CID0 with "[%]"); [intros _; reflexivity |].
    iApply ("Hcont" $! Mf with "[%] Hcg Hown Hpc Hparent3 HchildFinal Hirsp").
    exact (conj HMfcs HMfs1).
  Qed.

End KforkB4Proof.

End KforkB4.
