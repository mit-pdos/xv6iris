(* ProofCreateFreshTy.v -- create's FRESH-TYPE SPAN.
   ==================================================================

   WHAT THE STATEMENT IS.  A SPAN, not a fact: the four instructions
   create+0xa4 .. +0xb0

     +0xa4  c.mv   a1,s4          a1 := type
     +0xa6  lw     a0,0(s1)       a0 := dp->dev
     +0xa8  jal    ialloc         <- [wp_ialloc_gen] is a HYPOTHESIS
     +0xac  c.mv   s3,a0          s3 := ip
     +0xae  c.beqz a0 -> +0xec    [ARM A-FAIL]
     +0xb0  jal    ilock          <- [wp_ilock_sconf] is a HYPOTHESIS

   delivering control at +0xb4 (allocated) or +0xec (A-FAIL), with
   [di_type dn = ty] on the first.  It has to be a span and not a fact
   because [ty] is a MACHINE WORD -- the halfword in s4 -- and a bare
   entailment over free [ty] and [dn] is INCONSISTENT (two instantiations
   at different types derive False).

   WHERE THE TYPE EQUATION COMES FROM.  fs-icache.md 20.7 asks for "a
   carrier for: no free-and-reclaim since my claim".  The c column IS that
   carrier, once it is TYPED:

     * [IcacheRef.iclaim z ty] is minted by [InodeRegion.ireg_claim_au] at
       the type ialloc wrote, and the region's claim pin says a claimed
       slot's record still has it ([ireg_claim_ok]'s third conjunct);
     * a claimed slot's record is INSIDE the region
       ([InodeRegion.ireg_claim_no_out]: [c <> None] refutes the MARKED arm,
       and the other two arms park the fragment), so NOBODY holds its
       [dinode_at] -- which kills both of ilock's non-fill routes (the
       cached arm, and the pool's allocated bundle) and FORCES 16.4's
       claim-box fill;
     * the fill's [InodeRegion.ireg_withdraw] spends the claim and pays the
       type equation back.

   So [wp_ilock_sconf] at [InodeRegion.ClaimK ty] returns
   [filled = true /\ di_type dn = ty] as a THEOREM, and this span is that
   theorem plus four instructions of register bookkeeping.

   IT HIDES NEITHER CALLEE.  [wp_ialloc_gen] and [wp_ilock_sconf] are
   HYPOTHESES of [create_fresh_ty], supplied by [ProofCreate] out of its own
   [IA]/[IL] functor arguments, so a wrong ialloc or a wrong ilock is not
   covered.

   IT IS A PROOF FILE, NOT A LINK FILE.  The span is a stretch of create's
   OWN body, not a callee, so it is neither a module type nor a functor
   argument of [CreateProof]: [ProofCreate] requires this file and applies
   [create_fresh_ty] directly (design/spec-modules.md's shape is for
   callees).  Statement and proof sit in their own file only to keep
   [ProofCreate.v] from carrying another 600 lines; [create_fresh_ty_body]
   is therefore stated here and spliced from there VERBATIM. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import KernelText KernelDataInv.
Require Import CalleeSaved.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfBtype WpSconfCtl.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcGeom.
Require Import SleepLock.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
(* THE PAYLOAD'S OWN VOCABULARY (durable-disk 2b-inode-3): [top_frag],
   [fs_gamma_L], [era_node] / [inode_rec_local].  IMPORTED BEFORE
   [FsBlocks] on purpose -- the [FsState*] stack exports [fs_view] and
   [byte_range], both of which have live twins below, and the LAST import
   wins (durable-notes, "AND WHERE THAT IMPORT COLLIDES, PUT IT EARLY"). *)
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DinodeEnc.
(* [trunc16_sext64]: an [sh] of a register an [lh] filled is the identity on
   the halfword -- the three metadata stores at +0xb4 / +0xb8 are exactly
   that, at the ABI's sign-extended [major] / [minor] arguments. *)
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import FdSlots.
Require Import ProcInv.
Require Import SpecPrintk.
Require Import SpecIalloc.
Require Import SpecIlock.
Require Import CodeCreate.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import ProcDefs.  (* [pprivate], [proc_priv_bare] *)
Require Import TsoCtx.
Import Defs.

Local Open Scope Z_scope.

Local Notation CK := KernelSyms.create (only parsing).

(* THE SEAM'S REGISTER CONTRACT.  [callee_saved] is FALSE across the span --
   the [c.mv s3,a0] at +0xac is the point of it -- so what the span promises
   is [callee_saved] EVERYWHERE BUT s3, with s3's own value reported per
   arm.  Both callees restore sp and s0, so the exception list is exactly
   the one register the span writes, and the predicate is stated
   POSITIVELY-BY-ONE-EXCEPTION rather than over a set the reader has to go
   and look up (durable-notes' rule; here the set IS the singleton). *)
Definition cr_cs_but_s3 (m mf : regfile) : Prop :=
  forall c : mword 5,
    is_cs_idx c = true -> c <> (mword_of_int 19 : mword 5) ->
    mf !!! Regidx c = (m !!! Regidx c : mword 64).

Definition create_fresh_ty_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}

    (γs : list gname) (j : nat) (γl : gname)
    (γu : uart_names) (γd : disk_names) (γk : gname)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names) (γi : gname)
    (cn : ic_names) (gtl : gname) (γpr : gname)
    (cov : gset Z) (logstart inodestart : Z) (ninodes : Z) (nib : nat)
    (dev : mword 32) (ty : mword 16)
    (kd : nat) (dqp : dfrac)                     (* the LOCKED PARENT's slot *)
    (u : nat) (Sb : gset Z)
    (pidv : mword 32) (dq dqs dqn : dfrac)
    (Ma : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) : Prop :=
  let pj := proc_addr j in
  (* ---- ialloc's and ilock's own geometry, verbatim ---- *)
  (K_ialloc <= K)%nat ->
  (K_ilock <= K)%nat ->
  log_geom_ok cov logstart ->
  0 <= inodestart ->
  InodeInv.ireg_blocks_ok inodestart nib cov logstart ->
  1 < ninodes ->
  ninodes <= 16 * Z.of_nat nib ->
  ninodes < 2 ^ 31 ->
  bv_unsigned ty <> 0 ->
  (* durable-disk 2b-inode-3: ialloc's claim box owes the region (L5) *)
  InodeRegion.ireg_ty_ok (ialloc_fresh ty) ->
  printk_gen_contract (kt := KT1) γpr γu γd ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  dev = ROOTDEV ->
  (* ---- THE PINNING PREMISE.  [ty] is the halfword in s4, which is what
     makes this statement consistent: at two different [ty] these two
     equations cannot both hold.  See the header. ---- *)
  Ma !!! Regidx (mword_of_int 20 : mword 5) = (sign_extend' 64 ty : mword 64) ->
  (* s1 = dp, whose [dev] word the [lw] at +0xa6 reads *)
  Ma !!! Regidx (mword_of_int 9 : mword 5) = ientry kd ->
  (kd < NINODE)%nat ->
  (* PARKING PREMISE *)
  eb = true ->
  (* the span's cone is ialloc ("log", 1) and ilock ("bcache", 2, and the
     inode sleeplock above it); "log" is the lower, so one premise there
     covers both via [locks_below_mono]. *)
  locks_below lks "log" ->
  (* ---- THE TWO REAL CONTRACTS, AS HYPOTHESES.  This is what keeps
     [ProofIalloc] and [ProofIlock] load-bearing: the axiom below assumes
     nothing about either function, only about the record identity across
     the two calls. ---- *)
  (forall `{CIDa : CpuId} `{XI : CurCtx}
     (γs' : list gname) (j' : nat) (γl' : gname)
     (γu' : uart_names) (γd' : disk_names) (γk' : gname)
     (pd' pav' pu' : mword 64) (bn' : bio_names)
     (γ' : log_names) (γfs' : fs_names) (γi' : gname)
     (cn' : ic_names) (gtl' : gname) (γpr' : gname)
     (cov' : gset Z) (logstart' inodestart' ninodes' : Z) (nib' : nat)
     (dev' : mword 32) (ty' : mword 16) (u' : nat) (Sb' : gset Z)
     (pidv' : mword 32) (dq' dqs' dqn' : dfrac)
     (m' : regfile) (K' : nat) (eb' : bool) (b' : bool)
     (lks' : gset string) (Vpr' : pprivate),
     wp_ialloc_gen_body (CID := CIDa) γs' j' γl' γu' γd' γk' pd' pav' pu' bn'
                        γ' γfs' γi' cn' gtl' γpr' cov' logstart' inodestart'
                        ninodes' nib' dev' ty' u' Sb' pidv' dq' dqs' dqn'
                        m' K' eb' b' lks' Vpr') ->
  (forall `{CIDl : CpuId} `{XI : CurCtx}
     (γs' : list gname) (j' : nat) (γl' : gname)
     (γu' : uart_names) (γd' : disk_names) (γk' : gname)
     (pd' pav' pu' : mword 64) (bn' : bio_names)
     (γfs' : fs_names) (γi' : gname) (cn' : ic_names) (gil' gisl' : gname)
     (cov' : gset Z) (logstart' inodestart' : Z) (nib' : nat)
     (k' : nat) (s' : Qp) (g' : gname) (o' : ilkc) (dev' inum' : mword 32)
     (pidv' : mword 32) (dq' dqs' : dfrac)
     (m' : regfile) (K' : nat) (eb' : bool) (b' : bool)
     (lks' : gset string) (Vpr' : pprivate),
     wp_ilock_sconf_body (CID := CIDl) γs' j' γl' γu' γd' γk' pd' pav' pu' bn'
                         γfs' γi' cn' gil' gisl' cov' logstart' inodestart'
                         nib' k' s' g' o' dev' inum' pidv' dq' dqs'
                         m' K' eb' b' lks' Vpr') ->
  (* ================= THE SPAN ================= *)
  sie_cap_gpr KT1 Ma K b pj -∗
  cpu_own 0 eb pj b lks -∗
  kernel_text -∗ pc_is (mword_of_int (KernelSyms.create + 0xa4) : mword 64) -∗
  kernel_data -∗
  printk_env γpr γu γd -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  is_itable2 gtl cn γfs γi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn γfs γi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv γi γfs inodestart nib -∗
  (* ...AND THE SEALED REGIME (iclaim-ledger.md §3.2, RULING B).  The span
     covers [jal ialloc] at +0xa8, and [wp_ialloc_gen_body] -- the
     HYPOTHESIS this axiom takes for that callee -- now asks for it (via
     [InodeRegion.ireg_claim_au], the one [c]-column mover).  Persistent, so
     the span borrows it and hands nothing back. *)
  ireg_open -∗
  procs_inv γs -∗
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  proc_priv_bare pj pidv Vpr -∗
  bslots 3 -∗
  iref_slot -∗
  (* THE PARENT'S OWN [dev] CELL: the [lw a0,0(s1)] at +0xa6 reads it, and
     it comes straight back.  It is the only piece of the locked parent the
     span touches. *)
  i_dev (ientry kd) ↦₄{dqp} dev -∗
  log_opS γ (S u) Sb -∗
  wp_next true pj (fun (CIDo : CpuId) =>
  ∀ (Mo : regfile) (alloc : bool)
    (kslot : nat) (q : Qp) (g : gname) (inum : mword 32)
    (gil gisl : gname) (dn : dinode) (bm : blkmap),
      ⌜cr_cs_but_s3 Ma Mo⌝ -∗
      sie_cap_gpr KT1 Mo K b pj -∗
      cpu_own 0 eb pj b lks -∗
      sb_ninodes ↦₄{dqn} (mword_of_int ninodes : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      proc_priv_bare pj pidv Vpr -∗
      bslots 3 -∗
      i_dev (ientry kd) ↦₄{dqp} dev -∗
      (if alloc
       then
         (* ---- CONTROL IS AT +0xb4, THE INODE IS LOCKED AND FILLED ---- *)
         ⌜Mo !!! Regidx (mword_of_int 19 : mword 5) = ientry kslot
          /\ (kslot < NINODE)%nat
          /\ 0 < bv_unsigned inum < ninodes
          /\ bv_unsigned inum < 16 * Z.of_nat nib
          (* THE ONE ASSUMED FACT.  Everything else in this arm is
             [wp_ialloc_gen]'s or [wp_ilock_sconf]'s own postcondition. *)
          /\ di_type dn = ty
          (* ...and this is ILOCK's, at the [filled] the line above pins:
             NOT assumed -- see the header. *)
          /\ fresh_shape dn⌝ ∗
         pc_is (mword_of_int (KernelSyms.create + 0xb4) : mword 64) ∗
         is_sleeplock_gen gil gisl (i_lock (ientry kslot)) "inode"%string
                          (ic_tok cn kslot) (slh_tok (icfg_isl kslot)) ∗
         sleeplocked_q gisl (q/2)%Qp (i_lock (ientry kslot)) pidv ∗
         ic_deposit cn kslot (DepShr (q/2)%Qp dev inum g) ∗
         i_dev (ientry kslot) ↦₄{DfracOwn (1/2)} dev ∗
         i_inum (ientry kslot) ↦₄{DfracOwn (1/2)} inum ∗
         i_valid (ientry kslot) ↦₄ valid_word true ∗
         ic_loaded γfs γi cov logstart kslot inum dn bm ∗
         ity_shot g (di_type dn) ∗
         (* ...AND THE INUM'S FREEZE TOKEN (iclaim-ledger.md §3.9, RULING
            A-prime).  The span ends at [ilock]'s return, and [SpecIlock]'s
            post now hands the holder [ifreeze_off] beside the payload
            ([IcacheEscrow.ic_payload]'s A-custody conjunct) -- so this is
            not new content, it is the callee's own postcondition relayed,
            exactly as [ic_loaded] and [ity_shot] above are.

            WHO WANTS IT: create's [ip->nlink = 1; iupdate(ip)] at +0xc4.
            The freeze pin's premise on [wp_iupdate_link] is FALSE at the
            fresh child (its pre-count is zero by [fresh_shape]), so the
            walk pays the TOKEN arm; the token is borrowed by the mover and
            comes straight back, and create returns it at the child's
            iunlock. *)
         ifreeze_off (bv_unsigned inum) ∗
         inode_ref_short_gen kslot (q/2 + q/2)%Qp (q/2)%Qp dev inum g ∗
         (* ...AND ITS PROVENANCE UNIT (item 7a-wire, iclaim-ledger.md
            §5''.3): ialloc's [ClaimL] iget minted it, and the iunlockput
            that closes the child spends it. *)
         runit_any (bv_unsigned inum) ∗
         (* ialloc's [ia_spend = 1], and the membership create's own
            [iupdate(ip)] and every [dirlink] on [ip] credit against *)
         log_opS γ u (Sb ∪ {[IBLOCK inum inodestart]})
       else
         (* ---- CONTROL IS AT +0xec, ARM A-FAIL: nothing was claimed ---- *)
         ⌜Mo !!! Regidx (mword_of_int 19 : mword 5)
          = (mword_of_int 0 : mword 64)⌝ ∗
         pc_is (mword_of_int (KernelSyms.create + 0xec) : mword 64) ∗
         iref_slot ∗
         log_opS γ (S u) Sb) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).



(* ===================================================================== *)
(*  THE PROOF                                                            *)
(* ===================================================================== *)

(* "a callee-saved index is not a caller-saved one", in the [Regidx] form
   [RegFile.upd_ne] wants. *)
Lemma cft_cs_ne (c r : mword 5) :
  is_cs_idx c = true -> is_cs_idx r = false -> Regidx c <> Regidx r.
Proof.
  intros Hc Hr Hcon. assert (Hcr : c = r) by congruence.
  rewrite Hcr Hr in Hc. discriminate.
Qed.

(* an entry address is never zero -- [ProofIget.ig_entry_nonzero]'s four
   lines, restated here so this file requires no [Proof*]. *)
Lemma cft_entry_nonzero (e : nat) :
  (e <= NINODE)%nat -> eq_vec (ientry e) (zero_reg : mword 64) = false.
Proof.
  intros He. apply eq_vec_false_iff. intro Hc.
  apply (f_equal (@bv_unsigned 64)) in Hc.
  rewrite (ientry_unsigned e He) in Hc.
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0)
    by (vm_compute; reflexivity).
  rewrite Hz in Hc. unfold ISLOTSZ, KernelSyms.itable in Hc. lia.
Qed.

Section CftHelpers.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  (* the escrow-family accessor and the slot split.  The sleeplock family's
     accessor is [IcacheEscrow.ic_sleeplocks_lookup], beside the definition. *)
  Lemma cft_esc_acc (cn : ic_names) (γfs : fs_names) (γi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) :
    (k < NINODE)%nat ->
    (ic_escrows cn γfs γi cov logstart -∗ ic_escrow cn γfs γi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma cft_bs3 :
    (bslots 3 : iProp Σ) ⊣⊢ bslot ∗ bslots 2.
  Proof. rewrite /bslot. change 3%nat with (1 + 2)%nat. apply bslots_op. Qed.
End CftHelpers.

Section CreateFreshTySpan.


Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).

Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
Local Ltac nz := vm_compute; discriminate.

Lemma create_fresh_ty :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ,
             ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names) (γi : gname)
      (cn : ic_names) (gtl : gname) (γpr : gname)
      (cov : gset Z) (logstart inodestart : Z) (ninodes : Z) (nib : nat)
      (dev : mword 32) (ty : mword 16)
      (kd : nat) (dqp : dfrac)
      (u : nat) (Sb : gset Z)
      (pidv : mword 32) (dq dqs dqn : dfrac)
      (Ma : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      create_fresh_ty_body γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr
                           cov logstart inodestart ninodes nib dev ty kd dqp
                           u Sb pidv dq dqs dqn Ma K eb b lks Vpr.
Proof.
  intros.
  cbv beta delta [create_fresh_ty_body]. cbv zeta.
  intros HKia HKil Hlg Hist Hiregb Hn1 Hn2 Hn3 Htynz Htyk Hpkc Hj Hgs Hdevr
         HAs4 HAs1 Hkdlt Heb Hbelow Hia Hil.
  iIntros "Hcg Hcnt #Htext Hpc #Hkd #Hpk #Hbio #Hlogc #Hitb2 #Hitbl #Hesc
           #Hslks #Hireg #Hiopen #Hprocs #Hdevi #Hdgeom #Hdlk Hsbn Hsbi
           Hppid Hbsl Hisl Hidev Hop Hcont".
  iPoseProof (printk_env_panic with "Hpk") as "#Hpenv".
  iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
  assert (Hb : b = true) by (rewrite -Hbm; exact Heb). clear Hbm.
  assert (Hcsra : is_cs_idx Rra = false) by (vm_compute; reflexivity).
  assert (Hcsa0 : is_cs_idx Ra0 = false) by (vm_compute; reflexivity).
  assert (Hcsa1 : is_cs_idx Ra1 = false) by (vm_compute; reflexivity).
  (* ===== +0xa4  c.mv a1,s4 : a1 := type ============================= *)
  iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xa4)) Ra1 Rs4 Ma K b
            ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
  { iApply (cri_0a4 with "Htext"). }
  iIntros (CID1 Hq1) "Hcg Hpc". iEval (rgne) in "Hcg".
  pose (A1 := <[Regidx Ra1 := regval_into_reg
                 (add_vec (zero_reg : mword 64) (Ma !!! Regidx Rs4))]> Ma).
  change (<[Regidx Ra1 := regval_into_reg
              (add_vec (zero_reg : mword 64) (Ma !!! Regidx Rs4))]> Ma) with A1.
  assert (HA1a1 : A1 !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64)).
  { rewrite /A1 upd_eq HAs4. apply add_vec_zero_l. }
  assert (HA1s1 : A1 !!! Regidx Rs1 = ientry kd)
    by (rewrite /A1 upd_ne; [exact HAs1 | nz]).
  assert (Hpp0a6 : add_vec_int (mword_of_int (CK + 0xa4) : mword 64) 2
                   = mword_of_int (CK + 0xa6)) by pcw.
  iEval (rewrite Hpp0a6) in "Hpc".
  (* ===== +0xa6  lw a0,0(s1) : a0 := dp->dev ========================= *)
  assert (Hdevadr : add_vec (rget A1 Rs1)
                      (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = i_dev (ientry kd)).
  { rewrite (rget_ne A1 Rs1 ltac:(nz)) HA1s1. reflexivity. }
  iEval (rewrite -Hdevadr) in "Hidev".
  iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0)
            (mword_of_int (CK + 0xa6)) Ra0 Rs1
            (mword_of_int 0 : mword 12) A1 K dev b (dqm := dqp)
            ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hidev").
  { iApply (cri_0a6 with "Htext"). }
  iIntros (CID2 Hq2) "Hcg Hpc Hidev".
  iEval (rewrite Hdevadr) in "Hidev".
  pose (A2 := <[Regidx Ra0 := regval_into_reg
                 (sign_extend' 64 (dev : mword 32))]> A1).
  change (<[Regidx Ra0 := regval_into_reg
              (sign_extend' 64 (dev : mword 32))]> A1) with A2.
  assert (HA2a0 : A2 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
    by (rewrite /A2; apply upd_eq).
  assert (HA2a1 : A2 !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64))
    by (rewrite /A2 upd_ne; [exact HA1a1 | nz]).
  assert (Hpp0a8 : add_vec_int (mword_of_int (CK + 0xa6) : mword 64) 2
                   = mword_of_int (CK + 0xa8)) by pcw.
  iEval (rewrite Hpp0a8) in "Hpc".
  (* ===== +0xa8  jal ialloc ========================================== *)
  assert (Htgia : add_vec (mword_of_int (CK + 0xa8) : mword 64)
                    (sign_extend' 64 (mword_of_int 2090038 : mword 21))
                  = mword_of_int KernelSyms.ialloc) by pcw.
  iApply (wp_jal_s_sconf (mword_of_int (CK + 0xa8)) Rra
            (mword_of_int 2090038 : mword 21) A2 K b
            ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
            with "Hcg Hpc []").
  { iApply (cri_0a8 with "Htext"). }
  iIntros (CID3 Hq3) "Hcg Hpc".
  iEval (rewrite Htgia) in "Hpc".
  pose (A3 := <[Regidx Rra := regval_into_reg
                 (add_vec_int (mword_of_int (CK + 0xa8) : mword 64) 4)]> A2).
  change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (CK + 0xa8) : mword 64) 4)]> A2) with A3.
  assert (HA3ra : A3 !!! Regidx Rra
                  = add_vec_int (mword_of_int (CK + 0xa8) : mword 64) 4)
    by (rewrite /A3; apply upd_eq).
  assert (HA3a0 : A3 !!! Regidx Ra0 = (sign_extend' 64 dev : mword 64))
    by (rewrite /A3 upd_ne; [exact HA2a0 | nz]).
  assert (HA3a1 : A3 !!! Regidx Ra1 = (sign_extend' 64 ty : mword 64))
    by (rewrite /A3 upd_ne; [exact HA2a1 | nz]).
  assert (HA3cs : forall c : mword 5, is_cs_idx c = true ->
                    A3 !!! Regidx c = (Ma !!! Regidx c : mword 64)).
  { intros c Hc.
    rewrite /A3 upd_ne; [| exact (cft_cs_ne c Rra Hc Hcsra)].
    rewrite /A2 upd_ne; [| exact (cft_cs_ne c Ra0 Hc Hcsa0)].
    rewrite /A1 upd_ne; [| exact (cft_cs_ne c Ra1 Hc Hcsa1)].
    reflexivity. }
  assert (Hpcac : ret_pc (A3 !!! Regidx Rra : mword 64)
                  = mword_of_int (CK + 0xac)) by (rewrite HA3ra; pcw).
  iDestruct (cft_bs3 with "Hbsl") as "[Hbs1 Hbs2]".
  iDestruct (cpu_own_transport CID CID3 0%nat eb (proc_addr j) b
               ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
  iApply (Hia CID3 XI γs j γl γu γd γk pd pav pu bn γ γfs γi cn gtl γpr cov logstart
            inodestart ninodes nib dev ty u Sb pidv dq dqs dqn A3 K eb b lks Vpr
            HKia Hlg Hist Hiregb Hn1 Hn2 Hn3 Htynz Htyk Hpkc Hj Hgs HA3a0 HA3a1 Heb
            Hbelow
            with "Hcg Hcnt Htext Hpc Hkd Hpk Hbio Hlogc Hsbn Hsbi Hireg Hiopen
                  Hppid Hprocs Hdevi Hdgeom Hdlk Hbs2 Hitb2 Hitbl Hesc Hisl Hop").
  iIntros (CID4 Hq4 Mi alloc kslot q inum dn')
    "%Hcsi Hcg Hcnt Hpc Hsbn Hsbi Hppid Hbs2 Hres".
  iEval (rewrite Hpcac) in "Hpc".
  (* ===== +0xac  c.mv s3,a0 : s3 := ip =============================== *)
  iApply (wp_cmv_s_sconf (mword_of_int (CK + 0xac)) Rs3 Ra0 Mi K b
            ltac:(nz) ltac:(rdok) with "Hcg Hpc []").
  { iApply (cri_0ac with "Htext"). }
  iIntros (CID5 Hq5) "Hcg Hpc". iEval (rgne) in "Hcg".
  pose (F1 := <[Regidx Rs3 := regval_into_reg
                 (add_vec (zero_reg : mword 64) (Mi !!! Regidx Ra0))]> Mi).
  change (<[Regidx Rs3 := regval_into_reg
              (add_vec (zero_reg : mword 64) (Mi !!! Regidx Ra0))]> Mi) with F1.
  assert (HF1a0 : F1 !!! Regidx Ra0 = (Mi !!! Regidx Ra0 : mword 64))
    by (rewrite /F1 upd_ne; [reflexivity | nz]).
  assert (HF1cs : forall c : mword 5, is_cs_idx c = true ->
                    c <> Rs3 -> F1 !!! Regidx c = (Mi !!! Regidx c : mword 64)).
  { intros c Hc Hne. rewrite /F1 upd_ne;
      [ reflexivity | intros Hcon; apply Hne; congruence ]. }
  assert (Hpp0ae : add_vec_int (mword_of_int (CK + 0xac) : mword 64) 2
                   = mword_of_int (CK + 0xae)) by pcw.
  iEval (rewrite Hpp0ae) in "Hpc".
  destruct alloc.
  - (* ============================================================== *)
    (*  ALLOCATED: a0 = ientry kslot, the branch FALLS THROUGH        *)
    (* ============================================================== *)
    (* SIMP-2: ialloc's receipt is ONE row now ([IcacheRef.inode_claimed]). *)
    iDestruct "Hres" as "(%Hpure & Hpkg & Hop)".
    destruct Hpure as (Hia0 & Hkslt & Hinpos & Hinb & Hdn'eq & Hdn'ty & Hdn'fr).
    destruct (Hiregb inum Hinb) as [Hcblk Hcblog].
    (* +0xae c.beqz a0 : NOT taken -- an entry address is never zero *)
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (CK + 0xae))
              (mword_of_int 31 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              F1 K b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rewrite (rget_ne F1 Ra0 ltac:(nz)) HF1a0 Hia0;
                    apply cft_entry_nonzero; unfold NINODE in *; lia)
              with "Hcg Hpc []").
    { iApply (cri_0ae with "Htext"). }
    iIntros (CID6 Hq6) "Hcg Hpc".
    assert (Hpp0b0 : add_vec_int (mword_of_int (CK + 0xae) : mword 64) 2
                     = mword_of_int (CK + 0xb0)) by pcw.
    iEval (rewrite Hpp0b0) in "Hpc".
    (* ===== +0xb0  jal ilock ======================================== *)
    assert (Htgil : add_vec (mword_of_int (CK + 0xb0) : mword 64)
                      (sign_extend' 64 (mword_of_int 2090398 : mword 21))
                    = mword_of_int KernelSyms.ilock) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (CK + 0xb0)) Rra
              (mword_of_int 2090398 : mword 21) F1 K b
              ltac:(nz) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_0b0 with "Htext"). }
    iIntros (CID7 Hq7) "Hcg Hpc".
    iEval (rewrite Htgil) in "Hpc".
    pose (B1 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (CK + 0xb0) : mword 64) 4)]> F1).
    change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (CK + 0xb0) : mword 64) 4)]> F1) with B1.
    assert (HB1ra : B1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (CK + 0xb0) : mword 64) 4)
      by (rewrite /B1; apply upd_eq).
    assert (HB1a0 : B1 !!! Regidx Ra0 = ientry kslot).
    { rewrite /B1 upd_ne; [| nz]. rewrite HF1a0. exact Hia0. }
    assert (HB1s3 : B1 !!! Regidx Rs3 = ientry kslot).
    { rewrite /B1 upd_ne; [| nz]. rewrite /F1 upd_eq Hia0.
      apply add_vec_zero_l. }
    assert (HB1cs : forall c : mword 5, is_cs_idx c = true ->
                      c <> Rs3 -> B1 !!! Regidx c = (Mi !!! Regidx c : mword 64)).
    { intros c Hc Hne. rewrite /B1 upd_ne;
        [ exact (HF1cs c Hc Hne) | exact (cft_cs_ne c Rra Hc Hcsra) ]. }
    assert (Hpcb4 : ret_pc (B1 !!! Regidx Rra : mword 64)
                    = mword_of_int (CK + 0xb4)) by (rewrite HB1ra; pcw).
    iDestruct (cft_esc_acc cn γfs γi cov logstart kslot Hkslt with "Hesc")
      as "#Hescc".
    iDestruct (ic_sleeplocks_lookup cn kslot Hkslt with "Hslks") as (gilc gislc) "#Hslkc".
    (* THE RECEIPT UNPACKS IN ONE STEP (SIMP-2), and what comes out beside
       the reference IS the licence ilock's claim arm asks for:
       [InodeRegion.inode_claimed_to_ClaimK] is exactly
       [ireg_wd_lic (ClaimK ty)], so the pair the call below wants is
       handed over as it stands.  ([ireg_wd_lic]'s
       ClaimK arm does not mention its gname, so the [γi] here is any gname
       in scope and the [gsh] the call wants is convertible with it.) *)
    iDestruct (inode_claimed_to_ClaimK ty kslot q dev inum γi with "Hpkg")
      as "[Href Hlic]".
    (* the claimant's reference SHEDS a share for ilock and keeps the rest *)
    iEval (rewrite inode_ref_shed) in "Href".
    iDestruct "Href" as "[Hkeep Hshr]".
    iEval (rewrite inode_shr_gen_intro) in "Hshr".
    iDestruct "Hshr" as (gsh) "Hshr".
    iEval (rewrite inode_ref_short_gen_intro) in "Hkeep".
    iDestruct "Hkeep" as (gkp) "Hkeep".
    iDestruct (inode_ref_short_shr_gen_agree with "Hkeep Hshr") as %->.
    iDestruct (cpu_own_transport CID4 CID7 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Hil CID7 XI γs j γl γu γd γk pd pav pu bn γfs γi cn gilc gislc cov logstart
              inodestart nib kslot (q/2)%Qp gsh (ClaimK ty) dev inum pidv dq dqs
              B1 K eb b lks Vpr
              HKil Hkslt Hlg Hist Hcblk Hinb Hj Hgs HB1a0 ltac:(lkbelow)
              with "Hcg Hcnt [] [] Htext Hkd Hpc Hpenv Hbio Hitbl Hescc Hireg
                    Hslkc Hshr Hlic Hsbi Hppid Hprocs Hdevi Hdgeom
                    Hdlk Hbs1").
    { rewrite Heb /trap_csrs_ext. done. }
    { rewrite Heb /cpu_claim_ext. done. }
    iIntros (CID8 Hq8 Mo dnc bmc filled)
      "%Hcso Hcg Hcnt _ _ Hpc Hppid Hsbi Hbs1 Hslq Hdep
       Hcidev Hciinum Hcivalid Hcload #Hcshot Hcfrz %Hfrf Hwb %Hilkp".
    destruct Hilkp as [Hfilled Htyeq].
    pose proof (Hfrf Hfilled) as Hfresh.
    assert (Hcss3 : is_cs_idx Rs3 = true) by (vm_compute; reflexivity).
    assert (HMos3 : Mo !!! Regidx Rs3 = ientry kslot).
    { rewrite (callee_saved_lookup Hcso Rs3 Hcss3). exact HB1s3. }
    iEval (rewrite Hpcb4) in "Hpc".
    iDestruct (cft_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    iSpecialize ("Hcont" $! CID8 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! Mo true kslot q gsh inum gilc gislc dnc bmc
              with "[%] Hcg Hcnt Hsbn Hsbi Hppid Hbsl Hidev
                    [Hpc Hslq Hdep Hcidev Hciinum Hcivalid Hcload Hcfrz
                     Hkeep Hwb Hop]").
    { intros c Hc Hne.
      rewrite (callee_saved_lookup Hcso c Hc) (HB1cs c Hc Hne)
              (callee_saved_lookup Hcsi c Hc).
      exact (HA3cs c Hc). }
    iSplitR.
    { iPureIntro. split_and!;
        [ exact HMos3 | exact Hkslt
        | exact (proj1 Hinpos) | exact (proj2 Hinpos) | exact Hinb
        | exact Htyeq | exact Hfresh ]. }
    iSplitL "Hpc"; [iExact "Hpc" |].
    iSplitR; [iExact "Hslkc" |].
    iSplitL "Hslq"; [iExact "Hslq" |].

    iSplitL "Hdep"; [iExact "Hdep" |].
    iSplitL "Hcidev"; [iExact "Hcidev" |].
    iSplitL "Hciinum"; [iExact "Hciinum" |].
    iSplitL "Hcivalid"; [iExact "Hcivalid" |].
    iSplitL "Hcload"; [iExact "Hcload" |].
    iSplitR; [iExact "Hcshot" |].
    iSplitL "Hcfrz"; [iExact "Hcfrz" |].
    iSplitL "Hkeep"; [iExact "Hkeep" |].
    iSplitL "Hwb"; [iExact "Hwb" | iExact "Hop"].
  - (* ============================================================== *)
    (*  NO INODES: a0 = 0, the branch is TAKEN, to +0xec               *)
    (* ============================================================== *)
    iDestruct "Hres" as "(%Ha0z & Hisl & Hop)".
    assert (HF1s3 : F1 !!! Regidx Rs3 = (mword_of_int 0 : mword 64)).
    { rewrite /F1 upd_eq Ha0z. apply add_vec_zero_l. }
    assert (Htk : add_vec (mword_of_int (CK + 0xae) : mword 64)
                    (sign_extend' 64 (sign_extend' 13
                       (concat_vec (mword_of_int 31 : mword 8) ('b"0"))))
                  = mword_of_int (CK + 0xec)) by pcw.
    iApply (wp_cbeqz_taken_s_sconf (mword_of_int (CK + 0xae))
              (mword_of_int 31 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              F1 K b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rewrite (rget_ne F1 Ra0 ltac:(nz)) HF1a0 Ha0z;
                    vm_compute; reflexivity)
              ltac:(rewrite Htk; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (cri_0ae with "Htext"). }
    iApply bi.later_intro.
    iIntros (CID6 Hq6) "Hcg Hpc".
    iEval (rewrite Htk) in "Hpc".
    iDestruct (cft_bs3 with "[Hbs1 Hbs2]") as "Hbsl";
      [iSplitL "Hbs1"; [iExact "Hbs1" | iExact "Hbs2"] |].
    iDestruct (cpu_own_transport CID4 CID6 0%nat eb (proc_addr j) b
                 ltac:(rewrite Hb; wp_next_chain) with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! F1 false 0%nat 1%Qp γl inum γl γl dn' bm_empty
              with "[%] Hcg Hcnt Hsbn Hsbi Hppid Hbsl Hidev [Hpc Hisl Hop]").
    { intros c Hc Hne.
      rewrite (HF1cs c Hc Hne) (callee_saved_lookup Hcsi c Hc).
      exact (HA3cs c Hc). }
    iSplitR; [iPureIntro; exact HF1s3 |].
    iSplitL "Hpc"; [iExact "Hpc" |].
    iSplitL "Hisl"; [iExact "Hisl" | iExact "Hop"].
Qed.

End CreateFreshTySpan.
