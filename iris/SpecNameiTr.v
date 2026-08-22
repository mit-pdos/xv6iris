(* SpecNameiTr.v -- N-3: namei WITH THE GHOST TRACE, the pinned-lookup
   campaign's general contract (claude-notes/projects/namei-pinned-lookup.md
   §4; rulings in its STATUS header and §11.4).

   WHAT THIS IS.  [SpecNamei.wp_namei_gen] returns [inode_held ipv] -- a
   reference to SOME inode, no relation to the path (the SpecNamex.v:113-124
   scope ruling: no path -> inode function exists across instants).  This
   file states the refinement that ruling itself recorded as the honest one:
   ONE caller-supplied atomic step per path element, fired at that hop's
   linearization instant, chaining a caller-chosen CURSOR [P k d] ("after k
   hops the walk stands at inum d").  On success the returned reference is
   pinned: [inode_held_at ipv iL] beside [P L iL].  The path -> inode
   function appears only where a CLIENT's own resources make the path
   stable (N-4, the cancellable lend -- M1, ruled 2026-08-21).

   THE HOP.  At hop k the walk holds the locked directory's payload, whose
   [DirViewG.dv_hold d ents] pins the abstract contents to the bytes
   (N-1, landed).  [nx_hop] lends that whole fragment through the caller's
   fupd at one instant: the caller sees [ents], learns the answer
   [ents !! s], steps its cursor, and hands the fragment straight back.
   The fupd is a single [={⊤}=∗]: the tree's resources are Timeless by
   culture, and the walk fires between instructions where nothing is open.
   (A two-mask ▷-form for clients with non-timeless invariants is a
   deliberate deferral, recorded here so its absence is not an accident.)

   THE HOP NAMES ARE THE ELEMENTS THEMSELVES: dirlookup searches
   [bname 14 nf] of the memmove'd buffer, and SpecNamex.v:104-111 rules
   that [bname 14 nf = e] for the element -- both memmove shapes.  So the
   caller's family is indexed by [path_elems pl] verbatim, and the bridge
   from [dir_first] to [ents !! s] is uniqueness-free
   (FsTree.dir_view_lookup; probe ZZProbeDvLookup.v, finding §9.2).

   FAILURE RETURNS THE UNCONSUMED SUFFIX.  The walk consumes hops
   0..k-1 and dies at k, either WITHOUT firing k (the cursor was not a
   directory -- the caller gets [P k d] back) or AT k (the name was
   absent -- the caller gets the [Pmiss k d] its own hop produced).
   Either way [nx_hops_from .. j] returns the hops the walk never fired,
   so a resource-carrying family is not lost to a short walk.

   SCOPE (ruled): ABSOLUTE PATHS ONLY -- [pfun 0 = SLASH], the walk
   starts at ROOTINO, and the caller's [P 0] is supplied there.  The
   relative form waits for an inum-exposed cwd (Q-c); the nameiparent
   variant rides the same machinery when a consumer appears.

   Everything below the two receipt premises and the changed
   postcondition arms is [SpecNamei.wp_namei_gen_body] VERBATIM -- same
   ambient ties, same ledger, same budget, same eb/trap-CSR threading.
   The landed contract does not move (R10); this is a NEW parallel
   contract, proven by a re-walk that reuses ProofNamexParts (charter
   §9, stage N-3). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import ProcDefs.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.   (* Require Export's DirViewG *)
Require Import FsTree.         (* [fname], [dir_view]'s home *)
Require Import KvmSpec.
Require Import FileInvDefs.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecNamei.      (* K_namei, and the landed body this shadows *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1. The hop, the receipt family, and the pinned package               *)
(* ===================================================================== *)

Section NameiTrDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  (* ONE caller-supplied atomic step.  The walk applies it at hop [k]'s
     linearization instant with [d] its current inum and [ents] the locked
     directory's abstract contents, LENDING the whole [dv_hold] through the
     caller's fupd.  The caller must hand the fragment back unchanged --
     whole ownership makes anything else unprovable -- and receives the
     answer as the match: the cursor steps on a hit, [Pmiss] fires on a
     miss.  Affine and single-use by construction; the contract carries one
     per element ([nx_hops_from .. 0]). *)
  (* THE LENT FRACTION IS EXPOSED AND RETURNED AT THE SAME [dq]: the walk
     lends whatever its custody carries -- [DfracOwn 1] today, and 3/4
     once N-4's lend is outstanding on the directory -- and the caller
     cannot keep a piece (the same [dq] comes back).  Agreement against a
     client-held fraction works at ANY positive pair, which is exactly
     what N-4's redeem does inside this fupd. *)
  Definition nx_hop (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (k : nat) (s : fname) : iProp Σ :=
    (∀ (d : Z) (ents : gmap fname Z) (dqv : dfrac),
       P k d -∗ dv_half d dqv ents ={⊤}=∗
       dv_half d dqv ents ∗
       match ents !! s with
       | Some c => P (S k) c
       | None   => Pmiss k d
       end)%I.

  (* the family from hop [n] on -- the premise at [n = 0], the failure
     arms' refund at the death index *)
  Definition nx_hops_from (P : nat -> Z -> iProp Σ)
      (Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) (n : nat) : iProp Σ :=
    ([∗ list] j ↦ s ∈ drop n (path_elems pl), nx_hop P Pmiss (n + j)%nat s)%I.

  (* [IcacheRef.inode_held] with the inum EXPOSED -- the pinned package.
     Same four conjuncts, one new pure tie; [inode_held_at_held] recovers
     the landed shape so every existing consumer composes unchanged. *)
  Definition inode_held_at (v : mword 64) (z : Z) : iProp Σ :=
    (∃ (k : nat) (q : Qp) (inum : mword 32),
       ⌜v = ientry k⌝ ∗ ⌜(k < NINODE)%nat⌝ ∗
       ⌜bv_unsigned inum < 16 * Z.of_nat icfg_nib⌝ ∗
       ⌜bv_unsigned inum = z⌝ ∗
       inode_refp k q icfg_dev inum)%I.

  Lemma inode_held_at_held (v : mword 64) (z : Z) :
    inode_held_at v z ⊢ inode_held v.
  Proof.
    iIntros "H". iDestruct "H" as (k q inum) "(%&%&%&%&Hr)".
    rewrite /inode_held. eauto 10 with iFrame.
  Qed.

End NameiTrDefs.

(* ===================================================================== *)
(*  2. The contract: [SpecNamei.wp_namei_gen_body] + the trace           *)
(* ===================================================================== *)

Definition wp_namei_tr_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (j : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)   (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                      (* the icache + itable *)
    (ga : gname) (gf : gname)                          (* kalloc, file table  *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (plen : nat) (pfun : nat -> bv 8)                  (* the path buffer     *)
    (n : nat) (Sb : gset Z)
    (P : nat -> Z -> iProp Σ)                          (* the cursor          *)
    (Pmiss : nat -> Z -> iProp Σ)                      (* the miss receipt    *)
    (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) (Vpr : pprivate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.namei in
  let pj := proc_addr j in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let pl := bview plen pfun in
  let L := length (path_elems pl) in
  (K_namei <= K)%nat ->
  dev = icfg_dev ->
  nib = icfg_nib ->
  g = icfg_log ->
  inodestart = icfg_ist ->
  dev = ROOTDEV ->
  (0 < nib)%nat ->
  log_geom_ok cov logstart ->
  0 < size <= BPB ->
  0 <= bmapstart ->
  bmapstart ∈ cov ->
  ~ (bmapstart ∈ log_region_set logstart) ->
  0 <= inodestart ->
  cov_below cov size ->
  ireg_blocks_ok inodestart nib cov logstart ->
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ABSOLUTE PATHS ONLY (ruling Q-c): the walk starts at the root and the
     cursor is supplied there.  The relative form waits for an inum-exposed
     cwd. *)
  pfun 0%nat = SLASH ->
  (walk_need L <= n)%nat ->
  (j < NPROC)%nat ->
  gs !! j = Some gl ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_env -∗
  bio_ctx bn (fs_view gfs gd dev cov) -∗
  log_ctx g bn gfs cov logstart dev -∗
  kalloc_env ga None -∗
  is_itable2 gtl cn gfs gi cov logstart nib dev -∗
  itable_inv -∗
  ic_escrows cn gfs gi cov logstart -∗
  ic_sleeplocks cn -∗
  ireg_inv gi gfs inodestart nib -∗
  ireg_open -∗
  procs_inv gs -∗
  dev_inv gu gd -∗
  disk_geom gd pd pav pu -∗
  is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  bitmap_inv gfs bmapstart cov logstart size -∗
  proc_priv_bare pj pidv Vpr -∗
  inode_held (pv_cwd Vpr) -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  log_opS g n Sb -∗
  (* ---- THE TRACE (the two new resource premises) ---- *)
  P 0%nat (bv_unsigned ROOTINO) -∗
  nx_hops_from P Pmiss pl 0%nat -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (n' : nat) (Sb' : gset Z)
    (ok : bool) (ipv : mword 64) (w : bool),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      proc_priv_bare pj pidv Vpr -∗
      inode_held (pv_cwd Vpr) -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      bslots 3 -∗
      ⌜Sb ⊆ Sb'⌝ -∗
      ⌜w = true -> bmapstart ∈ Sb'⌝ -∗
      ⌜((n - (walk_spend w + (if ok then 0%nat else 1%nat)))%nat <= n')%nat
       /\ (n' <= n)%nat⌝ -∗
      log_opS g n' Sb' -∗
      (if ok
       then (* THE PIN: the register, the package AT ITS INUM, and the
               cursor having walked the whole path to that same inum.  The
               caller alone knows what its [P] says about [iL]; the
               contract promises only the CHAIN -- L hops fired, in order,
               each at the then-current contents. *)
            ∃ (iL : Z),
              ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = ipv⌝ ∗
              inode_held_at ipv iL ∗
              P L iL ∗
              iref_slots 1
       else ⌜mf !!! Regidx (mword_of_int 10 : mword 5)
             = (mword_of_int 0 : mword 64)⌝ ∗
            iref_slots 2 ∗
            (* the death index, the receipt, and the UNFIRED suffix.  Left
               disjunct: hop [k] never fired -- the cursor's node was not a
               directory (or the walk's own [nlink] guard died there) --
               so [P k d] itself comes back beside hops [k..].  Right
               disjunct: hop [k] fired and missed -- [Pmiss k d] beside
               hops [k+1..]. *)
            (∃ (k : nat) (d : Z), ⌜(k < L)%nat⌝ ∗
               ((P k d ∗ nx_hops_from P Pmiss pl k) ∨
                (Pmiss k d ∗ nx_hops_from P Pmiss pl (S k))))) -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type NAMEI_TR.
  Parameter wp_namei_tr :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             ICFG : icfg, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (n : nat) (Sb : gset Z)
      (P : nat -> Z -> iProp Σ) (Pmiss : nat -> Z -> iProp Σ)
      (pidv : mword 32) (dq dqb dqs dqpv : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate),
      wp_namei_tr_body gs j gl gu gd gk pd pav pu bn g gfs gi cn gtl
                       ga gf cov logstart bmapstart inodestart nib
                       size dev plen pfun n Sb P Pmiss
                       pidv dq dqb dqs dqpv m K eb b lks Vpr.
End NAMEI_TR.

(* ===================================================================== *)
(*  3. The canonical instantiation: the ghost-variable cursor            *)
(*     (the "starting point" of the campaign's original ask)             *)
(* ===================================================================== *)

Section NameiTrCursor.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.
  Context `{!ghost_varG Σ (nat * Z)}.

  (* [P k d := γw ↦ half (k, d)]: the client keeps the other half, so the
     walk's position is readable mid-walk by whoever holds it, and the
     success post's [P L iL] IS the receipt "the walk ended at iL".  The
     hop's step is one [ghost_var_update_halves] against the client's
     half... which the CLIENT cannot be holding at the instant -- so the
     canonical form keeps BOTH halves in the family and the client reads
     the pin out of [P L iL] at the end.  (A mid-walk observer variant
     wants the halves split against a client invariant; that is N-4's
     business, not this file's.) *)
  Definition nxc_P (γw : gname) (k : nat) (d : Z) : iProp Σ :=
    ghost_var γw 1 (k, d).
  Definition nxc_Pmiss (γw : gname) (k : nat) (d : Z) : iProp Σ :=
    ghost_var γw 1 (k, d).

  Lemma nxc_hop (γw : gname) (k : nat) (s : fname) :
    ⊢ nx_hop (nxc_P γw) (nxc_Pmiss γw) k s.
  Proof.
    iIntros (d ents dqv) "HP Hdv".
    destruct (ents !! s) as [c|] eqn:Hs.
    - iMod (ghost_var_update (S k, c) with "HP") as "HP". by iFrame.
    - by iFrame.
  Qed.

  Lemma nxc_hops (γw : gname) (pl : list (bv 8)) (n : nat) :
    ⊢ nx_hops_from (nxc_P γw) (nxc_Pmiss γw) pl n.
  Proof.
    rewrite /nx_hops_from. iApply big_sepL_intro.
    iIntros "!>" (j s _). iApply nxc_hop.
  Qed.

End NameiTrCursor.
