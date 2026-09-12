(* ===================================================================== *)
(* UShKernel.v -- sh's WHOLE-PROCESS WP as a CONSTRUCTOR of the U-mode     *)
(* slot ([UexecRet.uslot]), and the bridge from the kernel's own image      *)
(* fact ([SpecKexec.kexec_image_ok]) to it.                              *)
(*                                                                        *)
(* USyncKernel.v / UEchoKernel.v build their slot from a program's         *)
(* [urun]-level theorem through [UkRun.uslot_of_urun].  sh is the process  *)
(* init execs and the one that execs everything else, and one thing about  *)
(* its entry differs:                                                      *)
(*                                                                        *)
(*  THE STATIC DATA.  sh reads and writes its .bss line buffer             *)
(*  ([UkSh.sh_buf], 100 bytes at 0x2020), which the lossy entry would      *)
(*  drop.  [UkRun.uslot_of_urun_all] hands the data outside the frame over *)
(*  exclusively, and the buffer is carved out of the half below the        *)
(*  frame's base.                                                          *)
(*                                                                        *)
(*  THE EXEC BUNDLE does NOT cross here.  sh's exec ecall is inside        *)
(*  [UkSh.ush_rest], and the supplier it needs ([UkRun.uxsup]) is a        *)
(*  premise of that obligation's discharge ([UkShFork.ushf_rest_of_body]), *)
(*  not of this entry.  What this entry owes is the ordinary deposit       *)
(*  supplier [UkRun.udep], exactly as sync's and echo's do.                *)
(*                                                                        *)
(* Also discharged here, from [UkRunSys.wp_uk_ecall_read_win]: UkSh's one  *)
(* Hypothesis, the read-window leaf [UkSh.ush_read_leaf] (the general      *)
(* window leaf did not exist when UkSh.v was written; it does now).        *)
(*                                                                        *)
(* THE BRIDGE ([sh_slot_of_kexec]) discharges every key premise from        *)
(* [kexec_image_ok ElfUser.sh_elf …]: the pc off [kexec_image_ok_pc] and   *)
(* [ElfUser.sh_elf_entry]; the image off [uimg_sub (elf_image sh_elf)]     *)
(* through [shk_img_sub_of_elf] below; the pages off [KexecBuilt.kxb_perm  *)
(* _ok] at sh's two PT_LOADs (R-X at 0x0/0x1000, RW- at 0x2000) and the    *)
(* RW stack page; the frame's bytes off [kexec_stack_at] (below the        *)
(* argument block every stack-page byte is zero, hence present); the .bss  *)
(* buffer off [ElfUser.sh_elf_image_concrete]; the descriptors off         *)
(* [kexec_image_ok_fd]; the map-stop row off [kexec_image_ok_below].  NO   *)
(* [vm_compute] ON [sh_elf] IS NEEDED: the entry,                          *)
(* the segment table and the image split are ElfUser.v's already-reduced   *)
(* facts, and the PT_LOAD headers are read off [sh_elf_segments] for a     *)
(* VARIABLE file ([elf_segments_loads]) so the kernel never reduces the    *)
(* 29 KB constant.  ElfUser.v is a declared leaf, so importing it here is  *)
(* in order.                                                               *)
(*                                                                        *)
(* SH'S ENTRY SAYS NOTHING ABOUT ITS STANDARD STREAMS.  The only          *)
(* descriptor premise is [length sts = NOFILE]: the ledger of the low      *)
(* [NSTD] slots ([UkSh.ush_std]) goes in at whatever state the exec'ing     *)
(* process left it, and sh's console preamble is xv6's own repair of a      *)
(* closed one.  A caller could not supply more anyway -- init's dups go     *)
(* through the untracked leaf and init never tests its repair open.         *)
(*                                                                         *)
(* THE ONE PREMISE THE IMAGE FACT DOES NOT GIVE: room for sh's frames.     *)
(* [kxc_stack_ok] only says the argument block fits the stack page, so     *)
(* "sp - 8 * avail is still on the stack page" is stated as a premise on   *)
(* [kxc_sp_final]; a MAXARG-bounded block leaves most of the page, so any  *)
(* caller has it.                                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import UmodeArith.
Require Import UserPerm UexecSlot UexecRet UsysMemOk.
Require Import UserHeap UkRunSys.
Require Import FdSlots.
Require Import ProcGeom.
Require Import UserFd.
Require Import UCodeShK UkSh.
Require Import UkRun.          (* [udep] / [uslot_of_urun_all] / [urun] *)
Require Import PageGeom.       (* [PGSIZE] *)
Require Import UserPtTree.     (* [pgroundup] *)
Require Import ElfFile.
Require Import KexecDefs.      (* [kxc_sp_final] / [kxc_round16] *)
Require Import KexecBuilt.     (* [kxb_perm_ok] / [kexec_pg] / [kexec_seg_perm] *)
Require Import SpecKexec.    (* [kexec_image_ok] *)
Require Import UmodeAbi.       (* [uimg_sub] -- the image inclusion *)
Require Import ElfUser.        (* [sh_elf] and its reduced facts (leaf, see header) *)
Require User.ShSyms User.ShData User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS0 THE PURE FACTS OF sh's IMAGE, off ElfUser.v's reduced constants.   *)
(* ===================================================================== *)

(* THE IMAGE INCLUSION AT sh.  The exec contract's image conjunct is
   [uimg_sub (elf_image sh_elf) M]; sh's own program-side premise is
   [UCodeShK.shk_img_sub M], the two dumped maps separately.  [elf_image]
   folds them into a union with the bss zeros, so the bridge is one
   inclusion-of-a-union projection per half -- the right half through a
   COMPUTED commutation of the two dumped maps rather than a disjointness
   side condition, so no set reasoning happens at an image consumer's
   altitude. *)
Lemma uimg_sub_union_l (m1 m2 M : gmap Z (bv 8)) :
  uimg_sub (m1 ∪ m2) M -> uimg_sub m1 M.
Proof.
  intros H a b Hb. apply H. by apply lookup_union_Some_l.
Qed.

Lemma sh_union_comm_bool :
  bool_decide (ShInstrs.sh_bytes ∪ ShData.sh_data
               = ShData.sh_data ∪ ShInstrs.sh_bytes) = true.
Proof.
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.
Qed.

Lemma shk_img_sub_of_elf (M : gmap Z (bv 8)) :
  uimg_sub (elf_image ElfUser.sh_elf) M -> shk_img_sub M.
Proof.
  intros H. rewrite ElfUser.sh_elf_image in H.
  split.
  - exact (uimg_sub_union_l _ _ _ (uimg_sub_union_l _ _ _ H)).
  - pose proof (uimg_sub_union_l _ _ _ H) as Hfd.
    intros a b Hb. apply Hfd.
    rewrite (bool_decide_eq_true_1 _ sh_union_comm_bool).
    by apply lookup_union_Some_l.
Qed.

(* the PT_LOAD table read off [elf_segments], for a VARIABLE file: the
   [destruct] never touches the constant, so the kernel never reduces it *)
Lemma elf_segments_loads (f : elf_bytes) (segs : list (Z * Z * Z * Z)) :
  elf_segments f = Some segs ->
  (fun p => (ep_vaddr p, ep_filesz p, ep_memsz p, ep_flags p)) <$> elf_loads f
  = segs.
Proof.
  unfold elf_segments, elf_loads.
  destruct (elf_phdrs f) as [ps |]; [| discriminate].
  cbn [mbind option_bind]. intro H. injection H as H. exact H.
Qed.

(* sh's two PT_LOADs: (0x0, 0x1c54, 0x1c54, R-X) and (0x2000, 0x10, 0x98, RW-) *)
Lemma sh_loads :
  exists p0 p1 : elf_phdr,
    elf_loads sh_elf = [p0; p1]
    /\ ep_vaddr p0 = 0 /\ ep_memsz p0 = 0x1c54 /\ ep_flags p0 = 5
    /\ ep_vaddr p1 = 0x2000 /\ ep_memsz p1 = 0x98 /\ ep_flags p1 = 6.
Proof.
  pose proof (elf_segments_loads sh_elf _ sh_elf_segments) as H.
  revert H. generalize (elf_loads sh_elf) as l. intros l H.
  destruct l as [| p0 [| p1 [| p2 l]]]; cbn [fmap list_fmap] in H;
    try discriminate H.
  injection H as Hv0 Hfs0 Hms0 Hfl0 Hv1 Hfs1 Hms1 Hfl1.
  exists p0, p1. split_and!; [ reflexivity | assumption.. ].
Qed.

Lemma sh_kexec_top : kexec_top sh_elf = 0x3000.
Proof. unfold kexec_top. rewrite sh_elf_end. reflexivity. Qed.

Lemma sh_kexec_sz : kexec_sz sh_elf = 0x5000.
Proof. unfold kexec_sz. rewrite sh_kexec_top. reflexivity. Qed.

(* the entry, as the resume pc reads it: 0x9d0 is 2-aligned, so [ret_pc]
   is the identity on it, and [ShData.shEntry] IS [ShSyms.start] *)
Lemma sh_start_pc :
  ret_pc (mword_of_int ShData.shEntry : mword 64) = mword_of_int ShSyms.start.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma csp_rs1_eq : csp_rs1 = (mword_of_int 2 : mword 5).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* a closed [lo <= x < hi] on literals, by computation rather than by
   [lia] in a wide context *)
Local Ltac zclosed :=
  split; [ vm_compute; discriminate | vm_compute; reflexivity ].
(* ...and a closed [x <= y] *)
Local Ltac zle := vm_compute; discriminate.

(* the final sp is 16-rounded, hence 8-aligned *)
Lemma kxc_sp_final_mod8 (top : Z) (alen : nat -> nat) (na : nat) :
  kxc_sp_final top alen na mod 8 = 0.
Proof. unfold kxc_sp_final, kxc_round16. lia. Qed.

(* a page's permission, read at any address on the page *)
Lemma sh_page_perm (π : gmap (mword 27) uperm) (b a : Z) (q : uperm) :
  π !! kexec_pg b = Some q ->
  b mod 4096 = 0 -> b <= a < b + 4096 -> 0 <= b -> b + 4096 <= 274877906944 ->
  uperm_at π (mword_of_int a : mword 64) = Some q.
Proof.
  intros Hq Hb Ha Hb0 Hhi. unfold uperm_at. unfold kexec_pg in Hq.
  rewrite (shk_svpn_page a ltac:(lia)).
  replace (4096 * (a / 4096)) with b; [ exact Hq | lia ].
Qed.

(* the two readings of [udata_lo] membership the bridge needs *)
Lemma udata_lo_is_Some (M : gmap Z (bv 8)) (π : gmap (mword 27) uperm)
    (sz a : Z) (b : bv 8) :
  M !! a = Some b -> uw_addr π a -> a < sz ->
  is_Some (udata_lo M π sz !! a).
Proof.
  intros HM Hw Hlt. exists b.
  unfold udata_lo, udata_part.
  apply map_lookup_filter_Some. split; [| cbn; exact Hlt ].
  apply map_lookup_filter_Some. split; [ exact HM | cbn; exact Hw ].
Qed.

Lemma uw_addr_of_perm (π : gmap (mword 27) uperm) (a : Z) (q : uperm) :
  uperm_at π (mword_of_int a : mword 64) = Some q -> up_W q = true ->
  uw_addr π a.
Proof. intros Hq Hw. exists q. exact (conj Hq Hw). Qed.

(* the kernel's read count is the signed low half of a2; at a caller whose
   a2 IS a count it is at most that count *)
Lemma sh_rdcount_le (x : mword 64) (k : nat) :
  uint x = Z.of_nat k ->
  (Z.to_nat (bv_signed (subrange_vec_dec x 31 0 : mword 32)) <= k)%nat.
Proof.
  intro H. unfold bv_signed, bv_swrap, bv_wrap.
  rewrite subrange_31_0_unsigned. rewrite <- uint_unsigned. rewrite H.
  assert (E1 : bv_modulus 32 = 4294967296) by (vm_compute; reflexivity).
  assert (E2 : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
  rewrite E1 E2.
  set (s := (Z.of_nat k mod 4294967296 + 2147483648) mod 4294967296
            - 2147483648).
  pose proof (Z.mod_pos_bound (Z.of_nat k) 4294967296 ltac:(lia)) as B1.
  pose proof (Z.mod_pos_bound (Z.of_nat k mod 4294967296 + 2147483648)
                4294967296 ltac:(lia)) as B2.
  assert (Hs : s <= Z.of_nat k).
  { unfold s.
    destruct (Z_lt_le_dec (Z.of_nat k mod 4294967296) 2147483648)
      as [Hlt | Hge].
    - rewrite (Z.mod_small (Z.of_nat k mod 4294967296 + 2147483648) 4294967296
                 ltac:(lia)). lia.
    - replace (Z.of_nat k mod 4294967296 + 2147483648)
        with ((Z.of_nat k mod 4294967296 - 2147483648) + 1 * 4294967296)
        by lia.
      rewrite Z_mod_plus_full.
      rewrite (Z.mod_small (Z.of_nat k mod 4294967296 - 2147483648) 4294967296
                 ltac:(lia)). lia. }
  lia.
Qed.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)
Require Import UserCwd.  (* [ucwd] / [ucwd_any] -- the process's own view of its working directory *)
Require Import UserChildren.  (* [uch_any] -- the process's own half of its children set *)
Require Import Xv6Cameras.    (* [uartGhostG] -- the console ring's cameras *)
Require Import UserConsole.   (* [ucons_pay] / [upos] -- sh's exit payload and
                                 its half of the console position pair *)

Section UShKernel.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  (* the console ring's cameras, at the narrow class ([UserConsole.v]'s
     header): this file binds no whole-system bundle either *)
  Context `{!uartGhostG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* THE NUMBERS SH ADMITS ([UexecSG.uprogSG]'s [psok]).  A SECTION
     hypothesis here as it is in the program files, and the exec dispatcher
     -- which sees the instance -- discharges it, exactly as it discharges
     [UexecCond.cond_entry_slot]'s. *)
  Hypothesis Hpsok : forall k : Z, k <> UsysMemOk.USYS_exec -> psok k.

  (* NO [Context {CID : CpuId}] and no ambient [CurCtx]: the slot binds the
     hart itself, and the run binds its own context. *)

  (* ------------------------------------------------------------------- *)
  (* SS1 UkSh's Hypothesis, discharged (header).                          *)
  (* ------------------------------------------------------------------- *)
  Lemma ush_read_leaf_of_win (N : uk_names Σ) :
    forall (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k : nat)
           (f : nat -> bv 8) (avail : nat),
      usysno m = USYS_read ->
      uint (m !!! Regidx (mword_of_int 11 : mword 5)) = a ->
      uint (m !!! Regidx (mword_of_int 12 : mword 5)) = Z.of_nat k ->
      is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
      uinstr_is (ukn_t N) pc false (ECALL tt) -∗
      ubytes (ukn_d N) a k f -∗
      urun N h m pc avail -∗
      (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
         ⌜ (d <= k)%nat ⌝ -∗
         ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
         ubytes (ukn_d N) a k g -∗
         urun N h' (<[Regidx (mword_of_int 10 : mword 5) := r]> m)
           (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).
  Proof.
    intros h m pc a k f avail Hn Ha Hk Hal4.
    iIntros "#Hi Hbuf Hrun Hcont".
    subst a.
    pose proof (sh_rdcount_le _ k Hk) as Hcnt.
    iApply (wp_uk_ecall_read_win N h m pc _ k f avail Hn eq_refl
              Hcnt Hal4 with "Hi Hrun [] Hbuf").
    { iApply udepw_of_psok; [ apply Hpsok | ]; (vm_compute; discriminate). }
    iIntros (h' r d g) "%Hd %Hgf Hrun Hbuf".
    iApply ("Hcont" $! h' r d g with "[%] [%] Hbuf Hrun");
      [ lia | exact Hgf ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS2 THE DEPOSIT (header (1), (2)).                                   *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_uexec_slot (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (T : iProp Σ) `{!Persistent T}
      (* SH'S EXIT PAYLOAD, a parameter (GENERIC-PAY).  It is where the
         console reader token lives, because only [UkRun.ukn_pay N (-1)]
         survives a kill: if the shell is killed, init has to get the
         input back to respawn it.  CONSTANT IN THE STATUS, because the
         exit stub answers [ukn_pay N xs ∧ ukn_pay N (-1)] out of the one
         resource the run carries; [UserConsole.ucons_pay_const] is the
         witness the application supplies. *)
      (Q : Z -> iProp Σ)
      (W : uvis) (n0 n : nat) :
    (forall x y : Z, Q x = Q y) ->
    tf_resume_pc (uvis_tf W) = (mword_of_int ShSyms.start : mword 64) ->
    shk_img_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 8192 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * (2 + (8 + (16 + (ush_Dbody + n0)))))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (* AND NOTHING ELSE ABOUT THE TABLE.  [ush_pstate]'s ledger is the low
       [NSTD] slots at whatever states the exec'ing process left them; sh's
       [fdalloc] reasoning reads the scan off THEM, and its console
       preamble reopens a stream that is closed. *)
    (* the map stops at the break -- [UkRun.uslot_of_urun]'s own premise,
       which is what lets a later [sbrk] hand sh fresh memory.  The bridge
       below reads it off [kexec_image_ok]'s own row. *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* THE PAYLOAD.  The data below the frame is handed over whole, and it
       is here that it is spent: on the line buffer, which every stage has
       needed, AND on [R] -- the two static lexer tables, the allocator's
       first-call state, the break.  Naming those would drag the parser's
       and the allocator's files into this one, so the cut is exactly the
       one [UkSh.ush_rest] makes: an opaque [R], produced once out of the
       image's own writable data and carried round the loop thereafter. *)
    □ (∀ γt γd γs : gname,
        usz γs (uvis_sz W) -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
           ubyte γd k b) -∗
        ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    (* THE DEPOSIT SUPPLIER, the one obligation the ARM adds to an entry
       constructor: whoever hands sh a [UkRun.urun] says which syscall
       bundles it can pay and out of what.  (Before the fold this slot held
       a supplier of the EXEC bundle at every key, because the entry handed
       over an ENRICHED run and a plain program proof could not build one.
       There is one tier now, so what is left is the ordinary deposit
       obligation; the exec bundle rides in through [ush_rest], whose
       discharge takes [UkRun.uxsup].) *)
    udep -∗
    (∀ N : uk_names Σ,
       ush_rest N γp (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    (* THE ENTRY'S ONE DESCRIPTOR ROW, at its three arms
       ([UkSh.ush_fd0]).  Persistent, and the walk reads none of the three
       -- which is what makes the CLOSED arm this same application. *)
    UkSh.ush_fd0 T (take NSTD (uvis_fd W)) -∗
    (* THE PAY FACT, at sh's own payload, and THE PAYLOAD ITSELF beside
       it: the run carries [Q (-1)] between traps, hands it to the kernel
       at every entry and is handed it back at every resume
       ([UkRun.uslot_of_urun_all]'s two rows).  The kernel is what puts it
       here -- [SpecKexec.exec_slot_pre]'s wands at the exec init's pinned
       bundle answers ([PinnedExec.pex_slot]). *)
    my_pay (uvis_gen W) Q -∗
    Q (-1) -∗
    (* ...AND THE POSITION, the ONE linear resource init's pinned exec
       bundle hands sh through [PinnedExec]'s [Pay].  It goes into
       [UkSh.ush_pstate] and is what the read will move. *)
    upos γp n -∗
    uslot W.
  Proof.
    intros HQc Hpc Hsub Hx Hal8 Hroom Hstk Hfdlen Hstop.
    iIntros "#Hpay #Hdep #Hrest #Hfd0 #Hmp HQ Hpos".
    iApply (uslot_of_urun_all W (2 + (8 + (16 + (ush_Dbody + n0)))) Q
              Hal8 Hroom Hstk Hfdlen Hstop with "Hdep Hmp HQ").
    (* sh's own half of its children set travels in [UkSh.ush_pstate]
       beside the ledger and the cwd: fork1 MOVES the set, so the fragment
       goes down the chain index-free ([UserChildren.uch_any]). *)
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd Hcwf Hchf Dlo _ Hrun".
    (* THE RECORD'S PAYLOAD IS SH'S, and it is CONSTANT: that is the whole
       of what the walk below needs of it ([UkRun.ukn_const]). *)
    pose proof (ukn_const_of_eq N Q Hpayeq HQc) as Hti.
    rewrite Hpc.
    (* [R] and the line buffer, out of the data below the frame *)
    iDestruct ("Hpay" $! (ukn_t N) (ukn_d N) (ukn_s N) with "Hszf Dlo")
      as (f) "[HR Hbs]".
    iPoseProof ("Hrest" $! N) as "#Hr".
    iApply (wp_ksh_start N γp T Hpsok (ush_read_leaf_of_win N)
              (R (ukn_t N) (ukn_d N) (ukn_s N)) h _ f n0 (take NSTD (uvis_fd W))
              with "Hr [] Hfd0 [Hstd Hcwf Hchf Hpos] HR Hbs [Hrun]").
    - iApply (shk_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                (shk_img_text _ Hsub) Hx with "Ht").
    - rewrite /UkSh.ush_pstate /UkSh.ush_std /UkSh.ush_pos. iFrame "Hstd".
      iSplitL "Hcwf"; [ iApply (ucwd_any_of with "Hcwf") | ].
      iSplitL "Hchf"; [ iApply (uch_any_of with "Hchf") | ].
      iExists n. iExact "Hpos".
    - iExact "Hrun".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* SS3 THE BRIDGE from the kernel's image fact (header).                *)
  (* ------------------------------------------------------------------- *)
  Lemma sh_slot_of_kexec (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (T : iProp Σ) `{!Persistent T}
      (* sh's exit payload, passed straight through: see [sh_uexec_slot] *)
      (Q : Z -> iProp Σ)
      (na : nat)
      (alen : nat -> nat) (afun : nat -> nat -> bv 8) (sts : list fdstate)
      (W' : uvis) (n0 n : nat) :
    (forall x y : Z, Q x = Q y) ->
    kexec_image_ok sh_elf na alen afun sts W' ->
    (* room for sh's frames on the stack page, below the argument block *)
    kexec_sz sh_elf - PGSIZE + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= kxc_sp_final (kexec_sz sh_elf) alen na ->
    length sts = NOFILE ->
    (* the payload, passed straight through: see [sh_uexec_slot] *)
    □ (∀ γt γd γs : gname,
        usz γs (uvis_sz W') -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
           ubyte γd k b) -∗
        ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    (* the deposit supplier, passed straight through *)
    udep -∗
    (∀ N : uk_names Σ,
       ush_rest N γp (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    (* the entry row, the pay fact, the payload and the position, all four
       passed straight through: see [sh_uexec_slot] *)
    UkSh.ush_fd0 T (take NSTD sts) -∗
    my_pay (uvis_gen W') Q -∗
    Q (-1) -∗
    upos γp n -∗
    uslot W'.
  Proof.
    intros HQc Hok Hroom Hlen.
    (* THE MAP STOPS AT THE BREAK, off the image fact's own row: exec built
       a fresh address space, so [KexecBuilt.kxb_perm_below] says it maps
       nothing above the break, which is what lets sh's later [sbrk] see
       the run it is handed as fresh ([UserHeap.uheap]'s map-stop clause). *)
    pose proof (kexec_image_ok_below _ _ _ _ _ _ Hok) as Hstop.
    destruct sh_loads as (p0 & p1 & Hld & Hv0 & Hm0 & Hf0 & Hv1 & Hm1 & Hf1).
    pose proof sh_kexec_sz as Hsz. pose proof sh_kexec_top as Htop.
    pose proof (kexec_image_ok_pc _ _ _ _ _ _ _ Hok sh_elf_entry) as Hpc.
    pose proof (kexec_image_ok_fd _ _ _ _ _ _ Hok) as Hfd.
    rewrite Hsz in Hroom. unfold PGSIZE in Hroom.
    unfold kexec_image_ok in Hok. cbv zeta in Hok. rewrite Hsz in Hok.
    destruct Hok as (_ & Hszv & Hsp & _ & _ & Himg & _ & Hstk & Hperm & _ & _ & _).
    destruct Hperm as (Hpg & _ & Hstpg).
    rewrite Htop in Hstpg. change (0x3000 + PGSIZE) with 0x4000 in Hstpg.
    set (spv := kxc_sp_final 0x5000 alen na) in *.
    set (π := uvis_perm W') in *.
    set (M := uvis_M W') in *.
    (* ---- the stack pointer: below the top, above the frame ---- *)
    pose proof (kxc_sp_final_gap 0x5000 alen na) as Hgap.
    pose proof (kxc_sp_mono 0x5000 alen 0 na (Nat.le_0_l na)) as Hmono.
    cbn [kxc_sp] in Hmono. fold spv in Hgap.
    assert (Hspv : 0x4000 <= spv < 0x5000) by (clear -Hroom Hgap Hmono; lia).
    assert (Hsp' : uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1) = spv).
    { rewrite csp_rs1_eq. unfold tf_resume_gpr0. rewrite tf_resume_gpr_sp.
      change tf_sp_idx with kxc_tf_sp_idx. rewrite Hsp.
      apply uint_moi. unfold Z64. clear -Hspv. lia. }
    (* every [lia] below runs in a cleared context: the one above the frame
       is the whole image fact, and it costs seconds per call otherwise *)
    (* ---- the pages: text R-X, .bss RW-, stack RW- ---- *)
    assert (Hpg0 : forall b : Z, b = 0 \/ b = 4096 ->
              π !! kexec_pg b = Some (kexec_seg_perm p0)).
    { intros b Hb. apply (Hpg 0%nat p0); [ rewrite Hld; reflexivity | ].
      unfold kexec_seg_pages. rewrite Hld. cbn [take].
      rewrite kexec_sz_after_nil. rewrite Hv0 Hm0.
      change (pgroundup 0) with 0. unfold PGSIZE.
      destruct Hb as [-> | ->]; split; [ reflexivity | zclosed | reflexivity | zclosed ]. }
    assert (Hpg1 : π !! kexec_pg 0x2000 = Some (kexec_seg_perm p1)).
    { apply (Hpg 1%nat p1); [ rewrite Hld; reflexivity | ].
      unfold kexec_seg_pages. rewrite Hld. cbn [take].
      unfold kexec_sz_after. cbn [foldl]. unfold kx_grow, kx_uvmalloc.
      rewrite Hv0 Hm0 Hv1 Hm1. unfold PGSIZE.
      (* closed arithmetic: [pgroundup 0x1c54 = 0x2000] *)
      split; [ reflexivity | zclosed ]. }
    assert (Hperm0 : kexec_seg_perm p0 = MkUperm true false)
      by (unfold kexec_seg_perm; rewrite Hf0; reflexivity).
    assert (Hperm1 : kexec_seg_perm p1 = MkUperm false true)
      by (unfold kexec_seg_perm; rewrite Hf1; reflexivity).
    assert (Hx : forall a : Z, 0 <= a < 8192 -> ux_addr π a /\ ~ uw_addr π a).
    { intros a Ha.
      assert (Hat : uperm_at π (mword_of_int a : mword 64)
                    = Some (MkUperm true false)).
      { destruct (Z_lt_le_dec a 4096) as [Hlt | Hge].
        - rewrite <- Hperm0. apply (sh_page_perm π 0 a);
            [ apply Hpg0; left; reflexivity | reflexivity
            | clear -Ha Hlt; lia | zle.. ].
        - rewrite <- Hperm0. apply (sh_page_perm π 4096 a);
            [ apply Hpg0; right; reflexivity | reflexivity
            | clear -Ha Hge; lia | zle.. ]. }
      split.
      - exists (MkUperm true false). exact (conj Hat eq_refl).
      - intros (q & Hq & Hw). rewrite Hat in Hq. injection Hq as <-.
        discriminate Hw. }
    assert (Hwbss : forall a : Z, 0x2000 <= a < 0x3000 -> uw_addr π a).
    { intros a Ha. apply (uw_addr_of_perm π a (MkUperm false true)); [| reflexivity ].
      rewrite <- Hperm1. apply (sh_page_perm π 0x2000 a);
        [ exact Hpg1 | reflexivity | clear -Ha; lia | zle.. ]. }
    assert (Hwstk : forall a : Z, 0x4000 <= a < 0x5000 -> uw_addr π a).
    { intros a Ha. apply (uw_addr_of_perm π a uperm_rw); [| reflexivity ].
      apply (sh_page_perm π 0x4000 a);
        [ exact Hstpg | reflexivity | clear -Ha; lia | zle.. ]. }
    (* ---- the frame's bytes: zero on the stack page below the block ---- *)
    destruct Hstk as (_ & Hzero). unfold PGSIZE in Hzero.
    assert (Hbelow : forall a : Z, 0x4000 <= a < spv -> M !! a = Some (bv_0 8)).
    { intros a Ha. apply Hzero; [ clear -Ha Hspv; lia | ].
      intros [ (i & Hi & Hlo & _) | (Hlo & _) ]; [| clear -Ha Hlo; lia ].
      pose proof (kxc_sp_mono 0x5000 alen (S i) na Hi) as Hm.
      clear -Ha Hlo Hm Hgap; lia. }
    (* ---- the deposit.  The line buffer is no longer carved here: it
           comes out of the payload premise, together with [R]. ---- *)
    assert (Hfrm : forall j : nat,
              (j < 8 * (2 + (8 + (16 + (ush_Dbody + n0)))))%nat ->
              0x4000 <= spv - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
                        + Z.of_nat j < spv)
      by (intros j Hj; clear -Hj Hroom; lia).
    (* the entry row is stated at the EXEC'ING process's table, which is
       the one the image fact says the new key carries *)
    rewrite <- Hfd.
    iApply (sh_uexec_slot R γp T Q W' n0 n).
    - exact HQc.
    - rewrite Hpc. exact sh_start_pc.
    - exact (shk_img_sub_of_elf M Himg).
    - exact Hx.
    - rewrite Hsp'. exact (kxc_sp_final_mod8 _ _ _).
    - rewrite Hsp'. clear -Hroom; lia.
    - intros j Hj. rewrite Hsp'. destruct (Hfrm j Hj) as [Hj0 Hj1].
      apply (udata_lo_is_Some M π (uvis_sz W') _ (bv_0 8)).
      + apply Hbelow. exact (conj Hj0 Hj1).
      + apply Hwstk. split; [ exact Hj0 | clear -Hj1 Hspv; lia ].
      + rewrite Hszv. clear -Hj1 Hspv; lia.
    - rewrite Hfd. exact Hlen.
    - exact Hstop.
  Qed.

End UShKernel.
