(* ===================================================================== *)
(*  SpecKexecPinned.v -- kexec("/init"), WITH THE IMAGE'S BYTES PINNED     *)
(*  (claude-notes/projects/namei-pinned-lookup.md §13, stage N-5.2B)       *)
(* ===================================================================== *)

(*  WHAT IT IS.  [SpecKexec.wp_kexec_sconf] is kexec's contract at
    EXISTENTIAL contents -- its own header's largest recorded give-up:
    "DOES NOT SAY WHAT THE USER PAGES HOLD", and, one level before that,
    does not say what the ELF header it read held either.  This file states
    the SAME contract for the ONE call site boot makes -- forkret's
    [kexec("/init", (char *[]){"/init", 0})] -- with the campaign's two
    boot pins added as premises, and with the one thing those pins buy that
    survives into the postcondition: THE ENTRY PC THE COMMIT BLOCK INSTALLS
    IS /init's OWN ELF ENTRY POINT.

    Everything else is [SpecKexec.wp_kexec_sconf_body] verbatim -- the same
    machine premises, the same eb-generic shape, the same budget and the
    same [fs_fabric].  The deltas are exactly four lines of premise (the
    path is the literal "/init"; root's dv pin; /init's fv pin) and one
    line of postcondition (the disjunct below).

    ---- THE CHAIN THIS CLOSES --------------------------------------------

      FsImgCheck    "/init" resolves in the root to inode 7, whose bytes
                    ARE [ElfUser.init_elf] -- the tracked raw the
                    user-rocq dump is proven consistent with.
      FsCfgBoot     the stocking mints root's dview lend and inode 7's
                    fview lend and hands both pins out of [fs_cfg_alloc].
      NameiInitPinned   namei("/init") returns inode 7, or a receipt.
      HERE          ...and the bytes that inode's readi delivers are
                    [init_bytes], so [elf.entry] is [init_entry].

    ---- WHAT IS *NOT* HERE, AND WHY (the lane's blocking finding) --------

    The chartered stage-B post also asked for the PROGRAM HEADERS and the
    LOADSEG'd user pages.  Neither has anywhere to land at this altitude
    and that is not a proof-effort question:

      * the phdr values are consumed by the loop's fold into [szv'], and
        [SpecKexec]'s header already records that [szv'] is deliberately
        existential ("has no consumer while the contents are existential
        anyway"); pinning it means re-stating the fold, which is a
        DIFFERENT strengthening from this one;
      * the loaded pages are owned by [ProcPtOwn.proc_pt] at existential
        contents -- the contents-indexed refinement is STAGE C (§13.1),
        explicitly not this lane's.

    So [init_entry] is the whole of what stage B can SAY, and it is the
    sentence the campaign was after: the process kexec builds will start
    executing /init's first instruction.

    ---- AND WHY THIS CONTRACT IS NOT PROVEN IN THIS TREE YET -------------

    See the lane report and §13.3 of the campaign notes.  In one sentence:
    every phase lemma of the landed kexec walk RELAYS kexec's own exit
    continuation at its full shape -- [∀ mf V' entry spv szv',
    ⌜kexec_ok V V' .. entry ..⌝ -∗ .. -∗ WP Loop], both arms -- and a
    consumer of that interface must therefore be prepared for the SUCCESS
    arm at an arbitrary [entry].  A caller cannot weaken its own
    strengthened continuation into that shape (the missing side is a pure
    fact about [entry], and no resource in the exit determines it), so the
    strengthening cannot be threaded through a single landed relay: it has
    to be threaded through ALL of them.  The unblock is to make the landed
    cone EXIT-GENERIC in [kexec_ok]'s success arm -- one mechanical
    parameter, the eb-generic sweep's shape -- and that is a decision about
    landed files, not a lane's to take.

    The definitions and the bridge kit below are what that walk will need
    whichever way the decision goes, and they are proven here.            *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl dfrac updates.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import own ghost_var invariants gen_heap ghost_map.
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
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import PathElems.        (* [SLASH], [bview], [path_elems]           *)
Require Import DirentEnc.
Require Import DinodeEnc.        (* [di_size]                                 *)
Require Import InodeDefs.        (* [file_byte]                               *)
Require Import InodeInv.
Require Import InodeRegion.      (* §LF: [fv_pin_redeem]                      *)
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import DirViewG.         (* [fv_of], [fv_half]                        *)
Require Import DirViewLend.      (* [fv_pin], [fv_ride], [fv_cancelled]       *)
Require Import DirViewPin.       (* [dv_pin_ent], [dv_cancelled]              *)
Require Import FsTree.           (* [file_bytes]                              *)
Require Import UserPtTree.
Require Import KvmSpec.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import ElfEnc.           (* [eh_entry]                                *)
Require Import SpecReadi.        (* [rd_delivered] -- the readi window bridge *)
Require Import SpecDirlink.
Require Import SpecNamex.        (* [ROOTDEV]                                 *)
Require Import SpecKexec.        (* the landed contract this parallels        *)
Require Import FsImg.            (* [fs_dinode], [fs_data_of], the reductions *)
Require Import FsImgDisk.        (* [fsimg_P]: the literal xv6 disk image     *)
Require Import FsImgCheck.       (* [fname_init], inode 7, [ElfUser.init_elf] *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  /init's BYTES, AND ITS ENTRY POINT                                *)
(* ===================================================================== *)

(*  The image's record for inode 7 and the payload behind it, spelled the
    way [FsCfgBoot.fs_cfg_alloc]'s new post conjunct spells them -- so
    [init_bytes] below is LITERALLY the list that postcondition names, and
    a caller discharges the [fv_pin] premise by [exact]. *)
Definition init_dn : dinode := fs_dinode fsimg_P fsimg_sb 7.
Definition init_data : nat -> list (bv 8) := fs_data_of fsimg_P init_dn.

(*  ...and the contents element itself.  [fv_of] is the definitional tie
    the custody chain carries (N-5.2A): the first [di_size] bytes of the
    payload.                                                              *)
Definition init_bytes : list (bv 8) := fv_of init_dn init_data.

(*  THE IMAGE BRIDGE.  Those bytes are the TRACKED RAW -- and therefore
    every [ElfUser] theorem about [init_elf] is a theorem about the file
    kexec is about to load.  Both sides are [FsImgCheck]'s own
    computations; the only step this file adds is [file_bytes_take_blocks],
    which turns [fv_of]'s per-byte walk into [fsimg_file_bytes]' one pass.  *)
Lemma init_bytes_elf : init_bytes = ElfUser.init_elf.
Proof.
  assert (Hb : init_bytes = fsimg_file_bytes 7).
  { rewrite /init_bytes /fv_of /fsimg_file_bytes /init_data /init_dn.
    apply file_bytes_take_blocks;
      [ intro q; apply (fs_data_of_sized fsimg_P _ fsimg_blocks_full)
      | unfold fs_nblocks, fs_nblk, BSIZE, BSIZE_z; vm_compute; lia ]. }
  rewrite Hb.
  pose proof fsimg_init_bytes_bool as H. by apply bool_decide_eq_true_1 in H.
Qed.

(*  THE HEADER, AS A BYTE READER.  [ElfEnc]'s field readers all take a
    [nat -> bv 8]; the file's bytes are a list, so this is the one
    coercion.  Only offsets below 64 are ever read through it.            *)
Definition init_ef : nat -> bv 8 := fun j => init_bytes !!! j.

(*  ...and the word the commit block writes into [trapframe->epc]:
    [elf.entry], bytes 24..31 of the header, little-endian.               *)
Definition init_entry : mword 64 := (mword_of_int (eh_entry init_ef) : mword 64).

(* ===================================================================== *)
(*  2.  THE BRIDGE KIT (what the walk consumes at its three instants)     *)
(* ===================================================================== *)

Section KexecPinnedBridge.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            ICFG : icfg, !irefslotG Σ, !pavG Σ}.

  Local Notation ROOTZ := (bv_unsigned InodeInv.ROOTINO).

  (*  THE DIVERGENCE RECEIPT, both halves in one name: either the ROOT
      DIRECTORY moved under the dv pin (namei's race) or /init's BYTES
      moved under the fv pin (the contents' race).  Both are persistent
      and neither is forgeable -- no client ever holds a share of the
      one-shot ([DirViewLend] §L/§LF).                                     *)
  Definition kxp_lost : iProp Σ :=
    ((∃ e : gmap fname Z, dv_cancelled ROOTZ e)
     ∨ fv_cancelled 7 init_bytes)%I.

  Global Instance kxp_lost_persistent : Persistent kxp_lost.
  Proof. rewrite /kxp_lost. apply _. Qed.

  (*  ---- INSTANT ONE: THE REDEEM, AT ic_loaded's RIDE -------------------

      D-52d's "fires ONCE after kexec's ilock", as a lemma.  What the
      holder of a checked-out inode has is [ic_loaded]'s [fv_ride] -- the
      whole element on the un-lent arm, three quarters of it on the lent
      one -- and either arm is a [fv_half] the pin can be agreed against.
      The ride comes back UNCHANGED (this is a read, not a move), so the
      caller re-packs [ic_loaded] at the very same [data] and every readi
      that follows still relates its output to it.                        *)
  Lemma kxp_fv_read (E : coPset) (gi : gname) (gfs : fs_names)
      (inodestart : Z) (nib : nat) (z : Z) (b : list (bv 8))
      (dn : dinode) (data : nat -> list (bv 8)) :
    ↑iregN ⊆ E ->
    ireg_inv gi gfs inodestart nib -∗
    fv_pin z b -∗ fv_ride z (fv_of dn data) ={E}=∗
      fv_ride z (fv_of dn data) ∗
      ((⌜fv_of dn data = b⌝ ∗ fv_pin z b) ∨ fv_cancelled z b).
  Proof.
    iIntros (HE) "#Hinv Hpin Hride".
    rewrite {1}/fv_ride. iDestruct "Hride" as "[Hw | [H34 Hm]]".
    - rewrite /fv_hold.
      iMod (fv_pin_redeem E gi gfs inodestart nib z b (DfracOwn 1)
              (fv_of dn data) HE with "Hinv Hpin Hw") as "[Hw Hout]".
      iModIntro. iSplitL "Hw"; [| iExact "Hout"].
      iApply fv_ride_of_hold. iExact "Hw".
    - iMod (fv_pin_redeem E gi gfs inodestart nib z b (DfracOwn (3/4))
              (fv_of dn data) HE with "Hinv Hpin H34") as "[H34 Hout]".
      iModIntro. iSplitR "Hout"; [| iExact "Hout"].
      rewrite /fv_ride. iRight. iFrame "H34 Hm".
  Qed.

End KexecPinnedBridge.

(* ===================================================================== *)
(*  3.  THE READI WINDOW, AGAINST THE BYTE LIST (pure)                    *)
(* ===================================================================== *)

(*  What the redeem's equation is FOR.  [SpecReadi]'s post says the
    destination holds [rd_delivered data dst_olds off tot], i.e.
    [file_byte data (off + i)] below [tot]; the pin says the file's first
    [|b|] bytes ARE [b].  Composing the two is what turns a readi into a
    statement about /init's image -- and it is three lines, because
    [fv_of]'s [file_bytes] is [file_byte <$> seq 0 n] by definition.      *)
Lemma fv_of_file_byte (dn : dinode) (data : nat -> list (bv 8))
    (b : list (bv 8)) (i : nat) :
  fv_of dn data = b -> (i < length b)%nat -> file_byte data i = b !!! i.
Proof.
  intros Hb Hi. rewrite -Hb. rewrite -Hb in Hi.
  rewrite /fv_of /file_bytes in Hi |- *.
  rewrite length_fmap length_seq in Hi.
  rewrite list_lookup_total_fmap; [| rewrite length_seq; exact Hi].
  by rewrite lookup_total_seq_lt.
Qed.

(*  ...and the same at a readi's destination, at [off = 0] -- kexec's ELF
    header read, and (shifted) every one of its phdr reads.               *)
Lemma rd_delivered_pinned (dn : dinode) (data : nat -> list (bv 8))
    (dst_olds : nat -> bv 8) (b : list (bv 8)) (tot i : nat) :
  fv_of dn data = b -> (tot <= length b)%nat -> (i < tot)%nat ->
  rd_delivered data dst_olds 0 tot i = b !!! i.
Proof.
  intros Hb Htot Hi. rewrite /rd_delivered.
  destruct (decide (i < tot)%nat) as [_ | Hno]; [| lia].
  rewrite Nat.add_0_l. apply (fv_of_file_byte dn data b i Hb). lia.
Qed.

(*  THE ONE THE WALK QUOTES: /init's file is 35976 bytes, so a 64-byte
    read at offset 0 is entirely inside it and lands on [init_ef].        *)
Lemma init_hdr_len : (64 <= length init_bytes)%nat.
Proof. rewrite init_bytes_elf. vm_compute. lia. Qed.

Lemma rd_delivered_init (data : nat -> list (bv 8)) (dst_olds : nat -> bv 8)
    (dn : dinode) (i : nat) :
  fv_of dn data = init_bytes -> (i < 64)%nat ->
  rd_delivered data dst_olds 0 64 i = init_ef i.
Proof.
  intros Hb Hi. rewrite /init_ef.
  apply (rd_delivered_pinned dn data dst_olds init_bytes 64 i Hb
           init_hdr_len Hi).
Qed.



(* ===================================================================== *)
(*  3bis.  THE RESULT RELATION, PARAMETERISED ON THE ENTRY POINT          *)
(* ===================================================================== *)

(*  [SpecKexec.kexec_ok] with ONE hole punched in its SUCCESS arm: a
    predicate the caller may impose on the entry PC.  The failure arm is
    untouched -- it does not mention [entry] at all, which is exactly why
    every one of the eight [bad:] tails of the landed walk proves this
    form with the SAME proof term as the landed one.

    ITS PURPOSE IS THE UNBLOCK, and it is stated here so the sweep has a
    vocabulary rather than an idea.  The landed kexec cone spells
    [kexec_ok] in 37 places across 11 files (about twenty lemma and seam
    statements); each one RELAYS kexec's exit continuation, so a client
    that wants to say anything about [entry] cannot weaken its own
    continuation into that shape -- the missing side is a pure fact about
    a universally quantified [entry] and no resource in the exit
    determines it.  Threading [Q] through those 37 sites (and the [Q]
    argument through the [iApply]s that chain them) makes every one of
    them generic, exactly as the eb-generic sweep made the whole tree
    generic in [eb]; [kexec_ok_q_True] below is the row that keeps
    [SpecKexec.wp_kexec_sconf] the theorem it is today.                    *)
Definition kexec_ok_q (Q : mword 64 -> Prop) (V V' : pprivate) (r : mword 64)
    (entry spv szv' : mword 64) (na : nat) (alen : nat -> nat) : Prop :=
  (r = (mword_of_int (-1) : mword 64) /\ V' = V)
  \/
  (Q entry /\
   r = (mword_of_int (Z.of_nat na) : mword 64) /\
   (na <= MAXARG)%nat /\
   kxc_stack_ok (uint szv') (uint szv' - 4096) alen na /\
   pv_sz V' = szv' /\
   spv = (mword_of_int (kxc_sp_final (uint szv') alen na) : mword 64) /\
   ud_tfp (pv_upt V') = ud_tfp (pv_upt V) /\
   kxc_tf (pv_tf V) (pv_tf V') entry spv /\
   pv_ofile V' = pv_ofile V /\
   pv_cwd V' = pv_cwd V /\
   length (pv_name V') = PNAMELEN /\
   (uint szv' - 4096 <= uint spv)%Z /\
   (uint spv <= uint szv')%Z).

(* the landed relation IS the vacuous instance *)
Lemma kexec_ok_q_True (V V' : pprivate) (r entry spv szv' : mword 64)
    (na : nat) (alen : nat -> nat) :
  kexec_ok_q (fun _ => True) V V' r entry spv szv' na alen
  <-> kexec_ok V V' r entry spv szv' na alen.
Proof.
  rewrite /kexec_ok_q /kexec_ok. split.
  - intros [Hl | (_ & H)]; [by left | by right].
  - intros [Hl | H]; [by left | right; split; [exact I | exact H]].
Qed.

Lemma kexec_ok_q_weaken (Q : mword 64 -> Prop)
    (V V' : pprivate) (r entry spv szv' : mword 64)
    (na : nat) (alen : nat -> nat) :
  kexec_ok_q Q V V' r entry spv szv' na alen ->
  kexec_ok V V' r entry spv szv' na alen.
Proof.
  intros [Hl | (_ & H)]; rewrite /kexec_ok; [by left | by right].
Qed.

(*  ...and THE instance this contract takes: the entry PC is /init's own. *)
Definition kxp_entry_ok (e : mword 64) : Prop := e = init_entry.

(* ===================================================================== *)
(*  4.  THE CONTRACT                                                      *)
(* ===================================================================== *)

Definition wp_kexec_pinned_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (gs : list gname) (jp : nat) (gl : gname)           (* the running process *)
    (gu : uart_names) (gd : disk_names) (gk : gname)    (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (g : log_names) (gfs : fs_names) (gi : gname)
    (cn : ic_names) (gtl : gname)                       (* the icache + itable *)
    (ga : gname) (gf : gname)                           (* kalloc, file table  *)
    (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
    (size : Z) (dev : mword 32)
    (plen : nat) (pfun : nat -> bv 8)                   (* the path buffer     *)
    (na : nat) (avf : nat -> mword 64)                  (* argv[0 .. na]       *)
    (alen : nat -> nat) (aslen : nat -> nat)            (* strlen / owned len  *)
    (afun : nat -> nat -> bv 8)                         (* the argument bytes  *)
    (pidv : mword 32) (V : pprivate)
    (dqb dqs dqa dqpv dqas : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kexec in
  let pj := proc_addr jp in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let av := m !!! Regidx (mword_of_int 11 : mword 5) in   (* a1 = argv *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kexec <= K)%nat ->
  (* ---- the file system's geometry, verbatim from SpecNamei ---- *)
  dev = icfg_dev ->
  nib = icfg_nib ->
  (* ...including the inode region's two ambient ties (fs-log.md §G.25):
     namei's walk MINTS the group receipt at its nlink guard, and
     [InodeRegion]'s vocabulary is ambient, so a contract that threads its
     own [g] and [inodestart] meets it through a pure equation.  Same
     pattern as the two above, and true at boot by [IcacheRef.icfg_alloc]. *)
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
  (* ---- the path ---- *)
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ---- AND THE PATH IS THE LITERAL "/init" ----
     the two premises [NameiInitPinned.wp_namei_init_pinned] takes: the
     buffer is ABSOLUTE, and the one name it spells is "init".  This is what
     scopes the whole contract to forkret's [kexec("/init", ...)] arm; a
     caller holding the .rodata literal discharges both by computation. *)
  pfun 0%nat = SLASH ->
  path_elems (bview plen pfun) = [fname_init] ->
  (* ---- the argument vector: [na] non-null pointers then a NULL ---- *)
  (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
  avf na = (mword_of_int 0 : mword 64) ->
  (* ...AND THE NULL IS INSIDE THE FIRST [MAXARG] ELEMENTS.  This is a
     PREMISE rather than something kexec discovers, because kexec cannot
     discover it: its own [argc >= MAXARG] test runs only once [argv[argc]]
     is known non-null, so a vector whose first null sits exactly at index
     [MAXARG] walks straight out of the loop with [argc = MAXARG] and the
     following [ustack[argc] = 0] writes one past [uint64 ustack[MAXARG]].
     sys_exec is the only caller and it guarantees the null is below MAXARG,
     which is what makes that store unreachable; see
     claude-notes/kernel-defects.md for the C-level story.  With the premise
     the argv loop's exit invariant can say [argc < MAXARG] outright instead
     of carrying the off-by-one as slack. *)
  (na < MAXARG)%nat ->
  (* each argument is a NUL-terminated string of [alen i] characters inside
     the [aslen i] bytes the caller owns *)
  (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
  (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
  (* EACH ARGUMENT FITS IN A PAGE, and this is load-bearing rather than a
     convenience.  The push at +0x222 is a 64-bit [sub], and the [bltu
     s2,s7] that guards it does NOT catch an underflow: a wrapped [sp] is
     ABOVE stackbase as an unsigned word, so the machine sails past the
     test with a stack pointer near 2^64.  The success arm's
     [kxc_stack_ok] -- an assertion, since [szv'] is existential and it
     therefore cannot be a premise -- is a Z-level claim and is simply
     FALSE on such a run, so something has to rule the underflow out.
     This does: with every argument at most PGSIZE-1 the decrement is at
     most 4096, and the invariant [stackbase <= sp] (established by the
     previous iteration's own [bltu]) plus [stackbase = sz1 - 4096] and
     [sz1 >= 8192] leaves [sp - (len+1) >= 0].
       sys_exec pays it for free: [fetchstr] copies each argument into a
     kalloc'd page and passes [max = PGSIZE], so no argument it hands over
     is longer.  It also subsumes the [< 2^31] bound strlen asks for. *)
  (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
  (* ---- the running process ---- *)
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  (* ---- THE INTERRUPT INDEX IS NOT A CHOICE THIS CONTRACT MAKES ----------
     [b = true] is FORCED by kexec's own callees, not by anything in its
     body: [SpecBeginOp], [SpecNamei], [SpecIlock], [SpecReadi],
     [SpecIunlockput] and [SpecEndOp] all state their continuation as
     [wp_next true pj], i.e. they are callable only with interrupts enabled,
     and phase A reaches the first of them at +0x00c.  That is a tree-wide
     convention (50 Spec files spell it the same way), not kexec's to
     change; relaxing it is an FS-layer sweep, recorded in
     claude-notes/projects/kexec.md.

     ONCE [b = true], THE OTHER THREE INDICES ARE THEOREMS RATHER THAN
     PREMISES.  [CpuOwn.cpu_own_on] reads
       [cpu_own n eb p C true lks  ⊣⊢  ⌜n = 0 /\ eb = true /\ lks = ∅⌝ ∗ C]
     so the nesting level is 0, the saved enable state is [true] and the
     held-lock set is empty on any run this contract describes -- a caller
     supplies them by supplying the bundle, and every seam in the proof can
     read them back off it.  [eb = true] below is therefore redundant with
     [b = true]; it is kept because it is what the callee contracts quote. *)
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* THE TRAP-CSR COMPLEMENT, in and out.  kexec holds no lock across a
     phase boundary, so what its interior sleeps (begin_op, namei, ilock,
     readi, iunlockput, end_op) need is the caller's pair: [emp] at
     [eb = true], the real [trap_csrs] / [cpu_claim] at [eb = false] --
     which is the index forkret's [if (first)] arm calls kexec at, since
     this revision's scheduler leaves [intena = 0].
     claude-notes/completed/eb-generic-sweep.md is the recipe. *)
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
            cov logstart inodestart nib dev -∗
  kalloc_env ga None -∗
  BitmapInv.sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
  InodeInv.sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
  (* THE BLOCK BITMAP'S INVARIANT (BitmapInv.v): persistent; namei's walk
     and the O-arm's iput/iunlockput free into it, and the B2 stage bundle
     [SpecKexecB2.kxc_res] carries it, so this is the row that funds them. *)
  bitmap_inv gfs bmapstart cov logstart size -∗
  (* THE PROCESS'S PRIVATE BLOCK.  p->pid, p->cwd and the cwd reference namei
     needs are all inside it (ProcInv.proc_priv_cwd_pid); so are the p->name
     bytes safestrcpy writes and the trapframe words the commit block writes. *)
  proc_priv gf pj pidv V -∗
  (* EVERY BYTE RUN KEXEC IS HANDED IS FRACTIONAL, because kexec only READS
     all three of them.  That is the tree's rule -- a byte run the callee only
     READS takes the caller's fraction, a run it WRITES stays whole -- and here
     it is not a nicety but a requirement.  forkret's [if (first)] arm calls

         kexec("/init", (char *[]){"/init", 0})

     so the SAME .rodata literal arrives as the PATH and as argv[0], and one
     byte run cannot be owned twice at full ownership.  A contract taking both
     at [DfracOwn 1] is simply not callable from there.
       So: the path at [dqpv], the argument strings at [dqas], the argv POINTER
     VECTOR at [dqa] (it always was).  Each is passed straight down at the
     caller's fraction -- the path to namei (SpecNamei) and to safestrcpy,
     each argument to strlen and to copyout (SpecCopyout) -- all of which are
     dfrac-generic on their source for the same reason.
       WHAT STAYS WHOLE, and deliberately: everything kexec WRITES.  The new
     page table and its pages, [proc_priv]'s p->name bytes (safestrcpy's
     DESTINATION), the trapframe words, namex's [name[DIRSIZ]] buffer, and
     copyout's destination table.  None of those is an over-ask.
       sys_exec, which owns [char path[MAXPATH]] on its own stack and kalloc's
     a page per argument, simply passes [DfracOwn 1] and sees no change. *)
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
  ([∗ list] i ∈ seq 0 na,
     [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  (* ==== THE TWO NEW PREMISES: BOOT'S PINS ===============================
     Both ride [FsCfgBoot.fs_cfg_alloc]'s postcondition (N-5.1 W5a and
     N-5.2A), and both are about the SAME file: root's directory pin says
     "init" is inode 7, and inode 7's contents pin says that file's bytes
     are the image's [init_bytes] -- which is [ElfUser.init_elf], the very
     ELF the user-rocq dump is proven consistent with ([init_bytes_elf]).
       The dv pin is SPENT by the walk (namei's pinned contract consumes it
     at the hop and answers with the inum or a receipt); the fv pin is only
     READ (an intact redeem is a read, §11.6), so it comes back. ==== *)
  dv_pin_ent (bv_unsigned InodeInv.ROOTINO) fname_init 7 -∗
  fv_pin 7 init_bytes -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  kexec PARKS -- through
     begin_op, namei, ilock, readi, iunlockput and end_op -- so the crossing
     has nothing to do with SIE.  Spelled [b] the two coincided at the only
     instance the deleted [b = true] premise admitted. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (V' : pprivate)
    (entry spv szv' : mword 64),
      ⌜callee_saved m mf⌝ -∗
      (* ==== THE RESULT RELATION, ON THE TWO ARMS THE PINS ADMIT ========
         INTACT (left): nobody moved the root's entry or /init's bytes
         between the boot mint and this walk, so the header kexec read at
         offset 0 IS [init_bytes] there and the word the commit block
         wrote into [trapframe->epc] is that header's e_entry field --
         [kxp_entry_ok], i.e. [init_entry], a literal.  The [-1] arm of
         [kexec_ok_q] does not mention [entry] at all, so a kexec that
         failed says exactly what the landed contract says it does; and
         the fv pin comes back UNSPENT either way (an intact redeem is a
         read, §11.6).
           LOST (right): a concurrent writer cancelled one of the two
         lends, and here is the unforgeable persistent receipt saying
         which.  On that arm the result relation is the LANDED one --
         nothing is known about the contents, which is the honest
         concurrent statement (§11.2).  M2 retires this arm; it rides
         with the D1/D2 forkret decisions (§11.7).
           The dv pin is NOT handed back: namei's pinned contract spends
         it at the hop, and a kexec that fails AFTER namei succeeded has
         genuinely spent it.  Only the fv pin is a read. ==== *)
      ((⌜kexec_ok_q kxp_entry_ok V V'
           (mf !!! Regidx (mword_of_int 10 : mword 5))
           entry spv szv' na alen⌝ ∗ fv_pin 7 init_bytes)
       ∨ (⌜kexec_ok V V' (mf !!! Regidx (mword_of_int 10 : mword 5))
                    entry spv szv' na alen⌝ ∗ kxp_lost)) -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      BitmapInv.sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
      InodeInv.sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
      kalloc_env ga None -∗
      proc_priv gf pj pidv V' -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
      ([∗ list] i ∈ seq 0 na,
         [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
      bslots 3 -∗
      iref_slots 2 -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).


(* ===================================================================== *)
(*  5.  THE MODULE TYPE                                                   *)
(* ===================================================================== *)

Module Type KEXEC_PINNED.
  Parameter wp_kexec_pinned :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_kexec_pinned_body gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
                           ga gf cov logstart bmapstart inodestart nib
                           size dev plen pfun na avf alen aslen afun
                           pidv V dqb dqs dqa dqpv dqas m K eb b lks.
End KEXEC_PINNED.
