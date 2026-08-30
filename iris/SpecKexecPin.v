(* ===================================================================== *)
(*  SpecKexecPin.v -- kexec OF A PINNED PATH, over the LANDED pin route    *)
(*  (fs-syscall-specs; the port of the seven off-build SpecKexecPinned     *)
(*   files onto FsInitPin/FsInitPinBoot's era-0 pins and KexecOkQ's hole)  *)
(* ===================================================================== *)

(*  WHAT THIS FILE IS.  A STATEMENT file: definitions, structural lemmas,
    and one Module Type.  It replaces the off-build
    [SpecKexecPinned]/[ProofKexecPinned*]/[LinkKexecPinned] contract --
    whose premises ([FsCfgBoot.dv_pin]/[fv_pin], cancellable lends minted
    by a deleted boot lemma) no longer exist -- with the SAME sentence
    stated over what IS landed:

      * the PINS are pure facts about the abstract view
        ([FsInitPin.era0_init_path_pin] / [era0_init_content_pin],
        transported to the boot's own premises by [FsInitPinBoot]), and
      * the ENTRY-POINT hole is [KexecOkQ.kexec_ok_q]'s [Q] slot, which
        the whole landed kexec cone already relays generically (the
        exit-generic sweep, namei-pinned-lookup.md sect. 13.3-13.5).

    THE SENTENCE (what init.c's proof needs): kexec of a PINNED path --
    era-0 "/init", and "sh" whose era-0 pins a sibling lane is landing --
    either fails with the process untouched, or succeeds and the process
    resumes in the pinned program's image: the trapframe epc the commit
    block installs IS the pinned ELF's entry point ([Q_pin], through the
    relation), a0 is argc, and the loaded segments are the ELF decode of
    the pinned bytes ([kxp_image_ok] -- see THE UPGRADE GAP below for
    exactly how much of that last clause the landed vocabulary can carry).

    ---- Q_pin's EXACT STRENGTH, AND THE UPGRADE GAP ---------------------

    [KexecOkQ.kexec_ok_q]'s hole is [Q : mword 64 -> Prop], applied to
    [entry] alone.  So what can ride the THIRTY-ONE landed relays with no
    restatement is precisely a pure claim on the entry PC, and [Q_pin pb]
    is the strongest such claim: [entry] is the 8-byte little-endian word
    at offset 24 of the pinned bytes -- [kxq_entry] of the pinned header,
    i.e. the pinned ELF's e_entry ([pin_init_entry] computes it to
    [InitData.initEntry], the address every [USpecInit] theorem runs from).

    THE SEGMENTS CANNOT RIDE THE HOLE.  The new image [us_M U'] is a
    ustate field: the landed post binds [U'] and hands back
    [proc_priv gf pj pidv U'] -- whose [proc_ptm_at] pins [us_M U'] as the
    real address-space contents -- but the pure relation says NOTHING
    about it, and a conjunct about [U'] cannot be threaded through one
    relay (the N-5.2B finding, verbatim: universally bound at every relay,
    and the [Q] hole reaches only [entry]).  [kxp_image_ok pb (us_M U')]
    -- [uimg_sub (elf_image (kxp_bytes pb)) (us_M U')] -- is therefore
    stated HERE as the named upgrade target, with bridges to the U-mode
    tier's own premises ([kxp_image_init] : it implies
    [UCodeInit.init_img_sub], which is [USpecInit]'s image premise;
    [kxp_image_sh] likewise), and the gap recorded: landing it in the post
    needs EITHER a second exit-generic sweep widening the hole to
    [Q' : mword 64 -> gmap Z (bv 8) -> Prop] (mechanical, the same 31
    sites, priced like the first sweep) OR stage C's M-threading of the
    kexec cone (namei-pinned-lookup.md sect. 14: [proc_ptm] through
    [kxc_grow_inv]; ProofKexecB2's loadseg reseal already NAMES the
    delivered bytes one line before folding them away).  Neither is this
    statement lane's to take.

    ---- THE HONEST CONCURRENCY STORY (why there is NO lost arm) ---------

    The old contract's post was a DISJUNCTION: the pinned result, or the
    landed result beside [kxp_lost] -- an unforgeable receipt that a
    concurrent writer CANCELLED one of the two lends.  That arm existed
    because the pins were resources (cancellable borrows of the payload
    column), and a resource carried across the walk can be invalidated
    mid-walk, so the statement had to account for the race even though no
    era-0 run can reach it.

    The ported pins are NOT resources and cannot be cancelled.  The pin
    premise here is [kxp_view_pin]: a PERSISTENT reader that, at ANY
    instant the walk opens the authority, reads the SAME eternal pure
    fact off whatever view the authority then holds.  Nothing is carried
    from one instant to the next -- each read stands alone -- so there is
    nothing a writer can invalidate and no receipt to hand out: the
    success arm is unconditional.  The stability question has not
    vanished; it has moved to where it belongs, the PREMISE's producer:
    whoever supplies [kxp_view_pin] is asserting that the authority stays
    at a pin-satisfying view for the duration, which at era-0 boot is the
    literal situation (the first process is being built; no other process
    exists to run a write) and in general is the tree layer's
    cross-syscall exclusivity fact (the lane-A(iii) ruling: "cross-syscall
    stability is the tree layer's exclusivity fact, not an in-logic
    cancellable share").  [era0_view] is the era-0 shape of that
    certificate, and [kxp_view_pin_era0_init] is the discharge.

    ---- SCOPE: ABSOLUTE PATHS -------------------------------------------

    The contract takes [pfun 0 = SLASH]: the pins are stated from
    [FsImg.ROOTINO], and an absolute path is the one spelling whose start
    inum a caller can name.  init.c's second exec is the RELATIVE "sh";
    its walk starts at [idup(p->cwd)], whose inum no landed reading
    exposes (SpecNameiTr's Q-c).  The landed answer shape is
    [FsAbsStart.ep_start]'s deferral -- the premise travels down
    quantified over the start inum, fired where the walk learns it -- and
    the relative twin of this contract is that one premise swap (an R10
    parallel form), gated on a cwd-inum reading or on firing the deferred
    form at the cwd package.  Recorded, not taken: "/init" is absolute,
    and the sibling lane's sh pins are ROOTINO-rooted either way.

    ---- MILESTONE J SCOPING (the seam, so it is not rediscovered) -------

    Milestone J's park slot deliberately carries NO image-naming fact this
    contract could speak instead of stating its own: (R-b) the park
    channel's captured row is the GENERIC family [forall W, uslot W]
    precisely because forkret's boot arm runs kexec BETWEEN the park and
    the resume (a key captured at the park is stale by the closer); and
    (R-c) on the exec ecall arm [uround_ok]'s left disjunct says NOTHING
    -- exec-success is a KERNEL MINT ([cond_entry_slot] at
    [uvis_of U']).  So J CONSUMES what this contract produces: the
    boot-arm mint (and later the loop's exec-arm mint) justifies minting
    the slot at the pinned program's [uvis] from [Q_pin]'s entry fact --
    epc = the pinned entry -- plus, once the image hole lands,
    [kxp_image_ok (us_M U')] for the slot's text premise.  Until then the
    U-mode side keeps taking [init_img_sub] as an assumption at its own
    boundary ([USpecInit]), exactly as today.                             *)

(* ---- SpecKexec.v's Require block, VERBATIM (the frame's home), with the
   pin-side cluster spliced in before the tail -- SpecSysMknodAU.v's
   proven combination order (machine frame first, fs-abs stack late,
   [Require FsImg] qualified, Xv6G/FsCfg/TsoCtx last). ---- *)
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
Require Import KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import WpUart.
Require Import DiskInv.
Require Import Xv6Cameras.
Require Import LogInv.
Require Import LogDefs.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import DirViewG.    (* Require Export's DirViewG: [fv_of] *)
Require Import KvmSpec.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecDirlink.
(* ---- the pin-side cluster ---- *)
Require Import BioDefs.         (* [BSIZE]                                   *)
Require Import DinodeEnc.       (* [dinode], [di_size]                       *)
Require Import InodeDefs.       (* [file_byte]                               *)
Require Import InodeLock.       (* [inode_ok] -- the ilock payload's bundle  *)
Require Import PathElems.       (* [SLASH], [path_elems]                     *)
Require Import DirentEnc.       (* [bview]                                   *)
Require Import FsTree.          (* [fname], [file_bytes]                     *)
Require FsImg.                  (* [FsImg.ROOTINO : Z] -- Require, NOT Import
                                   at syscall altitude (fs-syscall-specs
                                   lane W's recorded gotcha)                 *)
Require Import FsStateEra.      (* [era_node], [era_node_rec], [era_node_data] *)
Require Import FsDurSnap.       (* [snap_ok]                                 *)
Require Import SpecReadi.       (* [rd_delivered] -- the readi window        *)
Require Import SpecKexec.       (* the landed frame this file parallels      *)
Require Import KexecOkQ.        (* [kexec_ok_q], [kxq_entry], [kxq_hdr_ok],
                                   [kexec_closer] -- the hole and its relay  *)
Require Import ElfEnc.          (* [eh_entry]                                *)
Require Import FsAbs.           (* LAST of the fs-abs stack (its own rule):
                                   [aview], [anode], [abs_of], [apath_at],
                                   [astate], [nview]; Require Export FsState *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Gamma              *)
Require Import FsInitPin.       (* [era0_D], [INIT_INO], [init_path],
                                   [init_bytes]                              *)
Require Import FsInitPinBoot.   (* [era0_pins], [era0_pins_of_snap]          *)
Require Import ElfFile.         (* [elf_image] -- the ELF decode             *)
Require Import UmodeAbi.        (* [uimg_sub]                                *)
Require Import UCodeInit.       (* [init_img_sub] -- USpecInit's premise     *)
Require Import UCodeSh.         (* [sh_img_sub]                              *)
Require Import ElfUser.         (* [init_elf], [sh_elf], length/entry facts  *)
From User Require Import InitData ShData.   (* [initEntry], [shEntry]       *)
(* ---- SpecKexec.v's tail, verbatim ---- *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* [FsImgCheck]/[FsInitPin]'s [vm_eq]: build the cast directly, so the
   reduction is paid once, at [Qed] (claude-notes/optimization.md). *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

(* ===================================================================== *)
(*  1.  THE PIN PACK: a pinned program, as data                           *)
(* ===================================================================== *)

(*  Everything below is generic in this record, which is what "sh
    PARAMETERIZED" means: the sibling lane's pins plug in by building a
    [kx_pin] and supplying [kxp_pins]-shaped facts -- no inum, no path
    and no byte list is hardcoded anywhere but in the two era-0
    INSTANCES of section 5.                                               *)
Record kx_pin := MkKxPin {
  kxp_path  : list fname;      (* the path's elements (["init"], ["sh"])  *)
  kxp_ino   : Z;               (* the inum the path pins                  *)
  kxp_bytes : list (bv 8);     (* the file's bytes -- the pinned ELF      *)
}.

(*  The header as a byte reader ([ElfEnc]'s field readers take a
    [nat -> bv 8]); only offsets below 64 are ever read through it.       *)
Definition kxp_ef (pb : kx_pin) : nat -> bv 8 := fun j => kxp_bytes pb !!! j.

(*  The entry word: e_entry, bytes 24..31 little-endian, at the 64-bit
    width -- spelled through [eh_entry] and definitionally equal to
    [KexecOkQ.kxq_entry] of the pinned header ([kxp_entry_kxq]), which is
    EXACTLY the word ProofKexecD's commit block produces.                 *)
Definition kxp_entry (pb : kx_pin) : mword 64 :=
  (Z_to_bv 64 (eh_entry (kxp_ef pb)) : mword 64).

Lemma kxp_entry_kxq (pb : kx_pin) : kxp_entry pb = kxq_entry (kxp_ef pb).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2.  Q_pin -- THE VALUE THE HOLE IS PLUGGED WITH                       *)
(* ===================================================================== *)

(*  The salvaged [SpecKexecPinned.kxp_entry_ok], generalized from the
    /init literal to the pack.  This is the REAL [Q] the contract's post
    runs [kexec_ok_q] at; the thirty-one landed relays carry it with no
    restatement because they are generic in [Q] (the exit-generic sweep). *)
Definition kxp_entry_ok (pb : kx_pin) (e : mword 64) : Prop :=
  e = kxp_entry pb.

Notation Q_pin := kxp_entry_ok (only parsing).

(*  THE ONE PAYING SITE'S DISCHARGE.  [ProofKexecD.kxd_kexec_ok] (through
    [ProofKexec.kxc_cd]) takes the premise [Q (kxq_entry ef)] -- [ef] the
    header the walk read.  Under the phase-A header claim ("these are the
    pinned bytes' first 64") it is this lemma.                            *)
Lemma Q_pin_of_hdr (pb : kx_pin) (ef : nat -> bv 8) :
  kxq_hdr_ok (Some (kxp_ef pb)) ef -> kxp_entry_ok pb (kxq_entry ef).
Proof.
  intros H. rewrite /kxp_entry_ok kxp_entry_kxq.
  exact (kxq_entry_of_hdr (kxp_ef pb) ef H).
Qed.

(*  THE WEAKENING TO THE LANDED RELATION -- the [Q := True] projection,
    which is [KexecOkQ]'s own row applied.                                *)
Lemma kexec_ok_pin_weaken (pb : kx_pin) (V V' : pprivate)
    (r entry spv szv' : mword 64) (na : nat) (alen : nat -> nat) :
  kexec_ok_q (kxp_entry_ok pb) V V' r entry spv szv' na alen ->
  kexec_ok V V' r entry spv szv' na alen.
Proof. apply kexec_ok_q_weaken. Qed.

(*  THE SENTENCE, read off the relation: failed and untouched, or resumed
    at the pinned entry with argc in a0 and the three trapframe words
    written ([kxc_tf] puts [entry] in epc and [spv] in sp/a1).            *)
Lemma kexec_ok_pin_read (pb : kx_pin) (V V' : pprivate)
    (r entry spv szv' : mword 64) (na : nat) (alen : nat -> nat) :
  kexec_ok_q (kxp_entry_ok pb) V V' r entry spv szv' na alen ->
  (r = (mword_of_int (-1) : mword 64) /\ V' = V)
  \/ (entry = kxp_entry pb
      /\ r = (mword_of_int (Z.of_nat na) : mword 64)
      /\ kxc_tf (pv_tf V) (pv_tf V') entry spv).
Proof.
  intros [Hl | H]; [by left | right].
  destruct H as (HQ & Hr & _ & _ & _ & _ & _ & Htf & _).
  split; [exact HQ | split; [exact Hr | exact Htf]].
Qed.

(* ===================================================================== *)
(*  3.  THE PURE PIN FACTS, AND THE BRIDGE KIT                            *)
(* ===================================================================== *)

(*  What a pin-satisfying view says: the path resolves from the root to
    the pinned inum, and that inum's row is a regular file holding the
    pinned bytes (nlink existential -- content is what the loader reads). *)
Definition kxp_pins (av : aview) (pb : kx_pin) : Prop :=
  apath_at av FsImg.ROOTINO (kxp_path pb) = Some (kxp_ino pb)
  /\ (exists nl : nat,
        av !! kxp_ino pb = Some (MkAnode (AFile (kxp_bytes pb)) nl)).

(* ---- 3a.  the row, read at a node: [abs_of n = AFile bs row] pins the
   node's byte reading.  At VARIABLES (FsInitPin sect. 3's rule); the
   instances never [injection] a literal. ---- *)
Lemma abs_of_file_read (n : fs_node) (bs : list (bv 8)) (nl : nat) :
  abs_of n = MkAnode (AFile bs) nl -> fn_file_bytes n = bs.
Proof.
  intros H.
  assert (Hn : abs_node n = AFile bs) by exact (f_equal an_node H).
  revert Hn. rewrite /abs_node.
  destruct (fn_is_dir n).
  - intros Hc. discriminate Hc.
  - case_decide; intros Hc; [| discriminate Hc].
    injection Hc. intros Hb. exact Hb.
Qed.

(* ---- 3b.  the payload tie: on an ilock payload's node ([era_node dn bm
   data], with the payload's own [inode_ok] bundle), the node's byte
   reading IS [fv_of dn data] -- the FILE sibling of
   [FsAbsSeam.dv_of_dir_entries], stated over the same premise. ---- *)
Lemma fv_of_file_bytes_era (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov logstart dn bm data ->
  fn_file_bytes (era_node dn bm data) = fv_of dn data.
Proof.
  intros (_ & _ & _ & _ & Hsz & Hh & _).
  pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as H0.
  assert (Hcap : (Z.to_nat (bv_unsigned (di_size dn)) <= MAXFILE * BSIZE)%nat).
  { apply Nat2Z.inj_le. rewrite (Z2Nat.id _ H0) Nat2Z.inj_mul. exact Hsz. }
  rewrite /fn_file_bytes /fn_size era_node_rec /fv_of /file_bytes.
  apply list_eq. intros k. rewrite !list_lookup_fmap.
  destruct (seq 0 (Z.to_nat (bv_unsigned (di_size dn))) !! k) as [x |] eqn:E;
    [| reflexivity].
  apply lookup_seq in E as [-> Hlt]. simpl. f_equal.
  rewrite /file_byte. f_equal.
  apply era_node_data; [exact Hh |].
  apply Nat.Div0.div_lt_upper_bound. lia.
Qed.

(*  ...and the composition the oracle wants: pinned row + payload = the
    payload's contents ARE the pinned bytes. *)
Lemma kxp_era_bytes (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) (bs : list (bv 8)) (nl : nat) :
  inode_ok cov logstart dn bm data ->
  abs_of (era_node dn bm data) = MkAnode (AFile bs) nl ->
  fv_of dn data = bs.
Proof.
  intros Hok Habs.
  rewrite -(fv_of_file_bytes_era cov logstart dn bm data Hok).
  exact (abs_of_file_read _ _ _ Habs).
Qed.

(* ---- 3c.  the readi window, against the byte list -- the salvage of
   SpecKexecPinned sect. 3, verbatim and still at variables. ---- *)
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

Lemma rd_delivered_pinned (dn : dinode) (data : nat -> list (bv 8))
    (dst_olds : nat -> bv 8) (b : list (bv 8)) (tot i : nat) :
  fv_of dn data = b -> (tot <= length b)%nat -> (i < tot)%nat ->
  rd_delivered data dst_olds 0 tot i = b !!! i.
Proof.
  intros Hb Htot Hi. rewrite /rd_delivered.
  destruct (decide (i < tot)%nat) as [_ | Hno]; [| lia].
  rewrite Nat.add_0_l. apply (fv_of_file_byte dn data b i Hb). lia.
Qed.

(*  THE ONE THE WALK QUOTES: the 64-byte header read at offset 0 lands on
    the pinned header. *)
Lemma kxp_rd_hdr (pb : kx_pin) (dn : dinode) (data : nat -> list (bv 8))
    (dst_olds : nat -> bv 8) (i : nat) :
  fv_of dn data = kxp_bytes pb ->
  (64 <= length (kxp_bytes pb))%nat -> (i < 64)%nat ->
  rd_delivered data dst_olds 0 64 i = kxp_ef pb i.
Proof.
  intros Hb Hlen Hi. rewrite /kxp_ef.
  apply (rd_delivered_pinned dn data dst_olds (kxp_bytes pb) 64 i Hb Hlen Hi).
Qed.

(* ---- 3d.  the header claim, in the ORACLE's own spelling.  Phase A's
   oracle ([ProofKexecA.kxc_a2]'s premise, post-sweep) answers with
   [kxq_hdr_ok HD (fun j => file_byte data j)]; the walk transports it to
   the frame's named header with the landed [kxq_hdr_ok_ext]
   (ProofKexecA.v:1564).  This is the pinned verdict's whole content. ---- *)
Lemma kxp_hdr_of_fv (pb : kx_pin) (dn : dinode) (data : nat -> list (bv 8)) :
  fv_of dn data = kxp_bytes pb ->
  (64 <= length (kxp_bytes pb))%nat ->
  kxq_hdr_ok (Some (kxp_ef pb)) (fun j => file_byte data j).
Proof.
  intros Hb Hlen. cbn. intros j Hj.
  rewrite /kxp_ef. apply (fv_of_file_byte dn data (kxp_bytes pb) j Hb). lia.
Qed.

(* ===================================================================== *)
(*  4.  THE VIEW PREMISE (the contract's pin resource)                    *)
(* ===================================================================== *)

Section KexecPinView.
  (* [FsAbs.v]'s carrier binder list, verbatim ([fsLinkG]/[fsTopG] are
     [xv6G] members; this section binds the members, never the bundle). *)
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (*  THE PREMISE.  A persistent reader: whenever the walk holds the
      authority -- inside ftopN, at a hop fire, at the ilock instant --
      the view it reads satisfies the pins.  Non-destructive (the
      authority is handed straight back; the conclusion is pure).

      This is the seam the TREE LAYER's exclusivity fact will discharge
      in general, and [era0_view] discharges at era-0 boot.  It is NOT
      dischargeable from a client [nview] share: the walk's own custody
      is the whole element (lane A(iii)'s machine-checked finding --
      [FsAbs.top_frag_1_nview_excl]), which is exactly why the premise
      reads the AUTHORITY and needs no client share.                     *)
  Definition kxp_view_pin Γ (pb : kx_pin) : iProp Σ :=
    (□ (∀ av : aview, astate Γ av -∗ astate Γ av ∗ ⌜kxp_pins av pb⌝))%I.

  Global Instance kxp_view_pin_persistent Γ pb :
    Persistent (kxp_view_pin Γ pb).
  Proof. rewrite /kxp_view_pin. apply _. Qed.

  (*  THE CHAIN-CARRYING READER (the repair of the multi-hop finding,
      owner-authorized 2026-08-30).  [kxp_pins] pins only the ENDPOINTS,
      and the prover machine-checked that on a path of >= 2 elements the
      endpoint-only sentence is FALSE: between hops a writer can re-route
      the interior through pin-satisfying views.  What pins a walk is the
      chain at a FIXED [ds] -- [FsAbs.arun] -- which both era-0 pin
      packages already carry.  This definition is the prover's honest
      premise lifted verbatim (ProofKexecPinTrace's original); the sealed
      Parameter below consumes it, and the endpoint form survives as the
      view premise of the one-hop corollary. *)
  Definition kxp_run_pin Γ (pb : kx_pin) (ds : list Z) : iProp Σ :=
    (⌜ds !! 0%nat = Some FsImg.ROOTINO
      /\ ds !! length (kxp_path pb) = Some (kxp_ino pb)⌝
     ∗ □ (∀ av : aview, astate Γ av -∗
            astate Γ av
            ∗ ⌜kxp_pins av pb
               /\ arun av FsImg.ROOTINO (kxp_path pb) ds⌝))%I.

  Global Instance kxp_run_pin_persistent Γ pb ds :
    Persistent (kxp_run_pin Γ pb ds).
  Proof. rewrite /kxp_run_pin. apply _. Qed.

  (*  THE ILOCK-INSTANT READER: the pinned inum's payload fragment holds
      the pinned bytes.  [dq] is arbitrary, so the whole element (the
      loaded arm) and the 3/4 residue (the read arm) both fire it.       *)
  Lemma kxp_pins_frag_bytes Γ (pb : kx_pin) (av : aview) (dq : dfrac)
      (n : fs_node) :
    kxp_pins av pb ->
    astate Γ av -∗ top_frag_q Γ dq (kxp_ino pb) n -∗
      ⌜fn_file_bytes n = kxp_bytes pb⌝.
  Proof.
    intros (_ & nl & Hrow). iIntros "Hst Hf".
    iDestruct (nview_of_frag with "Hf") as "Hn".
    iDestruct (astate_nview_dq with "Hst Hn") as %Hav.
    iPureIntro.
    rewrite Hrow in Hav. apply Some_inj in Hav. symmetry in Hav.
    exact (abs_of_file_read n (kxp_bytes pb) nl Hav).
  Qed.

End KexecPinView.

(* ===================================================================== *)
(*  5.  THE ERA-0 INSTANTIATIONS                                          *)
(* ===================================================================== *)

(* ---- 5a.  /init, off FsInitPin's constants. ---- *)
Definition pin_init : kx_pin :=
  MkKxPin FsInitPin.init_path FsInitPin.INIT_INO FsInitPin.init_bytes.

(*  [era0_pins] (FsInitPinBoot's one-name package) delivers the pins. *)
Lemma era0_kxp_pins_init (av : aview) :
  era0_pins av -> kxp_pins av pin_init.
Proof.
  intros (Hp & Hc & _).
  split; [exact Hp | exists 1%nat; exact Hc].
Qed.

(*  the pinned header exists: /init is 35976 bytes.  READ AT [Z] off
    [ElfUser.init_elf_length] -- never [vm_compute] a [length] at [nat]
    (the unary-successor stack trap, SpecKexecPinned's own note).        *)
Lemma pin_init_hdr_len : (64 <= length (kxp_bytes pin_init))%nat.
Proof.
  change (64 <= length ElfUser.init_elf)%nat.
  apply Nat2Z.inj_le. rewrite ElfUser.init_elf_length.
  vm_compute. discriminate.
Qed.

(*  the pinned entry, computed: it is [InitData.initEntry] (0xbc), the pc
    every [USpecInit] theorem starts from -- the receipt that makes the
    contract's sentence consumable by the U-mode tier.                    *)
Lemma pin_init_entry : eh_entry (kxp_ef pin_init) = InitData.initEntry.
Proof. vm_eq. Qed.

Lemma pin_init_entry_word :
  kxp_entry pin_init = (Z_to_bv 64 InitData.initEntry : mword 64).
Proof. rewrite /kxp_entry pin_init_entry. reflexivity. Qed.

(* ---- 5b.  sh, PARAMETERIZED: the path and the inum are the sibling
   lane's to supply (do not hardcode; the image says 13, the premise
   decides).  Only the BYTES are this tree's: the tracked sh ELF. ---- *)
Definition pin_sh (ps : list fname) (i : Z) : kx_pin :=
  MkKxPin ps i ElfUser.sh_elf.

Lemma pin_sh_hdr_len (ps : list fname) (i : Z) :
  (64 <= length (kxp_bytes (pin_sh ps i)))%nat.
Proof.
  change (64 <= length ElfUser.sh_elf)%nat.
  apply Nat2Z.inj_le. rewrite ElfUser.sh_elf_length.
  vm_compute. discriminate.
Qed.

Lemma pin_sh_entry (ps : list fname) (i : Z) :
  eh_entry (kxp_ef (pin_sh ps i)) = ShData.shEntry.
Proof. vm_eq. Qed.

Lemma pin_sh_entry_word (ps : list fname) (i : Z) :
  kxp_entry (pin_sh ps i) = (Z_to_bv 64 ShData.shEntry : mword 64).
Proof. rewrite /kxp_entry pin_sh_entry. reflexivity. Qed.

(* ---- 5c.  the era-0 producer of the view premise. ---- *)
Section KexecPinEra0.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (*  THE ERA-0 CERTIFICATE: the authority reads as an era-0 snapshot
      view.  This is the exclusivity seam, NAMED: at forkret's boot arm
      it is the literal situation (the fs was founded moments ago at the
      snapshot's own table -- [FsCfgSnap] founds gamma-top at
      [fss_inodes S] -- and no other process exists to move it before
      kexec returns); its in-logic producer is the tree layer's
      cross-syscall exclusivity fact, still owed there.  Nothing in this
      file claims to prove it.                                           *)
  Definition era0_view Γ : iProp Σ :=
    (□ (∀ av : aview, astate Γ av -∗
          astate Γ av
          ∗ ⌜∃ S : fs_state_rec,
               snap_ok S era0_D /\ av = abs_view (fss_inodes S)⌝))%I.

  Global Instance era0_view_persistent Γ : Persistent (era0_view Γ).
  Proof. rewrite /era0_view. apply _. Qed.

  (*  the generic step: era-0 pure pins + the certificate = the view
      premise.  [pb]'s facts arrive as a hypothesis, which is exactly how
      the sibling lane's sh pins plug in.                                *)
  Lemma kxp_view_pin_era0 Γ (pb : kx_pin) :
    (forall S : fs_state_rec,
        snap_ok S era0_D -> kxp_pins (abs_view (fss_inodes S)) pb) ->
    era0_view Γ -∗ kxp_view_pin Γ pb.
  Proof.
    intros Hpin. rewrite /era0_view /kxp_view_pin.
    iIntros "#Hv !>" (av) "Hst".
    iDestruct ("Hv" $! av with "Hst") as "[Hst %Hs]".
    destruct Hs as (S & HS & ->).
    iFrame "Hst". iPureIntro. exact (Hpin S HS).
  Qed.

  (*  ...and /init's instance, off lane P's pins.  The consumer owes only
      the era-0 disk equation (through [era0_pins]' own producers,
      [FsInitPinBoot.era0_boot_pins] / [era0_recovery_pins]) plus the
      certificate above.                                                 *)
  Lemma kxp_view_pin_era0_init Γ :
    era0_view Γ -∗ kxp_view_pin Γ pin_init.
  Proof.
    apply kxp_view_pin_era0. intros S HS.
    exact (era0_kxp_pins_init _ (era0_pins_of_snap S HS)).
  Qed.

End KexecPinEra0.

(* ===================================================================== *)
(*  6.  THE PINNED IMAGE (the upgrade target, defined and bridged)        *)
(* ===================================================================== *)

(*  "The loaded segments are the ELF decode of the pinned bytes", at the
    lazy view: [elf_image] is the general ELF64 semantics' loaded image
    (file-backed windows plus the zeroed bss), and [uimg_sub] is the
    U-mode tier's own inclusion.  CANNOT ride [kexec_ok_q]'s hole today
    (header, "THE UPGRADE GAP"); it is defined here so the seam has ONE
    name on both sides of that gap.                                       *)
Definition kxp_image_ok (pb : kx_pin) (M : gmap Z (bv 8)) : Prop :=
  uimg_sub (elf_image (kxp_bytes pb)) M.

(* inclusion algebra for the union folds [elf_image] produces *)
Lemma uimg_sub_union_l (m1 m2 M : gmap Z (bv 8)) :
  uimg_sub (m1 ∪ m2) M -> uimg_sub m1 M.
Proof.
  intros H a b Hb. apply H. by apply lookup_union_Some_l.
Qed.

(*  the right leg is reached through a COMPUTED commutation of the two
    dumped maps rather than a disjointness side condition: gmap equality
    is decidable, so the fact is one [vm_eq] against the literal dumps
    and no set reasoning happens at an image-consumer's altitude (the
    FsInitPinBoot [set_solver] gotcha).                                   *)
Lemma init_union_comm_bool :
  bool_decide (InitInstrs.init_bytes ∪ InitData.init_data
               = InitData.init_data ∪ InitInstrs.init_bytes) = true.
Proof. vm_eq. Qed.

Lemma sh_union_comm_bool :
  bool_decide (ShInstrs.sh_bytes ∪ ShData.sh_data
               = ShData.sh_data ∪ ShInstrs.sh_bytes) = true.
Proof. vm_eq. Qed.

(*  THE /init BRIDGE: the pinned image delivers [UCodeInit.init_img_sub],
    which is [USpecInit]'s image premise -- so when the gap closes, the
    verified /init runs on provably its own text with no assumption left
    at the U-mode boundary. *)
Lemma kxp_image_init (M : gmap Z (bv 8)) :
  kxp_image_ok pin_init M -> init_img_sub M.
Proof.
  rewrite /kxp_image_ok /pin_init /= /init_bytes.
  intros H. rewrite ElfUser.init_elf_image in H.
  split.
  - exact (uimg_sub_union_l _ _ _ (uimg_sub_union_l _ _ _ H)).
  - pose proof (uimg_sub_union_l _ _ _ H) as Hfd.
    intros a b Hb. apply Hfd.
    rewrite (bool_decide_eq_true_1 _ init_union_comm_bool).
    by apply lookup_union_Some_l.
Qed.

(*  ...and sh's, symmetric. *)
Lemma kxp_image_sh (ps : list fname) (i : Z) (M : gmap Z (bv 8)) :
  kxp_image_ok (pin_sh ps i) M -> sh_img_sub M.
Proof.
  rewrite /kxp_image_ok /pin_sh /=.
  intros H. rewrite ElfUser.sh_elf_image in H.
  split.
  - exact (uimg_sub_union_l _ _ _ (uimg_sub_union_l _ _ _ H)).
  - pose proof (uimg_sub_union_l _ _ _ H) as Hfd.
    intros a b Hb. apply Hfd.
    rewrite (bool_decide_eq_true_1 _ sh_union_comm_bool).
    by apply lookup_union_Some_l.
Qed.

(* ===================================================================== *)
(*  7.  THE CONTRACT                                                      *)
(* ===================================================================== *)

(*  A caller that only wants the LANDED guarantee feeds its landed-shaped
    continuation through this: the pinned relation is stronger, so the
    conversion is the pointwise weakening and nothing else.  Generic in
    [Q] (it morally belongs in KexecOkQ; it lives here because landed
    files do not move -- fuse when KexecOkQ.v is next edited).

    Binder list = [kexec_closer]'s own, INCLUDING its pavG warning: do
    not add [pavG] here and do not drop a class (KexecOkQ.v's header has
    the measured failure modes).                                          *)
Lemma kexec_closer_weaken `{XI : TsoCtx.CurCtx}
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Q : mword 64 -> Prop)
    (gf ga : gname) (pj : mword 64) (pidv : mword 32) (U : ustate)
    (m : regfile) (ret_tgt : mword 64) (K : nat) (b eb : bool)
    (lks : gset string) (dqb dqs : dfrac) (bmapstart : Z)
    (na : nat) (alen : nat -> nat)
    (plen : nat) (pv : mword 64) (dqpv : dfrac) (pfun : nat -> bv 8)
    (av : mword 64) (dqa : dfrac) (avf : nat -> mword 64)
    (aslen : nat -> nat) (dqas : dfrac) (afun : nat -> nat -> bv 8) :
  kexec_closer (fun _ : mword 64 => Logic.True) gf ga pj pidv U m ret_tgt K b
               eb lks dqb dqs
               bmapstart na alen plen pv dqpv pfun av dqa avf aslen dqas afun
  -∗
  kexec_closer Q gf ga pj pidv U m ret_tgt K b eb lks dqb dqs
               bmapstart na alen plen pv dqpv pfun av dqa avf aslen dqas afun.
Proof.
  rewrite /kexec_closer.
  iIntros "H" (mf U' entry spv szv') "%Hcs %Hok Hsie Hcpu Htc Hcc Hpc Hbm
    Hin Hka Hpp Hpa Hav Has Hbs Hir".
  iApply ("H" $! mf U' entry spv szv'
            with "[%] [%] Hsie Hcpu Htc Hcc Hpc Hbm Hin Hka Hpp Hpa Hav
                  Has Hbs Hir").
  - exact Hcs.
  - apply kexec_ok_q_of_True.
    exact (kexec_ok_q_weaken Q _ _ _ _ _ _ _ _ Hok).
Qed.

(*  THE BODY: [SpecKexec.wp_kexec_sconf_body] VERBATIM -- same machine
    premises, same fabric, same budget, same eb-generic shape -- plus
    exactly:
      (i)   the pack parameter [pb];
      (ii)  three pure premises scoping the call to the pinned path (the
            buffer is absolute; it spells [kxp_path pb]; the pinned file
            has a whole header);
      (iii) one persistent resource premise, [kxp_view_pin];
      (iv)  the post at [kexec_ok_q (Q_pin pb)] -- spelled as
            [kexec_closer (Q_pin pb)], which IS the landed continuation
            shape at that [Q] (KexecOkQ sect. 1a, transparent), so every
            phase lemma's relay applies to it unchanged.                  *)
Definition wp_kexec_pinned_view_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (pb : kx_pin)
    (gs : list gname) (jp : nat) (gl : gname)           (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (gf : gname)                                        (* file table          *)
    (plen : nat) (pfun : nat -> bv 8)                   (* the path buffer     *)
    (na : nat) (avf : nat -> mword 64)                  (* argv[0 .. na]       *)
    (alen : nat -> nat) (aslen : nat -> nat)            (* strlen / owned len  *)
    (afun : nat -> nat -> bv 8)                         (* the argument bytes  *)
    (pidv : mword 32) (U : ustate)
    (dqb dqs dqa dqpv dqas : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kexec in
  let pj := proc_addr jp in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let av := m !!! Regidx (mword_of_int 11 : mword 5) in   (* a1 = argv *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kexec <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* ---- the path ---- *)
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ---- AND THE PATH IS THE PINNED ONE ----
     absolute (the pins are stated from the root; the relative twin is
     the recorded [FsAbsStart]-shaped parallel form) and spelling exactly
     the pinned elements.  A caller holding the .rodata literal
     discharges both by computation, as the dead contract's callers did. *)
  pfun 0%nat = SLASH ->
  path_elems (bview plen pfun) = kxp_path pb ->
  (* ---- and the pinned file has a whole ELF header: without this the
     oracle's verdict about the first 64 bytes would be unprovable (a
     shorter pinned file makes the header readi short -- a run the
     machine sends to [bad:], but the verdict is produced before the
     length test).  [pin_init_hdr_len]/[pin_sh_hdr_len] discharge it. *)
  (64 <= length (kxp_bytes pb))%nat ->
  (* ---- the argument vector: [na] non-null pointers then a NULL ---- *)
  (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
  avf na = (mword_of_int 0 : mword 64) ->
  (na < MAXARG)%nat ->
  (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
  (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
  (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
  (* ---- the running process ---- *)
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  fs_fabric gs pd pav pu -∗
  kalloc_env fsc_kalloc None -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  proc_priv gf pj pidv U -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
  ([∗ list] i ∈ seq 0 na,
     [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  (* ==== THE PIN: one persistent reader (section 4).  Persistent, so it
     costs the caller nothing to duplicate into the walk. ==== *)
  kxp_view_pin (fs_gamma_L fsc_fs) pb -∗
  (* ==== the moved image, at the PINNED relation.  [kexec_closer
     (Q_pin pb) ...] unfolds to the landed continuation verbatim with
     [kexec_ok_q (Q_pin pb)] in the pure slot: the [-1] arm is the landed
     failure arm character for character, and the success arm carries
     [entry = kxp_entry pb] in front ([kexec_ok_pin_read]). ==== *)
  wp_next true pj (fun (CID : CpuId) =>
    kexec_closer (kxp_entry_ok pb) gf fsc_kalloc pj pidv U m ret_tgt K b eb
                 lks dqb dqs fsc_bmapstart na alen plen pv dqpv pfun
                 av dqa avf aslen dqas afun) -∗
  WP (Loop : expr riscv_lang).

(*  THE SEALED FORM: the same body at the chain-carrying reader.  *)
Definition wp_kexec_pinned_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (pb : kx_pin) (ds : list Z)
    (gs : list gname) (jp : nat) (gl : gname)           (* the running process *)
    (pd pav pu : mword 64)                              (* disk fabric + lock  *)
    (gf : gname)                                        (* file table          *)
    (plen : nat) (pfun : nat -> bv 8)                   (* the path buffer     *)
    (na : nat) (avf : nat -> mword 64)                  (* argv[0 .. na]       *)
    (alen : nat -> nat) (aslen : nat -> nat)            (* strlen / owned len  *)
    (afun : nat -> nat -> bv 8)                         (* the argument bytes  *)
    (pidv : mword 32) (U : ustate)
    (dqb dqs dqa dqpv dqas : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kexec in
  let pj := proc_addr jp in
  let pv := m !!! Regidx (mword_of_int 10 : mword 5) in   (* a0 = path *)
  let av := m !!! Regidx (mword_of_int 11 : mword 5) in   (* a1 = argv *)
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_kexec <= K)%nat ->
  icfg_dev = ROOTDEV ->
  (0 < icfg_nib)%nat ->
  log_geom_ok fsc_cov fsc_logst ->
  0 < fsc_size <= BPB ->
  0 <= fsc_bmapstart ->
  fsc_bmapstart ∈ fsc_cov ->
  ~ (fsc_bmapstart ∈ log_region_set fsc_logst) ->
  0 <= icfg_ist ->
  cov_below fsc_cov fsc_size ->
  ireg_blocks_ok icfg_ist icfg_nib fsc_cov fsc_logst ->
  (* ---- the path ---- *)
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (* ---- AND THE PATH IS THE PINNED ONE ----
     absolute (the pins are stated from the root; the relative twin is
     the recorded [FsAbsStart]-shaped parallel form) and spelling exactly
     the pinned elements.  A caller holding the .rodata literal
     discharges both by computation, as the dead contract's callers did. *)
  pfun 0%nat = SLASH ->
  path_elems (bview plen pfun) = kxp_path pb ->
  (* ---- and the pinned file has a whole ELF header: without this the
     oracle's verdict about the first 64 bytes would be unprovable (a
     shorter pinned file makes the header readi short -- a run the
     machine sends to [bad:], but the verdict is produced before the
     length test).  [pin_init_hdr_len]/[pin_sh_hdr_len] discharge it. *)
  (64 <= length (kxp_bytes pb))%nat ->
  (* ---- the argument vector: [na] non-null pointers then a NULL ---- *)
  (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
  avf na = (mword_of_int 0 : mword 64) ->
  (na < MAXARG)%nat ->
  (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
  (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
  (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
  (* ---- the running process ---- *)
  (jp < NPROC)%nat ->
  gs !! jp = Some gl ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  fs_fabric gs pd pav pu -∗
  kalloc_env fsc_kalloc None -∗
  sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
  sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
  bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size -∗
  proc_priv gf pj pidv U -∗
  ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
  ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
  ([∗ list] i ∈ seq 0 na,
     [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
  bslots 3 -∗
  iref_slots 2 -∗
  (* ==== THE PIN: one persistent reader (section 4).  Persistent, so it
     costs the caller nothing to duplicate into the walk. ==== *)
  kxp_run_pin (fs_gamma_L fsc_fs) pb ds -∗
  (* ==== the moved image, at the PINNED relation.  [kexec_closer
     (Q_pin pb) ...] unfolds to the landed continuation verbatim with
     [kexec_ok_q (Q_pin pb)] in the pure slot: the [-1] arm is the landed
     failure arm character for character, and the success arm carries
     [entry = kxp_entry pb] in front ([kexec_ok_pin_read]). ==== *)
  wp_next true pj (fun (CID : CpuId) =>
    kexec_closer (kxp_entry_ok pb) gf fsc_kalloc pj pidv U m ret_tgt K b eb
                 lks dqb dqs fsc_bmapstart na alen plen pv dqpv pfun
                 av dqa avf aslen dqas afun) -∗
  WP (Loop : expr riscv_lang).

Module Type KEXEC_PIN.
  Parameter wp_kexec_pinned :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (pb : kx_pin) (ds : list Z)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen aslen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_kexec_pinned_body pb ds gs jp gl pd pav pu gf plen pfun na avf
                           alen aslen afun pidv U dqb dqs dqa dqpv dqas m
                           K eb b lks.
End KEXEC_PIN.

(* ===================================================================== *)
(*  8.  WHAT THE PROVER OWES (the assembly map, so it is priced once)     *)
(* ===================================================================== *)

(*  The proof is [ProofKexec.wp_kexec_sconf]'s own composition run at
    [Q := Q_pin pb] instead of [QT] -- the cone is generic in [Q] since
    the exit-generic sweep, so the failure tails and phases B/B2/B3/C/D
    apply UNCHANGED.  What is genuinely owed:

    (1) THE PAYING SITE.  [ProofKexec.kxc_cd]'s premise [Q (kxq_entry ef)]
        is discharged by [Q_pin_of_hdr] from the phase-A header claim,
        which rides the +0x090 seam exactly as the sweep built it:
        instantiate [HD := Some (kxp_ef pb)] (the landed run passes
        [None]) and [XCH := False] -- there is no lost arm to escape to,
        which is the point of section 4's premise shape.

    (2) THE ORACLE'S DISCHARGE, and its one seam finding.  Phase A's
        oracle premise (ProofKexecA.v:1847, post-sweep) hands the caller
        the payload's [fv_ride zi (fv_of dn data)] ALONE and asks for
        [kxq_hdr_ok HD (fun j => file_byte data j)] back at mask ⊤.  The
        pinned verdict is [kxp_hdr_of_fv] fired at
        [fv_of dn data = kxp_bytes pb] -- and THAT tie must come from the
        authority ([kxp_view_pin] + [kxp_pins_frag_bytes] +
        [kxp_era_bytes], opened through ftopN inside the oracle's fupd)
        via the payload's TOP FRAG, which the ride-only oracle does not
        carry: the fv ghost has no tie to gamma-top outside the payload.
        So the prover either (a) widens the oracle premise to
        [fv_ride ... ∗ top_frag_q ...] -- a kexec-internal, self-canceling
        edit of ProofKexecA's two oracle rows, the same authorization
        class as the sweep's B2/B3 seam bodies -- or (b) re-derives
        [kxc_a2] pinned (the copy the oracle existed to avoid).  Price
        (a) first.

    (3) THE NAMEI TRACE ([zi = kxp_ino pb]).  The landed functor argument
        is the traceless [SpecNamei.wp_namei_gen]; the pinned walk needs
        the era-traced twin ([SpecNameiEra] + [FsAbsStart.ex_start]) with
        the caller's [P k d := ⌜d = the pinned chain's k-th inum⌝], each
        hop fired by opening ftopN inside the hop's ⊤-fupd:
        [kxp_view_pin] reads [kxp_pins av], [FsAbsEra.elend_astate] reads
        the hop row off the same authority, and [apath_at]'s algebra
        steps the chain.  This is the old plan's "one new phase proof"
        (the pinned [kxc_a1] variant), now over the landed era walk; for
        [pin_init] the chain is [[ROOTINO; 7]] and there is ONE hop.

    (4) WHERE EACH RELAY FIRES: nowhere new.  The 31 relays are already
        [Q]-generic ([SpecKexecB2] x4, [SpecKexecB3] x2, and the phase
        proofs' [kexec_closer Q] continuations); the pinned assembly
        passes [Q_pin pb] down the same argument lists [ProofKexec]
        passes [QT] down, and only (1) pays.

    (5) THE WEAKENING, for a caller that wants the landed post from the
        pinned contract: [kexec_closer_weaken] at [Q := Q_pin pb]
        converts its continuation; the relation-level projection is
        [kexec_ok_pin_weaken].

    (6) THE PREMISE'S PRODUCER at the boot arm: [kxp_view_pin_era0_init]
        needs [era0_view] -- the era-0 exclusivity certificate.  Its
        discharge belongs to ProofForkret's boot arm together with the
        tree layer's exclusivity story (fs-syscall-specs; the boot's own
        pure pins are already free through [FsInitPinBoot.era0_boot_pins]
        given only the era-0 disk equation).  Until it lands, this
        contract composes but its era-0 instance is premise-gated --
        deliberately: that is the honest boundary, and it is ONE named
        iProp rather than a walk-shaped obligation.

    WHY NO STABILITY MACHINERY, once more and precisely: the general
    exec's image tie relates the loaded bytes to a FILE STATE that can
    move between the walk's instants, so any contract about it must
    either carry a resource across the walk (the deleted cancellable
    lends, with their receipt arm) or re-read state it can trust at each
    instant.  The pinned tie is to a LITERAL byte list, and the premise
    re-reads the eternal pure fact at every instant it is needed --
    nothing is carried, nothing can be cancelled, no receipt arm exists.
    The one assumption left standing is the premise itself, named
    [kxp_view_pin], produced at era 0 by [era0_view].                     *)
