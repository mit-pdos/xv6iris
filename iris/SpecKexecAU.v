(* SpecKexecAU.v -- exec()'s ATOMIC-UPDATE contract: the walk, ONE
   observation of the file, and -- if what was observed is a program xv6
   will load -- the caller's OWN WP for running it.  A STATEMENT FILE:
   definitions, structural lemmas, and a [Module Type] seal; no walk, no
   proof against the machine.

   Design of record: claude-notes/design/fs-syscall-specs.md (the AU
   family: sections 0-4), claude-notes/design/user-wp-slot.md (the slot
   [UexecRet.uslot] this contract's conclusion is keyed at -- through the
   SLOT PREDICATE [S] below -- and the ruled trap contract whose exec arm
   this fills), claude-notes/design/elf.md
   (the file-side ELF semantics [ElfFile.elf_image]), and the owner's
   2026-09-03 brief: "the caller must supply fupds for the pathname
   resolution and the reads of the resulting file; after those translate
   into some ELF binary, if that binary is valid the caller must provide
   the WP for starting execution of the u-mode process -- the WP the
   u-mode slot wants -- and that is how u-mode WPs chain: init proving
   the fupds for exec("sh") concludes in the WP for running sh."

   The molds are SpecSysOpenAU.v (the era walk premise, the single-phase
   whole-[anode] observation, the exclusion-by-premise pattern) and
   SpecKexecPin.v (the landed kexec frame with a file-side premise beside
   it; its [kxp_image_ok] is the image target this contract finally puts
   in a post).

   ==== WHAT THIS CONTRACT IS ==========================================

   A PARALLEL FORM beside [SpecKexec.wp_kexec_sconf] (R10: the landed
   contract does not move).  Same calling convention, same premises,
   same threaded resources -- the frame below is
   [SpecKexec.wp_kexec_sconf_body] row for row -- with THREE things
   added on the caller's side and ONE on the kernel's:

   IN (the AU bundle, [exec_au_pre]):
   1. THE WALK PREMISE, [SpecSysOpenAU.open_walk_pre_era] REUSED: kexec
      resolves the whole path with namei, exactly as open's plain arm
      does, so the one-shot that fires an [ax_hop] at the era lend per
      path element is the same statement.  A caller that knows the
      directory chain (init: "/" holds "sh" at a known inum) pins each
      hop from its own view; a caller that does not passes [True] hops.
   2. THE OBSERVATION, [SpecSysOpenAU.aopen_commit_at] REUSED: ONE
      single-phase read-only commit, fired inside the file's lock
      window, handing the caller the node kexec is about to read AS A
      WHOLE ([anode]: a file's bytes, or a directory / device that will
      fail the magic test).  See THE ONE OBSERVATION below for why this
      is one fupd and not one per readi.
   3. THE PROGRAM'S WP, [exec_slot_pre]: for every observed file [f]
      that xv6 loads ([kexec_loadable f]) and every resume key [W']
      kexec may build from it ([kexec_image_ok f na alen afun sts W']),
      the caller supplies [S W'] -- [S] a SLOT PREDICATE every form
      below is parametric in, instantiated by the dispatcher at the
      trapframe-keyed user-execution WP ([UexecRetExec.uslot_x]: the very
      proposition the trap loop deposits and runs; design note, "the two
      WP forms").  [S] is a parameter and not [uslot] because the exec
      bundle the process hands over ([UexecExecInst.exec_xbundle]) is an
      [exec_au_pre] whose slot wand concludes at the FIXPOINT VARIABLE of
      the enriched trap contract, which is what lets the kernel return
      the enriched slot rather than the plain one (UexecRetExec.v header:
      [uslot W -∗ uslot_x W] is not provable).  The caller receives its own
      observation receipt [Φo av i (AFile f)] first, so the WP it owes is
      only for the file it observed: init, whose receipt says
      [f = sh_bytes], owes only sh's start WP at sh's key.

   OUT (the arms, [exec_arms]):
   - ret = argc (SUCCESS).  The walk completed at [i] and the node
     observed there was [a]; then
       (a) [a] is a loadable file [f]: the landed success conjuncts hold
           at [entry = the ELF's entry of f] ([kexec_ok_exec]) and the
           kernel returns THE CALLER'S WP, applied: [S (exec_key U'
           sts na)] -- the slot at the state the process resumes in (the
           new trapframe with [a0 := argc], the new image, the new size,
           the caller's descriptor view) -- beside the pure
           [kexec_image_ok] it was instantiated at.  The receipt was
           consumed by the WP premise.
       (b) [a] is anything else and kexec succeeded anyway: a file the
           code accepts that [kexec_loadable] does not describe (see THE
           ACCEPTANCE PREDICATE), or NOT A FILE AT ALL -- kexec never
           tests the inode's type, it reads raw bytes off whatever the
           path names, so a directory whose dirent bytes begin with the
           ELF magic is exec'd (a finding of the phase-A proof,
           2026-09-04).  The landed success conjuncts hold at SOME entry,
           the receipt and the WP premise come back, and the kernel mints
           the generic slot as it does today.
   - ret = -1 (FAILURE): the landed failure arm ([V' = V]) beside the
     honest three-way fold of the bundle: (i) nothing fs-visible fired
     (begin_op/namei not reached: unspent bundle back); (ii) the walk died
     at hop [k] (the era refund shape, commit and WP back); (iii) the walk
     completed, the node was OBSERVED (the receipt is delivered), and
     exec failed past the lock -- a bad ELF, a directory or device, an
     allocation failure, an oversized argument set -- with the WP premise
     back.  A failed exec's abstract effect is NIL: kexec mutates no
     inode, so there is no delta anywhere in this contract.

   ==== THE ONE OBSERVATION (why not a fupd per readi) ==================

   kexec reads the file 1 + phnum + Σ ceil(filesz/PGSIZE) times (the
   header, each program header, each page of each segment -- the three
   static readi sites in ProofKexecA/B3/B2), and EVERY one of those reads
   happens under the ONE [ilock] kexec takes before the header read and
   releases at [iunlockput].  Under the lock the node cannot move (the
   payload's custody pins the authority's row, exactly as
   [SpecSysOpenAU]'s trunc receipt argues), so every readi returns bytes
   of the SAME [f]: the reads are deterministic functions of one observed
   value, and a per-read commit family would deliver [n] receipts of the
   same [f] at the same instant.  The linearization point of exec's READ
   side is the lock, and the contract says so with one commit.  A caller
   that wants per-read receipts derives them from [f] ([rd_bytes] is
   [file_byte] of the payload, and [FsStateInode.fn_file_bytes] reads the
   same payload) -- the prover's obligation is the single fire at the
   header oracle hook ProofKexecA already carries, generalized from
   "a header claim" to "the whole node".

   ==== THE ACCEPTANCE PREDICATE, HONESTLY ==============================

   [kexec_loadable f] is NOT the code's test.  The code checks the magic
   and, per PT_LOAD header, four arithmetic facts, and otherwise trusts
   an attacker-controlled table; a file with overlapping or descending
   segments can pass it, and its image is then NOT [ElfFile.elf_image]
   (later segments overwrite earlier ones; a descending one hits
   [loadseg]'s "address should exist" panic, which is why the ascending
   condition is in).  [kexec_loadable] is the set of files for which
   the LOADED IMAGE IS THE ELF SEMANTICS' IMAGE: [ElfFile.elf_wf] (the
   file-side well-formedness the dumps satisfy) plus the xv6-loadable
   bounds elf.md names (the two 4-byte [int] truncations kexec performs,
   page-aligned segment starts, ascending non-overlapping segments).
   Success arm (b) is the honest residue: the code CAN succeed on a file
   outside the set, and this contract then promises nothing about the
   image and keeps today's generic mint.  Tightening the set toward the
   code's test is the prover's finding to report, never a premise to
   strengthen here.

   ==== THE IMAGE, AND WHAT IS DEFERRED ================================

   [kexec_image_ok f na alen afun sts W'] states what kexec built, at the
   key the slot is stated on ([UexecSlot.uvis]):
     - the resume pc is the ELF entry (word [tf_epc_idx] of the
       trapframe; [tf_resume_pc] clears bit 0 and every entry is even);
     - the size is [kexec_sz f]: the segments' end rounded up plus the
       guard and stack pages;
     - sp and a1 are [kxc_sp_final], a0 is argc (the landed [kxc_tf]
       rows, plus the a0 the dispatcher writes on return);
     - the ELF's file image and its .bss zeros are IN the image
       ([UmodeAbi.uimg_sub (elf_image f)]);
     - THE STACK kexec allocates ON TOP of the image ([kexec_stack_at]):
       two pages above the rounded-up segment end, the lower one the
       guard [uvmclear] makes inaccessible, the upper one the initial
       stack; the arguments are pushed from its top -- argument [i]'s
       characters and NUL at [kxc_sp top alen (S i)], then the
       [na + 1]-word [ustack] vector at [kxc_sp_final], [ustack[i]] the
       address of string [i] and [ustack[na] = 0], every word
       little-endian ([kexec_args_at]); every other byte of the stack
       page reads ZERO (uvmalloc's zero fill, in the lazy view); [sp]
       and [a1] are the vector's address and [a0] is [argc] -- so
       main's [argv] is exactly that vector, which is what a slot
       constructor reads off the key through [kexec_image_ok_argv];
     - THE PERMISSIONS ([KexecBuilt.kxb_perm_ok] at [uvis_perm W']):
       every page [uvmalloc] mapped for a PT_LOAD header carries that
       header's X/W bits ([flags2perm]: X iff [flags & 1], W iff
       [flags & 2] -- the pages from the previous segment's rounded end
       up to [vaddr + memsz]), the stack page is W and not X, and the
       guard page, mapped with U cleared, is ABSENT from the projection.
       This is the code/data split the U-tier keys on: under the
       non-coherent instruction cache the only pages a program may run
       are those executable AND not writable, and a slot constructor
       reads exactly that off this row for the text segment;
     - the descriptor view is the caller's ([sts]) and the trapframe is
       [TFWORDS] long.
   NOT YET STATED, named so the follow-on is a list: (d2) the zero fill
   of the .bss-to-page-end tail and of the guard page's reading; (d3)
   [p->name].  Each is a pure conjunct on [W'], added without moving any
   shape.

   ==== LOADABLE MEANS SUCCESS, MODULO MEMORY ===========================

   The failure arm past the lock (arm (iii)) names its CAUSE
   ([exec_fail_cause]): the node was not a loadable file, or the
   arguments did not fit the stack page ([kxc_stack_ok] false), or an
   allocation failed (a kalloc / uvmalloc / proc_pagetable exhaustion).
   The pool is uncounted, so memory exhaustion has no pure witness; what
   keeps [EfNoMem] from being a blanket excuse is ORDER: every allocation
   kexec performs comes after the ELF magic test, so a memory failure
   implies the node's bytes -- if it was a file -- passed THE KERNEL'S
   test ([kexec_magic_ok]: a header's worth of bytes whose first four
   are the magic; the code compares only those four, not the class and
   data bytes [ElfFile.elf_magic_ok] also checks) -- [exec_fail_ok]'s
   [EfNoMem] row.  A real file that failed that test, or was too short
   to hold a header, must be blamed on [EfNotLoadable], and the tails
   have the header buffer to prove it.
   So a caller that proves [kexec_loadable f] and the fit condition for
   its arguments learns that the only way exec fails after resolving
   its path is running out of memory -- and that on success it holds
   its own WP at the image it computed.  A caller that proves nothing
   about the file runs under the generic user-mode safety WP, which
   does not care what the image holds, and takes arm (b).

   ==== WHAT THE PROVER OWES ===========================================

   1. THE WALK: [SpecNameiEra.wp_namei_era] at [open_walk_pre_era]'s
      one-shot, as ProofKexecPinA already does at its namei site
      ([ProofKexecPinA.v] fires the era walk; the landed ProofKexecA
      fires the set form).
   2. THE OBSERVATION: [FsAbsOpenFire.opf_open_fire] (the whole-[anode]
      fire off the lock window's [top_frag]) at the header-oracle hook
      of phase A ([ProofKexecA.kxc_a2]'s fupd), generalized to deliver
      [Φo]'s receipt instead of a header claim.
   3. THE BYTES: each readi's [rd_bytes data off] IS a window of the
      observed [f] ([era_node]'s [fn_file_bytes] = [file_byte data] over
      the size), so the header the commit block reads, the program
      headers the loop reads and the segments loadseg copies are
      [f]'s -- one bridge lemma per readi site.
   4. THE IMAGE: [kexec_image_ok] from the walk's own facts: [kxc_tf]
      for the trapframe words, the uvmalloc/loadseg loop for
      [uimg_sub (elf_image f)] (this is the "M-threading of the cone"
      SpecKexecPin.v section 8 prices), copyout's post for
      [kexec_args_at].
   5. THE HAND-OFF: instantiate [exec_slot_pre] at the observed [f] and
      the built key, and return the [S]-slot on arm (a); refund the
      premise on every other arm.  The proofs never open [S].
   6. THE DISPATCH SIDE (a separate seam, sys_exec -> ProofSyscall ->
      the trap loop): carry the returned slot to the deposit instead
      of minting ([UexecApply.uexec_ret_round_slot]'s exec case), and
      let the U-mode side's [uexec_ret] exec arm SUPPLY [exec_au_pre]
      -- that is the seam through which init's proof hands over sh's WP.

   BINDERS: SpecKexecPin's list plus [ufdG] (the slot's section binds
   it, and the dispatcher instantiates [S] there).  [GenId] because the
   arms carry [proc_priv]. *)
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
Require Import KvmSpec.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecDirlink.
Require Import PathElems.       (* [SLASH], [path_elems]                     *)
Require Import FsBlocks.        (* [fs_names]                                *)
Require Import SpecKexec.       (* the landed frame this file parallels:
                                   [K_kexec], [kexec_ok], [kxc_sp],
                                   [kxc_sp_final], [kxc_tf_sp_idx], [MAXARG] *)
Require Import PageGeom.        (* [PGSIZE]                                  *)
Require Import UserPtTree.      (* [pgroundup]                               *)
Require Import ElfEnc.          (* [ELF_MAGIC]: the four bytes the code tests *)
Require Import ElfFile.         (* [elf_bytes], [elf_wf], [elf_image],
                                   [elf_entry], [elf_loads], [elf_mem_end]  *)
Require Import UmodeAbi.        (* [uimg_sub]                                *)
Require Import KexecBuilt.      (* [kxb_perm_ok], [kexec_seg_perm], [kexec_pg]: the
                                   permission projection kexec builds (its home) *)
Require Import UserFd.          (* [ufdG] -- UexecRet's section binds it     *)
Require Import UexecSlot.       (* [uvis], [uvis_of], [tf_w]                 *)
Require Import SpecSysOpenAU.   (* [open_walk_pre_era], [open_walk_dead_era],
                                   [aopen_commit_at] -- REUSED, see header  *)
Require Import FsAbsInv.        (* [fsabsE]: the commit mask                 *)
Require Import FsAbsDefs.           (* LAST (FsAbs's own rule)                   *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the live Γ                  *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE LAYER: loadability, the size, the stack, the key        *)
(* ===================================================================== *)

(* the segments in program-header order do not overlap and ascend: each
   ends at or before the next begins.  [uvmalloc] grows [sz] monotonically
   and [loadseg] writes through [walkaddr] into pages that must already
   exist, so this is what makes the loop's image the union of disjoint
   windows -- [ElfFile.elf_image]. *)
Fixpoint loads_ascending (ps : list elf_phdr) : Prop :=
  match ps with
  | [] => True
  | p :: ps' =>
      (match ps' with
       | [] => True
       | q :: _ => ep_vaddr p + ep_memsz p <= ep_vaddr q
       end) /\ loads_ascending ps'
  end.

(* THE ACCEPTANCE PREDICATE (header): the files whose loaded image is the
   ELF semantics' image.  [elf_wf] carries the magic, the 56-byte header
   entries, the in-file bounds, [filesz <= memsz], no wrap, and pairwise
   disjointness; the four extra conjuncts are xv6's: the two [int]
   truncations kexec performs on eight-byte fields ([eh_phoff] and each
   [ph.off] are read as 4-byte words -- ElfEnc.v), page-aligned segment
   starts (the [vaddr % PGSIZE != 0] test), and the ascending order the
   loop's [sz] threading needs. *)
Definition kexec_loadable (f : elf_bytes) : Prop :=
  elf_wf f = true
  /\ (exists e, elf_parse_ehdr f = Some e /\ ee_phoff e < 2 ^ 31)
  /\ Forall (fun p => ep_offset p < 2 ^ 31 /\ ep_vaddr p `mod` PGSIZE = 0)
       (elf_loads f)
  /\ loads_ascending (elf_loads f).

(* the top of the loaded segments, page-rounded ([sz1] in the C: the
   [PGROUNDUP(sz)] after the load loop; 0 for a file with no PT_LOAD) *)
Definition kexec_top (f : elf_bytes) : Z :=
  match elf_mem_end f with
  | Some e => pgroundup e
  | None => 0
  end.

(* the new [p->sz]: two more pages, the lower one the guard uvmclear turns
   unusable, the upper one the stack ([USERSTACK = 1]) *)
Definition kexec_sz (f : elf_bytes) : Z := kexec_top f + 2 * PGSIZE.

(* THE ARGUMENT BLOCK, at the addresses the landed stack model computes:
   argument [i]'s [alen i] characters and its NUL at [kxc_sp top alen (S i)]
   (the pointer AFTER the push of argument [i], which is where copyout
   wrote it), and the [na + 1]-word pointer vector at [kxc_sp_final]:
   [ustack[i] = kxc_sp top alen (S i)] for [i < na], [ustack[na] = 0], each
   word little-endian over eight bytes. *)
Definition kexec_ustack (top : Z) (alen : nat -> nat) (na i : nat) : Z :=
  if decide (i < na)%nat then kxc_sp top alen (S i) else 0.

Definition kexec_args_at (top : Z) (alen : nat -> nat) (na : nat)
    (afun : nat -> nat -> bv 8) (M : gmap Z (bv 8)) : Prop :=
  (forall i j, (i < na)%nat -> (j < alen i)%nat ->
     M !! (kxc_sp top alen (S i) + Z.of_nat j) = Some (afun i j))
  /\ (forall i, (i < na)%nat ->
        M !! (kxc_sp top alen (S i) + Z.of_nat (alen i)) = Some (bv_0 8))
  /\ (forall i k, (i <= na)%nat -> (k < 8)%nat ->
        M !! (kxc_sp_final top alen na + 8 * Z.of_nat i + Z.of_nat k)
        = bv_to_little_endian 8 8 (kexec_ustack top alen na i) !! k).

(* the byte addresses the argument block occupies: the strings (with
   their NULs) and the pointer vector *)
Definition kexec_arg_addr (top : Z) (alen : nat -> nat) (na : nat) (a : Z) : Prop :=
  (exists i, (i < na)%nat
     /\ kxc_sp top alen (S i) <= a <= kxc_sp top alen (S i) + Z.of_nat (alen i))
  \/ (kxc_sp_final top alen na <= a < kxc_sp_final top alen na + 8 * (Z.of_nat na + 1)).

(* THE STACK (header, THE IMAGE): the stack page is the top page of the
   image, the guard page sits below it, the arguments fit ([kxc_stack_ok]
   at the guard's top as the base, the landed fit condition), and every
   stack-page byte outside the argument block reads zero.  The guard
   page's own reading and both pages' permissions are (d1)/(d2). *)
Definition kexec_stack_at (top : Z) (alen : nat -> nat) (na : nat)
    (M : gmap Z (bv 8)) : Prop :=
  kxc_stack_ok top (top - PGSIZE) alen na
  /\ (forall a, top - PGSIZE <= a < top -> ~ kexec_arg_addr top alen na a ->
        M !! a = Some (bv_0 8)).

(* THE KEY kexec BUILT (header, THE IMAGE): what the new process resumes
   at, stated on the user-visible record the slot is keyed by.  [sts] is
   the caller's descriptor view: exec closes no descriptor. *)
Definition kexec_image_ok (f : elf_bytes) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) : Prop :=
  let top := kexec_sz f in
  let spv := kxc_sp_final top alen na in
  (exists e, elf_entry f = Some e
             /\ tf_w (uvis_tf W') tf_epc_idx = (mword_of_int e : mword 64))
  /\ uvis_sz W' = top
  /\ tf_w (uvis_tf W') kxc_tf_sp_idx = (mword_of_int spv : mword 64)
  /\ tf_w (uvis_tf W') (tf_arg_idx 1) = (mword_of_int spv : mword 64)
  /\ tf_w (uvis_tf W') (tf_arg_idx 0) = (mword_of_int (Z.of_nat na) : mword 64)
  /\ uimg_sub (elf_image f) (uvis_M W')
  /\ kexec_args_at top alen na afun (uvis_M W')
  /\ kexec_stack_at top alen na (uvis_M W')
  /\ kxb_perm_ok f (kexec_top f) (uvis_perm W')
  /\ uvis_fd W' = sts
  /\ length (uvis_tf W') = TFWORDS.

(* WHY exec FAILED past the lock (header, LOADABLE MEANS SUCCESS) *)
Inductive exec_fail_cause :=
| EfNotLoadable   (* the node is not a loadable file: a directory or
                     device, a bad magic, headers outside
                     [kexec_loadable] *)
| EfArgsFit       (* the arguments do not fit the stack page *)
| EfNoMem.        (* kalloc / uvmalloc / proc_pagetable exhaustion *)

(* THE KERNEL'S MAGIC TEST, on the file: 64 bytes were read (a short
   read fails before the test) and the first four are the magic.  The
   code compares exactly these four ([ElfEnc.ELF_MAGIC]); ElfFile's
   [elf_magic_ok] is stronger (class and data bytes too), so it is NOT
   what a memory-failure tail can establish. *)
Definition kexec_magic_ok (f : elf_bytes) : Prop :=
  (64 <= length f)%nat /\ elf_le_at f 0 4 = ELF_MAGIC.

Definition anode_loadable (a : anode) : Prop :=
  exists (f : elf_bytes) (nl : nat), a = MkAnode (AFile f) nl /\ kexec_loadable f.

Definition exec_fail_ok (a : anode) (na : nat) (alen : nat -> nat)
    (c : exec_fail_cause) : Prop :=
  match c with
  | EfNotLoadable => ~ anode_loadable a
  | EfArgsFit =>
      exists (f : elf_bytes) (nl : nat),
        a = MkAnode (AFile f) nl
        /\ ~ kxc_stack_ok (kexec_sz f) (kexec_sz f - PGSIZE) alen na
  | EfNoMem =>
      (* the allocations all come after the magic test (header) *)
      forall (f : elf_bytes) (nl : nat),
        a = MkAnode (AFile f) nl -> kexec_magic_ok f
  end.

(* the landed success conjuncts, at the ELF's entry, the failure arm
   refuted: [kexec_ok] with [entry] the file's ([SpecKexec.kexec_ok]'s
   second disjunct is the only one a non-[-1] return admits) *)
Definition kexec_ok_exec (f : elf_bytes) (V V' : pprivate) (r : mword 64)
    (na : nat) (alen : nat -> nat) : Prop :=
  exists (e : Z) (spv szv' : mword 64),
    elf_entry f = Some e
    /\ r <> (mword_of_int (-1) : mword 64)
    /\ kexec_ok V V' r (mword_of_int e : mword 64) spv szv' na alen.

(* THE RESUME KEY: the post-exec block with argc written into a0 (the
   dispatcher's return-value store, which lands AFTER kexec), read through
   [uvis_of] at the caller's descriptor view *)
Definition exec_key (U' : ustate) (sts : list fdstate) (na : nat) : uvis :=
  uvis_of (us_tf U' (<[tf_arg_idx 0 := (mword_of_int (Z.of_nat na) : mword 64)]>
                       (pv_tf (us_V U'))))
          sts.

(* THE KEY'S WORKING DIRECTORY IS THE BLOCK'S, and the block's is the
   caller's: exec inherits the cwd ([SpecKexec.kexec_ok]'s row, read off
   [kexec_ok_exec] by [kexec_ok_exec_cwi]).  So [kexec_image_ok] names no
   cwd -- the key is [uvis_of] of the post-exec block, whose inum the entry
   block already pins. *)
Lemma exec_key_cwd (U' : ustate) (sts : list fdstate) (na : nat) :
  uvis_cwd (exec_key U' sts na) = pv_cwi (us_V U').
Proof. destruct U' as [V' M']. destruct V'. reflexivity. Qed.

Lemma kexec_ok_exec_cwi (f : elf_bytes) (V V' : pprivate) (r : mword 64)
    (na : nat) (alen : nat -> nat) :
  kexec_ok_exec f V V' r na alen -> pv_cwi V' = pv_cwi V.
Proof.
  intros (e & spv & szv' & _ & Hne & Hok).
  destruct Hok as [[Hr _] | Hs]; [ contradiction (Hne Hr) | ].
  destruct Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcwi & _). exact Hcwi.
Qed.

(* the two conjuncts a slot constructor reads first off the key *)
Lemma kexec_image_ok_pc (f : elf_bytes) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) (e : Z) :
  kexec_image_ok f na alen afun sts W' ->
  elf_entry f = Some e ->
  tf_resume_pc (uvis_tf W') = ret_pc (mword_of_int e : mword 64).
Proof.
  intros (He & _) Hent. destruct He as (e' & He' & Hw).
  rewrite Hent in He'. injection He' as ->.
  rewrite /tf_resume_pc Hw. reflexivity.
Qed.

Lemma kexec_image_ok_fd (f : elf_bytes) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok f na alen afun sts W' -> uvis_fd W' = sts.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfd & _). exact Hfd. Qed.

(* THE TEXT READER (header, THE PERMISSIONS): a page of PT_LOAD header
   [i] carries that header's bits.  For sh/init the text segment is
   R-X, so its pages read [MkUperm true false] -- executable and not
   writable, the U-tier's definition of text. *)
Lemma kexec_image_ok_perm (f : elf_bytes) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis)
    (i : nat) (p : elf_phdr) (b : Z) :
  kexec_image_ok f na alen afun sts W' ->
  elf_loads f !! i = Some p ->
  kexec_seg_pages (elf_loads f) i p b ->
  uvis_perm W' !! kexec_pg b = Some (kexec_seg_perm p).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & (Hperm & _ & _) & _) Hi Hb.
  exact (Hperm i p Hi b Hb).
Qed.

(* THE ARGV READER (header, THE STACK): what main sees.  [a1] is the
   vector's address; the [i]-th word of the vector, for [i < na], is the
   address of the [i]-th string, whose characters and NUL are in the
   image; the word after the last is NULL.  This is the whole of what a
   program's slot constructor needs to know about its arguments. *)
Lemma kexec_image_ok_argv (f : elf_bytes) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis) :
  kexec_image_ok f na alen afun sts W' ->
  let vec := kxc_sp_final (kexec_sz f) alen na in
  tf_w (uvis_tf W') (tf_arg_idx 1) = (mword_of_int vec : mword 64)
  /\ tf_w (uvis_tf W') (tf_arg_idx 0) = (mword_of_int (Z.of_nat na) : mword 64)
  /\ (forall i k, (i <= na)%nat -> (k < 8)%nat ->
        uvis_M W' !! (vec + 8 * Z.of_nat i + Z.of_nat k)
        = bv_to_little_endian 8 8 (kexec_ustack (kexec_sz f) alen na i) !! k)
  /\ (forall i j, (i < na)%nat -> (j < alen i)%nat ->
        uvis_M W' !! (kxc_sp (kexec_sz f) alen (S i) + Z.of_nat j) = Some (afun i j))
  /\ (forall i, (i < na)%nat ->
        uvis_M W' !! (kxc_sp (kexec_sz f) alen (S i) + Z.of_nat (alen i))
        = Some (bv_0 8)).
Proof.
  intros (_ & _ & _ & Ha1 & Ha0 & _ & (Hstr & Hnul & Hvec) & _).
  split; [exact Ha1 |]. split; [exact Ha0 |]. split; [exact Hvec |].
  split; [exact Hstr | exact Hnul].
Qed.

(* ===================================================================== *)
(*  2.  THE AU BUNDLE AND THE ARMS                                        *)
(* ===================================================================== *)

Section KexecAU.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* ------------------------------------------------------------------ *)
  (*  2a.  The program's WP, conditional on what was observed             *)
  (* ------------------------------------------------------------------ *)

  (* THE CALLER'S WP (header, IN 3): handed its own receipt for the node
     kexec read, and told the file is loadable and which key kexec built,
     the caller supplies the slot at that key.  [Φo] is the observation
     receipt's shape ([aopen_commit_at]'s), so a caller pins the file it
     is willing to answer for through [Φo] -- init answers only for
     [f = sh_bytes], with sh's start WP. *)
  Definition exec_slot_pre (S : uvis -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) : iProp Σ :=
    (∀ (av : aview) (i : Z) (f : elf_bytes) (nl : nat) (W' : uvis),
       Φo av i (MkAnode (AFile f) nl) -∗
       ⌜kexec_loadable f⌝ -∗
       ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
       S W')%I.

  (* everything the caller hands in *)
  Definition exec_au_pre (S : uvis -> iProp Σ) Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) : iProp Σ :=
    (open_walk_pre_era γfs cw P Pmiss
     ∗ aopen_commit_at Γ fsabsE Φo
     ∗ exec_slot_pre S Φo na alen afun sts)%I.

  (* non-expansive in the slot predicate: UexecExecInst.v instantiates
     [S] at a fixpoint variable, and the fixpoint's contractivity proof
     needs this of the bundle *)
  Lemma exec_slot_pre_ne (n : nat) (S S' : uvis -d> iPropO Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) :
    S ≡{n}≡ S' ->
    exec_slot_pre S Φo na alen afun sts ≡{n}≡ exec_slot_pre S' Φo na alen afun sts.
  Proof. intros HS. rewrite /exec_slot_pre. solve_proper. Qed.

  Lemma exec_au_pre_ne (n : nat) (S S' : uvis -d> iPropO Σ) Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) :
    S ≡{n}≡ S' ->
    exec_au_pre S Γ γfs cw P Pmiss Φo na alen afun sts
    ≡{n}≡ exec_au_pre S' Γ γfs cw P Pmiss Φo na alen afun sts.
  Proof.
    intros HS. rewrite /exec_au_pre.
    by rewrite (exec_slot_pre_ne n S S' Φo na alen afun sts HS).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  The arms                                                       *)
  (* ------------------------------------------------------------------ *)

  (* ret = argc (header, OUT): the walk completed at [i], a FILE was
     observed there, the landed success conjuncts hold at its entry, and
     the slot is the caller's (a) or the generic mint's (b). *)
  Definition exec_post_ok (S : uvis -> iProp Σ) Γ (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (U U' : ustate) (r : mword 64) : iProp Σ :=
    (∃ (pl : list (bv 8)) (i : Z) (av : aview) (a : anode),
       P (length (path_elems pl)) i ∗
       ⌜av !! i = Some a⌝ ∗
       ((* (a) a loadable file: the program xv6 loaded is the ELF
           semantics' image, and the caller's WP is returned at the key
           the process resumes in *)
        (∃ (f : elf_bytes) (nl : nat),
           ⌜a = MkAnode (AFile f) nl⌝ ∗
           ⌜kexec_loadable f⌝ ∗
           ⌜kexec_ok_exec f (us_V U) (us_V U') r na alen⌝ ∗
           ⌜kexec_image_ok f na alen afun sts (exec_key U' sts na)⌝ ∗
           S (exec_key U' sts na))
        ∨ (* (b) anything else the code accepted (header): the landed
             success conjuncts at some entry, the receipt and the WP
             premise back *)
        (⌜~ anode_loadable a⌝ ∗
         ⌜exists (entry spv szv' : mword 64),
            r <> (mword_of_int (-1) : mword 64)
            /\ kexec_ok (us_V U) (us_V U') r entry spv szv' na alen⌝ ∗
         Φo av i a ∗
         exec_slot_pre S Φo na alen afun sts)))%I.

  (* ret = -1 (header, OUT): the three-way fold of the bundle *)
  Definition exec_post_fail (S : uvis -> iProp Σ) Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) : iProp Σ :=
    ((* (i) nothing fs-visible happened *)
     exec_au_pre S Γ γfs cw P Pmiss Φo na alen afun sts
     ∨ (∃ pl : list (bv 8),
          (* (ii) the walk died at some hop: the era refund shape *)
          (open_walk_dead_era γfs P Pmiss pl
             ∗ aopen_commit_at Γ fsabsE Φo
             ∗ exec_slot_pre S Φo na alen afun sts)
          ∨ (* (iii) the walk completed and the node was observed; exec
               failed past the lock, and the arm says WHY (header,
               LOADABLE MEANS SUCCESS): not a loadable file, the
               arguments did not fit, or out of memory *)
          (∃ (i : Z) (av : aview) (a : anode) (c : exec_fail_cause),
             P (length (path_elems pl)) i
             ∗ ⌜av !! i = Some a⌝ ∗ Φo av i a
             ∗ ⌜exec_fail_ok a na alen c⌝
             ∗ exec_slot_pre S Φo na alen afun sts)))%I.

  (* the armed disjunction the continuation receives, keyed on a0, beside
     the landed result relation's own failure equation *)
  Definition exec_arms (S : uvis -> iProp Σ) Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (U U' : ustate) (r : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64) /\ us_V U' = us_V U /\ us_M U' = us_M U⌝
      ∗ exec_post_fail S Γ γfs cw P Pmiss Φo na alen afun sts)
     ∨ exec_post_ok S Γ P Φo na alen afun sts U U' r)%I.

  (* SANITY: the arms imply the landed result relation, so the parallel
     form never contradicts [SpecKexec.kexec_ok] -- the failure arm is the
     landed one on the nose, the success arm's pure conjunct IS the landed
     success arm at the file's entry. *)
  Lemma exec_arms_landed (S : uvis -> iProp Σ) Γ (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (U U' : ustate) (r : mword 64) :
    exec_arms S Γ γfs cw P Pmiss Φo na alen afun sts U U' r ⊢
      ⌜exists (entry spv szv' : mword 64),
         kexec_ok (us_V U) (us_V U') r entry spv szv' na alen⌝.
  Proof.
    rewrite /exec_arms /exec_post_ok.
    iIntros "[[(%Hr & %HV & _) _] | H]".
    - iPureIntro. exists (mword_of_int 0), (mword_of_int 0), (mword_of_int 0).
      left. split; [exact Hr | exact HV].
    - iDestruct "H" as (pl i av a) "(_ & _ & [H | H])".
      + iDestruct "H" as (f nl) "(_ & _ & %Hok & _)".
        iPureIntro. destruct Hok as (e & spv & szv' & _ & _ & Hok).
        exists (mword_of_int e), spv, szv'. exact Hok.
      + iDestruct "H" as "(_ & %Hok & _)".
        iPureIntro. destruct Hok as (entry & spv & szv' & _ & Hok).
        exists entry, spv, szv'. exact Hok.
  Qed.

End KexecAU.

(* big-op bodies behind definitions: sealed, per the family convention
   (durable-notes; optimization.md, "a big-op body is the predictor").
   [exec_slot_pre] is a plain wand and stays transparent. *)
Global Typeclasses Opaque exec_au_pre exec_post_ok exec_post_fail exec_arms.

(* ===================================================================== *)
(*  3.  THE MACHINE CONTRACT: SpecKexec's frame + the AU                  *)
(* ===================================================================== *)

(* [SpecKexec.wp_kexec_sconf_body]'s premises and threaded resources
   VERBATIM (R10), with the bundle [EXTRA] after the process block and
   the armed post in place of the landed [kexec_ok] conjunct.  The
   continuation's binders lose [entry spv szv'] -- they are the success
   arm's existentials now -- and keep every resource row. *)
Definition wp_kexec_au_frame
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
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
    (b : bool) (lks : gset string)
    (EXTRA : iProp Σ) (ARMS : ustate -> mword 64 -> iProp Σ) :=
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
  bb_cstr pfun plen ->
  (Z.of_nat plen < 2 ^ 31)%Z ->
  (forall i, (i < na)%nat -> avf i <> (mword_of_int 0 : mword 64)) ->
  avf na = (mword_of_int 0 : mword 64) ->
  (na < MAXARG)%nat ->
  (forall i, (i < na)%nat -> (alen i < aslen i)%nat) ->
  (forall i, (i < na)%nat -> bb_cstr (afun i) (alen i)) ->
  (forall i, (i < na)%nat -> (Z.of_nat (alen i) < 4096)%Z) ->
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
  (* ---- THE AU SIDE (the one addition to the landed premise list) ---- *)
  EXTRA -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile) (U' : ustate),
      ⌜callee_saved m mf⌝ -∗
      (* the armed post on the moved block and the returned a0 (implies
         the landed [kexec_ok] at some entry, [exec_arms_landed]) *)
      ARMS U' (mf !!! Regidx (mword_of_int 10 : mword 5)) -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sb_bmapstart ↦₄{dqb} (mword_of_int fsc_bmapstart : mword 32) -∗
      sb_inodestart ↦₄{dqs} (mword_of_int icfg_ist : mword 32) -∗
      kalloc_env fsc_kalloc None -∗
      proc_priv gf pj pidv U' -∗
      ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
      ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
      ([∗ list] i ∈ seq 0 na,
         [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
      bslots 3 -∗
      iref_slots 2 -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE CONTRACT.  The abstract state is read at the LIVE Γ; the
   descriptor view [sts] is the caller's (kexec never opens the
   descriptor block, so the key's fd leg is whatever the caller holds). *)
Definition wp_kexec_au_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (S : uvis -> iProp Σ)
    (gs : list gname) (jp : nat) (gl : gname)
    (pd pav pu : mword 64)
    (gf : gname)
    (plen : nat) (pfun : nat -> bv 8)
    (na : nat) (avf : nat -> mword 64)
    (alen : nat -> nat) (aslen : nat -> nat)
    (afun : nat -> nat -> bv 8)
    (pidv : mword 32) (U : ustate) (sts : list fdstate)
    (dqb dqs dqa dqpv dqas : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (P Pmiss : nat -> Z -> iProp Σ)
    (Φo : aview -> Z -> anode -> iProp Σ) :=
  let Γfs := fs_gamma_L fsc_fs in
  wp_kexec_au_frame gs jp gl pd pav pu gf plen pfun na avf alen aslen afun
    pidv U dqb dqs dqa dqpv dqas m K eb b lks
    (exec_au_pre S Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Φo na alen afun sts)
    (exec_arms S Γfs fsc_fs (pv_cwi (us_V U)) P Pmiss Φo na alen afun sts U).

(* ===================================================================== *)
(*  4.  THE SEAL                                                          *)
(* ===================================================================== *)

Module Type KEXEC_AU.
  Parameter wp_kexec_au :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
             !irefslotG Σ, !pavG Σ, !ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (S : uvis -> iProp Σ)
      (gs : list gname) (jp : nat) (gl : gname)
      (pd pav pu : mword 64)
      (gf : gname)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (U : ustate) (sts : list fdstate)
      (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ),
      wp_kexec_au_body S gs jp gl pd pav pu gf plen pfun na avf alen aslen afun
        pidv U sts dqb dqs dqa dqpv dqas m K eb b lks P Pmiss Φo.
End KEXEC_AU.
