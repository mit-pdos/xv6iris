(* SpecFileclose.v -- the public interface of fileclose, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     void fileclose(struct file *f) {
       struct file ff;
       acquire(&ftable.lock);
       if (f->ref < 1) panic("fileclose");
       if (--f->ref > 0) { release(&ftable.lock); return; }
       ff = *f;
       f->ref = 0;
       f->type = FD_NONE;
       release(&ftable.lock);
       if (ff.type == FD_PIPE) pipeclose(ff.pipe, ff.writable);
       else if (ff.type == FD_INODE || ff.type == FD_DEVICE) {
         begin_op(); iput(ff.ip); end_op();
       }
     }

   ==== THE REFERENCE HALF ===============================================

   The simple half, and it is stable: a reference goes in, one [fd_slot]
   comes back, and nothing says which arm ran.  Deliberately so -- the caller
   neither knows nor cares whether it held the last reference.  It is
   entirely [FileInv]'s two close steps:

   * [--f->ref > 0] (file_close_step + file_rest_absorb): the departing
     reference's fraction -- of the content cells, of the payload-names field
     and of the payload itself -- is absorbed back into the invariant's
     leftover.  That the fraction has somewhere to GO is why the authority's
     frac component tracks outstanding fraction rather than being pinned at 1.
   * [--f->ref == 0] (file_close_last_step + file_rest_join): the COUNT
     component forces this closer to hold every share ever handed out
     ([positiveR] has no unit), and the invariant's leftover makes it fraction
     ONE of the whole slot.  That is what licenses the unlocked-looking
     [ff = *f] read and the [f->type = FD_NONE] store, and -- the point of the
     payload link -- it is what puts a WHOLE pipe end, or a whole inode
     reference, in fileclose's hands to give to pipeclose / iput.

   Note the ORDER the C code uses and the model needs: [f->type = FD_NONE] is
   written, and the lock released, BEFORE the payload is spent.  At FD_NONE
   the payload is [emp], so what goes back into the table is the slot with no
   payload while the closer walks away with it.

   The [f->ref < 1] panic arm is dead for the same reason as filedup's: the
   caller's [file_ref] puts slot k in the authority's domain with a positive
   count, and [FileInv.fref_word_spos] turns that into "the sign-extended
   load is signed-positive", which is exactly what [blez] tests.

   ==== THE OTHER HALF: WHAT THE LAST-REFERENCE ARM COSTS ================

   fileclose can free a pipe's page, and it can do disk I/O and SLEEP.  Its
   callers must own the corresponding fabric, and there is no honest way to
   hide that.  What they must own depends on the TYPE of the file, because
   the type is what selects the arm -- so the environment is indexed by it
   ([fileclose_env] / [fileclose_env_out]) rather than being the union:

   * FD_PIPE   -> pipeclose's: the kmem lock and the page count (the page
                  comes back iff this was the pipe's last end), plus
                  [procs_inv] for the wakeup inside it.
   * FD_INODE
     / FD_DEVICE -> begin_op / iput / end_op's: the whole log + buffer-cache
                  + disk fabric, the running-thread bundle, and the parking
                  premise.  The log RESERVATION is not among them: begin_op
                  mints it and end_op retires it, so an operation's budget
                  never crosses fileclose's boundary.
   * FD_NONE   -> nothing at all.

   That last line is not a curiosity: it is what keeps pipealloc's failure
   path cheap.  pipealloc closes files it has just allocated and not yet
   typed ([SpecFilealloc]'s post pins [fc_type Cf = FD_NONE]), so it owns no
   file system and is not asked for one.  sys_pipe closes FD_PIPE files and
   is asked only for the pipe fabric it already has.  Only a caller closing a
   file of UNKNOWN type -- sys_close, kexit -- pays for both, which is the
   truth about closing an arbitrary descriptor.

   The type-indexing also decides the pure side conditions: pipeclose wants
   one more level of lock nesting than fileclose's own acquire, and the FS
   calls want [noff = 0] and the hart-generic parking premise.  Each sits in
   the arm that needs it.

   The ghost names and geometry both arms are indexed by are bundled into one
   [fclose_names], with an [Inhabited] instance, so that a caller which
   cannot reach either arm passes [inhabitant] rather than having to invent a
   [bio_names] it has never heard of.

   WHAT COMES BACK: one [fd_slot], plus the arm's own returns.  The fd slot
   is not a decoration -- it is the return leg of the conservation law that
   makes filedup's unchecked [f->ref++] safe (FdSlots.v /
   design/file-table.md).  [ftable_res] holds one unit per outstanding
   reference, so destroying a reference releases exactly one, whichever arm
   ran: at [n >= 2] the slot's [fd_slots n] shrinks to [fd_slots (n-1)], and
   at [n = 1] the whole entry leaves the authority.  The caller needs it:
   sys_close's descriptor is empty afterwards, and an empty
   [ProcInv.ofile_slot] owns its unit itself. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import FdSlots FileInv.
Require Import KallocInv.
Require Import WpLock.
Require Import SpecPanic.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import SpecIput.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.


(* fileclose's own frame is 8 slots ([addi sp,sp,-64]: ra, s0..s5 saved), and
   its deepest callee is iput ([SpecIput.K_iput] = 60, itself sized by bread
   under itrunc).  The others are smaller: end_op 58, begin_op 26, pipeclose
   22, acquire/release 10.  A CONSTANT, not a per-arm bound: the stack a
   function may need is a property of the function (durable-notes.md). *)
Definition fileclose_stack : nat := (8 + K_iput)%nat.

(* ---------------------------------------------------------------------- *)
(* The ghost names and geometry the last-reference arm's callees are        *)
(* indexed by, in one bundle.                                              *)
(* ---------------------------------------------------------------------- *)
Record fclose_names := MkFCloseNames {
  fcn_procs    : list gname;      (* the proc table's per-slot lock names   *)
  fcn_j        : nat;             (* the running process's index            *)
  fcn_plock    : gname;
  fcn_kmem     : gname;           (* kmem.lock                              *)
  fcn_kalloc   : gname * gname;
  fcn_uart     : uart_names;
  fcn_disk     : disk_names;
  fcn_dlock    : gname;           (* virtio_disk.lock                       *)
  fcn_pd       : mword 64;
  fcn_pav      : mword 64;
  fcn_pu       : mword 64;
  fcn_bio      : bio_names;
  fcn_log      : log_names;
  fcn_fs       : fs_names;
  fcn_cov      : gset Z;
  fcn_logstart : Z;
  fcn_dev      : mword 32;
  fcn_pid      : mword 32;        (* the caller's own pid cell              *)
  fcn_dq       : dfrac;
}.

(* Spelled out rather than derived: several of these records have no
   [Inhabited] instance of their own, and [bio_names] has function fields.
   Nothing reads these values -- the arm they belong to is unreachable for
   the caller that passes them -- so any closed term does. *)
Global Instance fclose_names_inhabited : Inhabited fclose_names :=
  populate (MkFCloseNames
    [] 0%nat 1%positive 1%positive (1%positive, 1%positive)
    (UartNames 1%positive 1%positive 1%positive 1%positive)
    (DiskNames 1%positive 1%positive 1%positive 1%positive 1%positive
               1%positive 1%positive)
    1%positive
    (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)
    (MkBioNames 1%positive 1%positive 1%positive
       (fun _ => (1%positive, 1%positive)) (fun _ => 1%positive)
       (fun _ => 1%positive))
    (MkLogNames 1%positive 1%positive)
    (MkFsNames 1%positive 1%positive 1%positive)
    ∅ 0 (mword_of_int 0) (mword_of_int 0) (DfracOwn 1)).

Section SpecFileclose.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ---- the FD_PIPE arm's environment: pipeclose's ---- *)
  (* [on] is a PARAMETER rather than a field of [fclose_names], because it is
     the one thing that moves: a caller closing descriptor after descriptor
     (kexit) carries it existentially while everything else stays fixed. *)
  Definition fileclose_pipe_env (Φ : mval -> iProp Σ) (fn : fclose_names)
      (on : option nat) (n : nat) : iProp Σ :=
    (⌜(Z.of_nat n + 2 < 2 ^ 31)%Z⌝ ∗
     procs_inv Φ (fcn_procs fn) ∗
     is_lock (fcn_kmem fn) (mword_of_int KernelSyms.kmem) "kmem"%string
       (kmem_res (fcn_kalloc fn) (mword_of_int (KernelSyms.kmem + 24))) ∗
     kalloc_avail (fcn_kalloc fn) on)%I.

  (* the page came back iff this was the pipe's LAST end; the caller cannot
     tell, and does not need to. *)
  Definition fileclose_pipe_out (fn : fclose_names) (on : option nat) : iProp Σ :=
    (kalloc_avail (fcn_kalloc fn) on ∨
     kalloc_avail (fcn_kalloc fn) (avail_inc on))%I.

  (* ---- the FD_INODE / FD_DEVICE arm's environment: begin_op / iput /
         end_op's, which is the whole file system ---- *)
  Definition fileclose_fs_env (Φ : mval -> iProp Σ) (fn : fclose_names)
      (n : nat) (eb : bool) (p : mword 64) : iProp Σ :=
    (⌜(n = 0)%nat⌝ ∗ ⌜eb = true⌝ ∗ ⌜p = proc_addr (fcn_j fn)⌝ ∗
     ⌜(fcn_j fn < NPROC)%nat⌝ ∗
     ⌜fcn_procs fn !! fcn_j fn = Some (fcn_plock fn)⌝ ∗
     ⌜log_geom_ok (fcn_cov fn) (fcn_logstart fn)⌝ ∗
     procs_inv Φ (fcn_procs fn) ∗ scheds_inv Φ (fcn_procs fn) ∗
     bio_ctx (fcn_bio fn)
       (fs_view (fcn_fs fn) (fcn_disk fn) (fcn_dev fn) (fcn_cov fn)) ∗
     log_ctx (fcn_log fn) (fcn_bio fn) (fcn_fs fn) (fcn_cov fn)
       (fcn_logstart fn) (fcn_dev fn) ∗
     fs_crash_seam (fcn_cov fn) (fcn_logstart fn) ∗ gen_cert ∗
     dev_inv (fcn_uart fn) (fcn_disk fn) ∗
     disk_geom (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) ∗
     is_lock (fcn_dlock fn) d_lock "virtio_disk"%string
       (disk_res (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn)) ∗
     bslots (fcn_bio fn) 3 ∗
     running_claim (fcn_j fn) ∗
     p_pid (proc_addr (fcn_j fn)) ↦₄{fcn_dq fn} fcn_pid fn)%I.

  (* the same bundle WITHOUT the caller's pid cell.  kexit closes every
     descriptor in a loop while holding [proc_priv], and the pid cell the FS
     calls want is INSIDE that block -- so its loop carries this, and pairs it
     with the quarter [ProcInv.proc_priv_pid_ofile] lends for the duration of
     one call. *)
  Definition fileclose_fs_env_nopid (Φ : mval -> iProp Σ) (fn : fclose_names)
      (n : nat) (eb : bool) (p : mword 64) : iProp Σ :=
    (⌜(n = 0)%nat⌝ ∗ ⌜eb = true⌝ ∗ ⌜p = proc_addr (fcn_j fn)⌝ ∗
     ⌜(fcn_j fn < NPROC)%nat⌝ ∗
     ⌜fcn_procs fn !! fcn_j fn = Some (fcn_plock fn)⌝ ∗
     ⌜log_geom_ok (fcn_cov fn) (fcn_logstart fn)⌝ ∗
     procs_inv Φ (fcn_procs fn) ∗ scheds_inv Φ (fcn_procs fn) ∗
     bio_ctx (fcn_bio fn)
       (fs_view (fcn_fs fn) (fcn_disk fn) (fcn_dev fn) (fcn_cov fn)) ∗
     log_ctx (fcn_log fn) (fcn_bio fn) (fcn_fs fn) (fcn_cov fn)
       (fcn_logstart fn) (fcn_dev fn) ∗
     fs_crash_seam (fcn_cov fn) (fcn_logstart fn) ∗ gen_cert ∗
     dev_inv (fcn_uart fn) (fcn_disk fn) ∗
     disk_geom (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn) ∗
     is_lock (fcn_dlock fn) d_lock "virtio_disk"%string
       (disk_res (fcn_disk fn) (fcn_pd fn) (fcn_pav fn) (fcn_pu fn)) ∗
     bslots (fcn_bio fn) 3 ∗
     running_claim (fcn_j fn))%I.

  Lemma fileclose_fs_env_split_pid Φ fn n eb p :
    fileclose_fs_env Φ fn n eb p ⊣⊢
    fileclose_fs_env_nopid Φ fn n eb p ∗
    p_pid (proc_addr (fcn_j fn)) ↦₄{fcn_dq fn} fcn_pid fn.
  Proof.
    rewrite /fileclose_fs_env /fileclose_fs_env_nopid. iSplit.
    - iIntros "(%H1 & %H2 & %H3 & %H4 & %H5 & %H6 & Hpr & Hsc & Hbio & Hlog &
                Hseam & Hcert & Hdev & Hgeom & Hdlk & Hbs & Hpark & $)".
      do 6 (iSplitR; [iPureIntro; assumption|]).
      iFrame "Hpr Hsc Hbio Hlog Hseam Hcert Hdev Hgeom Hdlk Hbs Hpark".
    - iIntros "[(%H1 & %H2 & %H3 & %H4 & %H5 & %H6 & Hpr & Hsc & Hbio & Hlog &
                 Hseam & Hcert & Hdev & Hgeom & Hdlk & Hbs & Hpark) $]".
      do 6 (iSplitR; [iPureIntro; assumption|]).
      iFrame "Hpr Hsc Hbio Hlog Hseam Hcert Hdev Hgeom Hdlk Hbs Hpark".
  Qed.

  Definition fileclose_fs_out (fn : fclose_names) : iProp Σ :=
    (running_claim (fcn_j fn) ∗
     p_pid (proc_addr (fcn_j fn)) ↦₄{fcn_dq fn} fcn_pid fn ∗
     bslots (fcn_bio fn) 3)%I.

  (* ---- and the two, selected by the file's type ---- *)
  Definition fileclose_env (Φ : mval -> iProp Σ) (fn : fclose_names)
      (on : option nat) (n : nat) (eb : bool) (p : mword 64) (Cf : fcontent)
      : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE)
     then fileclose_pipe_env Φ fn on n
     else if bool_decide (fc_type Cf = FD_INODE)
               || bool_decide (fc_type Cf = FD_DEVICE)
     then fileclose_fs_env Φ fn n eb p
     else emp)%I.

  Definition fileclose_env_out (fn : fclose_names) (on : option nat)
      (Cf : fcontent) : iProp Σ :=
    (if bool_decide (fc_type Cf = FD_PIPE)
     then fileclose_pipe_out fn on
     else if bool_decide (fc_type Cf = FD_INODE)
               || bool_decide (fc_type Cf = FD_DEVICE)
     then fileclose_fs_out fn
     else emp)%I.

  (* A file that is neither a pipe nor an inode costs its closer nothing.
     This is the lemma pipealloc's two error-path calls are discharged by --
     [SpecFilealloc]'s post already pins the type. *)
  Lemma fileclose_env_none Φ fn on n eb p Cf :
    fc_type Cf = FD_NONE -> ⊢ fileclose_env Φ fn on n eb p Cf.
  Proof.
    intro Ht. rewrite /fileclose_env Ht.
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    rewrite bool_decide_eq_false_2; [|by vm_compute].
    done.
  Qed.

  (* EACH BUNDLE ALREADY CONTAINS WHAT IT PROMISES BACK.  Two facts, and both
     are checks rather than conveniences: they are what catches a bundle
     stated with one of its returns going the wrong way. *)
  Lemma fileclose_pipe_env_out Φ fn on n :
    fileclose_pipe_env Φ fn on n -∗ fileclose_pipe_out fn on.
  Proof.
    rewrite /fileclose_pipe_env /fileclose_pipe_out.
    iIntros "(_ & _ & _ & Hav)". by iLeft.
  Qed.

  Lemma fileclose_fs_env_out Φ fn n eb p :
    fileclose_fs_env Φ fn n eb p -∗ fileclose_fs_out fn.
  Proof.
    rewrite /fileclose_fs_env /fileclose_fs_out.
    iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
              Hbs & Hpark & Hpid)".
    iFrame "Hpark Hpid Hbs".
  Qed.

  (* THE FAST PATH'S OBLIGATION, checked here rather than discovered in the
     proof: when [--f->ref > 0] fileclose returns without touching any of it,
     so the environment must already contain everything the postcondition
     promises. *)
  Lemma fileclose_env_out_of_env Φ fn on n eb p Cf :
    fileclose_env Φ fn on n eb p Cf -∗ fileclose_env_out fn on Cf.
  Proof.
    rewrite /fileclose_env /fileclose_env_out.
    case_bool_decide; [|case_match].
    - iApply fileclose_pipe_env_out.
    - iApply fileclose_fs_env_out.
    - by iIntros "_".
  Qed.

  (* ---- CLOSING MORE THAN ONE DESCRIPTOR ----

     kexit walks the whole fd table, so its loop has to carry the environment
     round.  Everything in both bundles except the four consumables and the
     page count is persistent, so the round trip is a persistent wand: hand
     the bundle over, and rebuild it from what comes back.  The page count
     comes back CHANGED -- pipeclose frees the page only if it closed the
     pipe's last end -- which is why the pipe bundle is rebuilt under an
     existential, and hence why [on] is a parameter and not a field.

     If either of these ever stops compiling, a conjunct of the environment
     has stopped being persistent and must be routed back through the
     corresponding [_out] instead. *)
  Lemma fileclose_pipe_env_reuse Φ fn on n :
    fileclose_pipe_env Φ fn on n -∗
    fileclose_pipe_env Φ fn on n ∗
    □ (fileclose_pipe_out fn on -∗ ∃ on', fileclose_pipe_env Φ fn on' n).
  Proof.
    rewrite /fileclose_pipe_env /fileclose_pipe_out.
    iIntros "(%Hb & #Hpi & #Hlk & Hav)".
    iSplitL "Hav".
    { iSplitR; [iPureIntro; exact Hb|]. iFrame "Hpi Hlk Hav". }
    iModIntro. iIntros "[H|H]".
    - iExists on. iSplitR; [iPureIntro; exact Hb|]. iFrame "Hpi Hlk H".
    - iExists (avail_inc on). iSplitR; [iPureIntro; exact Hb|]. iFrame "Hpi Hlk H".
  Qed.

  Lemma fileclose_fs_env_reuse Φ fn n eb p :
    fileclose_fs_env Φ fn n eb p -∗
    fileclose_fs_env Φ fn n eb p ∗
    □ (fileclose_fs_out fn -∗ fileclose_fs_env Φ fn n eb p).
  Proof.
    rewrite /fileclose_fs_env /fileclose_fs_out.
    iIntros "(%H1 & %H2 & %H3 & %H4 & %H5 & %H6 & #Hpr & #Hsc & #Hbio & #Hlog &
              #Hseam & #Hcert & #Hdev & #Hgeom & #Hdlk & Hbs & Hpark & Hpid)".
    iSplitL "Hbs Hpark Hpid".
    { do 6 (iSplitR; [iPureIntro; assumption|]).
      iFrame "Hpr Hsc Hbio Hlog Hseam Hcert Hdev Hgeom Hdlk Hbs Hpark Hpid". }
    iModIntro. iIntros "(Hpark & Hpid & Hbs)".
    do 6 (iSplitR; [iPureIntro; assumption|]).
    iFrame "Hpr Hsc Hbio Hlog Hseam Hcert Hdev Hgeom Hdlk Hbs Hpark Hpid".
  Qed.

  (* ---- WHAT A CLOSER OF AN ARBITRARY DESCRIPTOR DOES ----

     A caller that took its [struct file] out of the fd table -- sys_close,
     kexit, sys_pipe -- cannot see the type: [ProcInv.ofile_slot] quantifies
     the [fcontent] existentially, and that knowledge is going to arrive as
     per-[ofile] ghost state in [struct proc] rather than off the ftable.  So
     it carries BOTH bundles, hands over whichever the environment asks for,
     and keeps the other untouched.  This is that move, proved once: the
     environment out, and a wand that puts both bundles back together from
     whatever came back.

     (Only pipealloc escapes it, because [filealloc] pins its files untyped;
     it uses [fileclose_env_none] instead.) *)
  Lemma fileclose_env_split Φ fn on n eb p Cf :
    fileclose_pipe_env Φ fn on n -∗ fileclose_fs_env Φ fn n eb p -∗
    fileclose_env Φ fn on n eb p Cf ∗
    (fileclose_env_out fn on Cf -∗
       fileclose_pipe_out fn on ∗ fileclose_fs_out fn).
  Proof.
    rewrite /fileclose_env /fileclose_env_out.
    case_bool_decide; [|case_match].
    - iIntros "Hp Hf". iFrame "Hp". iIntros "$".
      by iApply fileclose_fs_env_out.
    - iIntros "Hp Hf". iFrame "Hf". iIntros "$".
      by iApply fileclose_pipe_env_out.
    - iIntros "Hp Hf". iSplitR; [done|]. iIntros "_".
      iDestruct (fileclose_pipe_env_out with "Hp") as "$".
      by iApply fileclose_fs_env_out.
  Qed.

  (* ...and the form every fd-table closer actually uses: hand over the
     environment, get the WHOLE environment back.  The page count has moved
     if the descriptor held a pipe's last end, so the pipe bundle returns
     under an existential -- which is exactly what lets a caller close a
     second descriptor, and hence what kexit's loop runs on. *)
  Lemma fileclose_env_frame Φ fn on n eb p Cf :
    fileclose_pipe_env Φ fn on n -∗ fileclose_fs_env Φ fn n eb p -∗
    fileclose_env Φ fn on n eb p Cf ∗
    (fileclose_env_out fn on Cf -∗
       (∃ on', fileclose_pipe_env Φ fn on' n) ∗ fileclose_fs_env Φ fn n eb p).
  Proof.
    iIntros "Hp Hf".
    iDestruct (fileclose_pipe_env_reuse with "Hp") as "[Hp #Hpre]".
    iDestruct (fileclose_fs_env_reuse with "Hf") as "[Hf #Hfre]".
    iDestruct (fileclose_env_split Φ fn on n eb p Cf with "Hp Hf") as "[$ Hback]".
    iIntros "Hout". iDestruct ("Hback" with "Hout") as "[Hpo Hfo]".
    iSplitL "Hpo"; [by iApply "Hpre" | by iApply "Hfre"].
  Qed.

  (* WHAT A LOOP OVER DESCRIPTORS CARRIES.  The pid quarter is lent per
     iteration out of [proc_priv]; everything else goes round. *)
  Lemma fileclose_loop_open Φ fn on n eb p Cf :
    fileclose_pipe_env Φ fn on n -∗
    fileclose_fs_env_nopid Φ fn n eb p -∗
    p_pid (proc_addr (fcn_j fn)) ↦₄{fcn_dq fn} fcn_pid fn -∗
    fileclose_env Φ fn on n eb p Cf ∗
    (fileclose_env_out fn on Cf -∗
       (∃ on', fileclose_pipe_env Φ fn on' n) ∗
       fileclose_fs_env_nopid Φ fn n eb p ∗
       p_pid (proc_addr (fcn_j fn)) ↦₄{fcn_dq fn} fcn_pid fn).
  Proof.
    iIntros "Hp Hf Hpid".
    iDestruct (fileclose_fs_env_split_pid with "[Hf Hpid]") as "Hf";
      [iFrame "Hf Hpid"|].
    iDestruct (fileclose_env_frame Φ fn on n eb p Cf with "Hp Hf") as "[$ Hback]".
    iIntros "Hout". iDestruct ("Hback" with "Hout") as "[$ Hf]".
    by iApply fileclose_fs_env_split_pid.
  Qed.

End SpecFileclose.

Definition wp_fileclose_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γfl γf : gname)            (* ftable.lock, ftable  *)
    (k : nat) (q : Qp) (Cf : fcontent)                (* the reference        *)
    (fn : fclose_names) (on : option nat)             (* the arms' ghosts     *)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (K : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.fileclose in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (fileclose_stack <= K)%nat ->
  (* fileclose's own acquire is one level of nesting; the arms that want more
     say so in [fileclose_env]. *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* a0 is the file being closed *)
  m !!! Regidx (mword_of_int 10 : mword 5) = fnode k ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_ftable γfl γf -∗
  panic_wp_any -∗
  file_ref γf k q Cf -∗
  fileclose_env Φ fn on n eb p Cf -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    fd_slot -∗
    fileclose_env_out fn on Cf -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type FILECLOSE.
  Parameter wp_fileclose_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !fsCrashG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γfl γf : gname)
      (k : nat) (q : Qp) (Cf : fcontent)
      (fn : fclose_names) (on : option nat)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool),
      wp_fileclose_sconf_body Φ γfl γf k q Cf fn on m n eb p C K b.
End FILECLOSE.
