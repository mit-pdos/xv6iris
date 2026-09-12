(* UexecExecInst.v -- THE KERNEL-SIDE INSTANCE of the per-syscall deposit
   class [UexecSG.uexecSG], and of the generic program's [UexecSG.uprogSG]
   beside it.

   UexecSG.v states the U-mode trap contract's returning arm over an
   ambient class whose family
   [sbundle : (uvis -d> iPropO Σ) -> Z -> uvis -> iProp Σ] says what the
   program hands over at an ecall of number [n], AT THE RECURSIVE
   OCCURRENCE: exec's bundle carries a slot wand, so the family is applied
   to the fixpoint variable and at the fixpoint it concludes at [uslot] --
   the slot the kernel returns for the new process.  The class is what
   keeps the whole U-mode fixpoint's cone clear of the fs tower.  THIS file
   is where the two meet.

   WHICH NUMBERS HAVE A BUNDLE.  Nine: read 5, exec 7, chdir 9, open 15,
   write 16, mknod 17, unlink 18, link 19, mkdir 20 -- every syscall with an
   AU contract.  Each branch is that contract's own landed INPUT, read off
   the key: the process's families, the image, the three argument words, the
   descriptor view and the working directory, and nothing else.  Every other
   number's [sbundle_at] is [emp].

   WHICH NUMBERS PAY A POST.  Eight: read 5, chdir 9, open 15, write 16,
   mknod 17, unlink 18, link 19, mkdir 20.  Six of them pay that contract's
   own armed post verbatim, read off the same key projections its input is;
   chdir and open pay their contract's RECEIPT ([SpecSysChdir.chdir_receipt],
   [SpecSysOpen.open_receipt]) -- the process-nameable half of the arms,
   whose kernel half ([ProcInv.proc_priv], the descriptor fragments,
   [FdSlots.fd_slot]) the dispatcher keeps.  exec 7 pays [emp], and alone:
   its bundle is consumed and its process never resumes on success.  Every
   number without a contract pays [emp] too.

   THE POST IS READ AT THE RESUME KEY, which is what makes the three
   receipts statable: read's whole effect on its caller is the bytes it put
   in the caller's buffer, which are entries of the image it resumes at
   ([M']); chdir's is the working directory it resumes at ([cw']) and
   open's is one row of the descriptor table it resumes at ([fdv']); none
   is a projection of the TRAP key.  So [UexecSG.spost_at] takes all three
   beside the returned a0, bound by the same [∀] of the arm that binds the
   four pure rows, and the receipts SHARPEN the rows
   [UsysMemOk.usys_mem_ok], [usys_cwd_ok] and [usys_fd_ok] state there:
   "the file's bytes from your offset" rather than "some byte function",
   "the directory you named" rather than "a failed chdir did not move", and
   "the console, at your omode" rather than "some slot became open".  The
   route back to the process is [SpecUsertrap.ut_sys_out] as a row of
   [usertrap_post], produced by the dispatcher's
   [SpecSyscall.sysc_sys_out].

   THE DEPOSIT'S FAMILIES ([UexecSG.sfam]) are a RECORD with one field per
   contracted syscall, so that the arm can bind them once in front of both
   legs and the post comes back at the receipts the process chose.  At this
   instance the record is [xfam]: exec's four, and the walk cursors, piece
   pairs, write's prefix cursor and console seed the other eight contracts
   take.  [xfam_exec] builds one at exec's four with every other field at
   the trivial family -- which is exactly what the two supply laws hand
   back, since those laws ARE [FsAbsInvFire]'s dischargers.

   THE DESCRIPTOR KEY IS [SpecArgfd.fd_st_of_key], NOT [sys_fd_st], and that
   is what makes read's and write's bundles statable here at all: [sys_fd_st]
   reads the process's [ofile] POINTER array, a kernel-side reading no
   process has.  [SpecArgfd.sys_fd_st_of_key] is the equation between the
   two and the DISPATCHER pays it, out of the fragment length,
   [ProcInv.proc_priv]'s length and [ProcInv.proc_priv_states_agree]
   ([ProofSyscall.sysc_fd_key]).

   NOTHING HERE READS A [TsoCtx.CurCtx], and that is a requirement rather
   than an accident (the section note below).  Getting there cost the dead
   context binders on [FsAbsDelta.delta_trunc],
   [SysOpenDefs.atrunc_commit_at] and the [om_*] mode readers,
   [SpecSysOpen.open_in] and [SpecSysMkdir.mkdir_au_pre]/[mkdir_arms] --
   TSO-rebase appends that no body ever read.

   WHAT EXEC'S BUNDLE IS.  [SpecSysExec.sys_exec_au_pre] at the TRAPPING
   KEY's own data -- and open's and mknod's rows (15 and 17) read the same
   two, the image and argument 0, for the same reason: their walks are at
   the path THEIR argument 0 names ([ArgPath.arg_path_of]):
     - the image [uvis_M W]: the arguments are read off the image the
       process trapped at ([wp_sys_exec_sconf_body] takes the bundle at
       [us_M U], and the trap-out key's image IS that image -- the loop
       hands [uvis_M W] to the dispatcher);
     - the argv pointer [tf_w (uvis_tf W) (tf_arg_idx 1)]: sys_exec's
       argument 1, read off the key's trapframe.  ([wp_sys_exec_sconf_body]
       names it [v1] and pins it by [pv_tf (us_V U) !! tf_arg_idx 1 =
       Some v1]; [tf_w] is the total reader of the same word.)
     - the descriptor view [uvis_fd W] as [sts]: the table the NEW process
       starts with is the one the caller had, which is exactly the key's
       ([exec_slot_pre]'s [sts] rides straight into [exec_key U' sts na]).
   The ghost/logical parameters [P], [Pmiss], [Fo] and the slot piece's
   refund are EXISTENTIAL here: the U-mode contract cannot name the
   caller's era predicates, so the arm says only "some AU bundle at this
   key", and the dispatch route re-binds them when it consumes the bundle.

   THE KEY CONGRUENCE is [UexecSG.skey_eq]'s six rows: the bundle reads the
   image, argument word 1, the descriptor view and the working directory,
   and nothing else off its key.

   MONOTONICITY IN THE SLOT FAMILY is the one field whose proof is not a
   projection: the family occurs only as the CONCLUSION of the slot piece's
   two wands (one per success arm), so the upgrader walks in under
   [sys_exec_slot_pre]'s ∀s and [PieceFam.pf_at]'s [∧]-refund, twice.

   THE SUPPLY [ssupply] IS THE APPLICATION'S PREDICATE HELD OF EVERY VIEW
   ([AppInv.app_sup]).  That is the credential an UNVERIFIED program runs
   on: it is what makes a view-moving commit's [AppInv.app_step] free, and
   so what every syscall bundle with a write-kind commit is paid out of.
   Exec's own bundle needs none of it -- [FsAbsInvFire.fsabs_exec_half]
   hands back the walk premise and open's commit at [True] receipts as a
   closed fact, and a generic slot family answers the slot wand at every
   key -- which is why both supply laws below still ignore their argument.
   The supply is spelled here anyway, because it is what the OTHER numbers'
   bundles will be paid from when they are turned on, and because the
   credential has to exist before the dischargers can be re-based on it.
   That is also why this file sits ABOVE the fire tower rather than beside
   SpecSysExec.v: the supply law is a class field, and its exec case is
   [fsabs_exec_half].

   WHERE THE SUPPLY COMES FROM, AND WHY IT IS NOT PARKED.  It is founded
   by the GENERIC application alone, out of the triviality of its own
   predicate ([AppInv.app_sup_of_triv]), at the one place that needs it:
   its discharge of the system theorem's [Hinit_boot]
   ([SystemAdequacy.init_boot_of_sup]), which mints the generic slot on it.
   It cannot ride an era-owned resource -- see [AppInv]'s [app_sup_raw] --
   because a constraining application cannot found it, and it appears in no
   kernel contract for the same reason.

   [Γ] and [γfs] are NOT existential: the whole tree runs at the single
   ambient file system ([FsCfg.fsc_fs] with the derived view names
   [FsBytesGamma.fs_gamma_L fsc_fs]), exactly as [wp_sys_exec_sconf_body]
   pins them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import FdSlots.
Require Import ProcGeom.       (* [tf_arg_idx]                        *)
Require Export SwtchCtx.
Require Import Xv6Cameras.
Require Import IrefSlots.
Require Import FileInvDefs.
Require Import UserFd.         (* [ufdG]                              *)
Require Import UserPtTree.     (* [uptd] / [ud_um] -- row 5's table    *)
Require Import UserPerm.       (* [perm_of] -- and the key's projection *)
Require Import UexecSlot.      (* [uvis] / [tf_w]                     *)
Require Import UsysMemOk.      (* [USYS_exec] -- the one number with a bundle *)
Require Import UexecSG.        (* [uexecSG] / [uprogSG] -- the class   *)
Require Import UexecRet.       (* [uslot] -- the family the generic
                                  inhabitants mint at                 *)
Require Import SpecSysExec.  (* [sys_exec_au_pre]                   *)
Require Import SpecKexec.    (* [exec_slot_pre] -- the piece the
                                  monotonicity walks through          *)
Require FsAbsEra.              (* [ex_start] / [ax_hops_triv]: the walk
                                  one-shot at ONE path, which is the form
                                  exec's bundle states                    *)
Require Import FsAbsInvFire.   (* [fsabs_exec_half] and the eight other
                                  numbers' dischargers, all out of the
                                  supply                              *)
Require Import SpecArgfd.      (* [fd_st_of_key] -- the descriptor key a
                                  PROCESS can name                    *)
Require Import SpecFileread.   (* [fileread_in] / [fileread_extra]    *)
Require Import SpecFilewrite.  (* [filewrite_in] / [filewrite_extra]  *)
Require Import SpecSysRead.    (* [sys_rw_count]                      *)
Require Import SpecSysChdir.   (* [chdir_au_pre]                      *)
Require Import SpecSysOpen.    (* [open_in]                           *)
Require Import SpecSysMknod.   (* [mknod_au_pre] / [mknod_arms]       *)
Require Import SysMknodDefs. (* [dev_arg]                           *)
Require Import SpecSysUnlink.  (* [unlink_au_pre] / [unlink_arms]     *)
Require Import SpecSysLink.    (* [link_commits] / [link_arms]        *)
Require Import SpecSysMkdir.   (* [mkdir_au_pre] / [mkdir_arms]       *)
Require Import FsTree.         (* [fname]                             *)
Require Import AppInv.         (* [app_sup] -- THE SUPPLY.  Required
                                  DIRECTLY: the definition is named in a
                                  class field's body                   *)
Require Import PieceFam.       (* [pfam]: the one-shot piece's pair *)
Require Import FsAbsDefs.          (* LAST (FsAbs's own rule)             *)
Require Import FsBytesGamma.   (* [fs_gamma_L]                        *)
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.
Require Import FsCfg.
Import Defs.

Local Open Scope Z_scope.

Section UexecExecInst.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  (* NO AMBIENT [CurCtx], AND THAT IS A REQUIREMENT, not a convenience.  The
     instance is what [UexecRet.uslot] is indexed by, and [uslot] rides
     through the park ([ParkCap.park_token] reads it) and every other place
     two proofs at two hart contexts meet.  A context-indexed class makes
     those two slots DIFFERENT terms that print identically, and the unifier
     does not stop.  A process's deposit does not depend on the context of
     the kernel proof that consumes it, and the chain the exec bundle names
     ([SpecSysExec.sys_exec_au_pre] down to [SysOpenDefs]'s pieces) does
     not read one. *)
  Context `{GEN : GenId}.

  (* ================================================================== *)
  (* THE DEPOSIT'S FAMILIES, as one record.                               *)
  (*                                                                      *)
  (* One field per syscall whose contract takes caller-chosen families.    *)
  (* The arm binds the whole record ONCE in front of both legs, so what a  *)
  (* process gets back is a post at the very receipts and refunds it       *)
  (* deposited.  Exec's four are the only ones here -- its walk cursor and *)
  (* miss predicate, its observation pair, and the slot piece's refund --  *)
  (* because exec is the only number with a bundle at this round.          *)
  (*                                                                      *)
  (* NOT [Z]-INDEXED (UexecSG.v's header): a record makes [f] a plain      *)
  (* value with no dependency, which is what keeps the fixpoint's          *)
  (* contractivity proof and the trap route's transport free of [eq_rect]. *)
  (* ================================================================== *)
  Record xfam : Type := MkXfam {
    (* ---- exec (7) ---- *)
    xf_P     : nat -> Z -> iProp Σ;
    xf_Pmiss : nat -> Z -> iProp Σ;
    xf_Fo    : pfam Σ (aview -> Z -> anode -> iProp Σ);
    xf_Rs    : iProp Σ;
    (* ---- read (5): one piece, one receipt ---- *)
    rf_F     : pfam Σ (aview -> nat -> anode -> nat -> iProp Σ);
    (* ---- chdir (9): the walk and the terminal observation ---- *)
    cf_P     : nat -> Z -> iProp Σ;
    cf_Pmiss : nat -> Z -> iProp Σ;
    cf_Fo    : pfam Σ (aview -> Z -> anode -> iProp Σ);
    (* ---- open (15): the walk, create's four legs, the two commits ---- *)
    of_P     : nat -> Z -> iProp Σ;
    of_Pmiss : nat -> Z -> iProp Σ;
    of_Farm  : pfam Σ (aview -> Z -> iProp Σ);
    of_Fun   : pfam Σ (aview -> Z -> iProp Σ);
    of_Fok   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    of_Fex   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    of_Fo    : pfam Σ (aview -> Z -> anode -> iProp Σ);
    of_Ft    : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ);
    (* ---- write (16): the chain's PREFIX CURSOR and the console seed ---- *)
    wf_Q     : nat -> iProp Σ;
    wf_tr0   : list (bv 8);
    (* ---- mknod (17) ---- *)
    nf_P     : nat -> Z -> iProp Σ;
    nf_Pmiss : nat -> Z -> iProp Σ;
    nf_Farm  : pfam Σ (aview -> Z -> iProp Σ);
    nf_Fun   : pfam Σ (aview -> Z -> iProp Σ);
    nf_Fok   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    nf_Fex   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    (* ---- unlink (18) ---- *)
    uf_P     : nat -> Z -> iProp Σ;
    uf_Pmiss : nat -> Z -> iProp Σ;
    uf_Fent  : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    uf_Ftgt  : pfam Σ (aview -> Z -> iProp Σ);
    uf_Fex   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    uf_Fmiss : pfam Σ (aview -> Z -> fname -> iProp Σ);
    (* ---- link (19): three commits, no walk (the contract keeps its own) ---- *)
    lf_Ftgt  : pfam Σ (aview -> Z -> anode -> iProp Σ);
    lf_Fent  : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    lf_Funt  : pfam Σ (aview -> Z -> iProp Σ);
    (* ---- mkdir (20): create at T_DIR, so the DOTS leg is real ---- *)
    df_P     : nat -> Z -> iProp Σ;
    df_Pmiss : nat -> Z -> iProp Σ;
    df_Farm  : pfam Σ (aview -> Z -> iProp Σ);
    df_Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ);
    df_Fun   : pfam Σ (aview -> Z -> iProp Σ);
    df_Fok   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    df_Fex   : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ);
    (* ---- fork (1): THE CHILD'S EXIT PAYLOAD ([UexecSG.sfork_pay]) ----
       What the process's child owes it back at exit, as a function of the
       status.  A field of the FAMILIES and not a parameter of fork's rows
       because the trap route splits a return into its deposit and its arm
       and carries them past each other, and [f] is the one value that
       travels with both -- see [UexecSG.v]'s [sfork_pay].  LAST, so every
       positional builder only gained a trailing argument. *)
    kf_pay   : Z -> iProp Σ;
    (* ---- exit (2): THIS PROCESS'S OWN EXIT PAYLOAD
       ([UexecSG.sexit_pay]) ---- What the process's own exit owes its
       parent, on [kf_pay]'s footing and for its reason: the deposit pays
       it and the arm reads it back, and [f] is what carries the two past
       each other.  LAST, again. *)
    kf_xpay  : Z -> iProp Σ;
    (* ---- read (5), second piece: WHAT THE CALLER ASKS TO BE TOLD ABOUT
       THE CONSOLE WINDOW ---- (app-echo.md, lane CONS-CURSOR, C3, and the
       LEASE ruling).  A read of the console takes
       [ConsoleInv.cons_acc fsc_cons app_sup (rf_ret f)] -- ONE ARM, whose
       two disjuncts are a lease holder's token and a tainted caller's
       credential -- and pays [rf_ret f cur dc] back: the position the
       ring's committed sequence stood at, and the advance the cursor made.
       A lease holder chooses "[cur] is my own [n], and here is my token
       back at [cur + dc]"; a generic process chooses [fun _ _ => True].
       A FIELD OF THE FAMILIES because the process CHOOSES it when it builds
       an explicit deposit; the kernel only relays it.  LAST, so every
       positional builder only gained a trailing argument. *)
    rf_ret   : nat -> nat -> iProp Σ;
  }.

  (* THE RE-KEYING ([UexecSG.sfam_at]): the same families at another
     payload.  Every other field passes through, so the two bundle rows are
     unmoved and a leaf can take its supplier's [f] and put its own
     [UkRun.ukn_pay] in it. *)
  Definition xfam_at (Q : Z -> iProp Σ) (f : xfam) : xfam :=
    {| xf_P := xf_P f; xf_Pmiss := xf_Pmiss f; xf_Fo := xf_Fo f;
       xf_Rs := xf_Rs f;
       rf_F     := rf_F f;
       cf_P     := cf_P f; cf_Pmiss := cf_Pmiss f; cf_Fo := cf_Fo f;
       of_P     := of_P f; of_Pmiss := of_Pmiss f;
       of_Farm  := of_Farm f; of_Fun := of_Fun f; of_Fok := of_Fok f;
       of_Fex   := of_Fex f; of_Fo := of_Fo f; of_Ft := of_Ft f;
       wf_Q     := wf_Q f; wf_tr0 := wf_tr0 f;
       nf_P     := nf_P f; nf_Pmiss := nf_Pmiss f;
       nf_Farm  := nf_Farm f; nf_Fun := nf_Fun f; nf_Fok := nf_Fok f;
       nf_Fex   := nf_Fex f;
       uf_P     := uf_P f; uf_Pmiss := uf_Pmiss f;
       uf_Fent  := uf_Fent f; uf_Ftgt := uf_Ftgt f; uf_Fex := uf_Fex f;
       uf_Fmiss := uf_Fmiss f;
       lf_Ftgt  := lf_Ftgt f; lf_Fent := lf_Fent f; lf_Funt := lf_Funt f;
       df_P     := df_P f; df_Pmiss := df_Pmiss f;
       df_Farm  := df_Farm f; df_Fdots := df_Fdots f; df_Fun := df_Fun f;
       df_Fok   := df_Fok f; df_Fex := df_Fex f;
       kf_pay   := kf_pay f;
       kf_xpay  := Q;
       rf_ret   := rf_ret f |}.

  (* THE RECORD AT EXEC'S FOUR AND THE TRIVIAL FAMILIES ELSEWHERE.  The
     eight other numbers' fields are spelled at exactly the families the
     [FsAbsInvFire] dischargers produce, because that is what the two supply
     laws below hand back: a process that answers for no abstract state gets
     its bundles AT THIS RECORD. *)
  Definition xfam_exec_at (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ)
      (pay : Z -> iProp Σ) : xfam :=
    {| xf_P := P; xf_Pmiss := Pmiss; xf_Fo := Fo; xf_Rs := Rs;
       rf_F     := pfam_triv (fun _ _ _ _ => True%I);
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_P     := fun _ _ => True%I;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := pfam_triv (fun _ _ => True%I);
       of_Fun   := pfam_triv (fun _ _ => True%I);
       of_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       wf_Q     := fun _ => True%I;
       wf_tr0   := [];
       nf_P     := fun _ _ => True%I;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := pfam_triv (fun _ _ => True%I);
       nf_Fun   := pfam_triv (fun _ _ => True%I);
       nf_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       nf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_P     := fun _ _ => True%I;
       uf_Pmiss := fun _ _ => True%I;
       uf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       uf_Ftgt  := pfam_triv (fun _ _ => True%I);
       uf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_Fmiss := pfam_triv (fun _ _ _ => True%I);
       lf_Ftgt  := pfam_triv (fun _ _ _ => True%I);
       lf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       lf_Funt  := pfam_triv (fun _ _ => True%I);
       df_P     := fun _ _ => True%I;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := pfam_triv (fun _ _ => True%I);
       df_Fdots := pfam_triv (fun _ _ _ _ => True%I);
       df_Fun   := pfam_triv (fun _ _ => True%I);
       df_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := pay;
       (* the process's OWN payload is the trivial one at every builder
          here: a leaf that has a real one re-keys with [xfam_at]. *)
       kf_xpay  := fun _ => True%I;
       (* A GENERIC PROCESS CLAIMS NOTHING ABOUT THE CONSOLE WINDOW, and is
          told nothing: at [fun _ _ => True] read's console arm is the
          TAINTED disjunct of [ConsoleInv.cons_acc], payable out of
          [AppInv.app_sup] alone, which is what keeps
          [xv6_sbundle_of_supply_ne] -- the generic slot's supply law, a
          FIELD of [UexecSG]'s class, stated at [□ ssupply] -- provable at
          n = 5. *)
       rf_ret   := fun _ _ => True%I |}.

  (* ...AT THE TRIVIAL PAYLOAD, which is what every generic process forks
     with: a generic child's exit owes its parent nothing.  The four-argument
     name is unchanged, so no discharger moved. *)
  Definition xfam_exec (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) : xfam :=
    xfam_exec_at P Pmiss Fo Rs (fun _ => True%I).

  (* the point, for the arms that carry no deposit *)
  Definition xfam_pt : xfam :=
    xfam_exec (fun _ _ => True%I) (fun _ _ => True%I)
              (pfam_triv (fun _ _ _ => True%I)) True%I.

  (* ...AND THE POINT AT A CHOSEN PAYLOAD, which is all a fork leaf needs:
     fork's rows read no other field of the families
     ([UexecSG.sfam_pay]). *)
  Definition xfam_pay (Q : Z -> iProp Σ) : xfam :=
    xfam_exec_at (fun _ _ => True%I) (fun _ _ => True%I)
                 (pfam_triv (fun _ _ _ => True%I)) True%I Q.

  (* ================================================================== *)
  (* THE KEY'S THREE ARGUMENT WORDS, named once.  A bundle reads nothing  *)
  (* else off the key but the image, the descriptor view and the cwd, and *)
  (* that is exactly [UexecSG.skey_eq]'s six rows.                        *)
  (* ================================================================== *)
  Definition xk_a (W : uvis) (i : nat) : mword 64 := tf_w (uvis_tf W) (tf_arg_idx i).

  (* what the program hands over at its exec ecall, at the trapping key
     [W] and at ITS OWN families [f]; the bundle's slot wand concludes at
     [X], the recursive occurrence (see the header) *)
  (* THE PAY FACT RIDES IN THE BUNDLE.  exec builds a slot for the NEW
     image, and a slot is keyed by what its process's exit owes
     ([UkRun.ukn_pay]); exec keeps the process's generation, so the fact
     the depositing process holds is the fact that slot needs -- and the
     kernel can only hand it to [SpecKexec.exec_slot_pre]'s wands if it
     was given it. *)
  (* AT THE FAMILY'S OWN EXIT PAYLOAD [kf_xpay] ([UexecSG.sexit_pay]),
     BECAUSE exec KEEPS THE PROCESS.  The image the kernel loads is a new
     PROGRAM at the same process -- same generation
     ([KexecDefs.KexecOkQ]'s [pv_gen V' = pv_gen V]), same parent, same
     debt -- so the payload the new image's run holds IS this process's
     own: the one its exit will pay ([UkRun.ukn_pay]) and the one the trap
     route is carrying across this very call ([SpecSyscall.sysc_pay_in],
     at [sexit_pay f]).  [kf_pay] ([UexecSG.sfork_pay]) is a DIFFERENT
     payload -- what a CHILD's exit owes its parent -- and belongs to
     fork, where a second process really is created.  The consequence is
     CONS-ROUTE's at read, one syscall over: exec's bundle READS the
     payload, so re-keying is no longer an identity here
     ([UexecSG.sbundle_at_at] is guarded off exec as well as read) and
     every supplier names its payload up front ([sbundle_pay_exec_intro],
     [UkRun.uxsup]). *)
  Definition exec_sbundle (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      : iProp Σ :=
    (my_pay (uvis_gen W) (kf_xpay f) ∗
     sys_exec_au_pre (MkPfam X (xf_Rs f)) (fs_gamma_L fsc_fs) fsc_fs
       (uvis_cwd W) (kf_xpay f) (xf_P f) (xf_Pmiss f) (xf_Fo f)
       (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
       (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W))%I.

  Lemma exec_sbundle_ne (n : nat) :
    Proper (dist n ==> eq ==> eq ==> dist n) exec_sbundle.
  Proof.
    intros X Y HXY f ? <- W ? <-. rewrite /exec_sbundle.
    (* the pay row does not mention the slot predicate, so it is untouched
       by the distance; only the AU half moves *)
    rewrite (sys_exec_au_pre_ne n X Y (xf_Rs f) (fs_gamma_L fsc_fs) fsc_fs
               (uvis_cwd W) (kf_xpay f) (xf_P f) (xf_Pmiss f) (xf_Fo f)
               (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
               (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) HXY).
    reflexivity.
  Qed.

  (* THE GENERATION IS A PREMISE NOW, beside the five readings the AU half
     uses: the bundle carries the depositing process's pay fact, which is
     keyed at the key's own generation ([UexecSG.skey_eq] carries the
     equality, so no caller gains an obligation). *)
  Lemma exec_sbundle_cong (X : uvis -d> iPropO Σ) (f : xfam) (W W' : uvis) :
    uvis_M W = uvis_M W' ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = tf_w (uvis_tf W') (tf_arg_idx 0) ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = tf_w (uvis_tf W') (tf_arg_idx 1) ->
    uvis_fd W = uvis_fd W' ->
    uvis_cwd W = uvis_cwd W' ->
    uvis_gen W = uvis_gen W' ->
    exec_sbundle X f W ⊣⊢ exec_sbundle X f W'.
  Proof.
    intros HM Hpv Hav Hfd Hcw Hgn.
    rewrite /exec_sbundle HM Hpv Hav Hfd Hcw Hgn. reflexivity.
  Qed.

  (* ===================================================================== *)
  (* THE CLASS INSTANCE.                                                     *)
  (*                                                                         *)
  (* [sbundle_at] is ONE MATCH ON THE NUMBER, and each branch is that         *)
  (* syscall's landed INPUT read off the key: the process's own families      *)
  (* [f], the image, the three argument words, the descriptor view and the    *)
  (* working directory, and nothing else.  Every branch is a definition       *)
  (* already proved against the code -- no parallel form is introduced here.  *)
  (*                                                                          *)
  (* READ AND WRITE ARE KEYED AT [SpecArgfd.fd_st_of_key], not at             *)
  (* [sys_fd_st]: the latter reads the process's [ofile] POINTER array, a     *)
  (* kernel-side reading no process has.  [SpecArgfd.sys_fd_st_of_key] is     *)
  (* the equation, and its three premises are the DISPATCHER's (the fragment  *)
  (* length, [proc_priv]'s length and [ProcInv.proc_priv_states_agree]), so   *)
  (* the bridge is paid where the kernel resources are and the deposit stays  *)
  (* statable at a key.                                                       *)
  (* ===================================================================== *)
  Definition xv6_sbundle (X : uvis -d> iPropO Σ) (n : Z) (f : xfam) (W : uvis)
      : iProp Σ :=
    (if decide (n = USYS_exec) then exec_sbundle X f W
     else if decide (n = 5) then
       (* AT THE FAMILY'S OWN EXIT PAYLOAD (app-echo.md, "SH-LINE RULING",
          R1).  read's deposit is a WAND from what this process's exit owes
          at the kill status, because a program whose payload holds the
          console reader token has handed that payload to the kernel at
          this very trap ([UexecRet.uexec_pay_dep]) and holds no second
          copy.  The kernel feeds the payment row's own resource back in
          and the console arm returns it inside [rf_ret]. *)
       fileread_in (fd_st_of_key (xk_a W 0) (uvis_fd W)) (rf_F f) (rf_ret f)
         (kf_xpay f (-1))
     else if decide (n = 9) then
       chdir_au_pre (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (cf_P f) (cf_Pmiss f) (cf_Fo f)
     else if decide (n = 15) then
       (* ...AT THE PATH ARGUMENT, beside the omode: row 15 reads argument
          0 (the path POINTER) through the key's own image
          ([ArgPath.arg_path_of (uvis_M W) (xk_a W 0)]) as well as argument
          1 (the omode), so what the process deposits is the walk at the
          string IT passed -- what a pinned open hands in and what open's
          receipt at row 15 below names. *)
       open_in (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (uvis_M W) (xk_a W 0) (xk_a W 1)
         (of_P f) (of_Pmiss f) (of_Farm f) (of_Fun f) (of_Fok f) (of_Fex f)
         (of_Fo f) (of_Ft f)
     else if decide (n = 16) then
       filewrite_in (fd_st_of_key (xk_a W 0) (uvis_fd W))
         (sys_rw_count (xk_a W 2)) (uvis_M W) (xk_a W 1) (wf_Q f) (wf_tr0 f)
     else if decide (n = 17) then
       (* ...and mknod's, at ITS path argument beside the two device
          numbers, for open's reason *)
       mknod_au_at (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (uvis_M W) (xk_a W 0)
         (dev_arg (xk_a W 1)) (dev_arg (xk_a W 2))
         (nf_P f) (nf_Pmiss f) (nf_Farm f) (nf_Fun f) (nf_Fok f) (nf_Fex f)
     else if decide (n = 18) then
       unlink_au_pre (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (uf_P f) (uf_Pmiss f) (uf_Fent f) (uf_Ftgt f) (uf_Fex f) (uf_Fmiss f)
     else if decide (n = 19) then
       link_commits (fs_gamma_L fsc_fs) (lf_Ftgt f) (lf_Fent f) (lf_Funt f)
     else if decide (n = 20) then
       mkdir_au_pre (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (df_P f) (df_Pmiss f) (df_Farm f) (df_Fdots f) (df_Fun f)
         (df_Fok f) (df_Fex f)
     else emp)%I.

  (* ...AND THE ARMED POST BACK, at the same key and the same families.
     WHICH NUMBERS PAY A POST -- eight of them.  Each branch is that syscall's own landed armed
     post, read off the SAME key projections its input branch above is read
     off -- so what a process gets back is a statement about the very
     receipts, refunds and cursors it deposited:
       5   [SpecFileread.fileread_extra] at [SpecArgfd.fd_st_of_key], at the
           RESUME IMAGE [M'] and the buffer address argument 1 -- the
           receipt names the bytes read() put in the caller's buffer; and 16
           [SpecFilewrite.filewrite_extra] at the same key -- WITHOUT the
           landed pure blanket ([fileread_ret] / [filewrite_ret]), which
           reads [pv_ofile V], a kernel array no process can name, while the
           round already carries [UsysMemOk.usys_mem_ok] / [usys_fd_ok];
       17/18/19/20  the contract's arms verbatim ([mknod_arms] /
           [unlink_arms] / [link_arms] / [mkdir_arms]).
       9/15  the contract's RECEIPT ([SpecSysChdir.chdir_receipt],
           [SpecSysOpen.open_receipt]).  These two arms are the ones whose
           landed form bundles kernel resources -- [ProcInv.proc_priv] at
           the block the syscall wrote, the descriptor fragments and
           [FdSlots.fd_slot] -- so what comes back here is the arms' OTHER
           half: the walk cursor, the observed rows, the fired receipts, the
           trunc leg, and, in place of the resources, the pure fact about
           the key the process RESUMES at ([cw'] for chdir, one row of
           [fdv'] for open).  [SpecSysChdir.chdir_arms_split] and
           [SpecSysOpen.open_arms_split] are the ties, and the dispatcher
           keeps the kernel half.
     ONE PAYS [emp]:
       7   exec's bundle is CONSUMED and its process never resumes on
           success -- there is nothing to give back.
     Every number without a contract pays [emp] too.

     THE RESUME KEY'S THREE MOVING COMPONENTS, [M'], [fdv'] and [cw'], are
     arguments here for exactly the three receipts that read them: the
     bytes read() delivered are entries of the resume image, a descriptor
     is a row of the table the call returns to, and a working directory IS
     the field chdir wrote.  The other five branches ignore them, as does
     every contract-free number.

     THE SLOT FAMILY [X] DOES NOT OCCUR: a post is what comes back to the
     process that is RESUMING, so no branch concludes at the fixpoint
     variable the way exec's input bundle does.  That is what makes
     non-expansiveness a [reflexivity]. *)
  (* [cs'] is the RESUME KEY'S CHILDREN SET, beside [fdv'] and [cw'] and for
     their reason: a receipt may be about what the call left in the resume
     key, and wait(2)'s is about exactly that.  No entry's post reads it
     yet -- the eight below are file-system entries -- so every branch
     ignores it. *)
  Definition xv6_spost (X : uvis -d> iPropO Σ) (n : Z) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z)
      (cs' : gset gname)
      : iProp Σ :=
    (if decide (n = 5) then
       (* THE PAYLOAD IS PEELED: what the PROCESS is told is
          [SpecFileread.fileread_extra_core], the arm's payout without the
          borrowed payload -- the payload goes back on the trap's own
          resume row ([UexecRet.uexec_pay_arm]), so this post is unchanged
          in force by R1.

          ...AND THE TABLE IS EXISTENTIAL, AT THE KEY'S OWN PROJECTION
          (app-echo.md, lane CONS-SWALLOW, W4).  The receipt is stated at
          the process's PAGE TABLE -- whether a byte read() popped reached
          the caller's buffer is a fact about that table
          ([SpecFileread.console_receipt]) -- and the key carries no
          table, only the per-page permission map [uvis_perm] it projects
          to.  So what the process is told here is that SOME table
          projecting to its own key's permission map was the one the call
          ran on: the honest weak form, since the projection cannot see
          which pages are lazily unmapped ([UserPerm]'s note on
          [perm_fill], and [ProcPtOwn.perm_of_uptd_ext_sz] -- MAP-KEY is
          what would strengthen it).  The dispatcher supplies the
          process's own [pv_upt (us_V U)] and the equation holds by
          [UexecSlot.uvis_of]'s definition ([ProofSyscall.sysc_out_read]).
          READING THE KEY HERE IS WHY [UexecSG.skey_eq] FIXES THE
          PERMISSION MAP AND THE SIZE. *)
       (* ...AND THE TABLE IS WELL-FORMED AND THE KEY'S LAZY BIT IS A CLAIM
          ABOUT IT (lane LAZY-FLAG, L5).  The projection cannot tell a page
          vmfault has yet to serve from a mapped RW page, and copyout can
          write only the second kind -- so the ∃ table is exhibited WITH
          what the key's bit claims about it ([UserPerm.lazy_free]) and with
          the well-formedness [UserPerm.lazy_free_wmapped] consumes.  At
          [uvis_lazy W = false] a process that owns a byte of its own buffer
          can then refute the receipt's copyout-fault disjunct; at [true] it
          learns nothing new, which is the honest reading of a process that
          may have called sbrklazy.  Both come off the DISPATCHER's own
          block: well-formedness from [ProcPtOwn.proc_ptm], and the claim
          from [ProcInv.proc_priv_core]'s invariant on
          [ProcDefs.pv_lazy]. *)
       (∃ P : uptd,
          ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
          ⌜ProcPtOwn.proc_pt_wf P⌝ ∗
          ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
          fileread_extra_core P (fd_st_of_key (xk_a W 0) (uvis_fd W))
            (sys_rw_count (xk_a W 2)) (rf_F f) (rf_ret f) r M' (xk_a W 1))
     else if decide (n = 9) then
       chdir_receipt (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (cf_P f) (cf_Pmiss f) (cf_Fo f) r cw'
     else if decide (n = 15) then
       open_receipt (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (uvis_M W) (xk_a W 0) (xk_a W 1)
         (of_P f) (of_Pmiss f) (of_Farm f) (of_Fun f) (of_Fok f) (of_Fex f)
         (of_Fo f) (of_Ft f) (uvis_fd W) r fdv'
     else if decide (n = 16) then
       filewrite_extra (fd_st_of_key (xk_a W 0) (uvis_fd W))
         (sys_rw_count (xk_a W 2)) (uvis_M W) (xk_a W 1)
         (wf_Q f) (wf_tr0 f) r
     else if decide (n = 17) then
       mknod_arms (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (uvis_M W) (xk_a W 0)
         (dev_arg (xk_a W 1)) (dev_arg (xk_a W 2))
         (nf_P f) (nf_Pmiss f) (nf_Farm f) (nf_Fun f) (nf_Fok f) (nf_Fex f) r
     else if decide (n = 18) then
       unlink_arms (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (uf_P f) (uf_Pmiss f) (uf_Fent f) (uf_Ftgt f) (uf_Fex f) (uf_Fmiss f) r
     else if decide (n = 19) then
       link_arms (fs_gamma_L fsc_fs) (lf_Ftgt f) (lf_Fent f) (lf_Funt f) r
     else if decide (n = 20) then
       mkdir_arms (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
         (df_P f) (df_Pmiss f) (df_Farm f) (df_Fdots f) (df_Fun f)
         (df_Fok f) (df_Fex f) r
     else emp)%I.

  (* THE SLOT FAMILY OCCURS IN ONE BRANCH OF THE DEPOSIT -- exec's slot wand
     -- so that non-expansiveness proof is that branch and eight
     [reflexivity]s, and the POST's is one [reflexivity]: no post concludes
     at the fixpoint variable. *)
  Ltac xv6_num_cases :=
    repeat (match goal with
            | |- context [decide (?n = ?k)] =>
                destruct (decide (n = k)) as [_ | _]; [| ]
            end).

  Lemma xv6_sbundle_ne (k : nat) :
    Proper (dist k ==> eq ==> eq ==> eq ==> dist k) xv6_sbundle.
  Proof.
    intros X Y HXY n ? <- f ? <- W ? <-. rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _];
      [ exact (exec_sbundle_ne k X Y HXY f f eq_refl W W eq_refl) | ].
    xv6_num_cases; reflexivity.
  Qed.

  Lemma xv6_spost_ne (k : nat) :
    Proper (dist k ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> dist k)
      xv6_spost.
  Proof.
    intros X Y _ n ? <- f ? <- W ? <- r ? <- M' ? <- fdv' ? <- cw' ? <- cs' ? <-.
    reflexivity.
  Qed.

  (* THE KEY CONGRUENCE, off [UexecSG.skey_eq]: every branch reads the image,
     one of the three argument words, the descriptor view or the working
     directory, and [skey_eq] pins all six. *)
  Lemma xv6_sbundle_cong (X : uvis -d> iPropO Σ) (n : Z) (f : xfam)
      (W W' : uvis) :
    skey_eq W W' -> xv6_sbundle X n f W ⊣⊢ xv6_sbundle X n f W'.
  Proof.
    intros Hk.
    pose proof Hk as (HM & Ha0 & Ha1 & Ha2 & Hfd & Hcw & Hgn & _ & _ & _ & _).
    rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _];
      [ exact (exec_sbundle_cong X f W W' HM Ha0 Ha1 Hfd Hcw Hgn) | ].
    rewrite /xk_a /tf_w HM Ha0 Ha1 Ha2 Hfd Hcw.
    reflexivity.
  Qed.

  (* ...and the post's, at the same rows PLUS the permission map and the
     size, which read(2)'s receipt reads ([xv6_spost]'s row 5 names the
     table its key projects from) and [skey_eq] pins for that reason. *)
  Lemma xv6_spost_cong (X : uvis -d> iPropO Σ) (n : Z) (f : xfam)
      (W W' : uvis) (r : mword 64) (M' : gmap Z (bv 8))
      (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    skey_eq W W' ->
    xv6_spost X n f W r M' fdv' cw' cs' ⊣⊢ xv6_spost X n f W' r M' fdv' cw' cs'.
  Proof.
    intros Hk.
    pose proof Hk as (HM & Ha0 & Ha1 & Ha2 & Hfd & Hcw & _ & _ & _ & Hpi & Hsz
                      & Hlz).
    rewrite /xv6_spost /xk_a /tf_w HM Ha0 Ha1 Ha2 Hfd Hcw Hpi Hsz Hlz.
    reflexivity.
  Qed.

  (* MONOTONICITY IN THE SLOT FAMILY.  The family occurs in exactly one
     branch -- the CONCLUSION of both of exec's slot piece's wands
     ([exec_slot_pre]) -- so the upgrader walks in under the piece's ∀s and
     its [∧]-refund, once per success arm, and every other branch is the
     identity. *)
  Lemma xv6_sbundle_mono (X Y : uvis -d> iPropO Σ) (n : Z) (f : xfam)
      (W : uvis) :
    ⊢ □ (∀ W' : uvis, X W' -∗ Y W') -∗
      xv6_sbundle X n f W -∗ xv6_sbundle Y n f W.
  Proof.
    iIntros "#Hup Hb". rewrite /xv6_sbundle.
    destruct (decide (n = USYS_exec)) as [_ | _];
      [ | xv6_num_cases; iExact "Hb" ].
    rewrite /exec_sbundle.
    rewrite /sys_exec_au_pre.
    (* the pay row is untouched by the slot's monotonicity: it mentions no
       slot predicate *)
    iDestruct "Hb" as "(#Hmp & Hwalk & Hcommit & Hslot)".
    iFrame "Hmp Hwalk Hcommit".
    rewrite /pf_at. cbn [pf_recv pf_refund].
    iSplit; [ | iDestruct "Hslot" as "[_ $]" ].
    iDestruct "Hslot" as "[Hslot _]".
    rewrite /sys_exec_slot_pre.
    iIntros (pl na alen afun) "%Hpsh %Hsh".
    iDestruct ("Hslot" $! pl na alen afun with "[%] [%]") as "Hslot";
      [ exact Hpsh | exact Hsh | ].
    (* BOTH success arms' wands conclude at the family, so the upgrader
       walks in twice. *)
    rewrite /exec_slot_pre.
    iDestruct "Hslot" as "[Hsa Hsb]".
    iSplitL "Hsa".
    - iIntros (av i ff nl W') "HP Ho %Hld %Him %Hcwq %Hlzq Hpy HQ".
      iApply "Hup".
      iApply ("Hsa" $! av i ff nl W' with "HP Ho [%] [%] [%] [%] Hpy HQ");
        [ exact Hld | exact Him | exact Hcwq | exact Hlzq ].
    - iIntros (av i a W') "HP Ho %Hnl %Hkk %Hcwq %Hlzq Hpy HQ".
      iApply "Hup".
      iApply ("Hsb" $! av i a W' with "HP Ho [%] [%] [%] [%] Hpy HQ");
        [ exact Hnl | exact Hkk | exact Hcwq | exact Hlzq ].
  Qed.

  (* THE SUPPLY.  Opaque in the class, and at THIS instance it is the
     application's predicate held of EVERY view ([AppInv.app_sup]) -- the
     credential that makes a write-kind commit's [AppInv.app_step] free, and
     hence the one an unverified program's bundles are paid from.  Every
     branch of the two laws below is one [FsAbsInvFire] discharger at the
     trivial families, which is exactly the record [xfam_pt] names. *)
  Definition xv6_ssupply : iProp Σ := app_sup.

  (* THE BUPD IS WRITE'S, AND ONLY WRITE'S: the console arm carries the trace
     seed [UartSentLoc.uart_sent γu []], a mono-list lower bound at the empty
     list -- the algebra's unit, mintable by anyone but not derivable from
     [emp].  Every other branch is a closed fact or a wand off the supply. *)
  (* AT THE PAYLOAD THE CALLER NAMES (app-echo.md, "SH-LINE RULING", R1).
     The point re-keyed at [Q] ([xfam_at]) is the witness: every branch but
     read's ignores the payload, and read's -- the console arm -- is
     payable out of the persistent credential at ANY [P]
     ([FsAbsInvFire.fsabs_fileread_in]), because what it owes back is
     [∀ cur dc, |==> P ∗ True] and a [∀] over a constant IS that constant.
     Nothing is duplicated: the caller gets its [P] back at the ONE
     position the read landed on. *)
  Lemma xv6_sbundle_of_supply_ne (X : uvis -d> iPropO Σ) (n : Z) (W : uvis)
      (Q : Z -> iProp Σ) :
    n <> USYS_exec ->
    ⊢ □ xv6_ssupply ==∗ ∃ f : xfam, ⌜kf_xpay f = Q⌝ ∗ xv6_sbundle X n f W.
  Proof.
    intros Hne. rewrite /xv6_ssupply. iIntros "#Hsup".
    iAssert (|==> xv6_sbundle X n (xfam_at Q xfam_pt) W)%I with "[]" as "Hb";
      [ | iMod "Hb" as "Hb"; iModIntro; iExists (xfam_at Q xfam_pt);
          iSplitR; [ done | iExact "Hb" ] ].
    rewrite /xv6_sbundle /xfam_at /xfam_pt /xfam_exec /=.
    destruct (decide (n = USYS_exec)) as [He | _];
      [ exfalso; exact (Hne He) | ].
    destruct (decide (n = 5)) as [_ | _];
      [ iModIntro; iApply (fsabs_fileread_in with "Hsup") | ].
    destruct (decide (n = 9)) as [_ | _];
      [ iModIntro; iApply fsabs_chdir_pre | ].
    destruct (decide (n = 15)) as [_ | _];
      [ iModIntro; iApply (fsabs_open_in with "Hsup") | ].
    destruct (decide (n = 16)) as [_ | _];
      [ iApply (fsabs_filewrite_in with "Hsup") | ].
    destruct (decide (n = 17)) as [_ | _];
      [ iModIntro; iApply (fsabs_mknod_pre with "Hsup") | ].
    destruct (decide (n = 18)) as [_ | _];
      [ iModIntro; iApply (fsabs_unlink_pre with "Hsup") | ].
    destruct (decide (n = 19)) as [_ | _];
      [ iModIntro; iApply (fsabs_link_pre with "Hsup") | ].
    destruct (decide (n = 20)) as [_ | _];
      [ iModIntro; iApply (SpecSysMkdir.mkdir_au_pre_unit with "Hsup") | ].
    by iModIntro.
  Qed.

  (* ...and the half the generic inhabitants use: the same eight branches
     plus exec, whose fs half is [fsabs_exec_half] out of the invariant and
     whose slot wand a generic family answers at every key. *)
  (* THE FAMILY IS INDEXED BY THE PAY FACT ([UexecSG]'s own law): a slot
     that is safe at every key has to be able to pay exit's deposit, and
     the credential for that is the key's own generation at the payload
     the slot runs at.  AT A CONSTANT PAYLOAD [fun _ => R] (GENERIC-PAY):
     the generic slot HOLDS one [R] and pays exit's additive
     [R ∧ R] out of it.  The exec branch RELAYS it -- both slot wands hand
     the pay fact AND [kf_xpay f (-1)] in at the resume key, and at a
     constant payload that resource is the [R] the next image's slot is
     minted from.  [R := True] is the trivial instance. *)
  Lemma xv6_sbundle_of_supply (X : uvis -d> iPropO Σ) (n : Z) (W : uvis)
      (R : iProp Σ) :
    ⊢ my_pay (uvis_gen W) (fun _ => R)%I -∗ □ xv6_ssupply -∗
      □ (∀ W' : uvis, my_pay (uvis_gen W') (fun _ => R)%I -∗ R -∗ X W') ==∗
      ∃ f : xfam, ⌜kf_xpay f = (fun _ => R)%I⌝ ∗ xv6_sbundle X n f W.
  Proof.
    rewrite /xv6_ssupply. iIntros "#Hpay #Hsup #Hs".
    destruct (decide (n = USYS_exec)) as [He | Hne].
    - iModIntro. iExists (xfam_at (fun _ => R)%I xfam_pt). iSplitR; [done |].
      rewrite /xv6_sbundle. destruct (decide (n = USYS_exec)) as [_ | Hc];
        [ | exfalso; exact (Hc He) ].
      rewrite /exec_sbundle /xfam_at /xfam_pt /xfam_exec /xfam_exec_at /=.
      (* the bundle's own pay row, which the exec'ing process hands the
         kernel so that the kernel can hand it to the new image's slot *)
      iSplitR; [ iExact "Hpay" | ].
      (* read-kind only ([fsabs_exec_half]): the environment is carried, not
         spent *)
      iDestruct (fsabs_exec_half (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W))
        as "[#Hwalk #Hcommit]".
      rewrite /sys_exec_au_pre.
      (* THE WALK, AT WHATEVER PATH.  A family that tracks nothing owes the
         one-shot at every string, and every hop of it says yes -- proved
         here rather than converted from [Hwalk] through
         [FsAbsOpenFire.opf_start_of_open], whose own [CurCtx] binder this
         file has no instance for (the header's "NO AMBIENT [CurCtx]"). *)
      iSplitR;
        [ iIntros (pl) "_";
          rewrite /FsAbsEra.ex_start /FsAbsEra.ex_hops_from;
          iIntros (r) "_"; iModIntro; iSplit;
          [ done | iApply FsAbsEra.ax_hops_triv ] | ].
      iSplitR; [iExact "Hcommit" |].
      rewrite /pf_at. cbn [pf_recv pf_refund]. iSplit; [| done].
      rewrite /sys_exec_slot_pre. iIntros (pl na alen afun) "_ _".
      (* the generic family answers BOTH success arms' wands; the payload
         at this record is the constant [fun _ => R], so the [Q (-1)] each
         wand takes is the [R] the new image's slot runs on and is handed
         straight to the credential. *)
      rewrite /exec_slot_pre. iSplitR.
      + iIntros (av' i ff nl W') "_ _ _ _ _ _ Hp HQ". iApply ("Hs" with "Hp HQ").
      + iIntros (av' i a W') "_ _ _ _ _ _ Hp HQ". iApply ("Hs" with "Hp HQ").
    - iApply (xv6_sbundle_of_supply_ne X n W (fun _ => R)%I Hne).
      iExact "Hsup".
  Qed.

  (* THE RE-KEYING PASSES THROUGH BOTH BUNDLE ROWS ([UexecSG.sbundle_at_at]
     / [spost_at_at]): neither reads [kf_xpay], so re-keying the payload
     leaves what the process deposits and what it is handed back alone.
     [destruct f] rather than [eq_refl]: it turns the record into its
     constructor, so the projections in both bodies reduce by iota instead
     of by unfolding this file's twelve-number dispatch twice. *)
  (* ...AT EVERY NUMBER BUT read AND exec, the two branches that read
     [kf_xpay]: read's deposit is a wand from it (R1) and exec's carries it
     to the new image's slot (EXEC-PAY). *)
  Lemma xfam_at_sbundle (X : uvis -d> iPropO Σ) (n : Z) (Q : Z -> iProp Σ)
      (f : xfam) (W : uvis) :
    n <> USYS_read -> n <> USYS_exec ->
    xv6_sbundle X n (xfam_at Q f) W = xv6_sbundle X n f W.
  Proof.
    intros Hne Hnx. rewrite /xv6_sbundle. destruct f.
    destruct (decide (n = USYS_exec)) as [He | _]; [exfalso; exact (Hnx He) |].
    destruct (decide (n = 5)) as [He | _]; [exfalso; exact (Hne He) |].
    reflexivity.
  Qed.

  Lemma xfam_at_spost (X : uvis -d> iPropO Σ) (n : Z) (Q : Z -> iProp Σ)
      (f : xfam) (W : uvis) :
    xv6_spost X n (xfam_at Q f) W = xv6_spost X n f W.
  Proof. destruct f; reflexivity. Qed.

  Global Instance uexecSG_xv6 : uexecSG Σ :=
    {| sfam := xfam;
       sfam_pt := xfam_pt;
       sfork_pay := kf_pay;
       sfam_pay := xfam_pay;
       sfork_pay_pay := fun Q => eq_refl;
       sfork_pay_pt := eq_refl;
       sexit_pay := kf_xpay;
       sfam_at := xfam_at;
       sexit_pay_at := fun Q f => eq_refl;
       sfork_pay_at := fun Q f => eq_refl;
       sexit_pay_pt := eq_refl;
       sbundle_at_at := xfam_at_sbundle;
       spost_at_at := xfam_at_spost;
       sbundle_at := xv6_sbundle;
       spost_at := xv6_spost;
       sbundle_at_ne := xv6_sbundle_ne;
       spost_at_ne := xv6_spost_ne;
       sbundle_at_cong := xv6_sbundle_cong;
       spost_at_cong := xv6_spost_cong;
       sbundle_at_mono := xv6_sbundle_mono;
       ssupply := xv6_ssupply;
       sbundle_of_supply_ne := xv6_sbundle_of_supply_ne;
       sbundle_of_supply := xv6_sbundle_of_supply |}.

  (* ...AND THE GENERIC PROGRAM'S OWN DEPOSIT DATA ([UexecSG.uprogSG]): the
     supply itself, and every number admitted -- which is what makes the
     generic slot's minting law hold at every key ([sbundle_of_supply_ne] is
     the whole proof).  A verified program with a weaker supplier declares
     its own instance beside its constructor. *)
  Global Instance uprogSG_gen : uprogSG Σ :=
    {| Dsup := xv6_ssupply;
       psok := fun _ : Z => True |}.

  (* ...and the two at the class field, which is [exec_sbundle] at 7: what
     a consumer that speaks [UexecSG.sbundle_at] reads it back at.  The
     INTRO is at the families the caller chose (packed into the record);
     the ELIM is at the [∃] the family-free reader carries. *)
  (* ================================================================== *)
  (* THE PER-NUMBER READERS the dispatcher's arms take the deposit back    *)
  (* through.  Each is the match at one literal, and nothing else: an arm  *)
  (* knows its own number ([sysc_arm_goal]'s [Hnum]) and reads its own     *)
  (* branch.                                                               *)
  (* ================================================================== *)
  Local Ltac xv6_skip :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [Hc | _]; [ exfalso; by vm_compute in Hc | ]
    end.
  Local Ltac xv6_take :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [_ | Hc]; [ | exfalso; by apply Hc ]
    end.

  Lemma sbundle_at_read_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 5 f W -∗
    fileread_in (fd_st_of_key (tf_w (uvis_tf W) (tf_arg_idx 0)) (uvis_fd W))
      (rf_F f) (rf_ret f) (kf_xpay f (-1)).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_chdir_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 9 f W -∗
    chdir_au_pre (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (cf_P f) (cf_Pmiss f) (cf_Fo f).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_open_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 15 f W -∗
    open_in (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1))
      (of_P f) (of_Pmiss f) (of_Farm f) (of_Fun f) (of_Fok f) (of_Fex f)
      (of_Fo f) (of_Ft f).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_write_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 16 f W -∗
    filewrite_in (fd_st_of_key (tf_w (uvis_tf W) (tf_arg_idx 0)) (uvis_fd W))
      (sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2))) (uvis_M W)
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (wf_Q f) (wf_tr0 f).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_mknod_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 17 f W -∗
    mknod_au_at (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (dev_arg (tf_w (uvis_tf W) (tf_arg_idx 1)))
      (dev_arg (tf_w (uvis_tf W) (tf_arg_idx 2)))
      (nf_P f) (nf_Pmiss f) (nf_Farm f) (nf_Fun f) (nf_Fok f) (nf_Fex f).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_unlink_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 18 f W -∗
    unlink_au_pre (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (uf_P f) (uf_Pmiss f) (uf_Fent f) (uf_Ftgt f) (uf_Fex f) (uf_Fmiss f).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip.
    xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_link_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 19 f W -∗
    link_commits (fs_gamma_L fsc_fs) (lf_Ftgt f) (lf_Fent f) (lf_Funt f).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip.
    xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_mkdir_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X 20 f W -∗
    mkdir_au_pre (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (df_P f) (df_Pmiss f) (df_Farm f) (df_Fdots f) (df_Fun f)
      (df_Fok f) (df_Fex f).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip.
    xv6_skip. xv6_take. iExact "H".
  Qed.

  (* THE PAY ROW COMES IN BESIDE THE AU HALF, and at the TRIVIAL payload:
     [xfam_exec] is the record at the generic payloads (both [kf_pay] and
     [kf_xpay] of [xfam_exec] are [fun _ => True]), which is what a process
     that answers for no abstract state forks and execs with.  A process
     with a real payload introduces its bundle at it instead
     ([sbundle_pay_exec_intro]). *)
  Lemma sbundle_at_exec_intro (X : uvis -d> iPropO Σ) (W : uvis)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) :
    my_pay (uvis_gen W) (fun _ => True)%I -∗
    sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (fun _ => True)%I P Pmiss Fo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) -∗
    sbundle_at X USYS_exec (xfam_exec P Pmiss Fo Rs) W.
  Proof.
    iIntros "Hmp H". rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite /exec_sbundle /=. iFrame "Hmp". iExact "H".
  Qed.

  Lemma sbundle_exec_intro (X : uvis -d> iPropO Σ) (W : uvis)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) :
    my_pay (uvis_gen W) (fun _ => True)%I -∗
    sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (fun _ => True)%I P Pmiss Fo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) -∗
    sbundle X USYS_exec W.
  Proof.
    iIntros "Hmp H". rewrite /sbundle. iExists (xfam_exec P Pmiss Fo Rs).
    iApply (sbundle_at_exec_intro X W P Pmiss Fo Rs with "Hmp H").
  Qed.

  (* ...AND THE SAME AT THE DEPOSITING PROCESS'S OWN PAYLOAD, which is what
     a leaf actually owes now (app-echo.md, "SH-LINE RULING", R1, at exec):
     exec's bundle READS the payload -- it is the one the kernel hands the
     new image's slot ([SpecKexec.exec_slot_pre]) -- so a supplier cannot
     mint at some family and re-key afterwards ([UexecSG.sbundle_at_at] no
     longer licenses it at exec); it states its payload up front and this
     is the introduction that names it. *)
  Lemma sbundle_pay_exec_intro (X : uvis -d> iPropO Σ) (W : uvis)
      (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) :
    my_pay (uvis_gen W) Q -∗
    sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      Q P Pmiss Fo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) -∗
    sbundle_pay X USYS_exec Q W.
  Proof.
    iIntros "Hmp H". rewrite /sbundle_pay.
    iExists (xfam_at Q (xfam_exec P Pmiss Fo Rs)).
    iSplitR; [ done | ].
    rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite /exec_sbundle /=. iFrame "Hmp". iExact "H".
  Qed.

  Lemma sbundle_at_exec_elim (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis) :
    sbundle_at X USYS_exec f W -∗
    my_pay (uvis_gen W) (kf_xpay f) ∗
    sys_exec_au_pre (MkPfam X (xf_Rs f)) (fs_gamma_L fsc_fs) fsc_fs
      (uvis_cwd W) (kf_xpay f) (xf_P f) (xf_Pmiss f) (xf_Fo f)
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W).
  Proof.
    iIntros "H". rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite /exec_sbundle. iExact "H".
  Qed.

  Lemma sbundle_exec_elim (X : uvis -d> iPropO Σ) (W : uvis) :
    sbundle X USYS_exec W -∗
    ∃ (Q : Z -> iProp Σ) (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ),
      my_pay (uvis_gen W) Q ∗
      sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
        Q P Pmiss Fo
        (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
        (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W).
  Proof.
    iIntros "H". rewrite /sbundle. iDestruct "H" as (f) "H".
    iDestruct (sbundle_at_exec_elim X f W with "H") as "H".
    iExists (kf_xpay f), (xf_P f), (xf_Pmiss f), (xf_Fo f), (xf_Rs f).
    iExact "H".
  Qed.

  (* ================================================================== *)
  (* THE POST-SIDE INTRODUCTIONS, the mirror of the eight readers above:   *)
  (* the dispatcher's arm holds its contract's armed post and needs it at  *)
  (* the class field, at its own number and the key the process deposited  *)
  (* from.  Each is the match at one literal and nothing else.             *)
  (* ================================================================== *)
  Lemma spost_at_read_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (P : uptd)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
    ProcPtOwn.proc_pt_wf P ->
    (uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)) ->
    fileread_extra_core P (fd_st_of_key (tf_w (uvis_tf W) (tf_arg_idx 0)) (uvis_fd W))
      (sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2))) (rf_F f) (rf_ret f)
      r M' (tf_w (uvis_tf W) (tf_arg_idx 1)) -∗
    spost_at X 5 f W r M' fdv' cw' cs'.
  Proof.
    intros Hpm Hwf Hlz. iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_take. iExists P.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iExact "H".
  Qed.

  (* ...and chdir's, at the working directory the call RESUMES at: the arm
     the dispatcher splits ([SpecSysChdir.chdir_arms_split]) hands the
     kernel half back and this the process's. *)
  Lemma spost_at_chdir_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    chdir_receipt (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (cf_P f) (cf_Pmiss f) (cf_Fo f) r cw' -∗
    spost_at X 9 f W r M' fdv' cw' cs'.
  Proof.
    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_take. iExact "H".
  Qed.

  (* ...and open's, at the descriptor view it resumes at
     ([SpecSysOpen.open_arms_split]) *)
  Lemma spost_at_open_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    open_receipt (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1))
      (of_P f) (of_Pmiss f) (of_Farm f) (of_Fun f) (of_Fok f) (of_Fex f)
      (of_Fo f) (of_Ft f) (uvis_fd W) r fdv' -∗
    spost_at X 15 f W r M' fdv' cw' cs'.
  Proof.
    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_write_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    filewrite_extra (fd_st_of_key (tf_w (uvis_tf W) (tf_arg_idx 0)) (uvis_fd W))
      (sys_rw_count (tf_w (uvis_tf W) (tf_arg_idx 2))) (uvis_M W)
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (wf_Q f) (wf_tr0 f) r -∗
    spost_at X 16 f W r M' fdv' cw' cs'.
  Proof.
    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_mknod_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    mknod_arms (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (dev_arg (tf_w (uvis_tf W) (tf_arg_idx 1)))
      (dev_arg (tf_w (uvis_tf W) (tf_arg_idx 2)))
      (nf_P f) (nf_Pmiss f) (nf_Farm f) (nf_Fun f) (nf_Fok f) (nf_Fex f) r -∗
    spost_at X 17 f W r M' fdv' cw' cs'.
  Proof.
    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_unlink_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    unlink_arms (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (uf_P f) (uf_Pmiss f) (uf_Fent f) (uf_Ftgt f) (uf_Fex f) (uf_Fmiss f) r -∗
    spost_at X 18 f W r M' fdv' cw' cs'.
  Proof.
    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_link_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    link_arms (fs_gamma_L fsc_fs) (lf_Ftgt f) (lf_Fent f) (lf_Funt f) r -∗
    spost_at X 19 f W r M' fdv' cw' cs'.
  Proof.
    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip.
    xv6_take. iExact "H".
  Qed.

  Lemma spost_at_mkdir_intro (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    mkdir_arms (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      (df_P f) (df_Pmiss f) (df_Farm f) (df_Fdots f) (df_Fun f)
      (df_Fok f) (df_Fex f) r -∗
    spost_at X 20 f W r M' fdv' cw' cs'.
  Proof.
    iIntros "H". rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip.
    xv6_take. iExact "H".
  Qed.

  (* ...and the numbers that pay nothing, in one lemma: exec (whose [emp]
     the header explains) and every number without a contract at all. *)
  Lemma spost_at_emp (X : uvis -d> iPropO Σ) (n : Z) (f : xfam) (W : uvis)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate) (cw' : Z) (cs' : gset gname) :
    ~ (n = 5 \/ n = 9 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19
       \/ n = 20) ->
    ⊢ spost_at X n f W r M' fdv' cw' cs'.
  Proof.
    intros Hne. rewrite /spost_at /= /xv6_spost.
    destruct (decide (n = 5)) as [He | _]; [ exfalso; apply Hne; tauto |].
    destruct (decide (n = 9)) as [He | _]; [ exfalso; apply Hne; tauto |].
    destruct (decide (n = 15)) as [He | _]; [ exfalso; apply Hne; tauto |].
    destruct (decide (n = 16)) as [He | _]; [ exfalso; apply Hne; tauto |].
    destruct (decide (n = 17)) as [He | _]; [ exfalso; apply Hne; tauto |].
    destruct (decide (n = 18)) as [He | _]; [ exfalso; apply Hne; tauto |].
    destruct (decide (n = 19)) as [He | _]; [ exfalso; apply Hne; tauto |].
    destruct (decide (n = 20)) as [He | _]; [ exfalso; apply Hne; tauto |].
    done.
  Qed.

End UexecExecInst.
