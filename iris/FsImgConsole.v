(* ===================================================================== *)
(* FsImgConsole.v -- "console" IS NOT IN THE TRACKED IMAGE'S ROOT.         *)
(*                                                                         *)
(* The one image fact the era-0 pilot (FdRowPilot.v) needs and the two     *)
(* names it is stated over.  An image-check LEAF in FsImgCheck.v's sense    *)
(* (read that file's header): one [vm_compute] over the tracked disk, and   *)
(* NO PROOF FILE IMPORTS IT -- FdRowPilot re-exports it to its own two      *)
(* consumers.  It is its own file, not a lemma in FdRowPilot, because the    *)
(* MISS is the expensive case of [FsImgCheck.fsimg_path_root]'s scan: the   *)
(* [dir_first] walk reads all 64 root records and its [Qed] re-runs the     *)
(* computation in the kernel, ~25 s -- and FdRowPilot sits on the build's   *)
(* serial tail (after the system theorem), where every second is wall.      *)
(* Here it compiles beside FsImgCheck, hundreds of seconds earlier.         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp.bitvector Require Import definitions.
From xv6iris Require Import FsImgDisk FsImg FsTree FsImgCheck.
Local Open Scope Z_scope.

(* [FsImgCheck]'s own [Ltac], which is [Local] there *)
Local Ltac vm_eq :=
  lazymatch goal with
  | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
  end.

Definition fname_console : fname :=
  [fsimg_byte 0x63; fsimg_byte 0x6f; fsimg_byte 0x6e; fsimg_byte 0x73;
   fsimg_byte 0x6f; fsimg_byte 0x6c; fsimg_byte 0x65].

(* the string as fetched: same bytes, no terminator (the terminator is
   [ustrq]'s business) *)
Definition console_str : list (bv 8) := fname_console.

(* the ONE computing sentence of this file, [fsimg_init_path]'s mold *)
Lemma fsimg_console_miss :
  path_at (tree_of_disk fsimg_P fsimg_sb) FsImg.ROOTINO [fname_console]
  = None.
Proof. rewrite fsimg_path_root. vm_eq. Qed.
