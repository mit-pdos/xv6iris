(* USpecSh.v -- the VERIFIED-EXECUTION contracts of the `sh` program's 21
   reachable functions, on the input `echo Hello world!\n`
   (claude-notes/projects/user-sh.md, which carries the execution trace).

   THE TOP STATEMENT is [wp_sh_start_body]: from sh's entry state, with fd 0
   holding those bytes and then EOF, sh runs safely and the [exec] its child
   performs has a0 pointing at "echo" and a1 at ["echo","Hello","world!",0].
   The observation is made by the protocol, not by the WP: [UmodeIo]'s
   [IoExec] arm demands [uexec_args] -- the path and argv laid out BY
   CONTENT -- and hands the caller's [Q path args].  Instantiating [Q] with
   the equality is what turns "sh steps" into "sh execs echo".

   Everything is stated over [xv6_io_protocol] (UmodeIo.v), NOT over
   [xv6_sys_protocol]: the coarse protocol cannot mention the input and
   cannot observe exec's arguments.  Read UmodeIo.v's header for the four
   assumptions the rich protocol makes and why each is one conjunct in one
   arm rather than something hidden. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap UmodeAbi UmodeArith UmodeSyscall UmodeIo UCodeSh.
Require User.ShSyms User.ShInstrs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §0 The program's address space.                                        *)
(*                                                                        *)
(* sh does not fit echo's single-page picture: its text+rodata spans two   *)
(* pages, and -- unlike sync and echo -- it has a WRITABLE data page       *)
(* (`buf.0` @0x2020, `freep` @0x2010 and `base` @0x2088 all live in .bss,  *)
(* so the command buffer the parser chews on is NOT on the stack) and a    *)
(* HEAP that [sbrk] hands out.                                            *)
(* ===================================================================== *)

Definition SH_DATA_PG : Z := 0x2000.        (* .data + .bss, one page *)

Record sh_layout (pt : uptd) (hbase hlen : Z) : Prop := ShLayout {
  (* the text pages, fetch- and load-permitting (rodata shares them) *)
  shl_text : sh_text_layout pt;
  (* the data/bss page, load- AND store-permitting *)
  shl_data : exists w : mword 64,
      ud_um pt !! svpn_of (mword_of_int SH_DATA_PG : mword 64) = Some w /\
      uleaf_ok (Load Data) w /\ uleaf_ok (Store Data) w;
  (* the heap region [sbrk] carves from, mapped up front (UmodeIo.v's one
     modelling concession -- it is what keeps [pt] fixed) *)
  shl_hbase : Z.rem hbase 4096 = 0;
  shl_hlen  : Z.rem hlen 4096 = 0;
  shl_hroom : 65536 <= hlen;                (* the single malloc's sbrk *)
  shl_hhi   : hbase + hlen <= 2 ^ 38;
  shl_hlo   : SH_DATA_PG + 4096 <= hbase;
  shl_heap  : forall i : Z, 0 <= i < hlen / 4096 ->
      exists w : mword 64,
        ud_um pt !! svpn_of (mword_of_int (hbase + 4096 * i) : mword 64) = Some w /\
        uleaf_ok (Load Data) w /\ uleaf_ok (Store Data) w
}.

(* ===================================================================== *)
(* §0b THE INPUT AND THE ANSWER.                                           *)
(*                                                                        *)
(* `echo Hello world!\n' on fd 0, and the exec it must produce.  These are *)
(* the only place in the development where the scenario is spelled out;    *)
(* everything above is parametric in the input.                           *)
(* ===================================================================== *)

Definition sh_bytes (l : list Z) : list (bv 8) := (fun z => Z_to_bv 8 z) <$> l.

(* "echo Hello world!\n" *)
Definition sh_echo_input : list (bv 8) :=
  sh_bytes [101; 99; 104; 111; 32; 72; 101; 108; 108; 111; 32;
            119; 111; 114; 108; 100; 33; 10].

(* "echo" *)
Definition sh_echo_path : list (bv 8) := sh_bytes [101; 99; 104; 111].

(* ["echo"; "Hello"; "world!"] *)
Definition sh_echo_argv : list (list (bv 8)) :=
  [ sh_bytes [101; 99; 104; 111];
    sh_bytes [72; 101; 108; 108; 111];
    sh_bytes [119; 111; 114; 108; 100; 33] ].

(* THE observation: the protocol's [exec] arm hands this back, so a proof of
   [wp_sh_start_body] at this [Q] is a proof that the exec sh performs names
   `echo' with exactly these three arguments. *)
Definition sh_execs_echo `{!riscvGS Σ}
    (path : list (bv 8)) (args : list (list (bv 8))) : iProp Σ :=
  (⌜path = sh_echo_path /\ args = sh_echo_argv⌝)%I.

(* THE premise four contracts were missing.  [uv_stack] only guarantees
   [4096 <= uint sp0 - n], but sh's text keys run to 8192 and its heap sits
   above the data page, so a prologue spill could land on the image and no
   [ui_sh_*] fact would survive it.  Stated once, threaded everywhere. *)
Definition sh_frame_ok (hbase hlen : Z) (sp0 : mword 64) (n : Z) : Prop :=
  hbase + hlen <= uint sp0 - n.

(* A disturbed window, as [uM_only_in] takes them.  Named because a bare
   pair inside [⌜ ⌝] parses in the bi scope as a product TYPE, and the error
   ("has type Z while it is expected to have type Type") names neither the
   scope nor the pair. *)
Definition sh_win (a n : Z) : Z * Z := (a, n).

(* [sh_win] is a definition, not a notation, so a window's components hide
   behind it: [simpl] leaves [fst (sh_win a n)] and the following [lia] fails
   with "Cannot find witness", naming neither.  Unfold it with
   [cbv [sh_win]] before destructuring a window, or use this. *)
Lemma sh_win_fst (a n : Z) : fst (sh_win a n) = a.   Proof. reflexivity. Qed.
Lemma sh_win_snd (a n : Z) : snd (sh_win a n) = n.   Proof. reflexivity. Qed.

Section USpecSh.
  Context `{!riscvGS Σ} `{!uioG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).
  Context (gin gbrk : gname) (hbase hlen : Z).
  Context (Q : list (bv 8) -> list (list (bv 8)) -> iProp Σ).

  Local Notation Psh := (xv6_io_protocol C pt gin gbrk hbase hlen Q).
  Local Notation UVG m M := (uv_cap_gpr C pt Psh M m).

  Definition sh_zeroed (M : gmap Z (bv 8)) (a lo hi : Z) : Prop :=
    forall j : Z, lo <= j < hi -> M !! (a + j) = Some ubyte0.

  (* [n] copies of one byte at [a] -- memset's result.  Named, because an
     inline [forall] inside [⌜ ⌝] parses in the bi scope and fails with an
     unrelated "expected to have type Type". *)
  Definition sh_filled (M : gmap Z (bv 8)) (a n : Z) (c : bv 8) : Prop :=
    forall j : Z, 0 <= j < n -> M !! (a + j) = Some c.

  (* ------------------------------------------------------------------- *)
  (* §1 THE SYSCALL STUBS.                                                 *)
  (*                                                                       *)
  (* Each is `li a7,N; ecall; ret' and each contract is its protocol arm    *)
  (* (UmodeIo.v) read at the call site: the arm's obligation becomes the    *)
  (* stub's PRECONDITION and the arm's continuation becomes the stub's      *)
  (* postcondition, with a7 := N and a0 := the return value in the file the *)
  (* caller gets back.  Nothing here is sh-specific except the addresses.   *)
  (* ------------------------------------------------------------------- *)

  (* the register file every returning stub hands back *)
  Local Notation StubFile n ret m :=
    (<[Regidx a0_idx := ret]>
       (<[Regidx a7_idx := (mword_of_int n : mword 64)]> m)).

  (* the premises every stub shares *)
  Local Notation StubPre M m :=
    (sh_layout pt hbase hlen /\ sh_text_sub M /\
     is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true).

  (* --- the plain returning stubs: close, dup, chdir, wait ------------- *)
  Definition wp_sh_pureret_body (entry n : Z)
      (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hpre : StubPre M m)
      (Hsem : xv6_io_sem n = IoPureRet),
    UVG m M -∗
    pc_is (mword_of_int entry) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (StubFile n ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- exit: does not return ----------------------------------------- *)
  Definition wp_sh_exit_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hlay : sh_layout pt hbase hlen) (Htext : sh_text_sub M),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.exit) -∗
    WP (Loop : expr riscv_lang).

  (* --- write(fd, buf, n): the buffer must be readable ------------------ *)
  Definition wp_sh_write_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hpre : StubPre M m)
      (Hbuf : uv_rd pt M (uint (m !!! Regidx a1_idx))
                         (uint (m !!! Regidx a2_idx))),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.write) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       UVG (StubFile SYS_write ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- open(path, flags): reads the path, returns a fd >= 3 ----------- *)
  Definition wp_sh_open_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hpre : StubPre M m)
      (Hpath : uio_str_arg pt M (uint (m !!! Regidx a0_idx))),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.open) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       ⌜3 <= sint ret⌝ -∗
       UVG (StubFile SYS_open ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- fork(): 0 in the child, a positive pid in the parent ----------- *)
  Definition wp_sh_fork_body (M : gmap Z (bv 8)) (m : regfile) :=
    forall (Hpre : StubPre M m),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.fork) -∗
    (∀ CID : CpuId, ∀ ret : mword 64,
       ⌜uint ret = 0 \/ 0 < sint ret⌝ -∗
       UVG (StubFile SYS_fork ret m) M -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- exec(path, argv): THE observable one.  No continuation.  What the
     caller must produce is [Q path args] for the path and argv actually in
     memory, which is where sh's theorem gets its content. ---------------- *)
  Definition wp_sh_exec_body (M : gmap Z (bv 8)) (m : regfile)
      (path : list (bv 8)) (args : list (list (bv 8))) :=
    forall (Hlay : sh_layout pt hbase hlen) (Htext : sh_text_sub M)
      (Hargs : uexec_args M (uint (m !!! Regidx a0_idx))
                            (uint (m !!! Regidx a1_idx)) path args),
    UVG m M -∗
    Q path args -∗
    pc_is (mword_of_int ShSyms.exec) -∗
    WP (Loop : expr riscv_lang).

  (* --- read(fd, buf, n): consumes the stdin stream -------------------- *)
  Definition wp_sh_read_body (M : gmap Z (bv 8)) (m : regfile)
      (str : list (bv 8)) :=
    forall (Hpre : StubPre M m)
      (Hbuf : uv_wr pt M (uint (m !!! Regidx a1_idx))
                         (uint (m !!! Regidx a2_idx)))
      (* the buffer must miss the text, else the [ret] the stub returns to
         has no [uinstr] fact in the image [read] hands back *)
      (Hbufhi : 8192 <= uint (m !!! Regidx a1_idx)),
    UVG m M -∗
    ustdin gin str -∗
    pc_is (mword_of_int ShSyms.read) -∗
    (∀ CID : CpuId, ∀ (k : nat) (M' : gmap Z (bv 8)),
       ⌜(k <= length str)%nat⌝ -∗
       ⌜Z.of_nat k <= uint (m !!! Regidx a2_idx)⌝ -∗
       ⌜(k = 0)%nat -> str = []⌝ -∗
       ⌜uM_written M M' (uint (m !!! Regidx a1_idx)) (take k str)⌝ -∗
       ustdin gin (drop k str) -∗
       UVG (StubFile SYS_read (mword_of_int (Z.of_nat k) : mword 64) m) M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- sys_sbrk(n, eager): hands over [n] fresh bytes at the break ----- *)
  Definition wp_sh_sys_sbrk_body (M : gmap Z (bv 8)) (m : regfile) (b : Z) :=
    forall (Hpre : StubPre M m)
      (Hrange : hbase <= b /\ 0 <= sint (m !!! Regidx a0_idx) /\
                b + sint (m !!! Regidx a0_idx) <= hbase + hlen),
    UVG m M -∗
    ubrk gbrk b -∗
    pc_is (mword_of_int ShSyms.sys_sbrk) -∗
    (∀ CID : CpuId, ∀ M' : gmap Z (bv 8),
       ⌜uM_grown M M' b (sint (m !!! Regidx a0_idx))⌝ -∗
       ubrk gbrk (b + sint (m !!! Regidx a0_idx)) -∗
       UVG (StubFile SYS_sbrk (mword_of_int b : mword 64) m) M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* --- sbrk(n): the ulib wrapper -- `li a1,1; jal sys_sbrk' ----------- *)
  Definition wp_sh_sbrk_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (b : Z) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 16)
      (Hrange : hbase <= b /\ 0 <= sint (m !!! Regidx a0_idx) /\
                b + sint (m !!! Regidx a0_idx) <= hbase + hlen)
      (Hfr : sh_frame_ok hbase hlen sp0 16)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    ubrk gbrk b -∗
    pc_is (mword_of_int ShSyms.sbrk) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' M'' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       (* what sbrk RETURNS -- the old break.  [morecore] needs exactly this. *)
       ⌜m' !!! Regidx a0_idx = (mword_of_int b : mword 64)⌝ -∗
       (* the code carves its frame FIRST and calls sbrk second; stating it
          the other way round forces the caller to build the intermediate
          image by hand for no gain *)
       ⌜uM_only M M' (uint sp0 - 16) 16⌝ -∗
       ⌜uM_grown M' M'' b (sint (m !!! Regidx a0_idx))⌝ -∗
       ubrk gbrk (b + sint (m !!! Regidx a0_idx)) -∗
       UVG m' M'' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §1 The library leaves.                                               *)
  (*                                                                      *)
  (* All three are the same gcc shape sync and echo already established:   *)
  (* a 16-byte frame, a byte loop, a frame restore.  sh's [strlen] is      *)
  (* INSTRUCTION-FOR-INSTRUCTION echo's, at a different address.           *)
  (* ------------------------------------------------------------------- *)

  (* strlen(s) -- returns the index of the NUL. *)
  Definition wp_sh_strlen_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s len : Z) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 16)
      (Hs : m !!! Regidx a0_idx = (mword_of_int s : mword 64))
      (Hstr : ucstr M s len)
      (Hrd : uv_rd pt M s (len + 1))
      (Hlen : 0 <= len < 2 ^ 31)
      (Habove : uint sp0 <= s \/ s + len + 1 <= uint sp0 - 16)
      (Hfr : sh_frame_ok hbase hlen sp0 16)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.strlen) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int len : mword 64)⌝ -∗
       ⌜uM_only M M' (uint sp0 - 16) 16⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* strchr(s, c) -- the first occurrence of the byte [c], or NULL.
     [ustr_find] is the pure model; [c] is a BYTE value (every call site
     passes a zero-extended [lbu] result), so the comparison the code makes
     against the zero-extended loaded byte is exact. *)
  Definition ustr_find (bs : list (bv 8)) (c : bv 8) : option nat :=
    fst <$> (list_find (fun b => b = c) bs).

  Definition wp_sh_strchr_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (s : Z) (bs : list (bv 8)) (c : bv 8) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 16)
      (Hs : m !!! Regidx a0_idx = (mword_of_int s : mword 64))
      (Hc : m !!! Regidx a1_idx = (mword_of_int (bv_unsigned c) : mword 64))
      (Hnz : forall (j : nat) (b : bv 8), bs !! j = Some b -> b <> ubyte0)
      (Hstr : ustr_at M s bs)
      (Hrd : uv_rd pt M s (Z.of_nat (length bs) + 1))
      (Habove : uint sp0 <= s \/ s + Z.of_nat (length bs) + 1 <= uint sp0 - 16)
      (Hfr : sh_frame_ok hbase hlen sp0 16)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.strchr) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (match ustr_find bs c with
                           | Some i => s + Z.of_nat i
                           | None => 0
                           end) : mword 64)⌝ -∗
       ⌜uM_only M M' (uint sp0 - 16) 16⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* memset(dst, c, n) -- writes [n] copies of the low byte of [c] and
     returns [dst].  The image effect is [uM_written] (UmodeIo.v), the same
     shape a buffer-writing syscall has. *)
  Definition wp_sh_memset_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (dst n : Z) (c : bv 8) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 16)
      (Hdst : m !!! Regidx a0_idx = (mword_of_int dst : mword 64))
      (Hc : m !!! Regidx a1_idx = (mword_of_int (bv_unsigned c) : mword 64))
      (Hn : m !!! Regidx a2_idx = (mword_of_int n : mword 64))
      (Hnr : 0 <= n < 2 ^ 31)
      (Hwr : uv_wr pt M dst n)
      (Hfr : sh_frame_ok hbase hlen sp0 16)
      (* the destination must miss the program image: [uleaf_ok] is
         "permitted", so a store-permitting leaf and a fetch-permitting one
         are jointly satisfiable and nothing else excludes dst = 0 *)
      (Hdsthi : 8192 <= dst)
      (Habove : uint sp0 <= dst \/ dst + n <= uint sp0 - 16)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.memset) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int dst : mword 64)⌝ -∗
       (* the destination now reads [c] ... *)
       ⌜sh_filled M' dst n c⌝ -∗
       (* ... and NOTHING outside the destination and memset's own frame
          moved.  Stating only the destination would be wrong, not weak:
          the prologue spills ra and s0 into the frame and never restores
          those bytes. *)
       ⌜uM_only_in M M' [sh_win (dst) (n); sh_win (uint sp0 - 16) (16)]⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §3 THE HEAP: free, morecore-via-malloc, execcmd.                      *)
  (*                                                                       *)
  (* sh calls [malloc] EXACTLY ONCE on this input, from [execcmd], and its  *)
  (* outcome is therefore fully determined -- which is why these contracts  *)
  (* are concrete rather than a free-list invariant.  With `freep == 0'     *)
  (* (the .bss is zeroed by exec):                                         *)
  (*                                                                       *)
  (*   nunits   = (nbytes + 15)/16 + 1                                     *)
  (*   base self-links with size 0; the scan fails; p == freep             *)
  (*   morecore(nunits) clamps nu to 4096 and calls sbrk(65536)            *)
  (*   free() links that block after base                                  *)
  (*   the rescan splits it and returns hbase + 65536 - 16*(nunits-1)      *)
  (*                                                                       *)
  (* A general free-list invariant would be a project of its own and would  *)
  (* buy nothing here; that this contract is FIRST-CALL-ONLY is stated in   *)
  (* its name.                                                             *)
  (* ------------------------------------------------------------------- *)

  (* the two .bss cells the allocator owns *)
  Definition SH_FREEP : Z := SH_DATA_PG + 0x10.     (* Header *freep  *)
  Definition SH_BASE  : Z := SH_DATA_PG + 0x88.     (* Header  base   *)

  Definition sh_nunits (nbytes : Z) : Z := (nbytes + 15) / 16 + 1.

  (* free(ap) at the ONE call morecore makes: freep = &base, base is
     self-linked with size 0, and [bp = ap-16] is the fresh sbrk'd block
     with [bp->s.size] units, sitting ABOVE base. *)
  Definition wp_sh_free_first_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (bp nu : Z) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 16)
      (Hap : m !!! Regidx a0_idx = (mword_of_int (bp + 16) : mword 64))
      (Hbp : bp = hbase)
      (* [free] reads bp->s.size with a SIGNED 4-byte [lw] *)
      (Hnu : 0 < nu < 2 ^ 31 /\ bp + 16 * nu <= hbase + hlen)
      (* freep = &base, base.s.ptr = &base, base.s.size = 0 *)
      (Hfreep : uM_bytes M SH_FREEP 8 (mword_of_int SH_BASE : mword 64))
      (Hbaseptr : uM_bytes M SH_BASE 8 (mword_of_int SH_BASE : mword 64))
      (Hbasesz : uM_bytes M (SH_BASE + 8) 8 (mword_of_int 0 : mword 64))
      (* bp->s.size = nu, at FOUR bytes: [Header.s.size] is a C [uint],
         written by [sw] and read by [sw]'s matching [lw].  The other four
         bytes of the union slot are padding that no instruction writes and
         [uM_grown] does not constrain, so an 8-byte claim here is
         unprovable at the one call site. *)
      (Hbpsz : uM_bytes M (bp + 8) 4 (mword_of_int nu : mword 32))
      (Hheapw : uv_wr pt M bp (16 * nu))
      (Hbssw : uv_wr pt M SH_FREEP 0x88)
      (Hfr : sh_frame_ok hbase hlen sp0 16)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.free) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       (* base.s.ptr = bp, bp->s.ptr = &base, freep = &base *)
       ⌜uM_bytes M' SH_BASE 8 (mword_of_int bp : mword 64)⌝ -∗
       ⌜uM_bytes M' bp 8 (mword_of_int SH_BASE : mword 64)⌝ -∗
       ⌜uM_bytes M' (bp + 8) 4 (mword_of_int nu : mword 32)⌝ -∗
       ⌜uM_bytes M' SH_FREEP 8 (mword_of_int SH_BASE : mword 64)⌝ -∗
       ⌜uM_only_in M M' [sh_win (uint sp0 - 16) (16); sh_win (SH_FREEP) (8); sh_win (SH_BASE) (16); sh_win (bp) (16)]⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* malloc(nbytes), FIRST CALL ONLY: freep is still 0. *)
  Definition wp_sh_malloc_first_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (nbytes : Z) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (64 + 16 + 16))    (* own + free + sbrk *)
      (Hn : m !!! Regidx a0_idx = (mword_of_int nbytes : mword 64))
      (Hnr : 0 < nbytes /\ 16 * sh_nunits nbytes <= 65536)
      (* the whole .bss is zeroed by [exec] -- this subsumes freep = 0 and
         is what makes [base.s.size]'s upper four bytes zero, which no
         instruction writes *)
      (Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88)
      (Hbssw : uv_wr pt M SH_FREEP 0x88)
      (Hfr : sh_frame_ok hbase hlen sp0 96)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    ubrk gbrk hbase -∗
    pc_is (mword_of_int ShSyms.malloc) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (hbase + 65536 - 16 * (sh_nunits nbytes - 1))
             : mword 64)⌝ -∗
       (* the returned block is writable and disjoint from image and stack *)
       ⌜uv_wr pt M' (hbase + 65536 - 16 * (sh_nunits nbytes - 1))
                    (16 * (sh_nunits nbytes - 1))⌝ -∗
       ⌜uM_only_in M M' [sh_win (hbase) (65536); sh_win (SH_FREEP) (8); sh_win (SH_BASE) (16);
                         sh_win (uint sp0 - 96) (96)]⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* execcmd(): malloc(168), memset it, set type = EXEC (1). *)
  Definition SH_EXECCMD_SZ : Z := 168.

  (* a zero-filled byte range, as a named Prop: an inline [forall] inside
     [⌜ ⌝] parses in the bi scope and fails with an unrelated "expected to
     have type Type" *)

  Definition wp_sh_execcmd_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (32 + 64 + 16 + 16))
      (Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88)
      (Hbssw : uv_wr pt M SH_FREEP 0x88)
      (Hfr : sh_frame_ok hbase hlen sp0 128)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    ubrk gbrk hbase -∗
    pc_is (mword_of_int ShSyms.execcmd) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)) (cmd : Z),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int cmd : mword 64)⌝ -∗
       ⌜cmd = hbase + 65536 - 16 * (sh_nunits SH_EXECCMD_SZ - 1)⌝ -∗
       (* zeroed, except type = EXEC in the first word *)
       ⌜uM_bytes M' cmd 4 (mword_of_int 1 : mword 32)⌝ -∗
       ⌜sh_zeroed M' cmd 4 SH_EXECCMD_SZ⌝ -∗
       ⌜uv_wr pt M' cmd SH_EXECCMD_SZ⌝ -∗
       (* WITHOUT this [parseexec] cannot re-establish anything at all about
          the image it handed in *)
       ⌜uM_only_in M M' [sh_win hbase 65536; sh_win SH_FREEP 8;
                         sh_win SH_BASE 16; sh_win cmd SH_EXECCMD_SZ;
                         sh_win (uint sp0 - 128) 128]⌝ -∗
       ubrk gbrk (hbase + 65536) -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* fork1(): fork(), panic on -1 (excluded by the protocol's arm). *)
  Definition wp_sh_fork1_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 16)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    pc_is (mword_of_int ShSyms.fork1) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)) (ret : mword 64),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = ret⌝ -∗
       ⌜uint ret = 0 \/ 0 < sint ret⌝ -∗
       ⌜uM_only M M' (uint sp0 - 16) 16⌝ -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §4 THE INPUT PATH: gets, getcmd.                                      *)
  (*                                                                       *)
  (* [gets] leaves the loop three ways -- newline/CR, EOF, or the buffer    *)
  (* filling -- and only the first two are reachable here.  One contract    *)
  (* covers both, parameterised by the prefix [taken] it consumes: either a *)
  (* line ending in '\n' (with no earlier '\n' or '\r'), or nothing at EOF. *)
  (* ------------------------------------------------------------------- *)

  Definition SH_BUF : Z := SH_DATA_PG + 0x20.        (* static char buf[100] *)
  Definition ubyte_nl : bv 8 := Z_to_bv 8 10.
  Definition ubyte_cr : bv 8 := Z_to_bv 8 13.

  Definition sh_gets_taken (taken rest : list (bv 8)) : Prop :=
    (exists line : list (bv 8),
       taken = line ++ [ubyte_nl] /\
       forall (j : nat) (b : bv 8), line !! j = Some b ->
         b <> ubyte_nl /\ b <> ubyte_cr)
    \/ (taken = [] /\ rest = []).

  Definition wp_sh_gets_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (buf max : Z) (taken rest : list (bv 8)) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Htext : sh_text_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 96)
      (Hbuf : m !!! Regidx a0_idx = (mword_of_int buf : mword 64))
      (Hmax : m !!! Regidx a1_idx = (mword_of_int max : mword 64))
      (Htk : sh_gets_taken taken rest)
      (Hfit : Z.of_nat (length taken) + 1 < max /\ max < 2 ^ 31)
      (Hwr : uv_wr pt M buf max)
      (* the frame must miss image and heap: gets' one-byte read slot is at
         sp0-81, and [wp_sh_read_body]'s [Hbufhi] wants it above the text *)
      (Hfr : sh_frame_ok hbase hlen sp0 96)
      (* and the caller's buffer must miss the text, or the loop's own
         [ui_sh_*] facts do not survive its first [sb] *)
      (Hbufhi : 8192 <= buf)
      (Hdisj : buf + max <= uint sp0 - 96 \/ uint sp0 <= buf)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    ustdin gin (taken ++ rest) -∗
    pc_is (mword_of_int ShSyms.gets) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       ⌜m' !!! Regidx a0_idx = (mword_of_int buf : mword 64)⌝ -∗
       (* the line, NUL-terminated ... *)
       ⌜ustr_at M' buf taken⌝ -∗
       (* ... and nothing outside the buffer and gets' own 96-byte frame.
          A bare [uM_written] here is FALSE, not weak: the prologue spills
          ra and s0..s8 and [read] writes the byte slot at sp0-81. *)
       ⌜uM_only_in M M' [sh_win buf (Z.of_nat (length taken) + 1);
                         sh_win (uint sp0 - 96) 96]⌝ -∗
       ustdin gin rest -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* getcmd(buf, nbuf): prompt, zero the buffer, gets, and report EOF. *)
  Definition wp_sh_getcmd_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (buf nbuf : Z) (taken rest : list (bv 8)) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Himg : sh_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 (32 + 96))
      (Hbuf : m !!! Regidx a0_idx = (mword_of_int buf : mword 64))
      (Hnbuf : m !!! Regidx a1_idx = (mword_of_int nbuf : mword 64))
      (Htk : sh_gets_taken taken rest)
      (Hfit : Z.of_nat (length taken) + 1 < nbuf /\ nbuf < 2 ^ 31)
      (Hwr : uv_wr pt M buf nbuf)
      (* getcmd does not only WRITE the buffer: [lbu a0,0(s1)] reads buf[0]
         for the EOF test, and a store leaf does not give a load leaf *)
      (Hrd : uv_rd pt M buf nbuf)
      (Hfr : sh_frame_ok hbase hlen sp0 128)
      (Hbufhi : 8192 <= buf)
      (* getcmd returns -1 exactly when buf[0] = 0, and [sh_gets_taken] does
         NOT exclude a NUL inside the line -- on input "\000abc\n" the
         return value would be -1 with [taken] non-empty *)
      (Hnul : forall b : bv 8, taken !! 0%nat = Some b -> b <> ubyte0)
      (Hdisj : buf + nbuf <= uint sp0 - 128 \/ uint sp0 <= buf)
      (Hret2 : is_aligned_vaddr (Virtaddr (m !!! Regidx ra_idx)) 2 = true),
    UVG m M -∗
    ustdin gin (taken ++ rest) -∗
    pc_is (mword_of_int ShSyms.getcmd) -∗
    (∀ CID : CpuId, ∀ (m' : regfile) (M' : gmap Z (bv 8)),
       ⌜ucallee_saved m m'⌝ -∗
       (* 0 when a line was read, -1 at EOF *)
       ⌜m' !!! Regidx a0_idx
          = (mword_of_int (if bool_decide (taken = []) then (-1) else 0)
             : mword 64)⌝ -∗
       ⌜ustr_at M' buf taken⌝ -∗
       ⌜sh_zeroed M' buf (Z.of_nat (length taken) + 1) nbuf⌝ -∗
       ⌜uM_only_in M M' [sh_win (buf) (nbuf); sh_win (uint sp0 - 128) (128)]⌝ -∗
       ustdin gin rest -∗
       UVG m' M' -∗
       pc_is (m !!! Regidx ra_idx) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §5 THE LEXER'S STATIC TABLES, as pure models.                        *)
  (*                                                                      *)
  (* [peek] and [gettoken] consult two `static char[]' arrays in .data on  *)
  (* every token, through [strchr].  They are the reason [sh_layout] needs *)
  (* the data page at all -- no text-page lemma reaches them.             *)
  (* ------------------------------------------------------------------- *)

  Definition SH_SYMBOLS    : Z := SH_DATA_PG + 0.   (* "<|>&;()"   *)
  Definition SH_WHITESPACE : Z := SH_DATA_PG + 8.   (* " \t\r\n\v" *)

  Definition sh_ws_bytes  : list (bv 8) := sh_bytes [32; 9; 13; 10; 11].
  Definition sh_sym_bytes : list (bv 8) := sh_bytes [60; 124; 62; 38; 59; 40; 41].

  Definition sh_is_ws  (b : bv 8) : bool := bool_decide (b ∈ sh_ws_bytes).
  Definition sh_is_sym (b : bv 8) : bool := bool_decide (b ∈ sh_sym_bytes).

  (* how far [peek]/[gettoken]'s leading `while (s < es && strchr(whitespace,
     *s)) s++' advances *)
  Definition sh_skipws (bs : list (bv 8)) : nat :=
    match list_find (fun b => sh_is_ws b = false) bs with
    | Some (i, _) => i
    | None => length bs
    end.

  (* ... and how far [gettoken]'s default arm then runs *)
  Definition sh_toklen (bs : list (bv 8)) : nat :=
    match list_find (fun b => sh_is_ws b || sh_is_sym b) bs with
    | Some (i, _) => i
    | None => length bs
    end.

  (* the two static arrays are present in the image, as [sh_img_sub] gives
     them -- named here so the lexer contracts have one premise, not two *)
  Definition sh_tables_ok (M : gmap Z (bv 8)) : Prop :=
    ustr_at M SH_WHITESPACE sh_ws_bytes /\ ustr_at M SH_SYMBOLS sh_sym_bytes.

  (* ------------------------------------------------------------------- *)
  (* §6 runcmd and main.                                                  *)
  (*                                                                      *)
  (* Both DIVERGE, so neither has a continuation.  [runcmd] is stated for  *)
  (* the EXEC case only -- the one the input reaches; the other four       *)
  (* command types are unreachable here and their constructors             *)
  (* (redircmd/pipecmd/listcmd/backcmd) are not even in the catalog.       *)
  (* ------------------------------------------------------------------- *)

  Definition wp_sh_runcmd_exec_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (cmd p0 : Z)
      (path : list (bv 8)) (args : list (list (bv 8))) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Himg : sh_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 48)
      (Hcmd : m !!! Regidx a0_idx = (mword_of_int cmd : mword 64))
      (Hnn : cmd <> 0)
      (* cmd->type == EXEC, and argv[0] != 0 *)
      (Htype : uM_bytes M cmd 4 (mword_of_int 1 : mword 32))
      (Hp0 : uM_bytes M (cmd + 8) 8 (mword_of_int p0 : mword 64))
      (Hp0nz : p0 <> 0)
      (* what the exec will be observed to name *)
      (Hexec : uexec_args M p0 (cmd + 8) path args)
      (Hrd : uv_rd pt M cmd SH_EXECCMD_SZ),
    UVG m M -∗
    Q path args -∗
    pc_is (mword_of_int ShSyms.runcmd) -∗
    WP (Loop : expr riscv_lang).

  (* main(): prime the fds, then the REPL.  DIVERGES via exit(0). *)
  Definition wp_sh_main_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (input : list (bv 8)) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Himg : sh_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 512)
      (Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88)
      (Hbssw : uv_wr pt M (SH_DATA_PG + 0x10) 0x88)
      (Htab : sh_tables_ok M)
      (Hstkhi : hbase + hlen <= uint sp0 - 512)
      (Hstk : uint sp0 <= 2 ^ 38),
    UVG m M -∗
    ustdin gin input -∗
    ubrk gbrk hbase -∗
    Q sh_echo_path sh_echo_argv -∗
    pc_is (mword_of_int ShSyms.main) -∗
    WP (Loop : expr riscv_lang).

  (* ------------------------------------------------------------------- *)
  (* §N THE TOP STATEMENT.                                                *)
  (*                                                                      *)
  (* The stack budget is the deepest call chain:                          *)
  (*   start 16 + main 64 + parsecmd 64 + parseline 48 + parsepipe 48     *)
  (*   + parseexec 128 + parseredirs 112 + peek 64 + strchr 16 = 560,     *)
  (* rounded to 576.  (The IO chain start/main/getcmd/gets is only 208.)  *)
  (*                                                                      *)
  (* [Hbss] is not decoration: `freep' lives in .bss and [exec] zeroes it, *)
  (* and `freep == 0' is exactly what sends the single [malloc] down the   *)
  (* [morecore] path this proof follows.                                  *)
  (* ------------------------------------------------------------------- *)

  Definition wp_sh_start_body (M : gmap Z (bv 8)) (m : regfile)
      (sp0 : mword 64) (input : list (bv 8)) :=
    forall (Hlay : sh_layout pt hbase hlen)
      (Himg : sh_img_sub M)
      (Hsp : m !!! Regidx sp_idx = sp0)
      (Hst : uv_stack pt M sp0 576)
      (* .bss is mapped, present and ZEROED -- what [exec] leaves behind *)
      (Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88)
      (Hbssw : uv_wr pt M (SH_DATA_PG + 0x10) 0x88)
      (* the heap has not been handed out yet *)
      (Hstk : uint sp0 <= 2 ^ 38)
      (Hstkhi : hbase + hlen <= uint sp0 - 576),
    UVG m M -∗
    ustdin gin input -∗
    ubrk gbrk hbase -∗
    (* the right to conclude [Q] for THESE arguments, consumed exactly once
       -- at the [exec].  A run that exec'd anything else could not spend it,
       which is what gives the theorem its content. *)
    Q sh_echo_path sh_echo_argv -∗
    pc_is (mword_of_int ShSyms.start) -∗
    WP (Loop : expr riscv_lang).

End USpecSh.
