(* ===================================================================== *)
(* UkRun.v -- THE RUNNING PREDICATE, and the leaf interface above it.     *)
(*                                                                        *)
(* [UserHeap.uheap] is the memory half: two ghost_map authorities against  *)
(* the image, the segment facts, the break and the slack.  THIS file      *)
(* packages that together with the machine bundle into the one thing a    *)
(* user-program proof ever holds:                                          *)
(*                                                                        *)
(*   urun γt γd γs m pc                                                    *)
(*                                                                        *)
(* -- "the process is running, with general registers [m] at pc [pc]".     *)
(* Everything else is INSIDE, existentially: the hart, the loop-constant   *)
(* config, the page table, the residue the trap loop threads, [p->sz], the *)
(* memory image and the permission map.  None of them matter to a user     *)
(* program, and none of them appear in a leaf statement.                   *)
(*                                                                        *)
(* WHY THE EXISTENTIAL AMBIENT IS THE WHOLE TRICK.  Today every leaf       *)
(* consumes a bundle at ONE ambient but demands a continuation good at     *)
(* EVERY ambient ([UexecRet.ukc]'s ∀), because an interrupt may hand the   *)
(* process back on a different hart under a different table.  The program  *)
(* pays for that mismatch by re-introducing five binders after every       *)
(* instruction -- [rewrite /ukc. iIntros (h C pt Rut sz) "%Hlo %Hpm Hb"],  *)
(* seventy-six times in UkEcho.v alone.  Packing the ambient inside [urun] *)
(* makes the caller's continuation [urun ... m' pc' -* WP] good at any       *)
(* ambient BY CONSTRUCTION, so the leaf absorbs the quantifier and the     *)
(* program never sees it.  [ukc] then has nothing left to name.            *)
(*                                                                        *)
(* THE SPLIT BETWEEN REGISTERS AND MEMORY IS DELIBERATE.  Registers are a  *)
(* whole file inside [urun]: there is no framing to be had -- the slot's   *)
(* key is the trapframe, so every instruction's obligation mentions all of *)
(* them anyway.  Memory is the opposite: fragments live OUTSIDE [urun] and *)
(* a leaf names exactly the bytes it touches, so everything else frames.   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RegFile InstrBytes.
Require Import UserPtTree UserExec ProcPtOwn.
Require Import UmodeMem UmodeArith UmodeText.
Require Import UserPerm UexecWp UexecSlot UexecRet.
Require Import FdSlots.      (* [fdstate] -- the key's descriptor view *)
Require Import WpMmodeLeafBase.
Require Import UptTree.
Require Import WpUmodeStore.
Require Import WpUmodeStep.
Require Import UsysMemOk. (* [USYS_exec] -- the number the minting law excludes *)
Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the deposit class and
                             the program's supplier + admitted numbers *)
Require Import UkStep.
Require Import RiscvExtras.
Require Import UserHeap.
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.


(* ===================================================================== *)
(* WpUmodeStore's store-run and UserPtTree's are the same map.  The two   *)
(* build it from opposite ends -- [uM_store] folds index 0 outermost,     *)
(* [umem_write] recurses with index n-1 outermost -- so they are equal    *)
(* but not convertible.  The heap speaks [umem_write]; the store leaves   *)
(* speak [uM_store8]; this is the one lemma that lets a leaf wrapper hand *)
(* one to the other.                                                     *)
(* ===================================================================== *)
Lemma uM_store_umem_write (M : gmap Z (bv 8)) (a : Z) (n : nat) (v : mword 64) :
  uM_store M a (Z.of_nat n) v = umem_write M a n (nth_byte v).
Proof.
  apply map_eq. intro k.
  destruct (decide (a <= k < a + Z.of_nat n)) as [Hin | Hout].
  - assert (Hj : (Z.to_nat (k - a) < n)%nat) by lia.
    replace k with (a + Z.of_nat (Z.to_nat (k - a))) by lia.
    rewrite (uM_store_lookup M a (Z.of_nat n) v _
               ltac:(rewrite Nat2Z.id; exact Hj)).
    rewrite (umem_write_lookup_in M a n (nth_byte v) _ Hj). reflexivity.
  - rewrite (uM_store_lookup_ne M a (Z.of_nat n) v k
               ltac:(intros j Hj; rewrite Nat2Z.id in Hj; lia)).
    rewrite (umem_write_lookup_out M a n (nth_byte v) k
               ltac:(intros j Hj; lia)).
    reflexivity.
Qed.

Lemma uM_store8_umem_write (M : gmap Z (bv 8)) (a : Z) (v : mword 64) :
  uM_store8 M a v = umem_write M a 8 (nth_byte v).
Proof. exact (uM_store_umem_write M a 8%nat v). Qed.

Require Import FdSlots.  (* [fdstate] -- what a descriptor slot holds *)
Require Import ProcGeom.  (* [NOFILE] -- how many of them there are *)
Require Import UserFd.   (* [ufd_auth] -- the PROGRAM's own view of
                            its descriptor table, the authority for
                            which rides inside [urun] *)
Section UkRun.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* NO ambient [CpuId]: the hart is an explicit argument of [urun], and the
     [WP] under that binder resolves to the one bound there -- the trick
     [UexecRet.ukc] uses. *)
  Context `{!ghost_varG Σ Z}.

  (* ===================================================================== *)
  (* §1 THE RUNNING PREDICATE.                                             *)
  (* ===================================================================== *)
  (* [avail] is the FREE STACK, in words, below the current sp -- the
     user-mode twin of [sie_cap_gpr]'s counting argument.  The process owns
     it; an sp-adjust hands a frame out of it or takes one back; every other
     instruction threads it unchanged, which is why every leaf that writes a
     register takes [unot_sp] as a premise (a write to sp would move the
     index this ownership is keyed by). *)
  (* THE DESCRIPTOR VIEW IS HIDDEN HERE, exactly as the break and the image
     are: [urun] is what a PROGRAM proof carries between instructions, and a
     program that never looks at its descriptors should not have to name
     them.  A leaf that IS closing back up has just destructed the
     existential, so it can say which view it is at -- the same discipline
     [sz] follows, and the reason [urun_close] takes [fdv] as a parameter. *)
  (* THE DEPOSIT SUPPLIER AND ITS MINTING LAW.  Since the ARM, the trap
     contract's returning arm demands the process's bundle for the number it
     is at ([UexecRet.uexec_dep_F]); a leaf below the file-system tower
     cannot see that the instance's [sbundle_at] is [emp] at its number, so it
     pays with the law below.

     WHY IT RIDES IN [urun] AND NOT IN [uvb], AND WHY IT IS ABSTRACT.  A
     [uvb] conjunct would make the KERNEL owe the supply to resume ANY
     process, and an application whose predicate is not trivially true
     cannot pay that -- echo's is [taint ∨ pins], true of every view only
     after the taint is minted -- so every pre-taint trap round would be
     unsatisfiable: the GAP-premise trap sitting in the trap loop.  Carrying
     a CONCRETE [□ ssupply] here instead is the SAME refutation one level
     down: echo could not build a [urun] at all before the taint.  So what
     rides here is an ABSTRACT supplier the program chooses, the way [Rut]
     and [Rfd] are abstract, with the numbers it undertakes to pay for
     ([psok]) beside it -- both fields of the ambient [UexecSG.uprogSG],
     which is what keeps every program lemma statement from naming either.

     THE LAW IS KEY-FREE, AND THAT IS FORCED, NOT CHOSEN.  A law stated at
     [urun]'s own bound key would have to survive every move the program
     makes to that key, because [urun] is re-established after every
     instruction: a store moves [M] ([urun_close] at
     [umem_write M …]), sbrk moves [pm] and [sz], open / dup / close / pipe
     move [fdv], and every returning ecall moves [cw].  Closed under all
     five, a key-indexed law IS the key-free one.  So the admission [psok]
     is a set of NUMBERS, and a bundle whose content reads the key -- exec's,
     which reads argv out of the image -- is not payable through this law at
     all: it goes the EXPLICIT-PREMISE route the exec leaf already uses
     ([UkRunSys.wp_uk_ecall_exec] takes the deposit as a hypothesis), which
     is why [USYS_exec] is excluded here.  A bundle that IS key-free once
     the descriptor view is fixed -- echo's console write, whose input is a
     trace seed minted from unit -- goes through the law.  THE HONEST
     CONSEQUENCE: a program admitting a number pays that number's bundle at
     EVERY key, not only at the call it is about to make. *)
  (* BUPD-SHAPED, like the class's own two laws ([UexecSG.v]'s header): a
     bundle may hold a resource that is free but not derivable from [emp]
     -- write's console arm carries the trace seed, the mono-list unit --
     and putting the update in the LAW rather than in a particular supplier
     is what keeps such a piece payable by a program whose supplier is
     [emp].  The ARM still demands a plain [sbundle]; the leaf runs the
     update inside its own WP step. *)
  Definition udep : iProp Σ :=
    (□ Dsup ∗
     ⌜ forall (n : Z) (W : uvis),
         psok n -> n <> USYS_exec ->
         ⊢ □ Dsup ==∗ sbundle uslot n W ⌝)%I.

  Global Instance udep_persistent : Persistent udep.
  Proof. rewrite /udep. apply _. Qed.

  (* what a leaf does with it: mint the deposit the ecall arm asks for *)
  Lemma udep_dep (n : Z) (W : uvis) :
    psok n -> n <> USYS_exec -> udep -∗ |==> sbundle uslot n W.
  Proof.
    intros Hok Hne. iIntros "[#Hs %Hlaw]".
    iApply (Hlaw n W Hok Hne). iExact "Hs".
  Qed.

  (* [avail] is the FREE STACK, in words, below the current sp -- the
     user-mode twin of [sie_cap_gpr]'s counting argument.  The process owns
     it; an sp-adjust hands a frame out of it or takes one back; every other
     instruction threads it unchanged, which is why every leaf that writes a
     register takes [unot_sp] as a premise (a write to sp would move the
     index this ownership is keyed by). *)
  (* THE DESCRIPTOR VIEW IS HIDDEN HERE, exactly as the break and the image
     are: [urun] is what a PROGRAM proof carries between instructions, and a
     program that never looks at its descriptors should not have to name
     them.  A leaf that IS closing back up has just destructed the
     existential, so it can say which view it is at -- the same discipline
     [sz] follows, and the reason [urun_close] takes [fdv] as a parameter. *)
  (* THE ECALL LEAF'S DEPOSIT PREMISE, as a WAND OFF THE AUTHORITIES the
     leaf already holds -- and it has to be a wand and not a bare premise:
     the key the deposit is at is [uvis_of_run m pc M pm sz fdv cw], and
     [M] / [pm] / [sz] / [fdv] / [cw] are bound by [urun]'s own existential,
     so a leaf has them only AFTER it destructs and can never name them in
     its own statement.  Same wall as the key-free law above, one level out.

     THE DISJUNCTION IS THE TWO ROUTES.  Left: the number is one the program
     admits ([psok]), and the leaf mints the bundle from [udep] --
     [udepw_mint].  Right: the program hands an EXPLICIT deposit at this
     key, which is what exec takes always, and what a program with a
     key-reading bundle (init's mknod, a constraining application's write)
     takes at its own numbers. *)
  Definition udepw (γt γd γs γfd : gname) (m : regfile) (pc : mword 64)
      (n : Z) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (cw : Z),
       uheap γt γd γs M pm sz -∗ ufd_auth γfd fdv -∗
       uheap γt γd γs M pm sz ∗ ufd_auth γfd fdv ∗
       (⌜psok n /\ n <> USYS_exec⌝
        ∨ sbundle uslot n (uvis_of_run m pc M pm sz fdv cw)))%I.

  (* the GENERIC route's supplier: a number the program admits *)
  Lemma udepw_of_psok (γt γd γs γfd : gname) (m : regfile) (pc : mword 64)
      (n : Z) :
    psok n -> n <> USYS_exec -> ⊢ udepw γt γd γs γfd m pc n.
  Proof.
    intros Hok Hne. rewrite /udepw. iIntros (M pm sz fdv cw) "Hh Hf".
    iFrame "Hh Hf". iLeft. iPureIntro. exact (conj Hok Hne).
  Qed.

  (* THE LEAF'S USE OF IT, at every number including exec: the left
     disjunct carries [n <> USYS_exec] itself, so at exec only the explicit
     deposit can have been taken and no side condition is owed here. *)
  (* ...UNDER A BASIC UPDATE, since the law is (UexecSG.v's header).  Every
     call site is inside its leaf's own WP goal, which absorbs it. *)
  Lemma udepw_mint (γt γd γs γfd : gname) (m : regfile) (pc : mword 64)
      (n : Z) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
      (fdv : list fdstate) (cw : Z) :
    udep -∗ udepw γt γd γs γfd m pc n -∗
    uheap γt γd γs M pm sz -∗ ufd_auth γfd fdv ==∗
    uheap γt γd γs M pm sz ∗ ufd_auth γfd fdv ∗
    sbundle uslot n (uvis_of_run m pc M pm sz fdv cw).
  Proof.
    iIntros "#Hdep Hsb Hheap Hufd".
    iDestruct ("Hsb" $! M pm sz fdv cw with "Hheap Hufd")
      as "(Hheap & Hufd & [%Hok | Hb])"; iFrame "Hheap Hufd";
      [ iApply (udep_dep n _ (proj1 Hok) (proj2 Hok) with "Hdep")
      | by iModIntro ].
  Qed.

  (* THE EXEC DEPOSIT'S CARRIER, and why it is key-free too.  exec is the
     one number the law above excludes -- its bundle reads argv out of the
     key's image -- so its deposit takes the EXPLICIT route.  But the key an
     exec ecall traps from is built by the walk that reaches it ([M], [pm],
     [sz], [fdv], [cw] bound by [urun]'s existential, the register file by
     the caller's own instruction sequence), so no lemma up the chain can
     NAME it: what a program that execs carries is the bundle AT EVERY KEY,
     persistently.  This is the ARM's spelling of the enriched tier's own
     supplier: a program that execs takes it as an explicit premise and
     hands it down to its exec leaf, and the kernel-side constructor -- which
     sits above the file-system tower and holds the process's exec bundle --
     is what pays it.

     NOT IN [urun].  A conjunct there would make EVERY program owe the exec
     bundle at every key, which is the GAP-premise trap [udep]'s note
     refutes one number over: a constraining application (echo, at
     [Dsup := emp]) could not build a [urun] at all. *)
  Definition uxsup : iProp Σ := (□ ∀ W : uvis, sbundle uslot USYS_exec W)%I.

  Global Instance uxsup_persistent : Persistent uxsup.
  Proof. rewrite /uxsup. apply _. Qed.

  (* what an exec leaf's caller does with it: the explicit disjunct of
     [udepw], at whatever key the walk has reached *)
  Lemma udepw_of_uxsup (γt γd γs γfd : gname) (m : regfile) (pc : mword 64) :
    uxsup -∗ udepw γt γd γs γfd m pc USYS_exec.
  Proof.
    iIntros "#Hx" (M pm sz fdv cw) "Hh Hf". iFrame "Hh Hf". iRight.
    iApply "Hx".
  Qed.

  Definition urun (γt γd γs γfd : gname) (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) : iProp Σ :=
    (∃ (xi : TsoCtx.CurCtx) (C : ucfg) (pt : uptd) (Rfd : list fdstate -> iProp Σ)
       (Rut : uptd -> iProp Σ) (sz : Z)
       (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (fdv : list fdstate)
       (* THE WORKING DIRECTORY IS HIDDEN TOO, and with no ghost beside it:
          a program that never looks at its cwd should not have to name
          it, and nothing in the running bundle reads it -- it only rides
          the bundle so the trap-out key can be built at the inum the
          process was resumed at ([UexecRet.ukb_F]'s pin). *)
       (cw : Z),
       ⌜ loop_ok C pt ⌝ ∗ ⌜ perm_of (ud_um pt) sz = pm ⌝ ∗
       (* A6.140: the residue-token accessor rides the bundle as a PURE
          fact, so a leaf that re-enters [ukc] can hand it back over *)
       ⌜ forall pt' : uptd,
           ⊢ Rut pt' -∗ TsoCtx.own_context (CID := h) (cur_ctx (CurCtx := xi)) ∗
                        (TsoCtx.own_context (CID := h) (cur_ctx (CurCtx := xi)) -∗ Rut pt') ⌝ ∗
       uheap γt γd γs M pm sz ∗
       ustack γd (m !!! Regidx csp_rs1) avail ∗
       (* THE PROGRAM'S OWN VIEW OF ITS DESCRIPTORS, keyed at the very [fdv]
          the bundle is at.  This is the conjunct that makes a user-level fd
          fact possible: [urun] is where [fdv] is bound and carried between
          instructions, so it is the only place an authority can be pinned
          to it.  The HANDLES ([UserFd.ufd]) live outside, in the program's
          own context, which is what lets a proof say "I hold fd 1" without
          naming the whole table.
          Note this is NOT [Rfd] one line down: [Rfd] is the KERNEL's
          fragment bundle, chosen by the loop and handed back whole at every
          trap, and a program never learns its ghost name. *)
       ufd_auth γfd fdv ∗
       udep ∗
       uvb (CID := h) (XI := xi) C pt Rfd Rut sz pm fdv cw M m pc)%I.

  (* "this instruction does not write sp".  Every leaf that writes a general
     register carries it; a concrete [rd] decides it by [vm_compute]. *)
  Definition unot_sp (rd : mword 5) : Prop := Regidx csp_rs1 <> Regidx rd.

  Lemma unot_sp_upd (rd : mword 5) (v : mword 64) (m : regfile) :
    unot_sp rd -> (<[Regidx rd := v]> m) !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof. intro H. exact (upd_ne m (Regidx rd) (Regidx csp_rs1) v H). Qed.

  (* THE CLOSE.  This is the lemma that makes the whole interface work: a
     continuation phrased on [urun] discharges the ∀-quantified [ukc] that
     every existing leaf demands, because [urun] supplies its own ambient. *)
  (* [sz] is a parameter: [urun] hides the break existentially, but a leaf
     that is closing back up has just destructed it, so it can say which one.
     Re-introducing the existential at THAT size is all this does. *)
  Lemma urun_close (γt γd γs γfd : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (sz : Z) (fdv : list fdstate) (cw : Z) (m : regfile) (pc : mword 64)
      (avail : nat) :
    uheap γt γd γs M pm sz -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    (* ...and the descriptor authority, at the same [fdv] the key is at *)
    ufd_auth γfd fdv -∗
    (* the deposit supplier and its law, back at the same key -- persistent,
       so a leaf that destructed [urun] hands the very copy it read *)
    udep -∗
    (∀ h : CpuId, urun γt γd γs γfd h m pc avail -∗ WP (Loop : expr riscv_lang)) -∗
    ukc pm M sz fdv cw m pc.
  Proof.
    iIntros "Hheap Hstk Hufd #Hdep Hcont".
    rewrite /ukc. iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    iApply ("Hcont" $! h). iExists xi, C, pt, Rfd, Rut, sz, M, pm, fdv, cw.
    iFrame "Hheap Hstk Hufd Hdep Hb". iPureIntro.
    split_and!; [ exact Hlo | exact Hpm | exact HRut ].
  Qed.

  (* [uv_upd] is the OTHER way a leaf writes a register (jalr's, where the
     write is optional).  It hid a real bug: the generated wrapper did not
     recognise the shape, so it claimed [avail] was preserved across an
     instruction that can write sp -- and that showed up not as a proof
     failure but as unification diverging inside the transparent [rf_upd].
     Hence this lemma, and the [unot_sp] premise that goes with it. *)
  Lemma uv_upd_not_sp (m : regfile) (rd : mword 5)
      (wr : option (mword 5 * mword 64)) (d : mword 64) :
    unot_sp rd ->
    (uint rd = 0 /\ wr = None) \/ (uint rd <> 0 /\ wr = Some (rd, d)) ->
    (uv_upd m wr) !!! Regidx csp_rs1 = m !!! Regidx csp_rs1.
  Proof.
    intros Hns [[_ ->] | [_ ->]]; [ reflexivity | ].
    cbn [uv_upd]. exact (unot_sp_upd rd (regval_into_reg d) m Hns).
  Qed.

  (* ...and the same when the instruction WROTE a register: the free stack
     is keyed by sp, and [unot_sp] says this write was not to sp. *)
  Lemma urun_close_upd (γt γd γs γfd : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (m : regfile) (rd : mword 5) (v : mword 64)
      (sz : Z) (fdv : list fdstate) (cw : Z) (pc' : mword 64) (avail : nat) :
    unot_sp rd ->
    uheap γt γd γs M pm sz -∗
    ustack γd (m !!! Regidx csp_rs1) avail -∗
    ufd_auth γfd fdv -∗
    udep -∗
    (∀ h : CpuId, urun γt γd γs γfd h (<[Regidx rd := v]> m) pc' avail -∗
                  WP (Loop : expr riscv_lang)) -∗
    ukc pm M sz fdv cw (<[Regidx rd := v]> m) pc'.
  Proof.
    intros Hns. iIntros "Hheap Hstk Hufd #Hdep Hcont".
    iApply (urun_close with "Hheap [Hstk] Hufd Hdep Hcont").
    rewrite (unot_sp_upd rd v m Hns). iExact "Hstk".
  Qed.

  (* ===================================================================== *)
  (* §2 THE FETCH BRIDGE.                                                  *)
  (*                                                                       *)
  (* [uinstr_is] plus the heap gives the Prop-level decode fact the         *)
  (* existing engine consumes.  Every clause of [UmodeMem.uinstr] comes off *)
  (* a text fragment except [ui_inpage], which is TEMPORARY: it is here     *)
  (* only until WpUmodeStep's [uv_fetch_base_2] takes the second halfword's *)
  (* leaf as a premise instead of deriving it from the window being on one  *)
  (* page.  The source for that premise is the fragment at [uint pc + 2],   *)
  (* which this lemma already has in hand.                                  *)
  (* ===================================================================== *)
  Lemma uheap_text_byte (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (a : Z) (b : bv 8) :
    uheap γt γd γs M pm szh -∗ utext γt a b -∗
    ⌜ M !! a = Some b /\ forall pt sz, proc_pt_wf pt ->
        perm_of (ud_um pt) sz = pm -> uva_fetch_leaf pt (mword_of_int a) ⌝.
  Proof.
    iIntros "Hheap Hb".
    iDestruct (uheap_text with "Hheap Hb") as %(HM & (q & Hq & Hx) & Hbnd).
    iPureIntro. split; [ exact HM | ].
    intros pt sz Hwf Hpmeq.
    unfold uperm_at in Hq. rewrite <- Hpmeq in Hq.
    destruct (perm_of_X pt sz _ q Hwf Hq Hx) as (w & Hw & Hok).
    exists w. exact (conj Hw Hok).
  Qed.


  (* the byte AT THE PC gives the two things every branch of the bridge needs:
     the pc is canonical, and its page is fetch-ok at any table realizing the
     key.  Factored out so the three decode shapes below do not triplicate it. *)
  Lemma uheap_text_pc (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (pc : mword 64) (b : bv 8) :
    uheap γt γd γs M pm szh -∗ utext γt (uint pc + Z.of_nat 0) b -∗
    ⌜ uva_canon pc /\
      forall pt sz, proc_pt_wf pt -> perm_of (ud_um pt) sz = pm ->
                    uva_fetch_leaf pt pc ⌝.
  Proof.
    iIntros "Hheap Hb".
    iDestruct (uheap_text_byte with "Hheap Hb") as %(_ & Hlf).
    iDestruct (uheap_text with "Hheap Hb") as %(_ & _ & Hbnd).
    iPureIntro.
    change (Z.of_nat 0) with 0 in Hbnd, Hlf. rewrite Z.add_0_r in Hbnd, Hlf.
    destruct (ucanon_of_bound (uint pc) Hbnd) as [_ Hcan].
    rewrite moi_of_uint in Hcan, Hlf.
    exact (conj Hcan Hlf).
  Qed.

  (* ...and the pc's page is TEXT of every table the projection came from:
     X off the text half's class, not-W off its new clause, and
     [UmodeText.uva_text_of_perm] reads both off the leaf word *)
  Lemma uheap_text_pc_text (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (pc : mword 64) (b : bv 8) :
    uheap γt γd γs M pm szh -∗ utext γt (uint pc + Z.of_nat 0) b -∗
    ⌜ forall pt sz, proc_pt_wf pt -> perm_of (ud_um pt) sz = pm ->
                    uva_text pt (uint pc) ⌝.
  Proof.
    iIntros "Hheap Hb".
    iDestruct (uheap_text with "Hheap Hb") as %(_ & Hx & _).
    iDestruct (uheap_text_nw with "Hheap Hb") as %Hnw.
    iPureIntro.
    change (Z.of_nat 0) with 0 in Hx, Hnw. rewrite Z.add_0_r in Hx, Hnw.
    intros pt sz Hwf Hpmeq. subst pm.
    destruct Hx as (q & Hq & Hqx).
    destruct (up_W q) eqn:Hqw.
    - exfalso. apply Hnw. exists q. split; [ exact Hq | exact Hqw ].
    - exact (uva_text_of_perm pt sz (uint pc) q Hq Hqx Hqw).
  Qed.

  (* THE BRIDGE: [uinstr_is] plus the heap gives the Prop-level decode fact
     the existing engine consumes.  Every clause of [UmodeMem.uinstr] comes
     off a text fragment -- the leaf and canonicity from the byte at the pc,
     the code bytes from the run -- except [ui_inpage], which [uinstr_is]
     still carries for its one remaining consumer. *)
  Lemma uinstr_is_uk_instr (γt γd γs : gname) (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm)
      (szh : Z) (pc : mword 64) (is_rvc : bool) (i : instruction) :
    uheap γt γd γs M pm szh -∗ uinstr_is γt pc is_rvc i -∗
    ⌜ uk_instr pm M pc is_rvc i ⌝.
  Proof.
    iIntros "Hheap #Hi". rewrite /uinstr_is.
    iDestruct "Hi" as "(%Hal2 & %Hpg & Hcode)".
    destruct is_rvc.
    - iDestruct "Hcode" as (h) "(%HisRVC & %Hdec & Hbs)".
      destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal4.
      + (* compressed at a 4-ALIGNED pc: the window IS a 4-byte word whose
           low half is the halfword *)
        iDestruct "Hbs" as (w) "(%Hlow & #Hbs)".
        iDestruct (uheap_text_run with "Hheap Hbs") as %Hb4.
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
          [ reflexivity | ].
        iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
        iDestruct (uheap_text_pc_text with "Hheap H0") as %Htx.
        iPureIntro. intros pt sz Hwf Hpmeq.
        refine (UInstr pt M pc true i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _
                  (Htx pt sz Hwf Hpmeq)).
        exists h. split_and!; [ exact HisRVC | | exact Hdec | ].
        * intros j Hj. rewrite <- Hlow.
          rewrite (nth_byte_subrange_lo w j ltac:(lia)).
          exact (Hb4 j ltac:(lia)).
        * intros _. exists (nth_byte w 2), (nth_byte w 3).
          pose proof (Hb4 2%nat ltac:(lia)) as H2.
          pose proof (Hb4 3%nat ltac:(lia)) as H3.
          change (Z.of_nat 2) with 2 in H2. change (Z.of_nat 3) with 3 in H3.
          exact (conj H2 H3).
      + (* compressed at a 2-mod-4 pc: two bytes, no trailing obligation *)
        iDestruct "Hbs" as "#Hbs".
        iDestruct (uheap_text_run with "Hheap Hbs") as %Hb2.
        iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
          [ reflexivity | ].
        iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
        iDestruct (uheap_text_pc_text with "Hheap H0") as %Htx.
        iPureIntro. intros pt sz Hwf Hpmeq.
        refine (UInstr pt M pc true i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _
                  (Htx pt sz Hwf Hpmeq)).
        exists h. split_and!; [ exact HisRVC | exact Hb2 | exact Hdec | ].
        intros Hc. rewrite Hc in Hal4. discriminate Hal4.
    - iDestruct "Hcode" as (w) "(%HnRVC & %Hdec & #Hbs)".
      iDestruct (uheap_text_run with "Hheap Hbs") as %Hb4.
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbs") as "#H0";
        [ reflexivity | ].
      iDestruct (uheap_text_pc with "Hheap H0") as %[Hcanon Hlf].
      iDestruct (uheap_text_pc_text with "Hheap H0") as %Htx.
      iPureIntro. intros pt sz Hwf Hpmeq.
      refine (UInstr pt M pc false i Hal2 Hcanon (Hlf pt sz Hwf Hpmeq) Hpg _
                (Htx pt sz Hwf Hpmeq)).
      exists w. split_and!; [ exact HnRVC | exact Hb4 | exact Hdec ].
  Qed.


  (* ===================================================================== *)
  (* §3 WHAT A MEMORY LEAF READS OFF THE HEAP.                                                        *)
  (*                                                                       *)
  (* Two representatives, one register-only and one memory, cut in the     *)
  (* shape every remaining leaf will take:                                 *)
  (*                                                                       *)
  (*   the instruction resource, the memory the instruction TOUCHES, the   *)
  (*   run, and a continuation at the updated run.                         *)
  (*                                                                       *)
  (* No ambient, no [ukc], no postcondition, and the immediate in NORMAL   *)
  (* FORM.  Everything the instruction does not touch frames, because it   *)
  (* is either inside [urun] (registers, image, table, permissions) or     *)
  (* outside and unmentioned (every other byte).                           *)
  (* ===================================================================== *)

  (* THE DATA WORD AT AN ADDRESS: in range, and WRITABLE.  This is where
     the permission table stops being visible -- the caller holds an
     exclusive [uword], and the heap turns that into the leaf's
     [uk_store_ok] without the caller ever naming a page or a PTE bit.
     Consuming the run inside this proof is free: the conclusion is pure, so
     the caller's [iDestruct … as %…] keeps both the heap and the word. *)
  Lemma uheap_uword_at (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (w : mword 64) :
    uheap γt γd γs M pm sz -∗ uwordq γd dq a w -∗
    ⌜ 0 <= a < 2 ^ 38 /\ uw_addr pm a ⌝.
  Proof.
    iIntros "Hheap Hw". rewrite /uwordq /ubytesq.
    iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hw") as "H0";
      [ reflexivity | ].
    iDestruct (uheap_ubyte with "Hheap H0") as %(_ & Hw & Hb).
    iPureIntro. change (Z.of_nat 0) with 0 in Hw, Hb.
    rewrite Z.add_0_r in Hw, Hb. exact (conj Hb Hw).
  Qed.

  (* A RUN OF OWNED DATA BYTES: present in the image at its own values, on
     writable pages, in range.  This is the single lemma every memory leaf
     goes through -- it is what replaces the caller-supplied permission,
     canonicity and presence premises of the UkStore/UkLoad leaves. *)
  Lemma uheap_ubytes_at (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (dq : dfrac) (a : Z) (n : nat)
      (f : nat -> bv 8) :
    uheap γt γd γs M pm sz -∗ ubytesq γd dq a n f -∗
    ⌜ forall j : nat, (j < n)%nat ->
        M !! (a + Z.of_nat j)%Z = Some (f j) /\
        uw_addr pm (a + Z.of_nat j)%Z /\
        0 <= a + Z.of_nat j < 2 ^ 38 ⌝.
  Proof.
    iIntros "Hheap Hbs". rewrite /ubytes /ubytesq.
    iInduction n as [| n IH] "IH" forall (f).
    - iPureIntro. intros j Hj. exfalso. lia.
    - iEval (rewrite seq_S big_sepL_app /=) in "Hbs".
      iDestruct "Hbs" as "(Hlo & Hhi & _)".
      iDestruct (uheap_ubyte with "Hheap Hhi") as %Hn.
      (* the IH is generalised over [f], so instantiate that before feeding it *)
      iDestruct ("IH" $! f with "Hheap Hlo") as %Hlo.
      iPureIntro. intros j Hj.
      destruct (decide (j = n)) as [-> | Hne]; [ exact Hn | apply Hlo; lia ].
  Qed.

  (* ===================================================================== *)
  (* WHAT THE FREE STACK ITSELF SAYS ABOUT SP.                             *)
  (*                                                                       *)
  (* The deepest word [ustack γd sp n] owns sits at [uint sp - 8n], and     *)
  (* [uheap] bounds every owned address below MAXVA -- so "sp has n words   *)
  (* of room below it" is a CONSEQUENCE of holding the free stack, not an   *)
  (* obligation on whoever moves sp.  The sp-adjust rules take neither as   *)
  (* a premise.                                                            *)
  (* ===================================================================== *)
  Lemma ustack_room (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (sp : mword 64) (n : nat) :
    uheap γt γd γs M pm sz -∗ ustack γd sp n -∗ ⌜ 8 * Z.of_nat n <= uint sp ⌝.
  Proof.
    iIntros "Hheap Hstk".
    destruct n as [| n'].
    - iPureIntro. pose proof (proj1 (bv_unsigned_in_range _ sp)) as H0.
      rewrite uint_unsigned. lia.
    - iDestruct (ustack_acc γd sp (S n') n' ltac:(lia) with "Hstk") as "[Hw _]".
      iDestruct "Hw" as (w) "Hw".
      iDestruct (uheap_uword_at with "Hheap Hw") as %[Hb _].
      iPureIntro. rewrite Nat2Z.inj_succ. lia.
  Qed.

  (* ...and the same fact read at a MOVED sp: had [sp + 8k] wrapped, its own
     frame's deepest word would be at a negative address. *)
  Lemma ustack_nowrap (γt γd γs : gname) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) (sp : mword 64) (k : nat) :
    uheap γt γd γs M pm sz -∗
    ustack γd (add_vec_int sp (8 * Z.of_nat k)) k -∗
    ⌜ uint sp + 8 * Z.of_nat k < Z64 ⌝.
  Proof.
    iIntros "Hheap Hstk".
    iDestruct (ustack_room γt γd γs M pm sz
                 (add_vec_int sp (8 * Z.of_nat k)) k with "Hheap Hstk") as %Hr.
    iPureIntro.
    pose proof (bv_unsigned_in_range _ (add_vec_int sp (8 * Z.of_nat k))) as Hr2.
    rewrite Zmod64 in Hr2. rewrite <- uint_unsigned in Hr2.
    pose proof (bv_unsigned_in_range _ sp) as Hs.
    rewrite Zmod64 in Hs. rewrite <- uint_unsigned in Hs.
    (* the moved sp's unsigned value IS the sum mod 2^64 *)
    assert (Hmod : uint (add_vec_int sp (8 * Z.of_nat k))
                   = (uint sp + 8 * Z.of_nat k) mod Z64).
    { unfold add_vec_int. rewrite !uint_unsigned.
      rewrite add_vec64_unsigned moi64_unsigned. unfold bv_wrap.
      assert (E64 : bv_modulus 64 = 18446744073709551616)
        by (vm_compute; reflexivity).
      rewrite E64 Zplus_mod_idemp_r. unfold Z64. reflexivity. }
    destruct (decide (uint sp + 8 * Z.of_nat k < Z64)) as [Hlt | Hge];
      [ exact Hlt | exfalso ].
    (* one wrap at most: [8k] and [uint sp] are each below 2^64 *)
    assert (Hstep : (uint sp + 8 * Z.of_nat k) mod Z64
                    = uint sp + 8 * Z.of_nat k - Z64).
    { assert (Ha : uint sp + 8 * Z.of_nat k
                   = (uint sp + 8 * Z.of_nat k - Z64) + 1 * Z64) by lia.
      rewrite {1}Ha. rewrite Z_mod_plus_full.
      apply Z.mod_small. unfold Z64 in *. lia. }
    rewrite Hstep in Hmod. unfold Z64 in *. lia.
  Qed.

  (* ...and what a PROGRAM can read off its own run, without opening it: the
     two stack facts every prologue used to take as premises. *)
  Lemma urun_stack (γt γd γs γfd : gname) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) :
    urun γt γd γs γfd h m pc avail -∗
    ⌜ uint (m !!! Regidx csp_rs1) mod 8 = 0
      /\ 8 * Z.of_nat avail <= uint (m !!! Regidx csp_rs1) ⌝.
  Proof.
    iIntros "Hrun".
    iDestruct "Hrun" as (xi C pt Rfd Rut sz M pm fdv cw) "(%Hlo & %Hpm & %HRut & Hheap & Hstk & Hufd & #Hdep & Hb)".
    iDestruct (ustack_align with "Hstk") as %Hal.
    iDestruct (ustack_room with "Hheap Hstk") as %Hroom.
    iPureIntro. exact (conj Hal Hroom).
  Qed.

  (* ===================================================================== *)
  (* §4 THE ENTRY: the process's FIRST WP.                                 *)
  (*                                                                       *)
  (* This is the other end of the interface.  A program never constructs a  *)
  (* [urun]; it is handed one here, together with the points-to facts for   *)
  (* its whole initial image, in exchange for a proof that it is safe from  *)
  (* the key's resume state.  The gnames are FRESH -- allocated at this     *)
  (* WP, under the ambient the slot quantifies over -- which is why they    *)
  (* are arguments of [urun] rather than section variables.                 *)
  (* ===================================================================== *)

  (* [uheap_alloc]'s one premise, discharged.  Two sources: a MAPPED address
     sits in a page the table maps, and [upt_map_wf] puts every such page
     below the trapframe; a LIVE address is below the break, and [usz_ok]
     puts the break below the trapframe too. *)
  Lemma umem_lazy_bound {CIDL : CpuId} {XIL : TsoCtx.CurCtx} (pt : uptd) (sz : Z) (M : gmap Z (bv 8)) :
    proc_pt_wf pt -> usz_ok sz ->
    umem_lazy_x pt sz M -∗ ⌜ forall a : Z, is_Some (M !! a) -> 0 <= a < 2 ^ 38 ⌝.
  Proof.
    iIntros (Hwf Hsz) "H". iDestruct "H" as (Mp) "(_ & %Hiff & _ & _)".
    iPureIntro. intros a Ha.
    change (2 ^ 38) with 274877906944.
    destruct (proj1 (Hiff a) Ha) as [Hm | Hl].
    - destruct Hm as (vpn & w & j & Hvl & Hj & ->).
      destruct Hwf as (Hmw & _).
      destruct (Hmw vpn w Hvl) as [Hlt _].
      rewrite tf_vpn_unsigned in Hlt.
      pose proof (proj1 (bv_unsigned_in_range _ vpn)) as Hv0.
      lia.
    - pose proof (usz_ok_live sz a Hsz Hl). lia.
  Qed.

  (* THE ENTRY, with the process's initial free stack carved out of its data.
     [avail] words below the resume sp become [urun]'s free stack; the rest
     of the data is DROPPED (affinely), which is fine for a program whose
     only memory is its stack.  A program that also needs static data wants
     the non-lossy form of [ubytes_of_map], which its induction already
     produces -- see the note there.

     The two premises are exactly what the old [uk_stack] gate decided, in
     the vocabulary of the heap: enough room below sp, and the bytes there
     actually present in the data half.  [sz] is bound by the slot, so the
     second is stated for every [sz] the bundle could carry. *)
  (* [UserHeap.umap_split_at] at an arbitrary decidable cut: the data map
     split into the part satisfying [P] and its complement *)
  Local Lemma umap_split_pred (γd : gname) (D : gmap Z (bv 8)) (P : Z -> Prop)
      `{!forall a : Z, Decision (P a)} :
    ([∗ map] k ↦ b ∈ D, ubyte γd k b) -∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => P kv.1) D,
         ubyte γd k b) ∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => ~ P kv.1) D,
         ubyte γd k b).
  Proof.
    iIntros "H".
    rewrite -(big_sepM_union (fun k b => ubyte γd k b)
                (base.filter (fun kv : Z * bv 8 => P kv.1) D)
                (base.filter (fun kv : Z * bv 8 => ~ P kv.1) D)
                (map_disjoint_filter_complement _ D)).
    rewrite (map_filter_union_complement (fun kv : Z * bv 8 => P kv.1) D).
    iExact "H".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE GENERAL FORM: [uslot_of_urun]'s mint and carve with the data      *)
  (* OUTSIDE the frame handed over EXCLUSIVELY -- the bytes below the      *)
  (* frame's base and the bytes at or above sp.  A program whose static    *)
  (* data (a .bss buffer, say) lies below its stack takes it out of the    *)
  (* first half; an argument area is in the second.  [UShKernel.v] is what *)
  (* needs it: sh reads and writes its line buffer, which the lossy entry  *)
  (* would drop.                                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma uslot_of_urun_all (W : uvis) (avail : nat) :
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (* the map stops at the break -- [uslot_of_urun]'s own premise *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* ...and the deposit supplier, exactly as [uslot_of_urun] takes it *)
    udep -∗
    (∀ (γt γd γs γfd : gname) (h : CpuId),
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz γs (uvis_sz W) -∗
       utext_all γt (uvis_M W) (uvis_perm W) -∗
       ustd γfd (take NSTD (uvis_fd W)) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                       - 8 * Z.of_nat avail)
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyte γd k b) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                ~ (kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyte γd k b) -∗
       urun γt γd γs γfd h (tf_resume_gpr0 (uvis_tf W))
         (tf_resume_pc (uvis_tf W)) avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen Hstop. iIntros "#Hdep Hprog".
    rewrite uslot_ukc /ukc.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    set (sz := uvis_sz W).
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hfrag & Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan Hstop)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    iMod (ufd_alloc_std (uvis_fd W) ∅ Hfdlen (map_empty_subseteq _))
      as (γfd) "(Hufd & Hstd & _)".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    (* ---- the two cuts: at the frame's base, then at sp ---- *)
    set (sp := tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1).
    set (D := udata_lo (uvis_M W) (uvis_perm W) sz).
    set (base := (uint sp - 8 * Z.of_nat avail)%Z).
    iDestruct (umap_split_at γd D base with "Hd") as "[Dlo Dhi]".
    iDestruct (umap_split_pred γd _ (fun a : Z => a < uint sp) with "Dhi")
      as "[Dmid Dtop]".
    (* the upper half is [~ (k < sp)] on [D] itself: a key at or above sp
       is not below [base] *)
    iAssert ([∗ map] k ↦ b ∈ base.filter
                 (fun kv : Z * bv 8 => ~ (kv.1 < uint sp)) D, ubyte γd k b)%I
      with "[Dtop]" as "Dtop".
    { assert (E : base.filter (fun kv : Z * bv 8 => ~ (kv.1 < uint sp))
                    (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                  = base.filter (fun kv : Z * bv 8 => ~ (kv.1 < uint sp)) D).
      { rewrite map_filter_filter. apply map_filter_ext.
        intros k b _. cbn.
        split; [ intros [H _]; exact H
               | intro H; split; [ exact H | unfold base; lia ] ]. }
      rewrite E. iExact "Dtop". }
    (* ---- the frame, out of the middle ---- *)
    set (f := fun j : nat =>
                default (bv_0 8)
                  (base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                     (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                     !! (base + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < 8 * avail)%nat ->
                   base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                     (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                     !! (base + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hstk j Hj) as [b Hb].
      assert (Hb' : base.filter (fun kv : Z * bv 8 => kv.1 < uint sp)
                      (base.filter (fun kv : Z * bv 8 => ~ (kv.1 < base)) D)
                      !! (base + Z.of_nat j)%Z = Some b).
      { apply umap_filter_lookup_lt; [ unfold base; lia | ].
        apply umap_filter_lookup_ge; [ lia | exact Hb ]. }
      unfold f. rewrite Hb'. reflexivity. }
    iDestruct (ubytes_of_map γd _ base (8 * avail) f Hf with "Dmid") as "Hbs".
    iDestruct (ustack_of_ubytes γd sp avail f Hal8 Hroom with "Hbs") as "Hstk".
    iSpecialize ("Hprog" $! γt γd γs γfd h with "[%] Hszf Ht Hstd Dlo Dtop");
      [ exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    iFrame "Hheap Hstk Hufd Hdep".
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

  Lemma uslot_of_urun (W : uvis) (avail : nat) :
    (* the resume sp is word-aligned -- what [ustack] now asserts, and the
       one place it is an obligation rather than a consequence, since it is
       a fact about the process the kernel set up *)
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (* DECIDABLE FROM THE KEY, now that the key carries the break.  Before
       [uvis_sz] existed this had to be stated for every [sz] the slot's ∀
       admitted -- which includes [sz = 0], so it was not merely
       undecidable, it was unsatisfiable. *)
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    (* the descriptor table is [NOFILE] slots -- what the process's own
       authority is minted with ([UserFd.ufd_auth] carries it) *)
    length (uvis_fd W) = NOFILE ->
    (* THE MAP STOPS AT THE BREAK: above the page the break sits in, the
       key's permission view has no entry.  It is the U tier's reading of
       [ProcPtOwn.um_below] -- which the bundle does not carry, so it is
       stated here, where the program's own layout decides it -- and it is
       what makes [sbrk]'s new run FRESH ([UserHeap]'s own clause). *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* THE DEPOSIT SUPPLIER, at the key the slot is being built for.  This
       is the one obligation the ARM adds to an entry constructor: whoever
       hands a program a [urun] says which syscall bundles it can pay and
       out of what.  [UexecCond.cond_entry_slot] passes the generic one
       ([Dsup := ssupply], every number admitted); a verified program's
       constructor passes its own. *)
    udep -∗
    (∀ (γt γd γs γfd : gname) (h : CpuId),
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz γs (uvis_sz W) -∗
       utext_all γt (uvis_M W) (uvis_perm W) -∗
       (* THE LEDGER OF THE STANDARD STREAMS, at the states the resumed key
          carries.  It comes out here because it has to: the low [NSTD] keys
          are in [UserFd.ufd_map] by construction, so their fragments exist
          from the moment the authority does, and an exclusive fragment for
          a key already in the map can never be minted later.  A program
          that does not care about its standard streams drops it -- and then
          calls no allocating syscall, which is the honest reading of "it is
          not tracking its descriptors". *)
       ustd γfd (take NSTD (uvis_fd W)) -∗
       urun γt γd γs γfd h (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen Hstop. iIntros "#Hdep Hprog". rewrite uslot_ukc /ukc.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    set (sz := uvis_sz W).
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hfrag & Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan Hstop)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    (* ...AND THE PROGRAM'S DESCRIPTOR AUTHORITY, minted here beside the
       heap's three names.  This is where a process's [urun] is created, so
       it is where its own view of its table begins -- at the view the
       resumed KEY carries, which is the view the kernel is handing it. *)
    iMod (ufd_alloc_std (uvis_fd W) ∅ Hfdlen (map_empty_subseteq _))
      as (γfd) "(Hufd & Hstd & _)".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    (* ---- the carve ---- *)
    set (sp := tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1).
    set (D := udata_lo (uvis_M W) (uvis_perm W) sz).
    set (base := (uint sp - 8 * Z.of_nat avail)%Z).
    set (f := fun j : nat => default (bv_0 8) (D !! (base + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < 8 * avail)%nat ->
                   D !! (base + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hstk j Hj) as [b Hb].
      unfold f. unfold D, base in *. rewrite Hb. reflexivity. }
    iDestruct (ubytes_of_map γd D base (8 * avail) f Hf with "Hd") as "Hbs".
    iDestruct (ustack_of_ubytes γd sp avail f Hal8 Hroom with "Hbs") as "Hstk".
    iSpecialize ("Hprog" $! γt γd γs γfd h with "[%] Hszf Ht Hstd");
      [ exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    iFrame "Hheap Hstk Hufd Hdep".
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* ...AND THE SAME DEPOSIT WITH A READ-ONLY AREA ALONGSIDE.              *)
  (*                                                                      *)
  (* [uslot_of_urun] spends the whole data map on the frame.  A program    *)
  (* that also reads what exec left it -- its argument vector -- needs the *)
  (* rest of the map back, so this one CUTS the map at the entry sp:       *)
  (* everything below is frame territory and is carved into the free       *)
  (* stack exactly as before, everything at or above is PERSISTED and      *)
  (* handed over read-only.  The cut is [UkAbi.uk_args]'s own [uka_lo].    *)
  (*                                                                      *)
  (* Persisting is what makes the argument area cheap: the program may     *)
  (* take as many views of it as it likes and none of them has to be       *)
  (* disjoint from any other, so no caller and no entry gate ever has to   *)
  (* decide whether two argv slots point at the same string.               *)
  (* ------------------------------------------------------------------- *)
  Lemma uslot_of_urun_ro (W : uvis) (avail : nat) :
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat avail
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * avail)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat avail + Z.of_nat j)%Z)) ->
    (* the descriptor table is [NOFILE] slots -- what the process's own
       authority is minted with ([UserFd.ufd_auth] carries it) *)
    length (uvis_fd W) = NOFILE ->
    (* THE MAP STOPS AT THE BREAK: above the page the break sits in, the
       key's permission view has no entry.  It is the U tier's reading of
       [ProcPtOwn.um_below] -- which the bundle does not carry, so it is
       stated here, where the program's own layout decides it -- and it is
       what makes [sbrk]'s new run FRESH ([UserHeap]'s own clause). *)
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    (* THE DEPOSIT SUPPLIER, at the key the slot is being built for.  This
       is the one obligation the ARM adds to an entry constructor: whoever
       hands a program a [urun] says which syscall bundles it can pay and
       out of what.  [UexecCond.cond_entry_slot] passes the generic one
       ([Dsup := ssupply], every number admitted); a verified program's
       constructor passes its own. *)
    udep -∗
    (∀ (γt γd γs γfd : gname) (h : CpuId),
       ⌜ usz_ok (uvis_sz W) ⌝ -∗
       usz γs (uvis_sz W) -∗
       utext_all γt (uvis_M W) (uvis_perm W) -∗
       (* THE LEDGER OF THE STANDARD STREAMS, at the states the resumed key
          carries.  It comes out here because it has to: the low [NSTD] keys
          are in [UserFd.ufd_map] by construction, so their fragments exist
          from the moment the authority does, and an exclusive fragment for
          a key already in the map can never be minted later.  A program
          that does not care about its standard streams drops it -- and then
          calls no allocating syscall, which is the honest reading of "it is
          not tracking its descriptors". *)
       ustd γfd (take NSTD (uvis_fd W)) -∗
       ([∗ map] k ↦ b ∈ base.filter
             (fun kv : Z * bv 8 =>
                ~ (kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)))
             (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
          ubyteq γd DfracDiscarded k b) -∗
       urun γt γd γs γfd h (tf_resume_gpr0 (uvis_tf W)) (tf_resume_pc (uvis_tf W))
         avail -∗
       WP (Loop : expr riscv_lang))
    -∗ uslot W.
  Proof.
    intros Hal8 Hroom Hstk Hfdlen Hstop. iIntros "#Hdep Hprog". rewrite uslot_ukc /ukc.
    iIntros (h xi C pt Rfd Rut HRut) "%Hlo %Hpm Hb".
    set (sz := uvis_sz W).
    assert (Hwf : proc_pt_wf pt)
      by (destruct Hlo as (_ & _ & _ & _ & _ & H); exact H).
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iDestruct "Hb" as
      "(Hamb & Hregs & %Hsz & (Htlb & Hlazy & %Hinj & %Hacc) &
        Hfrag & Hcfg & Hgpr & Hpc & Hrut & Hkont)".
    iDestruct (umem_lazy_bound pt sz (uvis_M W) Hwf Hsz with "Hlazy") as %Hcan.
    iMod (uheap_alloc (uvis_M W) (uvis_perm W) sz Hcan Hstop)
      as (γt γd γs) "(Hheap & Hszf & #Ht & Hd)".
    (* ...AND THE PROGRAM'S DESCRIPTOR AUTHORITY, minted here beside the
       heap's three names.  This is where a process's [urun] is created, so
       it is where its own view of its table begins -- at the view the
       resumed KEY carries, which is the view the kernel is handing it. *)
    iMod (ufd_alloc_std (uvis_fd W) ∅ Hfdlen (map_empty_subseteq _))
      as (γfd) "(Hufd & Hstd & _)".
    rewrite -/(utext_all γt (uvis_M W) (uvis_perm W)).
    (* ---- the cut at the entry sp ---- *)
    set (sp := tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1).
    set (D := udata_lo (uvis_M W) (uvis_perm W) sz).
    iDestruct (umap_split_at γd D (uint sp) with "Hd") as "[Dlo Dhi]".
    iMod (uarea_persist γd _ with "Dhi") as "#Dhi".
    (* ---- the frame, out of what is below sp ---- *)
    set (base := (uint sp - 8 * Z.of_nat avail)%Z).
    set (f := fun j : nat =>
                default (bv_0 8)
                  (base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D
                     !! (base + Z.of_nat j)%Z)).
    assert (Hf : forall j : nat, (j < 8 * avail)%nat ->
                   base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D
                     !! (base + Z.of_nat j)%Z = Some (f j)).
    { intros j Hj. destruct (Hstk j Hj) as [b Hb].
      assert (Hb' : base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D
                      !! (base + Z.of_nat j)%Z = Some b)
        by (apply umap_filter_lookup_lt; [ unfold base; lia | exact Hb ]).
      unfold f. rewrite Hb'. reflexivity. }
    iDestruct (ubytes_of_map γd
                 (base.filter (fun kv : Z * bv 8 => kv.1 < uint sp) D)
                 base (8 * avail) f Hf with "Dlo") as "Hbs".
    iDestruct (ustack_of_ubytes γd sp avail f Hal8 Hroom with "Hbs") as "Hstk".
    iSpecialize ("Hprog" $! γt γd γs γfd h with "[%] Hszf Ht Hstd Dhi");
      [ exact Hsz | ].
    iApply "Hprog".
    iExists xi, C, pt, Rfd, Rut, sz, (uvis_M W), (uvis_perm W), (uvis_fd W),
      (uvis_cwd W).
    iSplitR; [ iPureIntro; exact Hlo | ].
    iSplitR; [ iPureIntro; exact Hpm | ].
    iSplitR; [ iPureIntro; exact HRut | ].
    iFrame "Hheap Hstk Hufd Hdep".
    rewrite /uvb /uvb_F /user_ptm_inv_x.
    iFrame "Hamb Hregs Hfrag Hcfg Hgpr Hpc Hrut Hkont Htlb Hlazy".
    iPureIntro. split_and!; [ exact Hsz | exact Hinj | exact Hacc ].
  Qed.

End UkRun.
