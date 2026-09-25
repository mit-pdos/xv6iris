/-
The closed trap loop's stage 2: THE ROUND'S ROWS (Rocq
`ProofUserretClosed.v`, `stvec_handler_loop`'s middle): what user execution
handed back at the trap, re-keyed onto usertrap's rows on the way in, and
usertrap's answers re-keyed onto the next slot on the way out.

* `urc_deposit` -- THE SPLIT (Rocq `uexec_ret_split`, the payment's
  `upay_at_ueq`, the fork / bundle case analysis, the kill row): the
  process's deposit at the trapped key `W` becomes usertrap's `utSysIn` /
  `utForkIn` / `utPayIn` / `utKillIn` at the record `syscall()` is called
  with; the ecall arm stays behind for the round.
* `urc_post` -- STEPS A/B (Rocq `uexec_ret_round_slot_of` with its row
  rewrites): usertrap's post rows (`utRound`, the kept rows, the ecall rows,
  exec's / fork's / wait's answers, the armed post, the untaken kill side)
  at the record, read at the trapped key's run projection, give the slot
  at the record the round left.  NOTHING IS MINTED.

## Deviations from Rocq

1. The rows are converted between the RECORD usertrap states them at
   (`utSysRec`/`utProTf` of uservec's saved frame, SpecUsertrap deviation 3)
   and the trapped key's run projection (`uvisRun W`), by the save walk's
   `tfUeq` (`UserretClosedDefs.urc_proTf_ueq`); Rocq's `wp_uservec_pt`
   hands the loop its rows at `uvis_run W` already.
2. Exec's failure arm: `syscExecFailed` at the post record up to the kernel
   words (SpecUsertrap deviation 9) gives Rocq's `uround_bump_ok ∧
   usys_mem_ok` reading here (`urc_exec_failed`).
3. The exit ecall's bundle row is `emp` at the kernel's deposit instance
   (`urc_sbundle_exit`, `UexecExecInst.xv6SbundleRest`): Lean's `uexecDepF`
   deposits nothing at exit (Rocq main's exit deposits the close payments --
   a later Rocq change, UexecRet drift).

Proof-mode lemmas; no instruction stepping.
-/
import Xv6.UserretClosedDefs

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The record uservec's save walk leaves (the trapped file in words 5..35). -/
abbrev urcV0 (V : ProcPriv) (W : Uvis) : ProcPriv := { V with tf := uservecTf V.tf (tfResumeGpr0 W.tf) }

attribute [local irreducible] uservecTf

theorem urcV0_len (V : ProcPriv) (W : Uvis) (hl : V.tf.length = 36) : (urcV0 V W).tf.length = 36 := by
  show (uservecTf V.tf _).length = 36; rw [uservecTf_length, hl]

/-- The key's run projection reads every `skeyEq` row the record does. -/
theorem urc_skey_run (W : Uvis) (V : ProcPriv) (Mp : Nat → List (BitVec 8)) (gn : GName)
    (cs : ExtTreeSet GName compare) (pid : BitVec 32) (hl : V.tf.length = 36)
    (hM : umemLazy V.upt V.sz.toNat Mp = W.M) (hpi : W.perm = permOf V.upt.um V.sz.toNat)
    (hsz : W.sz = V.sz.toNat) (hcw : W.cwd = V.cwi) (hgn : W.gen = gn) (hch : W.ch = cs)
    (hpid : W.pid = pid) (hlz : W.lazy = V.pvLazy) :
    skeyEq (uvisOf (utSysRec (tfW W.tf tfEpcIdx) (urcV0 V W)) Mp W.fd gn cs pid) (uvisRun W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    urc_skey W V Mp gn cs pid hl hM hpi hsz hcw hgn hch hpid hlz
  exact ⟨h1.symm, h2.symm.trans (uvisRun_arg W 0 (by decide)).symm,
    h3.symm.trans (uvisRun_arg W 1 (by decide)).symm, h4.symm.trans (uvisRun_arg W 2 (by decide)).symm,
    h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm, h11.symm, h12.symm⟩

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FdslotG GF] [BioslotG GF]
    [BcacheG GF] [SleepLockG GF] [DiskG GF] [IcacheG GF] [LogG GF] [FsBlocksG GF] [IregG GF]
    [FsTopG GF] [FsLinkG GF] [IcboxG GF] [OffboxG GF] [OffboxBoxG GF] [IrefslotG GF] [CtokG GF] [WchG GF]
    [Appcfg GF] [FileG GF] [Fscfg] [Icfg]
open UexecSG

/-- **Exit's bundle row is `emp`** at the kernel's deposit instance
(deviation 3). -/
theorem urc_sbundle_exit (X : Uvis → IProp GF) (f : Xfam GF) (W : Uvis) :
    ⊢ @UexecSG.sbundleAt GF _ (uexecSGXv6 (hlc := hlc)) X USYS_exit f W := by
  show ⊢ xv6Sbundle (hlc := hlc) X USYS_exit f W
  unfold xv6Sbundle xv6SbundleRest USYS_exit USYS_exec
  simp only [Int.reduceEq, if_false]
  exact .rfl

/-- **THE SPLIT, AT USERTRAP'S ROWS**: the deposit at the trapped key, moved
onto the record `syscall()` is called with; the ecall arm stays for the
round. -/
theorem urc_deposit (W : Uvis) (V : ProcPriv) (Mp : Nat → List (BitVec 8)) (gn : GName)
    (cs : ExtTreeSet GName compare) (pid : BitVec 32) (sc : BitVec 64) (f : sfam GF)
    (hl : V.tf.length = 36) (hlw : W.tf.length = 36)
    (hM : umemLazy V.upt V.sz.toNat Mp = W.M) (hpi : W.perm = permOf V.upt.um V.sz.toNat)
    (hsz : W.sz = V.sz.toNat) (hcw : W.cwd = V.cwi) (hgn : W.gen = gn) (hch : W.ch = cs)
    (hpid : W.pid = pid) (hlz : W.lazy = V.pvLazy) (hVgn : V.gen = gn) :
    uexecDep (hlc := hlc) sc W f ∗ uexecArm sc W f ⊢
      utSysIn (hlc := hlc) f sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp W.fd gn cs pid ∗
      utForkIn (hlc := hlc) f sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp W.fd ∗
      utPayIn f sc (tfW W.tf tfEpcIdx) (urcV0 V W) ∗
      utKillIn (hlc := hlc) f sc (uvisRun W) gn W.fd ∗
      (if sc = uecallScause then uexecArm sc W f else iprop(emp)) := by
  have hu := urc_proTf_run W V hl
  have hnum : syscNum (utSysRec (tfW W.tf tfEpcIdx) (urcV0 V W)) = usysNum W.tf := urc_num W V hl
  have hkey := urc_skey W V Mp gn cs pid hl hM hpi hsz hcw hgn hch hpid hlz
  have hpay : upayAt W.gen sc W.tf f ⊢ upayAt (urcV0 V W).gen sc (utProTf (tfW W.tf tfEpcIdx) (urcV0 V W)) f :=
    upayAt_ueq sc f ((uvisRun_num W).symm.trans (usysNum_tfUeq hu).symm)
      ((uvisRun_arg W 0 (by decide)).symm.trans (tfUeq_arg 0 (by decide) hu).symm) (hgn.trans hVgn.symm)
  have hkill : (uvisRun W).gen = gn ∧ (uvisRun W).fd = W.fd := ⟨hgn, rfl⟩
  unfold uexecDep uexecDepF uexecPayDep utSysIn utForkIn utPayIn utKillIn syscSysIn syscForkIn
  by_cases hec : sc = uecallScause
  · simp only [if_pos hec]
    by_cases hx : usysNum W.tf = USYS_exit
    · simp only [if_pos hx]
      iintro ⟨⟨Hpay, -⟩, Harm⟩
      ihave Hpay := hpay $$ Hpay
      iframe Hpay Harm
      isplitl []
      · iintro %_ %n %⟨hn, _⟩
        rw [← hn, hnum, hx]
        iapply urc_sbundle_exit
      isplitl []
      · iintro %_ %hf
        exfalso; rw [hnum, hx] at hf; exact absurd hf (by decide)
      isplitl []
      · ipureintro; exact hkill
      · iempintro
    simp only [if_neg hx]
    by_cases hfk : usysNum W.tf = USYS_fork
    · simp only [if_pos hfk]
      iintro ⟨⟨Hpay, Hd⟩, Harm⟩
      ihave Hpay := hpay $$ Hpay
      iframe Hpay Harm
      isplitl []
      · iintro %_ %n %⟨hn, hnf⟩
        exfalso; rw [← hn, hnum] at hnf; exact hnf hfk
      isplitl [Hd]
      · iintro %_ %_
        unfold uexecForkChildF
        icases Hd with ⟨#Hkw, HRc, Hc⟩
        iframe Hkw HRc
        iintro %g' %pidc %hne Hp HRc
        iapply (uslot_keyCong _ _ (urc_child_ukey W V Mp g' pidc hl hlw hM hpi hsz hcw hlz)).mp
        iapply Hc $$ %g' %pidc %hne Hp HRc
      isplitl []
      · ipureintro; exact hkill
      · iempintro
    · simp only [if_neg hfk]
      iintro ⟨⟨Hpay, Hd⟩, Harm⟩
      ihave Hpay := hpay $$ Hpay
      iframe Hpay Harm
      isplitl [Hd]
      · iintro %_ %n %⟨hn, _⟩
        rw [← hn, hnum]
        iapply (sbundleAt_cong uslot (usysNum W.tf) f W _ hkey).mp
        iexact Hd
      isplitl []
      · iintro %_ %hf
        exfalso; rw [hnum] at hf; exact hfk hf
      isplitl []
      · ipureintro; exact hkill
      · iempintro
  · simp only [if_neg hec]
    iintro ⟨⟨Hpay, -⟩, Harm⟩
    ihave Hpay := hpay $$ Hpay
    ihave Harm := (uexecArm_run sc W f hlw).mp $$ Harm
    iframe Hpay
    isplitl []
    · iintro %h; exact absurd h hec
    isplitl []
    · iintro %h; exact absurd h hec
    isplitl [Harm]
    · isplitl []
      · ipureintro; exact hkill
      · rw [← uexecArm_transparent _ _ _ hec]
        iexact Harm
    · iempintro

/-- **Exec's failure arm, at the trapped key** (deviation 2): `-1`, nothing
of the process moved but a0 (up to the kernel words). -/
theorem urc_exec_failed (W : Uvis) (V : ProcPriv) (Mp : Nat → List (BitVec 8)) (V' : ProcPriv)
    (M' : Nat → List (BitVec 8)) (ws : List (BitVec 64)) (sts' : List FdState) (hl : V.tf.length = 36)
    (hM : umemLazy V.upt V.sz.toNat Mp = W.M) (hpi : W.perm = permOf V.upt.um V.sz.toNat)
    (hsz : W.sz = V.sz.toNat) (hlz : W.lazy = V.pvLazy) (hws : tfUeq ws V'.tf)
    (H : syscExecFailed (utSysRec (tfW W.tf tfEpcIdx) (urcV0 V W)) Mp { V' with tf := ws } M' W.fd sts') :
    ∃ r : BitVec 64, uroundBumpOk (uvisRun W).tf V'.tf r ∧
      usysMemOk USYS_exec (uvisRun W).tf r W.M W.perm W.sz W.lazy (umemLazy V'.upt V'.sz.toNat M')
        (permOf V'.upt.um V'.sz.toNat) V'.sz.toNat V'.pvLazy ∧ sts' = W.fd := by
  obtain ⟨htf, himg, hperm, hsz', hlz', hsts⟩ := H
  have hu := urc_proTf_run W V hl
  have hl0 := urcV0_len V W hl
  have hlp : (utProTf (tfW W.tf tfEpcIdx) (urcV0 V W)).length = 36 := by
    unfold utProTf; rw [List.length_set]; exact hl0
  have hws' : ws = bumpTf (utProTf (tfW W.tf tfEpcIdx) (urcV0 V W)) (-1#64) := by
    rw [show ws = ({ V' with tf := ws } : ProcPriv).tf from rfl, htf]
    exact urc_sysTf_bump _ _ _ hl0
  refine ⟨-1#64, ⟨?_, ?_⟩, ?_, hsts⟩
  · rw [← tfUeq_resumeGpr0 hws, hws', tfResumeGpr0_bump _ _ (by rw [hlp]; decide), tfUeq_resumeGpr0 hu]
  · rw [← tfResumePc_tfUeq hws, hws', tfResumePc_bump _ _ (by rw [hlp]; decide), tfUeq_epc hu]
  · unfold usysMemOk
    rw [if_pos rfl]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · exact himg.trans hM
    · exact hperm.trans hpi.symm
    · show V'.sz.toNat = W.sz
      rw [hsz]; exact congrArg BitVec.toNat hsz'
    · show V'.pvLazy = W.lazy
      rw [hlz]; exact hlz'

set_option maxHeartbeats 1000000 in
/-- **STEPS A/B, AT USERTRAP'S ROWS**: the round's answers, read at the
trapped key's run projection, pay the slot at the record the round left. -/
theorem urc_post (W : Uvis) (V : ProcPriv) (Mp : Nat → List (BitVec 8)) (gn : GName)
    (cs : ExtTreeSet GName compare) (pid : BitVec 32) (sc : BitVec 64) (f : sfam GF)
    (V' : ProcPriv) (M' : Nat → List (BitVec 8)) (sts' : List FdState) (cs' : ExtTreeSet GName compare)
    (hl : V.tf.length = 36) (hlw : W.tf.length = 36)
    (hM : umemLazy V.upt V.sz.toNat Mp = W.M) (hpi : W.perm = permOf V.upt.um V.sz.toNat)
    (hsz : W.sz = V.sz.toNat) (hcw : W.cwd = V.cwi) (hgn : W.gen = gn) (hch : W.ch = cs)
    (hpid : W.pid = pid) (hlz : W.lazy = V.pvLazy)
    (hround : utRound (tfW W.tf tfEpcIdx) sc (urcV0 V W) Mp V' M')
    (hfdk : utFdKept sc W.fd sts') (hchk : utChKept sc (urcV0 V W).tf cs cs')
    (hfde : utFdEcall sc (urcV0 V W).tf V'.tf W.fd sts')
    (hpipe : utPipeEcall sc (urcV0 V W).tf V'.tf (syscImg (urcV0 V W) Mp) (syscImg V' M') W.fd sts')
    (hrp : utRetPid sc (urcV0 V W).tf V'.tf pid)
    (hlive : utLiveOut sc (utProTf (tfW W.tf tfEpcIdx) (urcV0 V W)) W.fd (tfW V'.tf (tfArgIdx 0)) cs') :
    utExecOut (hlc := hlc) sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp V' M' W.fd sts' gn cs pid ∗
    utForkOut f sc (tfW W.tf tfEpcIdx) (urcV0 V W) (tfW V'.tf (tfArgIdx 0)) cs cs' ∗
    utWaitOut (GF := GF) sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp (syscImg V' M') (tfW V'.tf (tfArgIdx 0)) cs cs' pid ∗
    utKillOut (hlc := hlc) sc (uvisRun W) ∗
    utSysOut (hlc := hlc) f sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp W.fd gn cs pid (tfW V'.tf (tfArgIdx 0))
      (syscImg V' M') sts' V'.cwi cs' ∗
    (if sc = uecallScause then uexecArm sc W f else iprop(emp))
    ⊢ uslot (hlc := hlc) (uvisOf V' M' sts' gn cs' pid) := by
  have hu := urc_proTf_run W V hl
  have hnum : syscNum (utSysRec (tfW W.tf tfEpcIdx) (urcV0 V W)) = usysNum W.tf := urc_num W V hl
  have hnum0 : usysNum (urcV0 V W).tf = usysNum (uvisRun W).tf :=
    (urc_num_entry W V hl).trans (uvisRun_num W).symm
  have ha0 : tfW (urcV0 V W).tf (tfArgIdx 0) = tfW (uvisRun W).tf (tfArgIdx 0) := by
    have h1 : tfW (utSysTf (tfW W.tf tfEpcIdx) (urcV0 V W)) (tfArgIdx 0) = tfW (urcV0 V W).tf (tfArgIdx 0) := by
      unfold utSysTf; exact tfW_set_ne _ _ _ _ (by decide)
    rw [← h1, urc_sysTf_arg W V hl 0 (by decide), uvisRun_arg W 0 (by decide)]
  have hrun : (uvisRun W).tf = tfOf (tfResumeGpr0 W.tf) (retPc (tfW W.tf tfEpcIdx)) := rfl
  have hkeyr := urc_skey_run W V Mp gn cs pid hl hM hpi hsz hcw hgn hch hpid hlz
  -- the pure rows, at the run projection
  have hr : uroundOk sc (uvisRun W).tf W.M W.perm W.sz W.cwd W.lazy V'.tf (umemLazy V'.upt V'.sz.toNat M')
      (permOf V'.upt.um V'.sz.toNat) V'.sz.toNat V'.cwi V'.pvLazy := by
    have h : uroundOk sc (uvisRun W).tf (umemLazy V.upt V.sz.toNat Mp) (permOf V.upt.um V.sz.toNat) V.sz.toNat
        V.cwi V.pvLazy V'.tf (umemLazy V'.upt V'.sz.toNat M') (permOf V'.upt.um V'.sz.toNat) V'.sz.toNat V'.cwi
        V'.pvLazy := uroundOk_ueq_l hu hround
    rw [hM, ← hpi, ← hsz, ← hcw, ← hlz] at h
    exact h
  have hfd : sc ≠ uecallScause → sts' = W.fd := hfdk
  have hchrow : ¬ (sc = uecallScause ∧ (usysNum (uvisRun W).tf = USYS_fork ∨
      usysNum (uvisRun W).tf = USYS_wait)) → cs' = W.ch := by
    intro h; rw [hchk (by rw [hnum0]; exact h), hch]
  have hfdrow : sc = uecallScause →
      usysFdOk (usysNum (uvisRun W).tf) (uvisRun W).tf (tfW V'.tf (tfArgIdx 0)) W.fd sts' := by
    intro h; rw [← hnum0]; exact usysFdOk_argCong ha0 (hfde h)
  have hpiperow : sc = uecallScause →
      usysPipeOk (usysNum (uvisRun W).tf) (uvisRun W).tf (tfW V'.tf (tfArgIdx 0)) W.M
        (umemLazy V'.upt V'.sz.toNat M') W.fd sts' := by
    intro h; rw [← hnum0, ← hM]; exact usysPipeOk_argCong ha0 (hpipe h)
  have hpidrow : sc = uecallScause → usysRetPid (usysNum (uvisRun W).tf) (tfW V'.tf (tfArgIdx 0)) W.pid := by
    intro h; rw [← hnum0, hpid]; exact hrp h
  have hliverow : sc = uecallScause →
      uexecLiveOk (usysNum (uvisRun W).tf) (uvisRun W).tf W.fd (tfW V'.tf (tfArgIdx 0)) cs' := by
    intro h
    have hn : usysNum (utProTf (tfW W.tf tfEpcIdx) (urcV0 V W)) = usysNum (uvisRun W).tf := usysNum_tfUeq hu
    rw [← hn]
    exact uexecLiveOk_cong (tfUeq_arg 0 (by decide) hu) (tfUeq_arg 2 (by decide) hu) (hlive h)
  have HR := uexecRet_roundSlot_of sc W f (tfResumeGpr0 W.tf) (tfW W.tf tfEpcIdx) V' M' sts' cs' hlw rfl rfl
    hfd hchrow hfdrow hpiperow hpidrow hliverow hr
  rw [hgn, hpid, ← hrun] at HR
  have hx1 : utExecOut (hlc := hlc) (GF := GF) sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp V' M' W.fd sts' gn cs pid ⊢
      ⌜sc = uecallScause ∧ usysNum (uvisRun W).tf = USYS_exec⌝ -∗
        (⌜∃ r : BitVec 64, uroundBumpOk (uvisRun W).tf V'.tf r ∧
            usysMemOk USYS_exec (uvisRun W).tf r W.M W.perm W.sz W.lazy (umemLazy V'.upt V'.sz.toNat M')
              (permOf V'.upt.um V'.sz.toNat) V'.sz.toNat V'.pvLazy ∧ sts' = W.fd⌝ ∨
          uslot (hlc := hlc) (uvisOf V' M' sts' gn cs' pid)) := by
    unfold utExecOut syscExecOut
    iintro Hxo %⟨hec, hx⟩
    ispecialize Hxo $$ %hec
    icases Hxo with ⟨%ws, %hws, Hxo⟩
    ispecialize Hxo $$ %(hnum.trans ((uvisRun_num W).symm.trans hx))
    icases Hxo with (%hfail | Hs)
    · ileft; ipureintro
      exact urc_exec_failed W V Mp V' M' ws sts' hl hM hpi hsz hlz hws hfail
    · iright
      have hcs : cs' = cs := hchk (fun h => by
        rcases h.2 with h2 | h2 <;> rw [hnum0, hx] at h2 <;> exact absurd h2 (by decide))
      iapply (uslot_key_cong (W := uvisOf { V' with tf := ws } M' sts' gn cs pid)
        (W' := uvisOf V' M' sts' gn cs' pid) (tfUeq_resumeGpr0 hws) (tfResumePc_tfUeq hws) rfl rfl rfl rfl rfl
        rfl (show cs = cs' from hcs.symm) rfl rfl).mp
      iexact Hs
  have hx2 : utForkOut f sc (tfW W.tf tfEpcIdx) (urcV0 V W) (tfW V'.tf (tfArgIdx 0)) cs cs' ⊢
      ⌜sc = uecallScause ∧ usysNum (uvisRun W).tf = USYS_fork⌝ -∗
        uforkAns (sforkPay f) (sforkLend f) (tfW V'.tf (tfArgIdx 0)) W.ch cs' := by
    unfold utForkOut syscForkOut
    iintro Hfo %⟨hec, hfk⟩
    ispecialize Hfo $$ %hec
    ispecialize Hfo $$ %(hnum.trans ((uvisRun_num W).symm.trans hfk))
    rw [hch]
    iexact Hfo
  have hx3 : utWaitOut (GF := GF) sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp (syscImg V' M') (tfW V'.tf (tfArgIdx 0))
      cs cs' pid ⊢
      ⌜sc = uecallScause ∧ usysNum (uvisRun W).tf = USYS_wait⌝ -∗
        uwaitAnsPid (tfW V'.tf (tfArgIdx 0)) W.ch cs' pid := by
    unfold utWaitOut syscWaitOut syscUwaitAnsAtM uwaitAnsPid uwaitAnsAt
    iintro Hwo %⟨hec, hwt⟩
    ispecialize Hwo $$ %hec
    ispecialize Hwo $$ %(hnum.trans ((uvisRun_num W).symm.trans hwt))
    icases Hwo with ⟨%rv, %xw, %hr0, -, Ha⟩
    rw [hch]
    iexists _, _, rv, _
    iframe Ha
    ipureintro; exact hr0
  have hx4 : utSysOut (hlc := hlc) f sc (tfW W.tf tfEpcIdx) (urcV0 V W) Mp W.fd gn cs pid (tfW V'.tf (tfArgIdx 0))
      (syscImg V' M') sts' V'.cwi cs' ⊢
      ⌜sc = uecallScause ∧ usysNum (uvisRun W).tf ≠ USYS_exit ∧ usysNum (uvisRun W).tf ≠ USYS_fork⌝ -∗
        spostAt uslot (usysNum (uvisRun W).tf) f (uvisRun W) (tfW V'.tf (tfArgIdx 0))
          (umemLazy V'.upt V'.sz.toNat M') sts' V'.cwi cs' := by
    unfold utSysOut syscSysOut
    iintro Hso %⟨hec, hnx, hnf⟩
    ispecialize Hso $$ %hec
    ispecialize Hso $$ %(usysNum (uvisRun W).tf) %⟨hnum.trans (uvisRun_num W).symm, hnx, hnf⟩
    iapply (spostAt_cong uslot _ f _ _ _ _ _ _ _ hkeyr).mp
    iexact Hso
  have hx5 : utKillOut (hlc := hlc) sc (uvisRun W) ∗
      (if sc = uecallScause then uexecArm sc W f else iprop(emp)) ⊢
      (if sc = uecallScause then uexecArm sc W f else uslot (uvisRun W)) := by
    unfold utKillOut
    by_cases hec : sc = uecallScause
    · simp only [if_pos hec]
      iintro ⟨-, H⟩
      iexact H
    · simp only [if_neg hec]
      iintro ⟨H, -⟩
      iexact H
  iintro ⟨Hxo, Hfo, Hwo, Hko, Hso, Harm⟩
  ihave Hxo := hx1 $$ Hxo
  ihave Hfo := hx2 $$ Hfo
  ihave Hwo := hx3 $$ Hwo
  ihave Hso := hx4 $$ Hso
  ihave Harm := hx5 $$ [Hko Harm]
  · iframe Hko Harm
  iapply HR $$ Hxo Hfo Hwo Hso Harm

end

end Xv6
