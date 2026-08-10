From Corelib Require Import PrimString.
From Stdlib Require Import String.

Definition p1 : PrimString.string := "H"%pstring.
Definition p2 : PrimString.string := "Hx"%pstring.
Definition p4 : PrimString.string := "Hfoo"%pstring.
Definition p8 : PrimString.string := "Hi_csrws"%pstring.
Definition p10 : PrimString.string := "Hi_csrw_ss"%pstring.
Definition p16 : PrimString.string := "Hi_csrw_sscratc"%pstring.
Definition p31 : PrimString.string := "Hi_csrw_sscratch_trapframe_slo"%pstring.
Definition s1 : String.string := "H"%string.
Definition s2 : String.string := "Hx"%string.
Definition s4 : String.string := "Hfoo"%string.
Definition s8 : String.string := "Hi_csrws"%string.
Definition s10 : String.string := "Hi_csrw_ss"%string.
Definition s16 : String.string := "Hi_csrw_sscratc"%string.
Definition s31 : String.string := "Hi_csrw_sscratch_trapframe_slo"%string.
