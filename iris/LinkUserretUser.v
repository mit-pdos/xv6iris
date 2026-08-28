(* LinkUserretUser.v -- instantiates the userret -> user-execution dovetail
   (UserretUser.v) against the real sealed userret trampoline proof
   (LinkUserret).  This is the machine-checked statement that userret's
   postcondition feeds the user-execution WP SLOT ([UexecWp.uexec_wp]) with
   nothing missing.  The dovetail no longer names [USER]: the WP to run is a
   PREMISE it takes (claude-notes/projects/user-wp-slot.md), so there is no
   second functor argument to link here. *)
Require Import LinkUserret UserretUser.

Module UserretUserD := UserretUser Userret.
