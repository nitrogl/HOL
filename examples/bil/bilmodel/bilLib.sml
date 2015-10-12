(* ========================================================================= *)
(* FILE          : bilScript.sml                                             *)
(* DESCRIPTION   : A model of BAP Intermediate Language.                     *)
(*                 Based on Antony's Fox binary words treatment.             *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

structure bilLib :> bilLib =
struct

open bilTheory;
open blastLib;

(* Get term with initial state of a program *)
fun bil_state_init p = (snd o dest_eq o concl o EVAL) ``bil_state_init ^p``;

(* Executing just one step of the program, let's retrieve the updated state (pc + environment) *)
fun bil_state_step_update p s = (snd o dest_eq o concl o EVAL) ``bil_exec_step ^p ^s``;

(*

Execute a program.
As it is not possible to say if any program will terminate or not,
also a maximum number of iterations must be passed as argument.
The program might stop its execution before the maximum number of iterations
is reached for several reasons: not (yet) terminating, errors, ...

*)
val bil_exec_program_noevalenv = fn (p, maxiter) =>
let
  val rec bil_exec_program_noevalenv' = fn(p, state, maxiter, i) =>
    if (i >= maxiter)
    then (i, state)
    else
      let
        val new_state = bil_state_step_update p state
        val pco = snd (dest_eq (concl (EVAL ``bil_stepstate_pco ^new_state``)))
      in
        if (pco = ``NONE:programcounter option``)
        then (i, new_state)
        else bil_exec_program_noevalenv'(p, new_state, maxiter, i + 1)
      end
in
  bil_exec_program_noevalenv'(p, bil_state_init p, maxiter, 0)
end;

fun eval_update s = (snd o dest_eq o concl) (SIMP_CONV (srw_ss()) [combinTheory.UPDATE_def] ``^s``);
fun bil_state_step_update_eval p s = eval_update (bil_state_step_update p s);

val bil_exec_program = fn (p, maxiter) =>
let
  val (i, ss) = bil_exec_program_noevalenv(p, maxiter)
in
  (i, eval_update ss)
end;

(* ------------------------------------------------------------------------- *)
end