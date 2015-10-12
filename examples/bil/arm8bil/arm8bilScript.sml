(* ========================================================================= *)
(* FILE          : arm8bilScript.sml                                         *)
(* DESCRIPTION   : A transcompiler from arm8model to BIL model.              *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;
open wordsTheory;
open bilTheory;

val _ = new_theory "arm8bil";
(* ------------------------------------------------------------------------- *)

(* This is to overload the combination not-equal, in order to have easier conversions to NotEqual in BIL model *)
val word_neq_def = Define `word_neq (a:α word) (b:α word) = ~(a = b)`;
val _ = overload_on ("≠",              Term`$word_neq`);

(* ------------------------------------------------------------------------- *)
(*  ARMv8 State - BIL State Bisimulation                                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
val _ = export_theory();
