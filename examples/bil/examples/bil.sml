val mainPath = "../bilmodel";

(* Load path *)
loadPath := mainPath :: !loadPath;

open bilTheory;

(* This is an BIL value of 8bit *)
val x = ``Reg8 0x1w``;
(* The BIL integer values are :bil_int_t *)
type_of x;

(* The BIL integer expression also of HOL4 type :bil_int_t *)
val z = ``(Reg8 0x1w) + (Reg8 0x3w)``;
type_of z;

(* To evaluate an expression we need an :environment *)
(* and we obtain a :bil_val_t *)
val a = ``bil_eval_exp (Plus (Const (Reg8 0x1w)) (Const ((Reg8 0x1w))))``;
type_of a;


(* We evaluare an expression with a free environment since we do not have variables *)
(* Here we prove that bil_eval 1+3 = 4 :) *)
val a = ``bil_eval_exp (Plus (Const (Reg8 0x1w)) (Const ((Reg8 0x3w)))) e``;
type_of a;
val t1 = (SIMP_CONV (srw_ss()) [Once bil_eval_exp_def] a);

val le = (SIMP_CONV (srw_ss()) [Once bil_eval_exp_def] ``bil_eval_exp (Const (Reg8 1w)) e``);
val re = (SIMP_CONV (srw_ss()) [Once bil_eval_exp_def] ``bil_eval_exp (Const (Reg8 3w)) e``);

val t2 = (SIMP_RULE (bool_ss) [le] t1);
val t3 = (SIMP_RULE (bool_ss) [re] t2);

val t2 = (SIMP_RULE (srw_ss()) [le, re] t1);

val t3 = (SIMP_RULE (srw_ss()) [bil_add_def] t2);

(* If we include all the HOL4 theory needed we can simplify the HOL4 *)
(* word expressions *)
open wordsTheory;
open wordsLib;
open arithmeticTheory;
open numTheory;
val t3 = (SIMP_RULE (srw_ss()) [bil_add_def] t2);

(* We can generalize this theorem, since this hold for all possible environment *)
val t4 = GEN ``e:environment`` t3;

(* We can obtain the same theorem using backward proof *)
(* that is bil_Eval 3+1 = 4 *)
val t5 = prove(``∀e. bil_eval_exp (Plus (Const (Reg8 1w)) (Const (Reg8 3w))) e = Int (Reg8 4w)``,
     GEN_TAC
     THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
     THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
     THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
     THEN (SIMP_TAC (srw_ss()) [bil_add_def])
);

(* If we have variables, we need some assumption on the environment *)
val t5 = prove(``∀e. 
(
 (((e:environment) "var") = (Reg Bit8, (Int (Reg8 3w)))) /\
 (((e:environment) "var1") = (Reg Bit8, (Int (Reg8 7w))))
) ==>
(bil_eval_exp (Plus (Const (Reg8 1w)) (Den "var")) e = Int (Reg8 4w))
``,
     GEN_TAC
THEN (DISCH_TAC)
THEN (FULL_SIMP_TAC (srw_ss()) [])
THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def, bil_env_read_def])
THEN (FULL_SIMP_TAC (srw_ss()) [])
THEN (SIMP_TAC (srw_ss()) [bil_add_def])
);

(* Sometime we are lucky and we can just use EVAL :) *)
EVAL ``bil_eval_exp (Plus (Const (Reg8 0x1w)) (Const ((Reg8 0x3w)))) e``;

val t5 = prove(``∀e. 
(
 (((e:environment) "var") = (Reg Bit8, (Int (Reg8 3w)))) /\
 (((e:environment) "var1") = (Reg Bit8, (Int (Reg8 7w))))
) ==>
(bil_eval_exp (Plus (Const (Reg8 1w)) (Den "var")) e = Int (Reg8 4w))
``,
     REPEAT (STRIP_TAC)
THEN (EVAL_TAC)
THEN (FULL_SIMP_TAC (srw_ss()) [])
);

(* Execution of a program that declares a variable *)
open listTheory;
open listLib;

val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "var" (Reg Bit8))
    ]
    |>;
 b
]:program
``;
val state = ``<|
  pco:= SOME <| label:= (Label "main"); index:= 0 |>;
  environ:= (\v. (NoType,Unknown)) ;
  termcode:= Unknown ;
  debug:=d1;
  execs:=e1;
  pi:=^x
|>``;

val t1 = (SIMP_CONV (srw_ss()) [Once bil_exec_step_def] ``bil_exec_step ^state``);
val t2 = (SIMP_RULE (srw_ss()) [bil_get_program_block_info_by_label_def] t1);
val t4 = (SIMP_RULE (srw_ss()) [listTheory.INDEX_FIND_def,
                       listTheory.EL,
                       listTheory.HD,
                       Ntimes LET_DEF 5,
                       combinTheory.UPDATE_def] t2);
val t5 = (SIMP_RULE (srw_ss()) [bil_exec_stmt_def, is_env_regular_def] t4);
val t6 = (SIMP_RULE (srw_ss()) [combinTheory.UPDATE_def] t5);
val t7 = (SIMP_RULE (srw_ss()) [bil_pcnext_def, bil_get_program_block_info_by_label_def] t6);
val t8 = (SIMP_RULE (srw_ss()) [listTheory.INDEX_FIND_def,
                       listTheory.EL,
                       listTheory.HD,
                       Ntimes LET_DEF 5,
                       combinTheory.UPDATE_def] t7);

open bilLib;
EVAL ``bil_exec_step ^state``;

(* A program that declares a variable and assign it *)
val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "var" (Reg Bit8));
      Assign  "var" (Const (Reg8 1w))
    ]
    |>;
 b
]:program
``;
val state = ``<|
  pco:= SOME <| label:= (Label "main"); index:= 0 |>;
  environ:= (\v. (NoType,Unknown)) ;
  termcode:= Unknown ;
  debug:=d1;
  execs:=e1;
  pi:=^x
|>``;

EVAL ``bil_exec_step (bil_exec_step ^state)``;

(* A program that declares two variable and assign them *)
val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "var" (Reg Bit8));
      Assign  "var" (Const (Reg8 1w));
      Declare (Var "var1" (Reg Bit8));
      Assign  "var1" (Plus (Const (Reg8 1w)) (Den "var"))
    ]
    |>;
 b
]:program
``;
val state = ``<|
  pco:= SOME <| label:= (Label "main"); index:= 0 |>;
  environ:= (\v. (NoType,Unknown)) ;
  termcode:= Unknown ;
  debug:=d1;
  execs:=e1;
  pi:=^x
|>``;

val v = snd(dest_eq (concl (EVAL ``bil_exec_step(bil_exec_step (bil_exec_step ^state))``)));
EVAL ``bil_exec_step ^v``;


(* TODO *)
(* JUMP *)
(* MEMORY *)
(* CONDITIONAL JUMP *)
