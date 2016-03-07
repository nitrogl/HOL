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
val a = ``Plus (Const (Reg8 0x1w)) (Const ((Reg8 0x1w)))``;
type_of a;
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

EVAL ``bil_exec_step ^state``;
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


val t1 = EVAL ``bil_exec_step(bil_exec_step (bil_exec_step ^state))``;
val tm1 = concl (EVAL ``bil_exec_step(bil_exec_step (bil_exec_step ^state))``);
val v = snd (dest_eq tm1);
EVAL ``bil_exec_step ^v``;

EVAL ``bil_exec_step (bil_exec_step (bil_exec_step( bil_exec_step ^state)))``;


(* JUMP: A program that declares two variable and assign them *)
val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "var" (Reg Bit8));
      Assign  "var" (Const (Reg8 1w));
      Jmp (Label "jumpto");
      Declare abc
    ]
    |>;
 <| label:= Label "jumpto";
    statements:= [
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

EVAL ``bil_exec_step (bil_exec_step (bil_exec_step (bil_exec_step (bil_exec_step ^state))))``;





(* TODO *)
(* MEMORY *)
val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "mem" (MemByte Bit64));
      Assign "mem" (Store (Den "mem") (Const (Reg64 5w)) (Const (Reg8 7w)) x Bit8)
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

val s = state;
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));


val t1 = (SIMP_CONV (srw_ss()) [Once bil_exec_step_def] ``bil_exec_step ^s``);
val t2 = (SIMP_RULE (srw_ss()) [bil_get_program_block_info_by_label_def] t1);
val t4 = (SIMP_RULE (srw_ss()) [listTheory.INDEX_FIND_def,
                       listTheory.EL,
                       listTheory.HD,
                       Ntimes LET_DEF 5,
                       combinTheory.UPDATE_def] t2);

val t5 = (SIMP_RULE (srw_ss()) [bil_exec_stmt_def] t4);
val t6 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def,
                       bil_sizeof_reg_def,
                       Ntimes LET_DEF 1,
                       bil_not_def, bil_eq_def] t5);
val t7 = (SIMP_RULE (srw_ss()) [n2b_8_def, n2bs_def] t6);

val t8 = (SIMP_RULE (srw_ss()) [LET_DEF] t7);
val t9 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t8);
val t10 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t9);
val t11 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def,  bil_env_read_def] t10);


val t12 = (SIMP_RULE (srw_ss()) [
ASSUME ``bil_eval_exp x (λc.
                  if "mem" = c then
                    (MemByte Bit64,Mem Bit64 (λx. Reg8 0w))
                  else (NoType,Unknown)) = Int y``] t11);

val t13 = (SIMP_RULE (srw_ss()) [bil_regtype_int_inf_def] t12);

val t14 = (SIMP_RULE (srw_ss()) [combinTheory.UPDATE_def,
				 is_env_regular_def] t13);

val t15 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def,
                       bil_sizeof_reg_def,
                       Ntimes LET_DEF 1,
                       bil_not_def, bil_eq_def] t14);
val t16 = (SIMP_RULE (srw_ss()) [n2b_8_def, n2bs_def] t15);

val t17 = (SIMP_RULE (srw_ss()) [LET_DEF] t16);
val t18 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t17);
val t19 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t18);
val t20 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def, bil_env_read_def] t19);

val t21 = (SIMP_RULE (srw_ss()) [
ASSUME ``bil_eval_exp x (λc.
                  if "mem" = c then
                    (MemByte Bit64,Mem Bit64 (λx. Reg8 0w))
                  else (NoType,Unknown)) = Int y``] t20);

val t22 = (SIMP_RULE (srw_ss()) [bil_regtype_int_inf_def] t21);

(* MEMORY 2 *)

val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "mem" (MemByte Bit64));
      Assign "mem" (Store (Den "mem") (Const (Reg64 5w)) (Const (Reg8 7w)) (Const (Reg8 1w)) Bit8)
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

val s = state;
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));


val t1 = (SIMP_CONV (srw_ss()) [Once bil_exec_step_def] ``bil_exec_step ^s``);
val t2 = (SIMP_RULE (srw_ss()) [bil_get_program_block_info_by_label_def] t1);
val t4 = (SIMP_RULE (srw_ss()) [listTheory.INDEX_FIND_def,
                       listTheory.EL,
                       listTheory.HD,
                       Ntimes LET_DEF 5,
                       combinTheory.UPDATE_def] t2);

val t5 = (SIMP_RULE (srw_ss()) [bil_exec_stmt_def] t4);
val t6 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def,
                       bil_sizeof_reg_def,
                       Ntimes LET_DEF 1,
                       bil_not_def, bil_eq_def] t5);
val t7 = (SIMP_RULE (srw_ss()) [n2b_8_def, n2bs_def] t6);

val t8 = (SIMP_RULE (srw_ss()) [LET_DEF] t7);
val t9 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t8);
val t10 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t9);
val t11 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def,  bil_env_read_def] t10);


val t12 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t11);

val t13 = (SIMP_RULE (srw_ss()) [bil_regtype_int_inf_def] t12);

val t14 = (SIMP_RULE (srw_ss()) [combinTheory.UPDATE_def,
				 is_env_regular_def] t13);

val t15 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def,
                       bil_sizeof_reg_def,
                       Ntimes LET_DEF 1,
                       bil_not_def, bil_eq_def] t14);
val t16 = (SIMP_RULE (srw_ss()) [n2b_8_def, n2bs_def] t15);

val t17 = (SIMP_RULE (srw_ss()) [LET_DEF] t16);
val t18 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t17);
val t19 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t18);
val t20 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def, bil_env_read_def] t19);

val t21 = (SIMP_RULE (srw_ss()) [Once bil_eval_exp_def] t20);


val t22 = (SIMP_RULE (srw_ss()) [bil_regtype_int_inf_def] t21);

val s = state;
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));

(* MEMORY READ *)

val x = ``[
 <| label:= Label "main";
    statements:= [
      Declare (Var "mem" (MemByte Bit64));
      Assign "mem" (Store (Den "mem") (Const (Reg64 5w)) (Const (Reg8 7w)) (Const (Reg8 1w)) Bit8);
      Declare (Var "var" (Reg Bit8));
      Assign  "var" (Load (Den "mem") (Const (Reg64 5w)) (Const (Reg8 1w)) Bit8)
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

val s = state;
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));
val s = snd(dest_eq(concl(EVAL ``bil_exec_step ^s``)));





(* CONDITIONAL JUMP *)
