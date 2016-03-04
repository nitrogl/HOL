HOL_Interactive.toggle_quietdec();
open HolKernel boolLib bossLib Parse;
open lcsymtacs utilsLib;
open wordsLib blastLib;
open state_transformerTheory updateTheory arm8Theory;
open stateTheory;
open lcsymtacs arm8_stepTheory;
open state_transformerSyntax;
open arm8_stepLib;
open proofTools arithTheory;
open bilTheory arm8bilTheory;
open arm8bilLib;
HOL_Interactive.toggle_quietdec();

val [[t]] = arm8_step_code `MOV X0, #1`;

val s2 = (optionLib.dest_some o snd o dest_eq o concl) t;
extract_arm8_changes s2;

val mainPath = "../l3-machine-code/arm8/model/";
(* Load path *)
loadPath := mainPath :: !loadPath;
open arm8AssemblerLib;

arm8_step_code `MOV X0, #1`;
val code = arm8AssemblerLib.arm8_code `MOV X0, #1`;
val instr = (hd code);

val (p, certs, [step]) = tc_stmt_arm8_hex instr;


val prog = ``
(^(list_mk_conj (hyp step))) ==>
(
 (env "" = (NoType,Unknown)) /\
 ((env "R0") = (Reg Bit64, Int (Reg64 (s.REG 0w))))
) ==>
(NextStateARM8 s = SOME s1) ==>
(bil_exec_step <|
  pco:= SOME <| label:= (Label "main"); index:= 0 |>;
  environ:= env ;
  termcode:= Unknown ;
  debug:=d1;
  execs:=e1;
  pi:=[
    <| label:= Label "main";
       statements:= [
         Assign "R0" (Const (Reg64 1w))
       ]|>
  ]|> = bs1) ==>
(
 (bs1.environ "" = (NoType,Unknown)) /\
 ((bs1.environ "R0") = (Reg Bit64, Int (Reg64 (s1.REG 0w))))
)``;

prove(``^prog``,
      (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``])
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (ASSUME_TAC (List.nth (certs, 0)))
      THEN (ASSUME_TAC (List.nth (certs, 1)))
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      (* for regular *)
      THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``])
      (* computation completed *)
      THEN DISCH_TAC
      (* use the step theorem *)
      THEN (ASSUME_TAC step)
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def])
);


val (p, certs, [step]) = tc_stmt_arm8_hex instr;


val prog = ``
(^(list_mk_conj (hyp step))) ==>
(
 (env "" = (NoType,Unknown)) /\
 ((env "R0") = (Reg Bit64, Int (Reg64 (s.REG 0w)))) /\
 ((env "arm8_state_PC") = (Reg Bit64, Int (Reg64 (s.PC)))) /\
 (?v.((env "tmp_R0") = (Reg Bit64, Int (Reg64 (v))))) /\
 (?v.((env "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v)))))
) ==>
(NextStateARM8 s = SOME s1) ==>
(bil_exec_step_n <|
  pco:= SOME <| label:= (Label "main"); index:= 0 |>;
  environ:= env ;
  termcode:= Unknown ;
  debug:=d1;
  execs:=e1;
  pi:=[<| label:= Label "main";
          statements:= ^p|>]
  |> 4 = bs1) ==>
(
 (bs1.environ "" = (NoType,Unknown)) /\
 ((bs1.environ "R0") = (Reg Bit64, Int (Reg64 (s1.REG 0w)))) /\
 ((bs1.environ "arm8_state_PC") = (Reg Bit64, Int (Reg64 (s1.PC)))) /\
 (?v.((bs1.environ "tmp_R0") = (Reg Bit64, Int (Reg64 (v))))) /\
 (?v.((bs1.environ "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v)))))
)``;

val (_,_,tmpt1) = tc_exp_arm8 ``s.REG 0w``;
val tmpt1 = SIMP_RULE (srw_ss()) [r2s_def] tmpt1;

val (_,_,tmpt2) = tc_exp_arm8 ``s.PC``;


fun ABBREV_NEW_ENV n (asl, g) =
    let val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
	val (x,_) = dest_imp g
	val (s,_) = dest_eq x
	val (f, [s,n]) = strip_comb s
	val nenv = (snd o dest_eq o concl o EVAL) ``^s.environ``
       in
	   (Q.ABBREV_TAC `^var_name=^nenv`) (asl,g)
    end;
	

prove(``^prog``,
      (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
      THEN (FULL_SIMP_TAC (srw_ss()) [])

      (* First instruction *)
      THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (ASSUME_TAC (SPEC ``s:arm8_state`` (SPEC_ENV (tmpt1))))
      THEN (REV_FULL_SIMP_TAC (srw_ss()) [])
      THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      (* Second instruction *)
      THEN (ABBREV_NEW_ENV 1)
      THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (FULL_SIMP_TAC (srw_ss()) [Abbr `env1`])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_exec_step_n``])
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      (* Third instruction *)
      THEN (ABBREV_NEW_ENV 2)
      THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (ASSUME_TAC (SPECL [``env2:environment``, ``s:arm8_state``] (tmpt2)))
      THEN (ASSUME_TAC (SPECL [``env2:environment``, ``s:arm8_state``] (List.nth (certs, 1))))
      THEN (REV_FULL_SIMP_TAC (srw_ss()) [Abbr `env2`])
      THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      (* Forth instruction *)
      THEN (ABBREV_NEW_ENV 3)
      THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (ASSUME_TAC (SPECL [``env3:environment``, ``s:arm8_state``] (List.nth (certs, 0))))
      THEN (FULL_SIMP_TAC (srw_ss()) [Abbr `env3`])
      THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
      THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])

      (* Computation completed *)
      THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
      THEN DISCH_TAC
      (* use the step theorem *)
      THEN (ASSUME_TAC step)
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def])
);
