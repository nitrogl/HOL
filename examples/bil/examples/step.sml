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


(* Try to generate certificates for every expressions (inclusing the temporary variables) *)

arm8_step_code `MOV X0, #1`;
val code = arm8AssemblerLib.arm8_code `MOV X0, #1`;
val instr = (hd code);

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
  |> ^((numSyntax.term_of_int o List.length) certs) = bs1) ==>
(
 (bs1.environ "" = (NoType,Unknown)) /\
 ((bs1.environ "R0") = (Reg Bit64, Int (Reg64 (s1.REG 0w)))) /\
 ((bs1.environ "arm8_state_PC") = (Reg Bit64, Int (Reg64 (s1.PC)))) /\
 (?v.((bs1.environ "tmp_R0") = (Reg Bit64, Int (Reg64 (v))))) /\
 (?v.((bs1.environ "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v)))))
)``;


fun ABBREV_NEW_ENV n (asl, g) =
    let val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
	val (x,_) = dest_imp g
	val (s,_) = dest_eq x
	val (f, [s,n]) = strip_comb s
	val nenv = (snd o dest_eq o concl o EVAL) ``^s.environ``
       in
	   (Q.ABBREV_TAC `^var_name=^nenv`) (asl,g)
    end;

fun PROCESS_ONE_ASSIGNMENT n =
    let val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
    in
	(ABBREV_NEW_ENV n)
	THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
	THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])
	THEN (FULL_SIMP_TAC (srw_ss()) [])
	THEN (ASSUME_TAC (SPECL [``^var_name``, ``s:arm8_state``] (List.nth (certs, n-1))))
	THEN (REV_FULL_SIMP_TAC (srw_ss()) [Abbr `^var_name`])
	THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
	THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``])
    end;


prove(``^prog``,
      (DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
      THEN (FULL_SIMP_TAC (srw_ss()) [])

      (* First instruction *)
      THEN (MAP_EVERY PROCESS_ONE_ASSIGNMENT (List.tabulate (List.length certs, fn x => x+1)))

      (* Computation completed *)
      THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
      THEN DISCH_TAC
      (* use the step theorem *)
      THEN (ASSUME_TAC step)
      THEN (FULL_SIMP_TAC (srw_ss()) [])
      THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def])
);


(* **************************************** *)
(* INSTRUCTION LIFTER *)
(* **************************************** *)

(* To use a normal form, we prefer to express casts as bool2b x *)
(* instead of if x then v1 else v2 *)
fun ABBREV_NEW_ENV n (asl, g) =
    let val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
	val (x,_) = dest_imp g
	val (s,_) = dest_eq x
	val (f, [s,n]) = strip_comb s
        (* eval tac was simplifying too much *)
        val thm_rev = (SIMP_CONV (srw_ss()) [] ``^s.environ``)
	val nenv = (snd o dest_eq o concl) thm_rev
       in
	(* I must ensure that the same simplification is applied to the env *)
	   ((SIMP_TAC (srw_ss()) []) THEN
	   (Q.ABBREV_TAC `^var_name=^nenv`)) (asl,g)
    end;

(* Theorem to simplifying boolean cast *)
val bool_cast_simpl_tm = prove (``!e.(case if e then Reg1 (1w :word1) else Reg1 (0w :word1)
       of Reg1 v11 => Reg Bit1
        | Reg8 v12 => Reg Bit8
        | Reg16 v13 => Reg Bit16
        | Reg32 v14 => Reg Bit32
        | Reg64 v15 => Reg Bit64) = Reg Bit1``,
       (RW_TAC (srw_ss()) []));
(* Theorem to simplifying boolean cast *)
val bool_cast_simpl2_tm = prove (``!e.(case bool2b e
       of Reg1 v11 => Reg Bit1
        | Reg8 v12 => Reg Bit8
        | Reg16 v13 => Reg Bit16
        | Reg32 v14 => Reg Bit32
        | Reg64 v15 => Reg Bit64) = Reg Bit1``,
       (RW_TAC (srw_ss()) [bool2b_def]));


fun PROCESS_ONE_ASSIGNMENT certs n =
    let val _ = print "Processing instructio\n"
	val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
	val th_just = (List.nth (certs, n-1))
	val th1 = SPEC ``^var_name`` th_just
	val th2 = if is_forall (concl th1) then SPEC ``s:arm8_state`` th1 else th1
    in
	(ABBREV_NEW_ENV n)
	THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
	THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
	THEN (FULL_SIMP_TAC (srw_ss()) [])
	THEN (ASSUME_TAC th2)
	THEN (REV_FULL_SIMP_TAC (srw_ss()) [Abbr `^var_name`])
	(* bool type simplification *)
	THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
	THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
	THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
	THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
    end;

fun tc_one_instruction inst = 
    let val code = arm8AssemblerLib.arm8_code inst;
	val instr = (hd code);
	val (p, certs, [step]) = tc_stmt_arm8_hex instr;

        val prog = ``
        (^(list_mk_conj (hyp step))) ==>
        (
         (env "" = (NoType,Unknown)) /\
         ((env "R0") = (Reg Bit64, Int (Reg64 (s.REG 0w)))) /\
         ((env "R1") = (Reg Bit64, Int (Reg64 (s.REG 1w)))) /\
         ((env "R30") = (Reg Bit64, Int (Reg64 (s.REG 30w)))) /\
         ((env "ProcState_C") = (Reg Bit1, Int (bool2b s.PSTATE.C))) /\
         ((env "ProcState_N") = (Reg Bit1, Int (bool2b s.PSTATE.N))) /\
         ((env "ProcState_V") = (Reg Bit1, Int (bool2b s.PSTATE.V))) /\
         ((env "ProcState_Z") = (Reg Bit1, Int (bool2b s.PSTATE.Z))) /\
         ((env "arm8_state_PC") = (Reg Bit64, Int (Reg64 (s.PC)))) /\
         (?v.((env "tmp_R0") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_R1") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_R30") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_ProcState_C") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_ProcState_N") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_ProcState_V") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_ProcState_Z") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?m. (env "MEM" = (MemByte Bit64,Mem Bit64 m)) /\
	      (!a. m (Reg64 a) = Reg8 (s.MEM a)))
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
          |> ^((numSyntax.term_of_int o List.length) certs) = bs1) ==>
        (
         (bs1.environ "" = (NoType,Unknown)) /\
         ((bs1.environ "R0") = (Reg Bit64, Int (Reg64 (s1.REG 0w)))) /\
         ((bs1.environ "R1") = (Reg Bit64, Int (Reg64 (s1.REG 1w)))) /\
         ((bs1.environ "R30") = (Reg Bit64, Int (Reg64 (s1.REG 30w)))) /\
         ((bs1.environ "ProcState_C") = (Reg Bit1, Int (bool2b s1.PSTATE.C))) /\
         ((bs1.environ "ProcState_N") = (Reg Bit1, Int (bool2b s1.PSTATE.N))) /\
         ((bs1.environ "ProcState_V") = (Reg Bit1, Int (bool2b s1.PSTATE.V))) /\
         ((bs1.environ "ProcState_Z") = (Reg Bit1, Int (bool2b s1.PSTATE.Z))) /\
         ((bs1.environ "arm8_state_PC") = (Reg Bit64, Int (Reg64 (s1.PC)))) /\
         (?v.((bs1.environ "tmp_R0") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_R1") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_R30") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_C") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_N") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_V") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_Z") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v)))))
        )``;

	val thm = prove(``^prog``,
			(DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
		        THEN (FULL_SIMP_TAC (srw_ss()) [])
			(* for every instruction *)
			THEN (MAP_EVERY (PROCESS_ONE_ASSIGNMENT certs) (List.tabulate (List.length certs, fn x => x+1)))
			(* Computation completed *)
			THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
			THEN DISCH_TAC
			(* use the step theorem *)
			THEN (ASSUME_TAC step)
			THEN (FULL_SIMP_TAC (srw_ss()) [])
			THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def, bool2b_def])
		       );
    in
	thm
    end;

val inst = `MOV X0, #1`;
tc_one_instruction `MOV X0, #1`;
tc_one_instruction `MOV X0, #2`;
tc_one_instruction `ADD X0, X0, X0`;
tc_one_instruction `MOV X1, #1`;
tc_one_instruction `MOV X0, X1`;
tc_one_instruction `ADD X1, X1, X0`;
tc_one_instruction `ADD X0, X1, #42 `;

tc_one_instruction `BR X0`;
tc_one_instruction `BLR X0`;

tc_one_instruction `BIC X0, X0, X1`;

(*  Other flags: *)
(* EQ, NE, CS, HS, CC, LO, MI, PL, VS, VC, HI, LS, GE, LT, GT, LE, AL, NV  *)
tc_one_instruction `CSINC X0, X1, X0, NE`;
tc_one_instruction `CSINC X0, X1, X0, EQ`;
tc_one_instruction `CSNEG X0, X1, X0, EQ`;

tc_one_instruction `LDRSB X0, [X1]`;



tc_one_instruction `ADDS X0, X1, X0`;
val inst = `ADDS X0, X1, X0`;
(PROCESS_ONE_ASSIGNMENT certs 1)
THEN (PROCESS_ONE_ASSIGNMENT certs 2)
THEN (PROCESS_ONE_ASSIGNMENT certs 3)
THEN (PROCESS_ONE_ASSIGNMENT certs 4)
THEN (PROCESS_ONE_ASSIGNMENT certs 5)
THEN (PROCESS_ONE_ASSIGNMENT certs 6)
THEN (PROCESS_ONE_ASSIGNMENT certs 7)
THEN (PROCESS_ONE_ASSIGNMENT certs 8)
THEN (PROCESS_ONE_ASSIGNMENT certs 9)
THEN (PROCESS_ONE_ASSIGNMENT certs 10)

THEN (PROCESS_ONE_ASSIGNMENT certs 11)
THEN (PROCESS_ONE_ASSIGNMENT certs 12)
THEN (PROCESS_ONE_ASSIGNMENT certs 13)
      






val inst = `BLR X0`;
(PROCESS_ONE_ASSIGNMENT certs 1)
(PROCESS_ONE_ASSIGNMENT certs 2)
val n = 2;





(* There are problems since we can not lift the carry flag expression *)
tc_one_instruction `CMP X0, X1 `;
val inst = `CMP X0, X1`;


