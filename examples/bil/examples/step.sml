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

val bool_cast_simpl3_tm = prove (``(!v1 . ∃v. Reg1 v1 = bool2b v)``,
 (RW_TAC (srw_ss()) [bool2b_def])
 THEN (EXISTS_TAC ``if v1=1w:word1 then T else F``)
 THEN (RW_TAC (srw_ss()) [])
 THEN (UNDISCH_TAC ``v1 <> 1w:word1``)
 THEN (blastLib.BBLAST_TAC)
);
val bool_cast_simpl4_tm = prove (``(!v1 . (∃v. bool2b v1 = bool2b v))``,
 (RW_TAC (srw_ss()) [bool2b_def])
 THENL [
    (EXISTS_TAC ``T``) THEN (RW_TAC (srw_ss()) []),
    (EXISTS_TAC ``F``) THEN (RW_TAC (srw_ss()) [])
 ]);




fun PROCESS_ONE_ASSIGNMENT certs n =
    let val var_name = mk_var(concat["env", Int.toString n], ``:environment``)
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

fun tc_gen_goal p certs step =
      let val goal = ``
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
         (?m. (env "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) /\
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
         (?v.((bs1.environ "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?m. (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) /\
	      (!a. m (Reg64 a) = Reg8 (s1.MEM a)))
        )``
      in
	  goal
      end;

fun tc_one_instruction inst = 
    let val code = arm8AssemblerLib.arm8_code inst;
	val instr = (hd code);
	val (p, certs, [step]) = tc_stmt_arm8_hex instr;
	val goal = tc_gen_goal p certs step;
	val thm = prove(``^goal``,
			(DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
		        THEN (FULL_SIMP_TAC (srw_ss()) [])
			(* for every instruction *)
			THEN (MAP_EVERY (PROCESS_ONE_ASSIGNMENT certs) (List.tabulate (List.length certs, fn x => x+1)))
			(* Computation completed *)
			THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
			THEN DISCH_TAC
			(* use the step theorem *)
			THEN (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE myss [] (DISCH_ALL step))))
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
tc_one_instruction `LDR X0, [X1]`;

tc_one_instruction `ADDS X0, X1, X0`;
tc_one_instruction `CMP X0, X1 `;


(* There are problems since we can not lift the carry flag expression *)
tc_one_instruction `STR X1, [X0]`;



(* Speed up the process *)
val inst = `ADDS X0, X1, X0`;
(* Complete instruction 70s *)
(* tc_one_instruction inst; *)

val code = arm8AssemblerLib.arm8_code inst;
val instr = (hd code);
(* 2.11 seconds *)
val (p, certs, [step]) = tc_stmt_arm8_hex instr;

(* goal 0.2s *)
val goal = tc_gen_goal p certs step;

prove(``^goal``,
 (* first processing 0.6s *)
      (DISCH_TAC) 
	  THEN (DISCH_TAC) THEN (DISCH_TAC)
	  THEN (FULL_SIMP_TAC (srw_ss()) [])

(* Fist assignment 1.984s *)
HOL_Interactive.toggle_quietdec();
e (PROCESS_ONE_ASSIGNMENT certs 1);
HOL_Interactive.toggle_quietdec();

(* Fist assignment 2.492s *)
THEN (PROCESS_ONE_ASSIGNMENT certs 2)
(* Fist assignment 3.008s *)
THEN (PROCESS_ONE_ASSIGNMENT certs 3)
(* Fist assignment 3.592s *)
THEN (PROCESS_ONE_ASSIGNMENT certs 4)
(* Fist assignment 4.232s *)
THEN (PROCESS_ONE_ASSIGNMENT certs 5)
(* Fist assignment 4.656s *)
THEN (PROCESS_ONE_ASSIGNMENT certs 6)


(* PROCESS_ONE_ASSIGNMENT 1 *)
(* An ALL_TAC takes 0.3 s *)
ALL_TAC

(* Header 0.040s *)
val n = 1;
val var_name = mk_var(concat["env", Int.toString n], ``:environment``);
val th_just = (List.nth (certs, n-1));
val th1 = SPEC ``^var_name`` th_just;
val th2 = if is_forall (concl th1) then SPEC ``s:arm8_state`` th1 else th1;

(* 0.396s *)
(ABBREV_NEW_ENV n)

(* computation of the instruction 0.692s *)
THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])

(* Elimination of the assumptions on types 0.852s *)
THEN (FULL_SIMP_TAC (srw_ss()) [])
THEN (ASSUME_TAC th2)
THEN (REV_FULL_SIMP_TAC (srw_ss()) [Abbr `^var_name`])

(* bool type simplification 0.576s *)
THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])

(* type on the dest variable of the assignment 0.796s *)
THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])


(* PROCESS_ONE_ASSIGNMENT 7 *)
(* An ALL_TAC takes 0.384s s *)
ALL_TAC

(* Header 0.040s *)
val n = 7;
val var_name = mk_var(concat["env", Int.toString n], ``:environment``);
val th_just = (List.nth (certs, n-1));
val th1 = SPEC ``^var_name`` th_just;
val th2 = if is_forall (concl th1) then SPEC ``s:arm8_state`` th1 else th1;

(* 0.592s *)
(ABBREV_NEW_ENV n)

(* computation of the instruction 0.956s *)
THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])

(* Elimination of the assumptions on types 2.816s *)
THEN (FULL_SIMP_TAC (srw_ss()) [])
THEN (ASSUME_TAC th2)
THEN (REV_FULL_SIMP_TAC (srw_ss()) [Abbr `^var_name`])

(* bool type simplification 1.100s *)
THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])

(* type on the dest variable of the assignment 1.540s *)
THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def])
THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])






(* Try to speed up the computation *)
val single_step_assign_64_thm = prove( ``
!env past_steps var e v lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Assign var e)) ==>
((LENGTH l) >= (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
(var <> "") ==>
(?v.((env var) = (Reg Bit64, Int (Reg64 (v))))) ==>
((bil_eval_exp e env) = Int (Reg64 v)) ==>
(
 (bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i|>;
     pi :=
       [<|label := lbl;
          statements := l
        |>];
     environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
   n) = 
(bil_exec_step_n
   <|pco := if i < LENGTH l − 1 then SOME <|label := lbl; index := i + 1|> else NONE;
     pi :=
       [<|label := lbl;
          statements := l
       |>];
     environ :=
       (λc.
          if var = c then (Reg Bit64,Int (Reg64 v))
          else env c); termcode := Unknown; debug := d1;
     execs := past_steps + 1|> (n-1))
)
``,
       (REPEAT STRIP_TAC)
       THEN (fn (asl,g) =>
	  let val rx = (snd o dest_eq) g in
	      (Q.ABBREV_TAC `s2=^rx`)(asl,g)
	  end)
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def, Abbr `s2`])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
);


(* Try to speed up the computation *)
val single_step_assign_1_thm = prove( ``
!env past_steps var e v lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Assign var e)) ==>
((LENGTH l) >= (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
(var <> "") ==>
(?v.((env var) = (Reg Bit1, Int (bool2b (v))))) ==>
((bil_eval_exp e env) = Int (bool2b v)) ==>
(
 (bil_exec_step_n
   <|pco := SOME <|label := lbl; index := i|>;
     pi :=
       [<|label := lbl;
          statements := l
        |>];
     environ := env; termcode := Unknown; debug := d1; execs := past_steps|>
   n) = 
(bil_exec_step_n
   <|pco := if i < LENGTH l − 1 then SOME <|label := lbl; index := i + 1|> else NONE;
     pi :=
       [<|label := lbl;
          statements := l
       |>];
     environ :=
       (λc.
          if var = c then (Reg Bit1,Int (bool2b v))
          else env c); termcode := Unknown; debug := d1;
     execs := past_steps + 1|> (n-1))
)
``,
       (REPEAT STRIP_TAC)
       THEN (fn (asl,g) =>
	  let val rx = (snd o dest_eq) g in
	      (Q.ABBREV_TAC `s2=^rx`)(asl,g)
	  end)
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def, Abbr `s2`])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (arith_ss) [bool_cast_simpl2_tm])
);




HOL_Interactive.toggle_quietdec();

fun ONE_EXEC2 certs i =
(fn (asl,curr_goal) =>
let val exec_term = (fst o dest_eq o fst o dest_imp) curr_goal;
    val (_, [state, steps]) = strip_comb exec_term;
    val (_, [pco, ("pi", pi),  ("environ", env), tc, db, ("execs", ex)]) = TypeBase.dest_record state;
    val th_just = (List.nth (certs, i-1));
    val th_just1 = SPEC env th_just;
    val th_just2 = if is_forall (concl th1)
		   then SPEC ``s:arm8_state`` th_just1
		   else th_just1;
    val th_just3 = (SIMP_RULE (srw_ss()) [combinTheory.UPDATE_def] th_just2);
    val th_just4 = (UNDISCH_ALL th_just3);
    val ([pr], _) = listSyntax.dest_list pi;
    val (_, [("label", lbl),  ("statements", sts)]) = TypeBase.dest_record pr;
    val (sts1, _) = listSyntax.dest_list sts;
    val statement = List.nth(sts1, i-1);
    val (operator, [vname, exp]) = strip_comb statement;
    val value = (hd o snd o strip_comb o hd o snd o strip_comb o snd o dest_eq o concl) th_just4;
    val single_assign_th = if (type_of value) = ``:word64``
			   then single_step_assign_64_thm
			   else  single_step_assign_1_thm
    val th1 = SPECL [env, ex, vname, exp, value, ``Label "main"``, steps] single_assign_th;
    (* val simp1 = (SIMP_RULE (srw_ss()) [] th1); *)
    val simp1 = (SIMP_RULE (bool_ss) [] th1);
    val hd_thm = prove (``(EL ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1))) ^sts = Assign ^vname ^exp)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_thm = prove (``(LENGTH ^sts >= ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1)))+1)``, (FULL_SIMP_TAC (srw_ss()) []));
    val th2 = (SPECL [sts, numSyntax.mk_numeral(Arbnum.fromInt (i-1))]) simp1;
    val th3 = (MP (MP th2 hd_thm) length_thm);
in
    (
      (ASSUME_TAC th_just4)
      THEN (ASSUME_TAC th3)
      (* This is a problem becouse we should not use bool2b_def *)
      THEN (REV_FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl3_tm, bool_cast_simpl4_tm])
      THEN (PAT_ASSUM ``p:bool`` (fn thm=> ALL_TAC))
      THEN (PAT_ASSUM ``p:bool`` (fn thm=> ALL_TAC))
    )
    (asl, curr_goal)
end
);


(* New execution: 31.466 s down from 70 s*)

val code = arm8AssemblerLib.arm8_code inst;
val instr = (hd code);
(* 2.11 seconds *)
val (p, certs, [step]) = tc_stmt_arm8_hex instr;

(* goal 0.2s *)
val goal = tc_gen_goal p certs step;

prove(``^goal``,
 (* first processing 0.6s *)
      (DISCH_TAC) 
	  THEN (DISCH_TAC) THEN (DISCH_TAC)
	  THEN (FULL_SIMP_TAC (srw_ss()) [])

THEN (ONE_EXEC2 certs 1)
THEN (ONE_EXEC2 certs 2)
THEN (ONE_EXEC2 certs 3)
THEN (ONE_EXEC2 certs 4)
THEN (ONE_EXEC2 certs 5)
THEN (ONE_EXEC2 certs 6)
THEN (ONE_EXEC2 certs 7)
THEN (ONE_EXEC2 certs 8)
THEN (ONE_EXEC2 certs 9)
THEN (ONE_EXEC2 certs 10)
THEN (ONE_EXEC2 certs 11)
THEN (ONE_EXEC2 certs 12)
THEN (ONE_EXEC2 certs 13)

(* Computation completed *)
THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
THEN DISCH_TAC
(* use the step theorem *)
THEN (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE myss [] (DISCH_ALL step))))
THEN (FULL_SIMP_TAC (srw_ss()) [])
THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def, bool2b_def])
);


val i = 13;
val curr_goal = ``
(bil_exec_step_n
   <|pco := SOME <|label := Label "main"; index := 12|>;
     pi :=
       [<|label := Label "main";
          statements :=
            [Assign "tmp_arm8_state_PC" (Den "arm8_state_PC");
             Assign "tmp_ProcState_C" (Den "ProcState_C");
             Assign "tmp_ProcState_N" (Den "ProcState_N");
             Assign "tmp_ProcState_V" (Den "ProcState_V");
             Assign "tmp_ProcState_Z" (Den "ProcState_Z");
             Assign "tmp_R0" (Den "R0"); Assign "tmp_R1" (Den "R1");
             Assign "R0" (Plus (Den "tmp_R1") (Den "tmp_R0"));
             Assign "ProcState_N"
               (SignedLessThan (Plus (Den "tmp_R0") (Den "tmp_R1"))
                  (Const (Reg64 0w)));
             Assign "ProcState_Z"
               (Equal (Plus (Den "tmp_R0") (Den "tmp_R1"))
                  (Const (Reg64 0w)));
             Assign "ProcState_C"
               (Not
                  (LessThan
                     (Plus
                        (Plus (Div (Den "tmp_R0") (Const (Reg64 2w)))
                           (Div (Den "tmp_R1") (Const (Reg64 2w))))
                        (Mult (Mod (Den "tmp_R0") (Const (Reg64 2w)))
                           (Mod (Den "tmp_R1") (Const (Reg64 2w)))))
                     (Const (Reg64 0x8000000000000000w))));
             Assign "ProcState_V"
               (And
                  (Equal
                     (SignedLessThan (Den "tmp_R1") (Const (Reg64 0w)))
                     (SignedLessThan (Den "tmp_R0") (Const (Reg64 0w))))
                  (Not
                     (Equal
                        (SignedLessThan (Den "tmp_R1")
                           (Const (Reg64 0w)))
                        (Equal
                           (And
                              (RightShift
                                 (Plus (Den "tmp_R0") (Den "tmp_R1"))
                                 (Const (Reg64 63w)))
                              (Const (Reg64 1w)))
                           (Const (Reg64 1w))))));
             Assign "arm8_state_PC"
               (Plus (Den "tmp_arm8_state_PC") (Const (Reg64 4w)))]|>];
     environ :=
       (λc.
          if "ProcState_V" = c then
            (Reg Bit1,
             Int
               (bool2b
                  ((word_msb (s.REG 1w) ⇔ word_msb (s.REG 0w)) ∧
                   (word_msb (s.REG 1w) ⇎
                    BIT 63 (w2n (s.REG 1w) + w2n (s.REG 0w))))))
          else if "ProcState_C" = c then
            (Reg Bit1,
             Int
               (bool2b
                  ((if
                      w2n (s.REG 1w) + w2n (s.REG 0w) <
                      18446744073709551616
                    then
                      w2n (s.REG 1w) + w2n (s.REG 0w)
                    else
                      (w2n (s.REG 1w) + w2n (s.REG 0w)) MOD
                      18446744073709551616) ≠
                   w2n (s.REG 1w) + w2n (s.REG 0w))))
          else if "ProcState_Z" = c then
            (Reg Bit1,Int (bool2b (s.REG 0w + s.REG 1w = 0w)))
          else if "ProcState_N" = c then
            (Reg Bit1,Int (bool2b (word_msb (s.REG 0w + s.REG 1w))))
          else if "R0" = c then
            (Reg Bit64,Int (Reg64 (s.REG 0w + s.REG 1w)))
          else if "tmp_R1" = c then (Reg Bit64,Int (Reg64 (s.REG 1w)))
          else if "tmp_R0" = c then (Reg Bit64,Int (Reg64 (s.REG 0w)))
          else if "tmp_ProcState_Z" = c then
            (Reg Bit1,Int (bool2b s.PSTATE.Z))
          else if "tmp_ProcState_V" = c then
            (Reg Bit1,Int (bool2b s.PSTATE.V))
          else if "tmp_ProcState_N" = c then
            (Reg Bit1,Int (bool2b s.PSTATE.N))
          else if "tmp_ProcState_C" = c then
            (Reg Bit1,Int (bool2b s.PSTATE.C))
          else if "tmp_arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 s.PC))
          else env c); termcode := Unknown; debug := d1;
     execs := e1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1|> 1 =
 bs1) ⇒
(bs1.environ "" = (NoType,Unknown)) ∧
(bs1.environ "R0" = (Reg Bit64,Int (Reg64 (s1.REG 0w)))) ∧
(bs1.environ "R1" = (Reg Bit64,Int (Reg64 (s1.REG 1w)))) ∧
(bs1.environ "R30" = (Reg Bit64,Int (Reg64 (s1.REG 30w)))) ∧
(bs1.environ "ProcState_C" = (Reg Bit1,Int (bool2b s1.PSTATE.C))) ∧
(bs1.environ "ProcState_N" = (Reg Bit1,Int (bool2b s1.PSTATE.N))) ∧
(bs1.environ "ProcState_V" = (Reg Bit1,Int (bool2b s1.PSTATE.V))) ∧
(bs1.environ "ProcState_Z" = (Reg Bit1,Int (bool2b s1.PSTATE.Z))) ∧
(bs1.environ "arm8_state_PC" = (Reg Bit64,Int (Reg64 s1.PC))) ∧
(∃v. bs1.environ "tmp_R0" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R1" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R30" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_ProcState_C" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_N" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_V" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_Z" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_arm8_state_PC" = (Reg Bit64,Int (Reg64 v))) ∧
∃m.
  (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
  ∀a. m (Reg64 a) = Reg8 (s1.MEM a)
``;





val i = 1;
(* For the first execution *)
val curr_goal = ``
(bil_exec_step_n
   <|pco := SOME <|label := Label "main"; index := 0|>;
     pi :=
       [<|label := Label "main";
          statements :=
            [Assign "tmp_arm8_state_PC" (Den "arm8_state_PC");
             Assign "tmp_ProcState_C" (Den "ProcState_C");
             Assign "tmp_ProcState_N" (Den "ProcState_N");
             Assign "tmp_ProcState_V" (Den "ProcState_V");
             Assign "tmp_ProcState_Z" (Den "ProcState_Z");
             Assign "tmp_R0" (Den "R0"); Assign "tmp_R1" (Den "R1");
             Assign "R0" (Plus (Den "tmp_R1") (Den "tmp_R0"));
             Assign "ProcState_N"
               (SignedLessThan (Plus (Den "tmp_R0") (Den "tmp_R1"))
                  (Const (Reg64 0w)));
             Assign "ProcState_Z"
               (Equal (Plus (Den "tmp_R0") (Den "tmp_R1"))
                  (Const (Reg64 0w)));
             Assign "ProcState_C"
               (Not
                  (LessThan
                     (Plus
                        (Plus (Div (Den "tmp_R0") (Const (Reg64 2w)))
                           (Div (Den "tmp_R1") (Const (Reg64 2w))))
                        (Mult (Mod (Den "tmp_R0") (Const (Reg64 2w)))
                           (Mod (Den "tmp_R1") (Const (Reg64 2w)))))
                     (Const (Reg64 0x8000000000000000w))));
             Assign "ProcState_V"
               (And
                  (Equal
                     (SignedLessThan (Den "tmp_R1") (Const (Reg64 0w)))
                     (SignedLessThan (Den "tmp_R0") (Const (Reg64 0w))))
                  (Not
                     (Equal
                        (SignedLessThan (Den "tmp_R1")
                           (Const (Reg64 0w)))
                        (Equal
                           (And
                              (RightShift
                                 (Plus (Den "tmp_R0") (Den "tmp_R1"))
                                 (Const (Reg64 63w)))
                              (Const (Reg64 1w)))
                           (Const (Reg64 1w))))));
             Assign "arm8_state_PC"
               (Plus (Den "tmp_arm8_state_PC") (Const (Reg64 4w)))]|>];
     environ := env; termcode := Unknown; debug := d1; execs := e1|>
   13 =
 bs1) ⇒
(bs1.environ "" = (NoType,Unknown)) ∧
(bs1.environ "R0" = (Reg Bit64,Int (Reg64 (s1.REG 0w)))) ∧
(bs1.environ "R1" = (Reg Bit64,Int (Reg64 (s1.REG 1w)))) ∧
(bs1.environ "R30" = (Reg Bit64,Int (Reg64 (s1.REG 30w)))) ∧
(bs1.environ "ProcState_C" = (Reg Bit1,Int (bool2b s1.PSTATE.C))) ∧
(bs1.environ "ProcState_N" = (Reg Bit1,Int (bool2b s1.PSTATE.N))) ∧
(bs1.environ "ProcState_V" = (Reg Bit1,Int (bool2b s1.PSTATE.V))) ∧
(bs1.environ "ProcState_Z" = (Reg Bit1,Int (bool2b s1.PSTATE.Z))) ∧
(bs1.environ "arm8_state_PC" = (Reg Bit64,Int (Reg64 s1.PC))) ∧
(∃v. bs1.environ "tmp_R0" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R1" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R30" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_ProcState_C" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_N" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_V" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_Z" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_arm8_state_PC" = (Reg Bit64,Int (Reg64 v))) ∧
∃m.
  (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
  ∀a. m (Reg64 a) = Reg8 (s1.MEM a)
``;

