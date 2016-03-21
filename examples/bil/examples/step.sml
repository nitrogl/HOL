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
(* open arm8stepbilLib; *)
HOL_Interactive.toggle_quietdec();


(* **************************************** *)
(* INSTRUCTION LIFTER *)
(* **************************************** *)
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
         ((env "R2") = (Reg Bit64, Int (Reg64 (s.REG 2w)))) /\
         ((env "R3") = (Reg Bit64, Int (Reg64 (s.REG 3w)))) /\
         ((env "R30") = (Reg Bit64, Int (Reg64 (s.REG 30w)))) /\
         ((env "ProcState_C") = (Reg Bit1, Int (bool2b s.PSTATE.C))) /\
         ((env "ProcState_N") = (Reg Bit1, Int (bool2b s.PSTATE.N))) /\
         ((env "ProcState_V") = (Reg Bit1, Int (bool2b s.PSTATE.V))) /\
         ((env "ProcState_Z") = (Reg Bit1, Int (bool2b s.PSTATE.Z))) /\
         ((env "arm8_state_PC") = (Reg Bit64, Int (Reg64 (s.PC)))) /\
         ((env "arm8_state_SP_EL0") = (Reg Bit64, Int (Reg64 (s.SP_EL0)))) /\
         (?v.((env "tmp_R0") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_R1") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_R2") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_R3") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_R30") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_ProcState_C") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_ProcState_N") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_ProcState_V") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_ProcState_Z") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((env "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((env "tmp_arm8_state_SP_EL0") = (Reg Bit64, Int (Reg64 (v))))) /\
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
         ((bs1.environ "R2") = (Reg Bit64, Int (Reg64 (s1.REG 2w)))) /\
         ((bs1.environ "R3") = (Reg Bit64, Int (Reg64 (s1.REG 3w)))) /\
         ((bs1.environ "R30") = (Reg Bit64, Int (Reg64 (s1.REG 30w)))) /\
         ((bs1.environ "ProcState_C") = (Reg Bit1, Int (bool2b s1.PSTATE.C))) /\
         ((bs1.environ "ProcState_N") = (Reg Bit1, Int (bool2b s1.PSTATE.N))) /\
         ((bs1.environ "ProcState_V") = (Reg Bit1, Int (bool2b s1.PSTATE.V))) /\
         ((bs1.environ "ProcState_Z") = (Reg Bit1, Int (bool2b s1.PSTATE.Z))) /\
         ((bs1.environ "arm8_state_PC") = (Reg Bit64, Int (Reg64 (s1.PC)))) /\
         ((bs1.environ "arm8_state_SP_EL0") = (Reg Bit64, Int (Reg64 (s1.SP_EL0)))) /\
         (?v.((bs1.environ "tmp_R0") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_R1") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_R2") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_R3") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_R30") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_C") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_N") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_V") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_ProcState_Z") = (Reg Bit1, Int (Reg1 (v))))) /\
         (?v.((bs1.environ "tmp_arm8_state_PC") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?v.((bs1.environ "tmp_arm8_state_SP_EL0") = (Reg Bit64, Int (Reg64 (v))))) /\
         (?m. (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) /\
	      (!a. m (Reg64 a) = Reg8 (s1.MEM a)))
        )``
      in
	  goal
      end;

HOL_Interactive.toggle_quietdec();
(* prevent >>>~ to become >>> *)
val myss = simpLib.remove_ssfrags (srw_ss()) ["word shift"];
HOL_Interactive.toggle_quietdec();

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


(* val inst = `MOV X0, #1`; *)
(* tc_one_instruction `MOV X0, #1`; *)
(* tc_one_instruction `MOV X0, #2`; *)
(* tc_one_instruction `ADD X0, X0, X0`; *)
(* tc_one_instruction `MOV X1, #1`; *)
(* tc_one_instruction `MOV X0, X1`; *)
(* tc_one_instruction `ADD X1, X1, X0`; *)
(* tc_one_instruction `ADD X0, X1, #42 `; *)

(* tc_one_instruction `BR X0`; *)
(* tc_one_instruction `BLR X0`; *)

(* tc_one_instruction `BIC X0, X0, X1`; *)

(* (\*  Other flags: *\) *)
(* (\* EQ, NE, CS, HS, CC, LO, MI, PL, VS, VC, HI, LS, GE, LT, GT, LE, AL, NV  *\) *)
(* tc_one_instruction `CSINC X0, X1, X0, NE`; *)
(* tc_one_instruction `CSINC X0, X1, X0, EQ`; *)
(* tc_one_instruction `CSNEG X0, X1, X0, EQ`; *)

(* tc_one_instruction `LDRSB X0, [X1]`; *)
(* tc_one_instruction `LDR X0, [X1]`; *)

(* tc_one_instruction `ADDS X0, X1, X0`; *)
(* tc_one_instruction `CMP X0, X1 `; *)
(* (\* There are problems since we can not lift the carry flag expression *\) *)

(* tc_one_instruction `STR X1, [X0]`; *)





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


val single_step_assign_mem64_thm = prove( ``
!env past_steps (vname:string) exp hm lbl n l i.
(lbl <> Label "") ==>
(n > 0) ==>
((EL i l) = (Assign "arm8_state_MEM"
     (* (Store (Den "arm8_state_MEM") ba bv (Const (Reg1 0w)) Bit64) *)
     exp
)) ==>
((LENGTH l) >= (i+1)) ==>
(env "" = (NoType,Unknown)) ==>
(?v.((env "arm8_state_MEM") = (MemByte Bit64,v))) ==>
(∃m.
   (* ((bil_eval_exp (Store (Den "arm8_state_MEM") ba bv (Const (Reg1 0w)) Bit64) env) = (Mem Bit64 m)) ∧ *)
   ((bil_eval_exp exp env) = (Mem Bit64 m)) ∧
   ∀a. m (Reg64 a) = Reg8 (hm a)) ==>
(?m.
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
          if "arm8_state_MEM" = c then (MemByte Bit64,Mem Bit64 m)
          else env c); termcode := Unknown; debug := d1;
     execs := past_steps + 1|> (n-1))
) /\
(∀a. m (Reg64 a) = Reg8 (hm a))
)
``,
       (REPEAT STRIP_TAC)
       THEN (EXISTS_TAC ``m:bil_int_t -> bil_int_t``)
       THEN (fn (asl,g) =>
	  let val rx = (snd o dest_eq o fst o dest_conj) g in
	      (Q.ABBREV_TAC `s2=^rx`)(asl,g)
	  end)
       THEN (SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (computeLib.RESTR_EVAL_TAC [``bil_eval_exp``, ``bil_exec_step_n``, ``bool2b``])
       THEN (FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl2_tm])
       THEN (FULL_SIMP_TAC (arith_ss) [])
       THEN (FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_def, Abbr `s2`])
);










fun ONE_EXEC2 certs i =

(fn (asl,curr_goal) =>
let val exec_term = (fst o dest_eq o fst o dest_imp) curr_goal;
    val (_, [state, steps]) = strip_comb exec_term;
    val (_, [pco, ("pi", pi),  ("environ", env), tc, db, ("execs", ex)]) = TypeBase.dest_record state;
    val th_just = (List.nth (certs, i-1));
    val th_just1 = SPEC env th_just;
    val th_just2 = if is_forall (concl th_just1)
		   then SPEC ``s:arm8_state`` th_just1
		   else th_just1;
    val th_just3 = (SIMP_RULE (srw_ss()) [combinTheory.UPDATE_def] th_just2);
    val th_just4 = (UNDISCH_ALL th_just3);
    val ([pr], _) = listSyntax.dest_list pi;
    val (_, [("label", lbl),  ("statements", sts)]) = TypeBase.dest_record pr;
    val (sts1, _) = listSyntax.dest_list sts;
    val statement = List.nth(sts1, i-1);
    val (operator, [vname, exp]) = strip_comb statement;
    val (single_assign_th, value) =
        (* standard case that is when we are not assigning a memory *)
        if (is_eq o concl) th_just4
        then
            let val value = (hd o snd o strip_comb o hd o snd o strip_comb o snd o dest_eq o concl) th_just4;
            in if (type_of value) = ``:word64``
               then (single_step_assign_64_thm, value)
               else (single_step_assign_1_thm, value)
            end
        else
          let val value = (snd o dest_comb o snd o dest_eq o snd o dest_forall o snd o dest_conj o snd o dest_exists o concl) th_just4;
              val value = ``\a.^value``;
  	      (* we extract the type of the write *)
	      val store_value_eq = (fst o dest_conj o snd o dest_exists o concl) th_just4;
	      val store_exp = (hd o snd o strip_comb o fst o dest_eq) store_value_eq;
	      val store_type = (hd o rev o snd o strip_comb) store_exp;
          in
	      if store_type = ``Bit64`` then
		  (single_step_assign_mem64_thm, value)
	      else
		  (single_step_assign_mem64_thm, value)
          end
    val th1 = SPECL [env, ex, vname, exp, value, ``Label "main"``, steps] single_assign_th;
    val th2 = (SPECL [sts, numSyntax.mk_numeral(Arbnum.fromInt (i-1))]) th1;
    val lbl_not_empty_thm = prove(``^((fst o dest_imp o concl) th2)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_minus_i_not_zero_thm = prove(``^((fst o dest_imp o snd o dest_imp o concl) th2)``, (FULL_SIMP_TAC (arith_ss) []));
    (* val simp2 = (SIMP_RULE (srw_ss()) [] th2); *)
    val hd_thm = prove (``(EL ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1))) ^sts = Assign ^vname ^exp)``, (FULL_SIMP_TAC (srw_ss()) []));
    val length_thm = prove (``(LENGTH ^sts >= ^(numSyntax.mk_numeral(Arbnum.fromInt(i-1)))+1)``, (FULL_SIMP_TAC (srw_ss()) []));
    val th3 = (MP (MP (MP (MP th2 lbl_not_empty_thm) length_minus_i_not_zero_thm) hd_thm) length_thm);
    val th4 = UNDISCH_ALL th3;
in
    (
     (* We prove the big theorem and we use it for the substitution *)
     (SUBGOAL_THEN (concl th4) (fn thm =>
           (* we are probably handling a memory update *)
           if ((is_exists o concl) thm) then
               ((CHOOSE_TAC thm)
		THEN (FULL_SIMP_TAC (srw_ss()) [])
		(* we should not remove the additional assumption *)
		(* that guarantee constraint the content of the memory *)
		THEN (PAT_ASSUM ``bil_exec_step_n a b = c`` (fn thm => ALL_TAC))
	       )
	   else
	      ((REWRITE_TAC [thm])
	       THEN (SIMP_TAC (srw_ss()) []))
     ))
     THENL [
          (fn (asl,goal) =>
          (MAP_EVERY (fn tm => if List.exists (fn tm1 => tm1 = tm) asl
                              then ALL_TAC
  			      (* This is probably a memory *)
                              else if (is_exists tm) then
				  (SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
				  THENL [
				    (FULL_SIMP_TAC (srw_ss()) []),
				    ALL_TAC
				  ]
			      else ALL_TAC
		     )
                    (hyp th_just4)
          )(asl,goal))
          THEN (ASSUME_TAC th_just4)
	  THEN (fn (asl,goal) =>
               (MAP_EVERY (fn tm =>
                              (* The hypotesis is in the assumptions *)
                              if List.exists (fn tm1 => tm1 = tm) asl then ALL_TAC
                              (* this is the assumption justified by the expression certificate *)
                              else if tm = (concl th_just4) then ALL_TAC
                              (* "tmp_arm8_state_PC" ≠ "" *)
                              else if (is_neq tm) andalso ((snd o dest_eq o dest_neg) tm = ``""``) then
                                   (ASSUME_TAC (prove(tm, FULL_SIMP_TAC (srw_ss()) [])))
                              (* it is an existential quantifier, we try to solve this using the assumptions *)
                              else if (is_exists tm) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) [
					    bool_cast_simpl3_tm,
					    bool_cast_simpl4_tm]), ALL_TAC])
                              (* env" "" = (NoType,Unknown) *)
                              else if (is_eq tm) andalso ((snd o dest_eq)tm = ``(NoType,Unknown)``) then
                                   ((SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm))
                                    THENL [(FULL_SIMP_TAC (srw_ss()) []), ALL_TAC])
                              else (print_term tm;
                                    ALL_TAC))
                    (hyp th4)
          )(asl,goal))
          THEN (ACCEPT_TAC th4)
          ,
          ALL_TAC]
      (* For memory the hypotesis must be proved manually *)
      (* due to the exist condition *)
      (* ((SUBGOAL_THEN ((hd o hyp) th_just4) *)
      (*                (fn thm => ((ASSUME_TAC thm) THEN (ASSUME_TAC th_just4)))) *)
      (*                THENL [(FULL_SIMP_TAC (srw_ss()) []), ALL_TAC]) *)
      (* THEN (MAP_EVERY (fn tm => (SUBGOAL_THEN tm (fn thm => ASSUME_TAC thm)) *)
      (*                           THENL [(FULL_SIMP_TAC (srw_ss()) []), ALL_TAC]) *)
      (*                 (hyp (UNDISCH_ALL th3))) *)
      (* THEN (ASSUME_TAC (UNDISCH_ALL th3)) *)
      (* THEN (REV_FULL_SIMP_TAC (bool_ss) []) *)
      (* THEN (SIMP_TAC (srw_ss()) []) *)
      (* THEN (PAT_ASSUM ``p:bool`` (fn thm=> ALL_TAC)) *)
(* (\* This is a problem becouse we should not use bool2b_def *\) *)
(*       THEN (REV_FULL_SIMP_TAC (srw_ss()) [bool_cast_simpl3_tm, bool_cast_simpl4_tm]) *)
(*       THEN (PAT_ASSUM ``p:bool`` (fn thm=> ALL_TAC)) *)
(*       (\* When we use the memory this can remove the property that we need *\) *)
(*       (\* since the theorem is a conjunction *\) *)
(*       (\* THEN (PAT_ASSUM ``p:bool`` (fn thm=> ALL_TAC)) *\) *)
    )
    (asl, curr_goal)
end
)

;

fun tc_one_instruction2_by_bin instr =
    let val (p, certs, [step]) = tc_stmt_arm8_hex instr;
	val goal = tc_gen_goal p certs step;
	val thm = prove(``^goal``,
			(DISCH_TAC) THEN (DISCH_TAC) THEN (DISCH_TAC)
		        THEN (FULL_SIMP_TAC (srw_ss()) [])
			(* for every instruction *)
			THEN (MAP_EVERY (ONE_EXEC2 certs) (List.tabulate (List.length certs, fn x => x+1)))
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

fun tc_one_instruction2 inst =
    let val code = arm8AssemblerLib.arm8_code inst;
	val instr = (hd code);
    in
	tc_one_instruction2_by_bin instr
    end;



(* COMPARISON: old execution *)
tc_one_instruction `MOV X0, #1`;
tc_one_instruction2 `MOV X0, #1`;

tc_one_instruction `ADD X0, X0, X0`;
tc_one_instruction2 `ADD X0, X0, X0`;

tc_one_instruction `ADD X0, X1, #42 `;
tc_one_instruction2 `ADD X0, X1, #42 `;

tc_one_instruction `BLR X0`;
tc_one_instruction2 `BLR X0 `;

tc_one_instruction `CSINC X0, X1, X0, NE`;
tc_one_instruction2 `CSINC X0, X1, X0, NE`;

tc_one_instruction `LDRSB X0, [X1]`;
tc_one_instruction2 `LDRSB X0, [X1]`;

tc_one_instruction `LDR X0, [X1]`;
tc_one_instruction2 `LDR X0, [X1]`;

tc_one_instruction `STR X1, [X0]`;
tc_one_instruction2 `STR X1, [X0]`;

tc_one_instruction `ADDS X0, X1, X0`;
tc_one_instruction2 `ADDS X0, X1, X0`;








(*   2c:   7900001f        strh    wzr, [x0] *)
val instr = "7900001f";
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


(* THEN (ONE_EXEC2 certs 5) *)

(* Computation completed *)
THEN (FULL_SIMP_TAC (srw_ss()) [Once bil_exec_step_n_def])
THEN DISCH_TAC

(* use the step theorem *)
THEN (ASSUME_TAC (UNDISCH_ALL (SIMP_RULE myss [] (DISCH_ALL step))))
THEN (FULL_SIMP_TAC (srw_ss()) [])

THEN (RW_TAC (srw_ss()) [combinTheory.UPDATE_def, bool2b_def])
);


val i = 5;
val curr_goal = ``
(bil_exec_step_n
   <|pco := SOME <|label := Label "main"; index := 4|>;
     pi :=
       [<|label := Label "main";
          statements :=
            [Assign "tmp_arm8_state_PC" (Den "arm8_state_PC");
             Assign "tmp_arm8_state_SP_EL0" (Den "arm8_state_SP_EL0");
             Assign "tmp_R3" (Den "R3");
             Assign "arm8_state_PC"
               (Plus (Den "tmp_arm8_state_PC") (Const (Reg64 4w)));
             Assign "arm8_state_MEM"
               (Store (Den "arm8_state_MEM")
                  (Plus (Den "tmp_arm8_state_SP_EL0")
                     (Const (Reg64 4w))) (LowCast (Den "tmp_R3") Bit32)
                  (Const (Reg1 0w)) Bit32)]|>];
     environ :=
       (λc.
          if "arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 (s.PC + 4w)))
          else if "tmp_R3" = c then (Reg Bit64,Int (Reg64 (s.REG 3w)))
          else if "tmp_arm8_state_SP_EL0" = c then
            (Reg Bit64,Int (Reg64 s.SP_EL0))
          else if "tmp_arm8_state_PC" = c then
            (Reg Bit64,Int (Reg64 s.PC))
          else env c); termcode := Unknown; debug := d1;
     execs := e1 + 1 + 1 + 1 + 1|> 1 =
 bs1) ⇒
(bs1.environ "" = (NoType,Unknown)) ∧
(bs1.environ "R0" = (Reg Bit64,Int (Reg64 (s1.REG 0w)))) ∧
(bs1.environ "R1" = (Reg Bit64,Int (Reg64 (s1.REG 1w)))) ∧
(bs1.environ "R2" = (Reg Bit64,Int (Reg64 (s1.REG 2w)))) ∧
(bs1.environ "R3" = (Reg Bit64,Int (Reg64 (s1.REG 3w)))) ∧
(bs1.environ "R30" = (Reg Bit64,Int (Reg64 (s1.REG 30w)))) ∧
(bs1.environ "ProcState_C" = (Reg Bit1,Int (bool2b s1.PSTATE.C))) ∧
(bs1.environ "ProcState_N" = (Reg Bit1,Int (bool2b s1.PSTATE.N))) ∧
(bs1.environ "ProcState_V" = (Reg Bit1,Int (bool2b s1.PSTATE.V))) ∧
(bs1.environ "ProcState_Z" = (Reg Bit1,Int (bool2b s1.PSTATE.Z))) ∧
(bs1.environ "arm8_state_PC" = (Reg Bit64,Int (Reg64 s1.PC))) ∧
(bs1.environ "arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 s1.SP_EL0))) ∧
(∃v. bs1.environ "tmp_R0" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R1" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R2" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R3" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_R30" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_ProcState_C" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_N" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_V" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_ProcState_Z" = (Reg Bit1,Int (Reg1 v))) ∧
(∃v. bs1.environ "tmp_arm8_state_PC" = (Reg Bit64,Int (Reg64 v))) ∧
(∃v. bs1.environ "tmp_arm8_state_SP_EL0" = (Reg Bit64,Int (Reg64 v))) ∧
∃m.
  (bs1.environ "arm8_state_MEM" = (MemByte Bit64,Mem Bit64 m)) ∧
  ∀a. m (Reg64 a) = Reg8 (s1.MEM a)  ``;




(* 0000000000000000 <internal_mul>: *)
(*    0:   d10103ff        sub     sp, sp, #0x40 *)
tc_one_instruction2_by_bin "d10103ff";
(*    4:   f9000fe0        str     x0, [sp,#24] *)
tc_one_instruction2_by_bin "f9000fe0";
(*    8:   f9000be1        str     x1, [sp,#16] *)
tc_one_instruction2_by_bin "f9000be1";
(*    c:   f90007e2        str     x2, [sp,#8] *)
tc_one_instruction2_by_bin "f90007e2";
(*   10:   b90007e3        str     w3, [sp,#4] *)
tc_one_instruction2_by_bin "b90007e3";
(*   14:   b9003bff        str     wzr, [sp,#56] *)
tc_one_instruction2_by_bin "b9003bff";
(*   18:   14000009        b       3c <internal_mul+0x3c> *)
tc_one_instruction2_by_bin "14000009";
(*   1c:   b9803be0        ldrsw   x0, [sp,#56] *)
tc_one_instruction2_by_bin "b9803be0";
(*   20:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(*   24:   f94007e1        ldr     x1, [sp,#8] *)
tc_one_instruction2_by_bin "f94007e1";
(*   28:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(*   2c:   7900001f        strh    wzr, [x0] *)
tc_one_instruction2_by_bin "7900001f";
(*   30:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(*   34:   11000400        add     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "11000400";
(*   38:   b9003be0        str     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9003be0";
(*   3c:   b94007e0        ldr     w0, [sp,#4] *)
tc_one_instruction2_by_bin "b94007e0";
(*   40:   531f7801        lsl     w1, w0, #1 *)
tc_one_instruction2_by_bin "531f7801";
(*   44:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(*   48:   6b00003f        cmp     w1, w0 *)
tc_one_instruction2_by_bin "6b00003f";
(* OK, even if in CMP we are currently cheating *)

(* 4c:   54fffe8c        b.gt    1c <internal_mul+0x1c> *)
tc_one_instruction2_by_bin "54fffe8c";
(* 50:   b94007e0        ldr     w0, [sp,#4] *)
tc_one_instruction2_by_bin "b94007e0";
(* 54:   51000400        sub     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "51000400";
(* 58:   b9003fe0        str     w0, [sp,#60] *)
tc_one_instruction2_by_bin "b9003fe0";
(* 5c:   14000043        b       168 <internal_mul+0x168> *)
tc_one_instruction2_by_bin "14000043";
(* 60:   b9803fe0        ldrsw   x0, [sp,#60] *)
tc_one_instruction2_by_bin "b9803fe0";
(* 64:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* 68:   f9400fe1        ldr     x1, [sp,#24] *)
tc_one_instruction2_by_bin "f9400fe1";
(* 6c:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* 70:   79400000        ldrh    w0, [x0] *)
tc_one_instruction2_by_bin "79400000";
(* 74:   53003c00        uxth    w0, w0 *)
tc_one_instruction2_by_bin "53003c00";
(* 78:   f90017e0        str     x0, [sp,#40] *)
tc_one_instruction2_by_bin "f90017e0";
(* 7c:   f9001bff        str     xzr, [sp,#48] *)
tc_one_instruction2_by_bin "f9001bff";
(* 80:   b94007e0        ldr     w0, [sp,#4] *)
tc_one_instruction2_by_bin "b94007e0";
(* 84:   51000400        sub     w0, w0, #0x1 *)
tc_one_instruction2_by_bin "51000400";
(* 88:   b9003be0        str     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9003be0";
(* 8c:   1400002a        b       134 <internal_mul+0x134> *)
tc_one_instruction2_by_bin "1400002a";
(* 90:   b9803be0        ldrsw   x0, [sp,#56] *)
tc_one_instruction2_by_bin "b9803be0";
(* 94:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* 98:   f9400be1        ldr     x1, [sp,#16] *)
tc_one_instruction2_by_bin "f9400be1";
(* 9c:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* a0:   79400000        ldrh    w0, [x0] *)
tc_one_instruction2_by_bin "79400000";
(* a4:   53003c01        uxth    w1, w0 *)
tc_one_instruction2_by_bin "53003c01";
(* a8:   f94017e0        ldr     x0, [sp,#40] *)
tc_one_instruction2_by_bin "f94017e0";
(* ac:   9b007c20        mul     x0, x1, x0 *)
tc_one_instruction2_by_bin "9b007c20";
(* b0:   f9401be1        ldr     x1, [sp,#48] *)
tc_one_instruction2_by_bin "f9401be1";
(* b4:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* b8:   f9001be0        str     x0, [sp,#48] *)
tc_one_instruction2_by_bin "f9001be0";
(* bc:   b9403fe1        ldr     w1, [sp,#60] *)
tc_one_instruction2_by_bin "b9403fe1";
(* c0:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(* c4:   0b000020        add     w0, w1, w0 *)
tc_one_instruction2_by_bin "0b000020";
(* c8:   93407c00        sxtw    x0, w0 *)
tc_one_instruction2_by_bin "93407c00";
(* cc:   91000400        add     x0, x0, #0x1 *)
tc_one_instruction2_by_bin "91000400";
(* d0:   d37ff800        lsl     x0, x0, #1 *)
tc_one_instruction2_by_bin "d37ff800";
(* d4:   f94007e1        ldr     x1, [sp,#8] *)
tc_one_instruction2_by_bin "f94007e1";
(* d8:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* dc:   79400000        ldrh    w0, [x0] *)
tc_one_instruction2_by_bin "79400000";
(* e0:   53003c00        uxth    w0, w0 *)
tc_one_instruction2_by_bin "53003c00";
(* e4:   f9401be1        ldr     x1, [sp,#48] *)
tc_one_instruction2_by_bin "f9401be1";
(* e8:   8b000020        add     x0, x1, x0 *)
tc_one_instruction2_by_bin "8b000020";
(* ec:   f9001be0        str     x0, [sp,#48] *)
tc_one_instruction2_by_bin "f9001be0";
(* f0:   b9403fe1        ldr     w1, [sp,#60] *)
tc_one_instruction2_by_bin "b9403fe1";
(* f4:   b9403be0        ldr     w0, [sp,#56] *)
tc_one_instruction2_by_bin "b9403be0";
(* f8:   0b000020        add     w0, w1, w0 *)
tc_one_instruction2_by_bin "0b000020";
(* fc:   93407c00        sxtw    x0, w0 *)
tc_one_instruction2_by_bin "93407c00";





(*   20:   d37ff800        lsl     x0, x0, #1 *)
val [t] = arm8_step_hex "d37ff800";
val instr = "d37ff800";


val ass_some = (List.filter (fn tm =>
    (is_eq tm) andalso ((optionLib.is_some o snd o dest_eq) tm) andalso ((optionLib.is_some o snd o dest_eq) tm)
) (hyp t));
val ass_some = List.map (SIMP_CONV (srw_ss()) []) ass_some;
val t1 = List.foldl (fn (thm, main_thm) => (DISCH ((fst o dest_eq o concl) thm) main_thm)) t ass_some;
val t2 = REWRITE_RULE ass_some t1;
val [t3] = IMP_CANON t2;
val t4 = UNDISCH_ALL t3;
val t5 = SIMP_RULE (bool_ss) [] t4;

val ass_const = (List.filter (fn tm =>
    (is_eq tm) andalso ((wordsSyntax.is_n2w o fst o dest_eq) tm)
) (hyp t5));
val ass_const = List.map (SYM o ASSUME) ass_const;
val t6 = REWRITE_RULE ass_const t5;

val upds = ((extract_arm8_changes o optionSyntax.dest_some o snd o dest_comb o concl) t6);
val exp = snd(List.nth(upds, 1));
tc_exp_arm8 exp;

