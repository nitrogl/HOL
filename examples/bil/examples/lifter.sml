(* You should open emacs from ../arm8bil *)

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

(* overflows *)
tc_exp_arm8 ``T``;
tc_exp_arm8 ``aaa.REG 1w``;
tc_exp_arm8 ``(aaa.REG 1w) + (aaa.REG 2w)``;
tc_exp_arm8 ``(aaa.REG 1w) * (aaa.REG 1w)``;
tc_exp_arm8 ``(aaa.REG 2w) + 3w``;
tc_exp_arm8 ``(aaa.REG 2w) >=+ 3w``;
tc_exp_arm8 ``T /\ F``;
tc_exp_arm8 ``T /\ (aaa.PSTATE.Z)``;
tc_exp_arm8 ``~(aaa.PSTATE.Z)``;
tc_exp_arm8 ``if T then F else T``;
tc_exp_arm8 ``if T then (aaa.REG 2w) + 3w else 2w``;

val [t1] = arm8_step_hex "0x910003e1";  (* mov     x1, sp *)
tc_exp_arm8 ``s.PC + 4w``;
tc_exp_arm8 ``s.SP_EL0 + 0w``;

(* From the manual  *)
(* https://www.element14.com/community/servlet/JiveServlet/previewBody/41836-102-1-229511/ARM.Reference_Manual.pdf *)

(* add 32-bit register  *)
arm8_step_code `ADD W0, W1, W2`;
tc_exp_arm8 ``(w2w
              ((w2w (s.REG (1w :word5)) :word32) +
               (w2w (s.REG (2w :word5)) :word32)) :word64)``;
(* FAILURE *)

(* 64-bit addition *)
arm8_step_code `ADD X0, X1, X2`;
tc_exp_arm8 `` s.REG 1w + s.REG 2w``;

(* add 64-bit extending register  *)
arm8_step_code `ADD X0, X1, W2, SXTW `;
tc_exp_arm8 ``s.REG 1w + ExtendValue (s.REG 2w,ExtendType_SXTW,0)``;
(* FAILURE *)

(* add 64-bit immediate  *)
arm8_step_code `ADD X0, X1, #42 `;
tc_exp_arm8 ``s.REG 1w + 42w``;

(* Absolute branch to address in Xn *)
arm8_step_code `BR X0`;
arm8_step_code `BLR X0`;

tc_exp_arm8 ``s.PC + 4w``;

arm8_step_code `B #4`;

(* Arithmetics instructions *)
arm8_step_code `ADD W0, W1, W2, LSL #3`;
(* still problems with 32 bits *)

(* Guancio: my first extension *)
arm8_step_code `SUB X0, X4, X3, ASR #2`;
tc_exp_arm8 ``s.REG 4w − s.REG 3w ≫ 2``;

val ae = ``s.REG 3w ≫ 2``;
tc_exp_arm8 ae;

val t = prove(``2 = w2n (2w:word64)``, (FULL_SIMP_TAC (srw_ss()) []));
val ae1 = (snd o dest_eq o concl) (REWRITE_CONV [Once t] ae);
val ae2 = (snd o dest_eq o concl) (REWRITE_CONV [(GSYM wordsTheory.word_asr_bv_def)] ae1);
(* val ae2 = (snd o dest_eq o concl) (REWRITE_CONV [Once t, (GSYM wordsTheory.word_asr_bv_def)] ae1); *)
tc_exp_arm8 ae2;

(* FLAGS *)

val [[t]] = arm8_step_code `ADDS X1, X2, X3 `;
val s1 = (snd o dest_comb o snd o dest_eq o concl) t;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.V``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.Z``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.N``;
tc_exp_arm8 exp;

arm8_step_code `CMP W3, W4 `;
val [[t]] = arm8_step_code `CMP X3, X4 `;
val s1 = (snd o dest_comb o snd o dest_eq o concl) t;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.V``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.C``;
tc_exp_arm8 exp;

val new_exp_thm = (SIMP_CONV (myss) [
      			(* These are for the C flag in addittion *)
      			carry_thm, plus_lt_2exp64_tm, minus_lt_2exp64_tm,
      			(* These are for the V flag in addittion *)
      			BIT63_thm, Bword_add_64_thm] exp);
val ae1 = (snd o dest_eq o concl) new_exp_thm;
tc_exp_arm8 ae1;

val plus1_lt_2exp64_tm = GSYM (tryprove(
    ``∀ x y . 
      (((x // 2w) + (y // 2w) + (word_mod x 2w) * (word_mod y 2w)) <+
       (9223372036854775808w:word64)) =
      (w2n x + w2n (~y) + 1 < 18446744073709551616)
    ``,
	(REPEAT STRIP_TAC)
	THEN (EVAL_TAC)
	THEN ((FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS, DIV_PRODMOD_LT_2EXP]))
	THEN  (FULL_SIMP_TAC (pure_ss) [prove(``(18446744073709551616:num) = 2 ** SUC 63``, EVAL_TAC), SPECL [``63:num``, ``w2n(x:word64)``, ``w2n(y:word64)``] SUM_2EXP_EQ])
	THEN (ASSUME_TAC (SPECL [``63:num``, ``w2n(x:word64)``, ``w2n(y:word64)``] DIV_PRODMOD_LT_2EXP))
	THEN (ASSUME_TAC (ISPEC ``x:word64`` wordsTheory.w2n_lt))
	THEN (ASSUME_TAC (ISPEC ``y:word64`` wordsTheory.w2n_lt))
	THEN (FULL_SIMP_TAC (srw_ss()) [wordsTheory.dimword_64])
	THEN ((FULL_SIMP_TAC (arith_ss) []))
));




val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.Z``;
tc_exp_arm8 exp;
val exp = (snd o dest_eq o concl o EVAL) ``^s1.PSTATE.N``;
tc_exp_arm8 exp;
(* TODO *)





(* BINARY OPERATIONS *)

arm8_step_code `BIC X0, X0, X1 `;
tc_exp_arm8 ``s.REG 0w && ¬s.REG 1w``;

arm8_step_code `SUB X0, X4, X3`;
tc_exp_arm8 ``s.REG 4w − s.REG 3w``;

arm8_step_code `SUBS X0, X4, X3`;

tc_exp_arm8 ``
((word_msb (s.REG 4w) ⇔ word_msb (¬s.REG 3w)) ∧
               (word_msb (s.REG 4w) ⇎
                BIT 63 (w2n (s.REG 4w) + w2n (¬s.REG 3w) + 1)))``;
(* WHY WE HAVE W2N IN THE HYPOTESYS? *)


arm8_step_code `CSINC X0, X1, X0, NE`;
tc_exp_arm8 ``
if ¬s.PSTATE.Z then s.REG 1w else s.REG 0w + 1w
``;


(* UNSUPPORTED *)
arm8_step_code `LDRB X0, [X1]`;

arm8_step_code `LDRSB X0, [X1]`;

tc_exp_arm8 ``sw2sw (s.MEM (s.REG 1w + 0w)):word64``;
tc_exp_arm8 ``(w2w (0w:word8)):word64``;
tc_exp_arm8 ``(w2n (0w:word8))``;
tc_exp_arm8 ``(sw2sw (0w:word8)):word64``;
tc_exp_arm8 ``s.MEM (0w:word64)``;
tc_exp_arm8 ``s.MEM (s.REG 1w + 0w)``;

(* memory should use an existential quantifier *)
tc_exp_arm8 ``s.MEM (0w:word64) + 2w``;


(* NO THEOREM WORKS IN 8bit? *)

tc_exp_arm8 ``s.MEM (0w:word64) + (if (s.REG 1w) = 1w then 0w else 1w)``;

(* LOAD OF A WORLD *)
val [[t]] = arm8_step_code `LDR X0, [X1]`;
val s1 = (snd o dest_comb o snd o dest_eq o concl) t;
val exp = (snd o dest_eq o concl o (computeLib.RESTR_EVAL_CONV [``mem_dword``])) ``^s1.REG 0w``;
tc_exp_arm8 exp;


val prefix = "";
val ae = exp;
