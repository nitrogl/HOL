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

(* COMPARISON *)

arm8_step_code `CMP W3, W4 `;
arm8_step_code `CMP X3, X4 `;

tc_exp_arm8 ``((word_msb (s.REG 3w) ⇔ word_msb (¬s.REG 4w)) ∧
               (word_msb (s.REG 3w) ⇎
                BIT 63 (w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1)))``;

tc_exp_arm8 ``
((if
                  w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1 <
                  18446744073709551616
                then
                  w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1
                else
                  (w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1) MOD
                  18446744073709551616) ≠
               w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1)
``;

tc_exp_arm8 ``(s.REG 3w − s.REG 4w = 0w)``;

tc_exp_arm8 ``word_msb (s.REG 3w − s.REG 4w)``;

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

tc_exp_arm8 ``s.MEM (0w:word64) + 2w``;
(* NO THEOREM WORKS IN 8bit? *)

tc_exp_arm8 ``s.MEM (0w:word64) + (if (s.REG 1w) = 1w then 0w else 1w)``;

(* LOAD OF A WORLD *)
arm8_step_code `LDR X0, [X1]`;

tc_exp_arm8 ``mem_dword s.MEM (s.REG 1w + 0w)``;
tc_exp_arm8 ``(mem_dword s.MEM (s.REG 1w + 0w)) + (s.REG 2w)``;

arm8_step_code `ADD W0, W1, W2`;
tc_exp_arm8 ``(w2w
              ((w2w (s.REG (1w :word5)) :word32) +
               (w2w (s.REG (2w :word5)) :word32)) :word64)``;

tc_exp_arm8 ``(w2w ((5w :word32) + (5w :word32)) :word64)``;



