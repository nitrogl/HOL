(* ========================================================================= *)
(* FILE          : arm8bilScript.sml                                         *)
(* DESCRIPTION   : A transcompiler from arm8model to BIL model.              *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

loadPath := "/opt/hol_snapshot/examples/l3-machine-code/common" :: !loadPath;
loadPath := "/opt/hol_snapshot/examples/l3-machine-code/arm8" :: !loadPath;
loadPath := "/opt/hol_snapshot/examples/l3-machine-code/arm8/model" :: !loadPath;
loadPath := "/opt/hol_snapshot/examples/l3-machine-code/arm8/step" :: !loadPath;

open HolKernel boolLib bossLib;
load "lcsymtacs";
load "utilsLib";
open lcsymtacs utilsLib;
open wordsLib blastLib;
load "updateTheory";
load "arm8Theory";
open state_transformerTheory updateTheory arm8Theory;
load "stateTheory";
open stateTheory;
load "arm8_stepTheory";
open lcsymtacs arm8_stepTheory;
(*open  arm_configLib; *)
load "state_transformerSyntax";
open state_transformerSyntax;
load "arm8_stepLib";
open arm8_stepLib;

load "arithmeticTheory";
load "wordsTheory";
load "fcpTheory";
load "bitTheory";
load "blastLib";
load "sum_numTheory";
load "pred_setTheory";
open wordsLib;

(* load BIL bla bla *)
(* load "bilTheory"; *)
(* open bilTheory; *)
use "/NOBACKUP/workspaces/rmet/verified_lifter/bil/bilsyntax.sml";
use "/NOBACKUP/workspaces/rmet/verified_lifter/bil/bilsemantics.sml";

val _ = new_theory "arm8bil";
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  Exceptions                                                               *)
(* ------------------------------------------------------------------------- *)
exception NotABoolException;
exception NotANumberException;
exception NotAWordException;
exception UnsupportedWordSizeException;
exception UnsupportedARM8ExpressionException of term;
exception ArgumentException of string;
exception ProveException of term * string;

(* ------------------------------------------------------------------------- *)
(*  Misc tools                                                               *)
(* ------------------------------------------------------------------------- *)
fun eval t = (snd o dest_eq o concl o EVAL) t;
fun opname t = (fst o dest_const o fst o strip_comb) t;
fun REPEATN (n, tac) = EVERY (List.tabulate (n, fn n => tac));
val EVALBOOL = (EQT_ELIM o EVAL);
fun MP_NOFAIL th1 th2 = MP th1 th2 handle e => th1;
val SPECX = (snd o SPEC_VAR);

(* Conjunction of list elements *)
val CONJL = fn lst =>
  if (List.length lst = 0)
    then TRUTH
    else
      let
        val thm1::thms = lst
        fun conjl lst thm = case lst of
            []   => thm
          | e::l => conjl l (CONJ e thm)
      in
        conjl thms thm1
      end
;

(* Just generalize/specialize the environment *)
val SPEC_ENV = SPEC ``env:environment``;
val GEN_ENV = GEN ``env:environment``;

(*
  MP on conjunctions:
  
      A1 |- t1 /\ t2 ==> t2   A2 |- t1   A3 |- t2
   --------------------------------------------------  MP
        A1 u A2 u A3 |- t2
*)
fun MP_CONJL thImp l = MP thImp (CONJL l);
fun MP_CONJ thImp (thm1, thm2) = MP thImp (CONJ thm1 thm2);

(* Modus Ponens for binary expressions *)
fun MP_UN      thImp (be1, ae1, thm1) = 
  MP (((SPECL [ae1, be1]) o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1)
;

fun MP_NUM_UN  thImp (be1, ae1, thm1) = 
  MP ((UNDISCH o (SPECL [ae1, be1]) o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1)
;

fun MP_BIN     thImp (be1, ae1, thm1) (be2, ae2, thm2) = 
  MP_CONJ ((SPECL [ae1, ae2, be1, be2] o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2)
;

fun MP_NUM_BIN thImp (be1, ae1, thm1) (be2, ae2, thm2) =
  MP_CONJ ((UNDISCH o UNDISCH o (SPECL [ae1, ae2, be1, be2]) o SPEC_ENV) thImp) ((UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2)
;

fun MP_NUM_ITE thImp (be1, ae1, thm1) (be2, ae2, thm2) (be3, ae3, thm3) = 
  MP_CONJL ((UNDISCH o UNDISCH o (SPECL [ae1, ae2, ae3, be1, be2, be3]) o SPEC_ENV) thImp) (List.rev [(UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2, (UNDISCH_ALL o SPEC_ALL) thm3])
;

(* This version needs to proove something... this is not good... *)
fun MP_NUM_BIN_OLD thImp (be1, ae1, thm1) (be2, ae2, thm2) =
  let
    val thm1_open  = (concl o UNDISCH_ALL o SPEC_ALL) thm1;
    val thm2_open  = (concl o UNDISCH_ALL o SPEC_ALL) thm2;
    val (c11, c12) = if (boolSyntax.is_imp thm1_open) then (dest_imp thm1_open) else (``^ae1 < dimword (:64)``, thm1_open);
    val (c21, c22) = if (boolSyntax.is_imp thm2_open) then (dest_imp thm2_open) else (``^ae2 < dimword (:64)``, thm2_open);
    val cl = List.concat [
      (CONJUNCTS o UNDISCH_ALL o SPEC_ALL) (tryprove(``^c11 ∧ ^c12``, EVAL_TAC)),
      (CONJUNCTS o UNDISCH_ALL o SPEC_ALL) (tryprove(``^c21 ∧ ^c22``, EVAL_TAC))
    ];
  in
    MP_CONJL ((SPECL [ae1, ae2, be1, be2] o SPEC_ENV) thImp) (List.rev cl)
  end
;
fun MPL impTh lst = case lst of
    []    => impTh
  | e::l  => MPL (MP impTh e) l
;

(*---------------------------------------------------------------------------*
 *  Discharge all hypotheses in reverse order                                *
 *                                                                           *
 *       t1, ... , tn |- t                                                   *
 *  ------------------------------                                           *
 *    |- t1 ==> ... ==> tn ==> t                                             *
 *---------------------------------------------------------------------------*)
fun DISCH_ALL_REV th = HOLset.foldr (Lib.uncurry DISCH) th (hypset th);

(*---------------------------------------------------------------------------*
 *  Convert a conjunctive implication antecedent to a cascade of             *
 *  implications.                                                             *
 *                                                                           *
 *       |- t1 /\ t2 /\ ... /\ tn => t                                       *
 *  -----------------------------------------------                          *
 *    |- t1 ==> (t2 ==> (... ==> tn ==> (t))...)                             *
 *---------------------------------------------------------------------------*)
fun CONJ_IMP t = 
  let
    val th = (DISCH_ALL o SPEC_ALL o UNDISCH_ALL) t;
    val conclusion = concl th;
  in
    if (boolSyntax.is_imp conclusion)
    then
      let
        val (preimp, _) = dest_imp conclusion;
      in
        if (boolSyntax.is_conj preimp)
          then
            let
              val cl = (List.rev o strip_conj) preimp;
            in
              (DISCH_ALL_REV (MP_CONJL th (List.map (fn x => ASSUME x) cl)))
            end
          else  t
      end
    else  t
  end
;

fun imp_extract th =
  let
    fun hh conclusion hs = if (is_imp conclusion)
      then hh ((snd o dest_imp) conclusion) (List.concat [hs, [((fst o dest_imp) conclusion)]])
      else hs
  in
    hh ((concl o DISCH_ALL o SPEC_ALL) th) []
  end
;

val dupe_theorem = prove(``F ==> T``, EVAL_TAC);
fun dupe_prove t =
  let
    val tac =       EVAL_TAC
              THEN  (RW_TAC (pure_ss) []) THEN (RW_TAC (arith_ss) []) THEN (RW_TAC (srw_ss()) [])
              THEN  (SIMP_TAC (bool_ss) []) THEN (SIMP_TAC (arith_ss) []) THEN (SIMP_TAC (srw_ss()) [])
              THEN  (FULL_SIMP_TAC (arith_ss) []) THEN (FULL_SIMP_TAC (srw_ss()) []);
    val goal = ([], t);
    fun dp (goal, tac) =
      case tac goal of
          ([], proof) => (
              let
                val theorem    = proof []
                val conclusion = concl theorem
              in
                if conclusion = snd goal
                  then theorem
                  else EQ_MP (ALPHA conclusion (snd goal)) theorem
              end handle e => dupe_theorem
            )
        | (_, _)      => dupe_theorem;
  in
    dp (goal, tac)
  end
;

fun DISPOSE_HYP th =
  let
    (* ordered subset of proved hypoteses *)
    val ths = filter (fn t => not ((concl t) = (concl dupe_theorem))) (map (fn t => dupe_prove t) (imp_extract th));
    fun d th ths = case ths of
        []    => th
      | t::ts =>
          let
            val (mp, nts) = (MP th t, ts) handle e => (UNDISCH th, ths);
          in
            d mp nts
          end
  in
    d ((DISCH_ALL o SPEC_ALL) th) ths
  end
;


(*
  Wrapper of prove function.
  It raises a ProveException if unable to prove, showing the initial
  goal (pretty printed).
*)
val tryprove = fn (goal, tac) => (prove(goal, tac))
    handle HOL_ERR {message: string, origin_function: string, origin_structure: string} => raise ProveException(goal, message)
;

(* ------------------------------------------------------------------------- *)
(*  Type and size utils                                                      *)
(* ------------------------------------------------------------------------- *)
(* Register constructors and corresponding sizes *)
val constructor_size_pairs = [
      (``Reg1  ``, 1 )
    , (``Reg8  ``, 8 )
    , (``Reg16 ``, 16)
    , (``Reg32 ``, 32)
    , (``Reg64 ``, 64)
  ];


val word_size = fn t =>
  if (wordsSyntax.is_word_type (type_of t))
    then
      let
        val nt = eval ``word_len ^t``
      in
              if (nt =  ``1:num``)                 then  1
        else  if (nt =  ``8:num``)                 then  8
        else  if (nt = ``16:num``)                 then  16
        else  if (nt = ``32:num``)                 then  32
        else  if (nt = ``64:num``)                 then  64
        else  if (numSyntax.is_numeral nt = false) then  (say "Working with generic words!?";0)
        else  raise UnsupportedWordSizeException
      end
    else raise NotAWordException
;

val word_type_size = fn t =>
  if (wordsSyntax.is_word_type t)
    then word_size (wordsSyntax.mk_n2w (``0:num``, t))
    else raise ArgumentException("Not a word type")
;

val get_alphatype = fn ty =>
  if (wordsSyntax.is_word_type ty)
    then List.nth (snd(dest_type ty), 1)
    else raise NotAWordException;


(* ------------------------------------------------------------------------- *)
(*  Expression tests                                                         *)
(* ------------------------------------------------------------------------- *)
fun is_arm8_app t cmp =
  let
    val dummystate = ``ds:arm8_state``;
    val godeep = fn t => (snd o dest_comb) t;
    val subst1 = fn t => subst [godeep t |-> dummystate] t;
    val subst2 = fn t => (subst [(godeep o fst o dest_comb) t |-> dummystate] o fst o dest_comb) t;
  in
            (is_comb t)
    andalso (
                  (subst1 t = subst1 cmp)
      handle _ => (subst2 t = subst1 cmp)
      handle _ => false
    )
  end
;
val is_bool = fn t => (type_of t) = ``:bool``;
val is_num  = fn t => (type_of t) = ``:num``;
val is_reg  = fn t => is_arm8_app t ``s.REG``;
val is_mem  = fn t => is_arm8_app t ``s.MEM``;
val is_boolean  = fn t => (t = ``T``) orelse (t = ``F``);
val is_eq_bool = fn t => (is_comb t) andalso (boolSyntax.is_eq t) andalso (List.nth ((snd o dest_type o type_of o fst o strip_comb) t, 0)) = ``:bool``;
val is_eq_num  = fn t => (is_comb t) andalso (boolSyntax.is_eq t) andalso (List.nth ((snd o dest_type o type_of o fst o strip_comb) t, 0)) = ``:num``;

val is_neq = fn t => if (boolSyntax.is_neg t)
  then
    boolSyntax.is_eq (List.nth ((snd o strip_comb) t, 0))
  else
    false
;

val is_word_eq = fn t => if (boolSyntax.is_eq t)
  then
    let
      val types = (snd o dest_type o type_of o fst o strip_comb) t
    in
      if (List.length types > 0)
        then
          wordsSyntax.is_word_type (List.nth(types, 0))
        else
          false
    end
  else
    false
;

(* This is to overload the combination not-equal, in order to have easier conversions to NotEqual in BIL model *)
val word_neq_def = Define `word_neq (a:α word) (b:α word) = ~(a = b)`;
val _ = overload_on ("≠",              Term`$word_neq`);

val is_word_neq = fn t => if (boolSyntax.is_neg t)
  then
    is_word_eq (List.nth ((snd o strip_comb) t, 0))
  else
    false
;

(*
  This function is used to detect carry bit.
  The main problem of this typical arm8 expression to compute the carry bit
  is that in BIL we cannot handle more than 64 bits, but this expression
  uses exactly 2**64, the smallest non-representable in BIL natural number.
*)
val is_plus_lt_2exp64 = fn t =>
  if (numSyntax.is_less t)
  then
    let
      val tplus = (List.nth ((snd o strip_comb) t, 0));
      val t2exp = (List.nth ((snd o strip_comb) t, 1));
    in
      (numSyntax.is_plus tplus) andalso ((eval t2exp) = (eval ``(2:num) ** 64``))
    end
  else
    false
;

(*
  Another annoying structure found through the armv8 expressions
  is the MOD 2**64
*)
val is_mod_2exp64 = fn t =>
  if (numSyntax.is_mod t)
  then
    let
      val t2exp = (List.nth ((snd o strip_comb) t, 1));
    in
      (eval t2exp) = (eval ``(2:num) ** 64``)
    end
  else
    false
;


(*
  WARNING: NOT SUPPORTED FIELDS
  
  ("MEM",ATy(F64,F8))
  ("branch_hint",OTy(CTy"BranchType"))
  ("exception",CTy"exception")])
*)
val arm8_supported_den = fn a8s => [
      ``^(a8s).PC
      
  ``, ``^(a8s).PSTATE.C
  ``, ``^(a8s).PSTATE.EL
  ``, ``^(a8s).PSTATE.N
  ``, ``^(a8s).PSTATE.SPS
  ``, ``^(a8s).PSTATE.V
  ``, ``^(a8s).PSTATE.Z
  ``, ``^(a8s).PSTATE.Z
      
  ``(*, ``^(a8s).SP_EL0
  ``, ``^(a8s).SP_EL1
  ``, ``^(a8s).SP_EL2
  ``, ``^(a8s).SP_EL3
      
  ``, ``^(a8s).TCR_EL1.TBI0
  ``, ``^(a8s).TCR_EL1.TBI1
  ``, ``^(a8s).TCR_EL1.tcr_el1'rst
      
  ``, ``^(a8s).TCR_EL2.TBI
  ``, ``^(a8s).TCR_EL2.tcr_el2_el3'rst
      
  ``, ``^(a8s).TCR_EL3.TBI
  ``, ``^(a8s).TCR_EL3.tcr_el2_el3'rst
      
  ``, ``^(a8s).SCTLR_EL1.A
  ``, ``^(a8s).SCTLR_EL1.E0E
  ``, ``^(a8s).SCTLR_EL1.EE
  ``, ``^(a8s).SCTLR_EL1.SA
  ``, ``^(a8s).SCTLR_EL1.SA0
  ``, ``^(a8s).SCTLR_EL1.sctlrtype'rst
      
  ``, ``^(a8s).SCTLR_EL2.A
  ``, ``^(a8s).SCTLR_EL2.E0E
  ``, ``^(a8s).SCTLR_EL2.EE
  ``, ``^(a8s).SCTLR_EL2.SA
  ``, ``^(a8s).SCTLR_EL2.SA0
  ``, ``^(a8s).SCTLR_EL2.sctlrtype'rst
      
  ``, ``^(a8s).SCTLR_EL3.A
  ``, ``^(a8s).SCTLR_EL3.E0E
  ``, ``^(a8s).SCTLR_EL3.EE
  ``, ``^(a8s).SCTLR_EL3.SA
  ``, ``^(a8s).SCTLR_EL3.SA0
  ``, ``^(a8s).SCTLR_EL3.sctlrtype'rst
  
  `` *)
];


val is_arm8_den = fn t =>
  let
    val dummystate = ``ds:arm8_state``;
    val godeep = fn t => (snd o dest_comb) t;
    val subst1 = fn t => subst [godeep t |-> dummystate] t;
    val subst2 = fn t => subst [(godeep o godeep) t |-> dummystate] t;
    val st     = fn t => (subst1 t) handle _ => (subst2 t) handle _ => t;
  in
    (List.length o List.filter (fn x => x = st t) o map (fn x => st x)) (arm8_supported_den dummystate) = 1
  end
;

(* ------------------------------------------------------------------------- *)
(*  Raw conversion of several types to BIL model expressions                 *)
(* ------------------------------------------------------------------------- *)
val bil_expr_const_bool = fn t =>
  if  t then ``(Const (Reg1 1w))``
        else ``(Const (Reg1 0w))``;

val bil_expr_const = fn t =>
  let
    val s = word_size t
  in
    case s of
        0  => ``(Const (Reg64 (w2w ^t)))`` (* Encapsulate a generic α word to maximum size (worst choice?) *)
      | 1  => ``(Const (Reg1  ^t))``
      | 8  => ``(Const (Reg8  ^t))``
      | 16 => ``(Const (Reg16 ^t))``
      | 32 => ``(Const (Reg32 ^t))``
      | 64 => ``(Const (Reg64 ^t))``
      | _  => raise UnsupportedWordSizeException
  end
;

val bil_expr_bool = fn t =>
        if (t = ``T`` orelse t = ``F``) then ``Const (bool2b ^t)``
  else  raise NotABoolException
;

val bil_expr_num = fn t =>
  if (numSyntax.is_numeral t)
    then ``Cast (Const (n2b ^t)) Bit64``
    else raise NotANumberException
;

val r2s_def = Define `r2s = λ(w:bool[5]).STRCAT ("R") (w2s (10:num) HEX w)`;

val bil_a8e2HOLstring = fn t =>
        if (is_reg t) then ``r2s ^((snd o dest_comb) t)``
  else  stringSyntax.fromMLstring (opname t)
;

val bil_a8e2string = fn t =>
        if (is_reg t) then stringSyntax.fromHOLstring (eval ``r2s ^((snd o dest_comb) t)``)
  else  opname t
;

val bil_a8e_den = fn t => ``(Den ^(bil_a8e2HOLstring t))``;

(* ------------------------------------------------------------------------- *)
(*  Conversion of several types to BIL model values                          *)
(* ------------------------------------------------------------------------- *)
fun bil_value_word_encapsulate t ws =
        if (ws  = 0)  then ``(Int (Reg64 (w2w ^t)))`` (* Encapsulate a generic α word to maximum size (worst choice?) *)
  else  if (ws <= 1)  then ``(Int (Reg1  ^t))``
  else  if (ws <= 8)  then ``(Int (Reg8  ^t))``
  else  if (ws <= 16) then ``(Int (Reg16 ^t))``
  else  if (ws <= 32) then ``(Int (Reg32 ^t))``
  else  if (ws <= 64) then ``(Int (Reg64 ^t))``
  else  raise UnsupportedWordSizeException
;

val bil_value_word = fn t => bil_value_word_encapsulate t (word_size t);

val bil_value_bool = fn t =>
  if (is_bool t)
    then ``(Int (bool2b ^t))``
    else  raise NotABoolException
;

val bil_value_num = fn t =>
  if (is_num t)
    then  ``(Int (n2b_64 ^t))``
    else  raise NotANumberException
;

val bil_value_reg = fn t =>
  if (is_reg t)
    then ``Int (Reg64 t)``
    else  raise ArgumentException "Argument is not a register"
;

val bil_value =
      fn t                             => bil_value_bool t
  handle NotABoolException             => bil_value_num  t
  handle NotANumberException           => bil_value_word t
  handle UnsupportedWordSizeException  => bil_value_reg  t
  handle ArgumentException _           => if (wordsSyntax.is_word_type (type_of t))
                                            then ``Int (w2b ^t)``
                                            else raise NotAWordException
;


(* ------------------------------------------------------------------------- *)
(*  Theorems - Supporting important theorems                                 *)
(* ------------------------------------------------------------------------- *)

val SUC_INC = prove(``∀n. SUC n = n + 1``, numLib.ARITH_TAC);
val ADDSUB_COMM = prove(``∀(n:num) (h:num). (h <= n) ==> (n + h - h = n - h + h)``, numLib.ARITH_TAC);
val PREC_EXISTS = prove(
    ``∀ (n:num). (0 < n) ==> (∃m. n = m + 1)``
  ,       (REPEAT STRIP_TAC)
    THEN  (EXISTS_TAC ``(n:num) - 1``)
    THEN  (RW_TAC (arith_ss) []) 
);

val MULT_MOD2_01 = prove(``∀ (j:num) (k:num). (j MOD 2 * k MOD 2 = 0) ∨ (j MOD 2 * k MOD 2 = 1)``, (RW_TAC (srw_ss()) [arithmeticTheory.MOD_2]));

(* This theorem comes from ARMv7 lifter by Hamed Nemati *)
val BIT_DIV_MOD = prove(
    ``∀ (n:num) (h:num). BIT h n = ((n DIV 2**h) MOD 2 = 1)``
  , (RW_TAC (srw_ss()) [bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def, bitTheory.BIT_def, bitTheory.BITS_def, SUC_INC])
);

val MOD_LESS_ALT = prove(
    ``∀ (j:num) (n:num) (m:num). (0 < n) ==> ((n <= m) ==> (j MOD n < m))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPECL [``j:num``, ``n:num``])) arithmeticTheory.MOD_LESS))
    THEN  (FULL_SIMP_TAC (arith_ss) [])
);

val BITS_LT_2EXP = prove(
    ``∀ (h:num) (j:num) (k:num). BITS h j k < 2**(SUC h)``
  , (RW_TAC (arith_ss) [bitTheory.MOD_2EXP_def, bitTheory.BITS_def, MOD_LESS_ALT])
);

val MOD_LESS_ALT = prove(
    ``∀ (j:num) (n:num) (m:num). (0 < n) ==> ((n <= m) ==> (j MOD n < m))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPECL [``j:num``, ``n:num``])) arithmeticTheory.MOD_LESS))
    THEN  (FULL_SIMP_TAC (arith_ss) [])
);

val MODN_MODM = prove(
    ``∀n k m. (0 < n) ==> ((n <= m) ==> (k MOD n MOD m = k MOD n))``
  , (RW_TAC (srw_ss()) [MOD_LESS_ALT])
);

val EXP_LT_ALT = prove(
    ``∀ (n:num) (m:num) (j:num). ((j < 2**n) ==> ((j DIV 2**m) < 2**(n - m)))``
  ,       (REPEAT STRIP_TAC)
    THEN  (Cases_on `(n:num) <= m`)
    THENL [
            (ASSUME_TAC ((UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``n:num``, ``m:num``])) arithmeticTheory.SUB_EQ_0))
      THEN  (ASSUME_TAC ((UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``m:num``, ``n:num``])) (DISPOSE_HYP (SPEC ``2:num`` arithmeticTheory.EXP_BASE_LE_MONO))))
      THEN  (SIMP_TAC (arith_ss) [arithmeticTheory.DIV_LT_X, GSYM arithmeticTheory.EXP_BASE_LE_MONO])
      THEN  (RW_TAC (arith_ss) [])
    ,       (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.EXP_ADD, arithmeticTheory.DIV_LT_X])
    ]
);

val n2w_w2w_concat_0 = prove(
    ``∀(w :β word) (z :α word) (c :γ word). FINITE 𝕌((:α) :α itself) ==> (dimindex (:β) <= dimindex (:γ) ==> ((z = 0w) ==> ((c = (n2w (w2n w) :γ word)) ==> (c = z @@ w))))``
  ,       (RW_TAC (pure_ss) [])
    THEN  (ASSUME_TAC (ISPEC ``w :β word`` wordsTheory.w2n_lt))
    THEN  (ASSUME_TAC ((UNDISCH_ALL o CONJ_IMP o (SPECL [``w:β word``, ``w2n (w:β word)``])) wordsTheory.word_concat_0_eq))
    THEN  ((FULL_SIMP_TAC (srw_ss()) []))
);

val ADD2_DIV2_ADD1_DIV2 = prove (
    ``∀(n :num). (2 + n) DIV 2 = 1 + n DIV 2``
  ,       GEN_TAC
    THEN  (ASSUME_TAC ((DISPOSE_HYP o DISCH_ALL o (SPECL [``1:num``, ``n:num``]) o UNDISCH_ALL o (SPEC ``2:num``)) arithmeticTheory.ADD_DIV_ADD_DIV))
    THEN  (FULL_SIMP_TAC (srw_ss()) [])
);

val MULT_SUM = prove(
    ``∀ (n:num) (m:num). (m * n = SUM m (λx.n))``
  ,       (Induct_on `m`)
    THEN  (FULL_SIMP_TAC (arith_ss) [sum_numTheory.SUM_def,arithmeticTheory.MULT_SUC])
);

val MULT_SUM_COMM = prove(
    ``∀ (j:num) (k:num). SUM j (λx. k) = SUM k (λx. j)``
  , (RW_TAC (arith_ss) [GSYM MULT_SUM])
);

val EVENS_DIV_ADD = prove(
    ``∀ (j:num) (k:num). (EVEN j ∧ EVEN k) ==> (j DIV 2 + k DIV 2 = (j + k) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
);

val ODDS_DIV_ADD = prove(
    ``∀ (j:num) (k:num). (ODD  j ∧ ODD  k) ==> (j DIV 2 + k DIV 2 = (j + k - 2) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
);

val EVEN_ODD_MIX_DIV_ADD = prove(
    ``∀ (j:num) (k:num). (EVEN j ≠ EVEN k) ==> (j DIV 2 + k DIV 2 = (j + k - 1) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (Cases_on `EVEN j`)
    THEN  (
            (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
      THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.EVEN_ODD, arithmeticTheory.EVEN_EXISTS])
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD_EXISTS])
      THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
      THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
      THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
      THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
      THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD_COMM])
      THEN  (FULL_SIMP_TAC (srw_ss()) [ADD2_DIV2_ADD1_DIV2])
      THEN  (FULL_SIMP_TAC (pure_ss) [MULT_SUM, MULT_SUM_COMM])
      THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
      THEN  (FULL_SIMP_TAC (arith_ss) [])
    )
);

val ODD_POS = prove(
    ``∀ (n:num). (ODD n) ==> (0 < n)``
  , Induct THEN (FULL_SIMP_TAC (arith_ss) [])
);

val ODD_MOD2 = prove(
    ``∀ (n:num). (ODD n) = (n MOD 2 = 1)``
  ,       (RW_TAC (arith_ss) [arithmeticTheory.MOD_2])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])
);

val ODD_SUM_GT1 = prove(
    ``∀ (j:num) (k:num). ODD j ==> (ODD k ==> (1 < j + k))``
  , Induct THEN Induct THEN (FULL_SIMP_TAC (arith_ss) [])
);

val GT1_DIV2_GT0 = prove(
    ``∀ (n:num). 1 < n ==> (0 < n DIV 2)``
  ,       Induct
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (Induct_on `n`)
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (RW_TAC (arith_ss) [SUC_INC])
    THEN  (SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [ADD2_DIV2_ADD1_DIV2])
);

val SUB2_DIV2_SUB1_DIV2 = prove (
    ``∀(n :num). (n - 2) DIV 2 = n DIV 2 - 1``
  ,       Induct
    THENL [
      (FULL_SIMP_TAC (arith_ss) [])
    ,
            (Induct_on `n`)
      THENL [
              (FULL_SIMP_TAC (arith_ss) [])
      ,       (RW_TAC (pure_ss) [])
        THEN  (FULL_SIMP_TAC (arith_ss) [SUC_INC])
        THEN  (RW_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM, ADD2_DIV2_ADD1_DIV2])
        THEN  (FULL_SIMP_TAC (arith_ss) [])
      ]
    ]
);

val EVEN_DIV_EQ_SUC = prove(
    ``∀ (n:num). (EVEN n) = (n DIV 2 = (SUC n) DIV 2)``
  ,       GEN_TAC
    THEN  EQ_TAC
    THENL [
              (RW_TAC (pure_ss) [])
        THEN  (FULL_SIMP_TAC (pure_ss) [SPEC_ALL arithmeticTheory.EVEN_EXISTS])
        THEN  (RW_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
        THEN  (RW_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
        THEN  (RW_TAC (srw_ss()) [arithmeticTheory.MULT_DIV])
      ,
              (Cases_on `EVEN n`)
        THEN  (FULL_SIMP_TAC (arith_ss) [])
        THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])
        THEN  (FULL_SIMP_TAC (pure_ss) [SPEC_ALL arithmeticTheory.ODD_EXISTS])
        THEN  (RW_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
        THEN  (RW_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
        THEN  (FULL_SIMP_TAC (arith_ss) [])
        THEN  (RW_TAC (pure_ss) [
                    EVALBOOL ``(2:num) * m + 2 = 2*m + 2*1``
                  , GSYM arithmeticTheory.LEFT_ADD_DISTRIB
                ]
              )
        THEN  (RW_TAC (pure_ss) [MULT_SUM, SPECL [``2:num``, ``(m:num) + 1``] MULT_SUM_COMM])
        THEN  (RW_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
        THEN  (FULL_SIMP_TAC (arith_ss) [])
    ]
);

val ODDSUC_DIV_EQ_SUC = prove(
    ``∀ (n:num). (ODD (SUC n)) = (n DIV 2 = (SUC n) DIV 2)``
  , (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD, GSYM arithmeticTheory.EVEN_ODD, EVEN_DIV_EQ_SUC])
);

val ODD_DIV_EQ_PREC = prove(
    ``∀ (n:num). 0 < n ==> ((ODD n) = (n DIV 2 = (n - 1) DIV 2))``
  ,       (RW_TAC (pure_ss) [])
    THEN  (ASSUME_TAC ((UNDISCH_ALL o SPEC_ALL) PREC_EXISTS))
    THEN  (FULL_SIMP_TAC (srw_ss()) [])
    THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPEC ``m:num``)) ODDSUC_DIV_EQ_SUC))
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC])
    THEN  (RW_TAC (arith_ss) [ODDSUC_DIV_EQ_SUC])
);

val SUM_LT_2EXP = prove(
    ``∀ (n:num) (j:num) (k:num). (j + k < 2**n) ==> (j < 2**n)``
  , (RW_TAC (arith_ss) [])
);

(*
    Lemmas/Theorems dependency:

     EVENS_DIV_ADD
     ODDS_DIV_ADD
     SUB2_DIV2_SUB1_DIV2
     ODD_SUM_GT1
     GT1_DIV2_GT0
     ADDSUB_COMM
     ODD_POS
     ODD_DIV_EQ_PREC
     EVEN_ODD_MIX_DIV_ADD
     SUM_LT_2EXP
*)
val SUM_2EXP_EQ = prove(
    ``∀ (n:num) (j:num) (k:num). (j + k < 2**(SUC n)) = ((j DIV 2) + (k DIV 2) + (j MOD 2) * (k MOD 2) < 2**n)``
  ,       (REPEAT GEN_TAC)
    THEN  EQ_TAC
    THENL [
            (Cases_on `EVEN j = EVEN k`)
      THENL [
              (RW_TAC (pure_ss) [arithmeticTheory.MOD_2])
        THENL [
                (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV_ADD, (GSYM arithmeticTheory.EXP2_LT)])
          , (
                  (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
            THEN  (FULL_SIMP_TAC (bool_ss) [GSYM arithmeticTheory.EVEN_ODD])
          )
          THEN  (FULL_SIMP_TAC (arith_ss) [ODDS_DIV_ADD, (GSYM arithmeticTheory.EXP2_LT)])
          THEN  (FULL_SIMP_TAC (arith_ss) [SUB2_DIV2_SUB1_DIV2])
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o SPEC_ALL) ODD_SUM_GT1 ))
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o (SPEC ``(j:num) + k``)) GT1_DIV2_GT0 ))
          THEN  (FULL_SIMP_TAC (arith_ss) [ADDSUB_COMM])
        ]
      ,
              (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
        THEN  (ASSUME_TAC ( (UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``j:num``, ``k:num``])) arithmeticTheory.ODD_ADD ))
        THEN  (ASSUME_TAC ( (UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_POS ))
        THEN  (ASSUME_TAC ( (UNDISCH_ALL o GSYM o fst o EQ_IMP_RULE o UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_DIV_EQ_PREC ))
        THEN  (FULL_SIMP_TAC (bool_ss) [GSYM arithmeticTheory.ODD_EVEN])
        THEN  (RW_TAC (arith_ss) [EVEN_ODD_MIX_DIV_ADD, arithmeticTheory.MOD_2]) (* 4 subgoals from here *)
        THENL [
            (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.ODD_EVEN])
          , (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD, (GSYM arithmeticTheory.EXP2_LT)])
          , (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD, (GSYM arithmeticTheory.EXP2_LT)])
          , (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD, (GSYM arithmeticTheory.EXP2_LT)])
        ]
      ]
    ,
              (FULL_SIMP_TAC (arith_ss) [Once (GSYM arithmeticTheory.ADD_ASSOC)])
        THEN  (FULL_SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM])
        THEN  (RW_TAC (pure_ss) [])
        THEN  (ASSUME_TAC ( (UNDISCH_ALL o (SPECL [``n:num``, ``(j:num) DIV 2 + (k :num) DIV 2``, ``j MOD 2 * k MOD 2``])) SUM_LT_2EXP ))
        
        THEN  (Cases_on `EVEN j = EVEN k`)
        THENL [
                (Cases_on `EVEN j`)
          THENL [
            (
                    (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
              THEN  (FULL_SIMP_TAC (bool_ss) [GSYM arithmeticTheory.EVEN_ODD])
            )
            THEN  (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV_ADD, (GSYM arithmeticTheory.EXP2_LT)])
          ,
            (
                    (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
              THEN  (FULL_SIMP_TAC (bool_ss) [GSYM arithmeticTheory.EVEN_ODD])
            )
            THEN  (FULL_SIMP_TAC (arith_ss) [ODDS_DIV_ADD, (GSYM arithmeticTheory.EXP2_LT)])
            THEN  (FULL_SIMP_TAC (arith_ss) [SUB2_DIV2_SUB1_DIV2, ODD_MOD2])
          ]
        ,
                (FULL_SIMP_TAC (srw_ss()) [EVEN_ODD_MIX_DIV_ADD])
          THEN  (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``j:num``, ``k:num``])) arithmeticTheory.ODD_ADD ))
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_POS ))
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o GSYM o fst o EQ_IMP_RULE o UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_DIV_EQ_PREC ))
          THEN  (FULL_SIMP_TAC (bool_ss) [])
          
          THEN  (Cases_on `EVEN j`)
          THEN  (FULL_SIMP_TAC (arith_ss) [(GSYM arithmeticTheory.EXP2_LT), arithmeticTheory.MOD_2])
        ]
    ]
);
(* ---- *)

val SUM_CONST_LT_2EXP = prove(
    ``∀ (n:num) (j:num) (k:num) (c:num). (j < 2**n) ∧ (k < 2**n) ==> (c < 2 ==> ((j + k + c < 2**(SUC n))))``
  , (FULL_SIMP_TAC (arith_ss) [SUC_INC, arithmeticTheory.EXP_ADD])
);

val RIGHT_SHIFT_SUM_LT_2EXP = prove(
    ``∀ (n:num) (j:num) (k:num). (j < 2**(SUC n)) ∧ (k < 2**(SUC n)) ==> ((j DIV 2 + k DIV 2 + 1 < 2**(SUC n)) ∧ (j DIV 2 + k DIV 2 < 2**(SUC n)))``
  ,       (RW_TAC (pure_ss) [])
    THENL [
            (ASSUME_TAC (SPECL [``n:num``, ``j DIV 2``, ``k DIV 2``, ``1:num``] SUM_CONST_LT_2EXP))
      THEN  (RW_TAC (srw_ss()) [(fst o EQ_IMP_RULE o SPEC_ALL) (GSYM arithmeticTheory.EXP2_LT)])
    ,       (ASSUME_TAC (SPECL [``n:num``, ``j DIV 2``, ``k DIV 2``, ``0:num``] SUM_CONST_LT_2EXP))
      THEN  (FULL_SIMP_TAC (arith_ss) [(fst o EQ_IMP_RULE o SPEC_ALL) (GSYM arithmeticTheory.EXP2_LT)])
    ]
);

val DIV_PRODMOD_LT_2EXP = prove(
    ``∀ (n:num) (j:num) (k:num). (j < 2**(SUC n)) ∧ (k < 2**(SUC n)) ==> (j DIV 2 + k DIV 2 + (j MOD 2) * (k MOD 2) < 2**(SUC n))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC (SPEC_ALL MULT_MOD2_01))
    THEN  (RW_TAC (pure_ss) [])
    THEN  (
            (RW_TAC (arith_ss) [])
      THEN  (RW_TAC (pure_ss) [arithmeticTheory.ADD_ASSOC])
      THEN  (FULL_SIMP_TAC (arith_ss) [RIGHT_SHIFT_SUM_LT_2EXP])
    )
);

val DIV_MOD = prove(
    ``∀ (n :num) (j :num). (0 < n) ==> (n * (j DIV n) + j MOD n = j)``
  , (FULL_SIMP_TAC (arith_ss) [])
);

val MOD_2EXP_EQ = prove(
    ``∀ (n :num) (j :num). j MOD 2**(SUC n) = 2 * ((j DIV 2) MOD 2**n) + j MOD 2``
  ,       (FULL_SIMP_TAC (arith_ss) [SUC_INC, arithmeticTheory.EXP_ADD, arithmeticTheory.DIV_MOD_MOD_DIV])
    THEN  (REWRITE_TAC [Once ((SIMP_RULE arith_ss [] o SPECL [``2:num``, ``j MOD ((2 :num) * (2 :num) ** n)``] o GSYM) DIV_MOD)])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_MULT_MOD])
);

(* ------------------------------------------------------------------------- *)
(*  Tactics                                                                  *)
(* ------------------------------------------------------------------------- *)
(* TACTICS *)
val BIL_CONST_TAC = (REPEAT GEN_TAC) THEN EVAL_TAC;
val BIL_OP_FULL_SIMP_TAC = (FULL_SIMP_TAC (srw_ss()) [
      bil_add_def
    , bil_sub_def
    , bil_mul_def
    , bil_div_def
    , bil_sdiv_def
    , bil_mod_def
    , bil_smod_def
    , bil_lsl_def
    , bil_lsr_def
    , bil_asr_def
    , bil_and_def
    , bil_or_def
    , bil_xor_def
    , bil_eq_def
    , bil_neq_def
    , bil_lt_def
    , bil_le_def
    , bil_ult_def
    , bil_ule_def
    , bil_cast_def
    , bil_scast_def
    , bil_hcast_def
    , bil_lcast_def
    , n2b_def
    , n2b_1_def
    , n2b_8_def
    , n2b_16_def
    , n2b_32_def
    , n2b_64_def
    , n2bs_def
    , w2b_def
    , w2bs_def
    , bool2b_def
    , r2s_def
    , word_neq_def
    , wordsTheory.n2w_w2n
    , wordsTheory.word_msb_neg
    , arithmeticTheory.GREATER_DEF
    , arithmeticTheory.GREATER_EQ
    , BIT_DIV_MOD
    , SUM_2EXP_EQ
    , MOD_2EXP_EQ
    , n2w_w2w_concat_0
  ]
);
val BIL_EVAL_ONCE_TAC = ((SIMP_TAC (arith_ss) [Once bil_eval_exp_def]) THEN  BIL_OP_FULL_SIMP_TAC);
val BIL_LSB_TAC =
        (FULL_SIMP_TAC (srw_ss()) [wordsTheory.word_lsb, wordsTheory.word_bit_def])
  THEN  (RW_TAC (srw_ss()) [])
  THEN  (
          (SIMP_TAC (srw_ss()) [Ntimes bil_eval_exp_def 2])
    THEN  BIL_OP_FULL_SIMP_TAC
    THEN  (SIMP_TAC (srw_ss()) [Ntimes bil_eval_exp_def 2])
    THEN  EVAL_TAC
    THEN  blastLib.BBLAST_TAC
    THEN  (RW_TAC (srw_ss()) [])
  )
;
val BIL_OP_BIT_TAC = (
        (RW_TAC (pure_ss) [])
  THEN  (REPEATN (12, BIL_EVAL_ONCE_TAC))
  THEN  (FULL_SIMP_TAC (arith_ss++WORD_ss++WORD_ARITH_ss++WORD_SHIFT_ss++WORD_EXTRACT_ss) [wordsTheory.word_extract_n2w, wordsTheory.word_and_n2w])
  THEN  EVAL_TAC
  THEN  (ASSUME_TAC (SPECL [``63:num``, ``n:num``, ``m:num``] BITS_LT_2EXP))
  THEN  (FULL_SIMP_TAC (srw_ss()) [MODN_MODM])
  THEN  (FULL_SIMP_TAC (arith_ss) [bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def, bitTheory.BITS_def, EXP_LT_ALT])
);
val BIL_OP_TAC = (
        BIL_OP_FULL_SIMP_TAC
  THEN  (
          (RW_TAC (srw_ss()) [])
    THEN  (SIMP_TAC (arith_ss) [Once bil_eval_exp_def])
    THEN  (RW_TAC (arith_ss) [])
  )
  THEN  (
          (RW_TAC (srw_ss()) [])
    THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
    THEN  BIL_OP_FULL_SIMP_TAC
    THEN  EVAL_TAC
  )
  THEN  (
          (RW_TAC (srw_ss()) [])
    THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
    THEN  BIL_OP_FULL_SIMP_TAC
    THEN  blastLib.BBLAST_TAC
    THEN  EVAL_TAC
    THEN  WORD_DECIDE_TAC
  )
);
val BIL_DEN_TAC = (SRW_TAC [] [Once bil_eval_exp_def, bil_env_read_def, search_snd_def, LET_DEF, r2s_def]);
val BIL_NUMERAL_TAC = (
        (SIMP_TAC (srw_ss()) [Ntimes bil_eval_exp_def 2])
  THEN  BIL_OP_FULL_SIMP_TAC
  THEN  (
            (RW_TAC (pure_ss++WORD_ARITH_ss++WORD_SHIFT_ss++WORD_EXTRACT_ss) [])
      THEN  (REPEAT (BIL_OP_FULL_SIMP_TAC THEN WORD_DECIDE_TAC))
  )
);
val BIL_PLUS_LT_2EXP64_TAC = (
        (REPEAT STRIP_TAC)
  THEN  (REPEATN (12, BIL_EVAL_ONCE_TAC))
  THEN  EVAL_TAC
  THEN  ((FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS, DIV_PRODMOD_LT_2EXP]))
  THEN  (FULL_SIMP_TAC (pure_ss) [prove(``(18446744073709551616:num) = 2 ** SUC 63``, EVAL_TAC), SPECL [``63:num``, ``n:num``, ``m:num``] SUM_2EXP_EQ])
  THEN  (ASSUME_TAC ((UNDISCH_ALL o CONJ_IMP o (SPECL [``63:num``, ``n:num``, ``m:num``])) DIV_PRODMOD_LT_2EXP))
  THEN  ((FULL_SIMP_TAC (arith_ss) []))
);
val BIL_MOD_2EXP64_TAC = (
       (REPEAT STRIP_TAC)
  THEN (REPEATN (9, BIL_EVAL_ONCE_TAC))
  THEN EVAL_TAC
  THEN AP_TERM_TAC
  THEN (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.DIV_MOD_MOD_DIV])
  THEN (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, MODN_MODM])
  THEN (ASSUME_TAC ((DISPOSE_HYP o SPECL [``2:num``, ``n:num``]) MULT_DIV_LE))
  THEN (FULL_SIMP_TAC (arith_ss) [DIV_MOD])
);


(* ------------------------------------------------------------------------- *)
(*  Theorems - basic conversion theorems                                     *)
(* ------------------------------------------------------------------------- *)
(* Generic prove for variables (they MUST be at least declared in the environment) *)
val arm8_to_bil_den_tm = tryprove(
    ``∀ env d dt dv. (env d = (dt, dv)) ==> (bil_eval_exp (Den d) env = dv)``
  , BIL_DEN_TAC
);

(* Generic prove for bil constants *)
val bil_const_tm = tryprove(
    ``∀ env x. bil_eval_exp (Const x) env = Int x``
  , BIL_CONST_TAC
);

(* Generic prove for numbers and booleans *)
val bil_boolean_tm = tryprove(
    ``∀ env x. (bil_eval_exp (Const (bool2b x)) env = Int (bool2b x))``
  , BIL_CONST_TAC
);

val bil_numeral_expressibility_tm = tryprove(
    ``∀ env n. (n < dimword (:64)) = (bil_eval_exp (Cast (Const (n2b n)) Bit64) env = Int (n2b_64 n))``
  , BIL_NUMERAL_TAC
);

val bil_numeral_tm = (GEN_ALL o (GEN ``n:num``) o fst o EQ_IMP_RULE o UNDISCH_ALL o SPEC_ALL) bil_numeral_expressibility_tm;

val bil_num_tm = tryprove(
    ``∀ env n. (n < dimword (:64)) ==> ((∃ bn. bil_eval_exp (bn) env = Int (n2b_64 n)))``
  , PROVE_TAC [bil_numeral_expressibility_tm]
); (* useless... ? *)

val bil_plus_lt_2exp64_tm = tryprove(
    ``∀ env n m bn bm. (n < dimword (:64)) ==> ((m < dimword (:64)) ==> ((bil_eval_exp (bn) env = Int (n2b_64 n)) ∧ (bil_eval_exp (bm) env = Int (n2b_64 m)) ==> (bil_eval_exp (
      LessThan  (Plus (Div bn (Const 2x))
                      (Plus (Div bm (Const 2x))
                            (Mult (Mod bn (Const 2x))
                                  (Mod bm (Const 2x))
                            )
                      )
                )
                (Const 9223372036854775808x)
    ) env = Int (bool2b (n + m < 18446744073709551616)))))``
  , BIL_PLUS_LT_2EXP64_TAC
);

val bil_mod_2exp64_tm = tryprove(
    ``∀ env n bn. (n < dimword(:64)) ==> ((bil_eval_exp (bn) env = Int (n2b_64 n)) ==> (bil_eval_exp (
      Plus (Mult  (Const 2x)
                  (Mod  (Div bn (Const 2x))
                        (Const 9223372036854775808x)
                  )
           )
           (Mod (bn)
                (Const 2x)
           )
    ) env = Int (n2b_64 (n MOD 18446744073709551616))))``
  , BIL_MOD_2EXP64_TAC
);

fun nw n s = wordsSyntax.mk_wordii(n, s);

(* Generic theorems for binary expressions *)
val bil_op_tms =
  let
    val bopPairs = [
          (fn s => (fst o strip_comb) ``word_add    ^(nw 0 s)``, fn s => ``Plus              bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_sub    ^(nw 0 s)``, fn s => ``Minus             bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_mul    ^(nw 0 s)``, fn s => ``Mult              bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_div    ^(nw 0 s)``, fn s => ``Div               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_sdiv   ^(nw 0 s)``, fn s => ``SignedDiv         bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_mod    ^(nw 0 s)``, fn s => ``Mod               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_smod   ^(nw 0 s)``, fn s => ``SignedMod         bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lsl_bv ^(nw 0 s)``, fn s => ``LeftShift         bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lsr_bv ^(nw 0 s)``, fn s => ``RightShift        bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_asr_bv ^(nw 0 s)``, fn s => ``SignedRightShift  bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_and    ^(nw 0 s)``, fn s => ``And               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_or     ^(nw 0 s)``, fn s => ``Or                bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_xor    ^(nw 0 s)``, fn s => ``Xor               bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``$=          ^(nw 0 s)``, fn s => ``Equal             bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``$≠          ^(nw 0 s)``, fn s => ``NotEqual          bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lt     ^(nw 0 s)``, fn s => ``SignedLessThan    bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_le     ^(nw 0 s)``, fn s => ``SignedLessOrEqual bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_ls     ^(nw 0 s)``, fn s => ``LessOrEqual       bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lo     ^(nw 0 s)``, fn s => ``LessThan          bx by``, BIL_OP_TAC)
      ];
    val uopPairs = [
          (fn s => (fst o strip_comb) ``word_2comp  ^(nw 0 s)``, fn s => ``ChangeSign        bx``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_1comp  ^(nw 0 s)``, fn s => ``Not               bx``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``w2n         ^(nw 0 s)``, fn s => ``Cast              bx Bit64``, BIL_OP_TAC)
        
        (* Some special operator *)
        , (fn s => (fst o strip_comb) ``word_msb    ^(nw 0 s)``, fn s => ``SignedLessThan bx ^(bil_expr_const (nw 0 s))``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lsb    ^(nw 0 s)``, fn s => ``Equal (And bx ^(bil_expr_const (nw 1 s))) ^(bil_expr_const (nw 1 s))``, BIL_LSB_TAC)
      ];
    val bopPairsBool = [
          (fn s => (fst o strip_comb) ``T ∧ T``, fn s => ``And    bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``T ∨ T``, fn s => ``Or     bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``T = T``, fn s => ``Equal  bx by``, BIL_OP_TAC)
      ];
    val uopPairsBool = [
          (fn s => (fst o strip_comb) ``~T``, fn s => ``Not bx``, BIL_OP_TAC)
(*         , (fn s => (fst o strip_comb) ``¬T``, fn s => ````, BIL_OP_TAC) *)
      ];
    val bopPairsNum = [
          (fn s => (fst o strip_comb) ``(n:num)   + m``, fn s => ``Plus      bn bm``, BIL_OP_TAC)
(*         , (fn s => (fst o strip_comb) ``(n:num)   - m``, fn s => ``IfThenElse (SignedLessThan bn bm) (Const 0x) (Minus bn bm)``, BIL_OP_TAC) *)
        , (fn s => (fst o strip_comb) ``(n:num)   * m``, fn s => ``Mult         bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num) DIV m``, fn s => ``Div          bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num) MOD m``, fn s => ``Mod          bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)   = m``, fn s => ``Equal        bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)   < m``, fn s => ``LessThan     bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)  <= m``, fn s => ``LessOrEqual  bn bm``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)   > m``, fn s => ``LessThan     bm bn``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(n:num)  >= m``, fn s => ``LessOrEqual  bm bn``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``BIT (n:num) m``, fn s => ``Equal (Mod (RightShift bm bn) ^(bil_expr_const (nw 2 s))) ^(bil_expr_const (nw 1 s))``, BIL_OP_BIT_TAC)
      ];
    val uopPairsNum = [
      ];
    val ifthenelseNum = [
          (fn s => (fst o strip_comb) ``if (c:bool) then (n:num) else (m:num)``, fn s => ``IfThenElse bc bn bm``, BIL_OP_TAC)
      ];
    
    (* cartesian product *)
    fun prod bints opPairs =
      let
        fun prod' lst1 lst2 res =
          case lst1 of
              []          => res
            | (br, s)::l1 => prod' l1 lst2 (List.concat [map (fn (f, b, tac) => (f s, b s, tac, br)) lst2, res])
      in
        prod' bints opPairs []
      end;
      
    val goalgenerator_uop = fn (auop, bexp, tac, br) =>
      let
        val auopValue = bil_value ``(^auop x)``
      in
        (
            auop, bexp, tac, br
            , ``∀ env x bx. (bil_eval_exp bx env = Int (^br x)) ==> (bil_eval_exp ^bexp env = ^auopValue)``
        )
      end;
      
    val goalgenerator_bop = fn (abop, bexp, tac, br) =>
      let
        val abopValue = bil_value ``(^abop x y)``
      in
        (
            abop, bexp, tac, br
          , ``∀ env x y bx by. (bil_eval_exp bx env = Int (^br x)) ∧ (bil_eval_exp by env = Int (^br y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
      
    val goalgenerator_bop_bool = fn (abop, bexp, tac, _) =>
      let
        val abopValue = bil_value ``(^abop x y)``
      in
        (
            abop, bexp, tac, ``Reg1``
          , ``∀ env x y bx by. (bil_eval_exp bx env = Int (bool2b x)) ∧ (bil_eval_exp by env = Int (bool2b y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
      
    val goalgenerator_uop_bool = fn (abop, bexp, tac, _) =>
      let
        val abopValue = bil_value ``(^abop x)``
      in
        (
            abop, bexp, tac, ``Reg1``
          , ``∀ env x bx. (bil_eval_exp bx env = Int (bool2b x)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
    val goalgenerator_bop_num = fn (abop, bexp, tac, _) =>
      let
        val aexp = ``(^abop n m)``;
        val abopValue = bil_value aexp;
        val concl = if (is_num  aexp)
          then ``((^aexp) < dimword(:64)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
          else ``(bil_eval_exp ^bexp env = ^abopValue)``;
      in
        (
            abop, bexp, tac, ``Reg64``
          , ``∀ env n m bn bm.  (n < dimword(:64))
                            ==> ((m < dimword(:64))
                            ==> ((bil_eval_exp bn env = Int (n2b_64 n)) ∧ (bil_eval_exp bm env = Int (n2b_64 m))
                            ==> (^concl)
                            ))``
        )
      end;
    val goalgenerator_ite_num = fn (abop, bexp, tac, _) =>
      let
        val aexp = ``(^abop c n m)``;
        val abopValue = bil_value aexp;
        val concl = ``(bil_eval_exp ^bexp env = ^abopValue)``;
      in
        (
            abop, bexp, tac, ``Reg64``
          , ``∀ env c n m bc bn bm. (n < dimword(:64))
                                ==> ((m < dimword(:64))
                                ==> ((bil_eval_exp bc env = Int (bool2b c)) ∧ (bil_eval_exp bn env = Int (n2b_64 n)) ∧ (bil_eval_exp bm env = Int (n2b_64 m))
                                ==> (^concl)
                                ))``
        )
      end;
      
    val goals = List.concat [
          map goalgenerator_bop      (prod constructor_size_pairs bopPairs)
        , map goalgenerator_uop      (prod constructor_size_pairs uopPairs)
        , map goalgenerator_bop_bool (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) bopPairsBool)
        , map goalgenerator_uop_bool (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) uopPairsBool)
        , map goalgenerator_bop_num  (prod (List.filter (fn (_, n) => n = 64) constructor_size_pairs) bopPairsNum)
        , map goalgenerator_ite_num  (prod (List.filter (fn (_, n) => n = 64) constructor_size_pairs) ifthenelseNum)
      ];
  in
    (* And now batch proofs... *)
    map (fn (abop, bop, tac, br, g) => (abop, bop, br, tryprove (g, tac))) goals
  end
;

(* This function helps selecting a theorem by operator and size *)
fun select_bil_op_theorem operator size =
  let
    val constr = fst (List.nth (List.filter (fn (_, s) => s = size) constructor_size_pairs, 0))
      handle Subscript => raise UnsupportedWordSizeException
    val (_, _, _, th) = List.nth (List.filter (fn (aop, _, c, _) => (aop = operator) andalso (c = constr)) bil_op_tms, 0)
      handle Subscript => raise UnsupportedARM8ExpressionException operator
  in
    th
  end
;

(* ------------------------------------------------------------------------- *)
(*  Transcompiler of expressions                                             *)
(* ------------------------------------------------------------------------- *)

(* Extract operands in triplets *)
fun extract_operands t =
        if (wordsSyntax.is_n2w t) then (``T``, ``T``, ``T``)
  else  if (is_comb t) then
    let
      val ops = snd(strip_comb t)
      val l = List.length ops (* can't be 0, can it? *)
    in
            if (l = 1) then (List.nth (ops, 0), ``F``, ``F``)
      else  if (l = 2) then (List.nth (ops, 0), List.nth (ops, 1),``F``)
      else  if (l = 3) then (List.nth (ops, 0), List.nth (ops, 1), List.nth (ops, 2))
      else  raise ArgumentException("Too many operands found...")
    end
  else (``F``, ``F``, ``F``)
;


(* Transcompiler arm8 expressions to BIL model expressions *)
fun tce ae =
  let
    val (o1, o2, o3) = extract_operands ae;
  in
          if (wordsSyntax.is_n2w ae) then (
                  bil_expr_const ae
                , ae
                , GEN_ALL (SPECL [``env:environment``, eval ``w2b ^ae``] bil_const_tm)
              )
    else  if  (is_boolean ae) then (
                  bil_expr_bool ae
                , ae
                , GEN_ALL (SPECL [``env:environment``, ``bool2b ^ae``] bil_const_tm)
              )
    else  if  (numSyntax.is_numeral ae) then (
                  bil_expr_num ae
                , ae
                , GEN_ALL (SPECL [``env:environment``, ae] bil_numeral_tm)
              )
    else  if  (is_reg ae) then (
                  bil_a8e_den ae
                , ae
                , (GEN_ENV o GENL [``s:arm8_state``, ``w:word5``] o SPECL [``r2s ^((snd o dest_comb) ae)``, ``Reg Bit64``, ``Int (Reg64 ^ae)``] o SPEC_ENV) arm8_to_bil_den_tm
              )
    else  if  (is_arm8_den ae) then (
                  bil_a8e_den ae
                , ae
                , (GEN_ENV o GEN ``s:arm8_state`` o SPECL [
                      bil_a8e2HOLstring ae
                    , eval ``bil_type_val_int_inf ^(bil_value ae)``
                    , ``^(bil_value ae)``
                  ] o SPEC_ENV) arm8_to_bil_den_tm
              )
    else  if  (is_plus_lt_2exp64 ae)
      then
        let
          val (add1, add2, _) = extract_operands o1;
          val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_BIN bil_plus_lt_2exp64_tm (tce add1) (tce add2));
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
        in
          (be, ae, mp)
        end
    else  if  (is_mod_2exp64 ae)
      then
        let
          val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_UN bilmod_2exp64_tm (tce o1));
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
        in
          (be, ae, mp)
        end
    else  if          (wordsSyntax.is_word_add    ae)
              orelse  (wordsSyntax.is_word_sub    ae)
              orelse  (wordsSyntax.is_word_mul    ae)
              orelse  (wordsSyntax.is_word_div    ae)
              orelse  (wordsSyntax.is_word_sdiv   ae)
              orelse  (wordsSyntax.is_word_mod    ae)
              orelse  (wordsSyntax.is_word_smod   ae)
              orelse  (wordsSyntax.is_word_lsl_bv ae)
              orelse  (wordsSyntax.is_word_lsr_bv ae)
              orelse  (wordsSyntax.is_word_asr_bv ae)
              orelse  (wordsSyntax.is_word_and    ae)
              orelse  (wordsSyntax.is_word_or     ae)
              orelse  (wordsSyntax.is_word_xor    ae)
              orelse  (            is_word_eq     ae)
      then
        let
          val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1)) (tce o1) (tce o2));
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
        in
          (be, ae, mp)
        end
    else  if          (boolSyntax.is_disj    ae)
              orelse  (boolSyntax.is_conj    ae)
              orelse  (           is_eq_bool ae)
      then
        let
          val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (select_bil_op_theorem ((fst o strip_comb) ae) 1) (tce o1) (tce o2));
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
        in
          (be, ae, mp)
        end
    else  if          (boolSyntax.is_neg ae)
      then
        let
          val mp = (GEN_ALL o DISCH_ALL) (MP_UN (select_bil_op_theorem ((fst o strip_comb) ae) 1) (tce o1));
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
        in
          (be, ae, mp)
        end
    else  if          ( numSyntax.is_plus    ae)
(*               orelse  ( numSyntax.is_minus   ae) *)
              orelse  ( numSyntax.is_mult    ae)
              orelse  ( numSyntax.is_div     ae)
              orelse  ( numSyntax.is_mod     ae)
              orelse  ( numSyntax.is_less    ae)
              orelse  ( numSyntax.is_leq     ae)
              orelse  ( numSyntax.is_greater ae)
              orelse  ( numSyntax.is_geq     ae)
              orelse  ( bitSyntax.is_bit     ae)
              orelse  (           is_eq_num  ae)
      then
        let
          val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_BIN (select_bil_op_theorem ((fst o strip_comb) ae) 64) (tce o1) (tce o2));
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
        in
          (be, ae, mp)
        end
    else  if          (boolSyntax.is_cond     ae)
      then
        let
          val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_ITE (select_bil_op_theorem ((fst o strip_comb) ae) 64) (tce o1) (tce o2) (tce o3))
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)
        in
          (be, ae, mp)
        end
    else  if          (wordsSyntax.is_word_1comp  ae)
              orelse  (wordsSyntax.is_word_2comp  ae)
              orelse  (wordsSyntax.is_word_msb    ae)
              orelse  (wordsSyntax.is_w2n         ae)
      then
        let
          val mp = (GEN_ALL o DISCH_ALL) (MP_UN (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1)) (tce o1))
          val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)
        in
          (be, ae, mp)
        end
    else  raise UnsupportedARM8ExpressionException ae
  end
;
val tc_exp_arm8 = tce;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
val _ = export_theory();
