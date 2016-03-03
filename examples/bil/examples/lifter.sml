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
HOL_Interactive.toggle_quietdec();

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
exception UnsupportedARM8StateField of string;

(* ------------------------------------------------------------------------- *)
(*  Misc tools                                                               *)
(* ------------------------------------------------------------------------- *)

(* Just generalize/specialize the environment *)
val SPEC_ENV = SPEC ``env:environment``;
val GEN_ENV = GEN ``env:environment``;

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

fun MP_ITE thImp (be1, ae1, thm1) (be2, ae2, thm2) (be3, ae3, thm3) = 
  MP_CONJL (((SPECL [ae1, ae2, ae3, be1, be2, be3]) o SPEC_ENV) thImp) (List.rev [(UNDISCH_ALL o SPEC_ALL) thm1, (UNDISCH_ALL o SPEC_ALL) thm2, (UNDISCH_ALL o SPEC_ALL) thm3])
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
    else raise NotAWordException
;

val word_length = fn t =>
  if (wordsSyntax.is_word_type (type_of t))
    then
      let
        val l = eval ``word_len ^t``;
      in
        if (numSyntax.is_numeral l)
          then  numSyntax.int_of_term l
          else  raise UnsupportedWordSizeException
      end
    else raise NotAWordException
;

(* ------------------------------------------------------------------------- *)
(*  Expression tests                                                         *)
(* ------------------------------------------------------------------------- *)
fun is_arm8_app t cmp =
  let
    val dummystate = ``ds:arm8_state``;
    val godeep = fn t => (snd o dest_comb) t;
    val subst1 = fn t => subst [godeep t |-> dummystate] t;
    val subst2 = fn t => (subst [(godeep o fst o dest_comb) t |-> dummystate] o fst o dest_comb) t;
    val subst3 = fn t => (subst [(godeep o godeep) t |-> dummystate]) t;
  in
            (is_comb t)
    andalso (
                  (subst1 t = subst1 cmp)
      handle _ => (subst2 t = subst1 cmp)
      handle _ => (subst3 t = subst3 cmp)
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
val is_cond_num  = fn t => (is_cond t) andalso ((is_num  o trd3 o dest_cond) t);
val is_cond_bool = fn t => (is_cond t) andalso ((is_bool o trd3 o dest_cond) t);

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

val is_word_neq = fn t => if (boolSyntax.is_neg t)
  then
    is_word_eq (List.nth ((snd o strip_comb) t, 0))
  else
    false
;

(*
  This function is used to detect carry bit (substructure).
  The main problem of this typical arm8 expression to compute the carry bit
  is that in BIL we cannot handle more than 64 bits, but this expression
  uses exactly 2**64, the smallest unrepresentable-in-BIL natural number.
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
val is_plus_mod_2exp64 = fn t =>
  if (numSyntax.is_mod t)
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
      
  ``, ``^(a8s).SP_EL0
  ``, ``^(a8s).SP_EL1
  ``, ``^(a8s).SP_EL2
  ``, ``^(a8s).SP_EL3
      
  ``(*, ``^(a8s).TCR_EL1.TBI0
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

val bil_expr_bool = fn t =>
        if (t = ``T`` orelse t = ``F``) then ``Const (bool2b ^t)``
  else  raise NotABoolException
;

val bil_expr_const = fn t =>
        if  (is_boolean t) then bil_expr_const_bool (t = ``T``)
  else  if  (is_bool    t) then ``Const (bool2b ^t)``
  else
    let
      val s = word_length t;
    in
            if (s  = 1 ) then ``(Const (Reg1  ^t))``
      else  if (s  = 8 ) then ``(Const (Reg8  ^t))``
      else  if (s  = 16) then ``(Const (Reg16 ^t))``
      else  if (s  = 32) then ``(Const (Reg32 ^t))``
      else  if (s  = 64) then ``(Const (Reg64 ^t))``
      else  if (s <= 8 ) then ``(Const (Reg8  (w2w ^t)))``
      else  if (s <= 16) then ``(Const (Reg16 (w2w ^t)))``
      else  if (s <= 32) then ``(Const (Reg32 (w2w ^t)))``
      else  if (s <= 64) then ``(Const (Reg64 (w2w ^t)))``

      else  ``(Const (Reg64 (w2w ^t)))`` (* Encapsulate a generic α word to maximum size (worst choice?) *)
    end
;

val bil_expr_num = fn t =>
  if (numSyntax.is_numeral t)
    then ``Cast (Const (n2b_64 ^t)) Bit64``
    else raise NotANumberException
;

fun bil_a8e2HOLstring_prefix t prefix =
        if (is_reg t) then
          if (prefix = "")
            then  ``r2s ^((snd o dest_comb) t)``
            else  ``APPEND ^(stringSyntax.fromMLstring prefix) (r2s ^((snd o dest_comb) t))``
  else  stringSyntax.fromMLstring (prefix ^ (opname t))
;

val bil_a8e2HOLstring = fn t => bil_a8e2HOLstring_prefix t "";

val bil_a8e2string = fn t =>
        if (is_reg t) then stringSyntax.fromHOLstring (eval ``r2s ^((snd o dest_comb) t)``)
  else  opname t
;

fun bil_a8e_den_prefix t prefix = ``(Den ^(bil_a8e2HOLstring_prefix t prefix))``;
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
    , GEN_ALL (SIMP_RULE (arith_ss) [] (SPECL [``63:num``, ``n:num``, ``m:num``] PLUS_MOD_2EXP_EQ))
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
    THEN  (FULL_SIMP_TAC (srw_ss()++WORD_BIT_EQ_ss) [])
  )
;
val BIL_OP_BIT_TAC = (
        (RW_TAC (pure_ss) [])
  THEN  (REPEATN (12, BIL_EVAL_ONCE_TAC))
  THEN  (FULL_SIMP_TAC (arith_ss++WORD_ss++WORD_ARITH_ss++WORD_SHIFT_ss++WORD_EXTRACT_ss) [wordsTheory.word_extract_n2w, wordsTheory.word_and_n2w])
  THEN  EVAL_TAC
  THEN  (ASSUME_TAC (SPECL [``63:num``, ``n:num``, ``m:num``] BITS_LT_2EXP))
  THEN  (FULL_SIMP_TAC (srw_ss()) [MODN_MODM])
  THEN  (FULL_SIMP_TAC (arith_ss) [bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def, bitTheory.BITS_def, EXP2_LT_ALT])
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
val BIL_DEN_TAC = (SRW_TAC [] [Once bil_eval_exp_def, bil_env_read_def, LET_DEF, r2s_def,
			 bil_sizeof_reg_def, n2b_8_def, n2bs_def, bil_regtype_int_inf_def]);
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
  THEN  (REPEATN (13, BIL_EVAL_ONCE_TAC))
  THEN  EVAL_TAC
  THEN  ((FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_PLUS, DIV_PRODMOD_LT_2EXP]))
  THEN  (FULL_SIMP_TAC (pure_ss) [prove(``(18446744073709551616:num) = 2 ** SUC 63``, EVAL_TAC), SPECL [``63:num``, ``n:num``, ``m:num``] SUM_2EXP_EQ])
  THEN  (ASSUME_TAC ((UNDISCH_ALL o CONJ_IMP o (SPECL [``63:num``, ``n:num``, ``m:num``])) DIV_PRODMOD_LT_2EXP))
  THEN  ((FULL_SIMP_TAC (arith_ss) []))
);
val BIL_PLUS_MOD_2EXP64_TAC = (
        (REPEAT STRIP_TAC)
  THEN  (FULL_SIMP_TAC (arith_ss) [])
  THEN  (REPEATN (21, BIL_EVAL_ONCE_TAC))
  THEN  EVAL_TAC
  THEN  (FULL_SIMP_TAC (arith_ss) [MODN_MODM])
  THEN  ((Cases_on `EVEN n`)
    THEN  ((Cases_on `EVEN m`)
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, ODD_MOD2, GSYM arithmeticTheory.ODD_EVEN, Once (GSYM arithmeticTheory.MOD_PLUS)])
      THEN  EVAL_TAC
      THEN  (ASSUME_TAC ((CONJUNCT1 o UNDISCH_ALL o CONJ_IMP o SIMP_RULE (arith_ss) [] o SPECL [``63:num``, ``n:num``, ``m:num``]) RIGHT_SHIFT_SUM_LT_2EXP))
      THEN  (ASSUME_TAC ((CONJUNCT2 o UNDISCH_ALL o CONJ_IMP o SIMP_RULE (arith_ss) [] o SPECL [``63:num``, ``n:num``, ``m:num``]) RIGHT_SHIFT_SUM_LT_2EXP))
      THEN  (ASSUME_TAC ((SIMP_RULE (srw_ss()) [] o SPECL [``63:num``, ``(m DIV 2 + n DIV 2) MOD 9223372036854775808``]) EXP2_LT_ALT2))
      THEN  (ASSUME_TAC ((SIMP_RULE (srw_ss()) [] o SPECL [``63:num``, ``(m DIV 2 + (n DIV 2 + 1)) MOD 9223372036854775808``]) EXP2_LT_ALT2))
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_MOD])
    )
  )
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
    ``∀ env n. (n < dimword (:64)) = (bil_eval_exp (Cast (Const (n2b_64 n)) Bit64) env = Int (n2b_64 n))``
  , BIL_NUMERAL_TAC
);

val bil_numeral_tm = (GEN_ALL o (GEN ``n:num``) o fst o EQ_IMP_RULE o UNDISCH_ALL o SPEC_ALL) bil_numeral_expressibility_tm;

(* useless... ? *)
val bil_num_tm = tryprove(
    ``∀ env n. (n < dimword (:64)) ==> ((∃ bn. bil_eval_exp (bn) env = Int (n2b_64 n)))``
  , PROVE_TAC [bil_numeral_expressibility_tm]
);

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

val bil_plus_mod_2exp64_tm = tryprove(
    ``∀ env n m bn bm. (n < dimword (:64)) ==> ((m < dimword (:64)) ==> ((bil_eval_exp (bn) env = Int (n2b_64 n)) ∧ (bil_eval_exp (bm) env = Int (n2b_64 m)) ==> (bil_eval_exp (
          Plus  (Mult (Const 2x)
                      (Mod  (Plus (Plus (Div bn (Const 2x))
                                        (Div bm (Const 2x))
                                  )
                                  (Mult (Mod bn (Const 2x))
                                        (Mod bm (Const 2x))
                                  )
                            )
                            (Const 9223372036854775808x)
                      )
                )
                (Xor  (Mod  bn (Const 2x))
                      (Mod  bm (Const 2x))
                )
        ) env = Int (n2b_64 ((n + m) MOD 2**64)))))``
  , BIL_PLUS_MOD_2EXP64_TAC
);

val memory_access_2exp64_tm = tryprove(
    ``∀m env y x by bx .
   ((bil_eval_exp by env = Mem Bit64 m) /\
   (bil_eval_exp bx env = Int (Reg64 x))) ==>
   (!a. (m (Reg64 a)) = (Reg8 (y a))) ==>
   ((bil_eval_exp (Load by bx (Const (Reg1 1w)) Bit8) env) = (Int (Reg8 (y x))))``, (RW_TAC (srw_ss()) [])
      THEN  BIL_DEN_TAC
      THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
);

fun nw n s = wordsSyntax.mk_wordii(n, s);

(* Generic theorems for binary expressions *)
val bil_op_tms =
  let
    val bopTuples = [
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
    val uopTuples = [
          (fn s => (fst o strip_comb) ``word_2comp  ^(nw 0 s)``, fn s => ``ChangeSign        bx``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_1comp  ^(nw 0 s)``, fn s => ``Not               bx``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``w2n         ^(nw 0 s)``, fn s => ``Cast              bx Bit64``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``(w2w ^(nw 0 s)):word64``, fn s => ``Cast bx Bit64``, BIL_OP_TAC)
	, (fn s => (fst o strip_comb) ``(sw2sw ^(nw 0 s)):word64``, fn s => ``SignedCast bx Bit64``, (
	   (RW_TAC (srw_ss()) [])
           THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
	   THEN  (RW_TAC (arith_ss) [])
	   THEN BIL_OP_FULL_SIMP_TAC
	   THEN  blastLib.BBLAST_TAC
	   THEN  EVAL_TAC
	   THEN  WORD_DECIDE_TAC
	  ))
        
        (* Some special operator *)
        , (fn s => (fst o strip_comb) ``word_msb    ^(nw 0 s)``, fn s => ``SignedLessThan bx ^(bil_expr_const (nw 0 s))``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``word_lsb    ^(nw 0 s)``, fn s => ``Equal (And bx ^(bil_expr_const (nw 1 s))) ^(bil_expr_const (nw 1 s))``, BIL_LSB_TAC)
      ];
    val bopTuplesBool = [
          (fn s => (fst o strip_comb) ``T ∧ T``, fn s => ``And    bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``T ∨ T``, fn s => ``Or     bx by``, BIL_OP_TAC)
        , (fn s => (fst o strip_comb) ``T = T``, fn s => ``Equal  bx by``, BIL_OP_TAC)
      ];
    val uopTuplesBool = [
          (fn s => (fst o strip_comb) ``~T``, fn s => ``Not bx``, BIL_OP_TAC)
(*         , (fn s => (fst o strip_comb) ``¬T``, fn s => ````, BIL_OP_TAC) *)
      ];
    val bopTuplesNum = [
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
    val uopTuplesNum = [
      ];
    val iteTuple = [
        (fn s => (fst o strip_comb) ``if (c:bool) then ^(nw 0 s) else x``, fn s => ``IfThenElse bc bx by``, BIL_OP_TAC)
      ];
    val iteTupleBool = [
        (fn s => (fst o strip_comb) ``if (c:bool) then T else x``, fn s => ``IfThenElse bc bx by``, BIL_OP_TAC)
      ];
    val iteTupleNum = [
          (fn s => (fst o strip_comb) ``if (c:bool) then (n:num) else (m:num)``, fn s => ``IfThenElse bc bn bm``, BIL_OP_TAC)
      ];
    
    (* cartesian product *)
    fun prod bints opTuples =
      let
        fun prod' lst1 lst2 res =
          case lst1 of
              []          => res
            | (br, s)::l1 => prod' l1 lst2 (List.concat [List.map (fn (f, b, tac) => (f s, b s, tac, br)) lst2, res])
      in
        prod' bints opTuples []
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
    val goalgenerator_ite = fn (ite, bexp, tac, br) =>
      let
        val abopValue = bil_value ``(^ite c x y)``
      in
        (
            ite, bexp, tac, br
          , ``∀ env c x y bc bx by. (bil_eval_exp bc env = Int (bool2b c)) ∧ (bil_eval_exp bx env = Int (^br x)) ∧ (bil_eval_exp by env = Int (^br y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
    val goalgenerator_ite_bool = fn (ite, bexp, tac, _) =>
      let
        val abopValue = bil_value ``(^ite c x y)``
      in
        (
            ite, bexp, tac, ``Reg1``
          , ``∀ env c x y bc bx by. (bil_eval_exp bc env = Int (bool2b c)) ∧ (bil_eval_exp bx env = Int (bool2b x)) ∧ (bil_eval_exp by env = Int (bool2b y)) ==> (bil_eval_exp ^bexp env = ^abopValue)``
        )
      end;
    val goalgenerator_ite_num = fn (ite, bexp, tac, _) =>
      let
        val aexp = ``(^ite c n m)``;
        val abopValue = bil_value aexp;
        val concl = ``(bil_eval_exp ^bexp env = ^abopValue)``;
      in
        (
            ite, bexp, tac, ``Reg64``
          , ``∀ env c n m bc bn bm. (n < dimword(:64))
                                ==> ((m < dimword(:64))
                                ==> ((bil_eval_exp bc env = Int (bool2b c)) ∧ (bil_eval_exp bn env = Int (n2b_64 n)) ∧ (bil_eval_exp bm env = Int (n2b_64 m))
                                ==> (^concl)
                                ))``
        )
      end;
      
    val goals = List.concat [
          map goalgenerator_bop       (prod constructor_size_pairs bopTuples)
        , map goalgenerator_uop       (prod constructor_size_pairs uopTuples)
        , map goalgenerator_bop_bool  (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) bopTuplesBool)
        , map goalgenerator_uop_bool  (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) uopTuplesBool)
        , map goalgenerator_bop_num   (prod (List.filter (fn (_, n) => n = 64) constructor_size_pairs) bopTuplesNum)
        , map goalgenerator_ite_num   (prod (List.filter (fn (_, n) => n = 64) constructor_size_pairs) iteTupleNum)
        , map goalgenerator_ite_bool  (prod (List.filter (fn (_, n) => n = 1) constructor_size_pairs) iteTupleBool)
        , map goalgenerator_ite       (prod constructor_size_pairs iteTuple)
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
fun tc_exp_arm8_prefix ae prefix =
  let
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
                      bil_a8e_den_prefix ae prefix
                    , ae
                    , (GEN_ENV o GENL [``s:arm8_state``, ``w:word5``] o SPECL [if (prefix = "") then ``r2s ^((snd o dest_comb) ae)`` else ``APPEND ^(stringSyntax.fromMLstring prefix) (r2s ^((snd o dest_comb) ae))``, ``Reg Bit64``, ``Int (Reg64 ^ae)``] o SPEC_ENV) arm8_to_bil_den_tm
                  )
        else  if  (is_arm8_den ae) then (
                      bil_a8e_den_prefix ae prefix
                    , ae
                    , (GEN_ENV o GEN ``s:arm8_state`` o SPECL [
                          bil_a8e2HOLstring_prefix ae prefix
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
        else  if  (is_plus_mod_2exp64 ae)
          then
            let
              val (add1, add2, _) = extract_operands o1;
              val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_BIN bil_plus_mod_2exp64_tm (tce add1) (tce add2));
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
        else  if          (is_cond_num     ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_NUM_ITE (select_bil_op_theorem ((fst o strip_comb) ae) 64) (tce o1) (tce o2) (tce o3));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (is_cond_bool    ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_ITE (select_bil_op_theorem ((fst o strip_comb) ae) 1) (tce o1) (tce o2) (tce o3));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (boolSyntax.is_cond     ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_ITE (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o2)) (tce o1) (tce o2) (tce o3));
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
            in
              (be, ae, mp)
            end
        else  if          (wordsSyntax.is_word_1comp  ae)
                  orelse  (wordsSyntax.is_word_2comp  ae)
                  orelse  (wordsSyntax.is_word_msb    ae)
                  orelse  (wordsSyntax.is_word_lsb    ae)
                  orelse  (wordsSyntax.is_w2n         ae)
                  orelse  (wordsSyntax.is_w2w         ae)
                  orelse  (wordsSyntax.is_sw2sw       ae)
          then
            let
              val mp = (GEN_ALL o DISCH_ALL) (MP_UN (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1)) (tce o1))
              val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0)
            in
              (be, ae, mp)
            end
	(* Memory access *)
	else if is_mem ae then
	    let
	(* temporary lifter for memory. For now we do not support load from updated memory *)
		val tce_o1 = (``(Den "MEM")``, ``y:word64 -> word8``,
			      (GEN_ENV o GENL [``m:bil_int_t -> bil_int_t``] o SPECL [if (prefix = "") then ``"MEM"`` else ``APPEND ^(stringSyntax.fromMLstring prefix) "MEM"``, ``MemByte Bit64``, ``Mem Bit64 m``] o SPEC_ENV) arm8_to_bil_den_tm)
		val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (SPEC ``m:bil_int_t->bil_int_t`` memory_access_2exp64_tm) tce_o1 (tce o2));
		val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);
	    in
		(be, ae, mp)
	    end
        else  raise UnsupportedARM8ExpressionException ae
      end;
    val (be, _, mp) = tce ae;
  in
    (be, ae, (GEN_ALL o GENL [``env:environment``, ``s:arm8_state``] o DISCH_ALL_REV o DISPOSE_HYP) mp)
  end
;
val tc_exp_arm8 = fn ae => tc_exp_arm8_prefix ae "";


bil_expr_const_bool true;

bil_expr_bool ``T``;
bil_expr_bool ``F``;

bil_expr_const ``T``;
bil_expr_const ``2w:bool[2]``;
bil_expr_const ``2w:bool[12]``;
bil_expr_const ``2w:bool[32]``;
bil_expr_const ``2w:bool[64]``;

bil_expr_num ``5:num``;


(* Transcompiler arm8 expressions to BIL model expressions *)
val ae = ``5w:bool[3]``;
val (o1, o2, o3) = extract_operands ae;
wordsSyntax.is_n2w ae;
 (* If condition *)
 (bil_expr_const ae, ae,
  GEN_ALL (SPECL [``env:environment``, eval ``w2b ^ae``] bil_const_tm)
);

val ae = ``T``;
(is_boolean ae);
(* then *) (
bil_expr_bool ae
, ae
, GEN_ALL (SPECL [``env:environment``, ``bool2b ^ae``] bil_const_tm)
);

val ae = ``5:num``;
(numSyntax.is_numeral ae);
    (
     bil_expr_num ae
   , ae
   , GEN_ALL (SPECL [``env:environment``, ae] bil_numeral_tm)
    );

val ae = ``aaa.REG 1w``;
(is_reg ae);
val prefix = "";
    (
     bil_a8e_den_prefix ae prefix
   , ae
   , (GEN_ENV o GENL [``s:arm8_state``, ``w:word5``] o SPECL [if (prefix = "") then ``r2s ^((snd o dest_comb) ae)`` else ``APPEND ^(stringSyntax.fromMLstring prefix) (r2s ^((snd o dest_comb) ae))``, ``Reg Bit64``, ``Int (Reg64 ^ae)``] o SPEC_ENV) arm8_to_bil_den_tm
    );

val ae = ``aaa.PC``;
val prefix = "";
(is_arm8_den ae);
(
    bil_a8e_den_prefix ae prefix
  , ae
  , (GEN_ENV o GEN ``s:arm8_state`` o SPECL [
     bil_a8e2HOLstring_prefix ae prefix
   , eval ``bil_type_val_int_inf ^(bil_value ae)``
   , ``^(bil_value ae)``
     ] o SPEC_ENV) arm8_to_bil_den_tm
    );

(* something strange here *)
val ae = ``aaa.PSTATE.Z``;
val prefix = "";
(is_arm8_den ae);
(
    bil_a8e_den_prefix ae prefix
  , ae
  , (GEN_ENV o GEN ``s:arm8_state`` o SPECL [
     bil_a8e2HOLstring_prefix ae prefix
   , eval ``bil_type_val_int_inf ^(bil_value ae)``
   , ``^(bil_value ae)``
     ] o SPEC_ENV) arm8_to_bil_den_tm
    );

(* overflows *)
tc_exp_arm8_prefix ``T`` "";
tc_exp_arm8_prefix ``aaa.REG 1w`` "";
tc_exp_arm8_prefix ``(aaa.REG 1w) + (aaa.REG 2w)`` "";
tc_exp_arm8_prefix ``(aaa.REG 1w) * (aaa.REG 1w)`` "";
tc_exp_arm8_prefix ``(aaa.REG 2w) + 3w`` "";
tc_exp_arm8_prefix ``(aaa.REG 2w) >=+ 3w`` "";
tc_exp_arm8_prefix ``T /\ F`` "";
tc_exp_arm8_prefix ``T /\ (aaa.PSTATE.Z)`` "";
tc_exp_arm8_prefix ``~(aaa.PSTATE.Z)`` "";
tc_exp_arm8_prefix ``if T then F else T`` "";
tc_exp_arm8_prefix ``if T then (aaa.REG 2w) + 3w else 2w`` "";

val pat = (valOf (arm8_pattern "BitfieldMove64"));
arm8_step pat;

val [t1] = arm8_step_hex "0x910003e1";  (* mov     x1, sp *)
tc_exp_arm8_prefix ``s.PC + 4w`` "";
tc_exp_arm8_prefix ``s.SP_EL0 + 0w`` "";

(* From the manual  *)
(* https://www.element14.com/community/servlet/JiveServlet/previewBody/41836-102-1-229511/ARM.Reference_Manual.pdf *)

(* add 32-bit register  *)
arm8_step_code `ADD W0, W1, W2`;
tc_exp_arm8_prefix ``(w2w
              ((w2w (s.REG (1w :word5)) :word32) +
               (w2w (s.REG (2w :word5)) :word32)) :word64)`` "";
(* FAILURE *)

(* 64-bit addition *)
arm8_step_code `ADD X0, X1, X2`;
tc_exp_arm8_prefix `` s.REG 1w + s.REG 2w`` "";

(* add 64-bit extending register  *)
arm8_step_code `ADD X0, X1, W2, SXTW `;
tc_exp_arm8_prefix `` s.REG 1w + ExtendValue (s.REG 2w,ExtendType_SXTW,0)`` "";
(* FAILURE *)

(* add 64-bit immediate  *)
arm8_step_code `ADD X0, X1, #42 `;
tc_exp_arm8_prefix ``s.REG 1w + 42w`` "";

(* Absolute branch to address in Xn *)
arm8_step_code `BR X0`;
arm8_step_code `BLR X0`;

tc_exp_arm8_prefix ``s.PC + 4w`` "";

arm8_step_code `B #4`;


(* Arithmetics instructions *)
arm8_step_code `ADD W0, W1, W2, LSL #3`;
(* still problems with 32 bits *)

(* Guancio: my first extension *)
arm8_step_code `SUB X0, X4, X3, ASR #2`;
tc_exp_arm8_prefix ``s.REG 4w − s.REG 3w ≫ 2`` "";

val ae = ``s.REG 3w ≫ 2``;
tc_exp_arm8_prefix ae "";

val (o1, o2, o3) = extract_operands ae;
wordsSyntax.is_word_asr ae;
(* val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1)) (tce o1) (tce o2)); *)
val opH = ((fst o strip_comb) ae);
val  size = (word_size o1);
(select_bil_op_theorem ((fst o strip_comb) ae) (word_size o1));

val constr = fst (List.nth (List.filter (fn (_, s) => s = size) constructor_size_pairs, 0));

val ae = ``s.REG 3w ≫ 2``;
val t = prove(``2 = w2n (2w:word64)``, (FULL_SIMP_TAC (srw_ss()) []));
val ae1 = (snd o dest_eq o concl) (REWRITE_CONV [Once t] ae);
val ae2 = (snd o dest_eq o concl) (REWRITE_CONV [(GSYM wordsTheory.word_asr_bv_def)] ae1);

val ae2 = (snd o dest_eq o concl) (REWRITE_CONV [Once t, (GSYM wordsTheory.word_asr_bv_def)] ae1);
tc_exp_arm8_prefix ae2 "";

val ae = ``s.REG 3w >>~ 2w``;
tc_exp_arm8_prefix ae "";





arm8_step_code `CMP W3, W4 `;
arm8_step_code `CMP X3, X4 `;

tc_exp_arm8_prefix ``((word_msb (s.REG 3w) ⇔ word_msb (¬s.REG 4w)) ∧
               (word_msb (s.REG 3w) ⇎
                BIT 63 (w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1)))`` "";

tc_exp_arm8_prefix ``
((if
                  w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1 <
                  18446744073709551616
                then
                  w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1
                else
                  (w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1) MOD
                  18446744073709551616) ≠
               w2n (s.REG 3w) + w2n (¬s.REG 4w) + 1)
`` "";

tc_exp_arm8_prefix ``(s.REG 3w − s.REG 4w = 0w)`` "";

tc_exp_arm8_prefix ``word_msb (s.REG 3w − s.REG 4w)`` "";

List.length bil_op_tms;

arm8_step_code `BIC X0, X0, X1 `;
tc_exp_arm8_prefix ``s.REG 0w && ¬s.REG 1w`` "";

arm8_step_code `SUB X0, X4, X3`;
tc_exp_arm8_prefix ``s.REG 4w − s.REG 3w`` "";

arm8_step_code `SUBS X0, X4, X3`;

tc_exp_arm8_prefix ``
((word_msb (s.REG 4w) ⇔ word_msb (¬s.REG 3w)) ∧
               (word_msb (s.REG 4w) ⇎
                BIT 63 (w2n (s.REG 4w) + w2n (¬s.REG 3w) + 1)))`` "";


arm8_step_code `CSINC X0, X1, X0, NE`;
tc_exp_arm8_prefix ``
if ¬s.PSTATE.Z then s.REG 1w else s.REG 0w + 1w
`` "";

(* UNSUPPORTED *)
arm8_step_code `LDRB X0, [X1]`;
arm8_step_code `LDRSB X0, [X1]`;

tc_exp_arm8_prefix ``sw2sw (s.MEM (s.REG 1w + 0w))`` "";

tc_exp_arm8_prefix ``(sw2sw (0w:word8)):word64`` "";

tc_exp_arm8_prefix ``s.MEM (0w:word64)`` "";

tc_exp_arm8_prefix ``(w2w (0w:word8)):word64`` "";

tc_exp_arm8_prefix ``(w2n (0w:word8))`` "";

(* cartesian product *)
fun prod bints opTuples =
    let
        fun prod' lst1 lst2 res =
            case lst1 of
		[]          => res
              | (br, s)::l1 => prod' l1 lst2 (List.concat [List.map (fn (f, b, tac) => (f s, b s, tac, br)) lst2, res])
    in
        prod' bints opTuples []
    end;

val uopTuples = [
    (fn s => (fst o strip_comb) ``w2n         ^(nw 0 s)``, fn s => ``Cast              bx Bit64``, BIL_OP_TAC)
];

val v1 = (prod constructor_size_pairs uopTuples);

    val goalgenerator_uop = fn (auop, bexp, tac, br) =>
      let
        val auopValue = bil_value ``(^auop x)``
      in
        (
            auop, bexp, tac, br
            , ``∀ env x bx. (bil_eval_exp bx env = Int (^br x)) ==> (bil_eval_exp ^bexp env = ^auopValue)``
        )
      end;

val goals = map goalgenerator_uop v1;

map (fn (abop, bop, tac, br, g) => (abop, bop, br, tryprove (g, tac))) goals;

(* Signed cast *)
tc_exp_arm8_prefix ``(sw2sw (0w:word8)):word64`` "";

val uopTuples = [
    (fn s => (fst o strip_comb) ``(sw2sw ^(nw 0 s)):word64``, fn s => ``SignedCast bx Bit64``, 
      ((RW_TAC (srw_ss()) [])
      THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
      THEN  (RW_TAC (arith_ss) [])
      THEN  BIL_OP_FULL_SIMP_TAC
      THEN  blastLib.BBLAST_TAC
      THEN  EVAL_TAC
      THEN  WORD_DECIDE_TAC)
)
];
val v1 = (prod constructor_size_pairs uopTuples);

val goals = map goalgenerator_uop v1;

map (fn (abop, bop, tac, br, g) => (abop, bop, br, tryprove (g, tac))) goals;

val (abop, bop, tac, br, g1) = List.nth(goals,4);

prove(``^g1``,
      (RW_TAC (srw_ss()) [])
      THEN  (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def])
      THEN  (RW_TAC (arith_ss) [])
      THEN BIL_OP_FULL_SIMP_TAC
      THEN  blastLib.BBLAST_TAC
      THEN  EVAL_TAC
      THEN  WORD_DECIDE_TAC
  )

0xFFFFFFFFFFFFFFw
0xFFFFFFFFFFFFFFFFw
0xFFFFFFFFFFFFFFw
0xFFFFFFFFFFFFFFFFw

(FULL_SIMP_TAC (pure_ss) [bil_scast_def])
(FULL_SIMP_TAC (srw_ss()) [])
(FULL_SIMP_TAC (pure_ss) [wordsTheory.word_msb_def])

prove (``(((x :word32) <+ (0w :word32)) :bool) ==> ((((1w :32 word) @@ (0x7fffffffw && x :word32)) :word64) = (sw2sw x :word64))``,
       blastLib.BBLAST_TAC);


tc_exp_arm8_prefix ``(w2w (2w + 4w:word8)):word64 = 3w`` "";

(* MEMORY LOAD *)

val ae = ``s.MEM (0w:word64)``;
val prefix = "";
tc_exp_arm8_prefix ae "";

is_mem ae;
(
 bil_a8e_den_prefix ae prefix
, ae
, 

val (o1, o2, o3) = extract_operands ae;


val tce_o2 = tce o2;
val tce_o1 = (``(Den "MEM")``, ``y:word64 -> word8``,
	      (GEN_ENV o GENL [``m:bil_int_t -> bil_int_t``] o SPECL [if (prefix = "") then ``"MEM"`` else ``APPEND ^(stringSyntax.fromMLstring prefix) "MEM"``, ``MemByte Bit64``, ``Mem Bit64 m``] o SPEC_ENV) arm8_to_bil_den_tm);

val thImp= prove(``∀m env y x by bx .
   ((bil_eval_exp by env = Mem Bit64 m) /\
   (bil_eval_exp bx env = Int (Reg64 x))) ==>
   (!a. (m (Reg64 a)) = (Reg8 (y a))) ==>
   ((bil_eval_exp (Load by bx (Const (Reg1 1w)) Bit8) env) = (Int (Reg8 (y x))))
   ``,
      (RW_TAC (srw_ss()) [])
      THEN  BIL_DEN_TAC
      THEN (SIMP_TAC (srw_ss()) [Once bil_eval_exp_def]));

val (be1, ae1, thm1) = tce_o1;
val (be2, ae2, thm2) = tce_o2;

List.nth (bil_op_tms,1);

(* val hyp1 = ((UNDISCH_ALL o SPEC_ALL) thm1); *)
(* val hyp2 = ((UNDISCH_ALL o SPEC_ALL) thm2); *)

(* This does not work anymore since we use conjunction. *)
(* TODO, remove conjunction inthe hypothesis and puy implications *)
(* val spec = (((SPECL [ae1, ae2, be1, be2]) o SPEC_ENV) (SPEC ``m:bil_int_t->bil_int_t`` thImp)); *)
(* val res1 = (MP spec hyp1); *)
(* val res2 = (MP res1 hyp2); *)

MP_BIN (SPEC ``m:bil_int_t->bil_int_t`` thImp) (be1, ae1, thm1) (be2, ae2, thm2);

val mp = (GEN_ALL o DISCH_ALL) (MP_BIN (SPEC ``m:bil_int_t->bil_int_t`` thImp) tce_o1 tce_o2);

val be = List.nth ((snd o strip_comb o fst o dest_eq o concl o UNDISCH_ALL o SPEC_ALL) mp, 0);


val ae = ``s.MEM (0w:word64)``;
val prefix = "";
tc_exp_arm8_prefix ae "";


val ae = ``s.MEM ((s.REG 0w) + 0w:word64)``;
val prefix = "";
tc_exp_arm8_prefix ae "";



val ae = ``s.REG (0w)``;
val prefix = "";
tc_exp_arm8_prefix ae "";




List.nth(bil_op_tms, 0);


(* LOAD OF A WORLD *)
arm8_step_code `LDR X0, [X1]`;
