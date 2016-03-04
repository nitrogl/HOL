signature arm8bilLib =
sig
  include Abbrev
  
  val eval                    : term -> term
  
  
  val BIL_CONST_TAC           : tactic
  val BIL_OP_FULL_SIMP_TAC    : tactic
  val BIL_EVAL_ONCE_TAC       : tactic
  val BIL_LSB_TAC             : tactic
  val BIL_OP_BIT_TAC          : tactic
  val BIL_OP_TAC              : tactic
  val BIL_DEN_TAC             : tactic
  val BIL_NUMERAL_TAC         : tactic
  val BIL_PLUS_LT_2EXP64_TAC  : tactic
  val BIL_PLUS_MOD_2EXP64_TAC : tactic
  
  val bil_a8e2HOLstring       : term -> term
  val tc_exp_arm8_prefix      : term -> string -> term * term * thm
  val tc_exp_arm8             : term -> term * term * thm
end
