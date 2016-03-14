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
  
  val is_arm8_app             : term -> term -> bool
  val is_bool                 : term -> bool
  val is_num                  : term -> bool
  val is_reg                  : term -> bool
  val is_mem                  : term -> bool
  val is_boolean              : term -> bool
  val is_eq_bool              : term -> bool
  val is_eq_num               : term -> bool
  val is_cond_num             : term -> bool
  val is_cond_bool            : term -> bool
  val is_neq                  : term -> bool
  val is_word_eq              : term -> bool
  val is_word_neq             : term -> bool
  val is_plus_lt_2exp64       : term -> bool
  val is_plus_mod_2exp64      : term -> bool
  val is_arm8_den             : term -> bool

  val bil_expr_const          : term -> term
  val bil_value_word          : term -> term
  val bil_value_bool          : term -> term
  val bil_value_num           : term -> term
  val bil_value_reg           : term -> term
  val bil_value               : term -> term


  val bil_a8e2HOLstring       : term -> term
  val bil_a8e2HOLstring_prefix: term -> string -> term
  val bil_a8e2string          : term -> "string"
  val tc_exp_arm8_prefix      : term -> string -> term * term * thm
  val tc_exp_arm8             : term -> term * term * thm
end
