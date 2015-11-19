signature arm8bilLib =
sig
  include Abbrev
  
  val eval                    : term -> term
  
  val list_intersect          : ''a list -> ''a list -> ''a list
  val list_union              : 'a list -> 'a list -> 'a list
  val list_diff               : ''a list -> ''a list -> ''a list
  val list_exclusion          : ''a list -> ''a list -> ''a list
  val list_exclusion_id       : ''a list -> ''a list -> ''a list * ''a list
  val list_split              : ('a * 'b) list -> 'a list * 'b list
  val list_uniq               : ''a list -> ''a list
  
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
  
  val arm8_state_zero         : term
  val tc_exp_arm8             : term -> term * term * thm
  val tc_stmt_arm8_hex        : string -> term * thm list * thm list
  val tc_stmt_arm8_hexlist    : string list -> (term * thm list) list
  val a8s2bs_step_program     : string list -> term -> term * thm list
end
