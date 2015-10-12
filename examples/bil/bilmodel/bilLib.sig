signature bilLib =
sig
  include Abbrev
  
  val bil_state_init              : term -> term
  val bil_state_step_update       : term -> term -> term
  val bil_exec_program_noevalenv  : term * int -> int * term
  val eval_update                 : term -> term
  val bil_exec_program            : term * int -> int * term
end
