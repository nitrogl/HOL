signature proofTools =
sig
  include Abbrev
  
  val eval          : term -> term
  val opname        : term -> string
  val fst3          : 'a * 'b * 'c -> 'a
  val snd3          : 'a * 'b * 'c -> 'b
  val trd3          : 'a * 'b * 'c -> 'c
  val tryprove      : term * tactic -> thm
  
  val REPEATN       : int * tactic -> tactic
  val EVALBOOL      : term -> thm
  val MP_NOFAIL     : thm -> thm -> thm
  val SPECX         : thm -> thm
  
  val DISCHL        : term list -> thm -> thm
  val CONJL         : thm list -> thm
  
  val MP_CONJL      : thm -> thm list -> thm
  val MP_CONJ       : thm -> thm * thm -> thm
  val MPL           : thm -> thm list -> thm
  
  val DISCH_ALL_REV : thm -> thm
  val CONJ_IMP      : thm -> thm
  val DISPOSE_HYP   : thm -> thm
end
