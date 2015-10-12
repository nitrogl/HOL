(* ========================================================================= *)
(* FILE          : proofTools.sml                                            *)
(* DESCRIPTION   : Several proof tools collection.                           *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

structure proofTools :> proofTools =
struct

open HolKernel boolLib bossLib Parse;

(* ------------------------------------------------------------------------- *)
exception ProveException of term * string;

(* ------------------------------------------------------------------------- *)
(*  Misc tools                                                               *)
(* ------------------------------------------------------------------------- *)
fun eval t = (snd o dest_eq o concl o EVAL) t;
fun opname t = (fst o dest_const o fst o strip_comb) t;
val fst3 = fn (t, _, _) => t;
val snd3 = fn (_, t, _) => t;
val trd3 = fn (_, _, t) => t;

(*
  Wrapper of prove function.
  It raises a ProveException if unable to prove, showing the initial
  goal (pretty printed).
*)
val tryprove = fn (goal, tac) => (prove(goal, tac))
    handle HOL_ERR {message: string, origin_function: string, origin_structure: string} => raise ProveException(goal, message)
;

fun REPEATN (n, tac) = EVERY (List.tabulate (n, fn n => tac));
val EVALBOOL = (EQT_ELIM o EVAL);
fun MP_NOFAIL th1 th2 = MP th1 th2 handle e => th1;
val SPECX = (snd o SPEC_VAR);

(* Discharge a list of terms *)
fun DISCHL tml th = case tml of
    []    => th
  | t::l  => DISCHL l (DISCH t th)
;

(* Conjunction of list elements *)
val CONJL = fn lst =>
  if (List.length lst = 0)
    then TRUTH
    else
      let
        val thm1::thms = lst; (* apparently it is not an exhaustive pattern, but here the list is not-null, then everything is ok *)
        fun conjl lst thm = case lst of
            []   => thm
          | e::l => conjl l (CONJ e thm)
      in
        conjl thms thm1
      end
;

(*
  MP on conjunctions:
  
      A1 |- t1 /\ t2 ==> t2   A2 |- t1   A3 |- t2
   --------------------------------------------------  MP
        A1 u A2 u A3 |- t2
*)
fun MP_CONJL thImp l = MP thImp (CONJL l);
fun MP_CONJ thImp (thm1, thm2) = MP thImp (CONJ thm1 thm2);

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
 *  implications.                                                            *
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
              THEN  (RW_TAC (srw_ss()++ARITH_ss) [])
              THEN  (FULL_SIMP_TAC (srw_ss()++ARITH_ss) []);
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

(* ------------------------------------------------------------------------- *)
end