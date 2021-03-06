(* This file has been generated by java2opSem from /home/helen/Recherche/hol/HOL/examples/opsemTools/java2opsem/testFiles/javaFiles/ArraySwapElement.java*)


open HolKernel Parse boolLib
stringLib IndDefLib IndDefRules
finite_mapTheory relationTheory
newOpsemTheory
computeLib bossLib;

val _ = new_theory "ArraySwapElement";

(* Method swap*)
val MAIN_def =
  Define `MAIN =
    RSPEC
    (\state.
      ((ScalarOf (state ' "i")>0)/\(ScalarOf (state ' "i")<ScalarOf (state ' "aLength")))/\((ScalarOf (state ' "j")>0)/\(ScalarOf (state ' "j")<ScalarOf (state ' "aLength"))))
      (Seq
        (Assign "tmp"
          (Arr "a"
            (Var "i")
          )
        )
        (Seq
          (ArrayAssign "a"
            (Var "i")
            (Arr "a"
              (Var "j")
            )
          )
          (ArrayAssign "a"
            (Var "j")
            (Var "tmp")
          )
        )
      )
    (\state1 state2.
      ((ArrayOf (state2 ' "a") ' (Num(ScalarOf (state1 ' "i"))))=(ArrayOf (state1 ' "a") ' (Num(ScalarOf (state1 ' "j")))))/\((ArrayOf (state2 ' "a") ' (Num(ScalarOf (state1 ' "j"))))=(ArrayOf (state1 ' "a") ' (Num(ScalarOf (state1 ' "i"))))))
    `

    val intVar_def =
  	     Define `intVar =["i";"j";"tmp"]  `

    val arrVar_def =
  	     Define `arrVar =["a"]  `

  val _ = export_theory();
