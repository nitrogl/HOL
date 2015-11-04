(* ========================================================================= *)
(* FILE          : arithScript.sml                                           *)
(* DESCRIPTION   : Arithmetic supporting theorems.                           *)
(* AUTHOR        : (c) Roberto Metere, KTH - Royal Institute of Technology   *)
(* DATE          : 2015                                                      *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Parse;
open wordsTheory arithmeticTheory proofTools;

val _ = new_theory "arith";
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  Theorems - Supporting important theorems                                 *)
(* ------------------------------------------------------------------------- *)

val SUC_INC = store_thm("SUC_INC", ``∀n. SUC n = n + 1``, numLib.ARITH_TAC);
val ADDSUB_COMM = store_thm("ADDSUB_COMM", ``∀(n:num) (h:num). (h <= n) ==> (n + h - h = n - h + h)``, numLib.ARITH_TAC);
val PREC_EXISTS = store_thm("PREC_EXISTS"
  , ``∀ (n:num). (0 < n) ==> (∃m. n = m + 1)``
  ,       (REPEAT STRIP_TAC)
    THEN  (EXISTS_TAC ``(n:num) - 1``)
    THEN  (RW_TAC (arith_ss) []) 
);

val MULT_MOD2_01 = store_thm("MULT_MOD2_01", ``∀ (j:num) (k:num). (j MOD 2 * k MOD 2 = 0) ∨ (j MOD 2 * k MOD 2 = 1)``, (RW_TAC (srw_ss()) [arithmeticTheory.MOD_2]));

(* This theorem comes from ARMv7 lifter by Hamed Nemati *)
val BIT_DIV_MOD = store_thm("BIT_DIV_MOD"
  , ``∀ (n:num) (h:num). BIT h n = ((n DIV 2**h) MOD 2 = 1)``
  , (RW_TAC (srw_ss()) [bitTheory.MOD_2EXP_def, bitTheory.DIV_2EXP_def, bitTheory.BIT_def, bitTheory.BITS_def, SUC_INC])
);

val MOD_LESS_ALT = store_thm("MOD_LESS_ALT"
  , ``∀ (j:num) (n:num) (m:num). (0 < n) ==> ((n <= m) ==> (j MOD n < m))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPECL [``j:num``, ``n:num``])) arithmeticTheory.MOD_LESS))
    THEN  (FULL_SIMP_TAC (arith_ss) [])
);

val BITS_LT_2EXP = store_thm("BITS_LT_2EXP"
  , ``∀ (h:num) (j:num) (k:num). BITS h j k < 2**(SUC h)``
  , (RW_TAC (arith_ss) [bitTheory.MOD_2EXP_def, bitTheory.BITS_def, MOD_LESS_ALT])
);

val MODN_MODM = store_thm("MODN_MODM"
  , ``∀n k m. (0 < n) ==> ((n <= m) ==> (k MOD n MOD m = k MOD n))``
  , (RW_TAC (srw_ss()) [MOD_LESS_ALT])
);

val EXP2_LT_ALT = store_thm("EXP2_LT_ALT"
  , ``∀ (n:num) (m:num) (j:num). ((j < 2**n) ==> ((j DIV 2**m) < 2**(n - m)))``
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

val EXP2_LT_ALT2 = store_thm("EXP2_LT_ALT2"
  , ``∀ (n:num) (m:num). (m < 2**n = 2*m < 2** SUC n) ∧ (m < 2**n = 2*m + 1 < 2** SUC n)``
  ,       (REPEAT STRIP_TAC)
    THENL [
              (REWRITE_TAC [Once (prove(``m = ((2:num)*m) DIV 2``, FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.MULT_DIV, Once arithmeticTheory.MULT_COMM]))])
        THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EXP2_LT])
      ,       (REWRITE_TAC [Once (prove(``m = ((2:num)*m) DIV 2``, FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.MULT_DIV, Once arithmeticTheory.MULT_COMM]))])
        THEN  (ASSUME_TAC (prove(``EVEN (2*m)``, PROVE_TAC [arithmeticTheory.EVEN_EXISTS])))
        THEN  (FULL_SIMP_TAC (srw_ss()) [SPEC ``2*m:num`` EVEN_DIV_EQ_SUC])
        THEN  (FULL_SIMP_TAC (arith_ss) [SUC_INC, arithmeticTheory.EXP2_LT])
    ]

);

val n2w_w2w_concat_0 = store_thm("n2w_w2w_concat_0", 
    ``∀(w :β word) (z :α word) (c :γ word). FINITE 𝕌((:α) :α itself) ==> (dimindex (:β) <= dimindex (:γ) ==> ((z = 0w) ==> ((c = (n2w (w2n w) :γ word)) ==> (c = z @@ w))))``
  ,       (RW_TAC (pure_ss) [])
    THEN  (ASSUME_TAC (ISPEC ``w :β word`` wordsTheory.w2n_lt))
    THEN  (ASSUME_TAC ((UNDISCH_ALL o CONJ_IMP o (SPECL [``w:β word``, ``w2n (w:β word)``])) wordsTheory.word_concat_0_eq))
    THEN  ((FULL_SIMP_TAC (srw_ss()) []))
);

val ADDN_DIVN_DIVN_ADD1 = store_thm("ADDN_DIVN_DIVN_ADD1"
  , ``∀(n :num). (2 + n) DIV 2 = 1 + n DIV 2``
  ,       GEN_TAC
    THEN  (ASSUME_TAC (MP ((DISCH_ALL o (SPECL [``1:num``, ``n:num``]) o UNDISCH_ALL o (SPEC ``2:num``)) arithmeticTheory.ADD_DIV_ADD_DIV) (prove(``(0:num) < 2``, EVAL_TAC))))
    THEN  (FULL_SIMP_TAC (srw_ss()) [])
);

val MULT_SUM = store_thm("MULT_SUM"
  , ``∀ (n:num) (m:num). (m * n = SUM m (λx.n))``
  ,       (Induct_on `m`)
    THEN  (FULL_SIMP_TAC (arith_ss) [sum_numTheory.SUM_def,arithmeticTheory.MULT_SUC])
);

val MULT_SUM_COMM = store_thm("MULT_SUM_COMM"
  , ``∀ (j:num) (k:num). SUM j (λx. k) = SUM k (λx. j)``
  , (RW_TAC (arith_ss) [GSYM MULT_SUM])
);

val EVENS_DIV2_ADD = store_thm("EVENS_DIV2_ADD"
  , ``∀ (j:num) (k:num). (EVEN j ∧ EVEN k) ==> (j DIV 2 + k DIV 2 = (j + k) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
);

val ODDS_DIV2_ADD = store_thm("ODDS_DIV2_ADD"
  , ``∀ (j:num) (k:num). (ODD  j ∧ ODD  k) ==> (j DIV 2 + k DIV 2 = (j + k - 2) DIV 2)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
);

val ODDS_DIV2_ADD_ALT = prove(
    ``∀ (j:num) (k:num). (ODD  j ∧ ODD  k) ==> (j DIV 2 + k DIV 2 = (j + k) DIV 2 - 1)``
  ,       (RW_TAC (pure_ss) [])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD_EXISTS])
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC, MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
    THEN  (FULL_SIMP_TAC (arith_ss) [Once arithmeticTheory.MULT_COMM])
    THEN  (FULL_SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_ASSOC])
    THEN  (FULL_SIMP_TAC (arith_ss) [GSYM arithmeticTheory.LEFT_ADD_DISTRIB])
    THEN  (FULL_SIMP_TAC (pure_ss) [arithmeticTheory.ADD_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [ADDN_DIVN_DIVN_ADD1])
    THEN  (FULL_SIMP_TAC (pure_ss) [MULT_SUM, MULT_SUM_COMM])
    THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.DIV_MULT])
    THEN  (FULL_SIMP_TAC (srw_ss()) [(UNDISCH_ALL o (SPEC ``2:num``)) arithmeticTheory.MULT_DIV])
);

val EVEN_ODD_MIX_DIV2_ADD = store_thm("EVEN_ODD_MIX_DIV2_ADD"
  , ``∀ (j:num) (k:num). (EVEN j ≠ EVEN k) ==> (j DIV 2 + k DIV 2 = (j + k - 1) DIV 2)``
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
      THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD_DIV_ADD_DIV])
      THEN  (FULL_SIMP_TAC (pure_ss) [MULT_SUM, MULT_SUM_COMM])
      THEN  (FULL_SIMP_TAC (srw_ss()) [GSYM MULT_SUM, arithmeticTheory.MULT_DIV])
      THEN  (FULL_SIMP_TAC (arith_ss) [])
    )
);

val ODD_POS = store_thm("ODD_POS"
  , ``∀ (n:num). (ODD n) ==> (0 < n)``
  , Induct THEN (FULL_SIMP_TAC (arith_ss) [])
);

val ODD_MOD2 = store_thm("ODD_MOD2"
  , ``∀ (n:num). (ODD n) = (n MOD 2 = 1)``
  ,       (RW_TAC (arith_ss) [arithmeticTheory.MOD_2])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_ODD])
);

val ODD_SUM_GT1 = store_thm("ODD_SUM_GT1"
  , ``∀ (j:num) (k:num). ODD j ==> (ODD k ==> (1 < j + k))``
  , Induct THEN Induct THEN (FULL_SIMP_TAC (arith_ss) [])
);

val GT1_DIV2_GT0 = store_thm("GT1_DIV2_GT0"
  , ``∀ (n:num). 1 < n ==> (0 < n DIV 2)``
  ,       Induct
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (Induct_on `n`)
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (RW_TAC (arith_ss) [SUC_INC])
    THEN  (SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [ADDN_DIVN_DIVN_ADD1])
);

val GT1_DIV2_GE1 = prove(
    ``∀ (n:num). 1 < n ==> (1 ≤ n DIV 2)``
  ,       Induct
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (Induct_on `n`)
    THEN  (FULL_SIMP_TAC (arith_ss) [])
    THEN  (RW_TAC (arith_ss) [SUC_INC])
    THEN  (SIMP_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM])
    THEN  (FULL_SIMP_TAC (arith_ss) [ADDN_DIVN_DIVN_ADD1])
);

val SUB2_DIV2_DIV2_SUB1 = store_thm("SUB2_DIV2_DIV2_SUB1"
  , ``∀(n :num). (n - 2) DIV 2 = n DIV 2 - 1``
  ,       Induct
    THENL [
      (FULL_SIMP_TAC (arith_ss) [])
    ,
            (Induct_on `n`)
      THENL [
              (FULL_SIMP_TAC (arith_ss) [])
      ,       (RW_TAC (pure_ss) [])
        THEN  (FULL_SIMP_TAC (arith_ss) [SUC_INC])
        THEN  (RW_TAC (pure_ss) [Once arithmeticTheory.ADD_COMM, ADDN_DIVN_DIVN_ADD1])
        THEN  (FULL_SIMP_TAC (arith_ss) [])
      ]
    ]
);

val EVEN_DIV_EQ_SUC = store_thm("EVEN_DIV_EQ_SUC"
  , ``∀ (n:num). (EVEN n) = (n DIV 2 = (SUC n) DIV 2)``
  ,       GEN_TAC
    THEN  EQ_TAC
    THENL [
              (REPEAT STRIP_TAC)
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

val ODDSUC_DIV2_EQ_SUC = store_thm("ODDSUC_DIV2_EQ_SUC"
  , ``∀ (n:num). (ODD (SUC n)) = (n DIV 2 = (SUC n) DIV 2)``
  , (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.ODD, GSYM arithmeticTheory.EVEN_ODD, EVEN_DIV_EQ_SUC])
);

val ODD_DIV2_EQ_PREC = store_thm("ODD_DIV2_EQ_PREC"
  , ``∀ (n:num). 0 < n ==> ((ODD n) = (n DIV 2 = (n - 1) DIV 2))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC ((UNDISCH_ALL o SPEC_ALL) PREC_EXISTS))
    THEN  (FULL_SIMP_TAC (srw_ss()) [])
    THEN  (ASSUME_TAC ((UNDISCH_ALL o (SPEC ``m:num``)) ODDSUC_DIV2_EQ_SUC))
    THEN  (FULL_SIMP_TAC (pure_ss) [SUC_INC])
    THEN  (RW_TAC (arith_ss) [ODDSUC_DIV2_EQ_SUC])
);

val EVEN_ODD_MIX_DIV2 = prove(
    ``∀ (j:num) (k:num). (EVEN j ≠ EVEN k) ==> ((j + k - 1) DIV 2 = (j + k) DIV 2)``
  ,       (REPEAT STRIP_TAC)
    THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_ODD, GSYM arithmeticTheory.ODD_ADD, GSYM ODD_DIV2_EQ_PREC, ODD_POS])
);

val SUM_LT_2EXP = store_thm("SUM_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num). (j + k < 2**n) ==> (j < 2**n)``
  , (RW_TAC (arith_ss) [])
);

(*
    Lemmas/Theorems dependency:

     EVENS_DIV2_ADD
     ODDS_DIV2_ADD
     SUB2_DIV2_DIV2_SUB1
     ODD_SUM_GT1
     GT1_DIV2_GT0
     ADDSUB_COMM
     ODD_POS
     ODD_DIV2_EQ_PREC
     EVEN_ODD_MIX_DIV2_ADD
     SUM_LT_2EXP
*)
val SUM_2EXP_EQ = store_thm("SUM_2EXP_EQ"
  , ``∀ (n:num) (j:num) (k:num). (j + k < 2**(SUC n)) = ((j DIV 2) + (k DIV 2) + (j MOD 2) * (k MOD 2) < 2**n)``
  ,       (REPEAT GEN_TAC)
    THEN  EQ_TAC
    THENL [
            (Cases_on `EVEN j = EVEN k`)
      THENL [
              (RW_TAC (pure_ss) [arithmeticTheory.MOD_2])
        THENL [
                (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV2_ADD, (GSYM arithmeticTheory.EXP2_LT)])
          , (
                  (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
            THEN  (FULL_SIMP_TAC (bool_ss) [GSYM arithmeticTheory.EVEN_ODD])
          )
          THEN  (FULL_SIMP_TAC (arith_ss) [ODDS_DIV2_ADD, (GSYM arithmeticTheory.EXP2_LT)])
          THEN  (FULL_SIMP_TAC (arith_ss) [SUB2_DIV2_DIV2_SUB1])
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o SPEC_ALL) ODD_SUM_GT1 ))
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o (SPEC ``(j:num) + k``)) GT1_DIV2_GT0 ))
          THEN  (FULL_SIMP_TAC (arith_ss) [ADDSUB_COMM])
        ]
      ,
              (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
        THEN  (ASSUME_TAC ( (UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``j:num``, ``k:num``])) arithmeticTheory.ODD_ADD ))
        THEN  (ASSUME_TAC ( (UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_POS ))
        THEN  (ASSUME_TAC ( (UNDISCH_ALL o GSYM o fst o EQ_IMP_RULE o UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_DIV2_EQ_PREC ))
        THEN  (FULL_SIMP_TAC (bool_ss) [GSYM arithmeticTheory.ODD_EVEN])
        THEN  (RW_TAC (arith_ss) [EVEN_ODD_MIX_DIV2_ADD, arithmeticTheory.MOD_2]) (* 4 subgoals from here *)
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
            THEN  (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV2_ADD, (GSYM arithmeticTheory.EXP2_LT)])
          ,
            (
                    (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
              THEN  (FULL_SIMP_TAC (bool_ss) [GSYM arithmeticTheory.EVEN_ODD])
            )
            THEN  (FULL_SIMP_TAC (arith_ss) [ODDS_DIV2_ADD, (GSYM arithmeticTheory.EXP2_LT)])
            THEN  (FULL_SIMP_TAC (arith_ss) [SUB2_DIV2_DIV2_SUB1, ODD_MOD2])
          ]
        ,
                (FULL_SIMP_TAC (srw_ss()) [EVEN_ODD_MIX_DIV2_ADD])
          THEN  (FULL_SIMP_TAC (bool_ss) [arithmeticTheory.EVEN_ODD])
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o fst o EQ_IMP_RULE o GSYM o (SPECL [``j:num``, ``k:num``])) arithmeticTheory.ODD_ADD ))
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_POS ))
          THEN  (ASSUME_TAC ( (UNDISCH_ALL o GSYM o fst o EQ_IMP_RULE o UNDISCH_ALL o (SPEC ``(j:num) + k``)) ODD_DIV2_EQ_PREC ))
          THEN  (FULL_SIMP_TAC (bool_ss) [])
          
          THEN  (Cases_on `EVEN j`)
          THEN  (FULL_SIMP_TAC (arith_ss) [(GSYM arithmeticTheory.EXP2_LT), arithmeticTheory.MOD_2])
        ]
    ]
);
(* ---- *)

val SUM_CONST_LT_2EXP = store_thm("SUM_CONST_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num) (c:num). (j < 2**n) ∧ (k < 2**n) ==> (c < 2 ==> ((j + k + c < 2**(SUC n))))``
  , (FULL_SIMP_TAC (arith_ss) [SUC_INC, arithmeticTheory.EXP_ADD])
);

val RIGHT_SHIFT_SUM_LT_2EXP = store_thm("RIGHT_SHIFT_SUM_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num). (j < 2**(SUC n)) ∧ (k < 2**(SUC n)) ==> ((j DIV 2 + k DIV 2 + 1 < 2**(SUC n)) ∧ (j DIV 2 + k DIV 2 < 2**(SUC n)))``
  ,       (RW_TAC (pure_ss) [])
    THENL [
            (ASSUME_TAC (SPECL [``n:num``, ``j DIV 2``, ``k DIV 2``, ``1:num``] SUM_CONST_LT_2EXP))
      THEN  (RW_TAC (srw_ss()) [(fst o EQ_IMP_RULE o SPEC_ALL) (GSYM arithmeticTheory.EXP2_LT)])
    ,       (ASSUME_TAC (SPECL [``n:num``, ``j DIV 2``, ``k DIV 2``, ``0:num``] SUM_CONST_LT_2EXP))
      THEN  (FULL_SIMP_TAC (arith_ss) [(fst o EQ_IMP_RULE o SPEC_ALL) (GSYM arithmeticTheory.EXP2_LT)])
    ]
);

val DIV_PRODMOD_LT_2EXP = store_thm("DIV_PRODMOD_LT_2EXP"
  , ``∀ (n:num) (j:num) (k:num). (j < 2**(SUC n)) ∧ (k < 2**(SUC n)) ==> (j DIV 2 + k DIV 2 + (j MOD 2) * (k MOD 2) < 2**(SUC n))``
  ,       (REPEAT STRIP_TAC)
    THEN  (ASSUME_TAC (SPEC_ALL MULT_MOD2_01))
    THEN  (RW_TAC (pure_ss) [])
    THEN  (
            (RW_TAC (arith_ss) [])
      THEN  (RW_TAC (pure_ss) [arithmeticTheory.ADD_ASSOC])
      THEN  (FULL_SIMP_TAC (arith_ss) [RIGHT_SHIFT_SUM_LT_2EXP])
    )
);

val MOD_2EXP_EQ = store_thm("MOD_2EXP_EQ"
  , ``∀ (n :num) (j :num). j MOD 2**(SUC n) = 2 * ((j DIV 2) MOD 2**n) + j MOD 2``
  ,       (FULL_SIMP_TAC (arith_ss) [SUC_INC, arithmeticTheory.EXP_ADD, arithmeticTheory.DIV_MOD_MOD_DIV])
    THEN  (REWRITE_TAC [Once ((SIMP_RULE arith_ss [] o SPECL [``2:num``, ``j MOD ((2 :num) * (2 :num) ** n)``] o (SIMP_RULE (pure_ss) [arithmeticTheory.MULT_COMM]) o GEN_ALL o DISCH_ALL o CONJUNCT1 o SPEC_ALL o UNDISCH_ALL o SPEC_ALL) arithmeticTheory.DIVISION)])
    THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.MOD_MULT_MOD])
);

val ADD_DIV2_DIV2_ADD_MULT_MOD2 = store_thm("ADD_DIV2_DIV2_ADD_MULT_MOD2"
  , ``∀ (j:num) (k:num). (j + k) DIV 2 = j DIV 2 + k DIV 2 + j MOD 2 * k MOD 2``
  ,       (REPEAT STRIP_TAC)
    THEN  (Cases_on `EVEN j`)
    THENL [
              (Cases_on `EVEN k`)
        THEN  (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV2_ADD, ODDS_DIV2_ADD, EVEN_ODD_MIX_DIV2_ADD, EVEN_ODD_MIX_DIV2, arithmeticTheory.EVEN_MOD2])
      ,       (Cases_on `EVEN k`)
        THENL [
            (FULL_SIMP_TAC (srw_ss()) [EVENS_DIV2_ADD, ODDS_DIV2_ADD, EVEN_ODD_MIX_DIV2_ADD, EVEN_ODD_MIX_DIV2, arithmeticTheory.EVEN_MOD2])
          ,       (`0 < j` by FULL_SIMP_TAC (arith_ss) [ODD_POS, arithmeticTheory.EVEN_ODD])
            THEN  (`0 < k` by FULL_SIMP_TAC (arith_ss) [ODD_POS, arithmeticTheory.EVEN_ODD])
            THEN  (`1 ≤ (j + k) DIV 2` by FULL_SIMP_TAC (arith_ss) [ODD_POS, ODD_POS, GT1_DIV2_GE1])
            THEN  (FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.EVEN_ODD, ODDS_DIV2_ADD_ALT, ODD_MOD2, (SPECL [``(j + k) DIV 2``, ``1:num``] o GSYM) ADDSUB_COMM])
        ]
    ]
);

val ADD_MOD2_XOR = store_thm("ADD_MOD2_XOR"
  , ``∀ (j:num) (k:num). (j + k) MOD 2 = if (j MOD 2) = (k MOD 2) then 0 else 1``
  ,       (REPEAT STRIP_TAC)
    THEN  (Cases_on `EVEN j`)
    THEN  (
            (Cases_on `EVEN k`)
      THEN  (FULL_SIMP_TAC (arith_ss) [arithmeticTheory.EVEN_MOD2, ODD_MOD2, GSYM arithmeticTheory.ODD_EVEN, Once (GSYM arithmeticTheory.MOD_PLUS)])
    )
);

val PLUS_MOD_2EXP_EQ = store_thm("PLUS_MOD_2EXP_EQ"
  , ``∀ (n :num) (j :num) (k :num). (j + k) MOD 2**(SUC n) = 2 * ((j DIV 2 + k DIV 2 + (j MOD 2)*(k MOD 2)) MOD 2**n) + (j MOD 2 + k MOD 2) MOD 2``
  , (FULL_SIMP_TAC (arith_ss) [MOD_2EXP_EQ, ADD_DIV2_DIV2_ADD_MULT_MOD2, ADD_MOD2_XOR])
);

val MULT_DIV_LE = store_thm("MULT_DIV_LE"
  , ``∀ (n:num) (j:num). (0 < n) ==> (n * (j DIV n) <= j)``
  , (REPEAT STRIP_TAC) THEN (ASSUME_TAC ((SPEC ``j:num`` o UNDISCH_ALL o SPECX) arithmeticTheory.DIVISION)) THEN (RW_TAC (arith_ss) [])
);

(* ------------------------------------------------------------------------- *)
val _ = export_theory();
 
