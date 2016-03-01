(* You should open emacs from ../arm8bil *)

open arm8bilTheory;

open stateTheory;
open arm8bilLib;


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

