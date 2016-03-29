structure arm8stepbilLib :> arm8stepbilLib =
struct

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
open arm8bilLib;

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*  Exceptions                                                               *)
(* ------------------------------------------------------------------------- *)
exception UnsupportedARM8StateField of string;

(* WARNING THIS IS A COPU OF arm8bilLib *)
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
  ``, ``^(a8s).MEM
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

(* ------------------------------------------------------------------------- *)
(*  Some list operations                                                     *)
(* ------------------------------------------------------------------------- *)
fun list_intersect l1 l2 = List.filter (fn e => List.exists (fn x => x = e) l2) l1;
fun list_union l1 l2 = List.concat [l1, l2];
fun list_diff l1 l2 = List.filter (fn e => not (List.exists (fn x => x = e) l2)) l1;
fun list_exclusion l1 l2 = list_diff (list_union l1 l2) (list_intersect l1 l2);
fun list_exclusion_id l1 l2 = (list_diff l1 l2, list_diff l2 l1);
fun list_split lst =
  let
    fun ls lst l1 l2 = case lst of
        []        => (List.rev l1, List.rev l2)
      | (a, b)::l => ls l (a::l1) (b::l2);
  in
    ls lst [] []
  end
;
fun list_uniq lst =
  let
    fun lu lst res = case lst of
        []    =>  res
      | e::l  =>  lu l (if List.exists (fn x => x = e) res then res else e::res)
  in
    lu lst []
  end
;

(* ------------------------------------------------------------------------- *)
(*  Field update extraction of ARMv8 states                                  *)
(* ------------------------------------------------------------------------- *)
val extract_updates = fn upd =>
  let
    fun ex upd lst = if (combinSyntax.is_update_comb upd)
      then
        let
          val index = (snd o dest_comb o fst o dest_comb o fst o dest_comb) upd;
          val expr  = (snd o dest_comb o fst o dest_comb) upd;
        in
          ex ((snd o dest_comb) upd) ((stringSyntax.fromHOLstring (eval ``r2s ^index``), expr)::lst)
        end
      else  lst
  in
    ex upd []
  end
;

fun extract_updates_fg upd findex gexpr =
  let
    fun ex upd findex gexpr lst = if (combinSyntax.is_update_comb upd)
      then
        let
          val index = (snd o dest_comb o fst o dest_comb o fst o dest_comb) upd;
          val expr  = (snd o dest_comb o fst o dest_comb) upd;
        in
          ex ((snd o dest_comb) upd) findex gexpr ((findex index, gexpr expr)::lst)
        end
      else  lst
  in
    ex upd findex gexpr []
  end
;
fun extract_updates upd = extract_updates_fg upd (fn x => x) (fn x => x);

fun extract_arm8_changes a8s =
  let
    fun exreg regupd = extract_updates_fg regupd (fn i => (stringSyntax.fromHOLstring (eval ``r2s ^i``))) (fn x => x);
    fun ex a8s lst = if (is_comb a8s)
      then
        let
          val update = (opname o fst o dest_comb) a8s;
          val entry = (snd o dest_comb o snd o dest_comb o fst o dest_comb) a8s handle _ => a8s;
        in
          if (entry = a8s) then lst
          else
                if  (update = "arm8_state_PSTATE_fupd") then ex ((snd o dest_comb) a8s) (List.concat [(ex entry []), lst])
          else  if  (update = "arm8_state_REG_fupd") then ex ((snd o dest_comb) a8s) (List.concat [(exreg entry), lst])
          else ex ((snd o dest_comb) a8s) ((String.substring (update, 0, String.size update - String.size "_fupd"), entry)::lst)
        end
      else  lst;
  in
    ex a8s []
  end
;

fun extract_arm8_changes_cases (a8s1, a8s2) cond =
  let
    fun exreg regupd = extract_updates_fg regupd (fn i => (stringSyntax.fromHOLstring (eval ``r2s ^i``))) (fn x => x);
    fun exregs entries =
      let
        val er1 = exreg (fst entries);
        val er2 = exreg (snd entries);
        fun aux lst1 lst2 res = case (er1, er2) of
            ((s, e1)::l1, (_, e2)::l2) => aux l1 l2 ((s, ``if ^cond then ^e1 else ^e2``)::res)
          | _ => res;
      in
        aux er1 er2 []
      end;
    fun ex (a8s1, a8s2) lst = if (is_comb a8s1) andalso (is_comb a8s2)
      then
        let
          val updates = ((opname o fst o dest_comb) a8s1, (opname o fst o dest_comb) a8s2);
          val entries = (
              (snd o dest_comb o snd o dest_comb o fst o dest_comb) a8s1 handle _ => a8s1
            , (snd o dest_comb o snd o dest_comb o fst o dest_comb) a8s2 handle _ => a8s2
          );
        in
          if (fst entries = a8s1) orelse (snd entries = a8s2) then lst
          else  if  (fst updates = "arm8_state_PSTATE_fupd") andalso (fst updates = snd updates) 
            then ex ((snd o dest_comb) a8s1, (snd o dest_comb) a8s2)  (List.concat [(ex (fst entries, snd entries) []), lst])
          else  if  (fst updates = "arm8_state_REG_fupd") andalso (fst updates = snd updates)
            then ex ((snd o dest_comb) a8s1, (snd o dest_comb) a8s2)  (List.concat [(exregs entries), lst])
          else  if (fst updates = snd updates)
            then ex
              ((snd o dest_comb) a8s1, (snd o dest_comb) a8s2)
              ((String.substring (fst updates, 0, String.size (fst updates) - String.size "_fupd"), ``if ^cond then ^(fst entries) else ^(snd entries)``)::lst)
          else lst
        end
      else  lst;
  in
    ex (a8s1, a8s2) []
  end
;

fun get_a8s_from_upd a8supd = if (is_comb a8supd)
  then  get_a8s_from_upd ((snd o dest_comb) a8supd)
  else  a8supd
;

(* [[TODO: handle more general cases]] *)
fun rewrite_a8s_branch_upd (a8s1, a8s2) cond =
  let
    val changes = extract_arm8_changes_cases (a8s1, a8s2) cond;
    val a8s = get_a8s_from_upd a8s1;
    fun updfield (str, upd) =
            if  (str = "arm8_state_PC")           then  (fst o dest_comb) ``s with <| PC           := ^upd |>``
      else  if  (str = "arm8_state_branch_hint")  then  (fst o dest_comb) ``s with <| branch_hint  := ^upd |>`` (* still unsupported *)
      else  raise UnsupportedARM8StateField str;
  in
    List.foldl (fn (a,b) => ``^a (^b)``) a8s (List.map updfield changes)
  end
;

(* ------------------------------------------------------------------------- *)
(*  Transcompile instructions to BIL programs                                *)
(* ------------------------------------------------------------------------- *)
fun arm8_supported_fields a8s = (
  List.concat [
      arm8_supported_den a8s
    , List.tabulate(32, fn t => ``^a8s.REG ^(wordsSyntax.mk_wordii (t, 5))``)
  ]
);

val arm8_supported_fields_HOLstr = List.map (fn x => bil_a8e2HOLstring x) (arm8_supported_fields ``a8s:arm8_state``);
val arm8_supported_fields_str = List.map (fn x => (stringSyntax.fromHOLstring o eval o bil_a8e2HOLstring) x) (arm8_supported_fields ``a8s:arm8_state``);

fun bil_copy_a8s_state_stmts_prefix a8s prefix =
  let
    val gen_assign_tmp = 
      List.map (fn t => 
              let
                val be  = bil_expr_const t;
                val str = bil_a8e2HOLstring_prefix t prefix;
              in
                ``Assign ^str ^be``
              end
          ) (arm8_supported_fields a8s);
    val assign_tmp = eval (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` gen_assign_tmp);
  in
    assign_tmp
  end
;

fun bil_full_backup_arm8_vars_tmp bs =
  let
    val a8s = ``a8s:arm8_state``;
    val gen_assign_tmp = 
      List.map (fn t => 
              let
                val strsrc = bil_a8e2HOLstring_prefix t "";
                val strdst = bil_a8e2HOLstring_prefix t "tmp_";
              in
                ``Assign ^strdst (Den ^strsrc)``
              end
          ) (arm8_supported_fields a8s);
    val assign_tmp = eval (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` gen_assign_tmp);
  in
    assign_tmp
  end
;

fun bil_backup_arm8_vars_tmp bs bklst =
  let
    val a8s = ``s:arm8_state``;
    val removeme = ``rmme:bool``;
    val gen_assign_tmp = 
      List.map (fn t => 
              let
                val strsrc = eval (bil_a8e2HOLstring_prefix t "");
                val strdst = eval (bil_a8e2HOLstring_prefix t "tmp_");
              in
                if (t <> ``s.MEM``) andalso
		   (List.exists (fn x => x = stringSyntax.fromHOLstring strsrc) bklst)
                  then  (``Assign ^strdst (Den ^strsrc)``, SIMP_RULE (srw_ss()) [r2s_def] (#3(tc_exp_arm8 t)))
                  else  (removeme, ASSUME ``T``)
              end
          ) (arm8_supported_fields a8s);
    val gen_assign_tmp_ch = (List.filter (fn (x,y) => not (x = removeme)) gen_assign_tmp);
  in
    ListPair.unzip gen_assign_tmp_ch
  end
;

fun arm8_thms_hypdiff th1 th2 =
  let
    val excl = list_exclusion_id (hyp th1) (hyp th2);
    fun clist lst1 lst2 res = case (lst1, lst2) of
        (c1::l1, c2::l2)  =>  clist l1 l2 ((c1, c2)::res)
      | (_, _)            =>  res;
  in
    if (List.length (fst excl) = List.length (snd excl))
      then clist (fst excl) (snd excl) []
      else []
  end
;

fun contr_pairs_conj1 hd =
  let
    fun hdc hd tms = case hd of
        []          =>  tms
      | (t1, t2)::l =>
          if (eval ``^t1 = ~(^t2)``) = ``T``
            then hdc l (t1::tms)
            else [];
            (* [[]] an exception is better *)
  in
    eval (List.foldr (fn (a, b) => ``^a ∧ ^b``) ``T`` (hdc hd []))
  end
;

fun arm8_branch_thm_join thl = case thl of
    th1::th2::[] =>
      let
        val conds = arm8_thms_hypdiff th1 th2;
        val hyps = list_intersect (hyp th1) (hyp th2);
        val c1 = (optionSyntax.dest_some o snd o dest_comb o concl) th1;
        val c2 = (optionSyntax.dest_some o snd o dest_comb o concl) th2;
        val a8s' = rewrite_a8s_branch_upd (c1, c2) (contr_pairs_conj1 conds);
        val conc = ``(NextStateARM8 s = SOME (^a8s'))``;
        val th = List.foldl (fn (a, b) => ``^a ==> (^b)``) conc hyps;
        val tac = (RW_TAC (pure_ss) []) THENL [FULL_SIMP_TAC (srw_ss()) [th1], FULL_SIMP_TAC (srw_ss()) [th2]];
      in
        [UNDISCH_ALL (tryprove(th, tac))]
      end
  | _ => thl
;

fun supported_accesses a8sch =
  let
    val supp_pairs = List.map (fn x => (x, opname x)) (arm8_supported_den ``s:arm8_state``);
    val (writes, aes) = list_split a8sch;
    fun extract_reads ae res = 
            if (is_reg ae)      then  (stringSyntax.fromHOLstring (eval ``r2s ^((snd o dest_comb) ae)``))::res
      else  if (is_arm8_den ae) then  (opname ae)::res
      else  if (is_comb ae)     then  List.concat (List.map (fn x => extract_reads x []) ((snd o strip_comb) ae))
      else  res;
    val reads  =  List.concat (List.map (fn x => extract_reads x []) aes);
  in
    list_uniq (list_union writes reads)
  end
;

fun tc_stmt_arm8_hex instr =
  let
    val arm8thl = arm8_branch_thm_join (arm8_step_hex instr);
  in
    case arm8thl of
        th::[] =>
          let
            (* Normalize theorem to rewrite constants for immediate values *)
            (* Transform hypotesys like Some(constant1,constant2) = Some(v1, v2 )*)
            (* in (constant1=v1), (constant2=v2) *)
            val ass_some = (List.filter (fn tm =>
                (is_eq tm) andalso ((optionLib.is_some o snd o dest_eq) tm) andalso ((optionLib.is_some o snd o dest_eq) tm)
                ) (hyp th));
            val ass_some = List.map (SIMP_CONV (srw_ss()) []) ass_some;
            val t1 = List.foldl (fn (thm, main_thm) => (DISCH ((fst o dest_eq o concl) thm) main_thm)) th ass_some;
            val t2 = REWRITE_RULE ass_some t1;
            val t3 = IMP_CANON t2;
            val t4 = UNDISCH_ALL (List.nth 0 t3);
            val t5 = SIMP_RULE (bool_ss) [] t4;
            (* Apply constants to the conclusion *)
            val ass_const = (List.filter (fn tm =>
                (is_eq tm) andalso ((wordsSyntax.is_n2w o fst o dest_eq) tm)
                ) (hyp t5));
            val ass_const = List.map (SYM o ASSUME) ass_const;
            val th = REWRITE_RULE ass_const t5;
            (* End of normalization for immediate values *)
            (* Filter only supported changes *)
            val a8sch = List.filter (fn (s, v) => List.exists (fn x => x = s) arm8_supported_fields_str) ((extract_arm8_changes o optionSyntax.dest_some o snd o dest_comb o concl) th);
            val certify_assignments = List.map (fn (s, a8e) =>
                let
                  val (bexp, _, thm)  = tc_exp_arm8_prefix a8e "tmp_";
                  val str = stringSyntax.fromMLstring (s);
                in
                  (``Assign ^str ^bexp``, (SIMP_RULE (srw_ss()) [r2s_def] thm))
                end
              ) a8sch;
            val (assign, certs) = list_split certify_assignments;
	    val (tmp_assign, tmp_certs) = bil_backup_arm8_vars_tmp ``bs:stepstate`` (supported_accesses a8sch);
            val stmts = eval (List.foldl (fn (a,b) => ``^b ++ [^a]``) ``[]:bil_stmt_t list`` (List.concat [tmp_assign, assign]));
          in
            (eval stmts, List.concat [tmp_certs, certs], arm8thl)
          end
      | _    => (``[]``, [], [])
  end
;


(* after this we do not have certification of step *)


fun tc_stmt_arm8_hexlist instrlst =
  let
    fun tci ilist idx res = 
      case ilist of
          []    =>  res
        | i::l  =>
            let
              val (stmts, certs, arm8thl) = tc_stmt_arm8_hex i;
              val changes = (extract_arm8_changes o optionSyntax.dest_some o snd o dest_comb o concl) (List.hd arm8thl);
              val branch_hint = (snd o List.hd o List.filter (fn (s, e) => s = "arm8_state_branch_hint")) changes;
              val is_branch_conditional = boolSyntax.is_cond branch_hint;
              val is_branch = is_branch_conditional orelse optionSyntax.is_some branch_hint;
              val (assigns_n_jmp, jmp_certs) = if (is_branch_conditional) then
                  let
                    val cond = (snd o List.hd o List.filter (fn (s, e) => s = "arm8_state_PC")) changes;
                    val (c, t, e) = dest_cond cond;
                    val (bc, _, cert) = tc_exp_arm8 c;
                    val (next_t, next_e) = (eval ``^idx + ^((snd o dest_comb) t)``, eval ``^idx + ^((snd o dest_comb) e)``);
                  in
                    (``^stmts ++ [CJmp ^bc (Address (Reg64 ^next_t)) (Address (Reg64 ^next_e))]``, [cert])
                  end
                else if (is_branch) then
                  let
                    val ae = (snd o List.hd o List.filter (fn (s, e) => s = "arm8_state_PC")) changes;
                    val next_ae = eval ``^idx + ^((snd o dest_comb) ae)``;
                  in
                    (``^stmts ++ [Jmp (Address (Reg64 ^next_ae))]``, [])
                  end
                else  (``^stmts``, []);
            in
              tci l (eval ``^idx + 4w``) ((``<| label := Address (Reg64 ^idx); statements := ^assigns_n_jmp |>``, List.concat [certs, jmp_certs])::res)
            end;
  in
    List.rev (tci instrlst ``0w:bool[64]`` [])
  end
;

(* ------------------------------------------------------------------------- *)
(*  Transcompile instructions to BIL program                                 *)
(* ------------------------------------------------------------------------- *)
val arm8_state_zero = ``<|
    PC          := (0w:bool[64])
  ; REG         := λ(x:bool[5]).(0w:bool[64])
  ; MEM         := λ(x:bool[64]).(0w:bool[8])
  ; PSTATE      := <|N := F; Z := F; C := F; V := F; SPS := F; EL := (0w :word2)|>
  ; SCTLR_EL1   := <|
        A := F; E0E := F; EE := F; SA := F; SA0 := F
      ; sctlrtype'rst := (0w:bool[27])
    |>
  ; SCTLR_EL2   := <|
        A := F; E0E := F; EE := F; SA := F; SA0 := F
      ; sctlrtype'rst := (0w:bool[27])
    |>
  ; SCTLR_EL3   := <|
        A := F; E0E := F; EE := F; SA := F; SA0 := F
      ; sctlrtype'rst := (0w:bool[27])
    |>
  ; SP_EL0 := (0w:bool[64]); SP_EL1 := (0w:bool[64])
  ; SP_EL2 := (0w:bool[64]); SP_EL3 := (0w:bool[64])
  ; TCR_EL1     := <|TBI0 := F; TBI1 := F; tcr_el1'rst := (0w :62 word)|>
  ; TCR_EL2     := <|TBI := F; tcr_el2_el3'rst := (0w :31 word)|>
  ; TCR_EL3     := <|TBI := F; tcr_el2_el3'rst := (0w :31 word)|>
  ; branch_hint := NONE
  ; exception   := NoException
|>``;

fun init_arm8_hex instr = 
  let
    val instrHOL = stringSyntax.fromMLstring instr;
    val pc0 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 8, 2))``;
    val pc1 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 6, 2))``;
    val pc2 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 4, 2))``;
    val pc3 = eval ``s2n 16 UNHEX (SUBSTRING (^instrHOL, 2, 2))``;
  in
    eval ``^arm8_state_zero with <| MEM := (0w =+ n2w ^pc0) ((1w =+ n2w ^pc1) ((2w =+ n2w ^pc2) ((3w =+ n2w ^pc3) ^arm8_state_zero.MEM))) |>``
  end
;

val bil_init_declaration_stmts_a8s = fn prefix =>
  let
    val a8s     = arm8_state_zero;
    val bs      = ``bs:stepstate``;
    val gen_decls = 
      List.map (fn t => 
              let
                val bv  = bil_value t;
                val str = bil_a8e2HOLstring_prefix t prefix;
                val bvt = eval ``bil_type_val_int_inf ^bv``;
              in
                ``Declare (Var ^str ^bvt)``
              end
          ) (arm8_supported_fields a8s);
    val decls = eval (List.foldl (fn (a,b) => ``[^a] ++ ^b``) ``[]:bil_stmt_t list`` gen_decls);
  in
    decls
  end
;


(* Generate a BIL State equivalent to an ARMv8 State *)
fun a8s2bs_var_prefix a8s bs prefix =
  let
    fun triple_stv x prefix =
      let
        val v = (eval o bil_value) x;
      in
        ((eval o C bil_a8e2HOLstring_prefix prefix) x, eval ``bil_type_val_int_inf ^v``, v)
      end;
    val env_strings = List.map (fn x => triple_stv x prefix) (List.concat [
        arm8_supported_den a8s
      , List.tabulate(32, fn t => ``^a8s.REG ^(wordsSyntax.mk_wordii (t, 5))``)
    ]);
    val den_updates = List.map (fn (s, t, v) => ``(^s =+ (^t, ^v))``) env_strings;
    
    val mem_updates_list = fn a8s =>
      let
        val mem_upd = fn a8s => List.filter (fn (s, v) => s = bil_a8e2string ``s.MEM``) (extract_arm8_changes a8s);
      in
        ((extract_updates o snd) (List.nth (mem_upd a8s, 0))) handle Subscript => []
      end;
    
    val mem_updates =
      let
        fun mups updlp lst = case updlp of
            []        =>  lst
          | (f, v)::l =>  mups l ((``(Reg64 ^f =+ Reg8 ^v)``)::lst);
        val updl = (mups (mem_updates_list a8s) []);
      in
        List.foldr (fn (a, b) => ``^a (^b)``) ``λ(x:bil_int_t).(Reg8 0w)`` updl
      end;
      
    val mstr = bil_a8e2HOLstring_prefix ``^a8s.MEM`` ""; (* don't change memory name *)
    val mem_update = ``^mstr =+ (MemByte Bit64, Mem Bit64 ^mem_updates)``;
    
    val env = List.foldr (fn (a, b) => ``^a (^b)``) (eval ``^bs.environ``) (mem_update::den_updates);
  in
    ``^bs with <| environ  := ^env |>``
  end
;
fun a8s2bs a8s bs = a8s2bs_var_prefix a8s bs "";

fun a8s2bs_step_program instrl a8s =
  let
    val decl = bil_init_declaration_stmts_a8s "";
    val decl_tmp = bil_init_declaration_stmts_a8s "tmp_";
    val decls = eval ``^decl ++ ^decl_tmp``;
    val (blocks, certs) = list_split (tc_stmt_arm8_hexlist instrl);
    val prog = List.foldr (fn (a, b) => ``^a::^b``) ``[]:program`` blocks;
    val copy_block = bil_copy_a8s_state_stmts_prefix a8s "";
    val last_label = eval ``^(List.nth (blocks, (List.length blocks) - 1)).label``;
    val halt_label = eval ``Address (bil_read_address_label ^last_label + 4x)``;
  in
    (``(  (<| label := Label "Init declaration"; statements := ^decls |>)
        ::(<| label := Label "ARM8 state first copy"; statements := ^copy_block |>)
        ::^prog
       ) ++ [<| label := ^halt_label; statements := [ Halt (Const 0b) ] |>]``, List.concat certs)
  end
;


(* ------------------------------------------------------------------------- *)
(*  ARMv8 State - BIL State Bbbisimulation                                     *)
(* ------------------------------------------------------------------------- *)
end
