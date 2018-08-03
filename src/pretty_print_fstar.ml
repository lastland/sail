open Type_check
open Ast
open Ast_util
open State
open Format
open List
open PPrint
open Pretty_print_common

let arrow = string "->"

let opt_env_of_annot (l, tannot) = match destruct_tannot tannot with
  | Some (env, _, _) -> Some env
  | None -> None

let rec modify_var_string_fstar (x:string) : string =
  let hd = String.get x 0 in
  match hd with
  | '\'' -> modify_var_string_fstar (String.sub x 1 (String.length x - 1))
  | '_' -> "sail" ^ x (* or maybe [bultin_*]? *)
  | _ -> String.uncapitalize_ascii x

let get_id_string id =
  match id with
  | Id_aux ((Id x), _) -> x
  | _ -> "" (* TODO: this case *)

let rec pp_regnames o regs n =
  match regs with
  | [] -> fprintf o "@\n"
  | r :: regs' ->
     fprintf o "@\n@[let r%s : reg_t = %u@]" (get_id_string r.regid) n;
     pp_regnames o regs' (n+1)

let rec pp_n_regtype_rec o regs n =
  match regs with
  | [] -> ()
  | r :: regs' ->
     fprintf o "@\n@[| %u -> %u (* %s *)@]" n r.regnum (get_id_string r.regid);
     pp_n_regtype_rec o regs' (n+1)

let pp_n_regtype o regs =
  fprintf o "@\n@[<hov 2>let n_regtype (n : reg_t) : pos =@ match n with";
  pp_n_regtype_rec o regs 0;
  fprintf o "@]@\n"

let rec pp_regval_rec o regs n =
  match regs with
  | [] -> ()
  | r :: regs' ->
     fprintf o "@\n@[| %u -> bv_t %u (* %s *)@]" n r.reglen (get_id_string r.regid);
     pp_regval_rec o regs' (n+1)

let pp_regval o regs =
  fprintf o "@\n@[<hov 2>let regval (n : reg_t) : Type0 =@ match n with";
  pp_regval_rec o regs 0;
  fprintf o "@]@\n"

let pp_regs_fstar (regs_file,regs_modules) regs =
  let o = formatter_of_out_channel regs_file in
  fprintf o "module Regs\n\nopen Types\n";
  fprintf o "@\n@[let@ n_reg_t@ :@ pos = %u@]@\n" (length regs);
  pp_regnames o regs 0;
  pp_n_regtype o regs;
  pp_regval o regs;
  pp_print_flush o ()

let doc_rec_fstar force_rec (Rec_aux(r,_)) = match r with
  | Rec_nonrec when not force_rec -> space
  | _ -> space ^^ string "rec" ^^ space

let doc_lit_fstar (L_aux(lit,l)) =
  match lit with
  | L_unit  -> utf8string "()"
  | L_zero  -> utf8string "0"
  | L_one   -> utf8string "1"
  | L_false -> utf8string "false"
  | L_true  -> utf8string "true"
  | L_num i -> utf8string (Big_int.to_string i)
  | L_hex n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_bin n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_undef ->
     utf8string "(return (failwith \"undefined value of unsupported type\"))"
  | L_string s -> utf8string ("\"" ^ s ^ "\"")
  | L_real s -> utf8string s

let doc_id_fstar_ctor = Pretty_print_sail.doc_id

let doc_id_fstar_type = Pretty_print_sail.doc_id

let doc_id_fstar id =
  let id' = match id with
  | Id_aux (Id x, l) ->
     Id_aux (Id (modify_var_string_fstar x), l)
  | _ -> id in
  Pretty_print_sail.doc_id id'

let doc_var_fstar (Kid_aux(Var x, l)) =
  doc_var (Kid_aux (Var (modify_var_string_fstar x), l))

let doc_nexp_fstar parens_needed n =
  let m = nexp_simp n in
  let rec doc_nexp parens_needed (Nexp_aux (n, _)) =
    match n with
    | Nexp_id id -> doc_id_fstar id
    | Nexp_var kid -> doc_var_fstar kid
    | Nexp_constant n -> string (Big_int.to_string n)
    | Nexp_app (id, ns) ->
       let tnexp = doc_id_fstar id ^^ space ^^
                     separate_map space (doc_nexp true) ns in
       if parens_needed then parens tnexp else tnexp
    | Nexp_times (n1, n2) ->
       let tnexp = separate space
                     [string "op_Multiply"; doc_nexp true n1; doc_nexp true n2] in
       if parens_needed then parens tnexp else tnexp
    | Nexp_sum (n1, n2) ->
       let tnexp = doc_op (string "+") (doc_nexp true n1) (doc_nexp true n2) in
       if parens_needed then parens tnexp else tnexp
    | Nexp_minus (n1, n2) ->
       let tnexp = doc_op (string "-") (doc_nexp true n1) (doc_nexp true n2) in
       if parens_needed then parens tnexp else tnexp
    | Nexp_exp n ->
       let tnexp = string "pow2 " ^^ doc_nexp true n in
       if parens_needed then parens tnexp else tnexp
    | Nexp_neg n ->
       let tnexp = string "-" ^^ doc_nexp true n in
       if parens_needed then parens tnexp else tnexp in
  doc_nexp parens_needed m

let rec doc_nc_fstar (NC_aux (nc, _)) = match nc with
  | NC_equal (n1, n2) ->
     doc_op equals (doc_nexp_fstar false n1) (doc_nexp_fstar false n2)
  | NC_bounded_ge (n1, n2) ->
     doc_op (string ">=") (doc_nexp_fstar false n1) (doc_nexp_fstar false n2)
  | NC_bounded_le (n1, n2) ->
     doc_op (string "<=") (doc_nexp_fstar false n1) (doc_nexp_fstar false n2)
  | NC_not_equal (n1, n2) ->
     doc_op (string "!=") (doc_nexp_fstar false n1) (doc_nexp_fstar false n2)
  | NC_or (n1, n2) ->
     doc_op (string "||") (doc_nc_fstar n1) (doc_nc_fstar n2)
  | NC_and (n1, n2) ->
     doc_op (string "&&") (doc_nc_fstar n1) (doc_nc_fstar n2)
  | NC_true -> string "True"
  | NC_false -> string "False"
  | NC_set (kid, l) -> string "FStar.Set.mem " ^^ doc_var_fstar kid ^^
                         parens (string "FStar.Set.as_set " ^^
                                   brackets (separate_map colon
                                               (fun i -> utf8string (Big_int.to_string i)) l))

let doc_constraints_fstar ncs = separate_map (string " && ") doc_nc_fstar ncs

let doc_typ_fstar, doc_typ_arg_fstar =
  let rec typ_p cons ty = doc_typ true cons ty
  and typ_n cons ty = doc_typ false cons ty
  and add_cons cons ty =
    if length cons > 0 then
      separate (break 1)
        [string "Pure"; parens ty;
         parens (string "requires " ^^
                   parens (doc_constraints_fstar cons));
         parens (string "ensures fun _ -> True")]
    else ty
  and doc_typ parens_needed cons (Typ_aux (typ, _) as t) =
    let add_cons ty =
      if length cons > 0 then
        separate (break 1)
          [string "Pure"; parens ty;
           parens (string "requires " ^^
                     parens (doc_constraints_fstar cons));
           parens (string "ensures fun _ -> True")]
      else ty in
    match typ with
    (* Tuples *)
    | Typ_tup (typs) ->
       let tpp = add_cons (separate (string " * ") (List.map (typ_n []) typs)) in
       if parens_needed then parens tpp else tpp
    (* Applications *)
    | Typ_app(Id_aux (Id "vector", _), [
            Typ_arg_aux (Typ_arg_nexp m, _);
            Typ_arg_aux (Typ_arg_order ord, _);
            Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
       let tpp =  match elem_typ with
         | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
            string "bv_t " ^^ doc_nexp_fstar true m
         | _ -> string "list " ^^ typ_p [] elem_typ in
       let tpp' = add_cons tpp in
       if parens_needed then parens tpp' else tpp'
    | Typ_app(Id_aux (Id "range", _), [
            Typ_arg_aux (Typ_arg_nexp n, _);
            Typ_arg_aux (Typ_arg_nexp m, _)]) ->
       add_cons (separate space [string "int_between";
                                 doc_nexp_fstar true n;
                                 doc_nexp_fstar true m])
    | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
       add_cons (string "int_exact " ^^ doc_nexp_fstar true n)
    | Typ_app(id, xs) ->
       let tpp = add_cons (doc_id_fstar id ^^ space ^^
                             separate_map space (doc_typ_arg true) xs) in
       if parens_needed then parens tpp else tpp
    (* Functions *)
    | Typ_fn (ty1, ty2, eff) ->
       let tpp2 = match eff with
         | Effect_aux (Effect_set (_::_), _) -> add_cons (string "st " ^^ typ_p [] ty2)
         | _ -> typ_n cons ty2 in
       let tpp = doc_op arrow (typ_p [] ty1) tpp2 in
       if parens_needed then parens tpp else tpp
    (* Ids *)
    | Typ_id (Id_aux (Id "bit", _)) -> add_cons (string "bool")
    | Typ_id id -> add_cons (doc_id_fstar id)
    (* Vars *)
    | Typ_var v -> add_cons (doc_var_fstar v)
    (* Others *)
    | _ -> let tpp = add_cons (Pretty_print_sail.doc_typ t) in
           if parens_needed then parens tpp else tpp
  and doc_typ_arg parens_needed (Typ_arg_aux (ta_aux, _)) =
    match ta_aux with
    | Typ_arg_typ typ -> doc_typ parens_needed [] typ
    | Typ_arg_nexp nexp -> doc_nexp_fstar parens_needed nexp
    | Typ_arg_order _ -> empty
  in typ_n, doc_typ_arg false

(* let effect_of (E_aux (exp, (l, annot)) as e) =
  match annot with
  | Some (env, typ, eff) -> effect_of_annot (mk_tannot env typ eff)
  | None -> no_effect *)

let rec doc_exp_fstar (E_aux (exp, (l, annot)) as e) =
  match exp with
  | E_case (exp, pexps) ->
     separate space [string "match"; doc_exp_fstar exp;
                     string "with" ^^ hardline ^^ doc_pexps_fstar pexps]
  | E_app (f, args) ->
     let call = match destruct_tannot annot with
       | Some (env, _, _) when Env.is_extern f env "fstar" ->
          string (Env.get_extern f env "fstar")
       | _ -> doc_id_fstar f in
     parens (hang 2 (flow (break 1) (call :: List.map doc_exp_fstar args)))
  | E_id id ->
     if has_effect (effect_of e) BE_rreg then
       string "read_reg" ^^ space ^^ string "r" ^^ string (get_id_string id)
     else doc_id_fstar id
  | E_vector exps -> brackets (separate_map (string ";") doc_exp_fstar exps)
  | E_if (cond, e1, e2) ->
     string "if " ^^ parens (doc_exp_fstar cond) ^^
       string " then" ^^ break 1 ^^ parens (doc_exp_fstar e1) ^^ break 1 ^^
         string "else " ^^ parens (doc_exp_fstar e2)
  | E_cast (typ, e) -> doc_exp_fstar e
  | E_assign (le, e) ->
     string "update_reg" ^^ space ^^ doc_lexp_fstar le ^^ space ^^ doc_exp_fstar e
  | E_let (LB_aux (LB_val (pat, e1), _), e2) ->
     prefix 2 1 (string "let" ^^ space ^^ doc_pat_fstar false false pat ^^
                   space ^^ equals ^^ break 1 ^^ doc_exp_fstar e1 ^^ string " in")
       (parens (doc_exp_fstar e2))
  | E_internal_return e ->
     let de = doc_exp_fstar e in
     begin match e with
     | E_aux (E_cast (Typ_aux (typ, _), e), _) ->
        begin match typ with
        | Typ_app(Id_aux (Id "vector", _), [
              Typ_arg_aux (Typ_arg_nexp m, _);
              Typ_arg_aux (Typ_arg_order ord, _);
              Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
           let asrt = string "assert_norm " ^^
                        parens (string "List.Tot.length " ^^
                                parens (doc_exp_fstar e) ^^ space ^^ equals ^^
                                space ^^ doc_nexp_fstar false m) ^^ semi in
           begin match elem_typ with
             | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
                string "return " ^^ parens (string "list2bv " ^^ parens de)
             | _ ->
                asrt ^^ hardline ^^ string "return " ^^ de
           end
        | _ -> string "return " ^^ de
        end
     | _ -> string "return " ^^ de
     end
  | E_internal_plet (pat, e1, e2) ->
     begin match fst (untyp_pat pat) with
     | P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _) ->
        doc_exp_fstar e1 ^^ semi ^^ hardline ^^ doc_exp_fstar e2
     | _ ->
        doc_op (string "<--") (doc_pat_fstar true true pat) (doc_exp_fstar e1) ^^
          semi ^^ hardline ^^ doc_exp_fstar e2
     end
  | _ -> Pretty_print_sail.doc_exp e
and doc_pexp_fstar (Pat_aux (pat_aux, _)) =
  match pat_aux with
  | Pat_exp (pat, exp) ->
     prefix 2 1 (string "| " ^^ doc_pat_fstar true false pat ^^ space ^^ arrow)
       (parens (doc_exp_fstar exp))
  | Pat_when (pat, wh, exp) ->
     separate space [string "|"; doc_pat_fstar true false pat;
                     string "if"; doc_exp_fstar wh;
                     string "then"; parens (doc_exp_fstar exp)]
and doc_pexps_fstar pexps = separate_map hardline doc_pexp_fstar pexps
and doc_pat_fstar apat_needed cast_omitted (P_aux (p,(l,annot)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) ->
    let ppp = doc_unop (doc_id_fstar_ctor id)
                (parens (separate_map comma (doc_pat_fstar true cast_omitted) pats)) in
    if apat_needed then parens ppp else ppp
  | P_app(id, []) -> doc_id_fstar_ctor id
  | P_lit lit  -> doc_lit_fstar lit
  | P_wild -> underscore
  | P_id id -> doc_id_fstar id
  | P_var(p,_) -> doc_pat_fstar true cast_omitted p
  | P_as(p,id) -> parens (separate space
                            [doc_pat_fstar true cast_omitted p; string "as"; doc_id_fstar id])
  | P_typ(typ,p) ->
     let doc_p = doc_pat_fstar true cast_omitted p in
     if cast_omitted then doc_p
     else parens (doc_op colon doc_p (doc_typ_fstar [] typ))
  | P_vector pats ->
     let ppp = brackets (separate_map semi (doc_pat_fstar true cast_omitted) pats) in
     if apat_needed then parens ppp else ppp
  | P_vector_concat pats ->
     raise (Reporting_basic.err_unreachable l
       "vector concatenation patterns should have been removed before pretty-printing")
  | P_tup pats  ->
     (match pats with
      | [p] -> doc_pat_fstar apat_needed cast_omitted p
      | _ -> parens (separate_map comma_sp (doc_pat_fstar false cast_omitted) pats))
  | P_list pats -> brackets (separate_map semi (doc_pat_fstar false cast_omitted) pats) (*Never seen but easy in lem*)
  | P_cons (p,p') -> doc_op (string "::") (doc_pat_fstar true cast_omitted p) (doc_pat_fstar true cast_omitted p')
  | P_record (_,_) -> empty (* TODO *)
and doc_lexp_fstar (LEXP_aux (le, a) as l) =
  match le with
  | LEXP_id id -> doc_id_fstar id
  | LEXP_deref e -> doc_exp_fstar e
  | _ -> Pretty_print_sail.doc_lexp l

let doc_base_kind_aux_fstar k =
  let s = match k with
  | BK_type -> "Type"
  | BK_int -> "int"
  | BK_order -> "bool" in
  string s

let doc_kind_fstar (K_aux (K_kind ((BK_aux (k, _))::_), _)) =
  doc_base_kind_aux_fstar k

let doc_quant_item env imp (QI_aux (qi, _)) = match qi with
  | QI_id (KOpt_aux (KOpt_none kid, annot)) ->
     begin match env with
     | Some e ->
        let doc_kid = if imp then string "#" ^^ doc_var_fstar kid
                      else doc_var_fstar kid in
        parens (doc_op colon doc_kid (string "int"))
     | None -> doc_var_fstar kid
     end
  | QI_id (KOpt_aux (KOpt_kind (kind, kid), _)) ->
     parens (doc_var_fstar kid ^^ string ":" ^^ doc_kind_fstar kind)
  | _ -> empty

let quant_and_constraints qs =
  let rec go qs (vars, cons) =
    match qs with
    | QI_aux (QI_id _, _) as qi :: qs' -> go qs' (qi :: vars, cons)
    | QI_aux (QI_const c, _) :: qs' -> go qs' (vars, c :: cons)
    | [] -> (vars, cons)
  in
  let vars, cons = go qs ([], []) in
  (rev vars, rev cons)

let doc_typquant_fstar  (TypQ_aux(tq,_)) typ env = match tq with
  | TypQ_tq ((_ :: _) as qs) ->
     let vars, cons = quant_and_constraints qs in
     let typ' = doc_typ_fstar cons typ in
     doc_op arrow (separate_map (space ^^ arrow ^^ space)
                     (doc_quant_item env true) vars) typ'
  | _ -> doc_typ_fstar [] typ

let doc_typquant_items_fstar (TypQ_aux(tq,_)) env = match tq with
  | TypQ_tq qs -> separate_map space (doc_quant_item env false) qs
  | _ -> empty

let doc_typschm_fstar quants (TypSchm_aux(TypSchm_ts(tq,t),_)) env =
(*  then
    let nexps_used = lem_nexps_of_typ t in
    let ptyc, nexps_sizes = doc_typclasses_lem t in
    let nexps_to_include = NexpSet.union nexps_used nexps_sizes in
    if NexpSet.is_empty nexps_to_include
    then pt
    else doc_typquant_fstar tq (Some nexps_to_include) (ptyc ^^ pt) *)
  if quants then doc_typquant_fstar tq t env else (doc_typ_fstar [] t)

let doc_typdef_fstar (TD_aux(td, annot)) =
  match td with
  | TD_abbrev(id,nm,(TypSchm_aux (TypSchm_ts (typq, _), _) as typschm)) ->
     let env = opt_env_of_annot annot in
     doc_op equals
       (separate space [string "type";
                        doc_id_fstar_type id;
                        doc_typquant_items_fstar typq env])
       (doc_typschm_fstar false typschm env)
  (* TODO: finish this *)
  | _ -> empty

let doc_fun_body_fstar exp = doc_exp_fstar exp

let doc_funcl_fstar (FCL_aux(FCL_Funcl(id, pexp), annot)) =
  let typ = typ_of_annot annot in
  let pat,guard,exp,(l,_) = destruct_pexp pexp in
  let _ = match guard with
    | None -> ()
    | _ ->
       raise (Reporting_basic.err_unreachable l
                "guarded pattern expression should have been rewritten before pretty-printing") in
  group (prefix 3 1
    (separate space [doc_id_fstar id; doc_pat_fstar true false pat; equals])
    (doc_fun_body_fstar exp))

let doc_fundef_rhs_fstar (FD_aux(FD_function(r, typa, efa, funcls),fannot) as fd) =
  separate_map (hardline ^^ string "and ") doc_funcl_fstar funcls

let doc_fundef_fstar (FD_aux(FD_function(r, typa, efa, fcls),fannot) as fd) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | FCL_aux (FCL_Funcl(id,_),annot) :: _
    when not (Env.is_extern id (env_of_annot annot) "fstar") ->
     string "let" ^^ (doc_rec_fstar (List.length fcls > 1) r) ^^
       (doc_fundef_rhs_fstar fd)
  | _ -> empty

let doc_docstring_fstar (l, _) = match l with
  | Parse_ast.Documented (str, _) -> string ("(*" ^ str ^ "*)") ^^ hardline
  | _ -> empty

let doc_spec_fstar (VS_aux (valspec,annot)) =
  match valspec with
  | VS_val_spec (typschm,id,ext,_) when ext "fstar" = None ->
     (* let (TypSchm_aux (TypSchm_ts (tq, typ), _)) = typschm in
     if contains_t_pp_var typ then empty else *)
     doc_docstring_fstar annot ^^
       separate space [string "val"; doc_id_fstar id; string ":";
         doc_typschm_fstar true typschm (opt_env_of_annot annot)] ^/^ hardline
  (* | VS_val_spec (_,_,Some _,_) -> empty *)
  | _ -> empty

let doc_def_fstar def =
  match def with
  | DEF_spec v_spec -> doc_spec_fstar v_spec
  | DEF_type t_def -> group (doc_typdef_fstar t_def) ^/^ hardline
  | DEF_fundef fdef -> group (doc_fundef_fstar fdef) ^/^ hardline
  | _ -> empty

let pp_defs_fstar (regs_file, (defs_file, defs_module), base_imports)
      regs (Defs defs) top_line =
  pp_regs_fstar (regs_file, defs_module) regs;
  let is_typ_def = function
    | DEF_type _ -> true
    | _ -> false
  in
  let typdefs, defs = List.partition is_typ_def defs in
  (print defs_file)
    (concat
       [(string "module ") ^^ (string defs_module); hardline; hardline;
        separate hardline (List.map (fun s -> string "open " ^^ string s) base_imports);
        hardline; hardline;
        separate empty (List.map doc_def_fstar typdefs); hardline; hardline;
        separate empty (List.map doc_def_fstar defs)])
