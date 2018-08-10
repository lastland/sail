open Type_check
open Ast
open Ast_util
open State
open Format
open List
open PPrint
open Pretty_print_common

let arrow = string "->"

let is_ctor id env =
  Env.is_union_constructor id env || Env.is_enum id env

let opt_env_of_annot (l, tannot) = match destruct_tannot tannot with
  | Some (env, _, _) -> Some env
  | None -> None

let rec modify_var_string_fstar (x:string) : string =
  let hd = String.get x 0 in
  match hd with
  | '\'' -> modify_var_string_fstar (String.sub x 1 (String.length x - 1))
  | '_' -> "sail" ^ x (* or maybe [bultin_*]? *)
  | _ -> Str.global_replace (Str.regexp "#") "__" (String.uncapitalize_ascii x)

let rec translate_operator_rec (x:string) : string list =
  if String.length x >= 1 then
    let hd = String.get x 0 in
    let tl = String.sub x 1 (String.length x - 1) in
    match hd with
    | '<' -> "lt" :: translate_operator_rec tl
    | '>' -> "gt" :: translate_operator_rec tl
    | '=' -> "eq" :: translate_operator_rec tl
    | '_' -> "us" :: translate_operator_rec tl
    | '+' -> "plus" :: translate_operator_rec tl
    | '-' -> "minus" :: translate_operator_rec tl
    | _ -> String.make 1 hd :: translate_operator_rec tl
  else []

let translate_operator (x:string) =
  "op__" ^ String.concat "_" (translate_operator_rec x)

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
  | L_zero  -> utf8string "false"
  | L_one   -> utf8string "true"
  | L_false -> utf8string "false"
  | L_true  -> utf8string "true"
  | L_num i -> utf8string (Big_int.to_string i)
  | L_hex n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_bin n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_undef ->
     utf8string "(return (failwith \"undefined value of unsupported type\"))"
  | L_string s -> utf8string ("\"" ^ s ^ "\"")
  | L_real s -> utf8string s

let doc_reg_fstar id =
  string "r" ^^ string (get_id_string id)

let doc_id_fstar (Id_aux (id, _)) =
  match id with
  | Id x -> string (modify_var_string_fstar x)
  | DeIid x -> string (translate_operator x)

let doc_id_or_reg_fstar id env =
  if Env.is_register id env then doc_reg_fstar id else doc_id_fstar id

let doc_id_fstar_ctor (Id_aux (id, _)) =
  match id with
  | Id x -> string (String.capitalize (modify_var_string_fstar x))
  | DeIid x -> string (String.capitalize (translate_operator x))

let doc_id_fstar_type = doc_id_fstar

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
  | NC_true -> string "true"
  | NC_false -> string "false"
  | NC_set (kid, l) -> string "FStar.Set.mem " ^^ doc_var_fstar kid ^^
                         parens (string "FStar.Set.as_set " ^^
                                   brackets (separate_map colon
                                               (fun i -> utf8string (Big_int.to_string i)) l))

let doc_constraints_fstar ncs = separate_map (string " && ") doc_nc_fstar ncs

let doc_typ_fstar, doc_typ_arg_fstar =
  let rtval = "retval__" in
  let use_hoare pre post = length pre > 0 || length post > 0 in
  let add_cons pre quant post tpp =
    if use_hoare pre post then
      string "Pure " ^^ parens tpp ^^
        break 1 ^^ parens (string "requires " ^^
                             (if length pre > 0 then
                                doc_constraints_fstar pre
                              else string "True")) ^^
      break 1 ^^ parens (string "ensures fun " ^^
                           string rtval ^^ string " -> " ^^
                             (if length quant > 0 then
                                (string "exists " ^^
                                   separate_map space doc_var_fstar quant) ^^
                                  string "." ^^ break 1
                              else empty) ^^
                             (if length post > 0 then
                                doc_constraints_fstar post
                              else string "True"))
    else tpp in
  let add_st st tpp =
    if st then (string "st " ^^ parens tpp) else tpp in
  let rec doc_typ_pos parens_needed pre quant post st (Typ_aux (typ, l) as t) =
    let add_cons_r = add_cons pre quant in
    match typ with
    | Typ_tup typs ->
       let tpp = separate (space ^^ star ^^ space)
                   (List.map (doc_typ_pos false [] [] [] false) typs) in
       add_parens parens_needed (add_cons_r post (add_st st tpp))
    | Typ_app (Id_aux (Id "vector", _), [
            Typ_arg_aux (Typ_arg_nexp m, _);
            Typ_arg_aux (Typ_arg_order ord, _);
            Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
       let tpp =  match elem_typ with
         | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
            string "bv_t " ^^ doc_nexp_fstar true m
         | _ ->
            string "list " ^^ doc_typ_pos true [] [] [] false elem_typ in
       add_parens parens_needed (add_cons_r post (add_st st tpp))
    | Typ_app(Id_aux (Id "range", _), [
            Typ_arg_aux (Typ_arg_nexp n, _);
            Typ_arg_aux (Typ_arg_nexp m, _)]) ->
       if use_hoare pre post then
         let post = NC_aux (NC_bounded_le
                              (n, Nexp_aux
                                    (Nexp_id (Id_aux (Id rtval, l)), l)), l) ::
                    NC_aux (NC_bounded_le
                              (Nexp_aux (Nexp_id (Id_aux (Id rtval, l)), l), m), l) :: post in
          add_cons_r post (add_st st (string "int"))
       else
          let tpp = separate space [string "int_between";
                                    doc_nexp_fstar true n;
                                    doc_nexp_fstar true m] in
          add_parens parens_needed (add_st st tpp)
    | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
       if use_hoare pre post then
          let post = NC_aux (NC_equal
                               (Nexp_aux (Nexp_id (Id_aux (Id rtval, l)), l), n), l) :: post in
          add_cons_r post (add_st st (string "int"))
       else
          let tpp = string "int_exact " ^^ doc_nexp_fstar true n in
          add_parens parens_needed (add_st st tpp)
    | Typ_app(id, xs) ->
       let tpp = doc_id_fstar id ^^ space ^^
                   separate_map space (doc_typ_arg true) xs in
       add_parens parens_needed (add_cons_r post (add_st st tpp))
    | Typ_fn (ty1, ty2, eff) ->
       let tpp1 = doc_typ_neg true pre ty1 in
       let tpp2 = match eff with
         | Effect_aux (Effect_set (_::_), _) ->
            doc_typ_pos true pre quant post true ty2
         | _ -> doc_typ_pos false pre quant post false ty2 in
       let tpp = doc_op arrow tpp1 tpp2 in
       add_parens parens_needed (add_st st tpp)
    | Typ_id (Id_aux (Id "bit", _)) ->
       add_cons_r post (add_st st (string "bool"))
    | Typ_id id -> add_cons_r post (add_st st (doc_id_fstar id))
    | Typ_var kid -> add_cons_r post (add_st st (doc_var_fstar kid))
    | Typ_exist (qs, ns, ty) ->
       doc_typ_pos parens_needed pre (append qs quant) (ns::post) false ty
    | _ ->
       let tpp = Pretty_print_sail.doc_typ t in
       add_parens parens_needed tpp
 and doc_typ_neg parens_needed pre (Typ_aux (typ, l) as t) =
   match typ with
    (* Tuples *)
    | Typ_tup (typs) ->
       separate (space ^^ arrow ^^ break 1)
         (List.map (doc_typ_neg false []) typs)
    (* Applications *)
    | Typ_app(Id_aux (Id "vector", _), [
            Typ_arg_aux (Typ_arg_nexp m, _);
            Typ_arg_aux (Typ_arg_order ord, _);
            Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
       let tpp =  match elem_typ with
         | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
            string "bv_t " ^^ doc_nexp_fstar true m
         | _ -> string "list " ^^ doc_typ_neg true [] elem_typ in
       add_parens parens_needed tpp
    | Typ_app(Id_aux (Id "range", _), [
            Typ_arg_aux (Typ_arg_nexp n, _);
            Typ_arg_aux (Typ_arg_nexp m, _)]) ->
       add_parens parens_needed
         (separate space [string "int_between";
                          doc_nexp_fstar true n;
                          doc_nexp_fstar true m])
    | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
       add_parens parens_needed (string "int_exact " ^^ doc_nexp_fstar true n)
    | Typ_app(id, xs) ->
       let tpp = doc_id_fstar id ^^ space ^^
                   separate_map space (doc_typ_arg true) xs in
       add_parens parens_needed tpp
    | Typ_fn (ty1, ty2, eff) ->
       let tpp1 = doc_typ_neg true pre ty1 in
       let tpp2 = match eff with
         | Effect_aux (Effect_set (_::_), _) ->
            string "st " ^^ doc_typ_pos true pre [] [] true ty2
         | _ -> doc_typ_pos false pre [] [] false ty2 in
       let tpp = doc_op arrow tpp1 tpp2 in
       add_parens parens_needed tpp
    | Typ_id (Id_aux (Id "bit", _)) -> string "bool"
    | Typ_id id -> doc_id_fstar id
    | Typ_var kid -> doc_var_fstar kid
    | _ ->
       let tpp = Pretty_print_sail.doc_typ t in
       add_parens parens_needed tpp
 and add_parens parens_needed tpp =
   if parens_needed then parens tpp else tpp
  and doc_typ_arg parens_needed (Typ_arg_aux (ta_aux, _)) =
    match ta_aux with
    | Typ_arg_typ typ -> doc_typ_pos parens_needed [] [] [] false typ
    | Typ_arg_nexp nexp -> doc_nexp_fstar parens_needed nexp
    | Typ_arg_order _ -> empty in
(fun cons -> doc_typ_pos false cons [] [] false), doc_typ_arg false

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
       | Some (env, _, _) when Env.is_union_constructor f env ->
          doc_id_fstar_ctor f
       | Some (env, _, _) when Env.is_extern f env "fstar" ->
          string (Env.get_extern f env "fstar")
       | _ -> doc_id_fstar f in
     parens (hang 2 (flow (break 1) (call :: List.map doc_exp_fstar args)))
  | E_id id ->
     if has_effect (effect_of e) BE_rreg then
       string "read_reg" ^^ space ^^ string "r" ^^ string (get_id_string id)
     else
       begin match destruct_tannot annot with
       | Some (env, _, _) when is_ctor id env -> doc_id_fstar_ctor id
       | _ -> doc_id_fstar id
       end
  | E_vector exps ->
     let dexp = brackets (separate_map (string ";") doc_exp_fstar exps) in
     begin match destruct_tannot annot with
     | Some (env, Typ_aux (typ, _), _) ->
        begin match typ with
        | Typ_app (Id_aux (Id "vector", _), [
              Typ_arg_aux (Typ_arg_nexp m, _);
              Typ_arg_aux (Typ_arg_order ord, _);
              Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
           begin match elem_typ with
           | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
              let outer_id = string "s__tmp" in
              let inner_id = string "l__tmp" in
              let dnexp = doc_nexp_fstar false m in
              parens (doc_op equals (string "let " ^^ outer_id ^^ colon ^^
                                       string "bv_t " ^^ parens dnexp)
                        (parens (doc_op equals (string "let " ^^ inner_id) dexp ^^
                                   string " in" ^^ hardline ^^
                                   string "assert_norm" ^^
                                   parens (string "List.Tot.length " ^^ inner_id ^^ equals ^^
                                             doc_nexp_fstar false m) ^^
                                   semi ^^ hardline ^^
                                     string "list2bv " ^^ inner_id) ^^
                           string " in" ^^ break 1 ^^ outer_id))
           | _ -> dexp
           end
        | _ -> dexp
        end
     | None -> dexp
     end
  | E_if (cond, e1, e2) ->
     string "if " ^^ parens (doc_exp_fstar cond) ^^
       string " then" ^^ break 1 ^^ parens (doc_exp_fstar e1) ^^ break 1 ^^
         string "else " ^^ parens (doc_exp_fstar e2)
  | E_cast (typ, e) -> doc_exp_fstar e
  | E_assign (le, e) ->
     string "update_reg" ^^ space ^^ doc_lexp_fstar le ^^ space ^^ doc_exp_fstar e
  | E_assert (e1, e2) ->
  (* This is a runtime assert. I am using the assume in F* as an
     equivalent for now. *)
     string "assume " ^^ parens (doc_exp_fstar e1)
  | E_constraint nexp ->
     doc_nc_fstar nexp
  | E_let (LB_aux (LB_val (pat, e1), _), e2) ->
     parens (prefix 2 1 (string "let" ^^ space ^^ doc_pat_fstar false false pat ^^
                   space ^^ equals ^^ break 1 ^^ doc_exp_fstar e1 ^^ string " in")
       (parens (doc_exp_fstar e2)))
  | E_internal_return e ->
     let de = doc_exp_fstar e in
     string "return " ^^ parens de
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
and doc_pat_fstar apat_needed cast_omitted (P_aux (p,(l,annot)) as pa) =
  match p with
  | P_app(id, []) -> doc_id_fstar_ctor id
  | P_app(id, ((_ :: _) as pats)) ->
    let ppp = doc_unop (doc_id_fstar_ctor id)
                (separate_map space (doc_pat_fstar true cast_omitted) pats) in
    if apat_needed then parens ppp else ppp
  | P_app(id, []) -> doc_id_fstar_ctor id
  | P_lit lit  -> doc_lit_fstar lit
  | P_wild -> underscore
  | P_id id ->
     begin match destruct_tannot annot with
     | Some (env, _, _) when is_ctor id env ->
        doc_id_fstar_ctor id
     | _ -> doc_id_fstar id
     end
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
and doc_lexp_fstar (LEXP_aux (le, (_, a)) as l) =
  match le with
  | LEXP_id id ->
     begin match destruct_tannot a with
     | Some (env, _, _) -> doc_id_or_reg_fstar id env
     | _ -> doc_id_fstar id
     end
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
     parens ((if imp then string "#" ^^ doc_var_fstar kid
     else doc_var_fstar kid) ^^ string ": int")
  | QI_id (KOpt_aux (KOpt_kind (kind, kid), _)) ->
     parens ((if imp then string "#" ^^ doc_var_fstar kid
             else doc_var_fstar kid) ^^ string ":" ^^ doc_kind_fstar kind)
  | _ -> empty

let doc_quant_var env (QI_aux (qi, _)) = match qi with
  | QI_id (KOpt_aux (KOpt_none kid, annot)) -> doc_var_fstar kid
  | QI_id (KOpt_aux (KOpt_kind (kind, kid), _)) -> doc_var_fstar kid
  | _ -> empty

let quant_and_constraints qs =
  let rec go qs (vars, cons) =
    match qs with
    | QI_aux (QI_id _, _) as qi :: qs' -> go qs' (qi :: vars, cons)
    | QI_aux (QI_const c, _) :: qs' -> go qs' (vars, c :: cons)
    | [] -> (vars, cons) in
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

let doc_typquant_vars_fstar (TypQ_aux(tq,_)) env = match tq with
  | TypQ_tq qs -> separate_map space (doc_quant_var env) qs
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

let doc_type_union_fstar (Tu_aux (Tu_ty_id (typ, id),_)) =
  let tpp = match typ with
  | Typ_aux (Typ_tup typs, _) ->
     separate_map (space ^^ arrow ^^ space) (doc_typ_fstar []) typs
  | _ -> doc_typ_fstar [] typ in
  group (prefix 2 1 (string "| " ^^ doc_id_fstar_ctor id ^^ colon) tpp)

let doc_typdef_fstar (TD_aux(td, annot)) =
  match td with
  | TD_abbrev (id,nm,(TypSchm_aux (TypSchm_ts (typq, _), _) as typschm)) ->
     let env = opt_env_of_annot annot in
     doc_op equals
       (separate space [string "type";
                        doc_id_fstar_type id;
                        doc_typquant_items_fstar typq env])
       (doc_typschm_fstar false typschm env)
  | TD_enum (id,nm,lst,_)->
     doc_op equals
       (string "type" ^^ space ^^ doc_id_fstar_type id)
       (separate_map (break 1)
          (fun id -> string "| " ^^ doc_id_fstar_ctor id) lst)
  | TD_variant (id,nm,typq,lst,_)->
     let env = opt_env_of_annot annot in
     let name = doc_id_fstar_type id  in
     doc_op equals
       (separate space [string "type"; name;
                        space ^^ doc_typquant_items_fstar typq env])
       (separate_map hardline (fun s ->
            doc_type_union_fstar s ^^ space ^^ arrow ^^ space ^^ name ^^
              space ^^ doc_typquant_vars_fstar typq env) lst)
  (* TODO: finish this *)
  | _ -> empty

let args_of_typ l env typ =
  let typs = match typ with
    | Typ_aux (Typ_tup typs, _) -> typs
    | typ -> [typ] in
  let arg i typ =
    let id = mk_id ("arg_" ^ string_of_int i) in
    P_aux (P_id id, (l, mk_tannot env typ no_effect)),
    E_aux (E_id id, (l, mk_tannot env typ no_effect)) in
  List.split (List.mapi arg typs)

let rec untuple_args_pat (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let (Typ_aux (taux, _)) = typ_of_annot annot in
  match paux, taux with
  | P_tup [], _ ->
     let annot = (l, mk_tannot Env.empty unit_typ no_effect) in
     [P_aux (P_lit (mk_lit L_unit), annot)]
  | P_tup pats, _ -> pats
  | P_wild, Typ_tup typs ->
     let wild typ = P_aux (P_wild, (l, mk_tannot env typ no_effect)) in
     List.map wild typs
  | P_typ (_, pat), _ -> untuple_args_pat pat
  | P_as _, Typ_tup _ | P_id _, Typ_tup _ ->
     let pats, _ = args_of_typ l env (pat_typ_of pat) in pats
  | _, _ -> [pat]

let doc_fun_body_fstar exp = doc_exp_fstar exp

let orig_quant_item (QI_aux (q, l) as qa) = match q with
  | QI_id (KOpt_aux (k, l')) ->
     let k' = match k with
     | KOpt_none kid -> KOpt_none (orig_kid kid)
     | KOpt_kind (kind, kid) -> KOpt_kind (kind, orig_kid kid) in
     QI_aux (QI_id (KOpt_aux (k', l')), l)
  | _ -> qa

let doc_funcl_fstar (FCL_aux(FCL_Funcl(id, pexp), annot)) =
  let typ = typ_of_annot annot in
  let pat,guard,exp,(l,_) = destruct_pexp pexp in
  let _ = match guard with
    | None -> ()
    | _ ->
       raise (Reporting_basic.err_unreachable l
                "guarded pattern expression should have been rewritten before pretty-printing") in
  let imp_pars =
    let env = env_of_annot annot in
    let quants, typ = Env.get_val_spec id env in
    match quants with
    | TypQ_aux (TypQ_tq qs, _) ->
       let vars, _ = quant_and_constraints qs in
       let vars' = map orig_quant_item vars in
       separate_map space (doc_quant_item (Some env) true) vars'
    | _ -> empty in
  let pats = untuple_args_pat pat in
  let patspp = separate_map space (doc_pat_fstar true false) pats in
  group (prefix 3 1
           (separate space [doc_id_fstar id; imp_pars; patspp; equals])
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
