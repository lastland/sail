open Type_check
open Ast
open Ast_util
open State
open Format
open List
open PPrint
open Pretty_print_common

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

let rec pp_n_regtype_rec o regs =
  match regs with
  | [] -> ()
  | r :: regs' ->
     fprintf o "@\n@[| r%s -> %u@]" (get_id_string r.regid) r.regnum;
     pp_n_regtype_rec o regs'

let pp_n_regtype o regs =
  fprintf o "@\n@[<hov 2>let n_regtype (n : reg_t) : pos =@ match n with";
  pp_n_regtype_rec o regs;
  fprintf o "@]@\n"

let rec pp_regval_rec o regs =
  match regs with
  | [] -> ()
  | r :: regs' ->
     fprintf o "@\n@[| r%s -> bits %u@]" (get_id_string r.regid) r.reglen;
     pp_regval_rec o regs'

let pp_regval o regs =
  fprintf o "@\n@[<hov 2>let regval (n : reg_t) : Type0 =@ match n with";
  pp_regval_rec o regs;
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
       let tnexp = doc_op (string "*") (doc_nexp true n1) (doc_nexp true n2) in
       if parens_needed then parens tnexp else tnexp
    | Nexp_sum (n1, n2) ->
       let tnexp = doc_op (string "+") (doc_nexp true n1) (doc_nexp true n2) in
       if parens_needed then parens tnexp else tnexp
    | Nexp_minus (n1, n2) ->
       let tnexp = doc_op (string "-") (doc_nexp true n1) (doc_nexp true n2) in
       if parens_needed then parens tnexp else tnexp
    | Nexp_exp n ->
       let tnexp = string "2^" ^^ doc_nexp true n in
       if parens_needed then parens tnexp else tnexp
    | Nexp_neg n ->
       let tnexp = string "-" ^^ doc_nexp true n in
       if parens_needed then parens tnexp else tnexp in
  doc_nexp parens_needed m

let doc_typ_fstar, doc_typ_arg_fstar =
  let rec typ_p ty = doc_typ true ty
  and typ_n ty = doc_typ false ty
  and doc_typ parens_needed (Typ_aux (typ, _) as t) =
    match typ with
    (* Tuples *)
    | Typ_tup (typs) ->
       let tpp = separate (string " * ") (List.map typ_n typs) in
       if parens_needed then parens tpp else tpp
    (* Applications *)
    | Typ_app(Id_aux (Id "vector", _), [
            Typ_arg_aux (Typ_arg_nexp m, _);
            Typ_arg_aux (Typ_arg_order ord, _);
            Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
       let tpp =  match elem_typ with
         | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
            string "bv_t " ^^ doc_nexp_fstar true m
         | _ -> string "list " ^^ typ_p elem_typ in
       if parens_needed then parens tpp else tpp
    | Typ_app(Id_aux (Id "range", _), [
            Typ_arg_aux (Typ_arg_nexp n, _);
            Typ_arg_aux (Typ_arg_nexp m, _)]) ->
       separate space [string "int_between";
                       doc_nexp_fstar true n;
                       doc_nexp_fstar true m]
    | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
       string "int_exact " ^^ doc_nexp_fstar true n
    | Typ_app(id, xs) ->
       let tpp = doc_id_fstar id ^^ space ^^
                   separate_map space (doc_typ_arg true) xs in
       if parens_needed then parens tpp else tpp
    (* Functions *)
    | Typ_fn (ty1, ty2, eff) ->
       let tpp2 = match eff with
         | Effect_aux (Effect_set (_::_), _) -> string "st " ^^ typ_p ty2
         | _ -> typ_n ty2 in
       let tpp = doc_op (string "->") (typ_p ty1) (tpp2) in
       if parens_needed then parens tpp else tpp
    (* Ids *)
    | Typ_id (Id_aux (Id "bit", _)) -> string "bool"
    | Typ_id id -> doc_id_fstar id
    (* Vars *)
    | Typ_var v -> doc_var_fstar v
    (* Others *)
    | _ -> let tpp = Pretty_print_sail.doc_typ t in
           if parens_needed then parens tpp else tpp
  and doc_typ_arg parens_needed (Typ_arg_aux (ta_aux, _)) =
    match ta_aux with
    | Typ_arg_typ typ -> doc_typ parens_needed typ
    | Typ_arg_nexp nexp -> doc_nexp_fstar parens_needed nexp
    | Typ_arg_order _ -> empty
  in typ_n, doc_typ_arg false

let rec doc_exp_fstar (E_aux (exp, (l, annot)) as e) =
  match exp with
  | E_case (exp, pexps) ->
     separate space [string "match"; doc_exp_fstar exp;
                     string "with" ^^ hardline ^^ doc_pexps_fstar pexps]
  | E_app (f, args) ->
     let call = match annot with
       | Some (env, _, _) when Env.is_extern f env "fstar" ->
          string (Env.get_extern f env "fstar")
       | _ -> doc_id_fstar f in
     parens (hang 2 (flow (break 1) (call :: List.map doc_exp_fstar args)))
  | E_id id -> doc_id_fstar id
  | _ -> Pretty_print_sail.doc_exp e
and doc_pexp_fstar (Pat_aux (pat_aux, _)) =
  match pat_aux with
  | Pat_exp (pat, exp) ->
     separate space [string "|"; doc_pat_fstar true pat;
                     string "->"; doc_exp_fstar exp]
  | Pat_when (pat, wh, exp) ->
     separate space [string "|"; doc_pat_fstar true pat;
                     string "if"; doc_exp_fstar wh;
                     string "then"; doc_exp_fstar exp]
and doc_pexps_fstar pexps = separate_map hardline doc_pexp_fstar pexps
and doc_pat_fstar apat_needed (P_aux (p,(l,annot)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) ->
    let ppp = doc_unop (doc_id_fstar_ctor id)
                (parens (separate_map comma (doc_pat_fstar true) pats)) in
    if apat_needed then parens ppp else ppp
  | P_app(id, []) -> doc_id_fstar_ctor id
  | P_lit lit  -> doc_lit_fstar lit
  | P_wild -> underscore
  | P_id id -> doc_id_fstar id
  | P_var(p,_) -> doc_pat_fstar true p
  | P_as(p,id) -> parens (separate space
                            [doc_pat_fstar true p; string "as"; doc_id_fstar id])
  | P_typ(typ,p) ->
     let doc_p = doc_pat_fstar true p in
     parens (doc_op colon doc_p (doc_typ_fstar typ))
  | P_vector pats ->
     let ppp = brackets (separate_map semi (doc_pat_fstar true) pats) in
     if apat_needed then parens ppp else ppp
  | P_vector_concat pats ->
     raise (Reporting_basic.err_unreachable l
       "vector concatenation patterns should have been removed before pretty-printing")
  | P_tup pats  ->
     (match pats with
      | [p] -> doc_pat_fstar apat_needed p
      | _ -> parens (separate_map comma_sp (doc_pat_fstar false) pats))
  | P_list pats -> brackets (separate_map semi (doc_pat_fstar false) pats) (*Never seen but easy in lem*)
  | P_cons (p,p') -> doc_op (string "::") (doc_pat_fstar true p) (doc_pat_fstar true p')
  | P_record (_,_) -> empty (* TODO *)

let doc_kind_fstar (K_aux (K_kind ((BK_aux (k, _))::_), _)) =
  let s = match k with
  | BK_type -> "Type"
  | BK_int -> "int"
  | BK_order -> "bool" in
  string s

let doc_quant_item (QI_aux (qi, _)) = match qi with
  | QI_id (KOpt_aux (KOpt_none kid, _)) -> doc_var_fstar kid
  | QI_id (KOpt_aux (KOpt_kind (kind, kid), _)) ->
     parens (doc_var_fstar kid ^^ string ":" ^^ doc_kind_fstar kind)
  | _ -> empty

let doc_typquant_fstar (TypQ_aux(tq,_)) typ = match tq with
  | TypQ_tq ((_ :: _) as qs) ->
     string "forall " ^^ separate_map space doc_quant_item qs
     ^^ string ". " ^^ typ
  | _ -> typ


let doc_typquant_items_fstar (TypQ_aux(tq,_)) = match tq with
  | TypQ_tq qs -> separate_map space doc_quant_item qs
  | _ -> empty

let doc_typschm_fstar quants (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  let pt = doc_typ_fstar t in
(*  then
    let nexps_used = lem_nexps_of_typ t in
    let ptyc, nexps_sizes = doc_typclasses_lem t in
    let nexps_to_include = NexpSet.union nexps_used nexps_sizes in
    if NexpSet.is_empty nexps_to_include
    then pt
    else doc_typquant_fstar tq (Some nexps_to_include) (ptyc ^^ pt) *)
  if quants then doc_typquant_fstar tq pt else pt

let doc_typdef_fstar (TD_aux(td, (l, annot))) =
  match td with
  | TD_abbrev(id,nm,(TypSchm_aux (TypSchm_ts (typq, _), _) as typschm)) ->
     doc_op equals
       (separate space [string "type";
                        doc_id_fstar_type id;
                        doc_typquant_items_fstar typq])
       (doc_typschm_fstar false typschm)
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
    (separate space [doc_id_fstar id; doc_pat_fstar true pat; equals])
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
         doc_typschm_fstar true typschm] ^/^ hardline
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
