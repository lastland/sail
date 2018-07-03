open Type_check
open Ast
open Ast_util
open State
open Format
open List
open PPrint
open Pretty_print_common

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

let doc_id_fstar = Pretty_print_sail.doc_id

let doc_typ_fstar = Pretty_print_sail.doc_typ

let rec doc_exp_fstar (E_aux (exp, _) as e) = match exp with
  | E_case (exp, pexps) ->
     separate space [string "match"; doc_exp_fstar exp;
                     string "with" ^^ hardline ^^ doc_pexps_fstar pexps]
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

let doc_def_fstar def =
  match def with
  | DEF_fundef fdef -> group (doc_fundef_fstar fdef) ^/^ hardline
  | _ -> empty

let pp_defs_fstar (regs_file, defs_file, defs_modules) regs (Defs defs) top_line =
  pp_regs_fstar (regs_file, defs_modules) regs;
  let is_typ_def = function
    | DEF_type _ -> true
    | _ -> false
  in
  let typdefs, defs = List.partition is_typ_def defs in
  (print defs_file)
    (concat
       [separate empty (List.map doc_def_fstar typdefs); hardline;
        hardline;
        separate empty (List.map doc_def_fstar defs)])
