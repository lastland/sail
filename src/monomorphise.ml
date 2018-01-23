(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Parse_ast
open Ast
open Ast_util
module Big_int = Nat_big_num
open Type_check

let size_set_limit = 16

let optmap v f =
  match v with
  | None -> None
  | Some v -> Some (f v)

let kbindings_from_list = List.fold_left (fun s (v,i) -> KBindings.add v i s) KBindings.empty
let bindings_from_list = List.fold_left (fun s (v,i) -> Bindings.add v i s) Bindings.empty
(* union was introduced in 4.03.0, a bit too recently *)
let bindings_union s1 s2 =
  Bindings.merge (fun _ x y -> match x,y with
  |  _, (Some x) -> Some x
  |  (Some x), _ -> Some x
  |  _,  _ -> None) s1 s2

let subst_nexp substs nexp =
  let rec s_snexp substs (Nexp_aux (ne,l) as nexp) =
    let re ne = Nexp_aux (ne,l) in
    let s_snexp = s_snexp substs in
    match ne with
    | Nexp_var (Kid_aux (_,l) as kid) ->
       (try KBindings.find kid substs
       with Not_found -> nexp)
    | Nexp_id _
    | Nexp_constant _ -> nexp
    | Nexp_times (n1,n2) -> re (Nexp_times (s_snexp n1, s_snexp n2))
    | Nexp_sum (n1,n2)   -> re (Nexp_sum   (s_snexp n1, s_snexp n2))
    | Nexp_minus (n1,n2) -> re (Nexp_minus (s_snexp n1, s_snexp n2))
    | Nexp_exp ne -> re (Nexp_exp (s_snexp ne))
    | Nexp_neg ne -> re (Nexp_neg (s_snexp ne))
    | Nexp_app (id,args) -> re (Nexp_app (id,List.map s_snexp args))
  in s_snexp substs nexp

let rec subst_nc substs (NC_aux (nc,l) as n_constraint) =
  let snexp nexp = subst_nexp substs nexp in
  let snc nc = subst_nc substs nc in
  let re nc = NC_aux (nc,l) in
  match nc with
  | NC_equal (n1,n2) -> re (NC_equal (snexp n1, snexp n2))
  | NC_bounded_ge (n1,n2) -> re (NC_bounded_ge (snexp n1, snexp n2))
  | NC_bounded_le (n1,n2) -> re (NC_bounded_le (snexp n1, snexp n2))
  | NC_not_equal (n1,n2) -> re (NC_not_equal (snexp n1, snexp n2))
  | NC_set (kid,is) ->
     begin
       match KBindings.find kid substs with
       | Nexp_aux (Nexp_constant i,_) ->
          if List.exists (fun j -> Big_int.equal i j) is then re NC_true else re NC_false
       | nexp -> 
          raise (Reporting_basic.err_general l
                   ("Unable to substitute " ^ string_of_nexp nexp ^
                       " into set constraint " ^ string_of_n_constraint n_constraint))
       | exception Not_found -> n_constraint
     end
  | NC_or (nc1,nc2) -> re (NC_or (snc nc1, snc nc2))
  | NC_and (nc1,nc2) -> re (NC_and (snc nc1, snc nc2))
  | NC_true
  | NC_false
      -> n_constraint



let subst_src_typ substs t =
  let rec s_styp substs ((Typ_aux (t,l)) as ty) =
    let re t = Typ_aux (t,l) in
    match t with
    | Typ_id _
    | Typ_var _
      -> ty
    | Typ_fn (t1,t2,e) -> re (Typ_fn (s_styp substs t1, s_styp substs t2,e))
    | Typ_tup ts -> re (Typ_tup (List.map (s_styp substs) ts))
    | Typ_app (id,tas) -> re (Typ_app (id,List.map (s_starg substs) tas))
    | Typ_exist (kids,nc,t) ->
       let substs = List.fold_left (fun sub v -> KBindings.remove v sub) substs kids in
       re (Typ_exist (kids,nc,s_styp substs t))
  and s_starg substs (Typ_arg_aux (ta,l) as targ) =
    match ta with
    | Typ_arg_nexp ne -> Typ_arg_aux (Typ_arg_nexp (subst_nexp substs ne),l)
    | Typ_arg_typ t -> Typ_arg_aux (Typ_arg_typ (s_styp substs t),l)
    | Typ_arg_order _ -> targ
  in s_styp substs t

let make_vector_lit sz i =
  let f j = if Big_int.equal (Big_int.modulus (Big_int.shift_right i (sz-j-1)) (Big_int.of_int 2)) Big_int.zero then '0' else '1' in
  let s = String.init sz f in
  L_aux (L_bin s,Generated Unknown)

let tabulate f n =
  let rec aux acc n =
    let acc' = f n::acc in
    if Big_int.equal n Big_int.zero then acc' else aux acc' (Big_int.sub n (Big_int.of_int 1))
  in if Big_int.equal n Big_int.zero then [] else aux [] (Big_int.sub n (Big_int.of_int 1))

let make_vectors sz =
  tabulate (make_vector_lit sz) (Big_int.shift_left (Big_int.of_int 1) sz)

let pat_id_is_variable env id =
  match Env.lookup_id id env with
  (* Unbound is returned for both variables and constructors which take
     arguments, but the latter only don't appear in a P_id *)
  | Unbound
  (* Shadowing of immutable locals is allowed; mutable locals and registers
     are rejected by the type checker, so don't matter *)
  | Local _
  | Register _
    -> true
  | Enum _
  | Union _
    -> false

let rec is_value (E_aux (e,(l,annot))) =
  let is_constructor id =
    match annot with
    | None -> 
       (Reporting_basic.print_err false true l "Monomorphisation"
          ("Missing type information for identifier " ^ string_of_id id);
        false) (* Be conservative if we have no info *)
    | Some (env,_,_) ->
       Env.is_union_constructor id env ||
         (match Env.lookup_id id env with
         | Enum _ | Union _ -> true 
         | Unbound | Local _ | Register _ -> false)
  in
  match e with
  | E_id id -> is_constructor id
  | E_lit _ -> true
  | E_tuple es -> List.for_all is_value es
  | E_app (id,es) -> is_constructor id && List.for_all is_value es
  (* We add casts to undefined to keep the type information in the AST *)
  | E_cast (typ,E_aux (E_lit (L_aux (L_undef,_)),_)) -> true
(* TODO: more? *)
  | _ -> false

let is_pure (Effect_opt_aux (e,_)) =
  match e with
  | Effect_opt_pure -> true
  | Effect_opt_effect (Effect_aux (Effect_set [],_)) -> true
  | _ -> false

let rec list_extract f = function
  | [] -> None
  | h::t -> match f h with None -> list_extract f t | Some v -> Some v

let rec cross = function
  | [] -> failwith "cross"
  | [(x,l)] -> List.map (fun y -> [(x,y)]) l
  | (x,l)::t -> 
     let t' = cross t in
     List.concat (List.map (fun y -> List.map (fun l' -> (x,y)::l') t') l)

let rec cross' = function
  | [] -> [[]]
  | (h::t) ->
     let t' = cross' t in
     List.concat (List.map (fun x -> List.map (fun l ->  x::l) t') h)

let rec cross'' = function
  | [] -> [[]]
  | (k,None)::t -> List.map (fun l -> (k,None)::l) (cross'' t)
  | (k,Some h)::t ->
     let t' = cross'' t in
     List.concat (List.map (fun x -> List.map (fun l -> (k,Some x)::l) t') h)

let kidset_bigunion = function
  | [] -> KidSet.empty
  | h::t -> List.fold_left KidSet.union h t

(* TODO: deal with non-set constraints, intersections, etc somehow *)
let extract_set_nc l var nc =
  let rec aux (NC_aux (nc,l)) =
    let re nc = NC_aux (nc,l) in
    match nc with
    | NC_set (id,is) when Kid.compare id var = 0 -> Some (is,re NC_true)
    | NC_and (nc1,nc2) ->
       (match aux nc1, aux nc2 with
       | None, None -> None
       | None, Some (is,nc2') -> Some (is, re (NC_and (nc1,nc2')))
       | Some (is,nc1'), None -> Some (is, re (NC_and (nc1',nc2)))
       | Some _, Some _ ->
          raise (Reporting_basic.err_general l ("Multiple set constraints for " ^ string_of_kid var)))
    | _ -> None
  in match aux nc with
  | Some is -> is
  | None ->
     raise (Reporting_basic.err_general l ("No set constraint for " ^ string_of_kid var))

let rec peel = function
  | [], l -> ([], l)
  | h1::t1, h2::t2 -> let (l1,l2) = peel (t1, t2) in ((h1,h2)::l1,l2)
  | _,_ -> assert false

let rec split_insts = function
  | [] -> [],[]
  | (k,None)::t -> let l1,l2 = split_insts t in l1,k::l2
  | (k,Some v)::t -> let l1,l2 = split_insts t in (k,v)::l1,l2

let apply_kid_insts kid_insts t =
  let kid_insts, kids' = split_insts kid_insts in
  let kid_insts = List.map (fun (v,i) -> (v,Nexp_aux (Nexp_constant i,Generated Unknown))) kid_insts in
  let subst = kbindings_from_list kid_insts in
  kids', subst_src_typ subst t

let rec inst_src_type insts (Typ_aux (ty,l) as typ) =
  match ty with
  | Typ_id _
  | Typ_var _
    -> insts,typ
  | Typ_fn _ ->
     raise (Reporting_basic.err_general l "Function type in constructor")
  | Typ_tup ts ->
     let insts,ts = 
       List.fold_right
         (fun typ (insts,ts) -> let insts,typ = inst_src_type insts typ in insts,typ::ts)
         ts (insts,[])
     in insts, Typ_aux (Typ_tup ts,l)
  | Typ_app (id,args) ->
     let insts,ts = 
       List.fold_right
         (fun arg (insts,args) -> let insts,arg = inst_src_typ_arg insts arg in insts,arg::args)
         args (insts,[])
     in insts, Typ_aux (Typ_app (id,ts),l)
  | Typ_exist (kids, nc, t) ->
     let kid_insts, insts' = peel (kids,insts) in
     let kids', t' = apply_kid_insts kid_insts t in
     (* TODO: subst in nc *)
     match kids' with
     | [] -> insts', t'
     | _ -> insts', Typ_aux (Typ_exist (kids', nc, t'), l)
and inst_src_typ_arg insts (Typ_arg_aux (ta,l) as tyarg) =
  match ta with
  | Typ_arg_nexp _
  | Typ_arg_order _
      -> insts, tyarg
  | Typ_arg_typ typ ->
     let insts', typ' = inst_src_type insts typ in
     insts', Typ_arg_aux (Typ_arg_typ typ',l)

let rec contains_exist (Typ_aux (ty,_)) =
  match ty with
  | Typ_id _
  | Typ_var _
    -> false
  | Typ_fn (t1,t2,_) -> contains_exist t1 || contains_exist t2
  | Typ_tup ts -> List.exists contains_exist ts
  | Typ_app (_,args) -> List.exists contains_exist_arg args
  | Typ_exist _ -> true
and contains_exist_arg (Typ_arg_aux (arg,_)) =
  match arg with
  | Typ_arg_nexp _
  | Typ_arg_order _
      -> false
  | Typ_arg_typ typ -> contains_exist typ

let rec size_nvars_nexp (Nexp_aux (ne,_)) =
  match ne with
  | Nexp_var v -> [v]
  | Nexp_id _
  | Nexp_constant _
    -> []
  | Nexp_times (n1,n2)
  | Nexp_sum (n1,n2)
  | Nexp_minus (n1,n2)
    -> size_nvars_nexp n1 @ size_nvars_nexp n2
  | Nexp_exp n
  | Nexp_neg n
    -> size_nvars_nexp n
  | Nexp_app (_,args) -> List.concat (List.map size_nvars_nexp args)

(* Given a type for a constructor, work out which refinements we ought to produce *)
(* TODO collision avoidance *)
let split_src_type id ty (TypQ_aux (q,ql)) =
  let i = string_of_id id in
  (* This was originally written for the general case, but I cut it down to the
     more manageable prenex-form below *)
  let rec size_nvars_ty (Typ_aux (ty,l) as typ) =
    match ty with
    | Typ_id _
    | Typ_var _
      -> (KidSet.empty,[[],typ])
    | Typ_fn _ ->
       raise (Reporting_basic.err_general l ("Function type in constructor " ^ i))
    | Typ_tup ts ->
       let (vars,tys) = List.split (List.map size_nvars_ty ts) in
       let insttys = List.map (fun x -> let (insts,tys) = List.split x in
                                        List.concat insts, Typ_aux (Typ_tup tys,l)) (cross' tys) in
       (kidset_bigunion vars, insttys)
    | Typ_app (Id_aux (Id "vector",_),
               [Typ_arg_aux (Typ_arg_nexp sz,_);
                _;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]) ->
       (KidSet.of_list (size_nvars_nexp sz), [[],typ])
    | Typ_app (_, tas) ->
       (KidSet.empty,[[],typ])  (* We only support sizes for bitvectors mentioned explicitly, not any buried
                      inside another type *)
    | Typ_exist (kids, nc, t) ->
       let (vars,tys) = size_nvars_ty t in
       let find_insts k (insts,nc) =
         let inst,nc' =
           if KidSet.mem k vars then
             let is,nc' = extract_set_nc l k nc in
             Some is,nc'
           else None,nc
         in (k,inst)::insts,nc'
       in
       let (insts,nc') = List.fold_right find_insts kids ([],nc) in
       let insts = cross'' insts in
       let ty_and_inst (inst0,ty) inst =
         let kids, ty = apply_kid_insts inst ty in
         let ty =
           (* Typ_exist is not allowed an empty list of kids *)
           match kids with
           | [] -> ty
           | _ -> Typ_aux (Typ_exist (kids, nc', ty),l)
         in inst@inst0, ty
       in
       let tys = List.concat (List.map (fun instty -> List.map (ty_and_inst instty) insts) tys) in
       let free = List.fold_left (fun vars k -> KidSet.remove k vars) vars kids in
       (free,tys)
  in
  (* Only single-variable prenex-form for now *)
  let size_nvars_ty (Typ_aux (ty,l) as typ) =
    match ty with
    | Typ_exist (kids,_,t) ->
       begin
         match snd (size_nvars_ty typ) with
         | [] -> []
         | tys ->
            (* One level of tuple type is stripped off by the type checker, so
               add another here *)
            let tys =
              List.map (fun (x,ty) ->
                x, match ty with
                | Typ_aux (Typ_tup _,_) -> Typ_aux (Typ_tup [ty],Unknown)
                | _ -> ty) tys in
            if contains_exist t then
              raise (Reporting_basic.err_general l
                       "Only prenex types in unions are supported by monomorphisation")
            else if List.length kids > 1 then
              raise (Reporting_basic.err_general l
                       "Only single-variable existential types in unions are currently supported by monomorphisation")
            else tys
       end
    | _ -> []
  in
  (* TODO: reject universally quantification or monomorphise it *)
  let variants = size_nvars_ty ty in
  match variants with
  | [] -> None
  | sample::__ ->
     let () = if List.length variants > size_set_limit then
         raise (Reporting_basic.err_general ql
                  (string_of_int (List.length variants) ^ "variants for constructor " ^ i ^
                     "bigger than limit " ^ string_of_int size_set_limit)) else ()
     in
     let wrap = match id with
       | Id_aux (Id i,l) -> (fun f -> Id_aux (Id (f i),Generated l))
       | Id_aux (DeIid i,l) -> (fun f -> Id_aux (DeIid (f i),l))
     in
     let name_seg = function
       | (_,None) -> ""
       | (k,Some i) -> string_of_kid k ^ Big_int.to_string i
     in
     let name l i = String.concat "_" (i::(List.map name_seg l)) in
     Some (List.map (fun (l,ty) -> (l, wrap (name l),ty)) variants)

let reduce_nexp subst ne =
  let rec eval (Nexp_aux (ne,_) as nexp) =
    match ne with
    | Nexp_constant i -> i
    | Nexp_sum (n1,n2) -> Big_int.add (eval n1) (eval n2)
    | Nexp_minus (n1,n2) -> Big_int.sub (eval n1) (eval n2)
    | Nexp_times (n1,n2) -> Big_int.mul (eval n1) (eval n2)
    | Nexp_exp n -> Big_int.shift_left (eval n) 1
    | Nexp_neg n -> Big_int.negate (eval n)
    | _ ->
       raise (Reporting_basic.err_general Unknown ("Couldn't turn nexp " ^
                                                      string_of_nexp nexp ^ " into concrete value"))
  in eval ne


let typ_of_args args =
  match args with
  | [E_aux (E_tuple args,(_,Some (_,Typ_aux (Typ_exist _,_),_)))] ->
     let tys = List.map Type_check.typ_of args in
     Typ_aux (Typ_tup tys,Unknown)
  | [exp] ->
     Type_check.typ_of exp
  | _ ->
     let tys = List.map Type_check.typ_of args in
     Typ_aux (Typ_tup tys,Unknown)

(* Check to see if we need to monomorphise a use of a constructor.  Currently
   assumes that bitvector sizes are always given as a variable; don't yet handle
   more general cases (e.g., 8 * var) *)

let refine_constructor refinements l env id args =
  match List.find (fun (id',_) -> Id.compare id id' = 0) refinements with
  | (_,irefinements) -> begin
    let (_,constr_ty) = Env.get_val_spec id env in
    match constr_ty with
    | Typ_aux (Typ_fn (constr_ty,_,_),_) -> begin
       let arg_ty = typ_of_args args in
       match Type_check.destruct_exist env constr_ty with
       | None -> None
       | Some (kids,nc,constr_ty) ->
          let (bindings,_,_) = Type_check.unify l env constr_ty arg_ty in
          let find_kid kid = try Some (KBindings.find kid bindings) with Not_found -> None in
          let bindings = List.map find_kid kids in
          let matches_refinement (mapping,_,_) =
            List.for_all2
              (fun v (_,w) ->
                match v,w with
                | _,None -> true
                | Some (U_nexp (Nexp_aux (Nexp_constant n, _))),Some m -> Big_int.equal n m
                | _,_ -> false) bindings mapping
          in
          match List.find matches_refinement irefinements with
          | (_,new_id,_) -> Some (E_app (new_id,args))
          | exception Not_found ->
             (Reporting_basic.print_err false true l "Monomorphisation"
                ("Unable to refine constructor " ^ string_of_id id);
              None)
    end
    | _ -> None
  end
  | exception Not_found -> None


(* Substitute found nexps for variables in an expression, and rename constructors to reflect
   specialisation *)

(* TODO: kid shadowing *)
let nexp_subst_fns substs =

  let s_t t = subst_src_typ substs t in
(*  let s_typschm (TypSchm_aux (TypSchm_ts (q,t),l)) = TypSchm_aux (TypSchm_ts (q,s_t t),l) in
   hopefully don't need this anyway *)(*
  let s_typschm tsh = tsh in*)
  let s_tannot = function
    | None -> None
    | Some (env,t,eff) -> Some (env,s_t t,eff) (* TODO: what about env? *)
  in
  let rec s_pat (P_aux (p,(l,annot))) =
    let re p = P_aux (p,(l,s_tannot annot)) in
    match p with
    | P_lit _ | P_wild | P_id _ -> re p
    | P_var (p',kid) -> re (P_var (s_pat p',kid))
    | P_as (p',id) -> re (P_as (s_pat p', id))
    | P_typ (ty,p') -> re (P_typ (s_t ty,s_pat p'))
    | P_app (id,ps) -> re (P_app (id, List.map s_pat ps))
    | P_record (fps,flag) -> re (P_record (List.map s_fpat fps, flag))
    | P_vector ps -> re (P_vector (List.map s_pat ps))
    | P_vector_concat ps -> re (P_vector_concat (List.map s_pat ps))
    | P_tup ps -> re (P_tup (List.map s_pat ps))
    | P_list ps -> re (P_list (List.map s_pat ps))
    | P_cons (p1,p2) -> re (P_cons (s_pat p1, s_pat p2))
  and s_fpat (FP_aux (FP_Fpat (id, p), (l,annot))) =
    FP_aux (FP_Fpat (id, s_pat p), (l,s_tannot annot))
  in
  let rec s_exp (E_aux (e,(l,annot))) =
    let re e = E_aux (e,(l,s_tannot annot)) in
      match e with
      | E_block es -> re (E_block (List.map s_exp es))
      | E_nondet es -> re (E_nondet (List.map s_exp es))
      | E_id _
      | E_lit _
      | E_comment _ -> re e
      | E_sizeof ne -> re (E_sizeof ne) (* TODO: does this need done?  does it appear in type checked code? *)
      | E_constraint nc -> re (E_constraint (subst_nc substs nc))
      | E_internal_exp (l,annot) -> re (E_internal_exp (l, s_tannot annot))
      | E_sizeof_internal (l,annot) -> re (E_sizeof_internal (l, s_tannot annot))
      | E_internal_exp_user ((l1,annot1),(l2,annot2)) ->
         re (E_internal_exp_user ((l1, s_tannot annot1),(l2, s_tannot annot2)))
      | E_cast (t,e') -> re (E_cast (s_t t, s_exp e'))
      | E_app (id,es) -> re (E_app (id, List.map s_exp es))
      | E_app_infix (e1,id,e2) -> re (E_app_infix (s_exp e1,id,s_exp e2))
      | E_tuple es -> re (E_tuple (List.map s_exp es))
      | E_if (e1,e2,e3) -> re (E_if (s_exp e1, s_exp e2, s_exp e3))
      | E_for (id,e1,e2,e3,ord,e4) -> re (E_for (id,s_exp e1,s_exp e2,s_exp e3,ord,s_exp e4))
      | E_loop (loop,e1,e2) -> re (E_loop (loop,s_exp e1,s_exp e2))
      | E_vector es -> re (E_vector (List.map s_exp es))
      | E_vector_access (e1,e2) -> re (E_vector_access (s_exp e1,s_exp e2))
      | E_vector_subrange (e1,e2,e3) -> re (E_vector_subrange (s_exp e1,s_exp e2,s_exp e3))
      | E_vector_update (e1,e2,e3) -> re (E_vector_update (s_exp e1,s_exp e2,s_exp e3))
      | E_vector_update_subrange (e1,e2,e3,e4) -> re (E_vector_update_subrange (s_exp e1,s_exp e2,s_exp e3,s_exp e4))
      | E_vector_append (e1,e2) -> re (E_vector_append (s_exp e1,s_exp e2))
      | E_list es -> re (E_list (List.map s_exp es))
      | E_cons (e1,e2) -> re (E_cons (s_exp e1,s_exp e2))
      | E_record fes -> re (E_record (s_fexps fes))
      | E_record_update (e,fes) -> re (E_record_update (s_exp e, s_fexps fes))
      | E_field (e,id) -> re (E_field (s_exp e,id))
      | E_case (e,cases) -> re (E_case (s_exp e, List.map s_pexp cases))
      | E_let (lb,e) -> re (E_let (s_letbind lb, s_exp e))
      | E_assign (le,e) -> re (E_assign (s_lexp le, s_exp e))
      | E_exit e -> re (E_exit (s_exp e))
      | E_return e -> re (E_return (s_exp e))
      | E_assert (e1,e2) -> re (E_assert (s_exp e1,s_exp e2))
      | E_internal_cast ((l,ann),e) -> re (E_internal_cast ((l,s_tannot ann),s_exp e))
      | E_comment_struc e -> re (E_comment_struc e)
      | E_var (le,e1,e2) -> re (E_var (s_lexp le, s_exp e1, s_exp e2))
      | E_internal_plet (p,e1,e2) -> re (E_internal_plet (s_pat p, s_exp e1, s_exp e2))
      | E_internal_return e -> re (E_internal_return (s_exp e))
      | E_throw e -> re (E_throw (s_exp e))
      | E_try (e,cases) -> re (E_try (s_exp e, List.map s_pexp cases))
    and s_opt_default (Def_val_aux (ed,(l,annot))) =
      match ed with
      | Def_val_empty -> Def_val_aux (Def_val_empty,(l,s_tannot annot))
      | Def_val_dec e -> Def_val_aux (Def_val_dec (s_exp e),(l,s_tannot annot))
    and s_fexps (FES_aux (FES_Fexps (fes,flag), (l,annot))) =
      FES_aux (FES_Fexps (List.map s_fexp fes, flag), (l,s_tannot annot))
    and s_fexp (FE_aux (FE_Fexp (id,e), (l,annot))) =
      FE_aux (FE_Fexp (id,s_exp e),(l,s_tannot annot))
    and s_pexp = function
      | (Pat_aux (Pat_exp (p,e),(l,annot))) ->
         Pat_aux (Pat_exp (s_pat p, s_exp e),(l,s_tannot annot))
      | (Pat_aux (Pat_when (p,e1,e2),(l,annot))) ->
         Pat_aux (Pat_when (s_pat p, s_exp e1, s_exp e2),(l,s_tannot annot))
    and s_letbind (LB_aux (lb,(l,annot))) =
      match lb with
      | LB_val (p,e) -> LB_aux (LB_val (s_pat p,s_exp e), (l,s_tannot annot))
    and s_lexp (LEXP_aux (e,(l,annot))) =
      let re e = LEXP_aux (e,(l,s_tannot annot)) in
      match e with
      | LEXP_id _ -> re e
      | LEXP_cast (typ,id) -> re (LEXP_cast (s_t typ, id))
      | LEXP_memory (id,es) -> re (LEXP_memory (id,List.map s_exp es))
      | LEXP_tup les -> re (LEXP_tup (List.map s_lexp les))
      | LEXP_vector (le,e) -> re (LEXP_vector (s_lexp le, s_exp e))
      | LEXP_vector_range (le,e1,e2) -> re (LEXP_vector_range (s_lexp le, s_exp e1, s_exp e2))
      | LEXP_field (le,id) -> re (LEXP_field (s_lexp le, id))
  in (s_pat,s_exp)
let nexp_subst_pat substs = fst (nexp_subst_fns substs)
let nexp_subst_exp substs = snd (nexp_subst_fns substs)

let bindings_from_pat p =
  let rec aux_pat (P_aux (p,(l,annot))) =
    let env = Type_check.env_of_annot (l, annot) in
    match p with
    | P_lit _
    | P_wild
      -> []
    | P_as (p,id) -> id::(aux_pat p)
    | P_typ (_,p) -> aux_pat p
    | P_id id ->
       if pat_id_is_variable env id then [id] else []
    | P_var (p,kid) -> aux_pat p
    | P_vector ps
    | P_vector_concat ps
    | P_app (_,ps)
    | P_tup ps
    | P_list ps
      -> List.concat (List.map aux_pat ps)
    | P_record (fps,_) -> List.concat (List.map aux_fpat fps)
    | P_cons (p1,p2) -> aux_pat p1 @ aux_pat p2
  and aux_fpat (FP_aux (FP_Fpat (_,p), _)) = aux_pat p
  in aux_pat p

let remove_bound env pat =
  let bound = bindings_from_pat pat in
  List.fold_left (fun sub v -> Bindings.remove v sub) env bound

(* Attempt simple pattern matches *)
let lit_match = function
  | (L_zero | L_false), (L_zero | L_false) -> true
  | (L_one  | L_true ), (L_one  | L_true ) -> true
  | L_num i1, L_num i2 -> Big_int.equal i1 i2
  | l1,l2 -> l1 = l2

(* There's no undefined nexp, so replace undefined sizes with a plausible size.
   32 is used as a sensible default. *)

let fabricate_nexp_exist env l typ kids nc typ' =
  match kids,nc,Env.expand_synonyms env typ' with
  | ([kid],NC_aux (NC_set (kid',i::_),_),
     Typ_aux (Typ_app (Id_aux (Id "atom",_),
                       [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid'',_)),_)]),_))
      when Kid.compare kid kid' = 0 && Kid.compare kid kid'' = 0 ->
     Nexp_aux (Nexp_constant i,Unknown)
  | ([kid],NC_aux (NC_true,_),
     Typ_aux (Typ_app (Id_aux (Id "atom",_),
                       [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid'',_)),_)]),_))
      when Kid.compare kid kid'' = 0 ->
     nint 32
  | ([kid],NC_aux (NC_set (kid',i::_),_),
     Typ_aux (Typ_app (Id_aux (Id "range",_),
                       [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid'',_)),_);
                        Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid''',_)),_)]),_))
      when Kid.compare kid kid' = 0 && Kid.compare kid kid'' = 0 &&
        Kid.compare kid kid''' = 0 ->
     Nexp_aux (Nexp_constant i,Unknown)
  | ([kid],NC_aux (NC_true,_),
     Typ_aux (Typ_app (Id_aux (Id "range",_),
                       [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid'',_)),_);
                        Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid''',_)),_)]),_))
      when Kid.compare kid kid'' = 0 &&
        Kid.compare kid kid''' = 0 ->
     nint 32
  | _ -> raise (Reporting_basic.err_general l
                  ("Undefined value at unsupported type " ^ string_of_typ typ))

let fabricate_nexp l = function
  | None -> nint 32
  | Some (env,typ,_) ->
     match Type_check.destruct_exist env typ with
     | None -> nint 32
     | Some (kids,nc,typ') -> fabricate_nexp_exist env l typ kids nc typ'

let atom_typ_kid kid = function
  | Typ_aux (Typ_app (Id_aux (Id "atom",_),
                      [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid',_)),_)]),_) ->
     Kid.compare kid kid' = 0
  | _ -> false

(* We reduce casts in a few cases, in particular to ensure that where the
   type checker has added a ({'n, true. atom('n)}) ex_int(...) cast we can
   fill in the 'n.  For undefined we fabricate a suitable value for 'n. *)

let reduce_cast typ exp l annot =
  let env = env_of_annot (l,annot) in
  let replace_typ typ = function
    | Some (env,_,eff) -> Some (env,typ,eff)
    | None -> None
  in
  let typ' = Env.base_typ_of env typ in
  match exp, destruct_exist env typ' with
  | E_aux (E_lit (L_aux (L_num n,_)),_), Some ([kid],nc,typ'') when atom_typ_kid kid typ'' ->
     let nc_env = Env.add_typ_var kid BK_nat env in
     let nc_env = Env.add_constraint (nc_eq (nvar kid) (nconstant n)) nc_env in
     if prove nc_env nc
     then exp
     else raise (Reporting_basic.err_unreachable l
                   ("Constant propagation error: literal " ^ Big_int.to_string n ^
                       " does not satisfy constraint " ^ string_of_n_constraint nc))
  | E_aux (E_lit (L_aux (L_undef,_)),_), Some ([kid],nc,typ'') when atom_typ_kid kid typ'' ->
     let nexp = fabricate_nexp_exist env Unknown typ [kid] nc typ'' in
     let newtyp = subst_src_typ (KBindings.singleton kid nexp) typ'' in
     E_aux (E_cast (newtyp, exp), (Generated l,replace_typ newtyp annot))
  | E_aux (E_cast (_,
                   (E_aux (E_lit (L_aux (L_undef,_)),_) as exp)),_),
     Some ([kid],nc,typ'') when atom_typ_kid kid typ'' ->
     let nexp = fabricate_nexp_exist env Unknown typ [kid] nc typ'' in
     let newtyp = subst_src_typ (KBindings.singleton kid nexp) typ'' in
     E_aux (E_cast (newtyp, exp), (Generated l,replace_typ newtyp annot))
  | _ -> E_aux (E_cast (typ,exp),(l,annot))

(* Used for constant propagation in pattern matches *)
type 'a matchresult =
  | DoesMatch of 'a
  | DoesNotMatch
  | GiveUp

(* Remove top-level casts from an expression.  Useful when we need to look at
   subexpressions to reduce something, but could break type-checking if we used
   it everywhere. *)
let rec drop_casts = function
  | E_aux (E_cast (_,e),_) -> drop_casts e
  | exp -> exp

let int_of_str_lit = function
  | L_hex hex -> Big_int.of_string ("0x" ^ hex)
  | L_bin bin -> Big_int.of_string ("0b" ^ bin)
  | _ -> assert false

let lit_eq (L_aux (l1,_)) (L_aux (l2,_)) =
  match l1,l2 with
  | (L_zero|L_false), (L_zero|L_false)
  | (L_one |L_true ), (L_one |L_true)
    -> Some true
  | (L_hex _| L_bin _), (L_hex _|L_bin _)
    -> Some (Big_int.equal (int_of_str_lit l1) (int_of_str_lit l2))
  | L_undef, _ | _, L_undef -> None
  | L_num i1, L_num i2 -> Some (Big_int.equal i1 i2)
  | _ -> Some (l1 = l2)

let try_app (l,ann) (id,args) =
  let new_l = Generated l in
  let env = env_of_annot (l,ann) in
  let get_overloads f = List.map string_of_id
    (Env.get_overloads (Id_aux (Id f, Parse_ast.Unknown)) env @
    Env.get_overloads (Id_aux (DeIid f, Parse_ast.Unknown)) env) in
  let is_id f = List.mem (string_of_id id) (f :: get_overloads f) in
  if is_id "==" || is_id "!=" then
    match args with
    | [E_aux (E_lit l1,_); E_aux (E_lit l2,_)] ->
       let lit b = if b then L_true else L_false in
       let lit b = lit (if is_id "==" then b else not b) in
       (match lit_eq l1 l2 with
       | None -> None
       | Some b -> Some (E_aux (E_lit (L_aux (lit b,new_l)),(l,ann))))
    | _ -> None
  else if is_id "cast_bit_bool" then
    match args with
    | [E_aux (E_lit L_aux (L_zero,_),_)] -> Some (E_aux (E_lit (L_aux (L_false,new_l)),(l,ann)))
    | [E_aux (E_lit L_aux (L_one ,_),_)] -> Some (E_aux (E_lit (L_aux (L_true ,new_l)),(l,ann)))
    | _ -> None
  else if is_id "UInt" then
    match args with
    | [E_aux (E_lit L_aux ((L_hex _| L_bin _) as lit,_), _)] ->
       Some (E_aux (E_lit (L_aux (L_num (int_of_str_lit lit),new_l)),(l,ann)))
    | _ -> None
  else if is_id "shl_int" then
    match args with
    | [E_aux (E_lit L_aux (L_num i,_),_); E_aux (E_lit L_aux (L_num j,_),_)] ->
       Some (E_aux (E_lit (L_aux (L_num (Big_int.shift_left i (Big_int.to_int j)),new_l)),(l,ann)))
    | _ -> None
  else if is_id "mult_int" then
    match args with
    | [E_aux (E_lit L_aux (L_num i,_),_); E_aux (E_lit L_aux (L_num j,_),_)] ->
       Some (E_aux (E_lit (L_aux (L_num (Big_int.mul i j),new_l)),(l,ann)))
    | _ -> None
  else if is_id "ex_int" then
    match args with
    | [E_aux (E_lit lit,(l,_))] -> Some (E_aux (E_lit lit,(l,ann)))
    | [E_aux (E_cast (_,(E_aux (E_lit (L_aux (L_undef,_)),_) as e)),(l,_))] ->
       Some (reduce_cast (typ_of_annot (l,ann)) e l ann)
    | _ -> None
  else if is_id "vector_access" || is_id "bitvector_access" then
    match args with
    | [E_aux (E_lit L_aux ((L_hex _ | L_bin _) as lit,_),_);
       E_aux (E_lit L_aux (L_num i,_),_)] ->
       let v = int_of_str_lit lit in
       let b = Big_int.bitwise_and (Big_int.shift_right v (Big_int.to_int i)) (Big_int.of_int 1) in
       let lit' = if Big_int.equal b (Big_int.of_int 1) then L_one else L_zero in
       Some (E_aux (E_lit (L_aux (lit',new_l)),(l,ann)))
    | _ -> None
  else None


let construct_lit_vector args =
  let rec aux l = function
    | [] -> Some (L_aux (L_bin (String.concat "" (List.rev l)),Unknown))
    | E_aux (E_lit (L_aux ((L_zero | L_one) as lit,_)),_)::t ->
       aux ((if lit = L_zero then "0" else "1")::l) t
    | _ -> None
  in aux [] args

(* We may need to split up a pattern match if (1) we've been told to case split
   on a variable by the user or analysis, or (2) we monomorphised a constructor that's used
   in the pattern. *)
type split =
  | NoSplit
  | VarSplit of (tannot pat *                    (* pattern for this case *)
                   (id * tannot Ast.exp) list *  (* substitutions for arguments *)
                   (Parse_ast.l * int) list)     (* optional locations of case expressions to reduce *)
      list
  | ConstrSplit of (tannot pat * nexp KBindings.t) list

let threaded_map f state l =
  let l',state' =
    List.fold_left (fun (tl,state) element -> let (el',state') = f state element in (el'::tl,state'))
      ([],state) l
  in List.rev l',state'

let isubst_minus subst subst' =
  Bindings.merge (fun _ x y -> match x,y with (Some a), None -> Some a | _, _ -> None) subst subst'

let isubst_minus_set subst set =
  IdSet.fold Bindings.remove set subst

let assigned_vars exp =
  fst (Rewriter.fold_exp
         { (Rewriter.compute_exp_alg IdSet.empty IdSet.union) with
           Rewriter.lEXP_id = (fun id -> IdSet.singleton id, LEXP_id id);
           Rewriter.lEXP_cast = (fun (ty,id) -> IdSet.singleton id, LEXP_cast (ty,id)) }
         exp)

let assigned_vars_in_fexps (FES_aux (FES_Fexps (fes,_), _)) =
  List.fold_left
    (fun vs (FE_aux (FE_Fexp (_,e),_)) -> IdSet.union vs (assigned_vars e))
    IdSet.empty
    fes

let assigned_vars_in_pexp (Pat_aux (p,_)) =
  match p with
  | Pat_exp (_,e) -> assigned_vars e
  | Pat_when (p,e1,e2) -> IdSet.union (assigned_vars e1) (assigned_vars e2)

let rec assigned_vars_in_lexp (LEXP_aux (le,_)) =
  match le with
  | LEXP_id id
  | LEXP_cast (_,id) -> IdSet.singleton id
  | LEXP_tup lexps -> List.fold_left (fun vs le -> IdSet.union vs (assigned_vars_in_lexp le)) IdSet.empty lexps
  | LEXP_memory (_,es) -> List.fold_left (fun vs e -> IdSet.union vs (assigned_vars e)) IdSet.empty es
  | LEXP_vector (le,e) -> IdSet.union (assigned_vars_in_lexp le) (assigned_vars e)
  | LEXP_vector_range (le,e1,e2) ->
     IdSet.union (assigned_vars_in_lexp le) (IdSet.union (assigned_vars e1) (assigned_vars e2))
  | LEXP_field (le,_) -> assigned_vars_in_lexp le

(* Add a cast to undefined so that it retains its type, otherwise it can't be
   substituted safely *)
let keep_undef_typ value =
  match value with
  | E_aux (E_lit (L_aux (L_undef,lann)),eann) ->
     E_aux (E_cast (typ_of_annot eann,value),(Generated Unknown,snd eann))
  | _ -> value

let rec remove_pat_bindings p =
  let rec aux (P_aux (p,(l,annot)) as pat) =
    let mkp p = P_aux (p,(Generated l, annot)) in
    match p with
    | P_lit _
    | P_wild -> pat
    | P_as (p,_) -> aux p
    | P_typ (typ,p) -> mkp (P_typ (typ,aux p))
    | P_id id -> mkp P_wild
    | P_var (p,_) -> aux p
    | P_app (id,args) -> mkp (P_app (id,List.map aux args))
    | P_record (fpats,flag) -> mkp (P_record (List.map auxr fpats,flag))
    | P_vector ps -> mkp (P_vector (List.map aux ps))
    | P_vector_concat ps -> mkp (P_vector_concat (List.map aux ps))
    | P_tup ps -> mkp (P_tup (List.map aux ps))
    | P_list ps -> mkp (P_list (List.map aux ps))
    | P_cons (p1,p2) -> mkp (P_cons (aux p1, aux p2))
  and auxr (FP_aux (FP_Fpat (id,p),(l,annot))) =
    FP_aux (FP_Fpat (id, aux p),(Generated l,annot))
  in aux p

(* Use the location pairs in choices to reduce case expressions at the first
   location to the given case at the second. *)
(* TODO bound variables! *)
let apply_pat_choices choices =
  let rewrite_case (e,cases) =
    match List.assoc (exp_loc e) choices with
    | choice ->
       (match List.nth cases choice with
       | Pat_aux (Pat_exp (p,E_aux (e,_)),_) -> e
       | Pat_aux (Pat_when _,(l,_)) ->
          raise (Reporting_basic.err_unreachable l
                   "Pattern acquired a guard after analysis!")
       | exception Not_found ->
          raise (Reporting_basic.err_unreachable (exp_loc e)
                   "Unable to find case I found earlier!"))
    | exception Not_found -> E_case (e,cases)
  in
  let open Rewriter in
  fold_exp { id_exp_alg with e_case = rewrite_case }

let split_defs continue_anyway splits defs =
  let split_constructors (Defs defs) =
    let sc_type_union q (Tu_aux (tu,l) as tua) =
      match tu with
      | Tu_id id -> [],[tua]
      | Tu_ty_id (ty,id) ->
         (match split_src_type id ty q with
         | None -> ([],[Tu_aux (Tu_ty_id (ty,id),l)])
         | Some variants ->
            ([(id,variants)],
             List.map (fun (insts, id', ty) -> Tu_aux (Tu_ty_id (ty,id'),Generated l)) variants))
    in
    let sc_type_def ((TD_aux (tda,annot)) as td) =
      match tda with
      | TD_variant (id,nscm,quant,tus,flag) ->
         let (refinements, tus') = List.split (List.map (sc_type_union quant) tus) in
         (List.concat refinements, TD_aux (TD_variant (id,nscm,quant,List.concat tus',flag),annot))
      | _ -> ([],td)
    in
    let sc_def d =
      match d with
    | DEF_type td -> let (refinements,td') = sc_type_def td in (refinements, DEF_type td')
    | _ -> ([], d)
    in
    let (refinements, defs') = List.split (List.map sc_def defs)
    in (List.concat refinements, Defs defs')
  in

  let (refinements, defs') = split_constructors defs in

  (* Constant propogation.
     Takes maps of immutable/mutable variables to subsitute.
     Extremely conservative about evaluation order of assignments in
     subexpressions, dropping assignments rather than committing to
     any particular order *)
  let rec const_prop_exp substs assigns ((E_aux (e,(l,annot))) as exp) =
    (* Functions to treat lists and tuples of subexpressions as possibly
       non-deterministic: that is, we stop making any assumptions about
       variables that are assigned to in any of the subexpressions *)
    let non_det_exp_list es =
      let assigned_in =
        List.fold_left (fun vs exp -> IdSet.union vs (assigned_vars exp))
          IdSet.empty es in
      let assigns = isubst_minus_set assigns assigned_in in
      let es' = List.map (fun e -> fst (const_prop_exp substs assigns e)) es in
      es',assigns
    in
    let non_det_exp_2 e1 e2 =
       let assigned_in_e12 = IdSet.union (assigned_vars e1) (assigned_vars e2) in
       let assigns = isubst_minus_set assigns assigned_in_e12 in
       let e1',_ = const_prop_exp substs assigns e1 in
       let e2',_ = const_prop_exp substs assigns e2 in
       e1',e2',assigns
    in
    let non_det_exp_3 e1 e2 e3 =
       let assigned_in_e12 = IdSet.union (assigned_vars e1) (assigned_vars e2) in
       let assigned_in_e123 = IdSet.union assigned_in_e12 (assigned_vars e3) in
       let assigns = isubst_minus_set assigns assigned_in_e123 in
       let e1',_ = const_prop_exp substs assigns e1 in
       let e2',_ = const_prop_exp substs assigns e2 in
       let e3',_ = const_prop_exp substs assigns e3 in
       e1',e2',e3',assigns
    in
    let non_det_exp_4 e1 e2 e3 e4 =
       let assigned_in_e12 = IdSet.union (assigned_vars e1) (assigned_vars e2) in
       let assigned_in_e123 = IdSet.union assigned_in_e12 (assigned_vars e3) in
       let assigned_in_e1234 = IdSet.union assigned_in_e123 (assigned_vars e4) in
       let assigns = isubst_minus_set assigns assigned_in_e1234 in
       let e1',_ = const_prop_exp substs assigns e1 in
       let e2',_ = const_prop_exp substs assigns e2 in
       let e3',_ = const_prop_exp substs assigns e3 in
       let e4',_ = const_prop_exp substs assigns e4 in
       e1',e2',e3',e4',assigns
    in
    let re e assigns = E_aux (e,(l,annot)),assigns in
    match e with
      (* TODO: are there more circumstances in which we should get rid of these? *)
    | E_block [e] -> const_prop_exp substs assigns e
    | E_block es ->
       let es',assigns = threaded_map (const_prop_exp substs) assigns es in
       re (E_block es') assigns
    | E_nondet es ->
       let es',assigns = non_det_exp_list es in
       re (E_nondet es') assigns
    | E_id id ->
       let env = Type_check.env_of_annot (l, annot) in
       (try
         match Env.lookup_id id env with
         | Local (Immutable,_) -> Bindings.find id substs
         | Local (Mutable,_)   -> Bindings.find id assigns
         | _ -> exp
       with Not_found -> exp),assigns
    | E_lit _
    | E_sizeof _
    | E_internal_exp _
    | E_sizeof_internal _
    | E_internal_exp_user _
    | E_comment _
    | E_constraint _
      -> exp,assigns
    | E_cast (t,e') ->
       let e'',assigns = const_prop_exp substs assigns e' in
       if is_value e''
       then reduce_cast t e'' l annot, assigns
       else re (E_cast (t, e'')) assigns
    | E_app (id,es) ->
       let es',assigns = non_det_exp_list es in
       let env = Type_check.env_of_annot (l, annot) in
       (match try_app (l,annot) (id,es') with
       | None ->
          (match const_prop_try_fn l env (id,es') with
          | None -> re (E_app (id,es')) assigns
          | Some r -> r,assigns)
       | Some r -> r,assigns)
    | E_tuple es ->
       let es',assigns = non_det_exp_list es in
       re (E_tuple es') assigns
    | E_if (e1,e2,e3) ->
       let e1',assigns = const_prop_exp substs assigns e1 in
       let e2',assigns2 = const_prop_exp substs assigns e2 in
       let e3',assigns3 = const_prop_exp substs assigns e3 in
       (match drop_casts e1' with
       | E_aux (E_lit (L_aux ((L_true|L_false) as lit ,_)),_) ->
          (match lit with L_true -> e2',assigns2 | _ -> e3',assigns3)
       | _ ->
          let assigns = isubst_minus_set assigns (assigned_vars e2) in
          let assigns = isubst_minus_set assigns (assigned_vars e3) in
          re (E_if (e1',e2',e3')) assigns)
    | E_for (id,e1,e2,e3,ord,e4) ->
       (* Treat e1, e2 and e3 (from, to and by) as a non-det tuple *)
       let e1',e2',e3',assigns = non_det_exp_3 e1 e2 e3 in
       let assigns = isubst_minus_set assigns (assigned_vars e4) in
       let e4',_ = const_prop_exp (Bindings.remove id substs) assigns e4 in
       re (E_for (id,e1',e2',e3',ord,e4')) assigns
    | E_loop (loop,e1,e2) ->
       let assigns = isubst_minus_set assigns (IdSet.union (assigned_vars e1) (assigned_vars e2)) in
       let e1',_ = const_prop_exp substs assigns e1 in
       let e2',_ = const_prop_exp substs assigns e2 in
       re (E_loop (loop,e1',e2')) assigns
    | E_vector es ->
       let es',assigns = non_det_exp_list es in
       begin
         match construct_lit_vector es' with
         | None -> re (E_vector es') assigns
         | Some lit -> re (E_lit lit) assigns
       end
    | E_vector_access (e1,e2) ->
       let e1',e2',assigns = non_det_exp_2 e1 e2 in
       re (E_vector_access (e1',e2')) assigns
    | E_vector_subrange (e1,e2,e3) ->
       let e1',e2',e3',assigns = non_det_exp_3 e1 e2 e3 in
       re (E_vector_subrange (e1',e2',e3')) assigns
    | E_vector_update (e1,e2,e3) ->
       let e1',e2',e3',assigns = non_det_exp_3 e1 e2 e3 in
       re (E_vector_update (e1',e2',e3')) assigns
    | E_vector_update_subrange (e1,e2,e3,e4) ->
       let e1',e2',e3',e4',assigns = non_det_exp_4 e1 e2 e3 e4 in
       re (E_vector_update_subrange (e1',e2',e3',e4')) assigns
    | E_vector_append (e1,e2) ->
       let e1',e2',assigns = non_det_exp_2 e1 e2 in
       re (E_vector_append (e1',e2')) assigns
    | E_list es ->
       let es',assigns = non_det_exp_list es in
       re (E_list es') assigns
    | E_cons (e1,e2) ->
       let e1',e2',assigns = non_det_exp_2 e1 e2 in
       re (E_cons (e1',e2')) assigns
    | E_record fes ->
       let assigned_in_fes = assigned_vars_in_fexps fes in
       let assigns = isubst_minus_set assigns assigned_in_fes in
       re (E_record (const_prop_fexps substs assigns fes)) assigns
    | E_record_update (e,fes) ->
       let assigned_in = IdSet.union (assigned_vars_in_fexps fes) (assigned_vars e) in
       let assigns = isubst_minus_set assigns assigned_in in
       let e',_ = const_prop_exp substs assigns e in
       re (E_record_update (e', const_prop_fexps substs assigns fes)) assigns
    | E_field (e,id) ->
       let e',assigns = const_prop_exp substs assigns e in
       re (E_field (e',id)) assigns
    | E_case (e,cases) ->
       let e',assigns = const_prop_exp substs assigns e in
       (match can_match e' cases substs assigns with
       | None ->
          let assigned_in =
            List.fold_left (fun vs pe -> IdSet.union vs (assigned_vars_in_pexp pe))
              IdSet.empty cases
          in
          let assigns' = isubst_minus_set assigns assigned_in in
          re (E_case (e', List.map (const_prop_pexp substs assigns) cases)) assigns'
       | Some (E_aux (_,(_,annot')) as exp,newbindings,kbindings) ->
          let exp = nexp_subst_exp (kbindings_from_list kbindings) exp in
          let newbindings_env = bindings_from_list newbindings in
          let substs' = bindings_union substs newbindings_env in
          const_prop_exp substs' assigns exp)
    | E_let (lb,e2) ->
       begin
         match lb with
         | LB_aux (LB_val (p,e), annot) ->
            let e',assigns = const_prop_exp substs assigns e in
            let substs' = remove_bound substs p in
            let plain () =
              let e2',assigns = const_prop_exp substs' assigns e2 in
              re (E_let (LB_aux (LB_val (p,e'), annot),
                         e2')) assigns in
            if is_value e' && not (is_value e) then
              match can_match e' [Pat_aux (Pat_exp (p,e2),(Unknown,None))] substs assigns with
              | None -> plain ()
              | Some (e'',bindings,kbindings) ->
                 let e'' = nexp_subst_exp (kbindings_from_list kbindings) e'' in
                 let bindings = bindings_from_list bindings in
                 let substs'' = bindings_union substs' bindings in
                 const_prop_exp substs'' assigns e''
            else plain ()
       end
    (* TODO maybe - tuple assignments *)
    | E_assign (le,e) ->
       let env = Type_check.env_of_annot (l, annot) in
       let assigned_in = IdSet.union (assigned_vars_in_lexp le) (assigned_vars e) in
       let assigns = isubst_minus_set assigns assigned_in in
       let le',idopt = const_prop_lexp substs assigns le in
       let e',_ = const_prop_exp substs assigns e in
       let assigns =
         match idopt with
         | Some id ->
            begin
              match Env.lookup_id id env with
              | Local (Mutable,_) | Unbound ->
                 if is_value e'
                 then Bindings.add id (keep_undef_typ e') assigns
                 else Bindings.remove id assigns
              | _ -> assigns
            end
         | None -> assigns
       in
       re (E_assign (le', e')) assigns
    | E_exit e ->
       let e',_ = const_prop_exp substs assigns e in
       re (E_exit e') Bindings.empty
    | E_throw e ->
       let e',_ = const_prop_exp substs assigns e in
       re (E_throw e') Bindings.empty
    | E_try (e,cases) ->
       (* TODO: try and preserve *any* assignment info *)
       let e',_ = const_prop_exp substs assigns e in
       re (E_case (e', List.map (const_prop_pexp substs Bindings.empty) cases)) Bindings.empty
    | E_return e ->
       let e',_ = const_prop_exp substs assigns e in
       re (E_return e') Bindings.empty
    | E_assert (e1,e2) ->
       let e1',e2',assigns = non_det_exp_2 e1 e2 in
       re (E_assert (e1',e2')) assigns
    | E_internal_cast (ann,e) ->
       let e',assigns = const_prop_exp substs assigns e in
       re (E_internal_cast (ann,e')) assigns
    (* TODO: should I substitute or anything here?  Is it even used? *)
    | E_comment_struc e -> re (E_comment_struc e) assigns

    | E_app_infix _
    | E_var _
    | E_internal_plet _
    | E_internal_return _
      -> raise (Reporting_basic.err_unreachable l
                  ("Unexpected expression encountered in monomorphisation: " ^ string_of_exp exp))
  and const_prop_fexps substs assigns (FES_aux (FES_Fexps (fes,flag), annot)) =
    FES_aux (FES_Fexps (List.map (const_prop_fexp substs assigns) fes, flag), annot)
  and const_prop_fexp substs assigns (FE_aux (FE_Fexp (id,e), annot)) =
    FE_aux (FE_Fexp (id,fst (const_prop_exp substs assigns e)),annot)
  and const_prop_pexp substs assigns = function
    | (Pat_aux (Pat_exp (p,e),l)) ->
       Pat_aux (Pat_exp (p,fst (const_prop_exp (remove_bound substs p) assigns e)),l)
    | (Pat_aux (Pat_when (p,e1,e2),l)) ->
       let substs' = remove_bound substs p in
       let e1',assigns = const_prop_exp substs' assigns e1 in
       Pat_aux (Pat_when (p, e1', fst (const_prop_exp substs' assigns e2)),l)
  and const_prop_lexp substs assigns ((LEXP_aux (e,annot)) as le) =
    let re e = LEXP_aux (e,annot), None in
    match e with
    | LEXP_id id (* shouldn't end up substituting here *)
    | LEXP_cast (_,id)
      -> le, Some id
    | LEXP_memory (id,es) ->
       re (LEXP_memory (id,List.map (fun e -> fst (const_prop_exp substs assigns e)) es)) (* or here *)
    | LEXP_tup les -> re (LEXP_tup (List.map (fun le -> fst (const_prop_lexp substs assigns le)) les))
    | LEXP_vector (le,e) -> re (LEXP_vector (fst (const_prop_lexp substs assigns le), fst (const_prop_exp substs assigns e)))
    | LEXP_vector_range (le,e1,e2) ->
       re (LEXP_vector_range (fst (const_prop_lexp substs assigns le),
                              fst (const_prop_exp substs assigns e1),
                              fst (const_prop_exp substs assigns e2)))
    | LEXP_field (le,id) -> re (LEXP_field (fst (const_prop_lexp substs assigns le), id))
  (* Reduce a function when
     1. all arguments are values,
     2. the function is pure,
     3. the result is a value
     (and 4. the function is not scattered, but that's not terribly important)
     to try and keep execution time and the results managable.
  *)
  and const_prop_try_fn l env (id,args) =
    if not (List.for_all is_value args) then
      None
    else
      let Defs ds = defs in
      match list_extract (function
      | (DEF_fundef (FD_aux (FD_function (_,_,eff,((FCL_aux (FCL_Funcl (id',_),_))::_ as fcls)),_)))
        -> if Id.compare id id' = 0 then Some (eff,fcls) else None
      | _ -> None) ds with
      | None -> None
      | Some (eff,_) when not (is_pure eff) -> None
      | Some (_,fcls) ->
         let arg = match args with
           | [] -> E_aux (E_lit (L_aux (L_unit,Generated l)),(Generated l,None))
           | [e] -> e
           | _ -> E_aux (E_tuple args,(Generated l,None)) in
         let cases = List.map (function
           | FCL_aux (FCL_Funcl (_,pexp), ann) -> pexp)
           fcls in
         match can_match_with_env env arg cases Bindings.empty Bindings.empty with
         | Some (exp,bindings,kbindings) ->
            let substs = bindings_from_list bindings in
            let result,_ = const_prop_exp substs Bindings.empty exp in
            if is_value result then Some result else None
         | None -> None

  and can_match_with_env env (E_aux (e,(l,annot)) as exp0) cases substs assigns =
    let rec findpat_generic check_pat description assigns = function
      | [] -> (Reporting_basic.print_err false true l "Monomorphisation"
                 ("Failed to find a case for " ^ description); None)
      | [Pat_aux (Pat_exp (P_aux (P_wild,_),exp),_)] -> Some (exp,[],[])
      | (Pat_aux (Pat_exp (P_aux (P_typ (_,p),_),exp),ann))::tl ->
         findpat_generic check_pat description assigns ((Pat_aux (Pat_exp (p,exp),ann))::tl)
      | (Pat_aux (Pat_exp (P_aux (P_id id',_),exp),_))::tlx
          when pat_id_is_variable env id' ->
         Some (exp, [(id', exp0)], [])
      | (Pat_aux (Pat_when (P_aux (P_id id',_),guard,exp),_))::tl
          when pat_id_is_variable env id' -> begin
            let substs = Bindings.add id' exp0 substs in
            let (E_aux (guard,_)),assigns = const_prop_exp substs assigns guard in
            match guard with
            | E_lit (L_aux (L_true,_)) -> Some (exp,[(id',exp0)],[])
            | E_lit (L_aux (L_false,_)) -> findpat_generic check_pat description assigns tl
            | _ -> None
          end
      | (Pat_aux (Pat_when (p,guard,exp),_))::tl -> begin
        match check_pat p with
        | DoesNotMatch -> findpat_generic check_pat description assigns tl
        | DoesMatch (vsubst,ksubst) -> begin
          let guard = nexp_subst_exp (kbindings_from_list ksubst) guard in
          let substs = bindings_union substs (bindings_from_list vsubst) in
          let (E_aux (guard,_)),assigns = const_prop_exp substs assigns guard in
          match guard with
          | E_lit (L_aux (L_true,_)) -> Some (exp,vsubst,ksubst)
          | E_lit (L_aux (L_false,_)) -> findpat_generic check_pat description assigns tl
          | _ -> None
        end
        | GiveUp -> None
      end
      | (Pat_aux (Pat_exp (p,exp),_))::tl ->
         match check_pat p with
         | DoesNotMatch -> findpat_generic check_pat description assigns tl
         | DoesMatch (subst,ksubst) -> Some (exp,subst,ksubst)
         | GiveUp -> None
    in
    match e with
    | E_id id ->
       (match Env.lookup_id id env with
       | Enum _ ->
          let checkpat = function
            | P_aux (P_id id',_)
            | P_aux (P_app (id',[]),_) ->
               if Id.compare id id' = 0 then DoesMatch ([],[]) else DoesNotMatch
            | P_aux (_,(l',_)) ->
               (Reporting_basic.print_err false true l' "Monomorphisation"
                  "Unexpected kind of pattern for enumeration"; GiveUp)
          in findpat_generic checkpat (string_of_id id) assigns cases
       | _ -> None)
    | E_lit (L_aux (lit_e, lit_l)) ->
       let checkpat = function
         | P_aux (P_lit (L_aux (lit_p, _)),_) ->
            if lit_match (lit_e,lit_p) then DoesMatch ([],[]) else DoesNotMatch
         | P_aux (P_var (P_aux (P_id id,p_id_annot), kid),_) ->
            begin
              match lit_e with
              | L_num i ->
                 DoesMatch ([id, E_aux (e,(l,annot))],
                            [kid,Nexp_aux (Nexp_constant i,Unknown)])
              (* For undefined we fix the type-level size (because there's no good
                 way to construct an undefined size), but leave the term as undefined
                 to make the meaning clear. *)
              | L_undef ->
                 let nexp = fabricate_nexp l annot in
                 let typ = subst_src_typ (KBindings.singleton kid nexp) (typ_of_annot p_id_annot) in
                 DoesMatch ([id, E_aux (E_cast (typ,E_aux (e,(l,None))),(l,None))],
                            [kid,nexp])
              | _ ->
                 (Reporting_basic.print_err false true lit_l "Monomorphisation"
                    "Unexpected kind of literal for var match"; GiveUp)
            end
         | P_aux (_,(l',_)) ->
            (Reporting_basic.print_err false true l' "Monomorphisation"
               "Unexpected kind of pattern for literal"; GiveUp)
       in findpat_generic checkpat "literal" assigns cases
    | E_cast (undef_typ, (E_aux (E_lit (L_aux (L_undef, lit_l)),_) as e_undef)) ->
       let checkpat = function
         | P_aux (P_lit (L_aux (lit_p, _)),_) -> DoesNotMatch
         | P_aux (P_var (P_aux (P_id id,p_id_annot), kid),_) ->
              (* For undefined we fix the type-level size (because there's no good
                 way to construct an undefined size), but leave the term as undefined
                 to make the meaning clear. *)
            let nexp = fabricate_nexp l annot in
            let typ = subst_src_typ (KBindings.singleton kid nexp) (typ_of_annot p_id_annot) in
            DoesMatch ([id, E_aux (E_cast (typ,e_undef),(l,None))],
                       [kid,nexp])
         | P_aux (_,(l',_)) ->
            (Reporting_basic.print_err false true l' "Monomorphisation"
               "Unexpected kind of pattern for literal"; GiveUp)
       in findpat_generic checkpat "literal" assigns cases
    | _ -> None

  and can_match exp =
    let env = Type_check.env_of exp in
    can_match_with_env env exp
  in

  let subst_exp substs exp =
    let substs = bindings_from_list substs in
    fst (const_prop_exp substs Bindings.empty exp)
  in
    
  (* Split a variable pattern into every possible value *)

  let split var pat_l annot =
    let v = string_of_id var in
    let env = Type_check.env_of_annot (pat_l, annot) in
    let typ = Type_check.typ_of_annot (pat_l, annot) in
    let typ = Env.expand_synonyms env typ in
    let Typ_aux (ty,l) = typ in
    let new_l = Generated l in
    let renew_id (Id_aux (id,l)) = Id_aux (id,new_l) in
    let cannot msg =
      let open Reporting_basic in
      let error =
        Err_general (pat_l,
                     ("Cannot split type " ^ string_of_typ typ ^ " for variable " ^ v ^ ": " ^ msg))
      in if continue_anyway
        then (print_error error; [P_aux (P_id var,(pat_l,annot)),[],[]])
        else raise (Fatal_error error)
    in
    match ty with
    | Typ_id (Id_aux (Id "bool",_)) ->
       [P_aux (P_lit (L_aux (L_true,new_l)),(l,annot)),[var, E_aux (E_lit (L_aux (L_true,new_l)),(new_l,annot))],[];
        P_aux (P_lit (L_aux (L_false,new_l)),(l,annot)),[var, E_aux (E_lit (L_aux (L_false,new_l)),(new_l,annot))],[]]

    | Typ_id id ->
       (try
         (* enumerations *)
         let ns = Env.get_enum id env in
         List.map (fun n -> (P_aux (P_id (renew_id n),(l,annot)),
                             [var,E_aux (E_id (renew_id n),(new_l,annot))],[])) ns
       with Type_error _ ->
         match id with
         | Id_aux (Id "bit",_) ->
            List.map (fun b ->
              P_aux (P_lit (L_aux (b,new_l)),(l,annot)),
              [var,E_aux (E_lit (L_aux (b,new_l)),(new_l, annot))],[])
              [L_zero; L_one]
         | _ -> cannot ("don't know about type " ^ string_of_id id))

    | Typ_app (Id_aux (Id "vector",_), [Typ_arg_aux (Typ_arg_nexp len,_);_;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]) ->
       (match len with
       | Nexp_aux (Nexp_constant sz,_) ->
          let lits = make_vectors (Big_int.to_int sz) in
          List.map (fun lit ->
            P_aux (P_lit lit,(l,annot)),
            [var,E_aux (E_lit lit,(new_l,annot))],[]) lits
       | _ ->
          cannot ("length not constant, " ^ string_of_nexp len)
       )
    (* set constrained numbers *)
    | Typ_app (Id_aux (Id "atom",_), [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (value,_) as nexp),_)]) ->
       begin
         let mk_lit i =
            let lit = L_aux (L_num i,new_l) in
            P_aux (P_lit lit,(l,annot)),
            [var,E_aux (E_lit lit,(new_l,annot))],[]
         in
         match value with
         | Nexp_constant i -> [mk_lit i]
         | Nexp_var kvar ->
           let ncs = Env.get_constraints env in
           let nc = List.fold_left nc_and nc_true ncs in
           (match extract_set_nc l kvar nc with
           | (is,_) -> List.map mk_lit is
           | exception Reporting_basic.Fatal_error (Reporting_basic.Err_general (_,msg)) -> cannot msg)
         | _ -> cannot ("unsupport atom nexp " ^ string_of_nexp nexp)
       end
    | _ -> cannot ("unsupported type " ^ string_of_typ typ)
  in
  

  (* Split variable patterns at the given locations *)

  let map_locs ls (Defs defs) =
    let rec match_l = function
      | Unknown
      | Int _ -> []
      | Generated l -> [] (* Could do match_l l, but only want to split user-written patterns *)
      | Range (p,q) ->
         let matches =
           List.filter (fun ((filename,line),_,_) ->
             p.Lexing.pos_fname = filename &&
               p.Lexing.pos_lnum <= line && line <= q.Lexing.pos_lnum) ls
         in List.map (fun (_,var,optpats) -> (var,optpats)) matches
    in 

    let split_pat vars p =
      let id_match = function
        | Id_aux (Id x,_) -> (try Some (List.assoc x vars) with Not_found -> None)
        | Id_aux (DeIid x,_) -> (try Some (List.assoc x vars) with Not_found -> None)
      in

      let rec list f = function
        | [] -> None
        | h::t ->
           let t' =
             match list f t with
             | None -> [t,[],[]]
             | Some t' -> t'
           in
           let h' =
             match f h with
             | None -> [h,[],[]]
             | Some ps -> ps
           in
           Some (List.concat
                   (List.map (fun (h,hsubs,hpchoices) ->
                     List.map (fun (t,tsubs,tpchoices) ->
                       (h::t, hsubs@tsubs, hpchoices@tpchoices)) t') h'))
      in
      let rec spl (P_aux (p,(l,annot))) =
        let relist f ctx ps =
          optmap (list f ps) 
            (fun ps ->
              List.map (fun (ps,sub,pchoices) -> P_aux (ctx ps,(l,annot)),sub,pchoices) ps)
        in
        let re f p =
          optmap (spl p)
            (fun ps -> List.map (fun (p,sub,pchoices) -> (P_aux (f p,(l,annot)), sub, pchoices)) ps)
        in
        let fpat (FP_aux ((FP_Fpat (id,p),annot))) =
          optmap (spl p)
            (fun ps -> List.map (fun (p,sub,pchoices) -> FP_aux (FP_Fpat (id,p), annot), sub, pchoices) ps)
        in
        match p with
        | P_lit _
        | P_wild
        | P_var _
          -> None
        | P_as (p',id) when id_match id <> None ->
           raise (Reporting_basic.err_general l
                    ("Cannot split " ^ string_of_id id ^ " on 'as' pattern"))
        | P_as (p',id) ->
           re (fun p -> P_as (p,id)) p'
        | P_typ (t,p') -> re (fun p -> P_typ (t,p)) p'
        | P_id id ->
           (match id_match id with
           | None -> None
           | Some None -> Some (split id l annot)
           | Some (Some (pats,l)) ->
              Some (List.mapi (fun i p ->
                P_aux (P_as (remove_pat_bindings p,id),(l,annot)),[],[l,i])
                      pats)
           )
        | P_app (id,ps) ->
           relist spl (fun ps -> P_app (id,ps)) ps
        | P_record (fps,flag) ->
           relist fpat (fun fps -> P_record (fps,flag)) fps
        | P_vector ps ->
           relist spl (fun ps -> P_vector ps) ps
        | P_vector_concat ps ->
           relist spl (fun ps -> P_vector_concat ps) ps
        | P_tup ps ->
           relist spl (fun ps -> P_tup ps) ps
        | P_list ps ->
           relist spl (fun ps -> P_list ps) ps
        | P_cons (p1,p2) ->
           match spl p1, spl p2 with
           | None, None -> None
           | p1', p2' ->
              let p1' = match p1' with None -> [p1,[],[]] | Some p1' -> p1' in
              let p2' = match p2' with None -> [p2,[],[]] | Some p2' -> p2' in
              let ps = List.map (fun (p1',subs1,pchoices1) -> List.map (fun (p2',subs2,pchoices2) ->
                P_aux (P_cons (p1',p2'),(l,annot)),subs1@subs2,pchoices1@pchoices2) p2') p1' in
              Some (List.concat ps)
      in spl p
    in

    let map_pat_by_loc (P_aux (p,(l,_)) as pat) =
      match match_l l with
      | [] -> None
      | vars -> split_pat vars pat
    in
    let map_pat (P_aux (p,(l,tannot)) as pat) =
      match map_pat_by_loc pat with
      | Some l -> VarSplit l
      | None ->
         match p with
         | P_app (id,args) ->
            begin
              let kid,kid_annot =
                match args with
                | [P_aux (P_var (_,kid),ann)] -> kid,ann
                | _ -> 
                   raise (Reporting_basic.err_general l
                            "Pattern match not currently supported by monomorphisation")
              in match List.find (fun (id',_) -> Id.compare id id' = 0) refinements with
              | (_,variants) ->
                 let map_inst (insts,id',_) =
                   let insts =
                     match insts with [(v,Some i)] -> [(kid,Nexp_aux (Nexp_constant i, Generated l))]
                     | _ -> assert false
                   in
(*
                   let insts,_ = split_insts insts in
                   let insts = List.map (fun (v,i) ->
                     (??,
                      Nexp_aux (Nexp_constant i,Generated l)))
                     insts in
  P_aux (P_app (id',args),(Generated l,tannot)),
*)
                   P_aux (P_app (id',[P_aux (P_id (id_of_kid kid),kid_annot)]),(Generated l,tannot)),
                   kbindings_from_list insts
                 in
                 ConstrSplit (List.map map_inst variants)
              | exception Not_found -> NoSplit
            end
         | _ -> NoSplit
    in

    let check_single_pat (P_aux (_,(l,annot)) as p) =
      match match_l l with
      | [] -> p
      | lvs ->
         let pvs = bindings_from_pat p in
         let pvs = List.map string_of_id pvs in
         let overlap = List.exists (fun (v,_) -> List.mem v pvs) lvs in
         let () =
           if overlap then
             Reporting_basic.print_err false true l "Monomorphisation"
               "Splitting a singleton pattern is not possible"
         in p
    in

    let check_split_size lst l =
      let size = List.length lst in
      if size > size_set_limit then
        let open Reporting_basic in
        let error =
          Err_general (l, "Case split is too large (" ^ string_of_int size ^
            " > limit " ^ string_of_int size_set_limit ^ ")")
        in if continue_anyway
          then (print_error error; false)
          else raise (Fatal_error error)
      else true
    in

    let rec map_exp ((E_aux (e,annot)) as ea) =
      let re e = E_aux (e,annot) in
      match e with
      | E_block es -> re (E_block (List.map map_exp es))
      | E_nondet es -> re (E_nondet (List.map map_exp es))
      | E_id _
      | E_lit _
      | E_sizeof _
      | E_internal_exp _
      | E_sizeof_internal _
      | E_internal_exp_user _
      | E_comment _
      | E_constraint _
        -> ea
      | E_cast (t,e') -> re (E_cast (t, map_exp e'))
      | E_app (id,es) ->
         let es' = List.map map_exp es in
         let env = env_of_annot annot in
         begin
           match Env.is_union_constructor id env, refine_constructor refinements (fst annot) env id es' with
           | true, Some exp -> re exp
           | _,_ -> re (E_app (id,es'))
         end
      | E_app_infix (e1,id,e2) -> re (E_app_infix (map_exp e1,id,map_exp e2))
      | E_tuple es -> re (E_tuple (List.map map_exp es))
      | E_if (e1,e2,e3) -> re (E_if (map_exp e1, map_exp e2, map_exp e3))
      | E_for (id,e1,e2,e3,ord,e4) -> re (E_for (id,map_exp e1,map_exp e2,map_exp e3,ord,map_exp e4))
      | E_loop (loop,e1,e2) -> re (E_loop (loop,map_exp e1,map_exp e2))
      | E_vector es -> re (E_vector (List.map map_exp es))
      | E_vector_access (e1,e2) -> re (E_vector_access (map_exp e1,map_exp e2))
      | E_vector_subrange (e1,e2,e3) -> re (E_vector_subrange (map_exp e1,map_exp e2,map_exp e3))
      | E_vector_update (e1,e2,e3) -> re (E_vector_update (map_exp e1,map_exp e2,map_exp e3))
      | E_vector_update_subrange (e1,e2,e3,e4) -> re (E_vector_update_subrange (map_exp e1,map_exp e2,map_exp e3,map_exp e4))
      | E_vector_append (e1,e2) -> re (E_vector_append (map_exp e1,map_exp e2))
      | E_list es -> re (E_list (List.map map_exp es))
      | E_cons (e1,e2) -> re (E_cons (map_exp e1,map_exp e2))
      | E_record fes -> re (E_record (map_fexps fes))
      | E_record_update (e,fes) -> re (E_record_update (map_exp e, map_fexps fes))
      | E_field (e,id) -> re (E_field (map_exp e,id))
      | E_case (e,cases) -> re (E_case (map_exp e, List.concat (List.map map_pexp cases)))
      | E_let (lb,e) -> re (E_let (map_letbind lb, map_exp e))
      | E_assign (le,e) -> re (E_assign (map_lexp le, map_exp e))
      | E_exit e -> re (E_exit (map_exp e))
      | E_throw e -> re (E_throw e)
      | E_try (e,cases) -> re (E_try (map_exp e, List.concat (List.map map_pexp cases)))
      | E_return e -> re (E_return (map_exp e))
      | E_assert (e1,e2) -> re (E_assert (map_exp e1,map_exp e2))
      | E_internal_cast (ann,e) -> re (E_internal_cast (ann,map_exp e))
      | E_comment_struc e -> re (E_comment_struc e)
      | E_var (le,e1,e2) -> re (E_var (map_lexp le, map_exp e1, map_exp e2))
      | E_internal_plet (p,e1,e2) -> re (E_internal_plet (check_single_pat p, map_exp e1, map_exp e2))
      | E_internal_return e -> re (E_internal_return (map_exp e))
    and map_opt_default ((Def_val_aux (ed,annot)) as eda) =
      match ed with
      | Def_val_empty -> eda
      | Def_val_dec e -> Def_val_aux (Def_val_dec (map_exp e),annot)
    and map_fexps (FES_aux (FES_Fexps (fes,flag), annot)) =
      FES_aux (FES_Fexps (List.map map_fexp fes, flag), annot)
    and map_fexp (FE_aux (FE_Fexp (id,e), annot)) =
      FE_aux (FE_Fexp (id,map_exp e),annot)
    and map_pexp = function
      | Pat_aux (Pat_exp (p,e),l) ->
         let nosplit = [Pat_aux (Pat_exp (p,map_exp e),l)] in
         (match map_pat p with
         | NoSplit -> nosplit
         | VarSplit patsubsts ->
            if check_split_size patsubsts (pat_loc p) then
              List.map (fun (pat',substs,pchoices) ->
                let exp' = subst_exp substs e in
                let exp' = apply_pat_choices pchoices exp' in
                Pat_aux (Pat_exp (pat', map_exp exp'),l))
                patsubsts
            else nosplit
         | ConstrSplit patnsubsts ->
            List.map (fun (pat',nsubst) ->
              let pat' = nexp_subst_pat nsubst pat' in
              let exp' = nexp_subst_exp nsubst e in
              Pat_aux (Pat_exp (pat', map_exp exp'),l)
            ) patnsubsts)
      | Pat_aux (Pat_when (p,e1,e2),l) ->
         let nosplit = [Pat_aux (Pat_when (p,map_exp e1,map_exp e2),l)] in
         (match map_pat p with
         | NoSplit -> nosplit
         | VarSplit patsubsts ->
            if check_split_size patsubsts (pat_loc p) then
              List.map (fun (pat',substs,pchoices) ->
                let exp1' = subst_exp substs e1 in
                let exp1' = apply_pat_choices pchoices exp1' in
                let exp2' = subst_exp substs e2 in
                let exp2' = apply_pat_choices pchoices exp2' in
                Pat_aux (Pat_when (pat', map_exp exp1', map_exp exp2'),l))
                patsubsts
            else nosplit
         | ConstrSplit patnsubsts ->
            List.map (fun (pat',nsubst) ->
              let pat' = nexp_subst_pat nsubst pat' in
              let exp1' = nexp_subst_exp nsubst e1 in
              let exp2' = nexp_subst_exp nsubst e2 in
              Pat_aux (Pat_when (pat', map_exp exp1', map_exp exp2'),l)
            ) patnsubsts)
    and map_letbind (LB_aux (lb,annot)) =
      match lb with
      | LB_val (p,e) -> LB_aux (LB_val (check_single_pat p,map_exp e), annot)
    and map_lexp ((LEXP_aux (e,annot)) as le) =
      let re e = LEXP_aux (e,annot) in
      match e with
      | LEXP_id _
      | LEXP_cast _
        -> le
      | LEXP_memory (id,es) -> re (LEXP_memory (id,List.map map_exp es))
      | LEXP_tup les -> re (LEXP_tup (List.map map_lexp les))
      | LEXP_vector (le,e) -> re (LEXP_vector (map_lexp le, map_exp e))
      | LEXP_vector_range (le,e1,e2) -> re (LEXP_vector_range (map_lexp le, map_exp e1, map_exp e2))
      | LEXP_field (le,id) -> re (LEXP_field (map_lexp le, id))
    in

    let map_funcl (FCL_aux (FCL_Funcl (id,pexp),annot)) =
      List.map (fun pexp -> FCL_aux (FCL_Funcl (id,pexp),annot)) (map_pexp pexp)
    in

    let map_fundef (FD_aux (FD_function (r,t,e,fcls),annot)) =
      FD_aux (FD_function (r,t,e,List.concat (List.map map_funcl fcls)),annot)
    in
    let map_scattered_def sd =
      match sd with
      | SD_aux (SD_scattered_funcl fcl, annot) ->
         List.map (fun fcl' -> SD_aux (SD_scattered_funcl fcl', annot)) (map_funcl fcl)
      | _ -> [sd]
    in
    let map_def d =
      match d with
      | DEF_kind _
      | DEF_type _
      | DEF_spec _
      | DEF_default _
      | DEF_reg_dec _
      | DEF_comm _
      | DEF_overload _
      | DEF_fixity _
      | DEF_internal_mutrec _
        -> [d]
      | DEF_fundef fd -> [DEF_fundef (map_fundef fd)]
      | DEF_val lb -> [DEF_val (map_letbind lb)]
      | DEF_scattered sd -> List.map (fun x -> DEF_scattered x) (map_scattered_def sd)
    in
    Defs (List.concat (List.map map_def defs))
  in
  map_locs splits defs'



(* The next section of code turns atom('n) types into itself('n) types, which
   survive into the Lem output, so can be used to parametrise functions over
   internal bitvector lengths (such as datasize and regsize in ARM specs *)

module AtomToItself =
struct

let findi f =
  let rec aux n = function
    | [] -> None
    | h::t -> match f h with Some x -> Some (n,x) | _ -> aux (n+1) t
  in aux 0

let mapat f is xs =
  let rec aux n = function
    | _, [] -> []
    | (i,_)::is, h::t when i = n ->
       let h' = f h in
       let t' = aux (n+1) (is, t) in
       h'::t'
    | is, h::t ->
       let t' = aux (n+1) (is, t) in
       h::t'
  in aux 0 (is, xs)

let mapat_extra f is xs =
  let rec aux n = function
    | _, [] -> [], []
    | (i,v)::is, h::t when i = n ->
       let h',x = f v h in
       let t',xs = aux (n+1) (is, t) in
       h'::t',x::xs
    | is, h::t ->
       let t',xs = aux (n+1) (is, t) in
       h::t',xs
  in aux 0 (is, xs)

let tyvars_bound_in_pat pat =
  let open Rewriter in
  fst (fold_pat
         { (compute_pat_alg KidSet.empty KidSet.union) with
           p_var = (fun ((s,pat),kid) -> KidSet.add kid s, P_var (pat,kid)) }
         pat)
let tyvars_bound_in_lb (LB_aux (LB_val (pat,_),_)) = tyvars_bound_in_pat pat

let rec sizes_of_typ (Typ_aux (t,l)) =
  match t with
  | Typ_id _
  | Typ_var _
    -> KidSet.empty
  | Typ_fn _ -> raise (Reporting_basic.err_general l
                         "Function type on expressinon")
  | Typ_tup typs -> kidset_bigunion (List.map sizes_of_typ typs)
  | Typ_exist (kids,_,typ) ->
     List.fold_left (fun s k -> KidSet.remove k s) (sizes_of_typ typ) kids
  | Typ_app (Id_aux (Id "vector",_),
             [Typ_arg_aux (Typ_arg_nexp size,_);
              _;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)]) ->
     KidSet.of_list (size_nvars_nexp size)
  | Typ_app (_,tas) ->
     kidset_bigunion (List.map sizes_of_typarg tas)
and sizes_of_typarg (Typ_arg_aux (ta,_)) =
  match ta with
    Typ_arg_nexp _
  | Typ_arg_order _
    -> KidSet.empty
  | Typ_arg_typ typ -> sizes_of_typ typ

let sizes_of_annot = function
  | _,None -> KidSet.empty
  | _,Some (env,typ,_) -> sizes_of_typ (Env.base_typ_of env typ)

let change_parameter_pat kid = function
  | P_aux (P_id var, (l,_))
  | P_aux (P_typ (_,P_aux (P_id var, (l,_))),_)
    -> P_aux (P_id var, (l,None)), (var,kid)
  | P_aux (_,(l,_)) -> raise (Reporting_basic.err_unreachable l
                                "Expected variable pattern")

(* We add code to change the itself('n) parameter into the corresponding
   integer. *)
let add_var_rebind exp (var,kid) =
  let l = Generated Unknown in
  let annot = (l,None) in
  E_aux (E_let (LB_aux (LB_val (P_aux (P_id var,annot),
                                E_aux (E_app (mk_id "size_itself_int",[E_aux (E_id var,annot)]),annot)),annot),exp),annot)

(* atom('n) arguments to function calls need to be rewritten *)
let replace_with_the_value (E_aux (_,(l,_)) as exp) =
  let env = env_of exp in
  let typ, wrap = match typ_of exp with
    | Typ_aux (Typ_exist (kids,nc,typ),l) -> typ, fun t -> Typ_aux (Typ_exist (kids,nc,t),l)
    | typ -> typ, fun x -> x
  in
  let typ = Env.expand_synonyms env typ in
  let mk_exp nexp l l' =
     E_aux (E_cast (wrap (Typ_aux (Typ_app (Id_aux (Id "itself",Generated Unknown),
                                      [Typ_arg_aux (Typ_arg_nexp nexp,l')]),Generated Unknown)),
                    E_aux (E_app (Id_aux (Id "make_the_value",Generated Unknown),[exp]),(Generated l,None))),
            (Generated l,None))
  in
  match typ with
  | Typ_aux (Typ_app (Id_aux (Id "range",_),
                      [Typ_arg_aux (Typ_arg_nexp nexp,l');Typ_arg_aux (Typ_arg_nexp nexp',_)]),_)
    when nexp_identical nexp nexp' ->
     mk_exp nexp l l'
  | Typ_aux (Typ_app (Id_aux (Id "atom",_),
                      [Typ_arg_aux (Typ_arg_nexp nexp,l')]),_) ->
     mk_exp nexp l l'
  | _ -> raise (Reporting_basic.err_unreachable l
                  "atom stopped being an atom?")

let replace_type env typ =
  let Typ_aux (t,l) = Env.expand_synonyms env typ in
  match t with
  | Typ_app (Id_aux (Id "range",_),
             [Typ_arg_aux (Typ_arg_nexp nexp,l');Typ_arg_aux (Typ_arg_nexp _,_)]) ->
     Typ_aux (Typ_app (Id_aux (Id "itself",Generated Unknown),
                       [Typ_arg_aux (Typ_arg_nexp nexp,l')]),Generated l)
  | Typ_app (Id_aux (Id "atom",_),
                      [Typ_arg_aux (Typ_arg_nexp nexp,l')]) ->
     Typ_aux (Typ_app (Id_aux (Id "itself",Generated Unknown),
                       [Typ_arg_aux (Typ_arg_nexp nexp,l')]),Generated l)
  | _ -> raise (Reporting_basic.err_unreachable l
                  "atom stopped being an atom?")


let rewrite_size_parameters env (Defs defs) =
  let open Rewriter in
  let size_vars pexp =
    fst (fold_pexp
           { (compute_exp_alg KidSet.empty KidSet.union) with
             e_aux = (fun ((s,e),annot) -> KidSet.union s (sizes_of_annot annot), E_aux (e,annot));
             e_let = (fun ((sl,lb),(s2,e2)) -> KidSet.union sl (KidSet.diff s2 (tyvars_bound_in_lb lb)), E_let (lb,e2));
             e_for = (fun (id,(s1,e1),(s2,e2),(s3,e3),ord,(s4,e4)) ->
               let kid = mk_kid ("loop_" ^ string_of_id id) in
               KidSet.union s1 (KidSet.union s2 (KidSet.union s3 (KidSet.remove kid s4))),
               E_for (id,e1,e2,e3,ord,e4));
             pat_exp = (fun ((sp,pat),(s,e)) -> KidSet.diff s (tyvars_bound_in_pat pat), Pat_exp (pat,e))}
           pexp)
  in
  let sizes_funcl fsizes (FCL_aux (FCL_Funcl (id,pexp),(l,_))) =
    let sizes = size_vars pexp in
    let pat,guard,exp,pannot = destruct_pexp pexp in
    let visible_tyvars =
      KidSet.union
        (Pretty_print_lem.lem_tyvars_of_typ (pat_typ_of pat))
         (Pretty_print_lem.lem_tyvars_of_typ (typ_of exp))
    in
    let expose_tyvars = KidSet.diff sizes visible_tyvars in
    let parameters = match pat with
      | P_aux (P_tup ps,_) -> ps
      | _ -> [pat]
    in
    let to_change = Util.map_filter
      (fun kid ->
        let check (P_aux (_,(_,Some (env,typ,_)))) =
          match Env.expand_synonyms env typ with
            Typ_aux (Typ_app(Id_aux (Id "range",_),
                             [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid',_)),_);
                              Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid'',_)),_)]),_) ->
              if Kid.compare kid kid' = 0 && Kid.compare kid kid'' = 0 then Some kid else None
          | Typ_aux (Typ_app(Id_aux (Id "atom", _),
                             [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid',_)),_)]), _) ->
              if Kid.compare kid kid' = 0 then Some kid else None
          | _ -> None
        in match findi check parameters with
        | None -> (Reporting_basic.print_error (Reporting_basic.Err_general (l,
                           ("Unable to find an argument for " ^ string_of_kid kid)));
                   None)
        | Some i -> Some i)
      (KidSet.elements expose_tyvars)
    in
    let ik_compare (i,k) (i',k') =
      match compare (i : int) i' with
      | 0 -> Kid.compare k k'
      | x -> x
    in
    let to_change = List.sort ik_compare to_change in
    match Bindings.find id fsizes with
    | old -> if List.for_all2 (fun x y -> ik_compare x y = 0) old to_change then fsizes else
        raise (Reporting_basic.err_general l
                 ("Different size type variables in different clauses of " ^ string_of_id id))
    | exception Not_found -> Bindings.add id to_change fsizes
  in
  let sizes_def fsizes = function
    | DEF_fundef (FD_aux (FD_function (_,_,_,funcls),_)) ->
       List.fold_left sizes_funcl fsizes funcls
    | _ -> fsizes
  in
  let fn_sizes = List.fold_left sizes_def Bindings.empty defs in

  let rewrite_e_app (id,args) =
    match Bindings.find id fn_sizes with
    | [] -> E_app (id,args)
    | to_change ->
       let args' = mapat replace_with_the_value to_change args in
       E_app (id,args')
    | exception Not_found -> E_app (id,args)
  in
  let rewrite_funcl (FCL_aux (FCL_Funcl (id,pexp),(l,annot))) =
    let pat,guard,body,(pl,_) = destruct_pexp pexp in
    let pat,guard,body =
      (* Update pattern and add itself -> nat wrapper to body *)
      match Bindings.find id fn_sizes with
      | [] -> pat,guard,body
      | to_change ->
         let pat, vars =
           match pat with
             P_aux (P_tup pats,(l,_)) ->
               let pats, vars = mapat_extra change_parameter_pat to_change pats in
               P_aux (P_tup pats,(l,None)), vars
           | P_aux (_,(l,_)) ->
              begin
                match to_change with
                | [0,kid] ->
                   let pat, var = change_parameter_pat kid pat in
                   pat, [var]
                | _ ->
                   raise (Reporting_basic.err_unreachable l
                            "Expected multiple parameters at single parameter")
              end
         in
         (* TODO: only add bindings that are necessary (esp for guards) *)
         let body = List.fold_left add_var_rebind body vars in
         let guard = match guard with
           | None -> None
           | Some exp -> Some (List.fold_left add_var_rebind exp vars)
         in
         pat,guard,body
      | exception Not_found -> pat,guard,body
    in
    (* Update function applications *)
    let body = fold_exp { id_exp_alg with e_app = rewrite_e_app } body in
    let guard = match guard with
      | None -> None
      | Some exp -> Some (fold_exp { id_exp_alg with e_app = rewrite_e_app } exp) in
    FCL_aux (FCL_Funcl (id,construct_pexp (pat,guard,body,(pl,None))),(l,None))
  in
  let rewrite_def = function
    | DEF_fundef (FD_aux (FD_function (recopt,tannopt,effopt,funcls),(l,_))) ->
       (* TODO rewrite tannopt? *)
       DEF_fundef (FD_aux (FD_function (recopt,tannopt,effopt,List.map rewrite_funcl funcls),(l,None)))
    | DEF_spec (VS_aux (VS_val_spec (typschm,id,extern,cast),(l,annot))) as spec ->
       begin
         match Bindings.find id fn_sizes with
         | [] -> spec
         | to_change ->
            let typschm = match typschm with
              | TypSchm_aux (TypSchm_ts (tq,typ),l) ->
                 let typ = match typ with
                   | Typ_aux (Typ_fn (Typ_aux (Typ_tup ts,l),t2,eff),l2) ->
                      Typ_aux (Typ_fn (Typ_aux (Typ_tup (mapat (replace_type env) to_change ts),l),t2,eff),l2)
                   | Typ_aux (Typ_fn (typ,t2,eff),l2) ->
                      Typ_aux (Typ_fn (replace_type env typ,t2,eff),l2)
                   | _ -> replace_type env typ
                 in TypSchm_aux (TypSchm_ts (tq,typ),l)
            in
            DEF_spec (VS_aux (VS_val_spec (typschm,id,extern,cast),(l,None)))
         | exception Not_found -> spec
       end
    | def -> def
  in
(*
  Bindings.iter (fun id args ->
    print_endline (string_of_id id ^ " needs " ^
                     String.concat ", " (List.map string_of_int args))) fn_sizes
*)
  Defs (List.map rewrite_def defs)

end


let is_id env id =
  let ids = Env.get_overloads (Id_aux (id,Parse_ast.Unknown)) env in
  let ids = id :: List.map (fun (Id_aux (id,_)) -> id) ids in
  fun (Id_aux (x,_)) -> List.mem x ids



module Analysis =
struct

type loc = string * int (* filename, line *)

let string_of_loc (s,l) = s ^ "." ^ string_of_int l

let id_pair_compare (id,l) (id',l') =
    match Id.compare id id' with
    | 0 -> compare l l'
    | x -> x

(* Usually we do a full case split on an argument, but sometimes we find a
   case expression in the function body that suggests a more compact case
   splitting. *)
type match_detail =
  | Total
  | Partial of tannot pat list * Parse_ast.l

(* Arguments that we might split on *)
module ArgSplits = Map.Make (struct
  type t = id * loc
  let compare = id_pair_compare
end)
type arg_splits = match_detail ArgSplits.t

(* Arguments that we should look at in callers *)
module CallerArgSet = Set.Make (struct
  type t = id * int
  let compare = id_pair_compare
end)

(* Type variables that we should look at in callers *)
module CallerKidSet = Set.Make (struct
  type t = id * kid
  let compare (id,kid) (id',kid') =
    match Id.compare id id' with
    | 0 -> Kid.compare kid kid'
    | x -> x
end)

(* Map from locations to string sets *)
module Failures = Map.Make (struct
  type t = Parse_ast.l
  let compare = compare
end)
module StringSet = Set.Make (struct
  type t = string
  let compare = compare
end)

type dependencies =
  | Have of arg_splits * CallerArgSet.t * CallerKidSet.t
  (* args to split inside fn * caller args to split * caller kids that are bitvector parameters *)
  | Unknown of Parse_ast.l * string

let string_of_match_detail = function
  | Total -> "[total]"
  | Partial (pats,_) -> "[" ^ String.concat " | " (List.map string_of_pat pats) ^ "]"

let string_of_argsplits s =
  String.concat ", "
    (List.map (fun ((id,l),detail) ->
      string_of_id id ^ "." ^ string_of_loc l ^ string_of_match_detail detail)
                        (ArgSplits.bindings s))

let string_of_callerset s =
  String.concat ", " (List.map (fun (id,arg) -> string_of_id id ^ "." ^ string_of_int arg)
                        (CallerArgSet.elements s))

let string_of_callerkidset s =
  String.concat ", " (List.map (fun (id,kid) -> string_of_id id ^ "." ^ string_of_kid kid)
                        (CallerKidSet.elements s))

let string_of_dep = function
  | Have (args,callset,kidset) ->
     "Have (" ^ string_of_argsplits args ^ "; " ^ string_of_callerset callset ^ "; " ^
       string_of_callerkidset kidset ^ ")"
  | Unknown (l,msg) -> "Unknown " ^ msg ^ " at " ^ Reporting_basic.loc_to_string l

(* Result of analysing the body of a function.  The split field gives
   the arguments to split based on the body alone, and the failures
   field where we couldn't do anything.  The other fields are used at
   the end for the interprocedural phase. *)

type result = {
  split : arg_splits;
  failures : StringSet.t Failures.t;
  (* Dependencies for arguments and type variables of each fn called, so that
     if the fn uses one for a bitvector size we can track it back *)
  split_on_call : (dependencies list * dependencies KBindings.t) Bindings.t; (* (arguments, kids) per fn *)
  split_in_caller : CallerArgSet.t;
  kid_in_caller : CallerKidSet.t
}

let empty = {
  split = ArgSplits.empty;
  failures = Failures.empty;
  split_on_call = Bindings.empty;
  split_in_caller = CallerArgSet.empty;
  kid_in_caller = CallerKidSet.empty
}

let merge_detail _ x y =
  match x,y with
  | None, x -> x
  | x, None -> x
  | Some _, Some _ -> Some Total (* TODO preserve equivalent patterns *)

let dmerge x y =
  match x,y with
  | Unknown (l,s), _ -> Unknown (l,s)
  | _, Unknown (l,s) -> Unknown (l,s)
  | Have (a,c,k), Have (a',c',k') ->
     Have (ArgSplits.merge merge_detail a a', CallerArgSet.union c c', CallerKidSet.union k k')

let dempty = Have (ArgSplits.empty, CallerArgSet.empty, CallerKidSet.empty)

let dopt_merge k x y =
  match x, y with
  | None, _ -> y
  | _, None -> x
  | Some x, Some y -> Some (dmerge x y)

let dep_bindings_merge a1 a2 =
  Bindings.merge dopt_merge a1 a2

let dep_kbindings_merge a1 a2 =
  KBindings.merge dopt_merge a1 a2

let call_kid_merge k x y =
  match x, y with
  | None, x -> x
  | x, None -> x
  | Some d, Some d' -> Some (dmerge d d')

let call_arg_merge k args args' =
  match args, args' with
  | None, x -> x
  | x, None -> x
  | Some (args,kdep), Some (args',kdep')
    -> Some (List.map2 dmerge args args', KBindings.merge call_kid_merge kdep kdep')

let failure_merge _ x y =
  match x, y with
  | None, x -> x
  | x, None -> x
  | Some x, Some y -> Some (StringSet.union x y)

let merge rs rs' = {
  split = ArgSplits.merge merge_detail rs.split rs'.split;
  failures = Failures.merge failure_merge rs.failures rs'.failures;
  split_on_call = Bindings.merge call_arg_merge rs.split_on_call rs'.split_on_call;
  split_in_caller = CallerArgSet.union rs.split_in_caller rs'.split_in_caller;
  kid_in_caller = CallerKidSet.union rs.kid_in_caller rs'.kid_in_caller
}

type env = {
  var_deps : dependencies Bindings.t;
  kid_deps : dependencies KBindings.t
}

let rec split3 = function
  | [] -> [],[],[]
  | ((h1,h2,h3)::t) ->
     let t1,t2,t3 = split3 t in
     (h1::t1,h2::t2,h3::t3)

let kids_bound_by_pat pat =
  let open Rewriter in
  fst (fold_pat ({ (compute_pat_alg KidSet.empty KidSet.union)
                   with p_var = (fun ((s,p),kid) -> (KidSet.add kid s, P_var (p,kid))) }) pat)

(* Add bound variables from a pattern to the environment with the given dependency. *)

let update_env env deps pat =
  let bound = bindings_from_pat pat in
  let var_deps = List.fold_left (fun ds v -> Bindings.add v deps ds) env.var_deps bound in
  let kbound = kids_bound_by_pat pat in
  let kid_deps = KidSet.fold (fun v ds -> KBindings.add v deps ds) kbound env.kid_deps in
  { var_deps = var_deps; kid_deps = kid_deps }

let assigned_vars_exps es =
  List.fold_left (fun vs exp -> IdSet.union vs (assigned_vars exp))
    IdSet.empty es

(* For adding control dependencies to mutable variables *)

let add_dep_to_assigned dep assigns es =
  let assigned = assigned_vars_exps es in
  Bindings.mapi (fun id d -> if IdSet.mem id assigned then dmerge dep d else d) assigns

(* Functions to give dependencies for type variables in nexps, constraints, types and
   unification variables.  For function calls we also supply a list of dependencies for
   arguments so that we can find dependencies for existentially bound sizes. *)

let deps_of_tyvars kid_deps arg_deps kids =
  let check kid deps =
    match KBindings.find kid kid_deps with
    | deps' -> dmerge deps deps'
    | exception Not_found ->
       match kid with
       | Kid_aux (Var kidstr, l) ->
          let unknown = Unknown (l, "Unknown type variable " ^ string_of_kid kid) in
          (* Tyvars from existentials in arguments have a special format *)
          if String.length kidstr > 5 && String.sub kidstr 0 4 = "'arg" then
            try
              let i = String.index kidstr '#' in
              let n = String.sub kidstr 4 (i-4) in
              let arg = int_of_string n in
              List.nth arg_deps arg
            with Not_found | Failure _ -> unknown
          else unknown
  in
  KidSet.fold check kids dempty

let deps_of_nexp kid_deps arg_deps nexp =
  let kids = nexp_frees nexp in
  deps_of_tyvars kid_deps arg_deps kids

let rec deps_of_nc kid_deps (NC_aux (nc,l)) =
  match nc with
  | NC_equal (nexp1,nexp2)
  | NC_bounded_ge (nexp1,nexp2)
  | NC_bounded_le (nexp1,nexp2)
  | NC_not_equal (nexp1,nexp2)
    -> dmerge (deps_of_nexp kid_deps [] nexp1) (deps_of_nexp kid_deps [] nexp2)
  | NC_set (kid,_) ->
     (match KBindings.find kid kid_deps with
     | deps -> deps
     | exception Not_found -> Unknown (l, "Unknown type variable " ^ string_of_kid kid))
  | NC_or (nc1,nc2)
  | NC_and (nc1,nc2)
    -> dmerge (deps_of_nc kid_deps nc1) (deps_of_nc kid_deps nc2)
  | NC_true
  | NC_false
    -> dempty

let deps_of_typ kid_deps arg_deps typ =
  deps_of_tyvars kid_deps arg_deps (tyvars_of_typ typ)

let deps_of_uvar kid_deps arg_deps = function
  | U_nexp nexp -> deps_of_nexp kid_deps arg_deps nexp
  | U_order _
  | U_effect _ -> dempty
  | U_typ typ -> deps_of_typ kid_deps arg_deps typ

let mk_subrange_pattern vannot vstart vend =
  let (_,len,ord,typ) = vector_typ_args_of (typ_of_annot vannot) in
  match ord with
  | Ord_aux (Ord_var _,_) -> None
  | Ord_aux (ord',_) ->
     let vstart,vend = if ord' = Ord_inc then vstart,vend else vend,vstart
     in
     let dummyl = Generated Unknown in
     match len with
     | Nexp_aux (Nexp_constant len,_) -> 
        Some (fun pat ->
          let end_len = Big_int.pred (Big_int.sub len vend) in
          (* Wrap pat in its type; in particular the type checker won't
             manage P_wild in the middle of a P_vector_concat *)
          let pat = P_aux (P_typ (pat_typ_of pat, pat),(Generated (pat_loc pat),None)) in
          let pats = if Big_int.greater end_len Big_int.zero then
              [pat;P_aux (P_typ (vector_typ (nconstant end_len) ord typ,
                                 P_aux (P_wild,(dummyl,None))),(dummyl,None))]
            else [pat]
          in
          let pats = if Big_int.greater vstart Big_int.zero then
              (P_aux (P_typ (vector_typ (nconstant vstart) ord typ,
                             P_aux (P_wild,(dummyl,None))),(dummyl,None)))::pats
            else pats
          in
          let pats = if ord' = Ord_inc then pats else List.rev pats
          in
          P_aux (P_vector_concat pats,(Generated (fst vannot),None)))
     | _ -> None

(* If the expression matched on in a case expression is a function argument,
   and has no other dependencies, we can try to use the pattern match directly
   rather than doing a full case split. *)
let refine_dependency env (E_aux (e,(l,annot)) as exp) pexps =
  let check_dep id ctx =
    match Bindings.find id env.var_deps with
    | Have (args,callargs,callkids) ->
       if CallerArgSet.is_empty callargs && CallerKidSet.is_empty callkids then
         match ArgSplits.bindings args with
         | [(id',loc),Total] when Id.compare id id' == 0 ->
             (match Util.map_all (function
                 | Pat_aux (Pat_exp (pat,_),_) -> Some (ctx pat)
                 | Pat_aux (Pat_when (_,_,_),_) -> None) pexps
              with
              | Some pats ->
                 if l = Parse_ast.Unknown then
                   (Reporting_basic.print_error
                      (Reporting_basic.Err_general
                         (l, "No location for pattern match: " ^ string_of_exp exp));
                    None)
                 else
                   Some (Have (ArgSplits.singleton (id,loc) (Partial (pats,l)),callargs,callkids))
              | None -> None)
          | _ -> None
        else None
     | Unknown _ -> None
     | exception Not_found -> None
  in
  match e with
  | E_id id -> check_dep id (fun x -> x)
  | E_app (fn_id, [E_aux (E_id id,vannot);
                   E_aux (E_lit (L_aux (L_num vstart,_)),_);
                   E_aux (E_lit (L_aux (L_num vend,_)),_)])
      when is_id (env_of exp) (Id "vector_subrange") fn_id ->
     (match mk_subrange_pattern vannot vstart vend with
     | Some mk_pat -> check_dep id mk_pat
     | None -> None)
  | _ -> None

(* Takes an environment of dependencies on vars, type vars, and flow control,
   and dependencies on mutable variables.  The latter are quite conservative,
   we currently drop variables assigned inside loops, for example. *)

let rec analyse_exp fn_id env assigns (E_aux (e,(l,annot)) as exp) =
  let remove_assigns es message =
    let assigned = assigned_vars_exps es in
    IdSet.fold
      (fun id asn ->
        Bindings.add id (Unknown (l, string_of_id id ^ message)) asn)
      assigned assigns
  in
  let non_det es =
    let assigns = remove_assigns es " assigned in non-deterministic expressions" in
    let deps, _, rs = split3 (List.map (analyse_exp fn_id env assigns) es) in
    (deps, assigns, List.fold_left merge empty rs)
  in
  let merge_deps deps = List.fold_left dmerge dempty deps in
  let deps, assigns, r =
    match e with
    | E_block es ->
       let rec aux assigns = function
         | [] -> (dempty, assigns, empty)
         | [e] -> analyse_exp fn_id env assigns e
         | e::es ->
            let _, assigns, r' = analyse_exp fn_id env assigns e in
            let d, assigns, r = aux assigns es in
            d, assigns, merge r r'
       in
       aux assigns es
    | E_nondet es ->
       let _, assigns, r = non_det es in
       (dempty, assigns, r)
    | E_id id ->
       begin 
         match Bindings.find id env.var_deps with
         | args -> (args,assigns,empty)
         | exception Not_found ->
            match Bindings.find id assigns with
            | args -> (args,assigns,empty)
            | exception Not_found ->
               match Env.lookup_id id (Type_check.env_of_annot (l,annot)) with
               | Enum _ | Union _ -> dempty,assigns,empty
               | Register _ -> Unknown (l, string_of_id id ^ " is a register"),assigns,empty
               | _ ->
                  Unknown (l, string_of_id id ^ " is not in the environment"),assigns,empty
       end
    | E_lit _ -> (dempty,assigns,empty)
    | E_cast (_,e) -> analyse_exp fn_id env assigns e
    | E_app (id,args) ->
       let deps, assigns, r = non_det args in
       let (_,fn_typ) = Env.get_val_spec id (env_of_annot (l,annot)) in
       let fn_effect = match fn_typ with
         | Typ_aux (Typ_fn (_,_,eff),_) -> eff
         | _ -> Effect_aux (Effect_set [],Unknown)
       in
       let eff_dep = match fn_effect with
         | Effect_aux (Effect_set ([] | [BE_aux (BE_undef,_)]),_) -> dempty
         | _ -> Unknown (l, "Effects from function application")
       in
       let kid_inst = instantiation_of exp in
       (* Change kids in instantiation to the canonical ones from the type signature *)
       let kid_inst = KBindings.fold (fun kid -> KBindings.add (orig_kid kid)) kid_inst KBindings.empty in
       let kid_deps = KBindings.map (deps_of_uvar env.kid_deps deps) kid_inst in
       let rdep,r' =
         if Id.compare fn_id id == 0 then
           let bad = Unknown (l,"Recursive call of " ^ string_of_id id) in
           let deps = List.map (fun _ -> bad) deps in
           let kid_deps = KBindings.map (fun _ -> bad) kid_deps in
           bad, { empty with split_on_call = Bindings.singleton id (deps, kid_deps) }
         else
           dempty, { empty with split_on_call = Bindings.singleton id (deps, kid_deps) } in
       (merge_deps (rdep::eff_dep::deps), assigns, merge r r')
    | E_tuple es
    | E_list es ->
       let deps, assigns, r = non_det es in
       (merge_deps deps, assigns, r)
    | E_if (e1,e2,e3) ->
       let d1,assigns,r1 = analyse_exp fn_id env assigns e1 in
       let d2,a2,r2 = analyse_exp fn_id env assigns e2 in
       let d3,a3,r3 = analyse_exp fn_id env assigns e3 in
       let assigns = add_dep_to_assigned d1 (dep_bindings_merge a2 a3) [e2;e3] in
       (dmerge d1 (dmerge d2 d3), assigns, merge r1 (merge r2 r3))
    | E_loop (_,e1,e2) ->
       (* We remove all of the variables assigned in the loop, so we don't
          need to add control dependencies *)
       let assigns = remove_assigns [e1;e2] " assigned in a loop" in
       let d1,a1,r1 = analyse_exp fn_id env assigns e1 in
       let d2,a2,r2 = analyse_exp fn_id env assigns e2 in
     (dempty, assigns, merge r1 r2)
    | E_for (var,efrom,eto,eby,ord,body) ->
       let d1,assigns,r1 = non_det [efrom;eto;eby] in
       let assigns = remove_assigns [body] " assigned in a loop" in
       let d = merge_deps d1 in
       let loop_kid = mk_kid ("loop_" ^ string_of_id var) in
       let env' = { env with
         kid_deps = KBindings.add loop_kid d env.kid_deps} in
       let d2,a2,r2 = analyse_exp fn_id env' assigns body in
       (dempty, assigns, merge r1 r2)
    | E_vector es ->
       let ds, assigns, r = non_det es in
       (merge_deps ds, assigns, r)
    | E_vector_access (e1,e2)
    | E_vector_append (e1,e2)
    | E_cons (e1,e2) ->
       let ds, assigns, r = non_det [e1;e2] in
       (merge_deps ds, assigns, r)
    | E_vector_subrange (e1,e2,e3)
    | E_vector_update (e1,e2,e3) ->
       let ds, assigns, r = non_det [e1;e2;e3] in
       (merge_deps ds, assigns, r)
    | E_vector_update_subrange (e1,e2,e3,e4) ->
       let ds, assigns, r = non_det [e1;e2;e3;e4] in
       (merge_deps ds, assigns, r)
    | E_record (FES_aux (FES_Fexps (fexps,_),_)) ->
       let es = List.map (function (FE_aux (FE_Fexp (_,e),_)) -> e) fexps in
       let ds, assigns, r = non_det es in
       (merge_deps ds, assigns, r)
    | E_record_update (e,FES_aux (FES_Fexps (fexps,_),_)) ->
       let es = List.map (function (FE_aux (FE_Fexp (_,e),_)) -> e) fexps in
       let ds, assigns, r = non_det (e::es) in
       (merge_deps ds, assigns, r)
    | E_field (e,_) -> analyse_exp fn_id env assigns e
    | E_case (e,cases) ->
       let deps,assigns,r = analyse_exp fn_id env assigns e in
       let deps = match refine_dependency env e cases with
         | Some deps -> deps
         | None -> deps
       in
       let analyse_case (Pat_aux (pexp,_)) =
         match pexp with
         | Pat_exp (pat,e1) ->
            let env = update_env env deps pat in
            let d,assigns,r = analyse_exp fn_id env assigns e1 in
            let assigns = add_dep_to_assigned deps assigns [e1] in
            (d,assigns,r)
         | Pat_when (pat,e1,e2) ->
            let env = update_env env deps pat in
            let d1,assigns,r1 = analyse_exp fn_id env assigns e1 in
            let d2,assigns,r2 = analyse_exp fn_id env assigns e2 in
            let assigns = add_dep_to_assigned deps assigns [e1;e2] in
            (dmerge d1 d2, assigns, merge r1 r2)
       in
       let ds,assigns,rs = split3 (List.map analyse_case cases) in
       (merge_deps (deps::ds),
        List.fold_left dep_bindings_merge Bindings.empty assigns,
        List.fold_left merge r rs)
    | E_let (LB_aux (LB_val (pat,e1),_),e2) ->
       let d1,assigns,r1 = analyse_exp fn_id env assigns e1 in
       let env = update_env env d1 pat in
       let d2,assigns,r2 = analyse_exp fn_id env assigns e2 in
       (d2,assigns,merge r1 r2)
    | E_assign (lexp,e1) ->
       let d1,assigns,r1 = analyse_exp fn_id env assigns e1 in
       let assigns,r2 = analyse_lexp fn_id env assigns d1 lexp in
       (dempty, assigns, merge r1 r2)
    | E_sizeof nexp ->
       (deps_of_nexp env.kid_deps [] nexp, assigns, empty)
    | E_return e
    | E_exit e
    | E_throw e ->
       let _, _, r = analyse_exp fn_id env assigns e in
       (dempty, Bindings.empty, r)
    | E_try (e,cases) ->
       let deps,_,r = analyse_exp fn_id env assigns e in
       let assigns = remove_assigns [e] " assigned in try expression" in
       let analyse_handler (Pat_aux (pexp,_)) =
         match pexp with
         | Pat_exp (pat,e1) ->
            let env = update_env env (Unknown (l,"Exception")) pat in
            let d,assigns,r = analyse_exp fn_id env assigns e1 in
            let assigns = add_dep_to_assigned deps assigns [e1] in
            (d,assigns,r)
         | Pat_when (pat,e1,e2) ->
            let env = update_env env (Unknown (l,"Exception")) pat in
            let d1,assigns,r1 = analyse_exp fn_id env assigns e1 in
            let d2,assigns,r2 = analyse_exp fn_id env assigns e2 in
            let assigns = add_dep_to_assigned deps assigns [e1;e2] in
            (dmerge d1 d2, assigns, merge r1 r2)
       in
       let ds,assigns,rs = split3 (List.map analyse_handler cases) in
       (merge_deps (deps::ds),
        List.fold_left dep_bindings_merge Bindings.empty assigns,
        List.fold_left merge r rs)
    | E_assert (e1,_) -> analyse_exp fn_id env assigns e1

    | E_app_infix _
    | E_internal_cast _
    | E_internal_exp _
    | E_sizeof_internal _
    | E_internal_exp_user _
    | E_comment _
    | E_comment_struc _
    | E_internal_plet _
    | E_internal_return _
      -> raise (Reporting_basic.err_unreachable l
                  ("Unexpected expression encountered in monomorphisation: " ^ string_of_exp exp))
       
    | E_var (lexp,e1,e2) ->
       (* Really we ought to remove the assignment after e2 *)
       let d1,assigns,r1 = analyse_exp fn_id env assigns e1 in
       let assigns,r' = analyse_lexp fn_id env assigns d1 lexp in
       let d2,assigns,r2 = analyse_exp fn_id env assigns e2 in
       (dempty, assigns, merge r1 (merge r' r2))
    | E_constraint nc ->
       (deps_of_nc env.kid_deps nc, assigns, empty)
  in
  let r =
    (* Check for bitvector types with parametrised sizes *)
    match annot with
    | None -> r
    | Some (tenv,typ,_) ->
       (* TODO: existential wrappers *)
       let typ = Env.expand_synonyms tenv typ in
       if is_bitvector_typ typ then
         let _,size,_,_ = vector_typ_args_of typ in
         match deps_of_nexp env.kid_deps [] size with
         | Have (args,caller,caller_kids) ->
            { r with
              split = ArgSplits.merge merge_detail r.split args;
              split_in_caller = CallerArgSet.union r.split_in_caller caller;
              kid_in_caller = CallerKidSet.union r.kid_in_caller caller_kids
            }
         | Unknown (l,msg) ->
            { r with
              failures =
                Failures.add l (StringSet.singleton ("Unable to monomorphise " ^ string_of_nexp size ^ ": " ^ msg))
                  r.failures }
       else
         r
  in (deps, assigns, r)


and analyse_lexp fn_id env assigns deps (LEXP_aux (lexp,_)) =
 (* TODO: maybe subexps and sublexps should be non-det (and in const_prop_lexp, too?) *)
 match lexp with
  | LEXP_id id
  | LEXP_cast (_,id) ->
     Bindings.add id deps assigns, empty
  | LEXP_memory (id,es) ->
     let _, assigns, r = analyse_exp fn_id env assigns (E_aux (E_tuple es,(Unknown,None))) in
     assigns, r
  | LEXP_tup lexps ->
      List.fold_left (fun (assigns,r) lexp ->
       let assigns,r' = analyse_lexp fn_id env assigns deps lexp
       in assigns,merge r r') (assigns,empty) lexps
  | LEXP_vector (lexp,e) ->
     let _, assigns, r1 = analyse_exp fn_id env assigns e in
     let assigns, r2 = analyse_lexp fn_id env assigns deps lexp in
     assigns, merge r1 r2
  | LEXP_vector_range (lexp,e1,e2) ->
     let _, assigns, r1 = analyse_exp fn_id env assigns e1 in
     let _, assigns, r2 = analyse_exp fn_id env assigns e2 in
     let assigns, r3 = analyse_lexp fn_id env assigns deps lexp in
     assigns, merge r3 (merge r1 r2)
  | LEXP_field (lexp,_) -> analyse_lexp fn_id env assigns deps lexp


let translate_id (Id_aux (_,l) as id) =
  let rec aux l =
    match l with
    | Range (pos,_) -> Some (id,(pos.Lexing.pos_fname,pos.Lexing.pos_lnum))
    | Generated l -> aux l
    | _ -> None
  in aux l

let initial_env fn_id (TypQ_aux (tq,_)) pat =
  let pats = 
    match pat with
    | P_aux (P_tup pats,_) -> pats
    | _ -> [pat]
  in
  let arg i pat =
    let rec aux (P_aux (p,(l,_))) =
      let of_list pats =
        let ss,vs,ks = split3 (List.map aux pats) in
        let s = List.fold_left (ArgSplits.merge merge_detail) ArgSplits.empty ss in
        let v = List.fold_left dep_bindings_merge Bindings.empty vs in
        let k = List.fold_left dep_kbindings_merge KBindings.empty ks in
        s,v,k
      in
      match p with
      | P_lit _
      | P_wild
        -> ArgSplits.empty,Bindings.empty,KBindings.empty
      | P_as (pat,id) ->
         begin
           let s,v,k = aux pat in
           match translate_id id with
           | Some id' ->
              ArgSplits.add id' Total s,
              Bindings.add id (Have (ArgSplits.singleton id' Total,CallerArgSet.empty,CallerKidSet.empty)) v,
              k
           | None ->
              s,
              Bindings.add id (Unknown (l, ("Unable to give location for " ^ string_of_id id))) v,
              k
         end
      | P_typ (_,pat) -> aux pat
      | P_id id ->
         begin
         match translate_id id with
         | Some id' ->
            let s = ArgSplits.singleton id' Total in
            s,
            Bindings.singleton id (Have (s,CallerArgSet.empty,CallerKidSet.empty)),
            KBindings.empty
         | None ->
            ArgSplits.empty,
            Bindings.singleton id (Unknown (l, ("Unable to give location for " ^ string_of_id id))),
            KBindings.empty
         end
      | P_var (pat,kid) ->
         let s,v,k = aux pat in
         s,v,KBindings.add kid (Have (ArgSplits.empty,CallerArgSet.singleton (fn_id,i),CallerKidSet.empty)) k
      | P_app (_,pats) -> of_list pats
      | P_record (fpats,_) -> of_list (List.map (fun (FP_aux (FP_Fpat (_,p),_)) -> p) fpats)
      | P_vector pats
      | P_vector_concat pats
      | P_tup pats
      | P_list pats
        -> of_list pats
      | P_cons (p1,p2) -> of_list [p1;p2]
    in aux pat
  in
  let quant k = function
    | QI_aux (QI_id (KOpt_aux ((KOpt_none kid | KOpt_kind (_,kid)),_)),_) ->
       KBindings.add kid (Have (ArgSplits.empty,CallerArgSet.empty,CallerKidSet.singleton (fn_id,kid))) k
    | QI_aux (QI_const _,_) -> k
  in
  let kid_quant_deps =
    match tq with
    | TypQ_no_forall -> KBindings.empty
    | TypQ_tq qs -> List.fold_left quant KBindings.empty qs
  in
  let _,var_deps,kid_deps = split3 (List.mapi arg pats) in
  let var_deps = List.fold_left dep_bindings_merge Bindings.empty var_deps in
  let kid_deps = List.fold_left dep_kbindings_merge kid_quant_deps kid_deps in
  { var_deps = var_deps; kid_deps = kid_deps }

let print_result r =
  let _ = print_endline ("  splits: " ^ string_of_argsplits r.split) in
  let print_kbinding kid dep =
    let _ = print_endline ("      " ^ string_of_kid kid ^ ": " ^ string_of_dep dep) in
    ()
  in
  let print_binding id (deps,kdep) =
    let _ = print_endline ("    " ^ string_of_id id ^ ":") in
    let _ = List.iter (fun dep -> print_endline ("      " ^ string_of_dep dep)) deps in
    let _ = KBindings.iter print_kbinding kdep in
    ()
  in
  let _ = print_endline "  split_on_call: " in
  let _ = Bindings.iter print_binding r.split_on_call in
  let _ = print_endline ("  split_in_caller: " ^ string_of_callerset r.split_in_caller) in
  let _ = print_endline ("  kid_in_caller: " ^ string_of_callerkidset r.kid_in_caller) in
  let _ = print_endline ("  failures: \n    " ^
                            (String.concat "\n    "
                               (List.map (fun (l,s) -> Reporting_basic.loc_to_string l ^ ":\n     " ^
                                 String.concat "\n      " (StringSet.elements s))
                                  (Failures.bindings r.failures)))) in
  ()

let analyse_funcl debug tenv (FCL_aux (FCL_Funcl (id,pexp),_)) =
  let pat,guard,body,_ = destruct_pexp pexp in
  let (tq,_) = Env.get_val_spec id tenv in
  let aenv = initial_env id tq pat in
  let _,_,r = analyse_exp id aenv Bindings.empty body in
  let r = match guard with
    | None -> r
    | Some exp -> let _,_,r' = analyse_exp id aenv Bindings.empty exp in
                  merge r r'
  in
  let _ =
    if debug > 2 then
      (print_endline (string_of_id id);
       print_result r)
    else ()
  in r

let analyse_def debug env = function
  | DEF_fundef (FD_aux (FD_function (_,_,_,funcls),_)) ->
     List.fold_left (fun r f -> merge r (analyse_funcl debug env f)) empty funcls

  | _ -> empty

let analyse_defs debug env (Defs defs) =
  let r = List.fold_left (fun r d -> merge r (analyse_def debug env d)) empty defs in

  (* Resolve the interprocedural dependencies *)

  let rec chase_deps = function
    | Have (splits, caller_args, caller_kids) ->
       let splits,fails = CallerArgSet.fold add_arg caller_args (splits,Failures.empty) in
       let splits,fails = CallerKidSet.fold add_kid caller_kids (splits,fails) in
       splits, fails
    | Unknown (l,msg) ->
       ArgSplits.empty , Failures.singleton l (StringSet.singleton ("Unable to monomorphise dependency: " ^ msg))
  and chase_kid_caller (id,kid) =
    match Bindings.find id r.split_on_call with
    | (_,kid_deps) -> begin
      match KBindings.find kid kid_deps with
      | deps -> chase_deps deps
      | exception Not_found -> ArgSplits.empty,Failures.empty
    end
    | exception Not_found -> ArgSplits.empty,Failures.empty
  and chase_arg_caller (id,i) =
    match Bindings.find id r.split_on_call with
    | (arg_deps,_) -> chase_deps (List.nth arg_deps i)
    | exception Not_found -> ArgSplits.empty,Failures.empty
  and add_arg arg (splits,fails) =
    let splits',fails' = chase_arg_caller arg in
    ArgSplits.merge merge_detail splits splits', Failures.merge failure_merge fails fails'
  and add_kid k (splits,fails) =
    let splits',fails' = chase_kid_caller k in
    ArgSplits.merge merge_detail splits splits', Failures.merge failure_merge fails fails'
  in
  let _ = if debug > 1 then print_result r else () in
  let splits,fails = CallerArgSet.fold add_arg r.split_in_caller (r.split,r.failures) in
  let splits,fails = CallerKidSet.fold add_kid r.kid_in_caller (splits,fails) in
  let _ =
    if debug > 0 then
      (print_endline "Final splits:";
       print_endline (string_of_argsplits splits))
    else ()
  in
  let _ =
    if Failures.is_empty fails then () else
      begin
        Failures.iter (fun l msgs ->
          Reporting_basic.print_err false false l "Monomorphisation" (String.concat "\n" (StringSet.elements msgs)))
          fails;
        raise (Reporting_basic.err_general Unknown "Unable to monomorphise program")
      end
  in splits

let argset_to_list splits =
  let l = ArgSplits.bindings splits in
  let argelt  = function
    | ((id,(file,loc)),Total) -> ((file,loc),string_of_id id,None)
    | ((id,(file,loc)),Partial (pats,l)) -> ((file,loc),string_of_id id,Some (pats,l))
  in
  List.map argelt l
end

module MonoRewrites =
struct

let is_constant_range = function
  | E_aux (E_lit _,_), E_aux (E_lit _,_) -> true
  | _ -> false

let is_constant = function
  | E_aux (E_lit _,_) -> true
  | _ -> false

let is_constant_vec_typ env typ =
  let typ = Env.base_typ_of env typ in
  match destruct_vector env typ with
  | Some (size,_,_) ->
     (match nexp_simp size with
     | Nexp_aux (Nexp_constant _,_) -> true
     | _ -> false)
  | _ -> false

(* We have to add casts in here with appropriate length information so that the
   type checker knows the expected return types. *)

let rewrite_app env typ (id,args) =
  let is_append = is_id env (Id "append") in
  if is_append id then
    let is_subrange = is_id env (Id "vector_subrange") in
    let is_slice = is_id env (Id "slice") in
    let is_zeros = is_id env (Id "Zeros") in
    match args with
      (* (known-size-vector @ variable-vector) @ variable-vector *)
    | [E_aux (E_app (append,
              [e1;
               E_aux (E_app (subrange1,
                             [vector1; start1; end1]),_)]),_);
       E_aux (E_app (subrange2,
                     [vector2; start2; end2]),_)]
        when is_append append && is_subrange subrange1 && is_subrange subrange2 &&
          is_constant_vec_typ env (typ_of e1) &&
          not (is_constant_range (start1, end1) || is_constant_range (start2, end2)) ->
       let (start,size,order,bittyp) = vector_typ_args_of (Env.base_typ_of env typ) in
       let (_,size1,_,_) = vector_typ_args_of (Env.base_typ_of env (typ_of e1)) in
       let midsize = nminus size size1 in
       let midtyp = vector_typ midsize order bittyp in
       E_app (append,
              [e1;
               E_aux (E_cast (midtyp,
                              E_aux (E_app (mk_id "subrange_subrange_concat",
                                            [vector1; start1; end1; vector2; start2; end2]),
                                     (Unknown,None))),(Unknown,None))])
    | [E_aux (E_app (append,
              [e1;
               E_aux (E_app (slice1,
                             [vector1; start1; length1]),_)]),_);
       E_aux (E_app (slice2,
                     [vector2; start2; length2]),_)]
        when is_append append && is_slice slice1 && is_slice slice2 &&
          is_constant_vec_typ env (typ_of e1) &&
          not (is_constant length1 || is_constant length2) ->
       let (start,size,order,bittyp) = vector_typ_args_of (Env.base_typ_of env typ) in
       let (_,size1,_,_) = vector_typ_args_of (Env.base_typ_of env (typ_of e1)) in
       let midsize = nminus size size1 in
       let midtyp = vector_typ midsize order bittyp in
       E_app (append,
              [e1;
               E_aux (E_cast (midtyp,
                              E_aux (E_app (mk_id "slice_slice_concat",
                                            [vector1; start1; length1; vector2; start2; length2]),
                                     (Unknown,None))),(Unknown,None))])

    (* variable-range @ variable-range *)
    | [E_aux (E_app (subrange1,
                     [vector1; start1; end1]),_);
       E_aux (E_app (subrange2,
                     [vector2; start2; end2]),_)]
        when is_subrange subrange1 && is_subrange subrange2 &&
          not (is_constant_range (start1, end1) || is_constant_range (start2, end2)) ->
       E_cast (typ,
               E_aux (E_app (mk_id "subrange_subrange_concat",
                             [vector1; start1; end1; vector2; start2; end2]),
                      (Unknown,None)))

    (* variable-slice @ variable-slice *)
    | [E_aux (E_app (slice1,
                     [vector1; start1; length1]),_);
       E_aux (E_app (slice2,
                     [vector2; start2; length2]),_)]
        when is_slice slice1 && is_slice slice2 &&
          not (is_constant length1 || is_constant length2) ->
       E_cast (typ,
               E_aux (E_app (mk_id "slice_slice_concat",
                             [vector1; start1; length1; vector2; start2; length2]),(Unknown,None)))

    | [E_aux (E_app (append1,
                     [e1;
                      E_aux (E_app (slice1, [vector1; start1; length1]),_)]),_);
       E_aux (E_app (zeros1, [length2]),_)]
        when is_append append1 && is_slice slice1 && is_zeros zeros1 &&
          is_constant_vec_typ env (typ_of e1) &&
          not (is_constant length1 || is_constant length2) ->
       let (start,size,order,bittyp) = vector_typ_args_of (Env.base_typ_of env typ) in
       let (_,size1,_,_) = vector_typ_args_of (Env.base_typ_of env (typ_of e1)) in
       let midsize = nminus size size1 in
       let midtyp = vector_typ midsize order bittyp in
       E_cast (typ,
               E_aux (E_app (mk_id "append",
                             [e1;
                              E_aux (E_cast (midtyp,
                                             E_aux (E_app (mk_id "slice_zeros_concat",
                                                           [vector1; start1; length1; length2]),(Unknown,None))),(Unknown,None))]),
                      (Unknown,None)))

    | _ -> E_app (id,args)

  else if is_id env (Id "eq_vec") id then
    (* variable-range == variable_range *)
    let is_subrange = is_id env (Id "vector_subrange") in
    match args with
    | [E_aux (E_app (subrange1,
                     [vector1; start1; end1]),_);
       E_aux (E_app (subrange2,
                     [vector2; start2; end2]),_)]
        when is_subrange subrange1 && is_subrange subrange2 &&
          not (is_constant_range (start1, end1) || is_constant_range (start2, end2)) ->
       E_app (mk_id "subrange_subrange_eq",
              [vector1; start1; end1; vector2; start2; end2])
    | _ -> E_app (id,args)

  else if is_id env (Id "IsZero") id then
    match args with
    | [E_aux (E_app (subrange1, [vector1; start1; end1]),_)]
        when is_id env (Id "vector_subrange") subrange1 &&
          not (is_constant_range (start1,end1)) ->
       E_app (mk_id "is_zero_subrange",
              [vector1; start1; end1])
    | _ -> E_app (id,args)

  else if is_id env (Id "IsOnes") id then
    match args with
    | [E_aux (E_app (subrange1, [vector1; start1; end1]),_)]
        when is_id env (Id "vector_subrange") subrange1 &&
          not (is_constant_range (start1,end1)) ->
       E_app (mk_id "is_ones_subrange",
              [vector1; start1; end1])
    | _ -> E_app (id,args)

  else if is_id env (Id "Extend") id || is_id env (Id "ZeroExtend") id then
    let is_subrange = is_id env (Id "vector_subrange") in
    let is_slice = is_id env (Id "slice") in
    let is_zeros = is_id env (Id "Zeros") in
    match args with
    | (E_aux (E_app (append1,
                     [E_aux (E_app (subrange1, [vector1; start1; end1]), _);
                      E_aux (E_app (zeros1, [len1]),_)]),_))::
        ([] | [_;E_aux (E_id (Id_aux (Id "unsigned",_)),_)])
        when is_subrange subrange1 && is_zeros zeros1 && is_append append1
      -> E_app (mk_id "place_subrange",
                [vector1; start1; end1; len1])

    | (E_aux (E_app (append1,
                     [E_aux (E_app (slice1, [vector1; start1; length1]), _);
                      E_aux (E_app (zeros1, [length2]),_)]),_))::
        ([] | [_;E_aux (E_id (Id_aux (Id "unsigned",_)),_)])
        when is_slice slice1 && is_zeros zeros1 && is_append append1
      -> E_app (mk_id "place_slice",
                [vector1; start1; length1; length2])

    (* If we've already rewritten to slice_slice_concat, we can just drop the
       zero extension because it can do it *)
    | (E_aux (E_cast (_, (E_aux (E_app (Id_aux (Id "slice_slice_concat",_), args),_))),_))::
        ([] | [_;E_aux (E_id (Id_aux (Id "unsigned",_)),_)])
      -> E_app (mk_id "slice_slice_concat", args)

    | [E_aux (E_app (slice1, [vector1; start1; length1]),_)]
        when is_slice slice1 && not (is_constant length1) ->
       E_app (mk_id "zext_slice", [vector1; start1; length1])

    | _ -> E_app (id,args)

  else if is_id env (Id "SignExtend") id then
    let is_slice = is_id env (Id "slice") in
    match args with
    | [E_aux (E_app (slice1, [vector1; start1; length1]),_)]
        when is_slice slice1 && not (is_constant length1) ->
       E_app (mk_id "sext_slice", [vector1; start1; length1])

    | _ -> E_app (id,args)

  else if is_id env (Id "UInt") id then
    let is_slice = is_id env (Id "slice") in
    match args with
    | [E_aux (E_app (slice1, [vector1; start1; length1]),_)]
        when is_slice slice1 && not (is_constant length1) ->
       E_app (mk_id "UInt_slice", [vector1; start1; length1])

    | _ -> E_app (id,args)

  else E_app (id,args)

let rewrite_aux = function
  | (E_app (id,args),((_,Some (env,ty,_)) as annot)) ->
     E_aux (rewrite_app env ty (id,args),annot)
  | exp,annot -> E_aux (exp,annot)

let mono_rewrite defs =
  let open Rewriter in
  rewrite_defs_base
    { rewriters_base with
      rewrite_exp = fun _ -> fold_exp { id_exp_alg with e_aux = rewrite_aux } }
    defs
end

type options = {
  auto : bool;
  debug_analysis : int;
  rewrites : bool;
  rewrite_size_parameters : bool;
  all_split_errors : bool
}

let monomorphise opts splits env defs =
  let (defs,env) =
    if opts.rewrites then
      let defs = MonoRewrites.mono_rewrite defs in
    (* TODO: is this necessary? *)
      Type_check.check (Type_check.Env.no_casts Type_check.initial_env) defs
    else (defs,env)
  in
(*let _ = Pretty_print.pp_defs stdout defs in*)
  let new_splits =
    if opts.auto
    then Analysis.argset_to_list (Analysis.analyse_defs opts.debug_analysis env defs)
    else [] in
  let splits = new_splits @ (List.map (fun (loc,id) -> (loc,id,None)) splits) in
  let defs = split_defs opts.all_split_errors splits defs in
  (* TODO: stop if opts.all_split_errors && something went wrong *)
  (* TODO: currently doing this because constant propagation leaves numeric literals as
     int, try to avoid this later; also use final env for DEF_spec case above, because the
     type checker doesn't store the env at that point :( *)
  if opts.rewrite_size_parameters then
    let (defs,env) = Type_check.check (Type_check.Env.no_casts Type_check.initial_env) defs in
    let defs = AtomToItself.rewrite_size_parameters env defs in
    defs
  else
    defs
