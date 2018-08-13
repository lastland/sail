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

(** The type checker API *)

open Ast
open Ast_util
module Big_int = Nat_big_num

(** [opt_tc_debug] controls the verbosity of the type checker. 0 is
   silent, 1 prints a tree of the type derivation and 2 is like 1 but
   with much more debugging information. *)
val opt_tc_debug : int ref

(** [opt_no_effects] turns of the effect checking. This can break
   re-writer passes, so it should only be used for debugging. *)
val opt_no_effects : bool ref

(** [opt_no_lexp_bounds_check] turns of the bounds checking in vector
   assignments in l-expressions. *)
val opt_no_lexp_bounds_check : bool ref

(** {2 Type errors} *)

type type_error =
  | Err_no_casts of unit exp * typ * typ * type_error * type_error list
  | Err_no_overloading of id * (id * type_error) list
  | Err_unresolved_quants of id * quant_item list
  | Err_subtype of typ * typ * n_constraint list * Ast.l KBindings.t
  | Err_no_num_ident of id
  | Err_other of string

exception Type_error of l * type_error;;

val typ_debug : string Lazy.t -> unit
val typ_print : string Lazy.t -> unit

(** {2 Environments} *)

(** The env module defines the internal type checking environment, and
   contains functions that operate on that state. *)
module Env : sig
  (** Env.t is the type of environments *)
  type t

  (** Note: Most get_ functions assume the identifiers exist, and throw
     type errors if it doesn't. *)

  (** Get the quantifier and type for a function identifier, freshening
      type variables. *)
  val get_val_spec : id -> t -> typquant * typ

  (** Like get_val_spec, except that the original type variables are used.
      Useful when processing the body of the function. *)
  val get_val_spec_orig : id -> t -> typquant * typ

  val update_val_spec : id -> typquant * typ -> t -> t

  val get_register : id -> t -> effect * effect * typ

  (** Return all the identifiers in an enumeration. Throws a type
     error if the enumeration doesn't exist. *)
  val get_enum : id -> t -> id list

  val is_enum : id -> t -> bool

  val get_locals : t -> (mut * typ) Bindings.t

  val add_local : id -> mut * typ -> t -> t

  (** Check if a local variable is mutable. Throws Type_error if it
     isn't a local variable. Probably best to use Env.lookup_id
     instead *)
  val is_mutable : id -> t -> bool

  (** Get the current set of constraints. *)
  val get_constraints : t -> n_constraint list

  val add_constraint : n_constraint -> t -> t

  val get_typ_var : kid -> t -> base_kind_aux

  val get_typ_vars : t -> base_kind_aux KBindings.t

  val get_typ_var_locs : t -> Ast.l KBindings.t

  val add_typ_var : Ast.l -> kid -> base_kind_aux -> t -> t

  val is_record : id -> t -> bool

  (** Returns record quantifiers and fields *)
  val get_record : id -> t -> typquant * (typ * id) list

  (** Return type is: quantifier, argument type, return type, effect *)
  val get_accessor : id -> id -> t -> typquant * typ * typ * effect

  (** If the environment is checking a function, then this will get
     the expected return type of the function. It's useful for
     checking or inserting early returns. Returns an option type and
     won't throw any exceptions. *)
  val get_ret_typ : t -> typ option

  val get_typ_synonym : id -> t -> (t -> typ_arg list -> typ)

  val get_overloads : id -> t -> id list

  val get_num_def : id -> t -> nexp

  val is_extern : id -> t -> string -> bool

  val get_extern : id -> t -> string -> string

  (** Lookup id searchs for a specified id in the environment, and
     returns it's type and what kind of identifier it is, using the
     lvar type. Returns Unbound if the identifier is unbound, and
     won't throw any exceptions. If the raw option is true, then look
     up the type without any flow typing modifiers. *)
  val lookup_id : ?raw:bool -> id -> t -> typ lvar

  val is_union_constructor : id -> t -> bool

  (** Check if the id is both a constructor, and the only constructor of that
      type. *)
  val is_singleton_union_constructor : id -> t -> bool

  val is_mapping : id -> t -> bool

  val is_register : id -> t -> bool

  (** Return a fresh kind identifier that doesn't exist in the
     environment. The optional argument bases the new identifer on the
     old one. *)
  val fresh_kid : ?kid:kid -> t -> kid

  val expand_synonyms : t -> typ -> typ

  (** Expand type synonyms and remove register annotations (i.e. register<t> -> t)) *)
  val base_typ_of : t -> typ -> typ

  (** no_casts removes all the implicit type casts/coercions from the
     environment, so checking a term with such an environment will
     guarantee not to insert any casts. Not that this is only about
     the implicit casting and has nothing to do with the E_cast AST
     node. *)
  val no_casts : t -> t

  (* Is casting allowed by the environment? *)
  val allow_casts : t -> bool

  val empty : t

  val pattern_completeness_ctx : t -> Pattern_completeness.ctx
end

(** Push all the type variables and constraints from a typquant into
   an environment *)
val add_typquant : Ast.l -> typquant -> Env.t -> Env.t

val destruct_exist : Env.t -> typ -> (kid list * n_constraint * typ) option

val add_existential : Ast.l -> kid list -> n_constraint -> Env.t -> Env.t

(** When the typechecker creates new type variables it gives them
   fresh names of the form 'fvXXX#name, where XXX is a number (not
   necessarily three digits), and name is the original name when the
   type variable was created by renaming an exisiting type variable to
   avoid shadowing. orig_kid takes such a type variable and strips out
   the 'fvXXX# part. It returns the type variable unmodified if it is
   not of this form. *)
val orig_kid : kid -> kid

(* Vector with default order. *)
val dvector_typ : Env.t -> nexp -> typ -> typ

val exist_typ : (kid -> n_constraint) -> (kid -> typ) -> typ

(** The type of type annotations *)
type tannot

(** The canonical view of a type annotation is that it is a tuple
   containing an environment (env), a type (typ), and an effect such
   that check_X env (strip_X X) typ succeeds, where X is typically exp
   (i.e an expression). Note that it is specifically not guaranteed
   that calling destruct_tannot followed by mk_tannot returns an
   identical type annotation. *)
val destruct_tannot : tannot -> (Env.t * typ * effect) option
val mk_tannot : Env.t -> typ -> effect -> tannot

val empty_tannot : tannot
val is_empty_tannot : tannot -> bool

val destruct_tannot : tannot -> (Env.t * typ * effect) option
val string_of_tannot : tannot -> string (* For debugging only *)
val replace_typ : typ -> tannot -> tannot

(** {2 Removing type annotations} *)

(** Strip the type annotations from an expression. *)
val strip_exp : 'a exp -> unit exp

(** Strip the type annotations from a pattern *)
val strip_pat : 'a pat -> unit pat

(** Strip the type annotations from a pattern-expression *)
val strip_pexp : 'a pexp -> unit pexp

(** Strip the type annotations from an l-expression *)
val strip_lexp : 'a lexp -> unit lexp

val strip_mpexp : 'a mpexp -> unit mpexp
val strip_mapcl : 'a mapcl -> unit mapcl

(* Strip location information from types for comparison purposes *)
val strip_typ : typ -> typ
val strip_typq : typquant -> typquant
val strip_id : id -> id
val strip_kid : kid -> kid
val strip_base_effect : base_effect -> base_effect
val strip_effect : effect -> effect
val strip_nexp_aux : nexp_aux -> nexp_aux
val strip_nexp : nexp -> nexp
val strip_n_constraint_aux : n_constraint_aux -> n_constraint_aux
val strip_n_constraint : n_constraint -> n_constraint
val strip_typ_aux : typ_aux -> typ_aux

(** {2 Checking expressions and patterns} *)

(** Check an expression has some type. Returns a fully annotated
   version of the expression, where each subexpression is annotated
   with it's type and the Environment used while checking it. The can
   be used to re-start the typechecking process on any
   sub-expression. so local modifications to the AST can be
   re-checked. *)
val check_exp : Env.t -> unit exp -> typ -> tannot exp

val infer_exp : Env.t -> unit exp -> tannot exp

val infer_pat : Env.t -> unit pat -> tannot pat * Env.t * unit exp list

val check_case : Env.t -> typ -> unit pexp -> typ -> tannot pexp

val check_fundef : Env.t -> 'a fundef -> tannot def list * Env.t

val check_val_spec : Env.t -> 'a val_spec -> tannot def list * Env.t

val prove : Env.t -> n_constraint -> bool

val solve : Env.t -> nexp -> Big_int.num option

val subtype_check : Env.t -> typ -> typ -> bool

val bind_pat : Env.t -> unit pat -> typ -> tannot pat * Env.t * unit Ast.exp list

(** Variant that doesn't introduce new guards for literal patterns,
   but raises a type error instead.  This should always be safe to use
   on patterns that have previously been type checked. *)
val bind_pat_no_guard : Env.t -> unit pat -> typ -> tannot pat * Env.t

val typ_error : Ast.l -> string -> 'a

(** {2 Destructuring type annotations} Partial functions: The
   expressions and patterns passed to these functions must be
   guaranteed to have tannots of the form Some (env, typ) for these to
   work. *)

val env_of : tannot exp -> Env.t
val env_of_annot : Ast.l * tannot -> Env.t

val typ_of : tannot exp -> typ
val typ_of_annot : Ast.l * tannot -> typ


val pat_typ_of : tannot pat -> typ
val pat_env_of : tannot pat -> Env.t

val typ_of_pexp : tannot pexp -> typ
val env_of_pexp : tannot pexp -> Env.t

val typ_of_mpat : tannot mpat -> typ
val env_of_mpat : tannot mpat -> Env.t

val typ_of_mpexp : tannot mpexp -> typ
val env_of_mpexp : tannot mpexp -> Env.t

val effect_of : tannot exp -> effect
val effect_of_pat : tannot pat -> effect
val effect_of_annot : tannot -> effect
val add_effect_annot : tannot -> effect -> tannot

(** {2 Utilities } *)

val destruct_atom_nexp : Env.t -> typ -> nexp option

(** Safely destructure an existential type. Returns None if the type
   is not existential. This function will pick a fresh name for the
   existential to ensure that no name-clashes occur. *)
val destruct_exist : Env.t -> typ -> (kid list * n_constraint * typ) option

val destruct_range : Env.t -> typ -> (kid list * n_constraint * nexp * nexp) option

val destruct_numeric : Env.t -> typ -> (kid list * n_constraint * nexp) option

val destruct_vector : Env.t -> typ -> (nexp * order * typ) option

type uvar =
  | U_nexp of nexp
  | U_order of order
  | U_typ of typ

val string_of_uvar : uvar -> string

val subst_unifiers : uvar KBindings.t -> typ -> typ

val typ_subst_nexp : kid -> nexp_aux -> typ -> typ
val typ_subst_typ : kid -> typ_aux -> typ -> typ
val typ_subst_order : kid -> order_aux -> typ -> typ
val typ_subst_kid : kid -> kid -> typ -> typ

val unify : l -> Env.t -> typ -> typ -> uvar KBindings.t * kid list * n_constraint option

val alpha_equivalent : Env.t -> typ -> typ -> bool

(** Throws Invalid_argument if the argument is not a E_app expression *)
val instantiation_of : tannot exp -> uvar KBindings.t

(** Doesn't use the type of the expression when calculating instantiations.
    May fail if the arguments aren't sufficient to calculate all unifiers. *)
val instantiation_of_without_type : tannot exp -> uvar KBindings.t

(* Type variable instantiations that inference will extract from constraints *)
val instantiate_simple_equations : quant_item list -> uvar KBindings.t

val propagate_exp_effect : tannot exp -> tannot exp

val propagate_pexp_effect : tannot pexp -> tannot pexp * effect

(** {2 Checking full AST} *)

(** Fully type-check an AST

Some invariants that will hold of a fully checked AST are:

 - No internal nodes, such as E_internal_exp, or E_comment nodes.

 - E_vector_access nodes and similar will be replaced by function
   calls E_app to vector access functions. This is different to the
   old type checker.

 - Every expressions type annotation [tannot] will be Some (typ, env).

 - Also every pattern will be annotated with the type it matches.

 - Toplevel expressions such as typedefs and some subexpressions such
   as letbinds may have None as their tannots if it doesn't make sense
   for them to have type annotations.

   check throws type_errors rather than Sail generic errors from
   Reporting_basic. For a function that uses generic errors, use
   Type_error.check *)
val check : Env.t -> 'a defs -> tannot defs * Env.t

(** The initial type checking environment *)
val initial_env : Env.t
