open Type_check
open Ast
open Ast_util
open State
open Format
open List

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
     fprintf o "@\n@[| r%s -> bits(%u)@]" (get_id_string r.regid) r.reglen;
     pp_regval_rec o regs'

let pp_regval o regs =
  fprintf o "@\n@[<hov 2>let regval (n : reg_t) : Type0 =@ match n with";
  pp_regval_rec o regs;
  fprintf o "@]@\n"

let pp_defs_fstar (defs_file,defs_modules) regs defs top_line =
  let o = formatter_of_out_channel defs_file in
  fprintf o "@[let@ n_reg_t@ :@ pos = %u@]@\n" (length regs);
  pp_regnames o regs 0;
  pp_n_regtype o regs;
  pp_regval o regs;
  pp_print_flush o ()
