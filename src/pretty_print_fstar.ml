open Type_check
open Ast
open Ast_util

let pp_defs_fstar (defs_file,defs_modules) defs top_line =
  Pretty_print_sail.pp_defs defs_file defs
