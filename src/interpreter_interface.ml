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

open Ast
open Ast_util

open Prompt_monad
open Bytecode
open Interpreter2
open Value2

let rec get_functions = function
  | CDEF_fundef (id, _, _, _) :: cdefs -> id :: get_functions cdefs
  | _ :: cdefs -> get_functions cdefs

let get_extern tc_env id =
  let open Type_check in
  if Env.is_extern id tc_env "interpreter" then
    Some (Env.get_extern id tc_env "interpreter")
  else
    None

type graph_node = G_node of int * string * string

module Node = struct
  type t = graph_node
  let compare gn1 gn2 =
    match gn1, gn2 with
    | G_node (id1, _, _), G_node (id2, _, _) -> compare id1 id2
end

module NM = Map.Make(Node)
module NS = Set.Make(Node)

type execution_graph = NS.t NM.t

let graph = ref NM.empty
                            
let node_counter = ref 0

let new_node color str =
  let n = G_node (!node_counter, color, str) in
  incr node_counter;
  n

let add_link from_node to_node graph =
  try
    NM.add from_node (NS.add to_node (NM.find from_node graph)) graph
  with
  | Not_found -> NM.add from_node (NS.singleton to_node) graph

let leaves graph =
  List.fold_left (fun acc (from_node, to_nodes) -> NS.filter (fun to_node -> Node.compare to_node from_node != 0) (NS.union acc to_nodes))
                 NS.empty
                 (NM.bindings graph)

(* Ensure that all leaves exist in the graph *)
let fix_leaves graph =
  NS.fold (fun leaf graph -> if NM.mem leaf graph then graph else NM.add leaf NS.empty graph) (leaves graph) graph

let make_dot file graph =
  Util.opt_colors := false;
  let to_string = function
    | G_node (n, _, str) -> String.escaped (string_of_int n ^ ". " ^ str)
  in
  let node_color = function
    | G_node (_, color, _) -> color
  in
  let edge_color from_node to_node =
    match from_node, to_node with
    | _, _ -> "black"
  in
  let out_chan = open_out (file ^ ".gv") in
  output_string out_chan "digraph DEPS {\n";
  let make_node from_node =
    output_string out_chan (Printf.sprintf "  \"%s\" [fillcolor=%s;style=filled];\n" (to_string from_node) (node_color from_node))
  in
  let make_line from_node to_node =
    output_string out_chan (Printf.sprintf "  \"%s\" -> \"%s\" [color=%s];\n" (to_string from_node) (to_string to_node) (edge_color from_node to_node))
  in
  NM.bindings graph |> List.iter (fun (from_node, _) -> make_node from_node);
  NM.bindings graph |> List.iter (fun (from_node, to_nodes) -> NS.iter (make_line from_node) to_nodes);
  output_string out_chan "}\n";
  Util.opt_colors := true;
  close_out out_chan
          
let run k =
  let rec run_outcome from = function
    | Done v ->
       let node = new_node "olivedrab1" "Done" in
       graph := add_link from node !graph;
       
    | Print (str, k) ->
       let node = new_node "lightpink" str in
       graph := add_link from node !graph;
       run_outcome node k
                   
    | Undefined k ->
       let node = new_node "azure" "Choice" in
       graph := add_link from node !graph;
       run_outcome node (k true);
       run_outcome node (k false)
                   
    | Error str ->
       let node = new_node "orange1" ("Error " ^ str) in
       graph := add_link from node !graph
                         
    | _ -> failwith "Unimplemented"
  in
  node_counter := 0;
  let node = new_node "peachpuff" "Start" in
  run_outcome node k;
  fix_leaves !graph;
  make_dot "run" !graph;
