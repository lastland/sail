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

(** Graph library similar to Map and Set in standard library *)

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

module type S =
  sig
    type node
    type t
    val empty : t
    val add_edge : node -> node -> t -> t
    exception Not_a_DAG of node * t;;
    val topsort : t -> node list
    val visualize : node_label:(node -> string)
                    -> node_color:(node -> string)
                    -> edge_color:(node -> node -> string)
                    -> out_channel
                    -> string
                    -> t
                    -> unit
  end

module Make(Ord : OrderedType) =
  struct
    module NM = Map.Make(Ord)
    module NS = Set.Make(Ord)

    type node = Ord.t
    type t = NS.t NM.t

    let empty = NM.empty

    let leaves graph =
      List.fold_left (fun acc (from_node, to_nodes) -> NS.filter (fun to_node -> Ord.compare to_node from_node != 0) (NS.union acc to_nodes))
                     NS.empty
                     (NM.bindings graph)

    let fix_leaves graph =
      NS.fold (fun leaf graph -> if NM.mem leaf graph then graph else NM.add leaf NS.empty graph) (leaves graph) graph

    let add_edge from_node to_node graph =
      try
        NM.add from_node (NS.add to_node (NM.find from_node graph)) graph
      with
      | Not_found -> NM.add from_node (NS.singleton to_node) graph

    (** Visualise a graph to an output channel in graphviz format. *)
    let visualize ~node_label:node_label ~node_color:node_color ~edge_color:edge_color out_chan name graph =
      let graph = fix_leaves graph in
      let make_node node =
        output_string out_chan (Printf.sprintf "  \"%s\" [fillcolor=%s;style=filled];\n" (node_label node) (node_color node))
      in
      let make_edge from_node to_node =
        output_string out_chan (Printf.sprintf "  \"%s\" -> \"%s\" [color=%s];\n" (node_label from_node) (node_label to_node) (edge_color from_node to_node))
      in
      (* Temporarily switch colours off, so we don't end up with terminal colour codes in graphviz output *)
      let using_colors = !Util.opt_colors in
      Util.opt_colors := false;
      output_string out_chan ("digraph " ^ name ^ " {\n");
      NM.bindings graph |> List.iter (fun (from_node, _) -> make_node from_node);
      NM.bindings graph |> List.iter (fun (from_node, to_nodes) -> NS.iter (make_edge from_node) to_nodes);
      output_string out_chan "}\n";
      Util.opt_colors := using_colors

    (** Return all the nodes reachable from a node in root, without
       going through a node in cuts. *)
    let reachable roots cuts graph =
      let visited = ref NS.empty in
      let rec reachable' node =
        if NS.mem node !visited then ()
        else if NS.mem node cuts then visited := NS.add node !visited
        else
          begin
            visited := NS.add node !visited;
            let children =
              try NM.find node graph with
              | Not_found -> NS.empty
            in
            NS.iter reachable' children
          end
      in
      NS.iter reachable' roots; !visited

    (** Prune a graph so it only contains nodes reachable from roots,
       stopping at cuts *)
    let prune roots cuts graph =
      let rs = reachable roots cuts graph in
      fix_leaves (NM.filter (fun fn _ -> NS.mem fn rs) graph)

    let reverse_graph graph =
      let rgraph = ref NM.empty in
      let find_default n graph = try NM.find n graph with Not_found -> NS.empty in

      NM.iter (fun a -> NS.iter (fun b -> rgraph := NM.add b (NS.add a (find_default b !rgraph)) !rgraph)) graph;
      fix_leaves !rgraph

    let prune_loop node graph =
      let down = prune (NS.singleton node) NS.empty graph in
      let up = prune (NS.singleton node) NS.empty (reverse_graph down) in
      reverse_graph up

    exception Not_a_DAG of Ord.t * t;;

    let topsort graph =
      let graph = fix_leaves graph in
      let marked = Hashtbl.create (NM.cardinal graph) in
      let temp_marked = ref NS.empty in
      let list = ref [] in
      let keys = NM.bindings graph |> List.map fst in
      let find_unmarked keys = List.find (fun node -> not (Hashtbl.mem marked node)) keys in

      let rec visit node =
        if NS.mem node !temp_marked
        then raise (let loop = prune_loop node graph in Not_a_DAG (node, loop))
        else if Hashtbl.mem marked node
        then ()
        else
          begin
            let children =
              try NM.find node graph with
              | Not_found -> NS.empty
            in
            temp_marked := NS.add node !temp_marked;
            NS.iter (fun child -> visit child) children;
            Hashtbl.add marked node ();
            temp_marked := NS.remove node !temp_marked;
            list := node :: !list
          end
      in

      let rec topsort' () =
        try
          let unmarked = find_unmarked keys in
          visit unmarked; topsort' ()
        with
        | Not_found -> ()

      in topsort' (); !list
  end
