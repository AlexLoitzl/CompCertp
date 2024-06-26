(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(*- E_COMPCERT_CODE_IRC_001 *)
(*- #Justify_Derived "Module IRC.ml is part of CompCert's register allocator. Computed results are later checked by a formally verified validator." *)

open Printf
open Camlcoq
open AST
open Registers
open Machregs
open Locations
open Conventions1
open XTL
open Machregsaux
open Machregsaux.AllocInterface

(* Iterated Register Coalescing: George and Appel's graph coloring algorithm *)

type var_stats = {
  mutable cost: int;             (* estimated cost of a spill *)
  mutable usedefs: int           (* number of uses and defs *)
}

(* Representation of the interference graph.  Each node of the graph
   (i.e. each variable) is represented as follows. *)

type node =
  { ident: int;                         (*r unique identifier *)
    typ: typ;                           (*r its type *)
    var: var;                           (*r the XTL variable it comes from *)
    regclass: int;                      (*r identifier of register class *)
    accesses: int;                      (*r number of defs and uses *)
    mutable spillcost: float;           (*r estimated cost of spilling *)
    mutable adjlist: node list;         (*r all nodes it interferes with *)
    mutable squeeze: int;
    mutable movelist: move list;        (*r list of moves it is involved in *)
    mutable extra_adj: node list;       (*r extra interferences (see below) *)
    mutable extra_pref: move list;      (*r extra preferences (see below) *)
    mutable coalesced: node option;         (*r [Some n] if coalesced with [n] *)
    mutable color: loc option;          (*r chosen color *)
    mutable nstate: nodestate;          (*r in which set of nodes it is *)
    mutable nprev: node;                (*r for double linking *)
    mutable nnext: node                 (*r for double linking *)
  }

(* These are the possible states for nodes. *)

and nodestate =
  | Colored
  | Initial
  | SimplifyWorklist
  | FreezeWorklist
  | SpillWorklist
  | CoalescedNodes
  | SelectStack

(* Each move (i.e. wish to be put in the same location) is represented
   as follows. *)

and move =
  { src: node;                          (*r source of the move *)
    dst: node;                          (*r destination of the move *)
    mutable mstate: movestate;          (*r in which set of moves it is *)
    mutable mprev: move;                (*r for double linking *)
    mutable mnext: move                 (*r for double linking *)
  }

(* These are the possible states for moves *)

and movestate =
  | CoalescedMoves
  | ConstrainedMoves
  | FrozenMoves
  | WorklistMoves
  | ActiveMoves

(* Note on "precolored" nodes and how they are handled:

The register allocator can express interferences and preferences between
any two values of type [var]: either pseudoregisters, to be colored by IRC,
or fixed, "precolored" locations.

I and P between two pseudoregisters are recorded in the graph that IRC
modifies, via the [adjlist] and [movelist] fields.

I and P between a pseudoregister and a machine register are also
recorded in the IRC graph, but only in the [adjlist] and [movelist]
fields of the pseudoregister.  This is the special case described
in George and Appel's papers.

I and P between a pseudoregister and a stack slot
are omitted from the IRC graph, as they contribute nothing to the
simplification and coalescing process.  We record them in the
[extra_adj] and [extra_pref] fields, where they can be honored
after IRC elimination, when assigning a stack slot to a spilled variable. *)

let name_of_loc = function
  | R r ->
      begin match Machregsnames.name_of_register r with
                | None -> "fixed-reg"
                | Some s -> s
      end
  | S (Local, ofs, ty) ->
      sprintf "L%c%ld" (PrintXTL.short_name_of_type ty) (camlint_of_coqint ofs)
  | S (Incoming, ofs, ty) ->
      sprintf "I%c%ld" (PrintXTL.short_name_of_type ty) (camlint_of_coqint ofs)
  | S (Outgoing, ofs, ty) ->
      sprintf "O%c%ld" (PrintXTL.short_name_of_type ty) (camlint_of_coqint ofs)

let name_of_node n =
  match n.var with
  | V(r, ty) -> sprintf "x%ld (%s)" (P.to_int32 r) (PrintAST.name_of_type ty)
  | L l -> name_of_loc l

(* The algorithm manipulates partitions of the nodes and of the moves
   according to their states, frequently moving a node or a move from
   a state to another, and frequently enumerating all nodes or all moves
   of a given state.  To support these operations efficiently,
   nodes or moves having the same state are put into imperative doubly-linked
   lists, allowing for constant-time insertion and removal, and linear-time
   scanning.  We now define the operations over these doubly-linked lists. *)

module DLinkNode = struct
  type t = node
  let make state =
    let rec empty =
      { ident = 0; typ = Tint; var = V(P.one, Tint); regclass = 0;
        adjlist = []; squeeze = 0; accesses = 0;
        spillcost = 0.0; movelist = [];
        extra_adj = []; extra_pref = [];
        coalesced = None; color = None;
        nstate = state; nprev = empty; nnext = empty }
    in empty
  let dummy = make Colored
  let notempty dl = dl.nnext != dl
  let insert n dl =
    n.nstate <- dl.nstate;
    n.nnext <- dl.nnext; n.nprev <- dl;
    dl.nnext.nprev <- n; dl.nnext <- n
  let remove n dl =
    assert (n.nstate = dl.nstate);
    n.nnext.nprev <- n.nprev; n.nprev.nnext <- n.nnext
  let move n dl1 dl2 =
    remove n dl1; insert n dl2
  let pick dl =
    let n = dl.nnext in remove n dl; n
  let iter f dl =
    let rec iter n = if n != dl then (f n; iter n.nnext)
    in iter dl.nnext
  let fold f dl accu =
    let rec fold n accu = if n == dl then accu else fold n.nnext (f n accu)
    in fold dl.nnext accu
end

module DLinkMove = struct
  type t = move
  let make state =
    let rec empty =
      { src = DLinkNode.dummy; dst = DLinkNode.dummy;
        mstate = state; mprev = empty; mnext = empty }
    in empty
  let dummy = make CoalescedMoves
  let notempty dl = dl.mnext != dl
  let insert m dl =
    m.mstate <- dl.mstate;
    m.mnext <- dl.mnext; m.mprev <- dl;
    dl.mnext.mprev <- m; dl.mnext <- m
  let remove m dl =
    assert (m.mstate = dl.mstate);
    m.mnext.mprev <- m.mprev; m.mprev.mnext <- m.mnext
  let move m dl1 dl2 =
    remove m dl1; insert m dl2
  let pick dl =
    let m = dl.mnext in remove m dl; m
end

(* Auxiliary data structures *)

module IntSet = Set.Make(struct
  type t = int
  let compare (x:int) (y:int) = compare x y
end)

module IntPairs = Hashtbl.Make(struct
    type t = int * int
    let equal ((x1, y1): (int * int)) (x2, y2) = x1 = x2 && y1 = y2
    let hash = Hashtbl.hash
  end)

(* The global state of the algorithm *)

type graph = {
  (* Machine registers available for allocation *)
  preferred_registers: mreg array array;
  remaining_registers: mreg array array;
  num_available_registers: int array;
  start_points: int array;
  allocatable_registers: mreg list;
  (* Costs for pseudo-registers *)
  stats_of_reg: reg -> var_stats;
  (* Mapping from XTL variables to nodes *)
  varTable: (var, node) Hashtbl.t;
  mutable nextIdent: int;
  (* The adjacency set  *)
  adjSet: unit IntPairs.t;
  (* Low-degree, non-move-related nodes *)
  simplifyWorklist: DLinkNode.t;
  (* Low-degree, move-related nodes *)
  freezeWorklist: DLinkNode.t;
  (* High-degree nodes *)
  spillWorklist: DLinkNode.t;
  (* Nodes that have been coalesced *)
  coalescedNodes: DLinkNode.t;
  (* Moves that have been coalesced *)
  coalescedMoves: DLinkMove.t;
  (* Moves whose source and destination interfere *)
  constrainedMoves: DLinkMove.t;
  (* Moves that will no longer be considered for coalescing *)
  frozenMoves: DLinkMove.t;
  (* Moves enabled for possible coalescing *)
  worklistMoves: DLinkMove.t;
  (* Moves not yet ready for coalescing *)
  activeMoves: DLinkMove.t
}

(* Register classes and reserved registers *)

(* We have two main register classes:
     0 for integer registers
     1 for floating-point registers
   plus a third pseudo-class 2 that has no registers and forces
   stack allocation.  XTL variables are mapped to classes 0 and 1
   according to their types.  A variable can be forced into class 2
   by giving it a negative spill cost. *)

let class_of_loc = function
  | R r -> class_of_reg r
  | S(_, _, ty) -> class_of_type ty

let rec remove_reserved = function
  | [] -> []
  | hd :: tl ->
      if List.mem hd !CPragmas.reserved_registers
      then remove_reserved tl
      else hd :: remove_reserved tl

(* We don't have overlapping classes (for now), just aliasing registers *)

 (* Reference implementation *)
(* let recompute_squeeze g n = min (bound g n.regclass) (raw_bounded_sum n) *)

(* Initialize and return an empty graph *)

let init costs =
  let aregs = allocatable_registers () in
  let preferred_regs = List.map remove_reserved aregs.preferred_regs in
  let remaining_regs = List.map remove_reserved aregs.remaining_regs in
  {
    preferred_registers = Array.of_list (List.map Array.of_list preferred_regs);
    remaining_registers = Array.of_list (List.map Array.of_list remaining_regs);
    num_available_registers =
      Array.of_list (List.map2 (fun l1 l2 -> List.length l1 + List.length l2) preferred_regs remaining_regs);
    start_points = Array.make (List.length preferred_regs) 0;
    allocatable_registers =
      List.concat preferred_regs @ (List.concat remaining_regs);
    stats_of_reg = costs;
    varTable = Hashtbl.create 253;
    nextIdent = 0;
    adjSet = IntPairs.create 997;
    simplifyWorklist = DLinkNode.make SimplifyWorklist;
    freezeWorklist = DLinkNode.make FreezeWorklist;
    spillWorklist = DLinkNode.make SpillWorklist;
    coalescedNodes = DLinkNode.make CoalescedNodes;
    coalescedMoves = DLinkMove.make CoalescedMoves;
    constrainedMoves = DLinkMove.make ConstrainedMoves;
    frozenMoves = DLinkMove.make FrozenMoves;
    worklistMoves = DLinkMove.make WorklistMoves;
    activeMoves = DLinkMove.make ActiveMoves
  }

(* Create nodes corresponding to XTL variables *)

let weightedSpillCost st =
  if st.cost < max_int
  then float_of_int st.cost
  else infinity

let newNodeOfReg g r ty =
  let st = g.stats_of_reg r in
  g.nextIdent <- g.nextIdent + 1;
  { ident = g.nextIdent; typ = ty;
    var = V(r, ty);
    regclass = if st.cost >= 0 then class_of_type ty else no_spill_class;
    accesses = st.usedefs;
    spillcost = weightedSpillCost st;
    adjlist = [];
    squeeze = if st.cost >= 0 then 0 else 1;
    movelist = []; extra_adj = []; extra_pref = [];
    coalesced = None;
    color = None;
    nstate = Initial;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let newNodeOfLoc g l =
  (* printf "newNodeOfLoc: %s\n" (name_of_loc l); *)
  let ty = Loc.coq_type l in
  g.nextIdent <- g.nextIdent + 1;
  { ident = g.nextIdent; typ = ty;
    var = L l; regclass = class_of_loc l;
    accesses = 0; spillcost = 0.0;
    adjlist = []; squeeze = 0; movelist = [];
    extra_adj = []; extra_pref = [];
    coalesced = None;
    color = Some l;
    nstate = Colored;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let nodeOfVar g v =
  try
    Hashtbl.find g.varTable v
  with Not_found ->
    let n =
      match v with V(r, ty) -> newNodeOfReg g r ty | L l -> newNodeOfLoc g l in
    Hashtbl.add g.varTable v n;
    n

(* Determine if two nodes interfere *)
let interfere g n1 n2 =
  let i1 = n1.ident and i2 = n2.ident in
  let p = if i1 < i2 then (i1, i2) else (i2, i1) in
  IntPairs.mem g.adjSet p

(* Add an edge to the graph. *)

let recordInterf g n1 n2 =
  match n2.color with
  | None | Some (R _) ->
      if classes_alias n1.regclass n2.regclass then begin
        n1.adjlist <- n2 :: n1.adjlist;
        n1.squeeze <- n1.squeeze + (worst n1.regclass n2.regclass);
      end else begin
        n1.extra_adj <- n2 :: n1.extra_adj
      end
  | Some (S _) ->
      (*i printf "extra adj %s to %s\n" (name_of_node n1) (name_of_node n2); *)
      n1.extra_adj <- n2 :: n1.extra_adj

let addEdge g n1 n2 =
  (*i printf "edge  %s -- %s;\n" (name_of_node n1) (name_of_node n2); *)
  assert (n1 != n2);
  if not (interfere g n1 n2) then begin
    let i1 = n1.ident and i2 = n2.ident in
    let p = if i1 < i2 then (i1, i2) else (i2, i1) in
    IntPairs.add g.adjSet p ();
    if n1.nstate <> Colored then recordInterf g n1 n2;
    if n2.nstate <> Colored then recordInterf g n2 n1
  end

(* Add a move preference. *)

let recordMove g n1 n2 =
  let m =
    { src = n1; dst = n2; mstate = WorklistMoves;
      mnext = DLinkMove.dummy; mprev = DLinkMove.dummy } in
  n1.movelist <- m :: n1.movelist;
  n2.movelist <- m :: n2.movelist;
  DLinkMove.insert m g.worklistMoves

let recordExtraPref n1 n2 =
  let m =
    { src = n1; dst = n2; mstate = FrozenMoves;
      mnext = DLinkMove.dummy; mprev = DLinkMove.dummy } in
  n1.extra_pref <- m :: n1.extra_pref

let recordExtraPref2 n1 n2 =
  let m =
    { src = n1; dst = n2; mstate = FrozenMoves;
      mnext = DLinkMove.dummy; mprev = DLinkMove.dummy } in
  n1.extra_pref <- m :: n1.extra_pref;
  n2.extra_pref <- m :: n2.extra_pref

let addMovePref g n1 n2 =
  match n1.color, n2.color with
  | None, None ->
      if n1.regclass = n2.regclass
      then recordMove g n1 n2
      else recordExtraPref2 n1 n2
  | Some (R mr1), None ->
      if List.mem mr1 g.allocatable_registers then recordMove g n1 n2
  | None, Some (R mr2) ->
      if List.mem mr2 g.allocatable_registers then recordMove g n1 n2
  | Some (S _), None ->
      recordExtraPref n2 n1
  | None, Some (S _) ->
      recordExtraPref n1 n2
  | _, _ ->
      ()

(* Apply the given function to the relevant adjacent nodes of a node *)

let iterAdjacent f n =
  List.iter
    (fun n ->
      match n.nstate with
      | SelectStack | CoalescedNodes -> ()
      | _ -> f n)
    n.adjlist

(* Determine the moves affecting a node *)

let moveIsActiveOrWorklist m =
  match m.mstate with
  | ActiveMoves | WorklistMoves -> true
  | _ -> false

let nodeMoves n =
  List.filter moveIsActiveOrWorklist n.movelist

(* Determine whether a node is involved in a move *)

let moveRelated n =
  List.exists moveIsActiveOrWorklist n.movelist

(* Initial partition of nodes into spill / freeze / simplify *)

let initialNodePartition g =
  let part_node n =
    match n.nstate with
    | Initial ->
        let k = g.num_available_registers.(n.regclass) in
        if n.squeeze >= k then
          DLinkNode.insert n g.spillWorklist
        else if moveRelated n then
          DLinkNode.insert n g.freezeWorklist
        else
          DLinkNode.insert n g.simplifyWorklist
    | Colored -> ()
    | _ -> assert false in
  Hashtbl.iter (fun _ a -> part_node a) g.varTable
  (* let nodes = Hashtbl.fold (fun _ n accu -> n :: accu) g.varTable [] in *)
  (* let nodes = List.sort (fun n1 n2 -> *)
  (*     let dcmp = compare n2.squeeze n1.squeeze in *)
  (*     if dcmp = 0 then compare n2.ident n1.ident else dcmp) nodes in *)
  (* List.iter part_node nodes *)

(* Check invariants *)
(* Degree Invariant does not hold if we have e.g. worst(c1, c2) <> 1 for some c1, c2 *)
(* let _degreeInvariant g n = *)
(*   let k = g.num_available_registers.(n.regclass) in *)
(*   let c = ref 0 in *)
(*   iterAdjacent (fun n -> incr c) n; *)
(*   if n.squeeze < k && !c <> n.squeeze then *)
(*     (printf "Degree: %d\n%!" !c; *)
(*     failwith("degree invariant violated by " ^ name_of_node n)) *)

let _simplifyWorklistInvariant g n =
  if n.squeeze < g.num_available_registers.(n.regclass)
  && not (moveRelated n)
  then ()
  else failwith("simplify worklist invariant violated by " ^ name_of_node n)

let _freezeWorklistInvariant g n =
  if n.squeeze < g.num_available_registers.(n.regclass)
  && moveRelated n
  then ()
  else
    failwith("freeze worklist invariant violated by " ^ name_of_node n)

let _spillWorklistInvariant g n =
  if n.squeeze >= g.num_available_registers.(n.regclass)
  then ()
  else failwith("spill worklist invariant violated by " ^ name_of_node n)

let _checkInvariants g =
  DLinkNode.iter
    (fun n -> _simplifyWorklistInvariant g n)
    g.simplifyWorklist;
  DLinkNode.iter
    (fun n -> _freezeWorklistInvariant g n)
    g.freezeWorklist;
  DLinkNode.iter
    (fun n -> _spillWorklistInvariant g n)
    g.spillWorklist

(* Enable moves that have become low-degree related *)

let enableMoves g n =
  List.iter
    (fun m ->
      if m.mstate = ActiveMoves
      then DLinkMove.move m g.activeMoves g.worklistMoves)
    (nodeMoves n)

(* NOTE Do this smarter... maybe return bool if change happened in squeezeChange *)
(* Simulate the removal of a node of class 'regclass' from the graph *)
let decrementDegree g regclass n =
  let k = g.num_available_registers.(n.regclass) in
  let old_squeeze = n.squeeze in
  n.squeeze <- n.squeeze - (worst n.regclass regclass);
  if n.squeeze < k && old_squeeze >= k then begin
    enableMoves g n;
    iterAdjacent (enableMoves g) n;
    if moveRelated n
    then DLinkNode.move n g.spillWorklist g.freezeWorklist
    else DLinkNode.move n g.spillWorklist g.simplifyWorklist
  end

(* Simulate the effect of combining nodes [n1] and [n3] on [n2],
   where [n2] is a node adjacent to [n3] with n3 in class regclass. *)

let combineEdge g regclass n1 n2 =
  assert (n1 != n2);
  if interfere g n1 n2 then begin
    (* The two edges n2--n3 and n2--n1 become one, so degree of n2 decreases *)
    decrementDegree g regclass n2
  end else begin
    (* Add new edge *)
    let i1 = n1.ident and i2 = n2.ident in
    let p = if i1 < i2 then (i1, i2) else (i2, i1) in
    IntPairs.add g.adjSet p ();
    if n1.nstate <> Colored then begin
      n1.adjlist <- n2 :: n1.adjlist;
      n1.squeeze <- n1.squeeze + (worst n1.regclass n2.regclass)
    end;
    if n2.nstate <> Colored then begin
      n2.adjlist <- n1 :: n2.adjlist;
      (* n2's degree stays the same because the old edge n2--n3 disappears
         and becomes the new edge n2--n1 *)
    end
  end

(* Simplification of a low-degree node *)

let simplify g =
  let n = DLinkNode.pick g.simplifyWorklist in
  (*i printf "Simplifying %s\n" (name_of_node n); *)
  n.nstate <- SelectStack;
  iterAdjacent (decrementDegree g n.regclass) n;
  n
(* Briggs's conservative coalescing criterion.  In the terminology of
   Hailperin, "Comparing Conservative Coalescing Criteria",
   TOPLAS 27(3) 2005, this is the full Briggs criterion, slightly
   more powerful than the one in George and Appel's paper. *)
let canCoalesceBriggs g u v =
  let seen = ref IntSet.empty in
  let k = g.num_available_registers.(u.regclass) in
  let c = ref 0 in
  let consider other n =
    if not (IntSet.mem n.ident !seen) then begin
      seen := IntSet.add n.ident !seen;
      (* if n interferes with both u and v, its degree will decrease by one
         after coalescing. We assume u and v have the same register class *)
      let degree_after_coalescing =
        if interfere g n other then n.squeeze - (worst n.regclass other.regclass) else n.squeeze in
      if degree_after_coalescing >= k || n.nstate = Colored then begin
        c := !c + worst other.regclass n.regclass;
        if !c >= k then raise Exit
      end
    end in
  try
    iterAdjacent (consider v) u;
    iterAdjacent (consider u) v;
    (*i printf "  Briggs: OK for %s and %s\n" (name_of_node u) (name_of_node v); *)
    true
  with Exit ->
    (*i printf "  Briggs: no\n"; *)
    false

(* George's conservative coalescing criterion: all high-degree neighbors
   of [v] are neighbors of [u]. *)

let canCoalesceGeorge g u v =
  let k = g.num_available_registers.(u.regclass) in
  let isOK t =
    if t.nstate = Colored then
      if u.nstate = Colored || interfere g t u then () else raise Exit
    else
      if t.squeeze < k || interfere g t u then () else raise Exit
  in
  try
    iterAdjacent isOK v;
    (*i printf "  George: OK for %s and %s\n" (name_of_node u) (name_of_node v); *)
    true
  with Exit ->
    (*i printf "  George: no\n"; *)
    false

(* The combined coalescing criterion.  [u] can be precolored, but
   [v] is not.  According to George and Appel's paper:
-  If [u] is precolored, use George's criterion.
-  If [u] is not precolored, use Briggs's criterion.

   As noted by Hailperin, for non-precolored nodes, George's criterion
   is incomparable with Briggs's: there are cases where G says yes
   and B says no.  Typically, [u] is a long-lived variable with many
   interferences, and [v] is a short-lived temporary copy of [u]
   that has no more interferences than [u].  Coalescing [u] and [v]
   is "weakly safe" in Hailperin's terminology: [u] is no harder to color,
   [u]'s neighbors are no harder to color either, but if we end up
   spilling [u], we'll spill [v] as well.  So, we restrict this heuristic
   to [v] having a small number of uses.
*)

let thresholdGeorge = 3

let canCoalesce g u v =
  (*i printf "canCoalesce %s[%.2f] %s[%.2f]\n"
     (name_of_node u) u.spillcost (name_of_node v) v.spillcost; *)
  if u.nstate = Colored
  then canCoalesceGeorge g u v
  else canCoalesceBriggs g u v
       || (u.spillcost < infinity && v.spillcost < infinity &&
            ((v.accesses <= thresholdGeorge && canCoalesceGeorge g u v)
             || (u.accesses <= thresholdGeorge && canCoalesceGeorge g v u)))

(* Update worklists after a move was processed *)

let addWorkList g u =
  if (not (u.nstate = Colored))
  && u.squeeze < g.num_available_registers.(u.regclass)
  && (not (moveRelated u))
  then DLinkNode.move u g.freezeWorklist g.simplifyWorklist

(* Return the canonical representative of a possibly coalesced node *)

let rec getCanonicalName n =
  match n.coalesced with None -> n | Some n' -> getCanonicalName n'

(* Combine two nodes *)

let combine g u v =
  (*i printf "Combining %s and %s\n" (name_of_node u) (name_of_node v); *)
  (*i if u.spillcost = infinity then
    printf "Warning: combining unspillable %s\n" (name_of_node u);
  if v.spillcost = infinity then
    printf "Warning: combining unspillable %s\n" (name_of_node v); *)
  if v.nstate = FreezeWorklist
  then DLinkNode.move v g.freezeWorklist g.coalescedNodes
  else DLinkNode.move v g.spillWorklist g.coalescedNodes;
  v.coalesced <- Some u;
  (* Precolored nodes often have big movelists, and if one of [u] and [v]
     is precolored, it is [u].  So, append [v.movelist] to [u.movelist]
     instead of the other way around. *)
  u.movelist <- List.rev_append v.movelist u.movelist;
  u.spillcost <- u.spillcost +. v.spillcost;
  iterAdjacent (combineEdge g v.regclass u) v;  (*r original code using [decrementDegree] is buggy *)
  if u.nstate <> Colored then begin
    u.extra_adj <- List.rev_append v.extra_adj u.extra_adj;
    u.extra_pref <- List.rev_append v.extra_pref u.extra_pref
  end;
  enableMoves g v;                   (*r added as per Appel's book erratum *)
  if u.squeeze >= g.num_available_registers.(u.regclass)
  && u.nstate = FreezeWorklist
  then DLinkNode.move u g.freezeWorklist g.spillWorklist

(* Consider the following situation:
    A - - - x0
            |
    B - - - x1
  where A, B are machine registers move-related ot x0, x1 respectively.
  If A and B alias, i.e. they are overlapping, we cannot coalesce both
  moves. This was previously called a constrained move, but now it's
  more expensive to check for *)

(* Attempt coalescing *)
let coalesce g =
  let check_alias r n =
    let x = getCanonicalName n in
    match x.color with
    | Some (R r') -> if regs_alias r r' then raise Exit
    | _ -> ()
  in
  let move_constrained g u v =
    match u.color with
    | Some (R r) -> begin try
                     iterAdjacent (check_alias r) v;
                     false
                    with Exit ->
                      true
                    end
    | _ -> false
  in
  let m = DLinkMove.pick g.worklistMoves in
  let x = getCanonicalName m.src and y = getCanonicalName m.dst in
  let (u, v) = if y.nstate = Colored then (y, x) else (x, y) in
  (*i printf "Attempt coalescing %s and %s\n" (name_of_node u) (name_of_node v); *)
  if u == v then begin
    DLinkMove.insert m g.coalescedMoves;
    addWorkList g u
  end else if v.nstate = Colored || interfere g u v || move_constrained g u v then begin
    DLinkMove.insert m g.constrainedMoves;
    addWorkList g u;
    addWorkList g v
  end else if canCoalesce g u v then begin
    DLinkMove.insert m g.coalescedMoves;
    combine g u v;
    addWorkList g u
  end else begin
    DLinkMove.insert m g.activeMoves
  end

(* Freeze moves associated with node [u] *)

let freezeMoves g u =
  let u' = getCanonicalName u in
  let freeze m =
    let y = getCanonicalName m.src in
    let v = if y == u' then getCanonicalName m.dst else y in
    DLinkMove.move m g.activeMoves g.frozenMoves;
    if not (moveRelated v)
    && v.squeeze < g.num_available_registers.(v.regclass)
    && v.nstate <> Colored
    then DLinkNode.move v g.freezeWorklist g.simplifyWorklist in
  List.iter freeze (nodeMoves u)

(* Pick a move and freeze it *)

let freeze g =
  let u = DLinkNode.pick g.freezeWorklist in
  (*i printf "Freezing %s\n" (name_of_node u); *)
  DLinkNode.insert u g.simplifyWorklist;
  freezeMoves g u

(* This is the original spill cost function from Chaitin 1982 *)

(*
let spillCost n =
  n.spillcost /. float n.degree
*)

(* This is spill cost function h_0 from Bernstein et al 1989.  It performs
   slightly better than Chaitin's and than functions h_1 and h_2. *)

(*
let spillCost n =
  let deg = float n.degree in n.spillcost /. (deg *. deg)
*)

(* Spill a node *)

let selectSpill g =
  (*i printf "Attempt spilling\n"; *)
  (* Find a spillable node of minimal cost *)
  let (n, cost) =
    DLinkNode.fold
      (fun n (best_node, best_cost as best) ->
        (* Manual inlining of [spillCost] above plus algebraic simplif *)
        let deg = float n.squeeze in (* TODO Different approach? *)
        let deg2 = deg *. deg in
        (* if n.spillcost /. deg2 <= best_cost *)
        if n.spillcost <= best_cost *. deg2
        then (n, n.spillcost /. deg2)
        else best)
      g.spillWorklist (DLinkNode.dummy, infinity) in
  assert (n != DLinkNode.dummy);
  if cost = infinity then begin
    printf "Warning: spilling unspillable %s\n" (name_of_node n);
    printf "  spill queue is:";
    DLinkNode.iter (fun n -> printf " %s" (name_of_node n)) g.spillWorklist;
    printf "\n"
  end;
  DLinkNode.remove n g.spillWorklist;
  (*i printf "Spilling %s\n" (name_of_node n); *)
  freezeMoves g n;
  n.nstate <- SelectStack;
  iterAdjacent (decrementDegree g n.regclass) n;
  n

(* Produce the order of nodes that we'll use for coloring *)

let rec nodeOrder g stack =
  (*  *_checkInvariants g; *)
  if DLinkNode.notempty g.simplifyWorklist then
    (let n = simplify g in nodeOrder g (n :: stack))
  else if DLinkMove.notempty g.worklistMoves then
    (coalesce g; nodeOrder g stack)
  else if DLinkNode.notempty g.freezeWorklist then
    (freeze g; nodeOrder g stack)
  else if DLinkNode.notempty g.spillWorklist then
    (let n = selectSpill g in nodeOrder g (n :: stack))
  else
    stack

(* Assign a color (i.e. a hardware register or a stack location)
   to a node.  The color is chosen among the colors that are not
   assigned to nodes with which this node interferes.  The choice
   is guided by the following heuristics: consider first the preferred
   hardware registers of the correct type; second the remaining
   registers; third the stack.
   For most architectures the preferred registers are the caller-save hardware
   register and the rest are the callee-save hardware registers.
   For some architectures these differ due other constraints.
   Non-preferred registers (which always include callee-save registers)
   and stack locations  are ``expensive'' resources,
   so we try to minimize their number by picking the smallest available
   callee-save register or stack location.  In contrast, preferred
   registers are ``free'', so we pick an available one pseudo-randomly. *)

module Regset =
  Set.Make(struct type t = mreg let compare = compare end)

let find_reg g conflicts regclass =
  let rec find avail curr last =
    if curr >= last then None else begin
      let r = avail.(curr) in
      if Regset.exists (regs_alias r) conflicts
      then find avail (curr + 1) last
      else Some (R r)
    end in
  let preferred_reg = g.preferred_registers.(regclass)
  and remaining_reg = g.remaining_registers.(regclass)
  and start = g.start_points.(regclass) in
  match find preferred_reg start (Array.length preferred_reg) with
  | Some _ as res ->
      g.start_points.(regclass) <-
        (if start + 1 < Array.length preferred_reg then start + 1 else 0);
      res
  | None ->
      match find preferred_reg 0 start with
      | Some _ as res ->
          g.start_points.(regclass) <-
            (if start + 1 < Array.length preferred_reg then start + 1 else 0);
          res
      | None ->
          find remaining_reg 0 (Array.length remaining_reg)

(* Aggressive coalescing of stack slots.  When assigning a slot,
   try first the slots assigned to the pseudoregs for which we
   have a preference, provided no conflict occurs. *)

let rec reuse_slot conflicts n mvlist =
  match mvlist with
  | [] -> None
  | mv :: rem ->
      let attempt_reuse n' =
        match n'.color with
        | Some(S(Local, _, _) as l)
          when List.for_all (Loc.diff_dec l) conflicts -> Some l
        | _ -> reuse_slot conflicts n rem in
      let src = getCanonicalName mv.src and dst = getCanonicalName mv.dst in
      if n == src then attempt_reuse dst
      else if n == dst then attempt_reuse src
      else reuse_slot conflicts n rem (* should not happen? *)

(* If no reuse possible, assign lowest nonconflicting stack slot. *)

let compare_slots s1 s2 =
  match s1, s2 with
  | S(_, ofs1, _), S(_, ofs2, _) -> Z.compare ofs1 ofs2
  | _, _ -> assert false

let align a b = (a + b - 1) land (-b)   (* assuming b is a power of 2 *)

let find_slot conflicts typ =
  let sz = Z.to_int (Locations.typesize typ) in
  let al = Z.to_int (Locations.typealign typ) in
  let rec find curr = function
  | [] ->
      S(Local, Z.of_uint curr, typ)
  | S(Local, ofs, typ') :: l ->
      let ofs = Z.to_int ofs in
      if curr + sz <= ofs then
        S(Local, Z.of_uint curr, typ)
      else begin
        let sz'  = Z.to_int (Locations.typesize typ') in
        let ofs' = align (ofs + sz') al in
        find (if ofs' <= curr then curr else ofs') l
      end
  | _ :: l ->
      find curr l
  in find 0 (List.stable_sort compare_slots conflicts)

(* Record locations assigned to interfering nodes *)

let record_reg_conflict cnf n =
  match (getCanonicalName n).color with
  | Some (R r) -> Regset.add r cnf
  | _ -> cnf

let record_slot_conflict cnf n =
  match (getCanonicalName n).color with
  | Some (S _ as l) -> l :: cnf
  | _ -> cnf

(* Assign a location, the best we can *)

let assign_color g n =
  let reg_conflicts =
    List.fold_left record_reg_conflict Regset.empty n.adjlist in
  (* First, try to assign a register *)
  match find_reg g reg_conflicts n.regclass with
  | Some loc ->
      n.color <- Some loc
  | None ->
      (* Add extra conflicts for nonallocatable and preallocated stack slots *)
      let slot_conflicts =
        List.fold_left record_slot_conflict
          (List.fold_left record_slot_conflict [] n.adjlist)
            n.extra_adj in
      (* Second, try to coalesce stack slots *)
      match reuse_slot slot_conflicts n (n.extra_pref @ n.movelist) with
      | Some loc ->
          n.color <- Some loc
      | None ->
          (* Last, pick a Local stack slot *)
          n.color <- Some (find_slot slot_conflicts n.typ)

(* Extract the location of a variable *)

let location_of_var g v =
  match v with
  | L l -> l
  | V(r, ty) ->
      try
        let n = Hashtbl.find g.varTable v in
        let n' = getCanonicalName n in
        match n'.color with
        | None -> assert false
        | Some l -> l
      with Not_found ->
      let dummy_regs = Array.of_list Conventions1.dummy_regs in
      let idx = class_of_type ty in
      if idx < Array.length dummy_regs
      then R (dummy_regs.(idx))
      else assert false

(* The exported interface *)

let add_interf g v1 v2 =
  let n1 = nodeOfVar g v1 in let n2 = nodeOfVar g v2 in addEdge g n1 n2

let add_pref g v1 v2 =
  let n1 = nodeOfVar g v1 in let n2 = nodeOfVar g v2 in addMovePref g n1 n2

let coloring g =
  (* printf "Coloring:\nTable: "; *)
  (* Hashtbl.iter (fun _ n -> printf "%s, " (name_of_node n)) g.varTable; *)
  initialNodePartition g;
  (* printf "\nInitial partition:\n SimplifyWorklist: "; *)
  (* DLinkNode.iter (fun n -> printf "%s, " (name_of_node n)) g.simplifyWorklist; *)
  (* printf "\n FreezeWorklist:"; *)
  (* DLinkNode.iter (fun n -> printf "%s, " (name_of_node n)) g.freezeWorklist; *)
  (* printf "\n SpillWorklist:"; *)
  (* DLinkNode.iter (fun n -> printf "%s, " (name_of_node n)) g.spillWorklist; *)
  (* printf "\n"; *)
  List.iter (assign_color g) (nodeOrder g []);
  location_of_var g  (* total function var -> location *)

(*- #End *)
