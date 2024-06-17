open AST
open Machregs

module type ArchitectureInterface = sig
  val classes: int list

  val default_type_of_class: int -> AST.typ

  val class_of_reg: mreg -> int

  val no_spill_class: int

  val loc_result: AST.signature -> mreg AST.rpair

  val loc_arguments: AST.signature -> Locations.loc AST.rpair list

  val expand_mreg: mreg -> mreg AST.rpair

  val expand_loc: Locations.loc -> Locations.loc AST.rpair

  val worst: int -> int -> int

  val aliasing_classes: int -> int list

  val classes_alias: int -> int -> bool

  val regs_alias: mreg -> mreg -> bool

  val parallel_move_constraints: XTL.var list -> XTL.var list -> XTL.var list array * XTL.var list array

  val parallel_move_interfs_tmps: XTL.var list -> XTL.var list -> XTL.var list array
end

module DefaultInterface : ArchitectureInterface = struct
  let classes = [0; 1]

  let default_type_of_class = function
    | 0 -> Tint (* used in parallel moves only *)
    | 1 -> Tfloat
    | _ -> assert false

  let class_of_reg r =
    if Conventions1.is_float_reg r then 1 else 0

  let no_spill_class = 2

  let loc_result = Conventions1.loc_result

  let loc_arguments = Conventions1.loc_arguments

  let expand_mreg m = One m

  let expand_loc l = One l

  let aliasing_classes regclass = [regclass]

  let worst r1 r2 =
    match r1, r2 with
    | 0, 0 | 1, 1 -> 1
    | _, _ -> assert false

  let classes_alias class1 class2 = (class1 = class2)

  let regs_alias r1 r2 = (r1 = r2)

  let parallel_move_constraints srcs dsts = (Array.make 2 [], Array.make 2 [])

  let parallel_move_interfs_tmps srcs dsts = [|srcs@dsts; srcs@dsts|]

end
