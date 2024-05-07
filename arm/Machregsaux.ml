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

open AST
open Machregs
open Locations
open ArchitectureInterface
(** Auxiliary functions on machine registers *)

let is_scratch_register s =  s = "R14"  || s = "r14"

 (* Function to get the target specific register class for AST types.
   We have two main register classes:
     0 for integer registers
     1 for floating-point registers
   plus a third pseudo-class 2 that has no registers and forces
   stack allocation. *)

let class_of_type = function
  | Tint | Tlong -> 0
  | Tsingle -> 1
  | Tfloat -> 2
  | Tany32 -> 0
  | Tany64 -> assert false

let is_callee_save' = function
| R0 -> false
| R1 -> false
| R2 -> false
| R3 -> false
| R12 -> false
| D0 -> false
| D1 -> false
| D2 -> false
| D3 -> false
| D4 -> false
| D5 -> false
| D6 -> false
| D7 -> false
| ErrorReg -> false
| _ -> true

let interferes_caller_save tv mr = not (is_callee_save' mr)

module AllocInterface : ArchitectureInterface = struct
  let classes = [0; 1; 2]


  let default_type_of_class = function
  | 0 -> Tint (* used for parallel moves only *)
  | 1 -> Tsingle
  | 2 -> Tfloat
  | _ -> assert false

  let class_of_reg = function
    | R0  | R1  | R2  | R3
    | R4  | R5  | R6  | R7
    | R8  | R9  | R10 | R11
    | R12 -> 0
    | F0  | F1  | F2  | F3
    | F4  | F5  | F6  | F7
    | F8  | F9  | F10 | F11
    | F12 | F13 | F14 | F15
    | F16 | F17 | F18 | F19
    | F20 | F21 | F22 | F23
    | F24 | F25 | F26 | F27
    | F28 | F29 | F30 | F31 -> 1
    | D0  | D1  | D2  | D3
    | D4  | D5  | D6  | D7
    | D8  | D9  | D10 | D11
    | D12 | D13 | D14 | D15 -> 2
    | ErrorReg -> 3

  let no_spill_class = 3

  let use_double_reg p =
    match p with
    | One _ -> p
    | Two (F1, F0) -> One D0
    | Two (F3, F2) -> One D1
    | Two (F5, F4) -> One D2
    | Two (F7, F6) -> One D3
    | Two (F9, F8) -> One D4
    | Two (F11, F10) -> One D5
    | Two (F13, F12) -> One D6
    | Two (F15, F14) -> One D7
    | Two (F17, F16) -> One D8
    | Two (F19, F18) -> One D9
    | Two (F21, F20) -> One D10
    | Two (F23, F22) -> One D11
    | Two (F25, F24) -> One D12
    | Two (F27, F26) -> One D13
    | Two (F29, F28) -> One D14
    | Two (F31, F30) -> One D15
    | Two _ -> p

  let loc_result s =
    match use_double_reg (Conventions1.loc_result s) with
    | One ErrorReg -> assert false
    | x -> x

  let use_double_loc p =
    match p with
    | One _ -> p
    | Two (R F1, R F0) -> One (R D0)
    | Two (R F3, R F2) -> One (R D1)
    | Two (R F5, R F4) -> One (R D2)
    | Two (R F7, R F6) -> One (R D3)
    | Two (R F9, R F8) -> One (R D4)
    | Two (R F11, R F10) -> One (R D5)
    | Two (R F13, R F12) -> One (R D6)
    | Two (R F15, R F14) -> One (R D7)
    | Two (R F17, R F16) -> One (R D8)
    | Two (R F19, R F18) -> One (R D9)
    | Two (R F21, R F20) -> One (R D10)
    | Two (R F23, R F22) -> One (R D11)
    | Two (R F25, R F24) -> One (R D12)
    | Two (R F27, R F26) -> One (R D13)
    | Two (R F29, R F28) -> One (R D14)
    | Two (R F31, R F30) -> One (R D15)
    | Two _ -> p

  let rec check_any64 = function
    | [] -> ()
    | Tany64 :: _ -> assert false
    | _ :: tys -> check_any64 tys

  let loc_arguments s =
    check_any64 s.sig_args;
    List.map use_double_loc (Conventions1.loc_arguments s)

  let expand_mreg l =
    match l with
    | D0 -> Two (F1, F0)
    | D1 -> Two (F3, F2)
    | D2 -> Two (F5, F4)
    | D3 -> Two (F7, F6)
    | D4 -> Two (F9, F8)
    | D5 -> Two (F11, F10)
    | D6 -> Two (F13, F12)
    | D7 -> Two (F15, F14)
    | D8 -> Two (F17, F16)
    | D9 -> Two (F19, F18)
    | D10 -> Two (F21, F20)
    | D11 -> Two (F23, F22)
    | D12 -> Two (F25, F24)
    | D13 -> Two (F27, F26)
    | D14 -> Two (F29, F28)
    | D15 -> Two (F31, F30)
    | mr -> One mr

  let expand_loc l =
    match l with
    | Locations.S _ -> One l
    | R r -> map_rpair (fun r -> R r) (expand_mreg r)

  let aliasing_classes = function
    | 1 -> [1; 2]
    | 2 -> [1; 2]
    | x -> [x]

  let worst class1 class2 =
    match class1, class2 with
    | 0, 0 | 1, 1 | 2, 2 -> 1
    | 2, 1 -> 1
    | 1, 2 -> 2
    | _, _ -> assert false

  let classes_alias class1 class2 =
    match class1, class2 with
    | 1, 2 | 2, 1 -> true
    | _, _ -> (class1 = class2)

  let overlapping_regs = function
    | F0 -> [D0]   | F1 -> [D0]   | F2 -> [D1]   | F3 -> [D1]
    | F4 -> [D2]   | F5 -> [D2]   | F6 -> [D3]   | F7 -> [D3]
    | F8 -> [D4]   | F9 -> [D4]   | F10 -> [D5]  | F11 -> [D5]
    | F12 -> [D6]  | F13 -> [D6]  | F14 -> [D7]  | F15 -> [D7]
    | F16 -> [D8]  | F17 -> [D8]  | F18 -> [D9]  | F19 -> [D9]
    | F20 -> [D10] | F21 -> [D10] | F22 -> [D11] | F23 -> [D11]
    | F24 -> [D12] | F25 -> [D12] | F26 -> [D13] | F27 -> [D13]
    | F28 -> [D14] | F29 -> [D14] | F30 -> [D15] | F31 -> [D15]
    | D0 -> [F0; F1] | D1 -> [F2; F3] | D2 -> [F4; F5] | D3 -> [F6; F7]
    | D4 -> [F8; F9] | D5 -> [F10; F11] | D6 -> [F12; F13] | D7 -> [F14; F15]
    | D8 -> [F16; F17] | D9 -> [F18; F19] | D10 -> [F20; F21] | D11 -> [F22; F23]
    | D12 -> [F24; F25] | D13 -> [F26; F27] | D14 -> [F28; F29] | D15 -> [F30; F31]
    | _ -> []

  let regs_alias r1 r2 =
    r1 = r2
    || List.mem r1 (overlapping_regs r2)
    || List.mem r2 (overlapping_regs r1)

  let exclusion_sets regs =
    let idx r =
    match class_of_reg r with
    | 0 -> 0
    | 1 -> 2
    | 2 -> 1
    | _ -> 0
      in
    let add_regs s rs =
      List.fold_left (fun s' r -> MregSet.add r s') s rs
      in
    let a = Array.make 3 MregSet.empty in
    List.iter (fun r -> a.(idx r) <- (add_regs a.(idx r) (overlapping_regs r))) regs;
    a
end
