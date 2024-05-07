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

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Values.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers
  ([Fxx]).

  The type [mreg] does not include reserved machine registers
  such as the stack pointer, the link register, and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R0: mreg  | R1: mreg  | R2: mreg  | R3: mreg
  | R4: mreg  | R5: mreg  | R6: mreg  | R7: mreg
  | R8: mreg  | R9: mreg  | R10: mreg | R11: mreg
  | R12: mreg
  (** Allocatable single-precision float regs *)
  | F0: mreg  | F1: mreg  | F2: mreg  | F3: mreg
  | F4: mreg  | F5: mreg  | F6: mreg  | F7: mreg
  | F8: mreg  | F9: mreg  | F10: mreg | F11: mreg
  | F12: mreg | F13: mreg | F14: mreg | F15: mreg
  | F16: mreg | F17: mreg | F18: mreg | F19: mreg
  | F20: mreg | F21: mreg | F22: mreg | F23: mreg
  | F24: mreg | F25: mreg | F26: mreg | F27: mreg
  | F28: mreg | F29: mreg | F30: mreg | F31: mreg
  (** Allocatable double-precision float regs
      - Note that we do not model any aliasing,
        they can not be translated into pregs and are only used
        in XTL during Register Allocation *)
  | D0: mreg  | D1: mreg  | D2: mreg  | D3: mreg
  | D4: mreg  | D5: mreg  | D6: mreg  | D7: mreg
  | D8: mreg  | D9: mreg  | D10: mreg | D11: mreg
  | D12: mreg | D13: mreg | D14: mreg | D15: mreg
  (** Error Register for handling calling convention for pairs *)
  | ErrorReg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
     R0  :: R1  :: R2  :: R3 :: R4  :: R5  :: R6  :: R7
  :: R8  :: R9  :: R10 :: R11 :: R12
  :: F0  :: F1  :: F2  :: F3  :: F4  :: F5  :: F6  :: F7
  :: F8  :: F9  :: F10 :: F11 :: F12 :: F13 :: F14 :: F15
  :: F16 :: F17 :: F18 :: F19 :: F20 :: F21 :: F22 :: F23
  :: F24 :: F25 :: F26 :: F27 :: F28 :: F29 :: F30 :: F31
  :: D0  :: D1  :: D2  :: D3  :: D4  :: D5  :: D6  :: D7
  :: D8  :: D9  :: D10 :: D11 :: D12 :: D13 :: D14 :: D15
  :: ErrorReg :: nil.

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Global Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.

Global Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ :=
  match r with
  | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8
  | D9 | D10 | D11 | D12 | D13 | D14 | D15 => Tany64
  | ErrorReg => Tany64
  | _ => Tany32
  end.

Definition mreg_pair_type (p: rpair mreg): typ :=
  match p with
  | One r => mreg_type r
  | _ => Tany64
  end.

Lemma pair_words_type:
  forall rlo rhi v,
    Val.has_type v (mreg_pair_type (Two rhi rlo)) ->
    Val.has_type (Val.hiword v) (mreg_type rhi)
    /\ Val.has_type (Val.loword v) (mreg_type rlo).
Proof.
  intros. split.
  destruct v; auto; destruct rhi; easy.
  destruct v; auto; destruct rlo; easy.
Qed.

Lemma words_pair_type:
  forall rlo rhi v1 v2,
    Val.has_type v1 (mreg_type rhi) ->
    Val.has_type v2 (mreg_type rlo) ->
    Val.has_type (Val.combine v1 v2) (mreg_pair_type (Two rhi rlo)).
Proof.
  intros. assert (mreg_pair_type (Two rhi rlo) = Tany64) by (destruct rhi, rlo; auto).
  rewrite H1. destruct (Val.combine v1 v2); exact I.
Qed.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1  | R1 => 2  | R2 => 3  | R3 => 4
    | R4 => 5  | R5 => 6  | R6 => 7  | R7 => 8
    | R8 => 9  | R9 => 10 | R10 => 11 | R11 => 12
    | R12 => 13
    | F0 => 14  | F1 => 15  | F2 => 16  | F3 => 17
    | F4 => 18  | F5 => 19  | F6 => 20  | F7 => 21
    | F8 => 22  | F9 => 23  | F10 => 24 | F11 => 25
    | F12 => 26 | F13 => 27 | F14 => 28 | F15 => 29
    | F16 => 30 | F17 => 31 | F18 => 32 | F19 => 33
    | F20 => 34 | F21 => 35 | F22 => 36 | F23 => 37
    | F24 => 38 | F25 => 39 | F26 => 40 | F27 => 41
    | F28 => 42 | F29 => 43 | F30 => 44 | F31 => 45
    | D0 => 46  | D1 => 47  | D2 => 48  | D3 => 49
    | D4 => 50  | D5 => 51  | D6 => 52  | D7 => 53
    | D8 => 54  | D9 => 55  | D10 => 56 | D11 => 57
    | D12 => 58 | D13 => 59 | D14 => 60 | D15 => 61
    | ErrorReg => 62
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
  ("R0", R0)   :: ("R1", R1)   :: ("R2", R2)   :: ("R3", R3)   ::
  ("R4", R4)   :: ("R5", R5)   :: ("R6", R6)   :: ("R7", R7)   ::
  ("R8", R8)   :: ("R9", R9)   :: ("R10", R10) :: ("R11", R11) ::
  ("R12", R12) ::
  ("F0", F0)   :: ("F1", F1)   :: ("F2", F2)   :: ("F3", F3)   ::
  ("F4", F4)   :: ("F5", F5)   :: ("F6", F6)   :: ("F7", F7)   ::
  ("F8", F8)   :: ("F9", F9)   :: ("F10", F10) :: ("F11", F11) ::
  ("F12", F12) :: ("F13", F13) :: ("F14", F14) :: ("F15", F15) ::
  ("F16", F16) :: ("F17", F17) :: ("F18", F18) :: ("F19", F19) ::
  ("F20", F20) :: ("F21", F21) :: ("F22", F22) :: ("F23", F23) ::
  ("F24", F24) :: ("F25", F25) :: ("F26", F26) :: ("F27", F27) ::
  ("F28", F28) :: ("F29", F29) :: ("F30", F30) :: ("F31", F31) ::
  ("D0", D0)   :: ("D1", D1)   :: ("D2", D2)   :: ("D3", D3)   ::
  ("D4", D4)   :: ("D5", D5)   :: ("D6", D6)   :: ("D7", D7)   ::
  ("D8", D8)   :: ("D9", D9)   :: ("D10", D10) :: ("D11", D11) ::
  ("D12", D12) :: ("D13", D13) :: ("D14", D14) :: ("D15", D15) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Odiv | Odivu =>
             if Archi.hardware_idiv tt then
              nil
             else
              R0 :: R1 :: R2 :: R3 :: R12 :: F0  :: F1  :: F2  :: F3  :: F4  :: F5
                 :: F6 :: F7 :: F8 :: F9  :: F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: nil
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle => F12 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al => R2 :: R3 :: R12 :: F7 :: nil
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg :=
  R12 :: nil.

Definition destroyed_at_indirect_call: list mreg :=
  R0 :: R1 :: R2 :: R3 :: nil.

Definition temp_for_parent_frame: mreg :=
  R12.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Odiv | Odivu => if Archi.hardware_idiv tt then (nil, None) else (Some R0 :: Some R1 :: nil, Some R0)
  | _ => (nil, None)
  end.

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  (nil, nil).

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    destroyed_at_indirect_call
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are none for ARM. *)

Definition two_address_op (op: operation) : bool :=
  false.

Global Opaque two_address_op.

(* Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
