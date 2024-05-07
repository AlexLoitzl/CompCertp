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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import Decidableplus.
Require Import AST.
Require Import Events.
Require Import Locations.
Require Import Compopts.
Require Archi.
Require Import Values.
Require Import Floats.
Require Import Integers.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Temporaries used for spilling, reloading, and parallel move operations.
- Allocatable registers, that can be assigned to RTL pseudo-registers.
  These are further divided into:
-- Callee-save registers, whose value is preserved across a function call.
-- Caller-save registers that can be modified during a function call.

  We follow the ARM application binary interface (EABI) in our choice
  of callee- and caller-save registers.
*)

Definition is_callee_save (r: mreg): bool :=
  match r with
  | R0  | R1  | R2  | R3  | R12 => false
  | R4  | R5  | R6  | R7  | R8  | R9  | R10 | R11 => true
  | F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15 => false
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31 => true
  | D0  | D1  | D2  | D3  | D4  | D5  | D6  | D7 => false
  | D8  | D9  | D10 | D11 | D12 | D13 | D14 | D15 => true
  | ErrorReg => false
  end.

Definition int_caller_save_regs :=
  R0 :: R1 :: R2 :: R3 :: R12 :: nil.

Definition float_caller_save_regs :=
  F0 :: F1 :: F2  :: F3  :: F4  :: F5  :: F6  :: F7  :: F8
     :: F9 :: F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: nil.

Definition int_callee_save_regs :=
  R4 :: R5 :: R6 :: R7 :: R8 :: R9 :: R10 :: R11 :: nil.

Definition float_callee_save_regs :=
  F16 :: F17 :: F18 :: F19 :: F20 :: F21 :: F22 :: F23 :: F24
      :: F25 :: F26 :: F27 :: F28 :: F29 :: F30 :: F31 :: nil.

Definition destroyed_at_call :=
  (* D0 :: D1 :: D2 :: D3 :: D4 :: D5 :: D6 :: D7 :: int_caller_save_regs ++ float_caller_save_regs. *)
  List.filter (fun r => negb (is_callee_save r) && negb (mreg_eq ErrorReg r)) all_mregs.

Definition dummy_regs := R0 :: F0 :: D0 :: nil. (**r Used in [Coloring]. *)

Definition callee_save_type := mreg_type.
  
Definition is_float_reg (r: mreg): bool :=
  match r with
  | R0  | R1  | R2  | R3
  | R4  | R5  | R6  | R7
  | R8  | R9  | R10 | R11 | R12 => false
  | F0  | F1  | F2  | F3  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11 | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31 => true
  | D0  | D1  | D2  | D3  | D4  | D5  | D6  | D7
  | D8  | D9  | D10 | D11 | D12 | D13 | D14 | D15 => false (* ? *)
  | ErrorReg => false
  end.

(** How to use registers for register allocation.
    In classic ARM mode, we favor the use of caller-save registers,
    using callee-save registers only when no caller-save is available.
    In Thumb mode, we additionally favor integer registers R0 to R3 over the other
    integer registers, as they lead to more compact instruction encodings. *)

Record alloc_regs := mk_alloc_regs {
  preferred_regs: list (list mreg);
  remaining_regs: list (list mreg)
}.

Definition allocatable_registers (_ : unit) :=
  let preferred_single_regs := float_caller_save_regs in
  let remaining_single_regs := float_callee_save_regs in
  let preferred_double_regs := D0 :: D1 :: D2 :: D3 :: D4 :: D5 :: D6 :: D7 :: nil in
  let remaining_double_regs := D8 :: D9 :: D10 :: D11 :: D12 :: D13 :: D14 :: D15 :: nil in
  let preferred_int_regs := if thumb tt then R0 :: R1 :: R2 :: R3 :: nil else int_caller_save_regs in
  let remaining_int_regs := if thumb tt then R4 :: R5 :: R6 :: R7 :: R12 :: R8 :: R9 :: R10 :: R11 :: nil
                                        else int_callee_save_regs in
  {| preferred_regs := preferred_int_regs :: preferred_single_regs :: preferred_double_regs :: nil :: nil;
     remaining_regs := remaining_int_regs :: remaining_single_regs :: remaining_double_regs :: nil :: nil |}.

(* Definition allocatable_registers (_ : unit) := *)
(*   if thumb tt then *)
(*   {| preferred_int_regs := R0 :: R1 :: R2 :: R3 :: nil; *)
(*      remaining_int_regs := R4 :: R5 :: R6 :: R7 :: R12 :: R8 :: R9 :: R10 :: R11 :: nil; *)
(*      preferred_float_regs := float_caller_save_regs; *)
(*      remaining_float_regs := float_callee_save_regs |} *)
(*   else *)
(*   {| preferred_int_regs := int_caller_save_regs; *)
(*      remaining_int_regs := int_callee_save_regs; *)
(*      preferred_float_regs := float_caller_save_regs; *)
(*      remaining_float_regs := float_callee_save_regs |}. *)

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.  *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [R0] or [F0] or [R0,R1], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result.

  For the "softfloat" convention, results of FP types should be passed
  in [R0] or [R0,R1].  This doesn't fit the CompCert register model,
  so we have code in [arm/TargetPrinter.ml] that inserts additional moves
  to/from [F0].

  Concerning endianness for 64bit values in register pairs, the contents
  of the registers is as if the value had been loaded from memory
  representation with a single LDM instruction. *)

Definition loc_result (s: signature) : rpair mreg :=
  match proj_sig_res s with
  | Tint | Tany32 => One R0
  | Tany64 => One ErrorReg
  | Tfloat => Two F1 F0
  | Tsingle => One F0
  | Tlong => if Archi.big_endian
             then Two R0 R1
             else Two R1 R0
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (mreg_pair_type (loc_result sig)) = true.
Proof.
  intros. unfold loc_result. destruct (proj_sig_res sig); destruct Archi.big_endian; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros.
  unfold loc_result. destruct (proj_sig_res s); destruct Archi.big_endian; simpl; auto.
Qed.

(** If the result is in a pair of registers, those registers are distinct and have type [Tint] at least. *)

Lemma loc_result_pair:
  forall sg,
  match loc_result sg with
  | One _ => True
  | Two r1 r2 =>
        r1 <> r2
     /\ ((proj_sig_res sg = Tlong /\ Archi.ptr64 = false /\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true)
          \/ proj_sig_res sg = Tfloat /\ subtype Tsingle (mreg_type r1) = true /\ subtype Tsingle (mreg_type r2) = true)
  end.
Proof.
  intros; unfold loc_result; destruct (proj_sig_res sg); auto. intuition congruence.
  destruct Archi.big_endian; intuition congruence.
Qed.

(** The location of the result depends only on the result part of the signature *)

Lemma loc_result_exten:
  forall s1 s2, s1.(sig_res) = s2.(sig_res) -> loc_result s1 = loc_result s2.
Proof.
  intros. unfold loc_result, proj_sig_res. rewrite H; auto.
Qed.

(** ** Location of function arguments *)

(** For the "hardfloat" configuration, we use the following calling conventions,
    adapted from the ARM EABI-HF:
- The first 4 integer arguments are passed in registers [R0] to [R3].
- The first 2 long integer arguments are passed in an aligned pair of
  two integer registers.
- The first 8 single- and double-precision float arguments are passed
  in registers [F0...F7]
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer or single argument, 2 words for a float
  or a long), starting at word offset 0.

This convention is not quite that of the ARM EABI-HF, whereas single float
arguments are passed in 32-bit float registers.  Unfortunately,
this does not fit the data model of CompCert.  In [PrintAsm.ml]
we insert additional code around function calls that moves
data appropriately. *)

Definition int_param_regs :=
  R0 :: R1 :: R2 :: R3 :: nil.

Definition float_param_regs :=
  F0 :: F1 :: F2  :: F3  :: F4  :: F5  :: F6  :: F7  :: F8
     :: F9 :: F10 :: F11 :: F12 :: F13 :: F14 :: F15 :: nil.

Definition ireg_param (n: Z) : mreg :=
  match list_nth_z int_param_regs n with Some r => r | None => R0 end.

Definition freg_param (n: Z) : mreg :=
  match list_nth_z float_param_regs n with Some r => r | None => F0 end.

Fixpoint loc_arguments_hf
     (tyl: list typ) (ir fr sr ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint | Tany32) as ty :: tys =>
      if zlt ir 4
      then One (R (ireg_param ir)) :: loc_arguments_hf tys (ir + 1) fr sr ofs
      else One (S Outgoing ofs ty) :: loc_arguments_hf tys ir fr sr (ofs + 1)
  | Tfloat :: tys =>
      let sr := if zeq (fr mod 2) 0 then 0 else fr in
      let fr := align fr 2 in
      if zlt fr 16
      then Two (R (freg_param (fr + 1))) (R (freg_param fr)) :: loc_arguments_hf tys ir (fr + 2) sr ofs
      else let ofs := align ofs 2 in
           One (S Outgoing ofs Tfloat) :: loc_arguments_hf tys ir fr sr (ofs + 2)
  | Tany64 as ty :: tys => (* TODO This should never happen? Put it in ErrorReg? *)
      let ofs := align ofs 2 in
      One (S Outgoing ofs ty) :: loc_arguments_hf tys ir fr sr (ofs + 2)
  | Tsingle :: tys =>
      let p := if zlt 0 sr then sr else fr in
      let fr' := if zlt 0 sr then fr else fr + 1 in
      if zlt p 16
      then One (R (freg_param p)) :: loc_arguments_hf tys ir fr' 0 ofs
      else One (S Outgoing ofs Tsingle) :: loc_arguments_hf tys ir fr sr (ofs + 1)
  | Tlong :: tys =>
      let ohi := if Archi.big_endian then 0 else 1 in
      let olo := if Archi.big_endian then 1 else 0 in
      let ir := align ir 2 in
      if zlt ir 4
      then Two (R (ireg_param (ir + ohi))) (R (ireg_param (ir + olo))) :: loc_arguments_hf tys (ir + 2) fr sr ofs
      else let ofs := align ofs 2 in
           Two (S Outgoing (ofs + ohi) Tint) (S Outgoing (ofs + olo) Tint) :: loc_arguments_hf tys ir fr sr (ofs + 2)
  end.

(** For the "softfloat" configuration, as well as for variable-argument functions
  in the "hardfloat" configuration, we use the default ARM EABI (not HF)
  calling conventions:
- The first 4 integer arguments are passed in registers [R0] to [R3].
- The first 2 long integer arguments are passed in an aligned pair of
  two integer registers.
- The first 2 double-precision float arguments are passed in [F0] or [F2]
- The first 4 single-precision float arguments are passed in [F0...F3]
- Integer arguments and float arguments are kept in sync so that
  they can all be mapped back to [R0...R3] in [PrintAsm.ml].
- Extra arguments are passed on the stack, in [Outgoing] slots, consecutively
  assigned (1 word for an integer or single argument, 2 words for a float
  or a long), starting at word offset 0.

This convention is not quite that of the ARM EABI, whereas every float
argument are passed in one or two integer registers.  Unfortunately,
this does not fit the data model of CompCert.  In [PrintAsm.ml]
we insert additional code around function calls and returns that moves
data appropriately. *)

Fixpoint loc_arguments_sf
     (tyl: list typ) (ir: Z) (ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | (Tint|Tany32) as ty :: tys =>
      if zlt ir 4
      then One (R (ireg_param ir)) :: loc_arguments_sf tys (ir+1) ofs
      else One (S Outgoing ofs ty) :: loc_arguments_sf tys ir (ofs+1)
  | Tfloat :: tys =>
      let ir := align ir 2 in (* TODO If fixing Asmexpand multiplication shouldn't be necessary *)
      let ir' := 2 * ir in
      if zlt ir 4
      then Two (R (freg_param (ir' + 1))) (R (freg_param ir')) :: loc_arguments_sf tys (ir + 2) ofs
      else let ofs := align ofs 2 in
           One (S Outgoing ofs Tfloat) :: loc_arguments_sf tys ir (ofs + 2)
  | Tlong :: tys =>
      let ohi := if Archi.big_endian then 0 else 1 in
      let olo := if Archi.big_endian then 1 else 0 in
      let ir := align ir 2 in
      if zlt ir 4
      then Two (R (ireg_param (ir+ohi))) (R (ireg_param (ir+olo))) :: loc_arguments_sf tys (ir+2) ofs
      else let ofs := align ofs 2 in
           Two (S Outgoing (ofs+ohi) Tint) (S Outgoing (ofs+olo) Tint) :: loc_arguments_sf tys ir (ofs+2)
  | Tany64 :: tys =>
      let ofs := align ofs 2 in
      One (S Outgoing ofs Tany64) :: loc_arguments_sf tys ir (ofs+2)
  | Tsingle :: tys =>
      if zlt ir 4
      then One (R (freg_param ir)) :: loc_arguments_sf tys (ir+1) ofs
      else One (S Outgoing ofs Tsingle) :: loc_arguments_sf tys ir (ofs+1)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  match Archi.abi with
  | Archi.Softfloat =>
      loc_arguments_sf s.(sig_args) 0 0
  | Archi.Hardfloat =>
      if s.(sig_cc).(cc_vararg)
      then loc_arguments_sf s.(sig_args) 0 0
      else loc_arguments_hf s.(sig_args) 0 0 0 0
  end.

(** Argument locations are either non-temporary registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Definition loc_argument_charact (ofs: Z) (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs' ty => ofs' >= ofs /\ typealign ty = 1
  | _ => False
  end.

Remark ireg_param_caller_save: forall n, is_callee_save (ireg_param n) = false.
Proof.
  unfold ireg_param; intros.
  assert (A: forall r, In r int_param_regs -> is_callee_save r = false) by decide_goal.
  destruct (list_nth_z int_param_regs n) as [r|] eqn:NTH.
  apply A. eapply list_nth_z_in; eauto.
  auto.
Qed.

Remark freg_param_caller_save: forall n, is_callee_save (freg_param n) = false.
Proof.
  unfold freg_param; intros.
  assert (A: forall r, In r float_param_regs -> is_callee_save r = false) by decide_goal.
  destruct (list_nth_z float_param_regs n) as [r|] eqn:NTH.
  apply A. eapply list_nth_z_in; eauto.
  auto.
Qed.

Remark loc_arguments_hf_charact:
  forall tyl ir fr sr ofs p,
  In p (loc_arguments_hf tyl ir fr sr ofs) -> forall_rpair (loc_argument_charact ofs) p.
Proof.
  assert (X: forall ofs1 ofs2 l, loc_argument_charact ofs2 l -> ofs1 <= ofs2 -> loc_argument_charact ofs1 l).
  { destruct l; simpl; intros; auto. destruct sl; auto. intuition lia. }
  assert (Y: forall ofs1 ofs2 p, forall_rpair (loc_argument_charact ofs2) p -> ofs1 <= ofs2 -> forall_rpair (loc_argument_charact ofs1) p).
  { destruct p; simpl; intuition eauto. }
  induction tyl; simpl loc_arguments_hf; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (zlt ir 4); destruct H.
  subst. apply ireg_param_caller_save.
  eapply IHtyl; eauto.
  subst. split; [lia | auto].
  eapply Y; eauto. lia.
- (* float *)
  set (fr' := align fr 2) in *.
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct (zlt fr' 16); destruct H.
  subst. simpl. split; apply freg_param_caller_save.
  eapply IHtyl; eauto.
  subst. split. apply Z.le_ge. apply align_le. lia. auto.
  eapply Y; eauto. apply Z.le_trans with (align ofs 2). apply align_le; lia. lia.
- (* long *)
  set (ir' := align ir 2) in *.
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct (zlt ir' 4).
  destruct H. subst p. split; apply ireg_param_caller_save.
  eapply IHtyl; eauto.
  destruct H. subst p. split; destruct Archi.big_endian; (split; [ lia | auto ]).
  eapply Y. eapply IHtyl; eauto. lia.
- (* single *)
  Destructor; destruct H.
  destruct (zlt 0 sr); destruct (zlt fr 16); destruct H;
    try (subst; eapply freg_param_caller_save).
  eapply IHtyl; eauto.
  subst. eapply freg_param_caller_save.
  eapply IHtyl; eauto.
  subst. simpl. lia.
  eapply Y; eauto. lia.
  subst. simpl. lia.
  eapply Y; eauto. lia.
- (* any32 *)
  destruct (zlt ir 4); destruct H.
  subst. apply ireg_param_caller_save.
  eapply IHtyl; eauto.
  subst. split; [lia | auto].
  eapply Y; eauto. lia.
- (* any64 *)
  destruct H.
  subst. split. apply Z.le_ge. apply align_le. lia. auto.
  eapply Y; eauto. apply Z.le_trans with (align ofs 2). apply align_le; lia. lia.
Qed.

Remark loc_arguments_sf_charact:
  forall tyl ofs p ir,
  In p (loc_arguments_sf tyl ir ofs ) -> forall_rpair (loc_argument_charact ofs) p.
Proof.
  assert (X: forall ofs1 ofs2 l, loc_argument_charact ofs2 l -> ofs1 <= ofs2 -> loc_argument_charact ofs1 l).
  { destruct l; simpl; intros; auto. destruct sl; auto. intuition extlia. }
  assert (Y: forall ofs1 ofs2 p, forall_rpair (loc_argument_charact ofs2) p -> ofs1 <= ofs2 -> forall_rpair (loc_argument_charact ofs1) p).
  { destruct p; simpl; intuition eauto. }
  induction tyl; simpl loc_arguments_sf; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (zlt ir 4); destruct H.
  subst. apply ireg_param_caller_save.
  eapply IHtyl; eauto.
  subst. split; [lia | auto].
  eapply Y; eauto. lia.
- (* float *)
  set (ir' := align ir 2) in *.
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct (zlt ir' 4); destruct H.
  subst. simpl. split; apply freg_param_caller_save.
  eapply IHtyl; eauto.
  subst. split. apply Z.le_ge. apply align_le. lia. auto.
  eapply Y; eauto. apply Z.le_trans with (align ofs 2). apply align_le; lia. lia.
- (* long *)
  set (ir' := align ir 2) in *.
  assert (ofs <= align ofs 2) by (apply align_le; lia).
  destruct (zlt ir' 4).
  destruct H. subst p. split; apply ireg_param_caller_save.
  eapply IHtyl; eauto.
  destruct H. subst p. split; destruct Archi.big_endian; (split; [ lia | auto ]).
  eapply Y. eapply IHtyl; eauto. lia.
- (* single *)
  destruct (zlt ir 4); destruct H.
  subst. apply freg_param_caller_save.
  eapply IHtyl; eauto.
  subst. split; [lia | auto].
  eapply Y; eauto. lia.
- (* any32 *)
  destruct (zlt ir 4); destruct H.
  subst. apply ireg_param_caller_save.
  eapply IHtyl; eauto.
  subst. split; [lia | auto].
  eapply Y; eauto. lia.
- (* any64 *)
  destruct H.
  subst. split. apply Z.le_ge. apply align_le. lia. auto.
  eapply Y; eauto. apply Z.le_trans with (align ofs 2). apply align_le; lia. lia.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  assert (X: forall l, loc_argument_charact 0 l -> loc_argument_acceptable l).
  { unfold loc_argument_charact, loc_argument_acceptable.
    destruct l as [r | [] ofs ty]; auto. intros (A & B); split; auto. rewrite B; apply Z.divide_1_l. }
  assert (Y: forall p, forall_rpair (loc_argument_charact 0) p -> forall_rpair loc_argument_acceptable p).
  { destruct p0; simpl; intuition auto. }
  assert (In p (loc_arguments_sf (sig_args s) 0 0) -> forall_rpair loc_argument_acceptable p).
  { intros. exploit loc_arguments_sf_charact; eauto. }
  assert (In p (loc_arguments_hf (sig_args s) 0 0 0 0) -> forall_rpair loc_argument_acceptable p).
  { intros. exploit loc_arguments_hf_charact; eauto. }
  destruct Archi.abi; [ | destruct (cc_vararg (sig_cc s)) ]; auto.
Qed.

Global Hint Resolve loc_arguments_acceptable: locs.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  unfold loc_arguments.
  destruct Archi.abi; reflexivity.
Qed.

(** ** Normalization of function results and parameters *)

(** No normalization needed. *)

Definition return_value_needs_normalization (t: rettype) := false.
Definition parameter_needs_normalization (t: rettype) := false.
