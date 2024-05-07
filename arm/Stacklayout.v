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

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import Memory Separation.
Require Import Bounds.
Require Import AST.
Require Import Machregs.
Require Import FunInd.

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Pointer to activation record of the caller.
- Saved return address into caller.
- Local stack slots.
- Saved values of callee-save registers used by the function.
- Space for the stack-allocated data declared in Cminor.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)

Open Scope Z.

Definition fe_ofs_arg := 0.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition is_aligned (r: mreg) :=
  match r with
  | F16 | F18 | F20 | F22
  | F24 | F26 | F28 | F30 => true
  | _ => false
  end.

Definition valid_pair (r1 r2: mreg) :=
  match r1, r2 with
  | F17, F16 | F19, F18 | F21, F20
  | F23, F22 | F25, F24 | F27, F26
  | F29, F28 | F31, F30 => true
  | _, _ => false
  end.

Function pair_pairs (l: list mreg) {measure length l}: list (rpair mreg) :=
  match l with
  | r1 :: r2 :: l => if valid_pair r2 r1
                    then Two r2 r1 :: (pair_pairs l)
                    else One r1 :: (pair_pairs (r2 :: l))
  | r :: nil => One r :: nil
  | nil => nil
  end.
Proof.
  - intros. simpl. auto.
  - intros. simpl. auto.
Qed.

Definition align_pairs (l: list mreg) :=
  match l with
  | nil => nil
  | r :: l' => if is_aligned r
              then pair_pairs l
              else (One r) :: pair_pairs l'
  end.

Definition callee_save_pairs (l: list mreg) : list (rpair mreg) :=
  let (float_regs, int_regs) := partition Conventions1.is_float_reg l in
  (map (fun r => One r) int_regs) ++ (align_pairs float_regs).

Lemma pair_pairs_in_iff:
  forall l r, In r l <-> In r (regs_of_rpairs (pair_pairs l)).
Proof.
  intro.
  functional induction (pair_pairs l).
  - split; simpl; intros. rewrite IHl0 in H; intuition. rewrite <- IHl0 in H; intuition.
  - split; simpl; intros. simpl in IHl0. rewrite IHl0 in H; intuition. rewrite <- IHl0 in H; intuition.
  - simpl. easy.
  - simpl. easy.
Qed.

Corollary align_pairs_in_iff:
  forall l r, In r l <-> In r (regs_of_rpairs (align_pairs l)).
Proof.
  intros. destruct l. easy.
  unfold align_pairs. destruct (is_aligned m).
  apply pair_pairs_in_iff.
  simpl. apply or_iff_compat_l. apply pair_pairs_in_iff.
Qed.

Remark map_one_in_iff:
  forall l (r:mreg), In r l <-> In r (regs_of_rpairs (map (fun r0 => One r0) l)).
Proof.
  induction l; intros; simpl. easy.
  split; intros; destruct H; auto; right; apply IHl; auto.
Qed.

Lemma callee_save_pairs_in_iff:
  forall l r, In r l <-> In r (regs_of_rpairs (callee_save_pairs l)).
Proof.
  intros. unfold callee_save_pairs. destruct (partition _) eqn:E.
  rewrite regs_of_rpairs_app. rewrite in_app.
  rewrite <- map_one_in_iff. rewrite <- align_pairs_in_iff. rewrite or_comm.
  eapply elements_in_partition; eauto.
Qed.

Lemma pair_pairs_well_formed:
  forall l p, list_norepet l -> In p (pair_pairs l) -> pair_wf p.
Proof.
  intro. functional induction (pair_pairs l).
  - intros. destruct H0; inv H; auto. destruct r1, r2; simpl in e0; try discriminate; split; auto; discriminate.
    inv H4. auto.
  - intros. destruct H0. inv H0. simpl. auto. inv H. auto.
  - intros. destruct H0. rewrite <- H0. simpl. auto. contradiction.
  - intros. contradiction.
Qed.

Remark map_one_well_formed:
  forall l p, In p (map (fun r => One r) l) -> pair_wf p.
Proof.
  induction l. intros. contradiction.
  intros. destruct H; auto. rewrite <- H. simpl. auto.
Qed.

Program Definition make_env (b: bounds) :=
  let olink := 4 * b.(bound_outgoing) in  (* back link*)
  let ora := olink + 4 in (* return address *)
  let ol := align (ora + 4) 8 in    (* locals *)
  let ocs := ol + 4 * b.(bound_local) in (* callee-saves *)
  let ostkdata := align (size_callee_save_area_rec (callee_save_pairs (b.(used_callee_save))) ocs) 8 in (* retaddr *)
  let sz := align (ostkdata + b.(bound_stack_data)) 8 in
  {| fe_size := sz;
     fe_ofs_link := olink;
     fe_ofs_retaddr := ora;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := callee_save_pairs b.(used_callee_save) |}.
Next Obligation.
  eapply (used_callee_save_prop b). eapply callee_save_pairs_in_iff; auto.
Qed.

Lemma callee_save_correspond:
  forall r b , In r b.(used_callee_save) <-> In r (regs_of_rpairs ((make_env b).(fe_used_callee_save))).
Proof.
  intros. simpl. apply callee_save_pairs_in_iff.
Qed.

Lemma callee_save_well_formed:
  forall b p, In p (make_env b).(fe_used_callee_save) -> pair_wf p.
Proof.
  simpl. intros.
  unfold callee_save_pairs in H. destruct (partition _) eqn:E. rewrite in_app in H. destruct H.
  eapply map_one_well_formed; eauto.
  exploit list_norepet_partition; eauto. exact (used_callee_save_norepet b). intros.
  destruct l. simpl in H. contradiction. unfold align_pairs in H. destruct (is_aligned _).
  eapply pair_pairs_well_formed; eauto. eapply H0.  destruct H. rewrite <- H. simpl. auto. eapply pair_pairs_well_formed; eauto.
  destruct H0. inv H0. auto.
Qed.

(** Separation property *)

Local Open Scope sep_scope.

Lemma frame_env_separated:
  forall b sp m P,
  let fe := make_env b in
  m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
  m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
       ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
       ** range sp (fe_ofs_link fe) (fe_ofs_link fe + 4)
       ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + 4)
       ** range sp (fe_ofs_callee_save fe) (size_callee_save_area fe (fe_ofs_callee_save fe))
       ** P.
Proof.
Local Opaque Z.add Z.mul sepconj range.
  intros; simpl.
  set (olink := 4 * b.(bound_outgoing));
  set (ora := olink + 4);
  set (ol := align (ora + 4) 8);
  set (ocs := ol + 4 * b.(bound_local));
  set (ostkdata := align (size_callee_save_area fe ocs) 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= olink) by (unfold olink; lia).
  assert (olink <= ora) by (unfold ora; lia).
  assert (ora + 4 <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area fe ocs) by apply size_callee_save_area_incr.
  assert (size_callee_save_area fe ocs <= ostkdata) by (apply align_le; lia).
(* Reorder as:
     outgoing
     back link
     retaddr
     local
     callee-save *)
  rewrite sep_swap12.
  rewrite sep_swap23.
  rewrite sep_swap34.
(* Apply range_split and range_split2 repeatedly *)
  unfold fe_ofs_arg.
  apply range_split. lia.
  apply range_split. lia.
  apply range_split_2. fold ol; lia. lia.
  apply range_split. lia.
  apply range_drop_right with ostkdata. lia.
  eapply sep_drop2. eexact H.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (olink := 4 * b.(bound_outgoing));
  set (ora := olink + 4);
  set (ol := align (ora + 4) 8);
  set (ocs := ol + 4 * b.(bound_local)).
  set (ostkdata := align (size_callee_save_area fe ocs) 8).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= olink) by (unfold olink; lia).
  assert (olink <= ora) by (unfold ora; lia).
  assert (ora + 4 <= ol) by (apply align_le; lia).
  assert (ol + 4 * b.(bound_local) <= ocs) by (unfold ocs; lia).
  assert (ocs <= size_callee_save_area fe ocs) by apply size_callee_save_area_incr.
  assert (size_callee_save_area fe ocs <= ostkdata) by (apply align_le; lia).
  split. unfold size_callee_save_area in *. simpl in *. lia. apply align_le; lia.
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  /\ (4 | fe_ofs_link fe)
  /\ (4 | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (olink := 4 * b.(bound_outgoing));
  set (ora := olink + 4);
  set (ol := align (ora + 4) 8);
  set (ocs := ol + 4 * b.(bound_local));
  set (ostkdata := align (size_callee_save_area fe ocs) 8).
  split. apply Z.divide_0_r.
  split. apply align_divides; lia.
  split. apply align_divides; lia.
  unfold ora, olink; auto using Z.divide_mul_l, Z.divide_add_r, Z.divide_refl.
Qed.
