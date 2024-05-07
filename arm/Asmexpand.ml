(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the ARM assembly code.  *)

open Asm
open Asmexpandaux
open AST
open Camlcoq
open! Integers

exception Error of string

(* Useful constants and helper functions *)

let _0 = Integers.Int.zero
let _1 = Integers.Int.one
let _2 = coqint_of_camlint 2l
let _4 = coqint_of_camlint 4l
let _8 = coqint_of_camlint 8l
let _16 = coqint_of_camlint 16l
let _32 = coqint_of_camlint 32l
let _64 = coqint_of_camlint 64l

(* Emit instruction sequences that set or offset a register by a constant. *)
(* No S suffix because they are applied to SP most of the time. *)

let expand_movimm dst n =
  List.iter emit (Asmgen.loadimm dst n [])

let expand_subimm dst src n =
  if dst <> src || n <> _0 then begin
    List.iter emit (Asmgen.addimm dst src (Int.neg n) [])
  end

let expand_addimm dst src n =
  if dst <> src || n <> _0 then begin
    List.iter emit (Asmgen.addimm dst src n [])
  end

let expand_int64_arith conflict rl fn =
  if conflict then
    begin
      fn IR14;
      emit (Pmov (rl,SOreg IR14))
    end else
    fn rl


(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers.
*)

(* Handling of annotations *)

let expand_annot_val kind txt targ args res =
  emit (Pbuiltin (EF_annot(kind,txt,[targ]), args, BR_none));
  match args, res with
  | [BA(One (IR src))], BR(One (IR dst)) ->
     if dst <> src then emit (Pmov (dst,SOreg src))
  | [BA(Two (FR srchi, FR srclo))], BR(Two (FR dsthi, FR dstlo)) ->
     if dsthi <> srchi && dstlo <> srclo then emit (Pfcpyd ((dsthi, dstlo) ,(srchi, srclo)))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_intval")

(* Handling of memcpy *)

(* The ARM has strict alignment constraints for 2 and 4 byte accesses.
   8-byte accesses must be 4-aligned. *)

let memcpy_small_arg sz arg tmp =
  let offset_in_range ofs =
    let n = camlint_of_coqint ofs in n <= 128l && n >= -128l in
  match arg with
  | BA (One (IR r)) ->
      (r, _0)
  | BA_addrstack ofs ->
      if offset_in_range ofs
      && offset_in_range (Int.add ofs (Int.repr (Z.of_uint sz)))
      then (IR13, ofs)
      else begin expand_addimm tmp IR13 ofs; (tmp, _0) end
  | _ ->
      assert false

let expand_builtin_memcpy_small sz al src dst =
  let tsrc = if dst <> BA (One (IR IR2)) then IR2 else IR3 in
  let tdst = if src <> BA (One (IR IR3)) then IR3 else IR2 in
  let (rsrc, osrc) = memcpy_small_arg sz src tsrc in
  let (rdst, odst) = memcpy_small_arg sz dst tdst in
  (* If the source and destination register are not equal the source and
     destination register after memcpy_small_arg should also be not equal
     except for the case when both destination and source are on the stack *)
  assert (src = dst || rdst <> rsrc || (rsrc = IR13 && rdst = IR13));
  let rec copy osrc odst sz  =
    if sz >= 8 && al >= 4 && !Clflags.option_ffpu then begin
      emit (Pfldd ((FR15, FR14),rsrc,osrc));
      emit (Pfstd ((FR15, FR14),rdst,odst));
      copy (Int.add osrc _8) (Int.add odst _8) (sz - 8)
    end else if sz >= 4 && al >= 4 then begin
      emit (Pldr (IR14,rsrc,SOimm osrc));
      emit (Pstr (IR14,rdst,SOimm odst));
      copy (Int.add osrc _4) (Int.add odst _4) (sz - 4)
    end else if sz >= 2 && al >= 2 then begin
      emit (Pldrh (IR14,rsrc,SOimm osrc));
      emit (Pstrh (IR14,rdst,SOimm odst));
      copy (Int.add osrc _2) (Int.add odst _2) (sz - 2)
    end else if sz >= 1 then begin
      emit (Pldrb (IR14,rsrc,SOimm osrc));
      emit (Pstrb (IR14,rdst,SOimm odst));
      copy (Int.add osrc _1) (Int.add odst _1) (sz - 1)
    end in
  copy osrc odst sz

let memcpy_big_arg arg tmp =
  match arg with
  | BA (One (IR r)) ->
      if r <> tmp then emit (Pmov(tmp, SOreg r))
  | BA_addrstack ofs ->
      expand_addimm tmp IR13 ofs
  | _ ->
      assert false

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= al);
  assert (sz mod al = 0);
  let (s, d) =
    if dst <> BA (One (IR IR2)) then (IR2, IR3) else (IR3, IR2) in
  memcpy_big_arg src s;
  memcpy_big_arg dst d;
  let (load, store, chunksize) =
    if al >= 4 then
      (Pldr_p (IR12,s,SOimm _4), Pstr_p (IR12,d,SOimm _4) , 4)
    else if al = 2 then
       (Pldrh_p (IR12,s,SOimm _2), Pstrh_p (IR12,d,SOimm _2), 2)
    else
       (Pldrb_p (IR12,s,SOimm _1), Pstrb_p (IR12,d,SOimm _1), 1) in
  expand_movimm IR14 (coqint_of_camlint (Int32.of_int (sz / chunksize)));
  let lbl = new_label () in
  emit (Plabel lbl);
  emit load;
  emit (Psubs (IR14,IR14,SOimm _1));
  emit store;
  emit (Pbne lbl)

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= 32
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

(* Offset checks *)

let offset_in_range chunk ofs =
  match chunk with
  | Mint8signed | Mint16signed | Mint16unsigned  ->
    Int.eq (Asmgen.mk_immed_mem_small ofs) ofs
  | Mint8unsigned | Mint32 ->
    Int.eq (Asmgen.mk_immed_mem_word ofs) ofs
  | Mfloat32 | Mfloat64 ->
    Int.eq (Asmgen.mk_immed_mem_float ofs) ofs
  | Mint64 ->
    Int.eq (Asmgen.mk_immed_mem_word ofs) ofs &&
    Int.eq (Asmgen.mk_immed_mem_word (Int.add ofs _4)) (Int.add ofs _4)
  | _ ->
    assert false

let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8unsigned, BR(One (IR res)) ->
     emit (Pldrb (res, base, SOimm ofs))
  | Mint8signed, BR(One (IR res)) ->
     emit (Pldrsb (res, base, SOimm ofs))
  | Mint16unsigned, BR(One (IR res)) ->
     emit (Pldrh (res, base, SOimm ofs))
  | Mint16signed, BR(One (IR res)) ->
     emit (Pldrsh (res, base, SOimm ofs))
  | Mint32, BR(One (IR res)) ->
     emit (Pldr (res, base, SOimm ofs))
  | Mint64, BR_splitlong(BR(One (IR res1)), BR(One (IR res2))) ->
     let ofs_hi = if Archi.big_endian then ofs else Int.add ofs _4 in
     let ofs_lo = if Archi.big_endian then Int.add ofs _4 else ofs in
     if base <> res2 then begin
	 emit (Pldr (res2, base, SOimm ofs_lo));
	 emit (Pldr (res1, base, SOimm ofs_hi))
       end else begin
	 emit (Pldr (res1, base, SOimm ofs_hi));
	 emit (Pldr (res2, base, SOimm ofs_lo))
       end
  | Mfloat32, BR(One (FR res)) ->
     emit (Pflds (res, base, ofs))
  | Mfloat64, BR(Two (FR reshi, FR reslo)) ->
     emit (Pfldd ((reshi, reslo), base, ofs))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(One (IR addr))] ->
      expand_builtin_vload_common chunk addr _0 res
  | [BA_addrstack ofs] ->
      if offset_in_range chunk ofs then
        expand_builtin_vload_common chunk IR13 ofs res
      else begin
        expand_addimm IR14 IR13 ofs;
        expand_builtin_vload_common chunk IR14 _0 res
      end
  | [BA_addrglobal(id, ofs)] ->
      emit (Ploadsymbol (IR14,id,ofs));
      expand_builtin_vload_common chunk IR14 _0 res
  | [BA_addptr(BA(One (IR addr)), BA_int ofs)] ->
      if offset_in_range chunk ofs then
        expand_builtin_vload_common chunk addr ofs res
      else begin
        expand_addimm IR14 addr ofs;
        expand_builtin_vload_common chunk IR14 _0 res
      end
  | _ ->
      assert false

let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(One (IR src)) ->
     emit (Pstrb (src, base, SOimm ofs))
  | (Mint16signed | Mint16unsigned), BA(One (IR src)) ->
     emit (Pstrh (src, base, SOimm ofs))
  | Mint32, BA(One (IR src)) ->
     emit (Pstr (src, base, SOimm ofs))
  | Mint64, BA_splitlong(BA(One (IR src1)), BA(One (IR src2))) ->
     let ofs_hi = if Archi.big_endian then ofs else Int.add ofs _4 in
     let ofs_lo = if Archi.big_endian then Int.add ofs _4 else ofs in
     emit (Pstr (src2, base, SOimm ofs_lo));
     emit (Pstr (src1, base, SOimm ofs_hi))
  | Mfloat32, BA(One (FR src)) ->
     emit (Pfsts (src, base, ofs))
  | Mfloat64, BA(Two (FR srchi, FR srclo)) ->
     emit (Pfstd ((srchi, srclo), base, ofs))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(One (IR addr)); src] ->
      expand_builtin_vstore_common chunk addr _0 src
  | [BA_addrstack ofs; src] ->
      if offset_in_range chunk ofs then
        expand_builtin_vstore_common chunk IR13 ofs src
      else begin
        expand_addimm IR14 IR13 ofs;
        expand_builtin_vstore_common chunk IR14 _0 src
      end
  | [BA_addrglobal(id, ofs); src] ->
      emit (Ploadsymbol (IR14,id,ofs));
      expand_builtin_vstore_common chunk IR14 _0 src
  | [BA_addptr(BA(One (IR addr)), BA_int ofs); src] ->
      if offset_in_range chunk ofs then
        expand_builtin_vstore_common chunk addr ofs src
      else begin
        expand_addimm IR14 addr ofs;
        expand_builtin_vstore_common chunk IR14 _0 src
      end
  | _ ->
      assert false

(* Handling of varargs *)

let align n a = (n + a - 1) land (-a)

let rec next_arg_location ir ofs = function
  | [] ->
     Int32.of_int (ir * 4 + ofs)
  | (Tint | Tsingle | Tany32) :: l ->
     if ir < 4
     then next_arg_location (ir + 1) ofs l
     else next_arg_location ir (ofs + 4) l
  | (Tfloat | Tlong | Tany64) :: l ->
     if ir < 3
     then next_arg_location (align ir 2 + 2) ofs l
     else next_arg_location 4 (align ofs 8 + 8) l

let expand_builtin_va_start r =
  if not (is_current_function_variadic ()) then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let ofs =
    Int32.add
      (next_arg_location 0 0 (get_current_function_args ()))
      !PrintAsmaux.current_function_stacksize in
  expand_addimm IR14 IR13 (coqint_of_camlint ofs);
  emit (Pstr (IR14,r,SOimm _0))


(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Integer arithmetic *)
  | "__builtin_bswap64" , [BA_splitlong(BA(One (IR ah)), BA(One (IR al)))],
                          BR_splitlong(BR(One (IR rh)), BR(One (IR rl))) ->
     expand_int64_arith (rl = al) rl (fun rl ->
        emit (Prev (rl, ah));
        emit (Prev (rh, al)))
  | ("__builtin_bswap" | "__builtin_bswap32"), [BA(One (IR a1))], BR(One (IR res)) ->
     emit (Prev (res, a1))
  | "__builtin_bswap16", [BA(One (IR a1))], BR(One (IR res)) ->
     emit (Prev16 (res, a1))
  | ("__builtin_clz" | "__builtin_clzl"), [BA(One (IR a1))], BR(One (IR res)) ->
     emit (Pclz (res, a1))
  | "__builtin_clzll", [BA_splitlong(BA (One (IR ah)), BA (One (IR al)))], BR(One (IR res)) ->
     emit (Pclz (IR14, al));
     emit (Pcmp (ah, SOimm _0));
     emit (Pmovite (TCeq, IR14, SOreg IR14, SOimm _0));
     emit (Pclz (res, ah));
     emit (Padd (res, res, SOreg IR14))
  | ("__builtin_ctz" | "__builtin_ctzl"), [BA(One (IR a1))], BR(One (IR res)) ->
     emit (Psub(IR14, a1, SOimm _1));    (* tmp := x-1 *)
     emit (Pmvn(res, SOreg a1));         (* res := ~(x) *)
     emit (Pand(res, IR14, SOreg res));  (* res := tmp & ~(x) *)
     emit (Pclz(res, res));              (* res := #leading zeros *)
     emit (Prsb(res, res, SOimm _32))    (* res := 32 - #leading zeros *)
  | "__builtin_ctzll", [BA_splitlong(BA(One (IR ah)), BA(One (IR al)))], BR(One (IR res)) ->
     let lbl1 = new_label () in
     let lbl2 = new_label () in
     (* low word equal to zero? *)
     emit (Pcmp (al, SOimm _0));
     emit (Pbne lbl1);
     (* low word is zero, count trailing zeros in high word and increment by 32 *)
     emit (Psub(IR14, ah, SOimm _1));
     emit (Pmvn(res, SOreg ah));
     emit (Pand(res, IR14, SOreg res));
     emit (Pclz(res, res));
     emit (Prsb(res, res, SOimm _64));
     emit (Pb lbl2);
     (* count trailing zeros in low word *)
     emit (Plabel lbl1);
     emit (Psub(IR14, al, SOimm _1));
     emit (Pmvn(res, SOreg al));
     emit (Pand(res, IR14, SOreg res));
     emit (Pclz(res, res));
     emit (Prsb(res, res, SOimm _32));
     emit (Plabel lbl2)
  (* Float arithmetic *)
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA(Two (FR a1hi, FR a1lo))], BR(Two (FR reshi, FR reslo)) ->
     emit (Pfsqrt ((reshi, reslo) , (a1hi, a1lo)))
  (* 64-bit integer arithmetic *)
  | "__builtin_negl", [BA_splitlong(BA(One (IR ah)), BA(One (IR al)))],
                      BR_splitlong(BR(One (IR rh)), BR(One (IR rl))) ->
      expand_int64_arith (rl = ah ) rl (fun rl ->
        emit (Prsbs (rl,al,SOimm _0));
        (* No "rsc" instruction in Thumb2.  Emulate based on
           rsc a, b, #0 == a <- AddWithCarry(~b, 0, carry)
           == mvn a, b; adc a, a, #0 *)
        if !Clflags.option_mthumb then begin
	  emit (Pmvn (rh,SOreg ah));
	  emit (Padc (rh,rh,SOimm _0))
        end else begin
	  emit (Prsc (rh,ah,SOimm _0))
        end)
  | "__builtin_addl", [BA_splitlong(BA(One (IR ah)), BA(One (IR al)));
                       BA_splitlong(BA(One (IR bh)), BA(One (IR bl)))],
                      BR_splitlong(BR(One (IR rh)), BR(One (IR rl))) ->
     expand_int64_arith (rl = ah || rl = bh) rl
			(fun rl ->
			 emit (Padds (rl,al,SOreg bl));
			 emit (Padc (rh,ah,SOreg bh)))
  | "__builtin_subl", [BA_splitlong(BA(One (IR ah)), BA(One (IR al)));
                       BA_splitlong(BA(One (IR bh)), BA(One (IR bl)))],
                      BR_splitlong(BR(One (IR rh)), BR(One (IR rl))) ->
     expand_int64_arith (rl = ah || rl = bh) rl
		       (fun rl ->
			emit (Psubs (rl,al,SOreg bl));
			emit (Psbc (rh,ah,SOreg bh)))
  | "__builtin_mull", [BA(One (IR a)); BA(One (IR b))],
                      BR_splitlong(BR(One (IR rh)), BR(One (IR rl))) ->
     emit (Pumull (rl,rh,a,b))
  (* Memory accesses *)
  | "__builtin_read16_reversed", [BA(One (IR a1))], BR(One (IR res)) ->
     emit (Pldrh (res,a1,SOimm _0));
     emit (Prev16 (res, res));
  | "__builtin_read32_reversed", [BA(One (IR a1))], BR(One (IR res)) ->
     emit (Pldr (res,a1,SOimm _0));
     emit (Prev (res, res));
  | "__builtin_write16_reversed", [BA(One (IR a1)); BA(One (IR a2))], _ ->
     emit (Prev16 (IR14, a2));
     emit (Pstrh (IR14, a1, SOimm _0))
  | "__builtin_write32_reversed", [BA(One (IR a1)); BA(One (IR a2))], _ ->
     emit (Prev (IR14, a2));
     emit (Pstr (IR14, a1, SOimm _0))
  (* Synchronization *)
  | "__builtin_membar",[], _ ->
     ()
  | "__builtin_dmb", [], _ ->
     emit Pdmb
  | "__builtin_dsb", [], _ ->
     emit Pdsb
  | "__builtin_isb", [], _ ->
     emit Pisb
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(One (IR a))], _ ->
     expand_builtin_va_start a
  (* No operation *)
  | "__builtin_nop", [], _ ->
     emit Pnop
  (* Optimization hint *)
  | "__builtin_unreachable", [], _ ->
     ()
  (* Catch-all *)
  | _ ->
      raise (Error ("unrecognized builtin " ^ name))


(* Handling of calling conventions *)

type direction = Incoming | Outgoing

module FixupEABI = struct

  let ireg_param = function
    | 0 -> IR0 | 1 -> IR1 | 2 -> IR2 | 3 -> IR3 | _ -> assert false

  let freg_param_double = function
    | 0 -> (FR1, FR0) | 1 -> (FR3, FR2) | 2 -> (FR5, FR4) | 3 -> (FR7, FR6) | _ -> assert false

  let freg_param_single = function
    | 0 -> FR0 | 1 -> FR1 | 2 -> FR2 | 3 -> FR3 | _ -> assert false

  let fixup_double dir f i1 i2 =
    match dir with
    | Incoming -> (* f <- (i1, i2)  *)
      emit (Pfcpy_fii (f, i1, i2))
    | Outgoing -> (* (i1, i2) <- f *)
      emit (Pfcpy_iif (i1, i2, f))

  let fixup_single dir f i =
    match dir with
    | Incoming -> (* f <- i *)
      emit (Pfcpy_fi (f, i))
    | Outgoing -> (* i <- f *)
      emit (Pfcpy_if (i, f))

  let fixup_conventions dir tyl =
    let rec fixup i tyl =
      if i < 4 then
        match tyl with
        | [] -> ()
        | (Tint | Tany32) :: tyl' ->
          fixup (i+1) tyl'
        | Tlong :: tyl' ->
          fixup (((i + 1) land (-2)) + 2) tyl'
        | (Tfloat | Tany64) :: tyl' ->
          let i = (i + 1) land (-2) in
          if i < 4 then begin
            if Archi.big_endian
            then fixup_double dir (freg_param_double i) (ireg_param (i+1)) (ireg_param i)
            else fixup_double dir (freg_param_double i) (ireg_param i) (ireg_param (i+1));
            fixup (i+2) tyl'
          end
        | Tsingle :: tyl' ->
          fixup_single dir (freg_param_single i) (ireg_param i);
          fixup (i+1) tyl'
    in fixup 0 tyl

  let fixup_arguments dir sg =
    fixup_conventions dir sg.sig_args

  let fixup_result dir sg =
    fixup_conventions dir (proj_sig_res sg :: [])
end

module FixupHF = struct
  let fixup_arguments dir sg =
    if sg.sig_cc.cc_vararg <> None then
      FixupEABI.fixup_arguments dir sg

  let fixup_result dir sg =
    if sg.sig_cc.cc_vararg <> None then
      FixupEABI.fixup_result dir sg
end

let (fixup_arguments, fixup_result) =
  match Configuration.abi with
  | "eabi"      -> (FixupEABI.fixup_arguments, FixupEABI.fixup_result)
  | "hardfloat" -> (FixupHF.fixup_arguments, FixupHF.fixup_result)
  | _ -> assert false

(* Instruction expansion *)

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
     emit (Pmov (IR12,SOreg IR13));
     if (is_current_function_variadic ()) then begin
       emit (Ppush [IR0;IR1;IR2;IR3]);
       emit (Pcfi_adjust _16);
     end;
     let sz' = camlint_of_coqint sz in
     let ofs' = camlint_of_coqint ofs in
     if ofs' >= 4096l && sz' >= ofs' then begin
       expand_subimm IR13 IR13 (coqint_of_camlint (Int32.sub sz' (Int32.add ofs' 4l)));
       emit (Ppush [IR12]);
       expand_subimm IR13 IR13 ofs;
       emit (Pcfi_adjust sz);
     end else begin
        assert (ofs' < 4096l);
        expand_subimm IR13 IR13 sz;
        emit (Pcfi_adjust sz);
        emit (Pstr (IR12,IR13,SOimm ofs));
     end;
     PrintAsmaux.current_function_stacksize := camlint_of_coqint sz
  | Pfreeframe (sz, ofs) ->
     let sz =
       if (is_current_function_variadic ())
       then coqint_of_camlint (Int32.add 16l (camlint_of_coqint sz))
       else sz in
     if Asmgen.is_immed_arith sz
     then expand_addimm IR13 IR13 sz
     else begin
       if camlint_of_coqint ofs >= 4096l then begin
         expand_addimm IR13 IR13 ofs;
         emit (Pldr (IR13,IR13,SOimm _0))
       end else
         emit (Pldr (IR13,IR13,SOimm ofs));
     end
  | Pbuiltin (ef,args,res) ->
     begin match ef with
	   | EF_builtin (name,sg) ->
	      expand_builtin_inline (camlstring_of_coqstring name) args res
	   | EF_vload chunk ->
	      expand_builtin_vload chunk args res
	   | EF_vstore chunk ->
	      expand_builtin_vstore chunk args
	   | EF_annot_val (kind,txt,targ) ->
	      expand_annot_val kind txt targ args res
	   | EF_memcpy(sz, al) ->
	      expand_builtin_memcpy (Int32.to_int (camlint_of_coqint sz))
		(Int32.to_int (camlint_of_coqint al)) args
	   | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
              emit instr
	   | _ ->
              assert false
     end
  (* Fixup for calling conventions *)
  | Pbsymb(id, sg) ->
      fixup_arguments Outgoing sg;
      emit instr
  | Pbreg(r, sg) ->
    if r = IR14 then
      fixup_result Outgoing sg
    else
      fixup_arguments Outgoing sg;
    emit instr
  | Pblsymb(_, sg) ->
      fixup_arguments Outgoing sg;
      emit instr;
      fixup_result Incoming sg
  | Pblreg(_, sg) ->
      fixup_arguments Outgoing sg;
      emit instr;
      fixup_result Incoming sg
  | _ ->
     emit instr

let int_reg_to_dwarf = function
   | IR0 -> 0  | IR1 -> 1  | IR2 -> 2  | IR3 -> 3
   | IR4 -> 4  | IR5 -> 5  | IR6 -> 6  | IR7 -> 7
   | IR8 -> 8  | IR9 -> 9  | IR10 -> 10 | IR11 -> 11
   | IR12 -> 12 | IR13 -> 13 | IR14 -> 14

let float_reg_to_dwarf reg =
 let reg =  match reg with
   | FR0 -> 0   | FR1 -> 1   | FR2 -> 2   | FR3 -> 3
   | FR4 -> 4   | FR5 -> 5   | FR6 -> 6   | FR7 -> 7
   | FR8 -> 8   | FR9 -> 9   | FR10 -> 10 | FR11 -> 11
   | FR12 -> 12 | FR13 -> 13 | FR14 -> 14 | FR15 -> 15
   | FR16 -> 16 | FR17 -> 17 | FR18 -> 18 | FR19 -> 19
   | FR20 -> 20 | FR21 -> 21 | FR22 -> 22 | FR23 -> 23
   | FR24 -> 24 | FR25 -> 25 | FR26 -> 26 | FR27 -> 27
   | FR28 -> 28 | FR29 -> 29 | FR30 -> 30 | FR31 -> 31 in
   if Configuration.model >= "armv7" then
     256 + reg
   else
     64 + reg

let preg_rpair_to_dwarf = function
   | One (IR r) -> int_reg_to_dwarf r
   | One (FR r) -> float_reg_to_dwarf r
   | Two (FR hi, FR lo) -> float_reg_to_dwarf lo
   | _ -> assert false


let expand_function id fn =
  try
    set_current_function fn;
    fixup_arguments Incoming fn.fn_sig;
    expand id 13 preg_rpair_to_dwarf expand_instruction fn.fn_code;
    let fn = get_current_function () in
    let fn = Constantexpand.expand_constants fn in
    Errors.OK fn
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_program2 expand_fundef (fun id v -> Errors.OK v) p
