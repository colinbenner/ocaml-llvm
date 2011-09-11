open Cmm

exception Llvm_error of string

let counter = ref 0

let addr_type = "i" ^ string_of_int (8 * Arch.size_addr)
let int_type = "i" ^ string_of_int (8 * Arch.size_int)
let float_type = "double"

(* {{{ *)
let translate_op = function
  | Caddi -> "add " ^ int_type
  | Csubi -> "sub " ^ int_type
  | Cmuli -> "mul " ^ int_type
  | Cdivi -> "div " ^ int_type
  | Cmodi -> "mod " ^ int_type
  | Cand  -> "and " ^ int_type
  | Cor   -> "or "  ^ int_type
  | Cxor  -> "xor " ^ int_type
  | Clsl  -> "shl " ^ int_type
  | Clsr  -> "lshr "^ int_type
  | Casr  -> "ashr " ^ int_type
  | Caddf -> "fadd " ^ float_type
  | Csubf -> "fsub " ^ float_type
  | Cmulf -> "fmul " ^ float_type
  | Cdivf -> "fdiv " ^ float_type
  | _ -> raise (Llvm_error "not a binary operator")

let translate_mem_chunk = function
  | Byte_unsigned | Byte_signed -> "i8"
  | Sixteen_unsigned | Sixteen_signed -> "i16"
  | Thirtytwo_unsigned | Thirtytwo_signed -> "i32"
  | Word -> int_type
  | Single -> "float"
  | Double | Double_u -> float_type

let translate_type = function
  | Addr -> addr_type
  | Int -> int_type
  | Float -> float_type

let translate_fcomp = function
  | Ceq -> "oeq"
  | Cne -> "one"
  | Clt -> "olt"
  | Cle -> "ole"
  | Cgt -> "ogt"
  | Cge -> "oge"

let translate_icomp = function
  | Ceq -> "eq"
  | Cne -> "ne"
  | Clt -> "slt"
  | Cle -> "sle"
  | Cgt -> "sgt"
  | Cge -> "sge"

let translate_machtype typ = String.concat ", " (List.map (function
  | Addr -> addr_type
  | Int -> int_type
  | Float -> float_type) (Array.to_list typ))
(* }}} *)

let counter_inc () = counter := !counter + 1; string_of_int !counter

let tbl = Hashtbl.create 10

let ret_val name counter = Some (name ^ counter)

(* returns a tuple of
 -- instructions to execute before using the result of this operation
 -- the virtual register of the result
 -- the type of the result
 *)
let rec compile_expr expr = match expr with
  | Cconst_int i -> "", Some (string_of_int i), Some int_type
  | Cconst_natint i -> "", Some (Nativeint.to_string i), Some int_type
  | Cconst_float f -> "", Some "$float", Some float_type
  | Cconst_symbol s -> "", Some "$symb", Some "symbol_type"
  | Cconst_pointer i -> "", Some "$pointer", Some "pointer_type"
  | Cconst_natpointer i -> "", Some "$natpointer", Some "natpointer_type"

  | Cvar id -> "", Some ("%" ^ Ident.name id), (try Hashtbl.find tbl (Ident.name id) with Not_found -> None)
  | Clet(id,expr1,expr2) -> begin
      let name = Ident.name id in
      match (compile_expr expr1, compile_expr expr2) with
      | (instr1, Some res, Some type1), (instr2, res2, type2) ->
          let c = counter_inc () in
          Hashtbl.add tbl name (Some type1);
          "\t%" ^ name ^ " = alloca " ^ type1 ^ "\n" ^
          instr1 ^ "\t%tmp" ^ c ^ " = " ^ res ^ "\n" ^ instr2 ^
          "\tstore " ^ type1 ^ " %tmp" ^ c ^ ", " ^ type1 ^ "* %" ^ name ^ "\n",
          res2, type2
      | _ -> raise (Llvm_error "failed to compile subexpression of let statement")
    end
  | Cassign(id,expr) -> begin
      match compile_expr expr with
      | instr, Some res, typ ->
          "\t%" ^ Ident.name id ^ " = " ^ instr, Some ("%" ^ Ident.name id), typ
      | _ -> raise (Llvm_error "failed to compile subexpression of assignment")
    end
  | Ctuple exprs ->
      let c = counter_inc () in
      "\ttuple code...\n", ret_val "%tuple_res" c, Some "tuple_type"

  | Cop(Capply(typ, debug), exprs) -> begin
      let c = counter_inc () in
      match exprs with
      | Cconst_symbol s :: rem ->
          "\t%call_res" ^ c ^ " = call \n",
          ret_val "%call_res" c, Some (translate_machtype typ)
      | _ ->
          "\t%apply_res" ^ c ^ " = call ...\n",
          ret_val "%apply_res" c, Some "apply_type"
    end
  | Cop(Cextcall(name, types, b, debug), exprs) ->
      let c = counter_inc () in
      "\t%extcall_res" ^ c ^ " = call <return type> \n", ret_val "%extcall_res" c, Some "extcall_type"
  | Cop(Calloc, exprs) ->
      let c = counter_inc () in
      "\t%alloc_res = ...\n", ret_val "%alloc_res" c, Some "alloc_type"
  | Cop(Cstore mem, [addr; value]) -> begin
      match (compile_expr addr, compile_expr value) with
      | (addr_instr, Some addr_res, _), (val_instr, Some val_res, _) ->
          let typ = translate_mem_chunk mem in
          addr_instr ^ val_instr ^
          "\tstore " ^ typ ^ " " ^ val_res ^ ", " ^ typ ^ "* " ^ addr_res ^ "...\n", None, None
      | _ -> raise (Llvm_error "failed to compile subexpression of store statement")
    end
  | Cop(Craise debug, exprs) ->
      let c = counter_inc () in
      "raise exception...\n", ret_val "%raise_res" c, Some "raise_type"
  | Cop(Ccheckbound debug, exprs) ->
      let c = counter_inc () in
      "check bound...\n", ret_val "%checkbound_res" c, Some "checkbound_type"
  | Cop(op, exprs) -> compile_operation op exprs

  | Csequence(expr1,expr2) -> begin
      match (compile_expr expr1, compile_expr expr2) with
      | (instr1, _, _),(instr2, Some res, typ) ->
          instr1 ^ instr2, Some res, typ
      | _ -> raise (Llvm_error "could not compute subexpression of sequence")
    end
  | Cifthenelse(cond, expr1, expr2) -> begin
      match (compile_expr cond, compile_expr expr1, compile_expr expr2) with
      | (cond_instr, Some cond_res, _), (instr1, Some res1, typ), (instr2, Some res2, _) -> (* the else type is the same as the then type *)
          let c = counter_inc () in
          cond_instr ^ "\tbr i1 " ^ cond_res ^ ", label %then" ^ c ^ ", label %else" ^ c ^ "\n\n" ^
          "then" ^ c ^ ":\n" ^ instr1 ^ "\tbr %fi" ^ c ^ "\n\n" ^
          "else" ^ c ^ ":\n" ^ instr2 ^ "\tbr %fi" ^ c ^ "\n\n" ^
          "fi" ^ c ^ ":\n" ^
          "\t%res" ^ c ^ " = phi <type> [" ^ res1 ^ ", %then" ^ c ^ "], [" ^ res2 ^ ", %else" ^ c ^ "]\n",
          ret_val "%res" c, typ
      | _ -> raise (Llvm_error "could not compute subexpression of if-then-else statement")
    end
  | Cswitch(expr,is,exprs) -> begin
      match compile_expr expr with
      | instr, Some res, _ ->
          let c = counter_inc () in
          instr ^
          "switch " ^ int_type ^ " " ^ res ^ ", label <default label>, ..." , ret_val "%switch_res" c, Some "switch_type"
      | _ -> raise (Llvm_error "could not compute subexpression of switch statement")
    end
  | Cloop expr ->
      let c = counter_inc () in
      "start_loop" ^ c ^ ":\nbr %start_loop\n", None, Some "loop_type"
  | Ccatch(i,ids,expr1,expr2) -> "catch...\n", ret_val "%catch_res" "", Some "catch_type"
  | Cexit(i,exprs) -> "exit...\n", ret_val "%exit_res" "", Some "exit_type"
  | Ctrywith(expr1,id,expr2) -> "try ... with ...\n", ret_val "%try_with_res" "", Some "trywith_type"

and compile_operation op exprs =
  match exprs with
  | [l;r] -> begin
      match (compile_expr l, compile_expr r) with
      | ((linstr, Some lres, Some typ), (rinstr, Some rres, _)) ->
          let c = counter_inc () in begin
          match op with
          | Caddi|Csubi|Cmuli|Cdivi|Cmodi|Cand|Cor|Cxor|Clsl|Clsr|Casr|Caddf|Csubf|Cmulf|Cdivf ->
              linstr ^ rinstr ^
              "\t%res" ^ c ^ " = " ^ translate_op op ^ " " ^ lres ^ ", " ^ rres ^ "\n",
              ret_val "%res" c, Some typ (* this is the same as the other operand's type *)
          | Ccmpi comp ->
              linstr ^ rinstr ^
              "\t%res" ^ c ^ " = icmp " ^ translate_icomp comp ^ " i64 " ^ lres ^ ", " ^ rres ^ "\n",
              ret_val "%res" c, Some "i1"
          | Ccmpf comp ->
              linstr ^ rinstr ^
              "\t%res" ^ c ^ " = fcmp " ^ translate_fcomp comp ^ " " ^ lres ^ ", " ^ rres ^ "\n",
              ret_val "%res" c, Some "i1"
          | Ccmpa comp ->
              "\t%res" ^ c ^ " = cmp ...\n", ret_val "%res" c, Some "i1"
          | Cadda | Csuba ->
              let res = (if op == Cadda then "%adda_res" else "%suba_res") ^ c in
              linstr ^ rinstr ^
              "\t%addr_int" ^ c ^ " = ptrtoint " ^ int_type ^ "* " ^ lres ^ " to " ^ int_type ^ "\n" ^
              "\t%addr_res_int" ^ c ^ " = add " ^ int_type ^ " %addr_int" ^ c ^ ", " ^ rres ^ "\n" ^
              "\t" ^ res ^ " = inttoptr " ^ int_type ^ " %addr_res_int" ^ c ^ " to " ^ int_type ^ "*\n",
              Some res, Some (int_type ^ "*")
          | _ -> raise (Llvm_error "Not a binary operator")
          end
      | _ -> raise (Llvm_error "compiling arguments of binary operator failed")
    end

  | [arg] -> begin
      match compile_expr arg with
      | instr, Some res, _ -> begin
          let c = counter_inc () in
          match op with
          | Cfloatofint ->
              instr ^ "\t%float_of_int" ^ c ^ " = sitofp " ^ int_type ^ " " ^ res ^ " to " ^ float_type ^ "\n",
              ret_val "%float_of_int" c, Some float_type
          | Cintoffloat ->
              instr ^ "\t%int_of_float" ^ c ^ " = fptosi " ^ float_type ^ " " ^ res ^ " to " ^ int_type ^ "\n",
              ret_val "%int_of_float" c, Some int_type
          | Cabsf ->
              let mask = "0x7" ^ String.make (8 * Arch.size_int) 'f' in
              instr ^ "\t%tmp" ^ c ^ " = fptosi " ^ float_type ^ " " ^ res ^ " to " ^ int_type ^
              "\t%tmp2" ^ c ^ " = and " ^ int_type ^ " " ^ mask ^ ", %tmp" ^ c ^
              "\t%absf_res" ^ c ^ " = uitofp " ^ int_type ^ "%tmp2" ^ c ^ " to " ^ float_type ^ "\n",
              ret_val "%absf_res" c, Some float_type
          | Cload mem ->
              instr ^
              "\t%load_res" ^ c ^ " = load " ^ translate_mem_chunk mem ^ "* " ^ res ^ "\n",
              ret_val "%load_res" c, Some "load_type"
          | Cnegf ->
              instr ^ "\t%negf_res" ^ c ^ " = fsub double -0.0, " ^ res ^ "\n", ret_val "%negf_res" c, Some float_type
          | _ -> raise (Llvm_error "wrong op")
        end
      | _ -> raise (Llvm_error "failed to compute argument of unary operator")
    end
  | _ -> raise (Llvm_error "There is no operator with this number of arguments")

let argument_list args = String.concat ", " (List.map (fun (id, typ) -> translate_machtype typ ^ " " ^ Ident.name id) args)

let compile_fundecl fd_cmm =
  match fd_cmm with
    ({fun_name=name; fun_args=args; fun_body=body; fun_fast=fast}) ->
      ignore (List.map (fun (id, typ) -> Hashtbl.add tbl (Ident.name id) (Some (translate_machtype typ))) args);
      match compile_expr body with
      | instr, Some res, Some ret ->
          "define " ^ ret ^ " @" ^ name ^ "(" ^ argument_list args ^ ") {\n"
          ^ "entry:\n"
          ^ instr
          ^ "\tret " ^ ret ^ " " ^ res ^ "\n}\n\n"
      | _ -> raise (Llvm_error "compiling body failed")

