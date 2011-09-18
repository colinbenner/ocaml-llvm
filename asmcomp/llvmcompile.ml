open Cmm

exception Llvm_error of string

let counter = ref 0

let addr_type = "addr" (*"i" ^ string_of_int (8 * Arch.size_addr) ^ "*"*)
let int_type = "i" ^ string_of_int (8 * Arch.size_int)
let float_type = "double"

(* {{{ *)
let translate_op = function
  | Caddi -> "add " ^ int_type
  | Csubi -> "sub " ^ int_type
  | Cmuli -> "mul " ^ int_type
  | Cdivi -> "div " ^ int_type
  | Cmodi -> "srem "^ int_type
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
  | Single | Double | Double_u -> float_type
  | Word -> int_type (* should be addr_type *)
  | _ -> int_type

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

let translate_ucomp = function
  | Ceq -> "eq"
  | Cne -> "ne"
  | Clt -> "ult"
  | Cle -> "ule"
  | Cgt -> "ugt"
  | Cge -> "uge"

let translate_machtype typ = String.concat ", " (List.map (function
  | Addr -> addr_type
  | Int -> int_type
  | Float -> float_type) (Array.to_list typ))
(* }}} *)

let counter_inc () = counter := !counter + 1; string_of_int !counter

let tbl = Hashtbl.create 10

let ret_val name counter = Some (name ^ counter)

let strip_sigil s = String.sub s 1 (String.length s - 1)

(* returns a tuple of
 -- instructions to execute before using the result of this operation
 -- the virtual register of the result
 -- the type of the result
 *)
let rec compile_expr expr = match expr with
  | Cconst_int i -> "", Some (string_of_int i), Some int_type
  | Cconst_natint i -> "", Some (Nativeint.to_string i), Some int_type
  | Cconst_float f -> "", Some f, Some float_type
  | Cconst_symbol s -> "", Some ("@" ^ s), Some addr_type
  | Cconst_pointer i -> "", Some (string_of_int i), Some addr_type
  | Cconst_natpointer i -> "", Some (Nativeint.to_string i), Some addr_type

  | Cvar id -> begin
      let c = counter_inc () in
      let name = Ident.name id in
      match (try Hashtbl.find tbl name with Not_found -> None) with
      | Some typ ->
          "\t%id" ^ c ^ " = load " ^ typ ^ " %" ^ name ^ "\n",
          ret_val "%id" c,
          Some typ
      | None -> raise (Llvm_error ("could not find identifier '" ^ name ^ "'."))
    end
  | Clet(id,arg,body) -> begin
      let name = Ident.name id in
      match compile_expr arg with
      | (instr_arg, Some res_arg, Some type_arg) -> begin
          Hashtbl.add tbl name (Some type_arg);
          let (instr_body, res_body, type_body) = compile_expr body in
          "\t%" ^ name ^ " = alloca " ^ type_arg ^ "\n" ^
          instr_arg ^
          "\tstore " ^ type_arg ^ " " ^ res_arg ^ ", " ^ type_arg ^ "* %" ^ name ^ " ;generated for let statement\n" ^
          instr_body,
          res_body, type_body
        end
      | _ -> raise (Llvm_error "failed to compile subexpression of let statement")
    end
  | Cassign(id,expr) -> begin
      match compile_expr expr with
      | instr, Some res, typ ->
          "\t%" ^ Ident.name id ^ " = " ^ instr, Some ("%" ^ Ident.name id), typ
      | _ -> raise (Llvm_error "failed to compile subexpression of assignment")
    end
  | Ctuple [] -> "\t;()\n", None, None
  | Ctuple exprs -> begin
      let c = counter_inc () in
      "\t;tuple code...\n", ret_val "%tuple_res" c, Some "tuple_type"
    end

  | Cop(Capply(typ, debug), exprs) -> begin
      let c = counter_inc () in
      match exprs with
      | Cconst_symbol s :: rem ->
          "\t%call_res" ^ c ^ " = call @" ^ s ^ "(...)\n",
          ret_val "%call_res" c, Some (translate_machtype typ)
      | _ ->
          "\t;%apply_res" ^ c ^ " = call ...\n",
          ret_val "%apply_res" c, Some (translate_machtype typ)
    end
  | Cop(Cextcall(name, typ, b, debug), exprs) ->
      let c = counter_inc () in
      "\t%extcall_res" ^ c ^ " = call " ^ translate_machtype typ ^ " ;...\n",
      ret_val "%extcall_res" c, Some (translate_machtype typ)
  | Cop(Calloc, header :: args) -> begin
      let c = counter_inc () in
      match compile_expr header with
      | instr, Some res, _ ->
          let instrs = String.concat "" (List.map (fun arg -> let (a,_,_) = compile_expr arg in a) args) in
          let other_elements = "" (* TODO handle args *) in
          let len = List.length (header :: args) in
          Printf.sprintf ("%s%s\t%%young_ptr_int%s = load %s @caml_young_pointer
	%%new_young_ptr_int%s = sub %s %%young_ptr_int%s, %i
	store %s %%new_young_ptr_int%s, %s @caml_young_pointer
	%%new_young_ptr%s = inttoptr %s %%new_young_ptr_int%s to [%i x %s]*
	%%header_addr%s = getelementptr [%i x %s]* %%new_young_ptr%s, %s 0%s
	%%header_addr_int%s = ptrtoint %s %%header_addr%s to %s
	%%alloc_res_int%s = add %s %%header_addr_int%s, %i
	%%alloc_res%s = inttoptr %s %%alloc_res_int%s to %s\n")
          (* TODO check whether we have to call the garbage collector *)
          instr instrs
          c addr_type
          c int_type c len
          int_type c addr_type
          c int_type c len int_type
          c len int_type c int_type other_elements
          c addr_type c int_type
          c int_type c Arch.size_int
          c int_type c addr_type,
          ret_val "%alloc_res" c, Some addr_type
      | _ -> raise (Llvm_error "could not compile subexpression of alloc statement")
    end
  | Cop (Calloc, []) -> raise (Llvm_error "can not use Calloc with no arguments")

  | Cop(Cstore mem, [addr; value]) -> begin
      match (compile_expr addr, compile_expr value) with
      | (addr_instr, Some addr_res, _), (val_instr, Some val_res, _) ->
          let typ = translate_mem_chunk mem in
          addr_instr ^ val_instr ^
          "\tstore " ^ typ ^ " " ^ val_res ^ ", " ^ typ ^ " " ^ addr_res ^ " ;generated from Cstore\n", None, None
      | _ -> raise (Llvm_error "failed to compile subexpression of store statement")
    end
  | Cop(Craise debug, [arg]) -> begin
      match compile_expr arg with
      | instr, Some res, _ ->
(*      let c = counter_inc () in*)
          instr ^
          "\tunwind ;raise exception..." ^ res ^ "\n", None, Some "" (* void *)
      | _ -> raise (Llvm_error "could not compile subexpression of raise")
    end
  | Cop(Craise _, _) -> raise (Llvm_error "wrong number of arguments for Craise")
  | Cop(Ccheckbound debug, exprs) ->
      let c = counter_inc () in
      "\t;check bound...\n", ret_val "%checkbound_res" c, None
  | Cop(op, exprs) -> compile_operation op exprs

  | Csequence(expr1,expr2) -> begin
      match (compile_expr expr1, compile_expr expr2) with
      | (instr1, _, _),(instr2, Some res, typ) ->
          instr1 ^ instr2, Some res, typ
      | _ -> raise (Llvm_error "could not compute subexpression of sequence")
    end
  | Cifthenelse(cond, expr1, expr2) -> begin
      match (compile_expr cond, compile_expr expr1, compile_expr expr2) with
      | (cond_instr, Some cond_res, Some cond_typ), (instr1, res1, type1), (instr2, res2, type2) ->
          (* the else type is the same as the then type *)
          let c = counter_inc () in
          let res1 = (
            match res1 with
            | Some res -> res
            | None -> "0") in
          let res2 = (
            match res2 with
            | Some res -> res
            | None -> "0") in
          let typ, labels = (
            match (type1, type2) with
            | (Some t1, Some t2) -> t1, t1 ^ " [" ^ res1 ^ ", %then" ^ c ^ "], [" ^ res2 ^ ", %else" ^ c ^ "]\n"
            | (Some t1, None) -> t1, t1 ^ " [" ^ res1 ^ ", %then" ^ c ^ "], [ 0, %else" ^ c ^ "]\n"
            | (None, Some t2) -> t2, t2 ^ " [0, %then" ^ c ^ "], [" ^ res2 ^ ", %else" ^ c ^ "]\n"
            | (None, None) -> raise (Llvm_error "both alternatives never return")) in
          cond_instr ^
          "\t%cond" ^ c ^ " = icmp ne " ^ int_type ^ " 0, " ^ cond_res ^ "\n" ^
          "\tbr i1 %cond" ^ c ^ ", label %then" ^ c ^ ", label %else" ^ c ^ "\n\n" ^
          "then" ^ c ^ ":\n" ^ instr1 ^ "\tbr label %fi" ^ c ^ "\n\n" ^
          "else" ^ c ^ ":\n" ^ instr2 ^ "\tbr label %fi" ^ c ^ "\n\n" ^
          "fi" ^ c ^ ":\n" ^
          "\t%res" ^ c ^ " = phi " ^ labels,
          ret_val "%res" c, Some typ
      | _ -> raise (Llvm_error "could not compute subexpression of if-then-else statement")
    end
  | Cswitch(expr,is,exprs) -> begin
      match compile_expr expr with
      | instr, Some res, _ ->
          let c = counter_inc () in
          instr ^
          "\t;switch " ^ int_type ^ " " ^ res ^ ", label <default label>, ..." , ret_val "%switch_res" c, Some "switch_type"
      | _ -> raise (Llvm_error "could not compute subexpression of switch statement")
    end
  | Cloop expr -> begin
      let (instr, _, _)  = compile_expr expr in
      let c = counter_inc () in
      "loop" ^ c ^ ":\n" ^ instr ^ "\tbr %loop" ^ c ^ "\n",
      None, None
    end
  | Ccatch(i,ids,expr1,expr2) -> "\t;catch...\n", ret_val "%catch_res" "", Some "catch_type"
  | Cexit(i,exprs) -> "\t;exit...\n", ret_val "%exit_res" "", Some "exit_type"
  | Ctrywith(expr1,id,expr2) -> "\t;try ... with ...\n", ret_val "%try_with_res" "", Some "trywith_type"

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
              "\t%res" ^ c ^ " = icmp " ^ translate_icomp comp ^ " " ^ int_type ^ " " ^ lres ^ ", " ^ rres ^ "\n",
              ret_val "%res" c, Some "i1"
          | Ccmpf comp ->
              linstr ^ rinstr ^
              "\t%res" ^ c ^ " = fcmp " ^ translate_fcomp comp ^ " " ^ float_type ^ " " ^ lres ^ ", " ^ rres ^ "\n",
              ret_val "%res" c, Some "i1"
          | Ccmpa comp ->
              "\t%res" ^ c ^ " = icmp " ^ translate_ucomp comp ^ " " ^ addr_type ^ " " ^ lres ^ ", " ^ rres ^ "\n",
              ret_val "%res" c, Some "i1"
          | Cadda | Csuba ->
              let res = (if op == Cadda then "%adda_res" else "%suba_res") ^ c in
              linstr ^ rinstr ^
              "\t%addr_int" ^ c ^ " = ptrtoint " ^ addr_type ^ " " ^ lres ^ " to " ^ int_type ^ "\n" ^
              "\t%addr_res_int" ^ c ^ " = add " ^ int_type ^ " %addr_int" ^ c ^ ", " ^ rres ^ "\n" ^
              "\t" ^ res ^ " = inttoptr " ^ int_type ^ " %addr_res_int" ^ c ^ " to " ^ addr_type ^ "\n",
              Some res, Some (addr_type)
          | _ -> raise (Llvm_error "Not a binary operator")
          end
      | _ -> raise (Llvm_error "compiling arguments of binary operator failed")
    end

  | [arg] -> begin
      match compile_expr arg with
      | instr, Some res, Some typ -> begin
          let c = counter_inc () in
          match op with
          | Cfloatofint ->
              instr ^ "\t%float_of_int" ^ c ^ " = sitofp " ^ int_type ^ " " ^ res ^ " to " ^ float_type ^ "\n",
              ret_val "%float_of_int" c, Some float_type
          | Cintoffloat ->
              instr ^ "\t%int_of_float" ^ c ^ " = fptosi " ^ float_type ^ " " ^ res ^ " to " ^ int_type ^ "\n",
              ret_val "%int_of_float" c, Some int_type
          | Cabsf ->
              let mask = "0x7" ^ String.make (2 * Arch.size_int) 'f' in
              instr ^ "\t%tmp" ^ c ^ " = fptosi " ^ float_type ^ " " ^ res ^ " to " ^ int_type ^ "\n" ^
              "\t%tmp2" ^ c ^ " = and " ^ int_type ^ " " ^ mask ^ ", %tmp" ^ c ^ "\n" ^
              "\t%absf_res" ^ c ^ " = uitofp " ^ int_type ^ " %tmp2" ^ c ^ " to " ^ float_type ^ "\n",
              ret_val "%absf_res" c, Some float_type
          | Cload mem ->
              instr ^
              "\t%load_res" ^ c ^ " = load " ^ typ ^ " " ^ res ^ "\n",
              ret_val "%load_res" c, Some (translate_mem_chunk mem)
          | Cnegf ->
              let mask = "0x8" ^ String.make (2 * Arch.size_int) '0' in
              instr ^
              "\t%int_of_float" ^ c ^ " = fptosi " ^ float_type ^ " " ^ res ^ " to " ^ int_type ^ "\n" ^
              "\t%tmp" ^ c ^ " = xor " ^ int_type ^ " " ^ mask ^ ", %int_of_float" ^ c ^ "\n" ^
              "\t%negf_res" ^ c ^ " = uitofp " ^ int_type ^ " %tmp" ^ c ^ " to " ^ float_type ^ "\n",
              ret_val "%negf_res" c, Some float_type
          | _ -> raise (Llvm_error "wrong op")
        end
      | _ -> raise (Llvm_error "failed to compute argument of unary operator")
    end
  | _ -> raise (Llvm_error "There is no operator with this number of arguments")

let argument_list args = String.concat ", " (List.map (fun (id, typ) -> translate_machtype typ ^ " %" ^ Ident.name id) args)

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

