open Cmm

exception Llvm_error of string

let counter = ref 0

let size_int = 8 * Arch.size_int
let size_float = 8 * Arch.size_float

let int_type = "i" ^ string_of_int size_int
let addr_type = int_type ^ "*"
let float_type = "double"
let float_sized_int = "i" ^ string_of_int size_float

(* {{{ *)
let translate_op = function
  | Caddi -> "add"
  | Csubi -> "sub"
  | Cmuli -> "mul"
  | Cdivi -> "div"
  | Cmodi -> "srem"
  | Cand  -> "and"
  | Cor   -> "or"
  | Cxor  -> "xor"
  | Clsl  -> "shl"
  | Clsr  -> "lshr"
  | Casr  -> "ashr"
  | Caddf -> "fadd"
  | Csubf -> "fsub"
  | Cmulf -> "fmul"
  | Cdivf -> "fdiv"
  | _ -> raise (Llvm_error "not a binary operator")

let translate_mem = function
  | Byte_unsigned | Byte_signed -> "i8"
  | Sixteen_unsigned | Sixteen_signed -> "i16"
  | Thirtytwo_unsigned | Thirtytwo_signed -> "i32"
  | Word -> int_type
  | Single | Double | Double_u -> float_type

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

(* {{{ *)
let counter_inc () = counter := !counter + 1

let tbl = Hashtbl.create 10

let ret_val name counter = Some (name ^ counter)

let value s = String.sub s 0 (String.length s - 1)
let addr s = s ^ "*"
let is_addr s = String.contains s '*'
let is_float s = String.compare float_type s == 0
let is_int s = String.compare (String.sub s 0 1) "i" == 0 && not (is_addr s)

let is_none = function
  | Some _ -> false
  | None -> true

let get = function
  | Some x -> x
  | None -> raise (Llvm_error "can not get content of None")

let base_type str = try String.sub str 0 (String.index str '*') with Not_found -> str

let current_args : string list ref = ref [] (* this contains a list of the arguments of a function *)

let is_arg name = let rec find_name = function
  | [] -> false
  | head :: tail -> if compare name head == 0 then true else find_name tail in
  find_name !current_args

let emit str = print_endline str

let c () = string_of_int !counter
(* }}} *)

(* {{{ *)
let alloca name typ =
  emit ("\t" ^ name ^ " = alloca " ^ typ);
  name, typ ^ "*"

let load (addr, typ) =
  emit ("\t%load_res" ^ c () ^ " = load " ^ typ ^ " " ^ addr);
  "%load_res" ^ c (), value typ

let store (value,typ) (addr,ptrtype) =
  emit ("\tstore " ^ typ ^ " " ^ value ^ ", " ^ ptrtype ^ " " ^ addr)

let bitcast (src,src_type) dest_type =
  emit ("\t%bitcast_res" ^ c () ^ " = bitcast " ^ src_type ^ " " ^ src ^ " to " ^ dest_type);
  "%bitcast_res" ^ c (), dest_type

let inttoptr ptr ptr_type =
  emit ("\t%inttoptr_res" ^ c () ^ " = inttoptr " ^ int_type ^ " " ^ ptr ^ " to " ^ ptr_type);
  "%inttoptr_res" ^ c (), ptr_type

let ptrtoint (ptr,ptr_type) int_type =
  emit ("\t%ptrtoint" ^ c () ^ " = ptrtoint " ^ ptr_type ^ " " ^ ptr ^ " to " ^ int_type);
  "%ptrtoint" ^ c (), int_type

let convert op (value,typ) dest_type =
  counter_inc ();
  emit ("\t%convert_res" ^ c () ^ " = " ^ op ^ " " ^ typ ^ " " ^ value ^ " to " ^ dest_type);
  "%convert_res" ^ c (), dest_type


let bitcast_const (src,src_type) dest_type = "bitcast(" ^ src_type ^ " " ^ src ^ " to " ^ dest_type ^ ")"

let inttoptr_const value typ = "inttoptr(" ^ int_type ^ " " ^ value ^ " to " ^ typ ^ ")"

let ptrtoint_const (value,typ) dest_type = "ptrtoint(" ^ typ ^ " " ^ value ^ " to " ^ dest_type ^ ")"

let binop op typ left right =
  emit ("\t%binop_res" ^ c () ^ " = " ^ op ^ " " ^ typ ^ " " ^ left ^ ", " ^ right);
  "%binop_res" ^ c (), typ
(* }}} *)


let to_addr (value, typ) dest_type =
  if String.compare typ dest_type == 0
  then value
  else if is_addr typ
       then fst (bitcast (value,typ) dest_type)
       else if is_int typ
            then fst (inttoptr value dest_type)
            else raise (Llvm_error ("trying to cast float " ^ value ^ " to " ^ dest_type))

let adjust_length (value, typ) dest_type =
  let src_len = int_of_string (String.sub typ 1 (String.length typ - 1)) in
  let dest_len = int_of_string (String.sub dest_type 1 (String.length dest_type - 1)) in
  if src_len == dest_len
  then value, dest_type
  else if src_len > dest_len
       then convert "trunc" (value, typ) dest_type
       else convert "zext" (value, typ) dest_type

let to_int (value, typ) dest_type =
  if String.compare typ dest_type == 0
  then value
  else (counter_inc (); if is_addr typ
       then fst (ptrtoint (value,typ) dest_type)
       else if is_float typ
            then fst (bitcast (value, typ) dest_type)
            else fst (adjust_length (value, typ) dest_type))

let to_float (value, typ) =
  if compare typ float_type == 0
  then value
  else (emit ";converting to float..."; fst (bitcast (value,typ) float_type))

(* returns a tuple of
 -- instructions to execute before using the result of this operation
 -- the virtual register of the result
 -- the type of the result
 *)
let rec compile_expr expr = match expr with
  | Cconst_int i        -> Some (string_of_int i, int_type)
  | Cconst_natint i     -> Some (Nativeint.to_string i, int_type)
  | Cconst_float f      -> Some (f, float_type)
  | Cconst_symbol s     -> Some ("@" ^ s, addr_type)
  | Cconst_pointer i    -> Some (inttoptr_const (string_of_int i) addr_type, addr_type)
  | Cconst_natpointer i -> Some (inttoptr_const (Nativeint.to_string i) addr_type, addr_type)

  | Cvar id -> begin
      counter_inc ();
      let name = Ident.name id in
      let typ = try Hashtbl.find tbl name
                with Not_found -> raise (Llvm_error ("Could not find identifier " ^ name ^ ".")) in
      if is_arg name
      then Some ("%" ^ name, typ)
      else Some (load ("%" ^ name, typ ^ "*"))
    end
  | Clet(id,arg,body) -> begin
      let name = Ident.name id in
      match compile_expr arg with
      | Some (res_arg, type_arg) -> begin
          counter_inc ();
          let typ = if is_float type_arg then float_type else int_type in
          Hashtbl.add tbl name typ;
          let res, typ = alloca ("%" ^ name) typ in
          let body_ret = compile_expr body in
          store (to_int (res_arg, type_arg) int_type(* TODO handle floats *), int_type) ("%" ^ name, typ);
          body_ret
        end
      | _ -> raise (Llvm_error "failed to compile argument of let statement")
    end
  | Cassign(id,expr) -> begin
      match compile_expr expr with
      | Some (res, typ) ->
          counter_inc ();
          let name = Ident.name id in
          let typ = "BLABLA"(*try Hashtbl.find tbl name with Not_found -> raise (Llvm_error ("not found: " ^ name))*)in
          store (res,typ) ("%" ^ name, typ);
          None
      | _ -> raise (Llvm_error "failed to compile subexpression of assignment")
    end
  | Ctuple [] -> emit "\t;()"; None
  | Ctuple exprs -> begin
      counter_inc ();
      emit "\t;tuple code...";
      Some ("%tuple_res" ^ c (), "UNDEFINED")
    end

  | Cop(Capply(typ, debug), exprs) -> begin
      counter_inc ();
      match exprs with
      | Cconst_symbol s :: rem ->
          let results =
            List.map (fun x -> match compile_expr x with
                        | Some res -> addr_type ^ " " ^ to_addr res addr_type
                        | None -> raise (Llvm_error "could not compile argument")) rem in
          counter_inc ();
          emit ("\t%call_res" ^ c () ^ " = call " ^ addr_type ^ " @" ^ s ^ "(" ^ String.concat ", " results ^ ")");
          Some ("%call_res" ^ c (), addr_type)
      | _ ->
          emit ("\t;%call_res" ^ c () ^ " = call " ^ addr_type ^ " @bla()...");
          Some ("%call_res" ^ c (), addr_type)
    end
  | Cop(Cextcall(name, typ, b, debug), exprs) ->
      counter_inc ();
      emit ("\t%extcall_res" ^ c () ^ " = call " ^ addr_type ^ " ;...");
      Some ("%extcall_res" ^ c (), addr_type)
  | Cop(Calloc, header :: args) -> begin
      match compile_expr header with
      | Some (res, typ) ->
          counter_inc ();
          let len = string_of_int (Arch.size_int * List.length (header :: args)) in
          let (res, _) = load ("@caml_young_pointer", addr_type) in
          emit ("\t%new_young_ptr_int" ^ c () ^ " = sub " ^ int_type ^ " " ^ res ^ ", " ^ len);
          (* TODO check whether we have to call the garbage collector *)
          emit ("\t; if %new_young_ptr_int < @caml_young_limit then run gc");
          store ("%new_young_ptr_int" ^ c (), int_type) ("@caml_young_pointer", addr_type);
          let (res_header, typ) = inttoptr ("%new_young_ptr_int" ^ c ()) addr_type in
          let (res, typ) = ptrtoint (res_header, typ) int_type in
          let res = "%alloc_res_int" ^ c () in
          emit ("\t" ^ res ^ " = add " ^ typ ^ " " ^ res ^ ", " ^ string_of_int size_int);
          counter_inc ();
          (* TODO store header *)
          let (res, typ) = inttoptr res addr_type in
          let args = List.fold_left (fun a b -> match (a,b) with
              | lst, Some (c, d) -> lst @ [c,d]
              | _, None -> raise (Llvm_error "Some tuple element has type unit."))
                              [] (List.map compile_expr args) in
          let num = ref (-1) in
          let emit_arg (x, typ) = counter_inc(); num := !num + 1; let num = string_of_int !num in
            emit ("\t%elemptr." ^ num ^ "." ^ c () ^ " = getelementptr " ^ addr_type ^ " " ^ res_header ^
            ", " ^ int_type ^ " " ^ num);
            store (to_int (x, typ) int_type(*FIXME*), int_type) ("%elemptr." ^ num ^ "." ^ c (), addr_type) in
          List.iter emit_arg args;
          Some (res, typ)
      | _ -> raise (Llvm_error "could not compile subexpression of alloc statement")
    end
  | Cop (Calloc, []) -> raise (Llvm_error "can not use Calloc with no arguments")

  | Cop(Cstore mem, [addr; value]) -> begin
      counter_inc ();
      match (compile_expr addr, compile_expr value) with
      | Some (addr_res, addr_type), Some (val_res, val_type) ->
          if String.compare (base_type val_type) (translate_mem mem) == 0
          then store (val_res,val_type) (addr_res,addr_type)
          else (emit ("\t%val" ^ c () ^ " = trunc " ^ val_type ^ " " ^ val_res ^ " to " ^ translate_mem mem);
               store ("%val" ^ c (), translate_mem mem) (addr_res,translate_mem mem ^ "*"));
          None
      | _ -> raise (Llvm_error "failed to compile subexpression of store statement")
    end
  | Cop(Craise debug, [arg]) -> begin
      match compile_expr arg with
      | Some (res, typ) ->
          counter_inc ();
          emit ("\tunwind ;raise exception..." ^ res);
          None
      | _ -> raise (Llvm_error "could not compile subexpression of raise")
    end
  | Cop(Craise _, _) -> raise (Llvm_error "wrong number of arguments for Craise")
  | Cop(Ccheckbound debug, exprs) ->
      counter_inc ();
      emit "\t;check bound...";
      Some ("%checkbound_res" ^ c (), "UNDEFINED")
  | Cop(op, exprs) -> compile_operation op exprs

  | Csequence(expr1,expr2) ->
      ignore (compile_expr expr1);
      compile_expr expr2
  | Cifthenelse(cond, expr1, expr2) -> begin
      match compile_expr cond with
      | Some (cond_res, _) -> begin
          counter_inc ();
          let c = c () in
          let (if_res, res_type) = alloca ("%if_res" ^ c) int_type in
          emit ("\t%cond" ^ c ^ " = icmp ne " ^ int_type ^ " 0, " ^ cond_res);
          emit ("\tbr i1 %cond" ^ c ^ ", label %then" ^ c ^ ", label %else" ^ c ^ "\n");
          emit ("then" ^ c ^ ":");
          begin
          match compile_expr expr1 with
          | Some (res1, type1) -> begin
              counter_inc ();
              store (res1, int_type) (if_res, res_type);
              emit ("\tbr label %fi" ^ c ^ "\n");
              emit ("else" ^ c ^ ":");
              match compile_expr expr2 with
              | Some (res2, type2) ->
                  store (res2, int_type) ("%if_res" ^ c, addr_type);
              | None -> ()
            end
          | None -> begin
              emit ("\tbr label %fi" ^ c ^ "\n");
              emit ("else" ^ c ^ ":");
              match compile_expr expr2 with
              | Some (res2, type2) ->
                  store (res2, int_type) (if_res, res_type);
              | None -> ()
            end
          end;
          emit ("\tbr label %fi" ^ c ^ "\n");
          emit ("fi" ^ c ^ ":");
          Some (load (if_res, res_type))
        end
      | _ -> raise (Llvm_error "could not compute condition of if-then-else statement")
    end
  | Cswitch(expr,is,exprs) -> begin
      match compile_expr expr with
      | Some (res, typ) ->
          counter_inc ();
          emit ("\t;switch " ^ int_type ^ " " ^ res ^ ", label <default label>, ...");
          Some ("%switch_res" ^ c (), "UNDEFINED")
      | _ -> raise (Llvm_error "could not compute subexpression of switch statement")
    end
  | Cloop expr -> begin
      let c = c () in
      counter_inc ();
      emit ("loop" ^ c ^ ":");
      ignore(compile_expr expr);
      emit ("\tbr %loop" ^ c);
      None
    end
  | Ccatch(i,ids,expr1,expr2) -> emit "\t;catch..."; Some ("%catch_res", "UNDEFINED")
  | Cexit(i,exprs) -> emit "\t;exit..."; Some ("%exit_res", "UNDEFINED")
  | Ctrywith(expr1,id,expr2) -> emit "\t;try ... with ..."; Some ("%try_with_res", "UNDEFINED")

and compile_operation op exprs =
  match exprs with
  | [l;r] -> begin
      match (compile_expr l, compile_expr r) with
      | Some (lres, ltype), Some (rres, rtype) -> begin
          counter_inc ();
          match op with
          | Caddi|Csubi|Cmuli|Cdivi|Cmodi|Cand|Cor|Cxor|Clsl|Clsr|Casr ->
              Some (binop (translate_op op) int_type (to_int (lres, ltype) int_type) (to_int (rres, rtype) int_type))
          |Caddf|Csubf|Cmulf|Cdivf ->
              Some (binop (translate_op op) float_type (to_float (lres, ltype)) (to_float (rres, rtype)))
          | Ccmpi op ->
              let (res,_) = binop ("icmp " ^ translate_icomp op) int_type (to_int (lres, ltype) int_type) (to_int (rres, rtype) int_type) in
              Some (convert "zext" (res,"i1") int_type)
          | Ccmpf op ->
              let left = to_float (lres, ltype) in
              let right = to_float (rres, rtype) in
              let (res,_) = binop ("fcmp " ^ translate_fcomp op) float_type left right in
              Some (convert "zext" (res,"i1") int_type)
          | Ccmpa op ->
              let left = to_int (lres, ltype) int_type in
              let right = to_int (rres, rtype) int_type in
              let (res,_) = binop ("icmp " ^ translate_ucomp op) int_type left right in
              Some (convert "zext" (res,"i1") int_type)
          | Cadda | Csuba ->
              (* TODO use getelementptr for pointer arithmetic*)
              let (res, typ) = binop "add" int_type (to_int (lres, ltype) int_type) (to_int (rres, rtype) int_type) in
              Some (inttoptr res (if is_addr ltype then ltype else rtype))
          | _ -> raise (Llvm_error "Not a binary operator")
          end
      | _ -> raise (Llvm_error "compiling arguments of binary operator failed")
    end

  | [arg] -> begin
      match compile_expr arg with
      | Some (res, typ) -> begin
          counter_inc ();
          match op with
          | Cfloatofint ->
              Some (convert "sitofp" (res,int_type) float_type)
          | Cintoffloat ->
              Some (convert "fptosi" (res,float_type) int_type);
          | Cabsf ->
              let mask = Nativeint.to_string (Nativeint.of_string ("0x7" ^ String.make (2 * Arch.size_int - 1) 'f')) in
              let (res,_) = binop "and " float_sized_int mask (to_int (res,typ) float_sized_int) in
              counter_inc ();
              Some (bitcast (res, float_sized_int) float_type)
          | Cnegf ->
              let mask = Nativeint.to_string (Nativeint.of_string ("0x8" ^ String.make (2 * Arch.size_int - 1) '0')) in
              let (res,_) = binop "xor" float_sized_int mask (to_int (res,typ) float_sized_int) in
              counter_inc ();
              Some (bitcast (res, float_sized_int) float_type)
          | Cload mem ->
              let (res,typ) = load (to_addr (res, typ) (translate_mem mem ^ "*"), translate_mem mem ^ "*") in
              if not (is_float typ)
              then Some (to_int (res, typ) int_type, int_type)
              else Some (res, typ) (* TODO this has to be changed to reflect the actual type *)
          | _ -> raise (Llvm_error "wrong op")
        end
      | _ -> raise (Llvm_error "failed to compute argument of unary operator")
    end
  | _ -> raise (Llvm_error "There is no operator with this number of arguments")

let argument_list args = String.concat ", " (List.map (fun (id, _) -> addr_type ^ " %" ^ Ident.name id) args)

let compile_fundecl fd_cmm =
  match fd_cmm with
    ({fun_name=name; fun_args=args; fun_body=body; fun_fast=fast}) ->
      current_args := List.map (fun (id, _) -> Ident.name id) args;
      ignore (List.map (fun (id, typ) -> Hashtbl.add tbl (Ident.name id) addr_type) args);
      emit ("\ndefine " ^ addr_type ^ " @" ^ name ^ "(" ^ argument_list args ^ ") gc \"ocaml\" {");
      emit ("entry:");
      begin
        match compile_expr body with
        | Some (res, typ) -> emit ("\tret " ^ addr_type ^ " " ^ to_addr (res, typ) addr_type)
        | _ -> raise (Llvm_error "compiling body failed")
      end;
      emit "}"

let translate_data = function
  | Csingle s -> "float", s
  | Cdouble s -> float_type, s
  | Cint8 i -> "i8", string_of_int i
  | Cint16 i -> "i16", string_of_int i
  | Cint32 i -> "i32", Nativeint.to_string i
  | Cint i -> int_type, Nativeint.to_string i
  | Cstring s -> "[" ^ string_of_int (String.length s) ^ " x i8]", "c\"" ^ s ^ "\""
  | Calign i -> "void", "align " ^ string_of_int i
  | Cskip i -> "void", "skip " ^ string_of_int i
  | Cdefine_symbol s ->
      let typ = try Hashtbl.find tbl s with Not_found -> "unknown" in
      typ, s
  | _ -> "not implemented", "not implemented"

let data_to_string = function
  | Cdefine_symbol s -> "(define-symbol " ^ s ^ ")"
  | Cglobal_symbol s -> "(global-symbol " ^ s ^ ")"
  | Cdefine_label i -> "(define-label " ^ string_of_int i ^ ")"
  | Cint8 i -> "(int8 " ^ string_of_int i ^ ")"
  | Cint16 i -> "(int16 " ^ string_of_int i ^ ")"
  | Cint32 i -> "(int32 " ^ Nativeint.to_string i ^ ")"
  | Cint i -> "(word " ^ Nativeint.to_string i ^ ")"
  | Csingle s -> "c\"" ^ s ^ "\""
  | Cdouble s -> float_type ^ " " ^ s
  | Csymbol_address s -> "(symbol-address " ^ s ^ ")"
  | Clabel_address i -> "(label-address " ^ string_of_int i ^ ")"
  | Cstring s -> "(string " ^ s ^ ")"
  | Cskip i -> "(skip " ^ string_of_int i ^ ")"
  | Calign i -> "(align " ^ string_of_int i ^ ")"

let data d =
  match d with
  | [] -> emit "; no data"
  | Cint header :: Cglobal_symbol name :: body ->
      Hashtbl.add tbl name "i64";
      let (types, values) = List.fold_left (fun (a,b) (c,d) -> a @ [c], b @ [c ^ " " ^ d]) ([], [])
                              (List.map translate_data (Cint header :: body)) in
      emit (";@" ^ name ^ " = global {" ^ String.concat ", " types ^ "} {" ^
            String.concat ", " values ^ "}")
  | Cint header :: Cdefine_symbol name :: body ->
      Hashtbl.add tbl name "i64";
      let (types, values) = List.fold_left (fun (a,b) (c,d) -> a @ [c], b @ [c ^ " " ^ d]) ([], [])
                              (List.map translate_data (Cint header :: body)) in
      emit (";@" ^ name ^ " = global {" ^ String.concat ", " types ^ "} {" ^
            String.concat ", " values ^ "}")
  | data -> emit (String.concat " " (List.map data_to_string data))
(*  emit ("(" ^ String.concat "\n" (List.map (fun x -> counter_inc ();
  match x with
  | Cdefine_symbol s -> "@" ^ s ^ " = external global " ^ int_type
  | Cdefine_label i -> "; label " ^ string_of_int i
  | Cglobal_symbol s -> "@" ^ s ^ " = external global " ^ int_type
  | Cint8 i -> "@int" ^ c () ^ " = global " ^ int_type ^ " " ^ string_of_int i ^ " ;8 bit"
  | Cint16 i -> "@int" ^ c () ^ " = global " ^ int_type ^ " " ^ string_of_int i ^ " ;16 bit"
  | Cint32 i -> "@int" ^ c () ^ " = global " ^ int_type ^ " " ^ Nativeint.to_string i ^ " ;32 bit"
  | Cint i -> "@int" ^ c () ^ " = global " ^ int_type ^ " " ^ Nativeint.to_string i ^ " ;word"
  | Csingle s -> "@single" ^ c () ^ " = global " ^ float_type ^ " " ^ s ^ " ;single precision float"
  | Cdouble s -> "@double" ^ c () ^ " = global " ^ float_type ^ " " ^ s ^ " ;double precision float"
  | Csymbol_address s -> "; the following will be defined later: @" ^ s
  | Clabel_address i -> ";label_address " ^ string_of_int i
  | Cstring s -> "private constant [" ^ string_of_int (String.length s) ^ " x i8] c\"" ^ s ^ "\""
  | Cskip i -> ";skip " ^ string_of_int i
  | Calign i -> ";align " ^ string_of_int i
  ) d) ^ ")")*)

(* vim: set foldenable : *)
