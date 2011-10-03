open Cmm

exception Llvm_error of string

let counter = ref 0
let instrs = ref ([] : string list)

let instructions () =
  String.concat "\n" (List.rev !instrs)

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
  | Cdivi -> "sdiv"
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

let types = Hashtbl.create 10

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

let emit str = instrs := str :: !instrs

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
let getelementptr (addr, addr_type) (offset, offset_type) =
  emit ("\t%ptr" ^ c () ^ " = getelementptr " ^ addr_type ^ " " ^ addr ^ ", " ^ offset_type ^ " " ^ offset);
  "%ptr" ^ c (), addr_type
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
  let src_len = try int_of_string (String.sub typ 1 (String.length typ - 1))
                with Failure s -> raise (Llvm_error ("could not convert src_len ("^typ^") to int")) in
  let dest_len = try int_of_string (String.sub dest_type 1 (String.length dest_type - 1))
                 with Failure s->raise(Llvm_error("could not convert dest_len ("^dest_type^") to int")) in
  if src_len == dest_len
  then value, dest_type
  else if src_len > dest_len
       then convert "trunc" (value, typ) dest_type
       else convert "zext" (value, typ) dest_type

let to_int (value, typ) =
  if is_int typ
  then (value, typ)
  else begin
    counter_inc ();
    if is_addr typ
    then ptrtoint (value,typ) int_type
    else if is_float typ
         then bitcast (value, typ) float_sized_int
         else adjust_length (value, typ) int_type
  end

let to_float (value, typ) =
  if compare typ float_type == 0
  then value
  else (emit ";converting to float..."; fst (bitcast (value,typ) float_type))

let translate_symbol s =
  let result = ref "" in
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    match c with
      'A'..'Z' | 'a'..'z' | '0'..'9' | '_' ->
          result := !result ^ Printf.sprintf "%c" c
    | _ -> result := !result ^ Printf.sprintf "$%02x" (Char.code c)
  done;
  !result

let constants = ref ([] : string list)
let functions = ref ([] : (string * string list) list)

let add_const str =
  if List.exists (fun x -> String.compare x str == 0) !constants
  then ()
  else constants := str :: !constants

let add_function (str, args) =
  if List.exists (fun (x,_) -> String.compare x str == 0) !functions
  then ()
  else functions := (str, List.map (fun _ -> addr_type) args) :: !functions

(* returns a tuple of
 -- instructions to execute before using the result of this operation
 -- the virtual register of the result
 -- the type of the result
 *)
let rec compile_expr expr = match expr with
  | Cconst_int i        -> Some (string_of_int i, int_type)
  | Cconst_natint i     -> Some (Nativeint.to_string i, int_type)
  | Cconst_float f      -> Some (f, float_type)
  | Cconst_symbol s     -> add_const s; Some ("@" ^ translate_symbol s, addr_type)
  | Cconst_pointer i    -> Some (inttoptr_const (string_of_int i) addr_type, addr_type)
  | Cconst_natpointer i -> Some (inttoptr_const (Nativeint.to_string i) addr_type, addr_type)

  | Cvar id -> begin
      counter_inc ();
      let name = Ident.name id in
      let typ = try Hashtbl.find types name
                with Not_found -> raise (Llvm_error ("Could not find identifier " ^ name ^ ".")) in
      if is_arg name
      then Some ("%" ^ translate_symbol name, typ)
      else Some (load ("%" ^ translate_symbol name, typ ^ "*"))
    end
  | Clet(id,arg,body) -> begin
      let name = Ident.name id in
      match compile_expr arg with
      | Some (res_arg, type_arg) -> begin
          counter_inc ();
          let typ = if is_float type_arg then float_type else int_type in
          let res, typ = if Hashtbl.mem types name
                         then res_arg, typ ^ "*"
                         else begin
                           Hashtbl.add types name typ;
                           alloca ("%" ^ translate_symbol name) typ
                         end in
          store (to_int (res_arg, type_arg)) ("%" ^ name, typ);
          compile_expr body
        end
      | _ -> raise (Llvm_error "failed to compile argument of let statement")
    end
  | Cassign(id,expr) -> begin
      match compile_expr expr with
      | Some (res, typ) ->
          emit "; assignment";
          counter_inc ();
          let name = Ident.name id in
          let typ = try Hashtbl.find types name
                    with Not_found -> raise (Llvm_error ("not found: " ^ name)) in
          store (res,typ) ("%" ^ name, typ ^ "*");
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
      | Cconst_symbol s :: res ->
          let results =
            List.map (fun x -> match compile_expr x with
                        | Some res -> addr_type ^ " " ^ to_addr res addr_type
                        | None -> raise (Llvm_error "could not compile argument")) res in
          counter_inc ();
          add_function (s, results);
          emit ("\t%call_res" ^ c () ^ " = call " ^ addr_type ^ " @" ^ s ^ "(" ^ String.concat ", " results ^ ")");
          Some ("%call_res" ^ c (), addr_type)
      | ptr :: res -> begin
          match compile_expr ptr with
          | Some (fn, _) ->
              let results =
                List.map (fun x -> match compile_expr x with
                            | Some res -> addr_type ^ " " ^ to_addr res addr_type
                            | None -> raise (Llvm_error "could not compile argument")) res in
              counter_inc ();
              emit ("\t%call_res" ^ c () ^ " = call " ^ addr_type ^ " " ^ fn ^ "(" ^ String.concat ", " results ^ ")");
              Some ("%call_res" ^ c (), addr_type)
          | None -> raise (Llvm_error "could not compute the function's address")
        end
      | [] -> raise (Llvm_error "no function specified")
    end
  | Cop(Cextcall(fn, typ, alloc, debug), exprs) ->
      counter_inc ();
      let args =
        List.map (fun x -> match compile_expr x with
                    | Some res -> addr_type ^ " " ^ to_addr res addr_type
                    | None -> raise (Llvm_error "could not compile argument")) exprs in
      add_function (fn, args);
      (* TODO store caml_last_return_address, caml_bottom_of_stack,
      * caml_young_ptr, caml_exception_pointer *)
      emit ("\t%extcall_res" ^ c () ^ " = call ccc " ^ addr_type ^ " @" ^ fn ^ "(" ^ String.concat "," args ^ ")");
      (* TODO load caml_young_ptr *)
      Some ("%extcall_res" ^ c (), addr_type)
  | Cop(Calloc, header :: args) -> begin
      match compile_expr header with
      | Some (res, typ) ->
          emit "; begin allocation";
          counter_inc ();
          let len = string_of_int (Arch.size_int * List.length (header :: args)) in
          add_const "caml_young_pointer";
          let (res, _) = load ("@caml_young_pointer", addr_type) in
          emit ("\t%new_young_ptr_int" ^ c () ^ " = sub " ^ int_type ^ " " ^ res ^ ", " ^ len);
          (* TODO check whether we have to call the garbage collector *)
          emit ("\t; if %new_young_ptr_int < @caml_young_limit then run gc");
          store ("%new_young_ptr_int" ^ c (), int_type) ("@caml_young_pointer", addr_type);
          let (res_header, typ) = inttoptr ("%new_young_ptr_int" ^ c ()) addr_type in
          let (res_ptr, typ) = ptrtoint (res_header, typ) int_type in
          let (res, _) = binop "add" typ res_ptr (string_of_int size_int) in
(*          emit ("\t" ^ res ^ " = add " ^ typ ^ " " ^ res_ptr ^ ", " ^ string_of_int size_int);*)
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
            store (to_int (x, typ)) ("%elemptr." ^ num ^ "." ^ c (), addr_type) in
          List.iter emit_arg args;
          emit "; end allocation";
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
          emit "; rasing exception";
          counter_inc ();
          emit ("\tunwind ;raise exception..." ^ res);
          None
      | _ -> raise (Llvm_error "could not compile subexpression of raise")
    end
  | Cop(Craise _, _) -> raise (Llvm_error "wrong number of arguments for Craise")
  | Cop(Ccheckbound debug, [arr; index]) -> begin
      match (compile_expr arr, compile_expr index) with
      | Some (res_arr, type_arr), Some (res_index, type_index) ->
          counter_inc ();
          emit ("\t;checking bounds of " ^ res_arr);
          let (header, _) = getelementptr (to_addr (res_arr, type_arr) addr_type, addr_type)
                              ("-" ^ string_of_int Arch.size_addr, int_type) in
          let (length, _) = load (header, addr_type) in
          let (res, typ) = binop "lshr" int_type length "10" in
          counter_inc ();
          let (res, typ) = binop "shl" typ res "3" in
          counter_inc ();
          let (res, typ) = binop "sub" typ res "1" in
          counter_inc ();
          let (cond, _) = binop "icmp ule" typ res_index res in
          emit ("\tbr i1 " ^ cond ^ ", label %out_of_bounds" ^ c () ^ ", label %ok" ^ c ());
          emit ("out_of_bounds" ^ c () ^ ":");
          add_function ("caml_ml_array_bound_error", []);
          emit ("\t%res_call" ^ c () ^ " = call " ^ addr_type ^ " @caml_ml_array_bound_error()");
          emit ("\tbr label %ok" ^ c ());
          emit ("ok" ^ c () ^ ":");
          None
      | _, _ -> raise (Llvm_error "could not compile array or index argument of checkbound")
    end
  | Cop(Ccheckbound _, _) -> raise (Llvm_error "not implemented: checkound with #args != 2")
  | Cop(op, exprs) -> compile_operation op exprs

  | Csequence(fst,snd) ->
      ignore (compile_expr fst);
      compile_expr snd
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
              store (to_int (res1, type1)) (if_res, res_type);
              emit ("\tbr label %fi" ^ c ^ "\n");
              emit ("else" ^ c ^ ":");
              match compile_expr expr2 with
              | Some (res2, type2) ->
                  store (to_int (res2, type2)) (if_res, addr_type);
              | None -> ()
            end
          | None -> begin
              emit ("\tbr label %fi" ^ c ^ "\n");
              emit ("else" ^ c ^ ":");
              match compile_expr expr2 with
              | Some (res2, type2) ->
                  store (to_int (res2, type2)) (if_res, addr_type);
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
      emit "; begin of loop";
      let c = c () in
      counter_inc ();
      emit ("\tbr label %loop" ^ c);
      emit ("loop" ^ c ^ ":");
      ignore(compile_expr expr);
      emit ("\tbr label %loop" ^ c);
      emit ("\tunreachable");
      counter_inc ();
      emit "; end of loop";
      None
    end
  | Ccatch(i,ids,expr1,expr2) ->
      counter_inc ();
      emit ("\t; catch " ^ string_of_int i);
      emit "; expression 1";
      ignore (compile_expr expr1);
      emit "; expression 2";
      ignore (compile_expr expr2);
      emit ("\tbr label %exit" ^ string_of_int i);
      emit ("exit" ^ string_of_int i ^ ":");
      Some ("%catch_res", int_type)
  | Cexit(i,exprs) ->
      counter_inc ();
      emit ("\t; exit " ^ string_of_int i);
      emit ("\t; expressions...");
      emit ("\tbr label %exit" ^ string_of_int i);
      None
  | Ctrywith(expr1,id,expr2) ->
      counter_inc ();
      emit "\t; try-with-statament";
      Some ("%try_with_res", int_type)

and compile_operation op exprs =
  match exprs with
  | [l;r] -> begin
      match (compile_expr l, compile_expr r) with
      | Some (lres, ltype), Some (rres, rtype) -> begin
          counter_inc ();
          match op with
          | Caddi|Csubi|Cmuli|Cdivi|Cmodi|Cand|Cor|Cxor|Clsl|Clsr|Casr ->
              Some (binop (translate_op op) int_type
                      (fst (to_int (lres, ltype)))
                      (fst (to_int (rres, rtype))))
          |Caddf|Csubf|Cmulf|Cdivf ->
              Some (binop (translate_op op) float_type
                      (to_float (lres, ltype))
                      (to_float (rres, rtype)))
          | Ccmpi op ->
              let (res,_) = binop ("icmp " ^ translate_icomp op) int_type
                              (fst (to_int (lres, ltype)))
                              (fst (to_int (rres, rtype))) in
              Some (convert "zext" (res,"i1") int_type)
          | Ccmpf op ->
              let left = to_float (lres, ltype) in
              let right = to_float (rres, rtype) in
              let (res,_) = binop ("fcmp " ^ translate_fcomp op) float_type left right in
              Some (convert "zext" (res,"i1") int_type)
          | Ccmpa op ->
              let left, _ = to_int (lres, ltype) in
              let right, _ = to_int (rres, rtype) in
              let (res,_) = binop ("icmp " ^ translate_ucomp op) int_type left right in
              Some (convert "zext" (res,"i1") int_type)
          | Cadda | Csuba ->
              let (res, typ) = binop "add" int_type
                                 (fst (to_int (lres, ltype)))
                                 (fst (to_int (rres, rtype))) in
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
              let (res,_) = binop "and " float_sized_int mask (fst (to_int (res, typ))) in
              counter_inc ();
              Some (bitcast (res, float_sized_int) float_type)
          | Cnegf ->
              let mask = Nativeint.to_string (Nativeint.of_string ("0x8" ^ String.make (2 * Arch.size_int - 1) '0')) in
              let (res,_) = binop "xor" float_sized_int mask (fst (to_int (res,typ))) in
              counter_inc ();
              Some (bitcast (res, float_sized_int) float_type)
          | Cload mem ->
              let (res,typ) = load (to_addr (res, typ) (translate_mem mem ^ "*"), translate_mem mem ^ "*") in
              if not (is_float typ)
              then Some (adjust_length (res, typ) int_type)
              else Some (res, typ) (* TODO this has to be changed to reflect the actual type *)
          | _ -> raise (Llvm_error "wrong op")
        end
      | _ -> raise (Llvm_error "failed to compute argument of unary operator")
    end
  | _ -> raise (Llvm_error "There is no operator with this number of arguments")

let argument_list args = String.concat ", " (List.map (fun (id, _) -> addr_type ^ " %" ^ translate_symbol (Ident.name id)) args)

let emit_function_declarations () =
  List.iter (fun (name, args) -> print_endline ("declare " ^ addr_type ^ " @" ^ name ^
                                     "(" ^ String.concat "," args ^ ")")) !functions
let emit_constant_declarations () =
  List.iter (fun name -> print_endline ("@" ^ name ^ " = external global " ^ int_type)) !constants

let compile_fundecl fd_cmm =
  counter := 0;
  try
  match fd_cmm with
    ({fun_name=name; fun_args=args; fun_body=body; fun_fast=fast}) ->
      current_args := List.map (fun (id, _) -> Ident.name id) args;
      Hashtbl.clear types;
      ignore (List.map (fun (id, typ) -> Hashtbl.add types (Ident.name id) addr_type) args);
      emit ("\ndefine cc 11 " ^ addr_type ^ " @" ^ name ^ "(" ^ argument_list args ^ ") gc \"ocaml\" {");
      emit ("entry:");
      begin
        match compile_expr body with
        | Some (res, typ) -> emit ("\tret " ^ addr_type ^ " " ^ to_addr (res, typ) addr_type)
        | _ -> raise (Llvm_error "compiling body failed")
      end;
      emit "}"
  with Llvm_error s -> print_endline s;
                       emit_function_declarations ();
                       emit_function_declarations ();
                       print_endline (String.concat "\n" (List.rev !instrs));
                       raise (Llvm_error s)

let data d = ()

(* vim: set foldenable : *)
