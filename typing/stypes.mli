(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*          Damien Doligez, projet Moscova, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2003 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Recording and dumping (partial) type information *)

(* Clflags.save_types must be true *)

open Typedtree;;

type annotation =
  | Ti_pat   of pattern
  | Ti_expr  of expression
  | Ti_class of class_expr
  | Ti_mod   of module_expr
  | An_call of Location.t * Annot.call
  | An_ident of Location.t * string * Annot.ident
;;

val record : annotation -> unit;;
val record_phrase : Location.t -> unit;;
val dump : string -> unit;;

val get_location : annotation -> Location.t;;
val get_info : unit -> annotation list;;
