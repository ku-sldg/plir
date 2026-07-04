(**
Programming Languages in Rocq - Func Shared Infrastructure
Adding Functions (the FBAE language: first-class Functions +
Bind + Arithmetic Expressions)

This chapter mirrors the "Functions" unit of PLIH:
  https://ku-sldg.github.io/plih//funs/1-Adding-Functions.html
  https://ku-sldg.github.io/plih//funs/2-Scoping.html

FBAE extends the BAE language with two new forms:
  - [Lambda x b] : an anonymous, FIRST-CLASS function
  - [App f a]    : function application

We do NOT reuse the BAE datatype from the IDs chapter - functions
change the language enough that FBAE is defined fresh in the lecture.
What we DO reuse is the general-purpose infrastructure: the option
monad, the [Env]/[lookup]/[extend] operations, and the [String.eqb]
name-comparison lemmas.  All of that reaches us by re-exporting the
IDs shared library (which itself re-exports the AE shared library).
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Export plih_rocq_ids_shared.

(* Everything we need is inherited:
   - [Env A := list (string * A)], [extend x v env := (x,v)::env],
     [lookup], [lookup_extend_eq], [lookup_extend_ne] from the AE
     shared library;
   - [string_eqb_refl], [string_eqb_sym] from the IDs shared library. *)
