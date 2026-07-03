(**
 * Programming Languages in Rocq - Typed Recursion Shared Infrastructure
 * Adding a typed [Fix] to the simply-typed functional language
 *
 * This chapter mirrors the "Typed Recursion" unit of PLIH:
 *   https://ku-sldg.github.io/plih//types/3-Typed-Recursion.html
 *
 * The Typed Functions chapter (TFun) rejected self-application, so [omega]
 * and the Y/Z combinators no longer type-check - RECURSION was lost.  The
 * simply-typed language it left is even STRONGLY NORMALIZING: every
 * well-typed term terminates.  This chapter puts recursion back with a
 * primitive typed [Fix].  Type SAFETY is preserved (well-typed programs
 * never get stuck), but [Fix] deliberately TRADES AWAY normalization: a
 * well-typed term can once again diverge, so the interpreter stays
 * fuel-driven and partial.
 *
 * As with every chapter, the language (types + terms + values) is defined
 * fresh in the lecture - here it is TFun's typed language with one new
 * form, [Fix].  What we reuse is the general infrastructure (the option
 * monad and [Env]/[lookup]/[extend]), inherited by re-exporting the Typed
 * Functions shared library (a chain back through Func to AE).
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_tfun_shared.

(* Everything we need is inherited from the chain of shared libraries:
   - [Env A := list (string * A)], [extend], [lookup], and the lemmas
     [lookup_extend_eq]/[lookup_extend_ne] (AE shared);
   - [string_eqb_refl]/[string_eqb_sym] (IDs shared).
   The TYPE CONTEXT is [Env Ty] and the value environment is [Env TVal] -
   the same association-list machinery, carrying types resp. values. *)
