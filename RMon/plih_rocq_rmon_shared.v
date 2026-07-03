(**
 * Programming Languages in Rocq - Reader Monad Shared Infrastructure
 * Structuring the type checker with a READER monad
 *
 * This chapter mirrors the "More Reader Monad" unit of PLIH:
 *   https://ku-sldg.github.io/plih//types/5-More-Reader-Monad.html
 *
 * The type checkers of TFun and TRec thread a type CONTEXT [ctx] through
 * every recursive call by hand - passing it in, extending it for [Bind]
 * and [Lambda], reading it for [Id].  That plumbing is mechanical and
 * repetitive.  A READER MONAD packages "a computation that may consult a
 * fixed context" so the threading becomes implicit: [ask] reads the
 * context, [local] runs a sub-computation under a modified one, and [bind]
 * carries the context along automatically.
 *
 * This chapter is about HOW the checker is STRUCTURED, not what it checks:
 * we keep the typed language (with [Fix]) and its direct checker [typeof]
 * as a reference, build the monadic checker [typeofR], and PROVE the two
 * agree.  The evaluator is unchanged from Typed Recursion and omitted.
 *
 * As always the language is defined fresh in the lecture; we reuse only
 * the general infrastructure ([Env]/[lookup]/[extend]) by re-exporting the
 * Typed Recursion shared library.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_trec_shared.

(* Inherited from the shared-library chain: [Env A := list (string * A)],
   [extend], [lookup], and [lookup_extend_eq]/[lookup_extend_ne].  The type
   CONTEXT is [Env Ty]; the Reader monad below threads exactly this. *)
