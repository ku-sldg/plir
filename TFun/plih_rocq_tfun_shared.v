(**
Programming Languages in Rocq - Typed Functions Shared Infrastructure
Adding Types (the TFBAEC language: a TYPED version of Rec's FBAEC)

This chapter mirrors the "Typed Functions" unit of PLIH:
  https://ku-sldg.github.io/plih//types/1-Function-Types.html
  https://ku-sldg.github.io/plih//types/2-Adding-Booleans.html   (source stub)

The Func and Rec chapters built an UNTYPED language that is Turing
powerful: [omega] loops, [evalM] is inescapably partial, and nothing
stops you from adding a Boolean to a number - that error is only
discovered (as [None]) at run time.  This chapter adds a STATIC TYPE
SYSTEM so those errors are caught BEFORE evaluation.

As with every chapter, the language (types + terms + values) is defined
fresh in the lecture.  What we reuse from earlier chapters is the
general-purpose infrastructure: the option monad, the [Env]/[lookup]/
[extend] operations, and the [String.eqb] name-comparison lemmas.  All
of that reaches us by re-exporting the Func shared library (which itself
re-exports the IDs and AE shared libraries).

DESIGN NOTE - STRICT EVALUATION ONLY.  Func and Rec each carried two
interpreters (a strict [evalM] and a lazy [evalL]).  From this chapter
on we keep ONLY the strict, call-by-value interpreter: the typed
language pairs ONE evaluator with a TYPE CHECKER, and the headline
metatheorem shifts from fuel monotonicity to TYPE SOUNDNESS.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_func_shared.

(* Everything we need is inherited:
   - [Env A := list (string * A)], [extend x v env := (x,v)::env],
     [lookup], [lookup_extend_eq], [lookup_extend_ne] from the AE
     shared library;
   - [string_eqb_refl], [string_eqb_sym] from the IDs shared library.
   The TYPE CONTEXT used by the type checker is just [Env Ty] - the very
   same association-list machinery, carrying types instead of values. *)
