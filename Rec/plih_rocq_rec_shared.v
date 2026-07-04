(**
Programming Languages in Rocq - Rec Shared Infrastructure
Untyped Recursion (recursion via fixpoint combinators)

This chapter mirrors the "Untyped Recursion" unit of PLIH:
  https://ku-sldg.github.io/plih//funs/7-Untyped-Recursion.html

The Func chapter showed that first-class functions make the language
powerful enough to LOOP ([omega]), but FBAE has no CONDITIONAL, so a
recursion can never test its argument and stop.  Here we extend FBAE
with Booleans and an [If], giving FBAEC ("FBAE + Conditionals"), and
use it to encode PRODUCTIVE recursion with the Y and Z fixpoint
combinators - no new binding construct required.

As with Func, the language datatype is defined fresh in the lecture.
What we reuse is the general infrastructure - the option monad and the
[Env]/[lookup]/[extend] operations with their lemmas - which reaches
us by re-exporting the Func shared library (itself a chain back to AE).
 *)

Require Export plih_rocq_func_shared.

(* Everything we need is inherited from the chain of shared libraries:
   - [Env A := list (string * A)], [extend], [lookup], and the lemmas
     [lookup_extend_eq]/[lookup_extend_ne] (AE shared);
   - [string_eqb_refl]/[string_eqb_sym] (IDs shared). *)
