(**
 * Programming Languages in Rocq - State Monad Shared Infrastructure
 * Structuring the interpreter with a STATE monad
 *
 * This chapter mirrors the "State Monad" idea of PLIH:
 *   https://ku-sldg.github.io/plih//state/
 *
 * The State chapter's interpreter threads a STORE through every recursive
 * call BY HAND - taking it in, naming intermediate stores [s1], [s2], ...,
 * and passing each subexpression the store its predecessor left.  That
 * plumbing is mechanical, repetitive, and a silent bug the moment you pass
 * the wrong store.  A STATE MONAD packages "a computation over a mutable
 * store" so the threading becomes implicit: [get] reads the store, [put]
 * replaces it, and [bind] carries it along automatically.
 *
 * This chapter is about HOW the interpreter is STRUCTURED, not what it
 * computes: we keep the reference-cell language and its explicit
 * store-threading interpreter [evalM] as a reference, build the monadic
 * interpreter [evalS], and PROVE the two agree.
 *
 * As always the language is defined fresh in the lecture; we reuse only
 * the store plumbing ([update_at] and its lemmas) by re-exporting the
 * State shared library.
 *)

Require Export plih_rocq_state_shared.

(* Inherited from the State shared library (and the chain behind it):
   [Env A]/[extend]/[lookup] with their lemmas, and the store plumbing
   [update_at] with [update_at_length]/[update_at_read]/[nth_error_snoc].
   The State monad below threads a store of exactly this shape. *)
