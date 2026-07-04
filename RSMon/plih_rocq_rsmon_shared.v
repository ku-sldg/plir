(**
Programming Languages in Rocq - Reader+State Monad Shared Infrastructure
Structuring the interpreter with a combined READER + STATE monad

This chapter mirrors the "monad transformers" idea of PLIH - combining
the effects seen separately so far:
  https://ku-sldg.github.io/plih//state/

Two chapters set up the pieces.  RMon used a READER monad to hide the
read-only type CONTEXT in the checker.  SMon used a STATE monad to hide
the mutable STORE in the evaluator - but there the ENVIRONMENT was still
an explicit argument.  This chapter combines both: one monad that hides
the (read-only) environment via Reader operations AND the (mutable)
store via State operations, so the interpreter carries NEITHER by hand.

As with SMon, this is about HOW the interpreter is STRUCTURED, not what
it computes: we keep the reference-cell language and its explicit
interpreter [evalM] (threading BOTH env and store by hand) as a
reference, build the combined-monad interpreter [evalRS], and PROVE they
agree.

The language is defined fresh in the lecture; we reuse only the store
plumbing ([update_at] and its lemmas) by re-exporting the State-monad
shared library (itself a chain back through State to AE).
 *)

Require Export plih_rocq_smon_shared.

(* Inherited from the chain: [Env A]/[extend]/[lookup] with their lemmas,
   and the store plumbing [update_at] / [update_at_length] /
   [update_at_read] / [nth_error_snoc].  The combined monad below threads
   an environment of shape [Env RVal] and a store of shape [Store]. *)
