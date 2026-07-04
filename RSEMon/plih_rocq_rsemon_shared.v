(**
Programming Languages in Rocq - Reader+State+Either Monad Shared Infra
Stacking THREE effects: environment, store, and error messages

This chapter mirrors the effect-combining ("monad transformer") idea of
PLIH, taken to its conclusion:
  https://ku-sldg.github.io/plih//state/

RSMon combined a READER (read-only environment) with a STATE (mutable
store) in one monad.  EMon showed how an EITHER layer replaces silent
failure ([None]) with descriptive error MESSAGES, and that the refined
checker REFINES the plain one ([forget] erases the message).  This
chapter stacks all three: an interpreter that reads its environment,
mutates its store, AND reports typed failures, in a single monad

  RSE E S A := E -> S -> sum string (A * S)

and we prove it REFINES the explicit [evalM]: forgetting the error
message recovers exactly the option-valued answer.

The language is defined fresh in the lecture; we reuse only the store
plumbing ([update_at] and its lemmas) by re-exporting the Reader+State
shared library (a chain back through SMon/State to AE).
 *)

Require Export plih_rocq_rsmon_shared.

(* Inherited from the chain: [Env A]/[extend]/[lookup] with their lemmas,
   and the store plumbing [update_at] / [update_at_length] /
   [update_at_read] / [nth_error_snoc].  The combined monad below threads
   an environment [Env RVal] and a store [Store], and adds an error channel
   carrying a [string] message. *)
