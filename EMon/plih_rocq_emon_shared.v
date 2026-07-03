(**
 * Programming Languages in Rocq - Reader+Either Monad Shared Infrastructure
 * Informative type errors with a combined Reader-and-Either monad
 *
 * This chapter mirrors the "Reader and Either" unit of PLIH:
 *   https://ku-sldg.github.io/plih//types/6-Reader-And-Either.html
 * (The source page for this chapter is a placeholder, so - as we did for
 *  the Booleans chapter - we develop the standard content ourselves.)
 *
 * The Reader Monad chapter (RMon) hid the context threading but still
 * reported every failure as a bare [None] - "ill-typed", with no reason.
 * This chapter keeps the Reader threading and adds the EITHER monad on top
 * so a rejected program carries an informative error MESSAGE
 * ([inl "..."]).  The combined monad [RE E A = E -> string + A] both reads
 * a context AND may fail with a message.
 *
 * We keep the same typed language and direct checker [typeof] as a
 * reference, and prove the message-carrying checker REFINES it: forgetting
 * the message recovers RMon's [option] answer.  As always the language is
 * defined fresh in the lecture; only [Env]/[lookup]/[extend] are reused,
 * by re-exporting the Reader Monad shared library.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_rmon_shared.

(* Inherited: [Env]/[extend]/[lookup] and their lemmas.  The context is
   [Env Ty]; the combined monad below threads it and may fail with a
   [string] message. *)
