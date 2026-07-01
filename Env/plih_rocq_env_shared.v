(**
 * Programming Languages in Rocq - Env Shared Infrastructure
 * Adding Environments
 *
 * This chapter mirrors "Adding Environments" from PLIH:
 *   https://ku-sldg.github.io/plih//ids/2-Adding-Environments.html
 *
 * It keeps the SAME BAE language from the "Adding Identifiers" chapter,
 * but replaces eager substitution with a DEFERRED environment.  So we
 * re-export the IDs lecture wholesale: it gives us [BAE], [subst], the
 * substitution interpreter [eval], [size], the free-variable machinery,
 * and - crucially - lets us PROVE that the environment interpreter
 * agrees with the substitution interpreter.
 *
 * The environment type itself, [Env], together with [lookup] and
 * [extend], already lives in the AE shared library and reaches us
 * through this re-export chain.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Export plih_rocq_ids_shared.
Require Export plih_ids_lecture.

(* Everything we need is inherited.  [Env A := list (string * A)],
   [extend x v env := (x,v) :: env], and [lookup] come from the AE
   shared library; [BAE]/[subst]/[eval]/[size]/[free_in] come from the
   IDs lecture. *)
