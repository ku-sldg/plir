(**
 * Programming Languages in Rocq - Mutable State Exercises
 * An explicit, threaded store - Student Problem Set
 *
 * In these exercises you will:
 *   1. Run the store-threading interpreter [evalM] on reference cells,
 *      observing the (value, store) PAIR it returns
 *   2. Use the derived mutable-variable forms and see aliasing
 *   3. Use FUEL MONOTONICITY, simple value laws, and the store lemmas
 *      [update_at_length] / [nth_error_snoc]
 *
 * HOW TO USE THIS FILE
 * --------------------
 * Each exercise ends in [Admitted].  Replace it with a real proof ending
 * in [Qed].  The file compiles as given.
 *
 * From the lecture you have: the language [FBAES]; the value type [RVal]
 * ([NumV]/[BoolV]/[ClosureV]/[LocV]); the store [Store] and interpreter
 * [evalM] with wrapper [eval]; [evalM_mono]; the derived forms
 * [MutBind]/[Get]/[SetVar]; the combinator [Zc].  [lookup]/[extend],
 * [update_at], [update_at_length], and [nth_error_snoc] come from the
 * shared library.
 *
 * NOTE ON FUEL.  Keep fuel a VARIABLE whenever the term is abstract - a
 * literal fuel forces the kernel to unroll [evalM] and can blow up.  A
 * literal fuel is fine only on a CONCRETE closed term.
 *
 * Difficulty: [*] trivial, [**] a lemma citation, [***] short proof.
 * Solutions are in plih_state_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_state_shared.
Require Import plih_state_lecture.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* PART 1: RUNNING THE INTERPRETER                                 *)
(* ================================================================ *)

(* [*] Pure arithmetic leaves the store empty. *)
Example ex1_arith : eval (Plus (Num 2) (Num 3)) = Some (NumV 5, nil).
Proof. Admitted.

(* [*] Allocation returns a location and grows the store. *)
Example ex2_new : eval (New (Num 9)) = Some (LocV 0, [NumV 9]).
Proof. Admitted.

(* [*] A cell round-trip: allocate 0, write 42, read it back. *)
Example ex3_roundtrip :
  eval (Bind "r" (New (Num 0))
          (Seq (Assign (Id "r") (Num 42))
               (Deref (Id "r"))))
  = Some (NumV 42, [NumV 42]).
Proof. Admitted.

(* [*] ALIASING: [a] is bound to [r]'s location, so a write through [a]
   is visible when reading through [r]. *)
Example ex4_aliasing :
  eval (MutBind "r" (Num 5)
          (Bind "a" (Id "r")
             (Seq (SetVar "a" (Num 8))
                  (Get "r"))))
  = Some (NumV 8, [NumV 8]).
Proof. Admitted.

(* [*] DISTINCT cells are independent: writing [p] does not disturb [q]. *)
Example ex5_two_cells :
  eval (Bind "p" (New (Num 1))
          (Bind "q" (New (Num 2))
             (Seq (Assign (Id "p") (Num 9))
                  (Deref (Id "q")))))
  = Some (NumV 2, [NumV 9; NumV 2]).
Proof. Admitted.

(* ================================================================ *)
(* PART 2: DERIVED FORMS AND VALUE LAWS                            *)
(* ================================================================ *)

(* [*] A mutable variable updated in place. *)
Example ex6_mutvar :
  eval (MutBind "n" (Num 10)
          (Seq (SetVar "n" (Minus (Get "n") (Num 3)))
               (Get "n")))
  = Some (NumV 7, [NumV 7]).
Proof. Admitted.

(* [*] A numeral evaluates to itself and leaves the store alone. *)
Example ex7_num : forall k env st n,
  evalM (S k) env st (Num n) = Some (NumV n, st).
Proof. Admitted.

(* [***] Looking up an identifier returns its value with the store
   unchanged.  Hint: [simpl] then [rewrite] the lookup hypothesis. *)
Example ex8_id : forall k env st x v,
  lookup x env = Some v ->
  evalM (S k) env st (Id x) = Some (v, st).
Proof. Admitted.

(* ================================================================ *)
(* PART 3: METATHEORY AND THE STORE                               *)
(* ================================================================ *)

(* [**] Adding fuel cannot change an answer.  Cite [evalM_mono].  Keep the
   fuel a VARIABLE - do not instantiate it to a literal. *)
Example ex9_more_fuel : forall f env st e p,
  evalM f env st e = Some p -> evalM (f + 10) env st e = Some p.
Proof. Admitted.

(* [***] The store-threading interpreter is deterministic for fixed fuel. *)
Example ex10_deterministic : forall f env st e r1 r2,
  evalM f env st e = r1 -> evalM f env st e = r2 -> r1 = r2.
Proof. Admitted.

(* [**] An in-place write preserves the length of the store.  Cite
   [update_at_length]. *)
Example ex11_write_length : forall n v (xs ys : Store),
  update_at n v xs = Some ys -> length ys = length xs.
Proof. Admitted.

(* [**] Reading the location a fresh [New] returns (namely [length xs])
   yields the value just allocated.  Cite [nth_error_snoc]. *)
Example ex12_fresh_read : forall (xs : Store) (v : RVal),
  nth_error (xs ++ [v])%list (length xs) = Some v.
Proof. Admitted.
