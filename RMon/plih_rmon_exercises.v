(**
Programming Languages in Rocq - Reader Monad Exercises
Structuring the type checker with a Reader monad - Student Problem Set

In these exercises you will:
  1. Run the MONADIC type checker [typeofR]/[typecheckR]
  2. Use the AGREEMENT theorem relating it to the direct [typeof]
  3. Verify small READER-monad laws

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: [Ty]/[Ty_eqb], the terms [TFBAEC], the direct
checker [typeof]/[typecheck], the [Reader] monad
([retR]/[bindR]/[askR]/[localR]/[failR]/[runR] with [;;]), the monadic
checker [typeofR]/[typecheckR], the theorems [typeofR_agrees] and
[typecheckR_agrees], and the sample terms [inc]/[factGen].

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof.
Solutions are in plih_rmon_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rmon_shared.
Require Import plih_rmon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE MONADIC CHECKER *)

(* ★ A well-typed higher-order function has a function type. *)
Example ex1_ho :
  typecheckR (Lambda "f" (TArr TNum TNum) (App (Id "f") (Num 0)))
  = Some (TArr (TArr TNum TNum) TNum).
Proof. Admitted.

(* ★ A non-Boolean [If] condition is rejected (the monad fails). *)
Example ex2_reject_if : typecheckR (If (Num 1) (Num 2) (Num 3)) = None.
Proof. Admitted.

(* ★ [Bind] extends the context via [localR]; here the body sees [x:Nat]. *)
Example ex3_bind :
  typecheckR (Bind "x" (Num 5) (Plus (Id "x") (Num 1))) = Some TNum.
Proof. Admitted.

(** * PART 2: AGREEMENT WITH THE DIRECT CHECKER *)

(* ★★ On a concrete term the monadic and direct checkers agree at every
   context.  Cite [typeofR_agrees]. *)
Example ex4_agree_app : forall ctx,
  typeofR (App inc (Num 4)) ctx = typeof ctx (App inc (Num 4)).
Proof. Admitted.

(* ★★ The top-level monadic checker equals the direct one.  Cite the
   agreement theorem. *)
Example ex5_typecheck_agree : forall e, typecheckR e = typecheck e.
Proof. Admitted.

(** * PART 3: READER-MONAD LAWS *)

(* ★★ Left identity: binding a pure value just applies the function. *)
Example ex6_left_id : forall (E A B : Type) (a : A) (f : A -> Reader E B),
  bindR (retR a) f = f a.
Proof. Admitted.

(* ★ [askR] hands back exactly the environment it is run in. *)
Example ex7_ask : forall (E : Type) (e : E), runR askR e = Some e.
Proof. Admitted.

(* ★ [localR g m] runs [m] in the transformed environment. *)
Example ex8_local : forall (E A : Type) (g : E -> E) (m : Reader E A) (e : E),
  runR (localR g m) e = runR m (g e).
Proof. Admitted.

(** * PART 4: CONCRETE SYNTAX *)

(**
The typed language gets TRec's two notations: types between [<[ ... ]>]
([Nat], [Bool], the right-associative [->]) and terms between
[<{ ... }>] with the ascribed lambda [lambda ID : T in body] and the
prefix [fix f].  Read the concrete terms through the MONADIC checker
[typecheckR].
 *)

Open Scope rmon_scope.

(* ★ the function arrow is right-associative. *)
Example ex9_parse_ty :
  <[ Nat -> Nat -> Nat ]> = TArr TNum (TArr TNum TNum).
Proof. Admitted.

(* ★★ the monadic checker reads the concrete term and predicts its type. *)
Example ex10_typecheck_concrete :
  typecheckR <{ lambda "f" : Nat -> Nat in "f" 0 }>
  = Some <[ (Nat -> Nat) -> Nat ]>.
Proof. Admitted.

(* ★★ [fix] of the factorial generator checks at [Nat -> Nat]. *)
Example ex11_typecheck_fix :
  typecheckR <{ fix (lambda "g" : Nat -> Nat in
                       lambda "n" : Nat in
                         if iszero "n" then 1
                         else "n" * ("g" ("n" - 1))) }>
  = Some <[ Nat -> Nat ]>.
Proof. Admitted.
