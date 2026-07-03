(**
 * Programming Languages in Rocq - Reader+Either Monad Solutions
 * Complete solutions to plih_emon_exercises.v
 *
 * The typed language, the direct [typeof]/[typecheck], the combined
 * [RE] monad, the checker [typeofE]/[typecheckE], [forget], and the
 * refinement theorems all come from the Reader+Either Monad lecture.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_emon_shared.
Require Import plih_emon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* PART 1: RUNNING THE MESSAGE-CARRYING CHECKER                   *)
(* ================================================================ *)

Example ex1_ok : typecheckE (Bind "x" (Num 5) (IsZero (Id "x"))) = inr TBool.
Proof. reflexivity. Qed.

Example ex2_if_msg :
  typecheckE (If (Boolean true) (Num 1) (Boolean false))
  = inl "if: branches must have the same type".
Proof. reflexivity. Qed.

Example ex3_app_msg :
  typecheckE (App (Num 1) (Num 2)) = inl "app: applying a non-function".
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 2: REFINEMENT OF THE DIRECT CHECKER                       *)
(* ================================================================ *)

Example ex4_refine_app : forall ctx,
  forget (typeofE (App inc (Num 4)) ctx) = typeof ctx (App inc (Num 4)).
Proof. intros ctx. apply typeofE_refines. Qed.

Example ex5_refine_top : forall e, forget (typecheckE e) = typecheck e.
Proof. intros e. apply typecheckE_refines. Qed.

(* ================================================================ *)
(* PART 3: MONAD LAWS                                              *)
(* ================================================================ *)

Example ex6_left_id : forall (E A B : Type) (a : A) (f : A -> RE E B),
  bindE (retE a) f = f a.
Proof. reflexivity. Qed.

Example ex7_throw_short : forall (E A B : Type) (msg : string) (f : A -> RE E B),
  bindE (throwE msg) f = throwE msg.
Proof. reflexivity. Qed.

Example ex8_ask : forall (E : Type) (e : E), runE askE e = inr e.
Proof. reflexivity. Qed.
