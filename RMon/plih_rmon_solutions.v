(**
Programming Languages in Rocq - Reader Monad Solutions
Complete solutions to plih_rmon_exercises.v

The typed language, the direct [typeof]/[typecheck], the [Reader] monad,
the monadic [typeofR]/[typecheckR], and the agreement theorems all come
from the Reader Monad lecture.
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

Example ex1_ho :
  typecheckR (Lambda "f" (TArr TNum TNum) (App (Id "f") (Num 0)))
  = Some (TArr (TArr TNum TNum) TNum).
Proof. reflexivity. Qed.

Example ex2_reject_if : typecheckR (If (Num 1) (Num 2) (Num 3)) = None.
Proof. reflexivity. Qed.

Example ex3_bind :
  typecheckR (Bind "x" (Num 5) (Plus (Id "x") (Num 1))) = Some TNum.
Proof. reflexivity. Qed.

(** * PART 2: AGREEMENT WITH THE DIRECT CHECKER *)

Example ex4_agree_app : forall ctx,
  typeofR (App inc (Num 4)) ctx = typeof ctx (App inc (Num 4)).
Proof. intros ctx. apply typeofR_agrees. Qed.

Example ex5_typecheck_agree : forall e, typecheckR e = typecheck e.
Proof. intros e. apply typecheckR_agrees. Qed.

(** * PART 3: READER-MONAD LAWS *)

(* [bindR (retR a) f] reduces (with eta) to [f a]. *)
Example ex6_left_id : forall (E A B : Type) (a : A) (f : A -> Reader E B),
  bindR (retR a) f = f a.
Proof. reflexivity. Qed.

Example ex7_ask : forall (E : Type) (e : E), runR askR e = Some e.
Proof. reflexivity. Qed.

Example ex8_local : forall (E A : Type) (g : E -> E) (m : Reader E A) (e : E),
  runR (localR g m) e = runR m (g e).
Proof. reflexivity. Qed.
