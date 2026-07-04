(**
Programming Languages in Rocq - Untyped Recursion Solutions
Complete solutions to plih_rec_exercises.v

The language [FBAEC], the interpreters [evalM]/[evalL] with wrappers
[eval]/[evalLazy], the metatheorem [evalM_mono], the combinators
[Yc]/[Zc], and the generators [sumGen]/[factGen] all come from the
Untyped Recursion lecture.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rec_shared.
Require Import plih_rec_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE INTERPRETERS *)

Example ex1_arith : eval (Minus (Mult (Num 3) (Num 4)) (Num 2)) = Some (NumV 10).
Proof. reflexivity. Qed.

Example ex2_if : eval (If (IsZero (Num 3)) (Num 0) (Num 9)) = Some (NumV 9).
Proof. reflexivity. Qed.

Example ex3_sum3 : eval (App (App Zc sumGen) (Num 3)) = Some (NumV 6).
Proof. reflexivity. Qed.

Example ex4_fact4 : eval (App (App Zc factGen) (Num 4)) = Some (NumV 24).
Proof. reflexivity. Qed.

Example ex5_fact4_lazy : evalLazy (App (App Yc factGen) (Num 4)) = Some (LNumV 24).
Proof. reflexivity. Qed.

Example ex6_Y_strict_diverges :
  evalM 100 nil (App (App Yc factGen) (Num 4)) = None.
Proof. reflexivity. Qed.

(** * PART 2: VALUE AND BRANCH LAWS *)

Example ex7_boolean : forall k env b,
  evalM (S k) env (Boolean b) = Some (BoolV b).
Proof. reflexivity. Qed.

(* The condition [Boolean true] needs fuel of its own, so split on [k]:
   with [k = 0] both sides are [None]; otherwise both step to
   [evalM k env t]. *)
Example ex8_if_true : forall k env t f,
  evalM (S k) env (If (Boolean true) t f) = evalM k env t.
Proof. intros k env t f. destruct k; reflexivity. Qed.

(** * PART 3: FUEL MONOTONICITY *)

Example ex9_more_fuel : forall f env e v,
  evalM f env e = Some v -> evalM (f + 10) env e = Some v.
Proof.
  intros f env e v H.
  apply (evalM_mono f (f + 10) env e v); [lia | exact H].
Qed.

Example ex10_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. intros f env e r1 r2 H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.
