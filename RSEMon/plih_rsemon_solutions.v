(**
 * Programming Languages in Rocq - Reader+State+Either Monad Solutions
 * Complete solutions to plih_rsemon_exercises.v
 *
 * The language [FBAES], the explicit interpreter [evalM]/[eval], the
 * three-effect monad ([retRSE]/[bindRSE]/[askRSE]/[localRSE]/[getRSE]/
 * [putRSE]/[throwRSE]/[runRSE]), [forget], the monadic interpreter
 * [evalRSE]/[evalRSErr], and the theorems [evalRSE_refines] /
 * [evalRSErr_refines] all come from the Reader+State+Either lecture.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rsemon_shared.
Require Import plih_rsemon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* PART 1: RUNNING THE THREE-EFFECT INTERPRETER                   *)
(* ================================================================ *)

Example ex1_arith :
  evalRSErr (Minus (Mult (Num 3) (Num 4)) (Num 2)) = inr (NumV 10, nil).
Proof. reflexivity. Qed.

Example ex2_roundtrip :
  evalRSErr (Bind "r" (New (Num 0))
               (Seq (Assign (Id "r") (Num 42))
                    (Deref (Id "r"))))
  = inr (NumV 42, [NumV 42]).
Proof. reflexivity. Qed.

Example ex3_unbound :
  evalRSErr (Id "nope") = inl "unbound identifier".
Proof. reflexivity. Qed.

Example ex4_type_error :
  evalRSErr (Plus (Num 1) (Boolean true)) = inl "plus: operands must be numbers".
Proof. reflexivity. Qed.

Example ex5_not_a_location :
  evalRSErr (Deref (Boolean true)) = inl "deref: not a location".
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 2: REFINEMENT IN ACTION                                    *)
(* ================================================================ *)

Example ex6_forget_ok :
  forget (evalRSErr (Bind "r" (New (Num 5)) (Deref (Id "r"))))
  = eval (Bind "r" (New (Num 5)) (Deref (Id "r"))).
Proof. apply evalRSErr_refines. Qed.

Example ex7_refines_general : forall env e s,
  forget (evalRSE 9 e env s) = evalM 9 env s e.
Proof. intros env e s. apply evalRSE_refines. Qed.

Example ex8_transport : forall e p,
  evalRSErr e = inr p -> eval e = Some p.
Proof.
  intros e p H. rewrite <- evalRSErr_refines. rewrite H. reflexivity.
Qed.

(* ================================================================ *)
(* PART 3: MONAD LAWS AND EFFECT INTERACTION                      *)
(* ================================================================ *)

Example ex9_left_id : forall (A B : Type) (a : A) (f : A -> RSE (Env RVal) Store B),
  bindRSE (retRSE a) f = f a.
Proof. reflexivity. Qed.

Example ex10_throw_short_circuit :
  forall (B : Type) (msg : string) (f : RVal -> RSE (Env RVal) Store B),
    bindRSE (throwRSE msg) f = throwRSE msg.
Proof. reflexivity. Qed.

Example ex11_three_channels : forall (env : Env RVal) (s s' : Store),
  runRSE (x <- askRSE ;; _ <- putRSE s' ;; retRSE x) env s = inr (env, s').
Proof. reflexivity. Qed.
