(**
Programming Languages in Rocq - State Monad Solutions
Complete solutions to plih_smon_exercises.v

The language [FBAES], the explicit interpreter [evalM]/[eval], the State
monad ([retS]/[bindS]/[getS]/[putS]/[failS]/[runState]), the monadic
interpreter [evalS]/[evalStore], and the theorems [evalS_agrees] /
[evalStore_agrees] all come from the State Monad lecture.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_smon_shared.
Require Import plih_smon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE MONADIC INTERPRETER *)

Example ex1_arith :
  evalStore (Minus (Mult (Num 3) (Num 4)) (Num 2)) = Some (NumV 10, nil).
Proof. reflexivity. Qed.

Example ex2_roundtrip :
  evalStore (Bind "r" (New (Num 0))
               (Seq (Assign (Id "r") (Num 42))
                    (Deref (Id "r"))))
  = Some (NumV 42, [NumV 42]).
Proof. reflexivity. Qed.

Example ex3_two_cells :
  evalStore (Bind "p" (New (Num 1))
               (Bind "q" (New (Num 2))
                  (Seq (Assign (Id "p") (Num 9))
                       (Deref (Id "q")))))
  = Some (NumV 2, [NumV 9; NumV 2]).
Proof. reflexivity. Qed.

(** * PART 2: AGREEMENT IN ACTION *)

Example ex4_wrapper_agrees :
  evalStore (New (Num 5)) = eval (New (Num 5)).
Proof. apply evalStore_agrees. Qed.

Example ex5_agrees_general : forall env e s,
  evalS 7 env e s = evalM 7 env s e.
Proof. intros env e s. apply evalS_agrees. Qed.

Example ex6_transport : forall e v s',
  evalStore e = Some (v, s') -> eval e = Some (v, s').
Proof. intros e v s' H. rewrite <- evalStore_agrees. exact H. Qed.

(** * PART 3: MONAD LAWS *)

Example ex7_left_id : forall (A B : Type) (a : A) (f : A -> State Store B),
  bindS (retS a) f = f a.
Proof. reflexivity. Qed.

Example ex8_fail_bind : forall (f : RVal -> State Store RVal),
  bindS failS f = failS.
Proof. reflexivity. Qed.

Example ex9_put_put : forall (s1 s2 : Store),
  bindS (putS s1) (fun _ => putS s2) = putS s2.
Proof. reflexivity. Qed.

Example ex10_put_get : forall (s0 s' : Store),
  runState (bindS (putS s') (fun _ => getS)) s0 = Some (s', s').
Proof. reflexivity. Qed.

(** * PART 4: CONCRETE SYNTAX *)

Open Scope smon_scope.

Example ex11_deref_prec :
  <{ ! "r" + 1 }> = Plus (Deref (Id "r")) (Num 1).
Proof. reflexivity. Qed.

Example ex12_roundtrip :
  evalStore <{ bind "r" = new 5 in "r" := !"r" + 1 ; !"r" }>
  = Some (NumV 6, [NumV 6]).
Proof. reflexivity. Qed.

Example ex13_counter :
  evalStore <{ bind "c" = new 0 in
                 "c" := !"c" + 1 ; "c" := !"c" + 1 ; !"c" }>
  = Some (NumV 2, [NumV 2]).
Proof. reflexivity. Qed.
