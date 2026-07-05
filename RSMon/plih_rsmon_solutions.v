(**
Programming Languages in Rocq - Reader+State Monad Solutions
Complete solutions to plih_rsmon_exercises.v

The language [FBAES], the explicit interpreter [evalM]/[eval], the
combined monad ([retRS]/[bindRS]/[askRS]/[localRS]/[getRS]/[putRS]/
[failRS]/[runRS]), the monadic interpreter [evalRS]/[evalReaderState],
and the theorems [evalRS_agrees] / [evalReaderState_agrees] all come from
the Reader+State Monad lecture.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rsmon_shared.
Require Import plih_rsmon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE COMBINED INTERPRETER *)

Example ex1_arith :
  evalReaderState (Minus (Mult (Num 3) (Num 4)) (Num 2)) = Some (NumV 10, nil).
Proof. reflexivity. Qed.

Example ex2_static_scope :
  evalReaderState (Bind "x" (Num 5)
                     (Bind "f" (Lambda "y" (Id "x"))
                        (Bind "x" (Num 99)
                           (App (Id "f") (Num 0)))))
  = Some (NumV 5, nil).
Proof. reflexivity. Qed.

Example ex3_roundtrip :
  evalReaderState (Bind "r" (New (Num 0))
                     (Seq (Assign (Id "r") (Num 42))
                          (Deref (Id "r"))))
  = Some (NumV 42, [NumV 42]).
Proof. reflexivity. Qed.

Example ex4_scope_and_state :
  evalReaderState (Bind "r" (New (Num 100))
                     (Bind "f" (Lambda "n" (Assign (Id "r") (Id "n")))
                        (Seq (App (Id "f") (Num 7))
                             (Deref (Id "r")))))
  = Some (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

(** * PART 2: AGREEMENT IN ACTION *)

Example ex5_wrapper_agrees :
  evalReaderState (App (Lambda "x" (Id "x")) (Num 5))
  = eval (App (Lambda "x" (Id "x")) (Num 5)).
Proof. apply evalReaderState_agrees. Qed.

Example ex6_agrees_general : forall env e s,
  evalRS 9 e env s = evalM 9 env s e.
Proof. intros env e s. apply evalRS_agrees. Qed.

Example ex7_transport : forall e v s',
  evalReaderState e = Some (v, s') -> eval e = Some (v, s').
Proof. intros e v s' H. rewrite <- evalReaderState_agrees. exact H. Qed.

(** * PART 3: MONAD LAWS AND EFFECT INTERACTION *)

Example ex8_left_id : forall (A B : Type) (a : A) (f : A -> RS (Env RVal) Store B),
  bindRS (retRS a) f = f a.
Proof. reflexivity. Qed.

Example ex9_ask_pure : forall (env : Env RVal) (s : Store),
  runRS askRS env s = Some (env, s).
Proof. reflexivity. Qed.

Example ex10_put_get : forall (env : Env RVal) (s0 s' : Store),
  runRS (bindRS (putRS s') (fun _ => getRS)) env s0 = Some (s', s').
Proof. reflexivity. Qed.

(** * PART 4: CONCRETE SYNTAX *)

Open Scope rsmon_scope.

Example ex11_deref_prec :
  <{ ! "r" + 1 }> = Plus (Deref (Id "r")) (Num 1).
Proof. reflexivity. Qed.

Example ex12_roundtrip :
  evalReaderState <{ bind "r" = new 5 in "r" := !"r" + 1 ; !"r" }>
  = Some (NumV 6, [NumV 6]).
Proof. reflexivity. Qed.

Example ex13_scope_and_state :
  evalReaderState
    <{ bind "r" = new 1 in
         bind "f" = (lambda "n" in "r" := !"r" + "n") in
           "f" 10 ; !"r" }>
  = Some (NumV 11, [NumV 11]).
Proof. reflexivity. Qed.
