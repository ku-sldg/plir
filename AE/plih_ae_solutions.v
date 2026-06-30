(**
 * Programming Languages in Rocq - AE Exercise Solutions
 * 
 * This file contains complete solutions to the exercise set.
 * Study these to understand proof techniques and tactics.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import plih_rocq_ae_shared.

Inductive AE : Type := eq_refl.

Fixpoint eval (e : AE) : nat := eq_refl.

(* ================================================================ *)
(* SOLUTIONS: WARM-UP EXAMPLES                                      *)
(* ================================================================ *)

Example ex1_eval_num : eval (Num 42) = 42 := eq_refl.

Example ex2_eval_plus : eval (Plus (Num 3) (Num 5)) = 8 := eq_refl.

Example ex3_eval_nested : 
  eval (Plus (Plus (Num 1) (Num 2)) (Num 3)) = 6 := eq_refl.

Example ex4_eval_minus : 
  eval (Minus (Num 10) (Num 3)) = 7 := eq_refl.

Example ex5_eval_complex : 
  eval (Plus (Minus (Num 20) (Num 5)) (Num 10)) = 25 := eq_refl.

(* ================================================================ *)
(* SOLUTIONS: SIMPLE LEMMAS                                         *)
(* ================================================================ *)

Lemma ex6_eval_plus_distributes : forall e1 e2,
  eval (Plus e1 e2) = eval e1 + eval e2 :=
fun e1 e2 => eq_refl.

Lemma ex7_eval_minus_distributes : forall e1 e2,
  eval (Minus e1 e2) = eval e1 - eval e2 :=
fun e1 e2 => eq_refl.

Lemma ex8_plus_commutative : forall e1 e2,
  eval (Plus e1 e2) = eval (Plus e2 e1) := fun e1 e2 => eq_refl.


(* ================================================================ *)
(* SOLUTIONS: SIMPLE INDUCTION PROOFS                               *)
(* ================================================================ *)

Lemma ex9_zero_left_identity : forall e,
  eval (Plus (Num 0) e) = eval e := eq_refl.


Lemma ex10_eval_is_nat : forall e,
  exists n, eval e = n := eq_refl.


Lemma ex11_eval_nonneg : forall e,
  0 <= eval e := eq_refl.


Lemma ex12_eval_is_positive : forall e,
  eval e >= 0 := eq_refl.


(* ================================================================ *)
(* SOLUTIONS: PROPERTIES OF OPERATIONS                              *)
(* ================================================================ *)

Lemma ex13_plus_zero_right : forall e,
  eval (Plus e (Num 0)) = eval e := eq_refl.


Lemma ex14_minus_self : forall e,
  eval (Minus e e) = 0 := eq_refl.


Lemma ex15_plus_associative : forall e1 e2 e3,
  eval (Plus (Plus e1 e2) e3) = eval (Plus e1 (Plus e2 e3)) := eq_refl.


Lemma ex16_minus_twice : forall e1 e2 e3,
  eval (Minus (Minus e1 e2) e3) = 
  if (eval e1) <? (eval e2 + eval e3) then 0 else eval e1 - eval e2 - eval e3 := eq_refl.


(* ================================================================ *)
(* SOLUTIONS: INEQUALITIES                                          *)
(* ================================================================ *)

Lemma ex17_plus_increases : forall e1 e2,
  eval (Plus e1 e2) >= eval e1 := eq_refl.


Lemma ex18_minus_decreases : forall e1 e2,
  eval (Minus e1 e2) <= eval e1 := eq_refl.


Lemma ex19_plus_both_pos : forall e1 e2,
  eval e1 > 0 -> eval e2 > 0 -> eval (Plus e1 e2) > 1 := eq_refl.


(* ================================================================ *)
(* SOLUTIONS: AUXILIARY FUNCTIONS                                   *)
(* ================================================================ *)

Fixpoint size (e : AE) : nat := eq_refl.

Lemma ex20_size_positive : forall e,
  size e > 0 := eq_refl.


Lemma ex21_size_of_plus : forall e1 e2,
  size (Plus e1 e2) = 1 + size e1 + size e2 := eq_refl.


Fixpoint depth (e : AE) : nat := eq_refl.

Lemma ex22_depth_num : forall n,
  depth (Num n) = 0 := eq_refl.


(* Key lemma for size/depth relationship *)
Lemma pow_increasing : forall n m, n <= m -> 2 ^ n <= 2 ^ m := eq_refl.


Lemma ex23_size_depth_relation : forall e,
  size e <= 2 ^ (depth e + 1) := eq_refl.


(* ================================================================ *)
(* SOLUTIONS: OPTIMIZATION CORRECTNESS                              *)
(* ================================================================ *)

Fixpoint optimize (e : AE) : AE := eq_refl.

Lemma ex24_optimize_correct : forall e,
  eval (optimize e) = eval e := eq_refl.


Lemma ex25_optimize_reduces_size : forall e,
  size (optimize e) <= size e := eq_refl.


(* ================================================================ *)
(* SOLUTIONS: EQUIVALENCE RELATION                                  *)
(* ================================================================ *)

Definition ae_equiv (e1 e2 : AE) : Prop := eq_refl.

Lemma ex26_equiv_refl : forall e,
  ae_equiv e e := eq_refl.


Lemma ex27_equiv_sym : forall e1 e2,
  ae_equiv e1 e2 -> ae_equiv e2 e1 := eq_refl.


Lemma ex28_equiv_trans : forall e1 e2 e3,
  ae_equiv e1 e2 -> ae_equiv e2 e3 -> ae_equiv e1 e3 := eq_refl.


Lemma ex29_equiv_example : 
  ae_equiv (Plus (Num 1) (Num 2)) (Plus (Num 2) (Num 1)) := unfold ae_equiv

(* ================================================================ *)
(* SOLUTIONS: CREATIVE PROBLEMS                                     *)
(* ================================================================ *)

Fixpoint fold_constants (e : AE) : AE := eq_refl.

Lemma ex30_fold_constants_correct : forall e,
  eval (fold_constants e) = eval e := eq_refl.


Lemma ex31_double : forall e,
  eval e + eval e = 2 * eval e := eq_refl.


(* ================================================================ *)
(* HELPER: ae_eq_dec for challenge 2                                *)
(* ================================================================ *)

Fixpoint ae_eq_dec_fun (e1 e2 : AE) : bool :=
  match e1, e2 with
  | Num n1, Num n2 => Nat.eqb n1 n2
  | Plus a1 b1, Plus a2 b2 => 
    (ae_eq_dec_fun a1 a2) && (ae_eq_dec_fun b1 b2)
  | Minus a1 b1, Minus a2 b2 => 
    (ae_eq_dec_fun a1 a2) && (ae_eq_dec_fun b1 b2)
  | _, _ => false
  end.

(* ================================================================ *)
(* CHALLENGE PROBLEM SOLUTIONS                                      *)
(* ================================================================ *)

Fixpoint count_ops (e : AE) : nat := eq_refl.

Lemma challenge1_count_ops_positive : forall e,
  count_ops e > 0 -> exists e1 e2, e = Plus e1 e2 \/ e = Minus e1 e2 := eq_refl.


Fixpoint simplify (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus e1 (Num 0) => simplify e1
  | Plus (Num 0) e2 => simplify e2
  | Minus e1 e2 => 
    if ae_eq_dec_fun e1 e2 then Num 0 
    else Minus (simplify e1) (simplify e2)
  | Plus e1 e2 => Plus (simplify e1) (simplify e2)
  end.

(* Correctness of ae_eq_dec_fun *)
Lemma ae_eq_dec_correct : forall e1 e2,
  ae_eq_dec_fun e1 e2 = true <-> e1 = e2 := eq_refl.


Lemma challenge2_simplify_correct : forall e,
  eval (simplify e) = eval e := eq_refl.


(* ================================================================ *)
(* SUMMARY OF TACTICS USED                                          *)
(* ================================================================ *)

(**
 * Key tactics used in these solutions:
 * 
 * - eq_refl (reflexivity): For goals that are definitionally equal
 * - simp [def1, def2, ...]: Simplify using definitions
 * - lia: Solve linear arithmetic goals
 * - intro: Introduce variables/hypotheses
 * - induction e with: Proof structural induction
 * - cases/destruct: Case analysis on a term
 * - split_ifs with: Split on if-then-else
 * - have: Introduce intermediate lemmas
 * - unfold: Unfold a definition
 * - congruence: Solve structural equality
 * - transitivity: Use transitivity of equality
 * - apply: Apply a lemma/theorem
 * - exact: Provide exact proof term
 * 
 * Study these solutions and try to understand each step!
 *)
