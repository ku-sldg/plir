(**
 * Programming Languages in Rocq - AE Exercises
 * Arithmetic Expressions - Student Problem Set
 *
 * In these exercises you will:
 * 1. Complete proofs by replacing [Admitted] with [Qed]
 * 2. Understand the eval function through examples
 * 3. Learn proof tactics (induction, lia, destruct, ...)
 * 4. Discover properties of arithmetic
 *
 * HOW TO USE THIS FILE
 * --------------------
 * Each exercise ends in [Admitted].  Replace it with a real proof
 * ending in [Qed].  The file compiles as given (Rocq accepts
 * [Admitted]), so you can check progress incrementally.
 *
 * The [AE] syntax, the [eval] interpreter, and the helpers [count_ops],
 * [ae_equiv], and [ae_eq_dec] come from the lecture, which we import.
 * Helper functions needed by some exercises (size, depth, optimize,
 * fold_constants, simplify) are PROVIDED below - the exercise is to
 * prove the lemmas about them.
 *
 * Difficulty: [*] trivial, [**] easy induction, [***] case analysis,
 * [****] harder.  Complete solutions are in plih_ae_solutions.v.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import plih_rocq_ae_shared.
Require Import plih_ae_lecture.

(* ================================================================ *)
(* WARM-UP: DIRECT EVALUATION                                       *)
(* ================================================================ *)

(* Exercise 1 [*]: Basic evaluation *)
Example ex1_eval_num : eval (Num 42) = 42.
Proof. Admitted.

(* Exercise 2 [*]: Evaluate simple addition *)
Example ex2_eval_plus : eval (Plus (Num 3) (Num 5)) = 8.
Proof. Admitted.

(* Exercise 3 [*]: Evaluate nested expression *)
Example ex3_eval_nested :
  eval (Plus (Plus (Num 1) (Num 2)) (Num 3)) = 6.
Proof. Admitted.

(* Exercise 4 [*]: Evaluate with subtraction *)
Example ex4_eval_minus :
  eval (Minus (Num 10) (Num 3)) = 7.
Proof. Admitted.

(* Exercise 5 [*]: Evaluate complex expression *)
Example ex5_eval_complex :
  eval (Plus (Minus (Num 20) (Num 5)) (Num 10)) = 25.
Proof. Admitted.

(* ================================================================ *)
(* PART 1: SIMPLE LEMMAS                                            *)
(* ================================================================ *)

(* Exercise 6 [*]: Plus distributes into eval *)
Lemma ex6_eval_plus_distributes : forall e1 e2,
  eval (Plus e1 e2) = eval e1 + eval e2.
Proof. Admitted.

(* Exercise 7 [*]: Minus distributes into eval *)
Lemma ex7_eval_minus_distributes : forall e1 e2,
  eval (Minus e1 e2) = eval e1 - eval e2.
Proof. Admitted.

(* Exercise 8 [**]: Commutativity of Plus.  Hint: simpl then lia. *)
Lemma ex8_plus_commutative : forall e1 e2,
  eval (Plus e1 e2) = eval (Plus e2 e1).
Proof. Admitted.

(* ================================================================ *)
(* PART 2: SIMPLE INDUCTION PROOFS                                  *)
(* ================================================================ *)

(* Exercise 9 [**]: Zero is a left identity for plus *)
Lemma ex9_zero_left_identity : forall e,
  eval (Plus (Num 0) e) = eval e.
Proof. Admitted.

(* Exercise 10 [**]: Every expression evaluates to some number *)
Lemma ex10_eval_is_nat : forall e,
  exists n, eval e = n.
Proof. Admitted.

(* Exercise 11 [**]: eval is always non-negative (trivial for nat) *)
Lemma ex11_eval_nonneg : forall e,
  0 <= eval e.
Proof. Admitted.

(* Exercise 12 [***]: eval is never negative (another phrasing) *)
Lemma ex12_eval_is_positive : forall e,
  eval e >= 0.
Proof. Admitted.

(* ================================================================ *)
(* PART 3: PROPERTIES OF OPERATIONS                                 *)
(* ================================================================ *)

(* Exercise 13 [**]: Adding 0 on the right does nothing *)
Lemma ex13_plus_zero_right : forall e,
  eval (Plus e (Num 0)) = eval e.
Proof. Admitted.

(* Exercise 14 [**]: Subtracting an expression from itself gives zero *)
Lemma ex14_minus_self : forall e,
  eval (Minus e e) = 0.
Proof. Admitted.

(* Exercise 15 [***]: Plus is associative *)
Lemma ex15_plus_associative : forall e1 e2 e3,
  eval (Plus (Plus e1 e2) e3) = eval (Plus e1 (Plus e2 e3)).
Proof. Admitted.

(* Exercise 16 [***]: Iterated subtraction.
   Hint: in Rocq nat, a - b = 0 when a < b.  destruct the [<?] test. *)
Lemma ex16_minus_twice : forall e1 e2 e3,
  eval (Minus (Minus e1 e2) e3) =
  if (eval e1) <? (eval e2 + eval e3) then 0 else eval e1 - eval e2 - eval e3.
Proof. Admitted.

(* ================================================================ *)
(* PART 4: INEQUALITIES                                             *)
(* ================================================================ *)

(* Exercise 17 [**]: Plus does not decrease the value *)
Lemma ex17_plus_increases : forall e1 e2,
  eval (Plus e1 e2) >= eval e1.
Proof. Admitted.

(* Exercise 18 [**]: Minus does not increase the value *)
Lemma ex18_minus_decreases : forall e1 e2,
  eval (Minus e1 e2) <= eval e1.
Proof. Admitted.

(* Exercise 19 [***]: Adding two positive values gives something > 1 *)
Lemma ex19_plus_both_pos : forall e1 e2,
  eval e1 > 0 -> eval e2 > 0 -> eval (Plus e1 e2) > 1.
Proof. Admitted.

(* ================================================================ *)
(* PART 5: AUXILIARY FUNCTIONS                                      *)
(* ================================================================ *)

(* PROVIDED: number of nodes in the expression tree. *)
Fixpoint size (e : AE) : nat :=
  match e with
  | Num _ => 1
  | Plus a b => 1 + size a + size b
  | Minus a b => 1 + size a + size b
  end.

(* Exercise 20 [**]: Size is always positive *)
Lemma ex20_size_positive : forall e,
  size e > 0.
Proof. Admitted.

(* Exercise 21 [***]: Size of a Plus *)
Lemma ex21_size_of_plus : forall e1 e2,
  size (Plus e1 e2) = 1 + size e1 + size e2.
Proof. Admitted.

(* PROVIDED: depth (longest path to a leaf). *)
Fixpoint depth (e : AE) : nat :=
  match e with
  | Num _ => 0
  | Plus a b => 1 + Nat.max (depth a) (depth b)
  | Minus a b => 1 + Nat.max (depth a) (depth b)
  end.

(* Exercise 22 [**]: Depth of a number *)
Lemma ex22_depth_num : forall n,
  depth (Num n) = 0.
Proof. Admitted.

(* Exercise 23 [****]: Size is bounded by depth.  A classic result;
   you will likely need a strengthened induction hypothesis such as
   [S (size e) <= 2 ^ (depth e + 1)].  Useful lemmas:
   Nat.pow_le_mono_r and Nat.pow_add_r. *)
Lemma ex23_size_depth_relation : forall e,
  size e <= 2 ^ (depth e + 1).
Proof. Admitted.

(* ================================================================ *)
(* PART 6: OPTIMIZATION CORRECTNESS                                 *)
(* ================================================================ *)

(* PROVIDED: optimize children first, then drop a [+ 0] on the right. *)
Fixpoint optimize (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus a b =>
      match optimize b with
      | Num 0 => optimize a
      | b' => Plus (optimize a) b'
      end
  | Minus a b => Minus (optimize a) (optimize b)
  end.

(* Exercise 24 [***]: Optimization preserves meaning *)
Lemma ex24_optimize_correct : forall e,
  eval (optimize e) = eval e.
Proof. Admitted.

(* Exercise 25 [***]: Optimization does not increase size *)
Lemma ex25_optimize_reduces_size : forall e,
  size (optimize e) <= size e.
Proof. Admitted.

(* ================================================================ *)
(* PART 7: EQUIVALENCE RELATION                                     *)
(* ================================================================ *)

(* [ae_equiv e1 e2] is defined in the lecture as [eval e1 = eval e2]. *)

(* Exercise 26 [*]: Reflexivity of equivalence *)
Lemma ex26_equiv_refl : forall e,
  ae_equiv e e.
Proof. Admitted.

(* Exercise 27 [*]: Symmetry of equivalence *)
Lemma ex27_equiv_sym : forall e1 e2,
  ae_equiv e1 e2 -> ae_equiv e2 e1.
Proof. Admitted.

(* Exercise 28 [**]: Transitivity of equivalence *)
Lemma ex28_equiv_trans : forall e1 e2 e3,
  ae_equiv e1 e2 -> ae_equiv e2 e3 -> ae_equiv e1 e3.
Proof. Admitted.

(* Exercise 29 [**]: Different syntaxes can be equivalent *)
Lemma ex29_equiv_example :
  ae_equiv (Plus (Num 1) (Num 2)) (Plus (Num 2) (Num 1)).
Proof. Admitted.

(* ================================================================ *)
(* PART 8: CREATIVE PROBLEMS                                        *)
(* ================================================================ *)

(* PROVIDED: constant folding - evaluate constant subexpressions. *)
Fixpoint fold_constants (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus a b =>
      match fold_constants a, fold_constants b with
      | Num x, Num y => Num (x + y)
      | a', b' => Plus a' b'
      end
  | Minus a b =>
      match fold_constants a, fold_constants b with
      | Num x, Num y => Num (x - y)
      | a', b' => Minus a' b'
      end
  end.

(* Exercise 30 [***]: Constant folding preserves meaning *)
Lemma ex30_fold_constants_correct : forall e,
  eval (fold_constants e) = eval e.
Proof. Admitted.

(* Exercise 31 [****]: A "trivial" property - try to prove it without
   just calling reflexivity. *)
Lemma ex31_double : forall e,
  eval e + eval e = 2 * eval e.
Proof. Admitted.

(* ================================================================ *)
(* CHALLENGE PROBLEMS                                               *)
(* ================================================================ *)

(* Challenge 1: a nonzero operation count means the head is Plus or
   Minus. ([count_ops] is from the lecture.) *)
Lemma challenge1_count_ops_positive : forall e,
  count_ops e > 0 -> exists e1 e2, e = Plus e1 e2 \/ e = Minus e1 e2.
Proof. Admitted.

(* PROVIDED: simplify removes (Num 0) summands and (Minus e e).
   Children are simplified first, then zeros are folded. *)
Fixpoint simplify (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus a b =>
      match simplify a, simplify b with
      | Num 0, b' => b'
      | a', Num 0 => a'
      | a', b' => Plus a' b'
      end
  | Minus a b =>
      if ae_eq_dec a b then Num 0 else Minus (simplify a) (simplify b)
  end.

(* Challenge 2: simplify preserves meaning. *)
Lemma challenge2_simplify_correct : forall e,
  eval (simplify e) = eval e.
Proof. Admitted.

(* ================================================================ *)
(* SUBMISSION GUIDELINES                                            *)
(* ================================================================ *)

(**
 * Replace every [Admitted] with a complete proof ending in [Qed].
 * When you are done, the file should compile with no remaining
 * [Admitted].  Compare your proofs against plih_ae_solutions.v.
 *)
