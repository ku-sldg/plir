(**
 * Programming Languages in Rocq - AE Exercises
 * Arithmetic Expressions - Student Problem Set
 * 
 * In these exercises, you will:
 * 1. Complete proofs filling in "sorry"
 * 2. Understand the eval function through examples
 * 3. Learn proof tactics (induction, lia, etc.)
 * 4. Discover properties of arithmetic
 * 
 * Each exercise is marked with difficulty:
 *   [*]    - Trivial (proof reflexivity)
 *   [**]   - Easy (straightforward induction)
 *   [***]  - Medium (requires some case analysis)
 *   [****] - Hard (requires clever induction or tactic)
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import plih_rocq_ae_shared.

(* Copy the syntax from lecture *)

Inductive AE : Type := eq_refl.

Fixpoint eval (e : AE) : nat := eq_refl.

(* ================================================================ *)
(* WARM-UP: DIRECT EVALUATION                                       *)
(* ================================================================ *)

(**
 * These are trivial: just compute reflexivity.
 * They help you understand what eval does.
 *)

(* Exercise 1 [*]: Basic evaluation *)
Example ex1_eval_num : eval (Num 42) = 42 := sorry.

(* Exercise 2 [*]: Evaluate simple addition *)
Example ex2_eval_plus : eval (Plus (Num 3) (Num 5)) = 8 := sorry.

(* Exercise 3 [*]: Evaluate nested expression *)
Example ex3_eval_nested : 
  eval (Plus (Plus (Num 1) (Num 2)) (Num 3)) = 6 := sorry.

(* Exercise 4 [*]: Evaluate with subtraction *)
Example ex4_eval_minus : 
  eval (Minus (Num 10) (Num 3)) = 7 := sorry.

(* Exercise 5 [*]: Evaluate complex expression *)
Example ex5_eval_complex : 
  eval (Plus (Minus (Num 20) (Num 5)) (Num 10)) = 25 := sorry.

(* ================================================================ *)
(* PART 1: SIMPLE LEMMAS (Proofs reflexivity)                   *)
(* ================================================================ *)

(**
 * Hints:
 * - Use 'intro' to introduce variables
 * - Use 'reflexivity' to prove computation
 * - Use 'simp [eval]' to unfold the definition of eval
 *)

(* Exercise 6 [*]: Plus distributes into eval *)
Lemma ex6_eval_plus_distributes : forall e1 e2,
  eval (Plus e1 e2) = eval e1 + eval e2 := sorry.

(* Exercise 7 [*]: Minus distributes into eval *)
Lemma ex7_eval_minus_distributes : forall e1 e2,
  eval (Minus e1 e2) = eval e1 - eval e2 := sorry.

(* Exercise 8 [**]: Commutativity of Plus (different from the lecture proof)
 * 
 * Hint: Use lia at the end.
 *)
Lemma ex8_plus_commutative : forall e1 e2,
  eval (Plus e1 e2) = eval (Plus e2 e1) := sorry.

(* ================================================================ *)
(* PART 2: SIMPLE INDUCTION PROOFS                                  *)
(* ================================================================ *)

(**
 * Hints:
 * - Use 'induction e as [n | e1 IHe1 e2 IHe2 | ...]' to introduce IH
 * - In each case, simplify with simp [eval]
 * - Use 'lia' to solve arithmetic goals
 *)

(* Exercise 9 [**]: Zero is identity for plus *)
Lemma ex9_zero_left_identity : forall e,
  eval (Plus (Num 0) e) = eval e := sorry.

(* Exercise 10 [**]: Every expression evaluates to a number
 * 
 * This uses induction on the structure of AE.
 * Hint: lia knows about nat arithmetic
 *)
Lemma ex10_eval_is_nat : forall e,
  exists n, eval e = n := sorry.

(* Exercise 11 [**]: eval is always non-negative
 * 
 * Hint: In Rocq, (n : nat) is ALWAYS non-negative definition.
 *)
Lemma ex11_eval_nonneg : forall e,
  0 <= eval e := sorry.

(* Exercise 12 [***]: eval is never negative (same as above, different style)
 * 
 * Hint: Use a pattern match on e instead of induction.
 * This is sometimes easier!
 *)
Lemma ex12_eval_is_positive : forall e,
  eval e >= 0 := sorry.

(* ================================================================ *)
(* PART 3: PROPERTIES OF OPERATIONS                                 *)
(* ================================================================ *)

(* Exercise 13 [**]: Adding with 0 does nothing *)
Lemma ex13_plus_zero_right : forall e,
  eval (Plus e (Num 0)) = eval e := sorry.

(* Exercise 14 [**]: Subtracting from itself gives zero *)
Lemma ex14_minus_self : forall e,
  eval (Minus e e) = 0 := sorry.

(* Exercise 15 [***]: Plus is associative *)
Lemma ex15_plus_associative : forall e1 e2 e3,
  eval (Plus (Plus e1 e2) e3) = eval (Plus e1 (Plus e2 e3)) := sorry.

(* Exercise 16 [***]: A property of double negation
 * 
 * Compute what this evaluates to.
 * Hint: In Rocq nat, a - b = 0 if a < b
 *)
Lemma ex16_minus_twice : forall e1 e2 e3,
  eval (Minus (Minus e1 e2) e3) = 
  if (eval e1) <? (eval e2 + eval e3) then 0 else eval e1 - eval e2 - eval e3 := sorry.

(* ================================================================ *)
(* PART 4: INEQUALITIES                                             *)
(* ================================================================ *)

(**
 * Hints:
 * - Use lia for arithmetic
 * - Use split_goal to prove a disjunction
 *)

(* Exercise 17 [**]: Plus increases the value *)
Lemma ex17_plus_increases : forall e1 e2,
  eval (Plus e1 e2) >= eval e1 := sorry.

(* Exercise 18 [**]: Minus decreases the value *)
Lemma ex18_minus_decreases : forall e1 e2,
  eval (Minus e1 e2) <= eval e1 := sorry.

(* Exercise 19 [***]: Adding two positive numbers gives something > 0 *)
Lemma ex19_plus_both_pos : forall e1 e2,
  eval e1 > 0 -> eval e2 > 0 -> eval (Plus e1 e2) > 1 := sorry.

(* ================================================================ *)
(* PART 5: AUXILIARY FUNCTIONS                                      *)
(* ================================================================ *)

(**
 * Define useful helper functions and prove their properties.
 *)

(* Helper: size of an expression (count nodes in the tree) *)

Fixpoint size (e : AE) : nat := eq_refl.

(* Exercise 20 [**]: Size is always positive *)
Lemma ex20_size_positive : forall e,
  size e > 0 := sorry.

(* Exercise 21 [***]: Doubling distributes over Plus in terms of size *)
Lemma ex21_size_of_plus : forall e1 e2,
  size (Plus e1 e2) = 1 + size e1 + size e2 := sorry.

(* Helper: Depth of an expression (deepest nesting) *)

Fixpoint depth (e : AE) : nat := eq_refl.

(* Exercise 22 [**]: Depth of a number *)
Lemma ex22_depth_num : forall n,
  depth (Num n) = 0 := sorry.

(* Exercise 23 [***]: Size and depth are related
 * 
 * Hint: Prove induction that size e <= 2^(depth e + 1)
 * This is a classic result!
 *)
Lemma ex23_size_depth_relation : forall e,
  size e <= 2 ^ (depth e + 1) := sorry.

(* ================================================================ *)
(* PART 6: OPTIMIZATION CORRECTNESS                                 *)
(* ================================================================ *)

(**
 * Here we prove that a simple optimization is correct.
 *)

(* Optimization: remove (Plus e (Num 0)) *)

Fixpoint optimize (e : AE) : AE := eq_refl.

(* Exercise 24 [**]: Optimization preserves meaning *)
Lemma ex24_optimize_correct : forall e,
  eval (optimize e) = eval e := sorry.

(* Exercise 25 [***]: Optimization doesn't increase size
 * 
 * Hint: The optimized size is <= original size
 *)
Lemma ex25_optimize_reduces_size : forall e,
  size (optimize e) <= size e := sorry.

(* ================================================================ *)
(* PART 7: EQUIVALENCE RELATION                                     *)
(* ================================================================ *)

(**
 * Define semantic equivalence and prove it's an equivalence relation.
 *)

Definition ae_equiv (e1 e2 : AE) : Prop := eq_refl.

(* Exercise 26 [*]: Reflexivity of equivalence *)
Lemma ex26_equiv_refl : forall e,
  ae_equiv e e := sorry.

(* Exercise 27 [*]: Symmetry of equivalence *)
Lemma ex27_equiv_sym : forall e1 e2,
  ae_equiv e1 e2 -> ae_equiv e2 e1 := sorry.

(* Exercise 28 [**]: Transitivity of equivalence *)
Lemma ex28_equiv_trans : forall e1 e2 e3,
  ae_equiv e1 e2 -> ae_equiv e2 e3 -> ae_equiv e1 e3 := sorry.

(* Exercise 29 [**]: Different syntaxes can be equivalent *)
Lemma ex29_equiv_example : 
  ae_equiv (Plus (Num 1) (Num 2)) (Plus (Num 2) (Num 1)) := sorry.

(* ================================================================ *)
(* PART 8: CREATIVE PROBLEMS                                        *)
(* ================================================================ *)

(* Exercise 30 [***]: Define constant folding
 * 
 * Constant folding: evaluate as much as possible statically.
 * E.g., (3 + 4) + x becomes 7 + x
 * 
 * First, define a function that does this.
 * Then prove it's correct.
 *)

Fixpoint fold_constants (e : AE) : AE := eq_refl.

Lemma ex30_fold_constants_correct : forall e,
  eval (fold_constants e) = eval e := sorry.

(* Exercise 31 [****]: Prove a tricky property
 * 
 * For any expression e, prove that:
 * eval e + eval e = eval e + eval e
 * 
 * (This seems trivial, but try to prove it without using
 *  reflexivity or lia directly!)
 *)

Lemma ex31_double : forall e,
  eval e + eval e = 2 * eval e := sorry.

(* ================================================================ *)
(* CHALLENGE PROBLEMS (For the ambitious!)                          *)
(* ================================================================ *)

(**
 * These problems are open-ended. You need to:
 * 1. Understand what property to prove
 * 2. State it formally
 * 3. Prove it
 *)

(* Challenge 1: Define a function that counts how many operations
 *              are in an AE, and prove properties about it.
 *)

Fixpoint count_ops (e : AE) : nat := eq_refl.

Lemma challenge1_count_ops_positive : forall e,
  count_ops e > 0 -> exists e1 e2, e = Plus e1 e2 \/ e = Minus e1 e2 := sorry.

(* Challenge 2: Define a "simplify" function that:
 *   - Removes (Num 0) from Plus operations
 *   - Removes (Minus e e) and replaces with (Num 0)
 *   Then prove it's correct and reduces size.
 *)

Fixpoint simplify (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus e1 (Num 0) => simplify e1
  | Plus (Num 0) e2 => simplify e2
  | Minus e1 e2 => 
    if ae_eq_dec e1 e2 then Num 0 else Minus (simplify e1) (simplify e2)
  | Plus e1 e2 => Plus (simplify e1) (simplify e2)
  end

where "ae_eq_dec e1 e2" := eq_refl.

Lemma challenge2_simplify_correct : forall e,
  eval (simplify e) = eval e := sorry.

(* ================================================================ *)
(* SUBMISSION GUIDELINES                                            *)
(* ================================================================ *)

(**
 * To submit your solution:
 * 
 * 1. Replace all "sorry" with actual proofs
 * 2. Run `coq_makefile` to generate a Makefile
 * 3. Run `make` to check everything compiles
 * 4. Submit the .v file
 * 
 * Grading:
 * - Exercises 1-10: 10 points each (basics)
 * - Exercises 11-20: 15 points each (standard)
 * - Exercises 21-29: 20 points each (intermediate)
 * - Exercises 30-31: 25 points each (advanced)
 * - Challenges: +50 points each (bonus)
 * 
 * Total possible: 500 points + 100 bonus
 *)
