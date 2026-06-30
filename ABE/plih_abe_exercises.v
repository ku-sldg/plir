(**
 * Programming Languages in Rocq - ABE Exercises
 * Arithmetic + Boolean Expressions - Student Problem Set
 *
 * Building on AE, these exercises cover:
 * 1. Boolean evaluation
 * 2. Error handling with option
 * 3. Type consistency
 * 4. Conditionals
 * 5. Boolean algebra
 *
 * HOW TO USE THIS FILE
 * --------------------
 * Each exercise is stated as a Lemma/Example ending in [Admitted].
 * Replace [Admitted] with a real proof terminated by [Qed].
 * The file compiles as given (Rocq accepts [Admitted] with a warning),
 * so you can check your progress incrementally.
 *
 * The [ABE] syntax and the [eval] interpreter come from the lecture,
 * which we import.  Function definitions you need (count_ifs,
 * optimize_not, extract_booleans) are PROVIDED so the statements type
 * check - the exercise is to prove the lemmas about them.
 *
 * Complete solutions are in plih_abe_solutions.v.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_abe_lecture.

Import ListNotations.

(* ================================================================ *)
(* PART 1: BASIC BOOLEAN EVALUATION                                *)
(* ================================================================ *)

Example ex1_bool_true : eval BTrue = Some (BoolV true).
Proof. Admitted.

Example ex2_bool_false : eval BFalse = Some (BoolV false).
Proof. Admitted.

Example ex3_and_true_true :
  eval (And BTrue BTrue) = Some (BoolV true).
Proof. Admitted.

Example ex4_and_true_false :
  eval (And BTrue BFalse) = Some (BoolV false).
Proof. Admitted.

Example ex5_or_false_false :
  eval (Or BFalse BFalse) = Some (BoolV false).
Proof. Admitted.

(* ================================================================ *)
(* PART 2: TYPE MISMATCHES (Error Handling)                        *)
(* ================================================================ *)

Example ex6_type_error_add :
  eval (Plus BTrue (Num 3)) = None.
Proof. Admitted.

Example ex7_type_error_and :
  eval (And (Num 5) BTrue) = None.
Proof. Admitted.

Example ex8_type_error_not_num :
  eval (Not (Num 42)) = None.
Proof. Admitted.

(* Hint: case-split on [eval e1] and [eval e2]. *)
Lemma ex9_type_mismatch_both_operands : forall e1 e2,
  eval (Plus e1 e2) = None \/
  exists n1 n2, eval (Plus e1 e2) = Some (NumV (n1 + n2)).
Proof. Admitted.

(* ================================================================ *)
(* PART 3: CONDITIONALS                                            *)
(* ================================================================ *)

Example ex10_if_true_takes_then :
  eval (IfThenElse BTrue (Num 42) (Num 99)) = Some (NumV 42).
Proof. Admitted.

Example ex11_if_false_takes_else :
  eval (IfThenElse BFalse (Num 42) (Num 99)) = Some (NumV 99).
Proof. Admitted.

Example ex12_if_with_comparison :
  eval (IfThenElse (LessThan (Num 3) (Num 5))
                   (Plus (Num 1) (Num 2))
                   (Num 0))
  = Some (NumV 3).
Proof. Admitted.

(* Nested conditionals *)
Example ex13_nested_if :
  eval (IfThenElse BTrue
                   (IfThenElse BFalse (Num 1) (Num 2))
                   (Num 3))
  = Some (NumV 2).
Proof. Admitted.

(* ================================================================ *)
(* PART 4: COMPARISON OPERATIONS                                   *)
(* ================================================================ *)

Example ex14_less_than_true :
  eval (LessThan (Num 3) (Num 5)) = Some (BoolV true).
Proof. Admitted.

Example ex15_less_than_false :
  eval (LessThan (Num 5) (Num 3)) = Some (BoolV false).
Proof. Admitted.

Example ex16_equal_true :
  eval (Equal (Num 5) (Num 5)) = Some (BoolV true).
Proof. Admitted.

Example ex17_equal_false :
  eval (Equal (Num 3) (Num 5)) = Some (BoolV false).
Proof. Admitted.

(* ================================================================ *)
(* PART 5: BOOLEAN ALGEBRA                                         *)
(* ================================================================ *)

Lemma ex18_not_true :
  eval (Not BTrue) = Some (BoolV false).
Proof. Admitted.

Lemma ex19_not_false :
  eval (Not BFalse) = Some (BoolV true).
Proof. Admitted.

Lemma ex20_double_negation : forall (b : bool),
  eval (Not (Not (if b then BTrue else BFalse)))
  = Some (BoolV b).
Proof. Admitted.

Lemma ex21_and_commutative : forall e1 e2,
  eval (And e1 e2) = eval (And e2 e1).
Proof. Admitted.

Lemma ex22_or_commutative : forall e1 e2,
  eval (Or e1 e2) = eval (Or e2 e1).
Proof. Admitted.

(* ================================================================ *)
(* PART 6: CONDITIONAL PROPERTIES                                  *)
(* ================================================================ *)

(* NOTE: the condition must evaluate to a boolean - otherwise the whole
   conditional is a type error.  That is why this lemma takes a
   hypothesis about [eval cond]. *)
Lemma ex23_if_both_branches_equal : forall cond b,
  eval cond = Some (BoolV b) ->
  eval (IfThenElse cond (Num 5) (Num 5)) = Some (NumV 5).
Proof. Admitted.

Lemma ex24_if_then_takes_then : forall e1 e2,
  eval (IfThenElse BTrue e1 e2) = eval e1.
Proof. Admitted.

Lemma ex25_if_false_takes_else : forall e1 e2,
  eval (IfThenElse BFalse e1 e2) = eval e2.
Proof. Admitted.

(* ================================================================ *)
(* PART 7: COMBINING FEATURES                                      *)
(* ================================================================ *)

Example ex26_complex_expr :
  eval (Plus (IfThenElse BTrue (Num 3) (Num 5)) (Num 2))
  = Some (NumV 5).
Proof. Admitted.

Example ex27_boolean_conditional :
  eval (And BTrue (IfThenElse (LessThan (Num 1) (Num 2))
                              BTrue
                              BFalse))
  = Some (BoolV true).
Proof. Admitted.

(* ================================================================ *)
(* PART 8: TYPE CONSISTENCY PROOFS                                 *)
(* ================================================================ *)

(* The predicates [is_numeric] and [is_boolean] are defined in the
   lecture (plih_abe_lecture.v). *)

Lemma ex28_numeric_eval_to_num : forall e,
  is_numeric e -> exists n, eval e = Some (NumV n).
Proof. Admitted.

Lemma ex29_boolean_eval_to_bool : forall e,
  is_boolean e -> exists b, eval e = Some (BoolV b).
Proof. Admitted.

Lemma ex30_numeric_no_error : forall e,
  is_numeric e -> eval e <> None.
Proof. Admitted.

(* ================================================================ *)
(* PART 9: EQUIVALENCE PROOFS                                      *)
(* ================================================================ *)

(* [abe_equiv] is defined in the lecture. *)

Lemma ex31_equiv_refl : forall e,
  abe_equiv e e.
Proof. Admitted.

Lemma ex32_equiv_sym : forall e1 e2,
  abe_equiv e1 e2 -> abe_equiv e2 e1.
Proof. Admitted.

Lemma ex33_equiv_trans : forall e1 e2 e3,
  abe_equiv e1 e2 -> abe_equiv e2 e3 -> abe_equiv e1 e3.
Proof. Admitted.

(* De Morgan's Law *)
Lemma ex34_demorgan_and : forall e1 e2,
  abe_equiv (Not (And e1 e2)) (Or (Not e1) (Not e2)).
Proof. Admitted.

Lemma ex35_demorgan_or : forall e1 e2,
  abe_equiv (Not (Or e1 e2)) (And (Not e1) (Not e2)).
Proof. Admitted.

(* ================================================================ *)
(* PART 10: COMPLEXITY AND SIZE                                    *)
(* ================================================================ *)

(* [size] is defined in the lecture. *)

Lemma ex36_size_positive : forall e,
  size e > 0.
Proof. Admitted.

(* PROVIDED: counts the number of conditionals in an expression. *)
Fixpoint count_ifs (e : ABE) : nat :=
  match e with
  | Num _ => 0
  | BTrue => 0
  | BFalse => 0
  | Not a => count_ifs a
  | Plus a b => count_ifs a + count_ifs b
  | Minus a b => count_ifs a + count_ifs b
  | And a b => count_ifs a + count_ifs b
  | Or a b => count_ifs a + count_ifs b
  | LessThan a b => count_ifs a + count_ifs b
  | Equal a b => count_ifs a + count_ifs b
  | IfThenElse a b c => 1 + count_ifs a + count_ifs b + count_ifs c
  end.

Lemma ex37_ifs_bounded_by_size : forall e,
  count_ifs e <= size e.
Proof. Admitted.

(* ================================================================ *)
(* PART 11: OPTIMIZATION                                           *)
(* ================================================================ *)

(**
 * Naive "double-negation elimination" ([Not (Not e)] -> [e]) is UNSOUND
 * in a type-checked language: [Not (Not (Num 5))] is a type error but
 * [Num 5] is not.  Instead we implement (and prove correct) constant
 * folding of [Not] applied to a boolean literal.
 *)

(* PROVIDED *)
Definition fold_not (e : ABE) : ABE :=
  match e with
  | Not BTrue  => BFalse
  | Not BFalse => BTrue
  | _ => e
  end.

(* PROVIDED *)
Fixpoint optimize_not (e : ABE) : ABE :=
  match e with
  | Num n => Num n
  | BTrue => BTrue
  | BFalse => BFalse
  | Not a => fold_not (Not (optimize_not a))
  | Plus a b => Plus (optimize_not a) (optimize_not b)
  | Minus a b => Minus (optimize_not a) (optimize_not b)
  | And a b => And (optimize_not a) (optimize_not b)
  | Or a b => Or (optimize_not a) (optimize_not b)
  | LessThan a b => LessThan (optimize_not a) (optimize_not b)
  | Equal a b => Equal (optimize_not a) (optimize_not b)
  | IfThenElse a b c =>
      IfThenElse (optimize_not a) (optimize_not b) (optimize_not c)
  end.

Lemma ex38_optimize_not_correct : forall e,
  eval (optimize_not e) = eval e.
Proof. Admitted.

Lemma ex39_optimize_not_reduces_size : forall e,
  size (optimize_not e) <= size e.
Proof. Admitted.

(* ================================================================ *)
(* PART 12: CREATIVE PROBLEMS                                      *)
(* ================================================================ *)

(* PROVIDED: collect every boolean literal occurring in an expression. *)
Fixpoint extract_booleans (e : ABE) : list ABE :=
  match e with
  | Num _ => []
  | BTrue => [BTrue]
  | BFalse => [BFalse]
  | Not a => extract_booleans a
  | Plus a b => extract_booleans a ++ extract_booleans b
  | Minus a b => extract_booleans a ++ extract_booleans b
  | And a b => extract_booleans a ++ extract_booleans b
  | Or a b => extract_booleans a ++ extract_booleans b
  | LessThan a b => extract_booleans a ++ extract_booleans b
  | Equal a b => extract_booleans a ++ extract_booleans b
  | IfThenElse a b c =>
      extract_booleans a ++ extract_booleans b ++ extract_booleans c
  end.

Lemma ex40_booleans_extracted_all_eval : forall e,
  forall b, In b (extract_booleans e) ->
  (b = BTrue \/ b = BFalse).
Proof. Admitted.

(* ================================================================ *)
(* CHALLENGE PROBLEMS                                               *)
(* ================================================================ *)

(* Challenge 1: if/then/else with identical branches is neutral -
   provided the condition is a boolean. *)
Lemma challenge1_if_neutral : forall cond e b,
  eval cond = Some (BoolV b) ->
  abe_equiv (IfThenElse cond e e) e.
Proof. Admitted.

(* Challenge 2: our [eval] evaluates BOTH operands of [And] (no
   short-circuit), so we also assume [e2] is a boolean. *)
Lemma challenge2_and_short_circuit : forall e1 e2 b2,
  eval e1 = Some (BoolV false) ->
  eval e2 = Some (BoolV b2) ->
  eval (And e1 e2) = Some (BoolV false).
Proof. Admitted.

(* Challenge 3: comparisons of literal numbers always succeed. *)
Lemma challenge3_comparison_always_works : forall n1 n2,
  eval (LessThan (Num n1) (Num n2)) =
  Some (BoolV (Nat.ltb n1 n2)).
Proof. Admitted.

(* Challenge 4: a type error in an operand propagates. *)
Lemma challenge4_type_error_propagates : forall e1 e2,
  eval e1 = None ->
  eval (Plus e1 e2) = None.
Proof. Admitted.

(* ================================================================ *)
(* SUBMISSION GUIDELINES                                            *)
(* ================================================================ *)

(**
 * Replace every [Admitted] with a complete proof ending in [Qed].
 * When you are done, the file should compile with NO "Admitted"
 * warnings.  Compare your proofs against plih_abe_solutions.v.
 *)
