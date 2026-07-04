(**
Programming Languages in Rocq - ABE Solutions
Complete solutions to all exercises in plih_abe_exercises.v

The exercises reuse the [ABE] syntax and [eval] interpreter from the
lecture, so we simply import it.  A handful of exercise statements
carry extra hypotheses compared with the "obvious" untyped version -
see the comments at those exercises for why this is necessary in a
type-checked language.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_abe_lecture.

Import ListNotations.

(** * PART 1: BASIC BOOLEAN EVALUATION *)

Example ex1_bool_true : eval BTrue = Some (BoolV true).
Proof. reflexivity. Qed.

Example ex2_bool_false : eval BFalse = Some (BoolV false).
Proof. reflexivity. Qed.

Example ex3_and_true_true :
  eval (And BTrue BTrue) = Some (BoolV true).
Proof. reflexivity. Qed.

Example ex4_and_true_false :
  eval (And BTrue BFalse) = Some (BoolV false).
Proof. reflexivity. Qed.

Example ex5_or_false_false :
  eval (Or BFalse BFalse) = Some (BoolV false).
Proof. reflexivity. Qed.

(** * PART 2: TYPE MISMATCHES (Error Handling) *)

Example ex6_type_error_add :
  eval (Plus BTrue (Num 3)) = None.
Proof. reflexivity. Qed.

Example ex7_type_error_and :
  eval (And (Num 5) BTrue) = None.
Proof. reflexivity. Qed.

Example ex8_type_error_not_num :
  eval (Not (Num 42)) = None.
Proof. reflexivity. Qed.

(* Whatever [Plus e1 e2] does, it either fails or produces the sum of
   two numbers - it can never produce a boolean. *)
Lemma ex9_type_mismatch_both_operands : forall e1 e2,
  eval (Plus e1 e2) = None \/
  exists n1 n2, eval (Plus e1 e2) = Some (NumV (n1 + n2)).
Proof.
  intros e1 e2. simpl.
  destruct (eval e1) as [ [n1|b1] | ];
  destruct (eval e2) as [ [n2|b2] | ];
    try (left; reflexivity).
  right. exists n1, n2. reflexivity.
Qed.

(** * PART 3: CONDITIONALS *)

Example ex10_if_true_takes_then :
  eval (IfThenElse BTrue (Num 42) (Num 99)) = Some (NumV 42).
Proof. reflexivity. Qed.

Example ex11_if_false_takes_else :
  eval (IfThenElse BFalse (Num 42) (Num 99)) = Some (NumV 99).
Proof. reflexivity. Qed.

Example ex12_if_with_comparison :
  eval (IfThenElse (LessThan (Num 3) (Num 5))
                   (Plus (Num 1) (Num 2))
                   (Num 0))
  = Some (NumV 3).
Proof. reflexivity. Qed.

Example ex13_nested_if :
  eval (IfThenElse BTrue
                   (IfThenElse BFalse (Num 1) (Num 2))
                   (Num 3))
  = Some (NumV 2).
Proof. reflexivity. Qed.

(** * PART 4: COMPARISON OPERATIONS *)

Example ex14_less_than_true :
  eval (LessThan (Num 3) (Num 5)) = Some (BoolV true).
Proof. reflexivity. Qed.

Example ex15_less_than_false :
  eval (LessThan (Num 5) (Num 3)) = Some (BoolV false).
Proof. reflexivity. Qed.

Example ex16_equal_true :
  eval (Equal (Num 5) (Num 5)) = Some (BoolV true).
Proof. reflexivity. Qed.

Example ex17_equal_false :
  eval (Equal (Num 3) (Num 5)) = Some (BoolV false).
Proof. reflexivity. Qed.

(** * PART 5: BOOLEAN ALGEBRA *)

Lemma ex18_not_true :
  eval (Not BTrue) = Some (BoolV false).
Proof. reflexivity. Qed.

Lemma ex19_not_false :
  eval (Not BFalse) = Some (BoolV true).
Proof. reflexivity. Qed.

Lemma ex20_double_negation : forall (b : bool),
  eval (Not (Not (if b then BTrue else BFalse)))
  = Some (BoolV b).
Proof.
  intro b. destruct b; reflexivity.
Qed.

Lemma ex21_and_commutative : forall e1 e2,
  eval (And e1 e2) = eval (And e2 e1).
Proof.
  intros e1 e2. simpl.
  destruct (eval e1) as [ [n1|b1] | ];
  destruct (eval e2) as [ [n2|b2] | ];
    try reflexivity.
  rewrite Bool.andb_comm. reflexivity.
Qed.

Lemma ex22_or_commutative : forall e1 e2,
  eval (Or e1 e2) = eval (Or e2 e1).
Proof.
  intros e1 e2. simpl.
  destruct (eval e1) as [ [n1|b1] | ];
  destruct (eval e2) as [ [n2|b2] | ];
    try reflexivity.
  rewrite Bool.orb_comm. reflexivity.
Qed.

(** * PART 6: CONDITIONAL PROPERTIES *)

(* NOTE: the condition must evaluate to a boolean.  Without that
   hypothesis the conditional is itself a type error and evaluates to
   None, so the equation would be false (e.g. for cond = Num 0). *)
Lemma ex23_if_both_branches_equal : forall cond b,
  eval cond = Some (BoolV b) ->
  eval (IfThenElse cond (Num 5) (Num 5)) = Some (NumV 5).
Proof.
  intros cond b H. simpl. rewrite H. destruct b; reflexivity.
Qed.

Lemma ex24_if_then_takes_then : forall e1 e2,
  eval (IfThenElse BTrue e1 e2) = eval e1.
Proof. intros e1 e2. reflexivity. Qed.

Lemma ex25_if_false_takes_else : forall e1 e2,
  eval (IfThenElse BFalse e1 e2) = eval e2.
Proof. intros e1 e2. reflexivity. Qed.

(** * PART 7: COMBINING FEATURES *)

Example ex26_complex_expr :
  eval (Plus (IfThenElse BTrue (Num 3) (Num 5)) (Num 2))
  = Some (NumV 5).
Proof. reflexivity. Qed.

Example ex27_boolean_conditional :
  eval (And BTrue (IfThenElse (LessThan (Num 1) (Num 2))
                              BTrue
                              BFalse))
  = Some (BoolV true).
Proof. reflexivity. Qed.

(** * PART 8: TYPE CONSISTENCY PROOFS *)

(* The predicates is_numeric and is_boolean are defined in the lecture. *)

Lemma ex28_numeric_eval_to_num : forall e,
  is_numeric e -> exists n, eval e = Some (NumV n).
Proof.
  exact numeric_never_fails.
Qed.

Lemma ex29_boolean_eval_to_bool : forall e,
  is_boolean e -> exists b, eval e = Some (BoolV b).
Proof.
  exact boolean_never_fails.
Qed.

Lemma ex30_numeric_no_error : forall e,
  is_numeric e -> eval e <> None.
Proof.
  intros e Hnum Hcontra.
  destruct (numeric_never_fails e Hnum) as [n Hn].
  rewrite Hn in Hcontra. discriminate.
Qed.

(** * PART 9: EQUIVALENCE PROOFS *)

(* abe_equiv is defined in the lecture. *)

Lemma ex31_equiv_refl : forall e,
  abe_equiv e e.
Proof. exact abe_equiv_refl. Qed.

Lemma ex32_equiv_sym : forall e1 e2,
  abe_equiv e1 e2 -> abe_equiv e2 e1.
Proof. exact abe_equiv_sym. Qed.

Lemma ex33_equiv_trans : forall e1 e2 e3,
  abe_equiv e1 e2 -> abe_equiv e2 e3 -> abe_equiv e1 e3.
Proof. exact abe_equiv_trans. Qed.

Lemma ex34_demorgan_and : forall e1 e2,
  abe_equiv (Not (And e1 e2)) (Or (Not e1) (Not e2)).
Proof. exact de_morgan. Qed.

Lemma ex35_demorgan_or : forall e1 e2,
  abe_equiv (Not (Or e1 e2)) (And (Not e1) (Not e2)).
Proof.
  intros e1 e2. unfold abe_equiv. cbn.
  destruct (eval e1) as [ [n1|b1] | ];
  destruct (eval e2) as [ [n2|b2] | ];
  cbn; try reflexivity.
  destruct b1; destruct b2; reflexivity.
Qed.

(** * PART 10: COMPLEXITY AND SIZE *)

(* [size] is defined in the lecture. *)

Lemma ex36_size_positive : forall e,
  size e > 0.
Proof. exact size_positive. Qed.

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
Proof.
  intro e. induction e; simpl; lia.
Qed.

(** * PART 11: OPTIMIZATION *)

(**
A natural-looking optimization is "double-negation elimination":
rewrite [Not (Not e)] to [e].  In a TYPE-CHECKED language this is
UNSOUND: [Not (Not (Num 5))] is a type error (None) but [Num 5] is
not, so they are not equivalent.  This is the same phenomenon we saw
with [and_true_left] in the lecture.

The sound optimization we implement here is constant folding of [Not]
applied to a boolean LITERAL: [Not BTrue] becomes [BFalse] and
[Not BFalse] becomes [BTrue].
 *)

Definition fold_not (e : ABE) : ABE :=
  match e with
  | Not BTrue  => BFalse
  | Not BFalse => BTrue
  | _ => e
  end.

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

Lemma fold_not_correct : forall a, eval (fold_not a) = eval a.
Proof.
  intro a.
  destruct a as [n| a1 a2| a1 a2| | | a1 a2| a1 a2| a0| a1 a2| a1 a2| a1 a2 a3];
    try reflexivity.
  destruct a0; reflexivity.
Qed.

Lemma ex38_optimize_not_correct : forall e,
  eval (optimize_not e) = eval e.
Proof.
  induction e;
    try reflexivity;
    try (simpl; rewrite IHe1, IHe2; reflexivity).
  - (* Not e *)
    change (optimize_not (Not e)) with (fold_not (Not (optimize_not e))).
    rewrite fold_not_correct. simpl. rewrite IHe. reflexivity.
  - (* IfThenElse *)
    simpl. rewrite IHe1, IHe2, IHe3. reflexivity.
Qed.

Lemma fold_not_size : forall a, size (fold_not a) <= size a.
Proof.
  intro a.
  destruct a as [n| a1 a2| a1 a2| | | a1 a2| a1 a2| a0| a1 a2| a1 a2| a1 a2 a3];
    simpl; try lia.
  destruct a0; simpl; lia.
Qed.

Lemma ex39_optimize_not_reduces_size : forall e,
  size (optimize_not e) <= size e.
Proof.
  induction e; try (simpl; lia).
  (* Not e *)
  change (optimize_not (Not e)) with (fold_not (Not (optimize_not e))).
  eapply Nat.le_trans.
  - apply fold_not_size.
  - simpl. lia.
Qed.

(** * PART 12: CREATIVE PROBLEMS *)

(* Collect every boolean literal occurring in an expression. *)
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
Proof.
  induction e; simpl; intros b0 Hin; try contradiction.
  - (* Plus *) apply in_app_or in Hin. destruct Hin; auto.
  - (* Minus *) apply in_app_or in Hin. destruct Hin; auto.
  - (* BTrue *) destruct Hin as [H|H]; [ left; symmetry; exact H | contradiction ].
  - (* BFalse *) destruct Hin as [H|H]; [ right; symmetry; exact H | contradiction ].
  - (* And *) apply in_app_or in Hin. destruct Hin; auto.
  - (* Or *) apply in_app_or in Hin. destruct Hin; auto.
  - (* Not *) auto.
  - (* LessThan *) apply in_app_or in Hin. destruct Hin; auto.
  - (* Equal *) apply in_app_or in Hin. destruct Hin; auto.
  - (* IfThenElse *)
    apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [ auto |].
    apply in_app_or in Hin. destruct Hin; auto.
Qed.

(** * CHALLENGE SOLUTIONS *)

(* Challenge 1: an if-then-else with identical branches is equivalent to
   that branch - PROVIDED the condition is a boolean. *)
Lemma challenge1_if_neutral : forall cond e b,
  eval cond = Some (BoolV b) ->
  abe_equiv (IfThenElse cond e e) e.
Proof.
  intros cond e b H. unfold abe_equiv. simpl. rewrite H. destruct b; reflexivity.
Qed.

(* Challenge 2: our [eval] evaluates BOTH operands of [And] (it does not
   short-circuit), so to conclude the result we need [e2] to be a
   boolean as well.  Given that, a false left operand forces false. *)
Lemma challenge2_and_short_circuit : forall e1 e2 b2,
  eval e1 = Some (BoolV false) ->
  eval e2 = Some (BoolV b2) ->
  eval (And e1 e2) = Some (BoolV false).
Proof.
  intros e1 e2 b2 H1 H2. simpl. rewrite H1, H2. reflexivity.
Qed.

Lemma challenge3_comparison_always_works : forall n1 n2,
  eval (LessThan (Num n1) (Num n2)) =
  Some (BoolV (Nat.ltb n1 n2)).
Proof. intros n1 n2. reflexivity. Qed.

Lemma challenge4_type_error_propagates : forall e1 e2,
  eval e1 = None ->
  eval (Plus e1 e2) = None.
Proof.
  intros e1 e2 H. simpl. rewrite H. reflexivity.
Qed.
