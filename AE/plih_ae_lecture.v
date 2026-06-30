(**
 * Programming Languages in Rocq - AE Lecture
 * Arithmetic Expressions
 * 
 * This lecture covers:
 * 1. Defining a simple language of arithmetic expressions
 * 2. Writing an interpreter for the language
 * 3. Proving basic properties about the interpreter
 * 
 * This mirrors the first section of PLIH but with added proofs.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import plih_rocq_ae_shared.

(* ================================================================ *)
(* SECTION 1: SYNTAX - Defining the Language                       *)
(* ================================================================ *)

(**
 * An arithmetic expression (AE) is one of:
 *   - A number (literal)
 *   - The sum of two expressions
 *   - The difference of two expressions
 * 
 * This is an abstract syntax tree (AST). We're NOT implementing
 * parsing from text; we assume expressions are already in this form.
 * 
 * Compare to Haskell:
 *   data AE = Num Int | Plus AE AE | Minus AE AE
 *)

Inductive AE : Type :=
| Num : nat -> AE
| Plus : AE -> AE -> AE
| Minus : AE -> AE -> AE.

(**
 * Examples of AE terms (these are VALUES of type AE):
 * 
 *   Num 5              represents: 5
 *   Plus (Num 3) (Num 4)  represents: 3 + 4
 *   Minus (Num 10) (Num 2) represents: 10 - 2
 *   Plus (Num 1) (Plus (Num 2) (Num 3))  represents: 1 + (2 + 3)
 *)

(* Some example AE values *)
Definition ae_example_1 : AE := Num 5.
Definition ae_example_2 : AE := Plus (Num 3) (Num 4).
Definition ae_example_3 : AE := Minus (Num 10) (Num 2).
Definition ae_example_4 : AE := Plus (Num 1) (Plus (Num 2) (Num 3)).

(* ================================================================ *)
(* SECTION 2: SEMANTICS - Defining Evaluation                      *)
(* ================================================================ *)

(**
 * Now we define what these expressions MEAN writing an interpreter.
 * 
 * The eval function maps an AE to a natural number (its value).
 * 
 * Rocq requires that eval be TOTAL (terminates on all inputs).
 * This is enforced requiring structural recursion on the AE argument.
 * 
 * Compare to Haskell:
 *   eval :: AE -> Int
 *   eval (Num n) = n
 *   eval (Plus e1 e2) = eval e1 + eval e2
 *   eval (Minus e1 e2) = eval e1 - eval e2
 *)

Fixpoint eval (e : AE) : nat :=
  match e with
  | Num x => x
  | Plus x y => eval x + eval y
  | Minus x y => eval x - eval y
  end.

(* Let's test eval on our examples *)

Example test_eval_1 : eval (Num 5) = 5.
Proof. reflexivity. Qed.

Example test_eval_2 : eval (Plus (Num 3) (Num 4)) = 7.
Proof. reflexivity. Qed.

Example test_eval_3 : eval (Minus (Num 10) (Num 2)) = 8.
Proof. reflexivity. Qed.

Example test_eval_4 : eval (Plus (Num 1) (Plus (Num 2) (Num 3))) = 6.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 3: SIMPLE PROPERTIES                                    *)
(* ================================================================ *)

(**
 * Now we begin proving properties about eval.
 * This is what differentiates Rocq from Haskell: we can prove
 * that our interpreter has certain desirable properties.
 *)

(* PROPERTY 1: Evaluation is deterministic
 * 
 * If we evaluate the same expression twice, we get the same result.
 * This is OBVIOUS from the definition, but let's prove it formally.
 *)

Lemma eval_deterministic : forall e,
  eval e = eval e.
Proof.
  intro e.
  reflexivity.
Qed.

(* This is too trivial! Let's prove something more interesting. *)

(* PROPERTY 2: Eval distributes over Plus
 * 
 * This is obvious from the definition, but it's good practice.
 *)

Lemma eval_plus : forall e1 e2,
  eval (Plus e1 e2) = eval e1 + eval e2.
Proof.
  intro e1.
  intro e2.
  (* After simplifying, this is just: eval e1 + eval e2 = eval e1 + eval e2 *)
  reflexivity.
Qed.

(* PROPERTY 3: Plus is commutative on AE
 * 
 * eval (Plus e1 e2) = eval (Plus e2 e1)
 * 
 * Why? Because addition of natural numbers is commutative.
 *)

Lemma plus_commutative : forall e1 e2,
  eval (Plus e1 e2) = eval (Plus e2 e1).
Proof.
  intro e1.
  intro e2.
  (* Unfold the definition of eval *)
  simpl.
  (* Now we have: eval e1 + eval e2 = eval e2 + eval e1 *)
  (* This is Nat.add_comm *)
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(* PROPERTY 4: Plus is associative on AE *)

Lemma plus_associative : forall e1 e2 e3,
  eval (Plus (Plus e1 e2) e3) = eval (Plus e1 (Plus e2 e3)).
Proof.
  intro e1.
  intro e2.
  intro e3.
  simpl.
  (* Now we have: (eval e1 + eval e2) + eval e3 = eval e1 + (eval e2 + eval e3) *)
  symmetry.
  apply Nat.add_assoc.
Qed.

(* PROPERTY 5: Minus is not commutative (obviously) *)

Lemma minus_not_commutative : exists e1 e2,
  eval (Minus e1 e2) <> eval (Minus e2 e1).
Proof.
  exists (Num 5).
  exists (Num 3).
  intro H.
  (* Simplify the expressions *)
  simpl in H.
  (* Now H : 5 - 3 = 3 - 5, which simplifies to 2 = 0 *)
  discriminate.
Qed.

(* PROPERTY 6: Every AE evaluates to some natural number
 * 
 * This is TRIVIAL because eval always produces a nat,
 * but it's good to state explicitly.
 *)

Lemma eval_produces_nat : forall e,
  exists n, eval e = n.
Proof.
  intro e.
  exists (eval e).
  reflexivity.
Qed.

(* ================================================================ *)
(* SECTION 4: INDUCTION OVER AE                                    *)
(* ================================================================ *)

(**
 * The real power of formal verification comes when we use induction.
 * Since AE is inductively defined, we can prove properties * induction over its structure.
 *)

(* PROPERTY 7: Multiplication distributes over addition
 * 
 * For any k: k * (e1 + e2) = k * e1 + k * e2
 *)

Lemma distribute_mult : forall k e1 e2,
  k * eval (Plus e1 e2) = k * eval e1 + k * eval e2.
Proof.
  intro k.
  intro e1.
  intro e2.
  simpl.
  (* Now: k * (eval e1 + eval e2) = k * eval e1 + k * eval e2 *)
  lia.
Qed.

(* PROPERTY 8: Zero is identity for addition
 * 
 * For any e: eval (Plus (Num 0) e) = eval e
 *)

Lemma zero_plus_identity : forall e,
  eval (Plus (Num 0) e) = eval e.
Proof.
  intro e.
  reflexivity.
Qed.

(* PROPERTY 9: Every AE is >= 0 (when interpreted)
 * 
 * This uses induction on the structure of AE.
 *)

Lemma eval_nonnegative : forall e,
  0 <= eval e.
Proof.
  intro e.
  (* Use induction on the structure of e *)
  induction e as [n | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
  
  (* Case 1: e = Num n *)
  - simpl.
    (* Goal: 0 <= n *)
  lia.
  
  (* Case 2: e = Plus e1 e2 *)
  - simpl.
    (* Goal: 0 <= eval e1 + eval e2 *)
    (* We have IHe1 : 0 <= eval e1 and IHe2 : 0 <= eval e2 *)
  lia.
  
  (* Case 3: e = Minus e1 e2 *)
  - simpl.
    (* Goal: 0 <= eval e1 - eval e2 *)
    (* In Rocq, nat subtraction is truncated, so this is always true *)
  lia.
Qed.

(* ================================================================ *)
(* SECTION 5: AUXILIARY FUNCTIONS AND THEIR PROPERTIES              *)
(* ================================================================ *)

(**
 * Often we want helper functions to manipulate AE terms.
 * Let's prove properties about these helpers.
 *)

(* Helper: Count the number of operations in an AE *)

Fixpoint count_ops (e : AE) : nat :=
  match e with
  | Num _ => 0
  | Plus x y => 1 + count_ops x + count_ops y
  | Minus x y => 1 + count_ops x + count_ops y
  end.

Example count_ops_test_1 : count_ops (Num 5) = 0.
Proof. reflexivity. Qed.

Example count_ops_test_2 : count_ops (Plus (Num 3) (Num 4)) = 1.
Proof. reflexivity. Qed.

Example count_ops_test_3 : count_ops (Plus (Num 1) (Plus (Num 2) (Num 3))) = 2.
Proof. reflexivity. Qed.


(* ================================================================ *)
(* SECTION 6: EQUIVALENCE OF EXPRESSIONS                            *)
(* ================================================================ *)

(**
 * Two expressions are semantically equivalent if they evaluate to
 * the same value.
 *)

Definition ae_equiv (e1 e2 : AE) : Prop := eval e1 = eval e2.

(* Show that equivalence is an equivalence relation *)

Lemma ae_equiv_refl : forall e,
  ae_equiv e e.
Proof.
  intro e.
  unfold ae_equiv.
  reflexivity.
Qed.

Lemma ae_equiv_sym : forall e1 e2,
  ae_equiv e1 e2 -> ae_equiv e2 e1.
Proof.
  intro e1.
  intro e2.
  intro H.
  unfold ae_equiv in *.
  symmetry.
  exact H.
Qed.

Lemma ae_equiv_trans : forall e1 e2 e3,
  ae_equiv e1 e2 -> ae_equiv e2 e3 -> ae_equiv e1 e3.
Proof.
  intro e1.
  intro e2.
  intro e3.
  intro H12.
  intro H23.
  unfold ae_equiv in *.
  transitivity (eval e2).
  - exact H12.
  - exact H23.
Qed.

(* ================================================================ *)
(* SECTION 7: PROVING INEQUALITIES                                  *)
(* ================================================================ *)

(**
 * Sometimes we need to prove that one expression evaluates to
 * more or less than another.
 *)

Lemma plus_increases_value : forall e1 e2,
  eval (Plus e1 e2) >= eval e1.
Proof.
  intro e1.
  intro e2.
  simpl.
  lia.
Qed.

Lemma plus_both_positive : forall e1 e2,
  eval e1 > 0 -> eval e2 > 0 ->
  eval (Plus e1 e2) > 1.
Proof.
  intro e1.
  intro e2.
  intro H1.
  intro H2.
  simpl.
  lia.
Qed.

(* ================================================================ *)
(* SECTION 8: OPTIMIZATIONS AND CORRECTNESS PROOFS                 *)
(* ================================================================ *)

(**
 * A common task is to prove that an "optimized" version of
 * an interpreter is correct.
 *)

(* An optimization: replace (Plus e (Num 0)) with e *)

Fixpoint optimize_zero (e : AE) : AE :=
  match e with
  | Num x => Num x
  | Plus e (Num 0) => e
  | Plus x y => Plus (optimize_zero x) (optimize_zero y)
  | Minus x y => Minus (optimize_zero x) (optimize_zero y)
  end.

(* Prove that optimization preserves meaning *)

Lemma optimize_zero_correct : forall e,
  eval (optimize_zero e) = eval e.
Proof.
  intro e.
  induction e.
  - simpl. reflexivity.
  - simpl. rewrite <- IHe1. rewrite <- IHe2.
    destruct e2.
    -- destruct n.
       --- simpl. lia.
       --- simpl. reflexivity.
    -- simpl. reflexivity.
    -- simpl. reflexivity.
  - simpl. lia.
Qed.

(* ================================================================ *)
(* SECTION 9: REFLECTION / DECISION PROCEDURES                     *)
(* ================================================================ *)

(**
 * Sometimes we want to decide properties computationally
 * and then verify the decision.
 *)

(* Decide if two AE expressions are syntactically identical *)

Fixpoint ae_eq_dec (e1 e2 : AE) : bool :=
  match e1,e2 with
  | Num x, Num y => eqb x y
  | Plus x1 y1, Plus x2 y2 => andb (ae_eq_dec x1 x2) (ae_eq_dec y1 y2)
  | Minus x1 y1, Minus x2 y2 => andb (ae_eq_dec x1 x2) (ae_eq_dec y1 y2)
  | _,_ => false
  end.
                       
(* Prove that the decision procedure is correct *)

Search andb.
         
Lemma ae_eq_dec_correct : forall e1 e2,
  ae_eq_dec e1 e2 = true <-> e1 = e2.
Proof.
  intros e1 e2.
  split.
  generalize dependent e2.
  (* Forward direction: ae_eq_dec e1 e2 = true -> e1 = e2 *)
  - induction e1.
    -- destruct e2.
       --- simpl. rewrite Nat.eqb_eq. intros. subst. reflexivity.
       --- simpl. intros. discriminate.
       --- simpl. intros. discriminate.
    -- destruct e2.
       --- simpl. intros. discriminate.
       --- simpl. intros. apply andb_prop in H. destruct H.
           specialize IHe1_1 with e2_1. specialize IHe1_2 with e2_2.
           rewrite IHe1_1. rewrite IHe1_2. reflexivity.
           apply H0. apply H.
       --- simpl. intros. discriminate.
    -- destruct e2.
       --- simpl. intros. discriminate.
       --- simpl. intros. discriminate.
       --- simpl. intros. apply andb_prop in H. destruct H.
           specialize IHe1_1 with e2_1. specialize IHe1_2 with e2_2.
           rewrite IHe1_1. rewrite IHe1_2. reflexivity.
           apply H0. apply H.
  - intros H. subst. induction e2.
    -- simpl. apply Nat.eqb_refl.
    -- simpl. rewrite IHe2_1. rewrite IHe2_2. reflexivity.
    -- simpl. rewrite IHe2_1. rewrite IHe2_2. reflexivity.
Qed.

(* ================================================================ *)
(* SUMMARY                                                          *)
(* ================================================================ *)

(**
 * In this lecture, we:
 * 
 * 1. Defined a simple language (AE) using an inductive datatype
 * 2. Wrote an interpreter (eval) that is guaranteed to terminate
 * 3. Proved basic properties:
 *    - Commutativity of plus
 *    - Associativity of plus
 *    - Non-negativity of evaluation
 * 4. Proved correctness of optimizations
 * 5. Proved correctness of decision procedures
 * 
 * Key insight: By formalizing our language and interpreter in Rocq,
 * we can prove properties that would be difficult or impossible
 * to verify in Haskell alone.
 * 
 * Next: We'll add booleans, error handling, and environments.
 *)
