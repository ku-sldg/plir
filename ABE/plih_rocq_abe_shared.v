(**
 * Programming Languages in Rocq - ABE Shared Infrastructure
 * Arithmetic + Boolean Expressions
 *
 * Extends the foundation from AE to support multiple value types
 * and error handling.
 *
 * This module provides the [Value] type and the operations the ABE
 * interpreter is built from.  The interpreter itself lives in
 * plih_abe_lecture.v.
 *)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_ae_shared.

(* ================================================================ *)
(* PART 1: VALUE TYPES FOR ABE                                     *)
(* ================================================================ *)

(**
 * In AE, everything evaluated to nat.
 * In ABE, we have two kinds of values: numbers and booleans.
 *
 * We use a tagged union (inductive type) to represent both.
 *
 * Compare to Haskell, where the course represents values as ABE terms
 * (Num and Boolean).  Here we use a dedicated [Value] type so that the
 * distinction between *syntax* (ABE) and *values* (Value) is explicit.
 *)

Inductive Value : Type :=
| NumV  : nat  -> Value
| BoolV : bool -> Value.

(* ================================================================ *)
(* PART 2: VALUE OPERATIONS                                        *)
(* ================================================================ *)

(* Extract a number from a value (if it is one) *)
Definition value_to_nat (v : Value) : option nat :=
  match v with
  | NumV n  => Some n
  | BoolV _ => None
  end.

(* Extract a boolean from a value (if it is one) *)
Definition value_to_bool (v : Value) : option bool :=
  match v with
  | BoolV b => Some b
  | NumV _  => None
  end.

(* Convert nat to Value *)
Definition nat_to_value : nat -> Value := NumV.

(* Convert bool to Value *)
Definition bool_to_value : bool -> Value := BoolV.

(* ================================================================ *)
(* PART 3: ERROR HANDLING WITH OPTION                              *)
(* ================================================================ *)

(**
 * Evaluation can now fail if there is a type mismatch.
 * For example: (True + 3) is syntactically valid but semantically
 * nonsense.
 *
 * We reuse the option monad from the AE shared library
 * ([bind], [return_], and the [>>=] notation) to represent
 * success/failure.
 *)

Definition eval_result : Type := option Value.

(* Lift a numeric binary operation into the option monad.
   Both operands must be numbers, otherwise we get a type error. *)
Definition lift_binary_num (op : nat -> nat -> nat) (v1 v2 : Value)
  : option Value :=
  match v1, v2 with
  | NumV n1, NumV n2 => Some (NumV (op n1 n2))
  | _, _ => None
  end.

(* Lift a boolean binary operation into the option monad.
   Both operands must be booleans. *)
Definition lift_binary_bool (op : bool -> bool -> bool) (v1 v2 : Value)
  : option Value :=
  match v1, v2 with
  | BoolV b1, BoolV b2 => Some (BoolV (op b1 b2))
  | _, _ => None
  end.

(* Comparison: takes two numbers, returns a boolean. *)
Definition lift_compare (op : nat -> nat -> bool) (v1 v2 : Value)
  : option Value :=
  match v1, v2 with
  | NumV n1, NumV n2 => Some (BoolV (op n1 n2))
  | _, _ => None
  end.

(* ================================================================ *)
(* PART 4: TYPE CLASSIFICATION                                     *)
(* ================================================================ *)

(**
 * We can ask: "What type of value is this?"
 * This is preparation for actual type checking in later chapters.
 *)

Inductive ValueType : Type :=
| TNum  : ValueType
| TBool : ValueType.

Definition value_type (v : Value) : ValueType :=
  match v with
  | NumV _  => TNum
  | BoolV _ => TBool
  end.

(* A value [v] has type [t] when its computed type is exactly [t]. *)
Definition value_has_type (v : Value) (t : ValueType) : Prop :=
  value_type v = t.

Lemma num_value_has_type_num : forall n,
  value_has_type (NumV n) TNum.
Proof.
  intro n.
  unfold value_has_type, value_type.
  reflexivity.
Qed.

Lemma bool_value_has_type_bool : forall b,
  value_has_type (BoolV b) TBool.
Proof.
  intro b.
  unfold value_has_type, value_type.
  reflexivity.
Qed.

(* ================================================================ *)
(* PART 5: BOOLEAN OPERATIONS                                      *)
(* ================================================================ *)

(* Logical AND *)
Definition bool_and (b1 b2 : bool) : bool := andb b1 b2.

(* Logical OR *)
Definition bool_or (b1 b2 : bool) : bool := orb b1 b2.

(* Logical NOT *)
Definition bool_not (b : bool) : bool := negb b.

(* ================================================================ *)
(* PART 6: COMPARISON OPERATORS                                    *)
(* ================================================================ *)

Definition nat_less_than (n1 n2 : nat) : bool := Nat.ltb n1 n2.

Definition nat_equal (n1 n2 : nat) : bool := Nat.eqb n1 n2.

Definition nat_less_equal (n1 n2 : nat) : bool := Nat.leb n1 n2.

Lemma nat_less_than_correct : forall n1 n2,
  nat_less_than n1 n2 = true <-> n1 < n2.
Proof.
  intros n1 n2.
  unfold nat_less_than.
  apply Nat.ltb_lt.
Qed.

Lemma nat_equal_correct : forall n1 n2,
  nat_equal n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2.
  unfold nat_equal.
  apply Nat.eqb_eq.
Qed.

(* ================================================================ *)
(* PART 7: ERROR ANALYSIS                                          *)
(* ================================================================ *)

(**
 * When evaluation returns None, what went wrong?
 * We can classify errors.  For now the interpreter only uses option,
 * but this type previews how we might track richer error information.
 *)

Inductive EvalError : Type :=
| TypeError    : EvalError
| UnknownError : EvalError.

(* ================================================================ *)
(* PART 8: USEFUL LEMMAS ABOUT VALUES                              *)
(* ================================================================ *)

Lemma value_extraction_consistent : forall n,
  value_to_nat (NumV n) = Some n.
Proof.
  intro n.
  reflexivity.
Qed.

Lemma value_extraction_bool : forall b,
  value_to_bool (BoolV b) = Some b.
Proof.
  intro b.
  reflexivity.
Qed.

Lemma num_not_bool : forall n b,
  NumV n <> BoolV b.
Proof.
  intros n b.
  discriminate.
Qed.

Lemma value_type_decidable : forall v t,
  {value_has_type v t} + {~ value_has_type v t}.
Proof.
  intros v t.
  unfold value_has_type, value_type.
  destruct v; destruct t; simpl;
    try (left; reflexivity);
    right; discriminate.
Qed.

(* ================================================================ *)
(* PART 9: BOOLEAN ALGEBRA PROPERTIES                              *)
(* ================================================================ *)

Lemma and_commutative : forall b1 b2,
  bool_and b1 b2 = bool_and b2 b1.
Proof.
  intros b1 b2.
  unfold bool_and.
  destruct b1; destruct b2; reflexivity.
Qed.

Lemma or_commutative : forall b1 b2,
  bool_or b1 b2 = bool_or b2 b1.
Proof.
  intros b1 b2.
  unfold bool_or.
  destruct b1; destruct b2; reflexivity.
Qed.

Lemma not_involutive : forall b,
  bool_not (bool_not b) = b.
Proof.
  intro b.
  unfold bool_not.
  destruct b; reflexivity.
Qed.

Lemma not_and : forall b1 b2,
  bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2.
  unfold bool_not, bool_and, bool_or.
  destruct b1; destruct b2; reflexivity.
Qed.

Lemma not_or : forall b1 b2,
  bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2.
  unfold bool_not, bool_and, bool_or.
  destruct b1; destruct b2; reflexivity.
Qed.

(* ================================================================ *)
(* PART 10: EXPORTED INTERFACE                                     *)
(* ================================================================ *)

Export List.
Export Nat.
