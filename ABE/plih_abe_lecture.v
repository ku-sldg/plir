(**
 * Programming Languages in Rocq - ABE Lecture
 * Arithmetic + Boolean Expressions
 *
 * This lecture extends AE by adding:
 * 1. Boolean literals and operations
 * 2. Comparison operations
 * 3. Conditional expressions
 * 4. Multiple value types
 * 5. Error handling
 *
 * This mirrors the PLIH section "Adding Booleans".
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_abe_shared.

(* ================================================================ *)
(* SECTION 1: SYNTAX - EXTENDED LANGUAGE                           *)
(* ================================================================ *)

(**
 * ABE extends AE with:
 *   - Boolean literals: BTrue, BFalse
 *   - Boolean operations: And, Or, Not
 *   - Comparisons: LessThan, Equal
 *   - Conditionals: IfThenElse
 *
 * Compare to the Haskell course (data ABE = Num | Plus | Minus
 * | Boolean | And | Leq | IsZero | If).  We split the boolean and
 * comparison operators out into separate constructors so that each
 * proof exercises one idea at a time.
 *)

Inductive ABE : Type :=
| Num        : nat -> ABE
| Plus       : ABE -> ABE -> ABE
| Minus      : ABE -> ABE -> ABE
| BTrue      : ABE
| BFalse     : ABE
| And        : ABE -> ABE -> ABE
| Or         : ABE -> ABE -> ABE
| Not        : ABE -> ABE
| LessThan   : ABE -> ABE -> ABE
| Equal      : ABE -> ABE -> ABE
| IfThenElse : ABE -> ABE -> ABE -> ABE.

(* Examples *)

Definition abe_example_1 : ABE := BTrue.
Definition abe_example_2 : ABE := And BTrue BFalse.
Definition abe_example_3 : ABE := LessThan (Num 3) (Num 5).

(* ================================================================ *)
(* SECTION 2: SEMANTICS - EVALUATION WITH MULTIPLE TYPES           *)
(* ================================================================ *)

(**
 * ABE evaluation is the KEY DIFFERENCE from AE:
 * - It can return either a number or a boolean (a [Value]).
 * - It can FAIL if there is a type mismatch.
 * - It returns [option Value] instead of [nat].
 *
 * Compare to Haskell:
 *   eval :: ABE -> Maybe ABE
 * We use [option Value]; [None] models a type error.
 *
 * The [Value] type (NumV / BoolV) lives in plih_rocq_abe_shared.v.
 *)

Fixpoint eval (e : ABE) : option Value :=
  match e with
  | Num n => Some (NumV n)
  | Plus a b =>
      match eval a, eval b with
      | Some (NumV n1), Some (NumV n2) => Some (NumV (n1 + n2))
      | _, _ => None
      end
  | Minus a b =>
      match eval a, eval b with
      | Some (NumV n1), Some (NumV n2) => Some (NumV (n1 - n2))
      | _, _ => None
      end
  | BTrue  => Some (BoolV true)
  | BFalse => Some (BoolV false)
  | And a b =>
      match eval a, eval b with
      | Some (BoolV b1), Some (BoolV b2) => Some (BoolV (b1 && b2))
      | _, _ => None
      end
  | Or a b =>
      match eval a, eval b with
      | Some (BoolV b1), Some (BoolV b2) => Some (BoolV (b1 || b2))
      | _, _ => None
      end
  | Not a =>
      match eval a with
      | Some (BoolV b) => Some (BoolV (negb b))
      | _ => None
      end
  | LessThan a b =>
      match eval a, eval b with
      | Some (NumV n1), Some (NumV n2) => Some (BoolV (Nat.ltb n1 n2))
      | _, _ => None
      end
  | Equal a b =>
      match eval a, eval b with
      | Some (NumV n1), Some (NumV n2) => Some (BoolV (Nat.eqb n1 n2))
      | _, _ => None
      end
  | IfThenElse c t f =>
      match eval c with
      | Some (BoolV true)  => eval t
      | Some (BoolV false) => eval f
      | _ => None
      end
  end.

(* Test cases *)

Example test_eval_1 : eval BTrue = Some (BoolV true).
Proof. reflexivity. Qed.

Example test_eval_2 : eval (And BTrue BFalse) = Some (BoolV false).
Proof. reflexivity. Qed.

Example test_eval_3 : eval (LessThan (Num 3) (Num 5)) = Some (BoolV true).
Proof. reflexivity. Qed.

Example test_eval_4 :
  eval (IfThenElse BTrue (Num 10) (Num 20)) = Some (NumV 10).
Proof. reflexivity. Qed.

(* Type mismatch: True + 3 is nonsense, so evaluation fails. *)
Example test_eval_error :
  eval (Plus BTrue (Num 3)) = None.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 3: CLASSIFYING EXPRESSIONS                              *)
(* ================================================================ *)

(**
 * Some expressions are guaranteed to produce numbers.
 * Some are guaranteed to produce booleans.
 * We capture these classes with inductive predicates.
 *)

(* An expression is "numeric" if it is built only from number operations. *)
Inductive is_numeric : ABE -> Prop :=
| numeric_num   : forall n, is_numeric (Num n)
| numeric_plus  : forall a b, is_numeric a -> is_numeric b -> is_numeric (Plus a b)
| numeric_minus : forall a b, is_numeric a -> is_numeric b -> is_numeric (Minus a b).

(* An expression is "boolean" if it ultimately produces a boolean.
   Note that comparisons take numeric operands but produce booleans. *)
Inductive is_boolean : ABE -> Prop :=
| boolean_true  : is_boolean BTrue
| boolean_false : is_boolean BFalse
| boolean_and   : forall a b, is_boolean a -> is_boolean b -> is_boolean (And a b)
| boolean_or    : forall a b, is_boolean a -> is_boolean b -> is_boolean (Or a b)
| boolean_not   : forall a, is_boolean a -> is_boolean (Not a)
| boolean_lt    : forall a b, is_numeric a -> is_numeric b -> is_boolean (LessThan a b)
| boolean_eq    : forall a b, is_numeric a -> is_numeric b -> is_boolean (Equal a b).

(* Numeric expressions always evaluate successfully to a number. *)
Lemma numeric_never_fails : forall e,
  is_numeric e -> exists n, eval e = Some (NumV n).
Proof.
  intros e Hnum.
  induction Hnum.
  - (* Num n *)
    exists n. reflexivity.
  - (* Plus a b *)
    destruct IHHnum1 as [n1 H1].
    destruct IHHnum2 as [n2 H2].
    exists (n1 + n2).
    simpl. rewrite H1, H2. reflexivity.
  - (* Minus a b *)
    destruct IHHnum1 as [n1 H1].
    destruct IHHnum2 as [n2 H2].
    exists (n1 - n2).
    simpl. rewrite H1, H2. reflexivity.
Qed.

(* Boolean expressions always evaluate successfully to a boolean. *)
Lemma boolean_never_fails : forall e,
  is_boolean e -> exists b, eval e = Some (BoolV b).
Proof.
  intros e Hbool.
  induction Hbool.
  - (* BTrue *)
    exists true. reflexivity.
  - (* BFalse *)
    exists false. reflexivity.
  - (* And a b *)
    destruct IHHbool1 as [b1 H1].
    destruct IHHbool2 as [b2 H2].
    exists (b1 && b2).
    simpl. rewrite H1, H2. reflexivity.
  - (* Or a b *)
    destruct IHHbool1 as [b1 H1].
    destruct IHHbool2 as [b2 H2].
    exists (b1 || b2).
    simpl. rewrite H1, H2. reflexivity.
  - (* Not a *)
    destruct IHHbool as [b H].
    exists (negb b).
    simpl. rewrite H. reflexivity.
  - (* LessThan a b *)
    destruct (numeric_never_fails a H) as [n1 H1].
    destruct (numeric_never_fails b H0) as [n2 H2].
    exists (Nat.ltb n1 n2).
    simpl. rewrite H1, H2. reflexivity.
  - (* Equal a b *)
    destruct (numeric_never_fails a H) as [n1 H1].
    destruct (numeric_never_fails b H0) as [n2 H2].
    exists (Nat.eqb n1 n2).
    simpl. rewrite H1, H2. reflexivity.
Qed.

(* ================================================================ *)
(* SECTION 4: WORKING WITH CONDITIONALS                            *)
(* ================================================================ *)

(**
 * Conditionals are interesting because:
 * - The condition must be boolean.
 * - The branches can return anything.
 * - We only evaluate ONE branch.
 *)

Lemma if_true_evaluates_then : forall e1 e2,
  eval (IfThenElse BTrue e1 e2) = eval e1.
Proof.
  intros e1 e2. reflexivity.
Qed.

Lemma if_false_evaluates_else : forall e1 e2,
  eval (IfThenElse BFalse e1 e2) = eval e2.
Proof.
  intros e1 e2. reflexivity.
Qed.

(* If the condition is a boolean and both branches are the same constant,
   the result is that constant.  We need to know the condition is a
   boolean - otherwise the conditional would itself be a type error. *)
Lemma if_branches_equal : forall cond b,
  eval cond = Some (BoolV b) ->
  eval (IfThenElse cond (Num 5) (Num 5)) = Some (NumV 5).
Proof.
  intros cond b Hcond.
  simpl. rewrite Hcond. destruct b; reflexivity.
Qed.

(* ================================================================ *)
(* SECTION 5: TYPE CONSISTENCY                                      *)
(* ================================================================ *)

(**
 * An important property: a numeric expression, if it evaluates,
 * evaluates to a number.  This is a stepping stone toward formal
 * type checking.
 *)

Lemma numeric_produces_numbers : forall e,
  is_numeric e ->
  forall v, eval e = Some v ->
  exists n, v = NumV n.
Proof.
  intros e Hnum v Heval.
  destruct (numeric_never_fails e Hnum) as [n Hn].
  rewrite Hn in Heval.
  injection Heval as Heval.
  exists n. symmetry. exact Heval.
Qed.

(* ================================================================ *)
(* SECTION 6: EQUIVALENCE AND OPTIMIZATION                         *)
(* ================================================================ *)

(**
 * Two expressions are equivalent when they evaluate to the same
 * result.  Because eval returns [option Value], "same result" covers
 * both "both succeed with the same value" and "both fail".
 *)

Definition abe_equiv (e1 e2 : ABE) : Prop := eval e1 = eval e2.

Lemma abe_equiv_refl : forall e,
  abe_equiv e e.
Proof.
  intro e. unfold abe_equiv. reflexivity.
Qed.

Lemma abe_equiv_sym : forall e1 e2,
  abe_equiv e1 e2 -> abe_equiv e2 e1.
Proof.
  intros e1 e2 H. unfold abe_equiv in *. symmetry. exact H.
Qed.

Lemma abe_equiv_trans : forall e1 e2 e3,
  abe_equiv e1 e2 -> abe_equiv e2 e3 -> abe_equiv e1 e3.
Proof.
  intros e1 e2 e3 H12 H23.
  unfold abe_equiv in *.
  transitivity (eval e2); [ exact H12 | exact H23 ].
Qed.

(* De Morgan's law holds for our boolean expressions - including the
   error cases, where both sides fail in exactly the same situations. *)
Lemma de_morgan : forall e1 e2,
  abe_equiv (Not (And e1 e2))
            (Or (Not e1) (Not e2)).
Proof.
  intros e1 e2. unfold abe_equiv. cbn.
  destruct (eval e1) as [ [n1|b1] | ];
  destruct (eval e2) as [ [n2|b2] | ];
  cbn; try reflexivity.
  destruct b1; destruct b2; reflexivity.
Qed.

(* ================================================================ *)
(* SECTION 7: BOOLEAN PROPERTIES                                    *)
(* ================================================================ *)

Lemma not_true : eval (Not BTrue) = Some (BoolV false).
Proof. reflexivity. Qed.

Lemma not_false : eval (Not BFalse) = Some (BoolV true).
Proof. reflexivity. Qed.

(**
 * In a type-checked language, [And BTrue e] is only well behaved when
 * [e] is itself a boolean: if [e] evaluates to a number the whole
 * expression is a type error.  So these identities carry a hypothesis
 * about what [e] evaluates to - a small but important difference from
 * the untyped intuition "And True e = e".
 *)

Lemma and_true_left : forall e b,
  eval e = Some (BoolV b) ->
  eval (And BTrue e) = Some (BoolV b).
Proof.
  intros e b H. simpl. rewrite H. reflexivity.
Qed.

Lemma and_false_left : forall e b,
  eval e = Some (BoolV b) ->
  eval (And BFalse e) = Some (BoolV false).
Proof.
  intros e b H. simpl. rewrite H. reflexivity.
Qed.

Lemma or_true_left : forall e b,
  eval e = Some (BoolV b) ->
  eval (Or BTrue e) = Some (BoolV true).
Proof.
  intros e b H. simpl. rewrite H. reflexivity.
Qed.

Lemma or_false_left : forall e b,
  eval e = Some (BoolV b) ->
  eval (Or BFalse e) = Some (BoolV b).
Proof.
  intros e b H. simpl. rewrite H. reflexivity.
Qed.

(* ================================================================ *)
(* SECTION 8: COMPARISON PROPERTIES                                *)
(* ================================================================ *)

Lemma less_than_3_5 :
  eval (LessThan (Num 3) (Num 5)) = Some (BoolV true).
Proof. reflexivity. Qed.

Lemma less_than_5_3 :
  eval (LessThan (Num 5) (Num 3)) = Some (BoolV false).
Proof. reflexivity. Qed.

Lemma equal_reflexive : forall n,
  eval (Equal (Num n) (Num n)) = Some (BoolV true).
Proof.
  intro n.
  simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(* ================================================================ *)
(* SECTION 9: CONDITIONAL SEMANTICS                                *)
(* ================================================================ *)

Lemma conditional_with_arithmetic_branches :
  eval (IfThenElse (LessThan (Num 3) (Num 5))
                   (Plus (Num 1) (Num 2))
                   (Num 10))
  = Some (NumV 3).
Proof. reflexivity. Qed.

Lemma conditional_is_lazy :
  eval (IfThenElse BFalse (Plus BTrue (Num 1)) (Num 42))
  = Some (NumV 42).
Proof.
  (* Notice: we never try to evaluate (Plus BTrue (Num 1)),
     which is itself a type error, because the condition is false.
     Only the taken branch is evaluated. *)
  reflexivity.
Qed.

(* ================================================================ *)
(* SECTION 10: SIZE AND COMPLEXITY METRICS                         *)
(* ================================================================ *)

Fixpoint size (e : ABE) : nat :=
  match e with
  | Num _ => 1
  | BTrue => 1
  | BFalse => 1
  | Not a => 1 + size a
  | Plus a b => 1 + size a + size b
  | Minus a b => 1 + size a + size b
  | And a b => 1 + size a + size b
  | Or a b => 1 + size a + size b
  | LessThan a b => 1 + size a + size b
  | Equal a b => 1 + size a + size b
  | IfThenElse a b c => 1 + size a + size b + size c
  end.

Lemma size_positive : forall e,
  size e > 0.
Proof.
  intro e. induction e; simpl; lia.
Qed.

(* Count the number of conditionals in an expression. *)
Fixpoint count_conditionals (e : ABE) : nat :=
  match e with
  | Num _ => 0
  | BTrue => 0
  | BFalse => 0
  | Not a => count_conditionals a
  | Plus a b => count_conditionals a + count_conditionals b
  | Minus a b => count_conditionals a + count_conditionals b
  | And a b => count_conditionals a + count_conditionals b
  | Or a b => count_conditionals a + count_conditionals b
  | LessThan a b => count_conditionals a + count_conditionals b
  | Equal a b => count_conditionals a + count_conditionals b
  | IfThenElse a b c =>
      1 + count_conditionals a + count_conditionals b + count_conditionals c
  end.

Lemma size_bounds_conditionals : forall e,
  count_conditionals e <= size e.
Proof.
  intro e. induction e; simpl; lia.
Qed.

(* ================================================================ *)
(* SUMMARY                                                          *)
(* ================================================================ *)

(**
 * In this lecture, we:
 *
 * 1. Extended the language with booleans, comparisons, and conditionals.
 * 2. Introduced multiple value types (NumV, BoolV).
 * 3. Added error handling with [option Value].
 * 4. Proved that well-formed (numeric / boolean) expressions never fail.
 * 5. Explored boolean algebra properties, including De Morgan's law.
 * 6. Introduced type-consistency reasoning.
 * 7. Proved equivalence is reflexive, symmetric, and transitive.
 *
 * Key insight: adding booleans forces us to rethink evaluation.  We can
 * no longer assume every expression evaluates to a nat - some evaluate
 * to booleans, and some fail with type errors.
 *
 * Next: students add type checking to rule out the errors statically.
 *)
