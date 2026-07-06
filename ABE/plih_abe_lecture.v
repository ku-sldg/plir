(** * Programming Languages in Rocq - Arithmetic + Boolean Expressions *)

(**
This lecture extends AE by adding:
#<ol>#
#<li>#Boolean literals and operations#</li>#
#<li>#Comparison operations#</li>#
#<li>#Conditional expressions#</li>#
#<li>#Multiple value types#</li>#
#<li>#Error handling#</li>#
#</ol>#

This mirrors the PLIH section "Adding Booleans".
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_abe_shared.

(** * SECTION 1: SYNTAX - EXTENDED LANGUAGE *)

(**
ABE extends AE with:

  - Boolean literals: [BTrue], [BFalse]
  - Boolean operations: [And], [Or], [Not]
  - Comparisons: [LessThan], [Equal]
  - Conditionals: [IfThenElse]

We give the boolean and comparison operators each their _own_ constructor -
rather than folding several of them into one - so that every proof exercises a
single idea at a time.
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

(** * SECTION 2: SEMANTICS - EVALUATION WITH MULTIPLE TYPES *)

(**
Evaluation is the _key difference_ from AE:

  - it can return either a number or a boolean (a [Value]);
  - it can _fail_ when an operator's operands do not have the types it
    expects (a type mismatch);
  - so it returns an [option Value] rather than a bare [nat], with [None]
    standing for a type error.

The [Value] type ([NumV] / [BoolV]) lives in plih_rocq_abe_shared.v.
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

(**
Every operator follows the same shape: evaluate the operands, then _check their
[Value] shape_ with a nested [match].  [Plus] insists on two [NumV]s and
produces a [NumV]; [And] insists on two [BoolV]s; [LessThan] takes two [NumV]s
but produces a [BoolV].  Anything else - a boolean where a number is wanted, or
an operand that already failed with [None] - falls through the [_, _ => None]
wildcard, so a type error _propagates_ outward as [None].

[IfThenElse] is the one construct that does not evaluate all of its parts: it
evaluates the condition and then _only_ the taken branch.  That is why a type
error hiding in the untaken branch never surfaces - see [conditional_is_lazy]
in Section 9.
 *)

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

(** * SECTION 3: CLASSIFYING EXPRESSIONS *)

(**
Some expressions are guaranteed to produce a number, some a boolean.  We
capture these classes with _inductive predicates_.

An [Inductive] whose result is [Prop] (like [is_numeric] below) is not a
datatype of values but a set of _inference rules_: each constructor is a rule
saying when the predicate holds.  [numeric_num] says [Num n] is numeric with no
premises; [numeric_plus] says [Plus a b] is numeric _provided_ [a] and [b] are.
A proof that a particular expression is [is_numeric] is therefore a small
derivation built from these rules - and, like any inductive definition, we can
run [induction] on it.
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

(**
A note on inducting over a _derivation_.

In AE we ran [induction] on a term ([induction e]).  Here [induction Hnum] runs
it on a _hypothesis_ - the derivation [Hnum : is_numeric e].  It is the same
principle applied to [is_numeric]'s rules: one subgoal per rule that could have
built [Hnum] ([numeric_num], [numeric_plus], [numeric_minus]), with an
induction hypothesis for each recursive premise.  In the [Plus] case those
hypotheses are [IHHnum1] and [IHHnum2], one per operand.

Each hypothesis is itself an existential ([exists n, eval a = Some (NumV n)]),
so [destruct IHHnum1 as [n1 H1]] unpacks it - naming the witness [n1] and the
equation [H1] - after which [exists (n1 + n2)] supplies the answer and
[rewrite H1, H2] rewrites both operands at once.  [boolean_never_fails] follows
the same pattern, and in its comparison cases even calls [numeric_never_fails]
to discharge the numeric premises.
 *)

(** * SECTION 4: WORKING WITH CONDITIONALS *)

(**
Conditionals are interesting because:
- The condition must be boolean.
- The branches can return anything.
- We only evaluate ONE branch.
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

(** * SECTION 5: TYPE CONSISTENCY *)

(**
An important property: a numeric expression, if it evaluates,
evaluates to a number.  This is a stepping stone toward formal
type checking.
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

(**
A note on [injection].

The proof reaches a hypothesis [Heval : Some (NumV n) = Some v] and needs the
underlying [v = NumV n].  Constructors are _injective_ and _disjoint_: [Some x
= Some y] holds only when [x = y], and two different constructors are never
equal (the fact [discriminate] exploited in AE).  [injection Heval as Heval]
uses injectivity to peel off the shared [Some], leaving the hypothesis
[NumV n = v]; [symmetry] then orients it and [exact] closes the goal.
 *)

(** * SECTION 6: EQUIVALENCE AND OPTIMIZATION *)

(**
Two expressions are equivalent when they evaluate to the same result.  Because
[eval] returns an [option Value], "same result" now covers both "both succeed
with the same value" _and_ "both fail with [None]".

As in AE, [abe_equiv] is an _equivalence relation_: the next three lemmas prove
it _reflexive_, _symmetric_, and _transitive_, each reducing (after [unfold]) to
the corresponding fact about equality.  De Morgan's law then shows a genuine
boolean-algebra equivalence.
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

(**
That proof of De Morgan's law uses three case-analysis tools worth naming.

[abe_equiv] unfolds exactly as [ae_equiv] did in AE, so [reflexivity],
[symmetry], and [transitivity] apply to the underlying [eval _ = eval _].
([abe_equiv_trans] even discharges its two remaining goals with
[transitivity (eval e2); [ exact H12 | exact H23 ]] - the [; [ g1 | g2 ]] form
runs a _different_ tactic on each subgoal the [;] produced.)

  - [cbn] simplifies much like [simpl] but is gentler and more predictable;
    here it exposes the nested [match]es inside [eval] without over-reducing.
  - [destruct (eval e1) as [ [n1|b1] | ]] case-splits the _result_ of an
    expression.  Its type is [option Value], so the outer [[ _ | ]] splits
    [Some] from [None] and the inner [[n1|b1]] splits a [Some]'s [Value] into
    [NumV n1] / [BoolV b1] - all in one nested pattern.  Splitting both operands
    leaves nine combinations to consider.
  - [try reflexivity] attempts [reflexivity] and _quietly does nothing_ if it
    fails.  Eight of the nine combinations close immediately; [try] disposes of
    them and leaves only the genuine bool/bool case, finished by
    [destruct b1; destruct b2; reflexivity].
 *)

(** * SECTION 7: BOOLEAN PROPERTIES *)

(**
The boolean operators obey the usual laws - but, because evaluation is typed
now, the laws come with conditions.  We start with the negations of the
literals, then look at how [And]/[Or] behave once the left operand is known.
 *)

Lemma not_true : eval (Not BTrue) = Some (BoolV false).
Proof. reflexivity. Qed.

Lemma not_false : eval (Not BFalse) = Some (BoolV true).
Proof. reflexivity. Qed.

(**
In a type-checked language, [And BTrue e] is only well behaved when
[e] is itself a boolean: if [e] evaluates to a number the whole
expression is a type error.  So these identities carry a hypothesis
about what [e] evaluates to - a small but important difference from
the untyped intuition "And True e = e".
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

(** * SECTION 8: COMPARISON PROPERTIES *)

(**
Comparisons take two numbers and produce a boolean.  Concrete comparisons
compute, so they close by [reflexivity]; comparing a variable [n] with itself
needs one small rewrite with [Nat.eqb_refl].
 *)

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

(** * SECTION 9: CONDITIONAL SEMANTICS *)

(**
Two more looks at [IfThenElse]: a conditional whose branches are arithmetic,
and the payoff of evaluating only the taken branch - a type error sitting in
the _untaken_ branch is never triggered.
 *)

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

(** * SECTION 10: SIZE AND COMPLEXITY METRICS *)

(**
Finally, two structural measures defined by recursion over the syntax: [size]
counts the nodes of an expression, and [count_conditionals] counts its
[IfThenElse]s.  Both facts below are one-liners - [induction e; simpl; lia]
handles every constructor uniformly.
 *)

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

(** * SECTION 11: CONCRETE SYNTAX - A NOTATION PARSER *)

(**
As in AE, we can give ABE a layer of CONCRETE syntax so that programs
read the way we write them on the board, while still elaborating into
the abstract [ABE] tree.  Following Software Foundations' Imp, the
parser is built entirely from Rocq NOTATIONS - no separate lexer or
parser generator - and a concrete term is DEFINITIONALLY EQUAL to the
abstract tree it denotes.  The recipe is the same three ingredients as
AE, but the grammar is larger: it now covers booleans, the boolean
connectives, comparisons, and the conditional.
 *)

(**
INGREDIENT 1 - a COERCION from [nat] to [ABE], so a bare numeral stands
for [Num].
 *)

Coercion Num : nat >-> ABE.

(**
INGREDIENT 2 - a private grammar entry [abe], entered with [<{ ... }>],
plus grouping parentheses and the escape hatch back to ordinary Rocq
terms (numerals and [ABE] variables).
 *)

Declare Custom Entry abe.
Declare Scope abe_scope.
Delimit Scope abe_scope with abe.

Notation "<{ e }>" := e (e custom abe at level 99) : abe_scope.
Notation "( x )" := x (in custom abe, x at level 99) : abe_scope.
Notation "x" := x (in custom abe at level 0, x constr at level 0) : abe_scope.

(**
INGREDIENT 3 - the operators.  The boolean literals [true]/[false] are
keywords in the grammar (so they mean [BTrue]/[BFalse] rather than
Rocq's [bool] constructors).  The remaining notations each carry a
PRECEDENCE LEVEL; higher levels bind more loosely, so the ordering
below reads, from tightest to loosest:

  50  + -         (arithmetic)
  70  < =         (comparisons, non-associative)
  75  ~           (boolean negation, prefix)
  80  &&          (conjunction)
  85  ||          (disjunction)
  89  if/then/else

Thus [1 + 2 < 4] is [(1 + 2) < 4] and [a || b && c] is [a || (b && c)],
matching the usual reading.
 *)

Notation "'true'"  := BTrue  (in custom abe at level 0) : abe_scope.
Notation "'false'" := BFalse (in custom abe at level 0) : abe_scope.

Notation "x + y" := (Plus x y)     (in custom abe at level 50, left associativity) : abe_scope.
Notation "x - y" := (Minus x y)    (in custom abe at level 50, left associativity) : abe_scope.
Notation "x < y" := (LessThan x y) (in custom abe at level 70, no associativity) : abe_scope.
Notation "x = y" := (Equal x y)    (in custom abe at level 70, no associativity) : abe_scope.
Notation "'~' x" := (Not x)        (in custom abe at level 75, right associativity) : abe_scope.
Notation "x && y" := (And x y)     (in custom abe at level 80, left associativity) : abe_scope.
Notation "x || y" := (Or x y)      (in custom abe at level 85, left associativity) : abe_scope.
Notation "'if' c 'then' t 'else' f" := (IfThenElse c t f)
  (in custom abe at level 89, c custom abe at level 99,
   t custom abe at level 99, f custom abe at level 99) : abe_scope.

Open Scope abe_scope.

(**
Because the notation is only sugar, every parse below is proved by
[reflexivity].
 *)

Example parse_arith : <{ 3 + 4 }> = Plus (Num 3) (Num 4).
Proof. reflexivity. Qed.

Example parse_and : <{ true && false }> = And BTrue BFalse.
Proof. reflexivity. Qed.

Example parse_not : <{ ~ true }> = Not BTrue.
Proof. reflexivity. Qed.

Example parse_cmp : <{ 3 < 5 }> = LessThan (Num 3) (Num 5).
Proof. reflexivity. Qed.

(* Precedence: [&&] binds tighter than [||]. *)
Example parse_bool_prec : <{ true || false && true }> = Or BTrue (And BFalse BTrue).
Proof. reflexivity. Qed.

(* Precedence: arithmetic binds tighter than comparison. *)
Example parse_mixed_prec : <{ 1 + 2 < 4 }> = LessThan (Plus (Num 1) (Num 2)) (Num 4).
Proof. reflexivity. Qed.

(* The examples from Section 1, written concretely. *)
Example abe_example_2_concrete : <{ true && false }> = abe_example_2.
Proof. reflexivity. Qed.

Example abe_example_3_concrete : <{ 3 < 5 }> = abe_example_3.
Proof. reflexivity. Qed.

(* A conditional with arithmetic branches (compare Section 9). *)
Example parse_if :
  <{ if 3 < 5 then 1 + 2 else 10 }>
  = IfThenElse (LessThan (Num 3) (Num 5)) (Plus (Num 1) (Num 2)) (Num 10).
Proof. reflexivity. Qed.

(**
[eval] is oblivious to the notation - it consumes exactly the same tree.
 *)

Example eval_concrete_if :
  eval <{ if 3 < 5 then 1 + 2 else 10 }> = Some (NumV 3).
Proof. reflexivity. Qed.

Example eval_concrete_type_error :
  eval <{ true + 3 }> = None.
Proof. reflexivity. Qed.

(**
Metavariables of type [ABE] may appear inside the brackets, so laws can
be stated concretely.  Compare with [de_morgan] from Section 6.
 *)

Lemma de_morgan_concrete : forall e1 e2,
  abe_equiv <{ ~ (e1 && e2) }> <{ ~ e1 || ~ e2 }>.
Proof.
  intros e1 e2. unfold abe_equiv. cbn.
  destruct (eval e1) as [ [n1|b1] | ];
  destruct (eval e2) as [ [n2|b2] | ];
  cbn; try reflexivity.
  destruct b1; destruct b2; reflexivity.
Qed.

(** * SUMMARY *)

(**
In this lecture, we:
#<ol>#
#<li>#Extended the language with booleans, comparisons, and conditionals.#</li>#
#<li>#Introduced multiple value types (NumV, BoolV).#</li>#
#<li>#Added error handling with [option Value].#</li>#
#<li>#Proved that well-formed (numeric / boolean) expressions never fail.#</li>#
#<li>#Explored boolean algebra properties, including De Morgan's law.#</li>#
#<li>#Introduced type-consistency reasoning.#</li>#
#<li>#Proved equivalence is reflexive, symmetric, and transitive.#</li>#
#<li>#Added CONCRETE SYNTAX with a notation-based parser covering booleans,
the connectives, comparisons, and the conditional, so that
[<{ if 3 < 5 then 1 + 2 else 10 }>] elaborates to the abstract tree.#</li>#
#</ol>#

Key insight: adding booleans forces us to rethink evaluation.  We can
no longer assume every expression evaluates to a nat - some evaluate
to booleans, and some fail with type errors.

Next: students add type checking to rule out the errors statically.
 *)

(** * NEW PROOF TACTICS IN THIS CHAPTER *)

(**
This chapter reuses the AE toolkit ([intro]/[intros], [reflexivity], [simpl],
[rewrite], [symmetry], [exact], [exists], [discriminate], [induction], [lia],
[unfold], [destruct], and friends).  A few tactics and idioms appear here for
the first time:

#<ul>#
#<li>#[induction] _on a derivation_ - running [induction] on a hypothesis of an inductive predicate ([induction Hnum]), giving one subgoal per rule with induction hypotheses for the recursive premises.#</li>#
#<li>#[destruct (eval e) as [ [n|b] | ]] - a nested pattern that case-splits an [option Value] into [NumV], [BoolV], and [None] in a single step.#</li>#
#<li>#[injection] - use constructor injectivity to turn [C x = C y] into [x = y] (here [Some (NumV n) = Some v] into [NumV n = v]).#</li>#
#<li>#[cbn] - simplify by computation like [simpl], but gentler and more predictable.#</li>#
#<li>#[try t] - attempt tactic [t] and do nothing if it fails; used to clear the easy cases of a large case split ([try reflexivity]).#</li>#
#<li>#[t; [ g1 | g2 | ... ]] - after [t] leaves several goals, run a different tactic on each of them.#</li>#
#</ul>#
 *)
