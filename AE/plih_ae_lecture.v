(**
Programming Languages in Rocq - AE Lecture
Arithmetic Expressions

This lecture covers:
- Defining a simple language of arithmetic expressions
- Writing an interpreter for the language
- Proving basic properties about the interpreter

This mirrors the first section of PLIH but with added proofs.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import plih_rocq_ae_shared.

(** * SECTION 1: SYNTAX - Defining the Language *)

(**
An arithmetic expression (AE) is one of:
  - A number (literal)
  - The sum of two expressions
  - The difference of two expressions
*)

Inductive AE : Type :=
| Num : nat -> AE
| Plus : AE -> AE -> AE
| Minus : AE -> AE -> AE.

(**
This is an abstract syntax tree (AST). We will implement concrete syntax and a
parser later in this lesson.
*)

(**
** From an English expression to abstract syntax

How do we turn an ordinary arithmetic expression, written the way you would
say it out loud, into an [AE] value? We translate it recursively, working
from the _outside in_:

  - Find the _outermost_ operation - the one that is performed _last_ when you
    evaluate the expression by hand. Ordinary precedence and parentheses
    tell you which one that is.
  - Choose the constructor for that operation: a sum becomes [Plus], a
    difference becomes [Minus], and a bare number becomes [Num n].
  - The operands of that operation become the constructor's two arguments.
    Repeat these steps on each operand until every piece is a plain number.

Worked example - "one plus the quantity two plus three", i.e. [1 + (2 + 3)]:

  - The outermost operation is the _first_ [+] (the parentheses force
    [2 + 3] to happen first, so the leftmost [+] is performed last).
    That gives [Plus _ _].
  - Its left operand is [1], a bare number: [Num 1].
  - Its right operand is [2 + 3]. Recurse: the outermost operation there is
    [+], giving [Plus _ _], with operands [2] and [3] becoming [Num 2] and
    [Num 3]. So [2 + 3] translates to [Plus (Num 2) (Num 3)].
  - Assembling: [Plus (Num 1) (Plus (Num 2) (Num 3))], which is
    [ae_example_4] below.

Notice that the parenthesis disappear. The shape of the tree records
the grouping. Writing [(1 + 2) + 3] instead would make the second [+] the
outermost operation and yield a different tree,
[Plus (Plus (Num 1) (Num 2)) (Num 3)]. Abstract syntax is unambiguous for
exactly this reason - there is nothing left to parenthesize. (Turning the
English text back _into_ a tree, precedence and all, is the job of the parser
we write later; here we simply build the trees by hand.)
*)

(**
Examples of AE terms (these are VALUES of type AE):
 *)

Definition ae_example_1 : AE := Num 5. (* 5 *)
Definition ae_example_2 : AE := Plus (Num 3) (Num 4). (* 3+4 *)
Definition ae_example_3 : AE := Minus (Num 10) (Num 2). (* 10-2 *)
Definition ae_example_4 : AE := Plus (Num 1) (Plus (Num 2) (Num 3)). (* 1+(2+3) *)

(**
** How [Definition] works

[Definition] introduces a new named constant. Every definition above follows
the same three-part shape:

    Definition name : type := value.

read as "let [name], of type [type], stand for [value]." Each part has a job:

  - [name] is the fresh identifier you are introducing. After this command it
    is available everywhere below as a permanent, global binding.
  - [: type] is a type ascription. Rocq checks that [value] really does have
    this type and rejects the definition otherwise, so the annotation doubles
    as a machine-checked claim about [value]. In [ae_example_2 : AE := ...]
    it promises the value is an [AE]. The ascription is _optional_ - Rocq can
    usually infer the type from [value] - but writing it documents intent and
    catches mistakes early.
  - [:= value] is the defining term. It is type-checked once, now, against
    [type]; from then on [name] is just another way of writing it.
  - The closing period ends the command and tells Rocq to process it.

Definitions are _transparent_: [name] and [value] are interchangeable, and Rocq
may _unfold_ [name] back into [value] during computation. That is why a later
proof can compute straight through a definition - e.g. [eval ae_example_2]
reduces by first replacing [ae_example_2] with [Plus (Num 3) (Num 4)]. A
[Definition] is therefore not a copy or a runtime variable; it is a name for a
term that Rocq can always see inside.

Note that [Definition] cannot be used to define recursive constructions: the
[value] may not refer to [name] itself, because the name is not yet in scope
while its own defining term is being checked. Self-reference needs the
structural-recursion machinery of [Fixpoint] - which is exactly why [eval]
below is a [Fixpoint] and not a [Definition].
*)

(** * SECTION 2: SEMANTICS - Defining Evaluation *)

(**
Now we define what these expressions mean by writing an interpreter.

The [eval] function maps an AE to a natural number (its value).

Rocq requires that [eval] be total (terminates on all inputs).
This is enforced requiring structural recursion on the AE argument.
*)

Fixpoint eval (e : AE) : nat :=
  match e with
  | Num x => x
  | Plus x y => eval x + eval y
  | Minus x y => eval x - eval y
  end.

(**
Let's test eval on our examples
*)

Example test_eval_1 : eval (Num 5) = 5.
Proof. reflexivity. Qed.

Example test_eval_2 : eval (Plus (Num 3) (Num 4)) = 7.
Proof. reflexivity. Qed.

Example test_eval_3 : eval (Minus (Num 10) (Num 2)) = 8.
Proof. reflexivity. Qed.

Example test_eval_4 : eval (Plus (Num 1) (Plus (Num 2) (Num 3))) = 6.
Proof. reflexivity. Qed.

(**
Each [Example] defines a proof that looks and behaves a great deal like a test
case.  [test_eval_1] is defined as [eval (Num 5) = 5] meaning exactly what you
would think.  Evaluating [(Num 5)] should equal [5].  The period creates a goal
that must be discharged.

[Proof] tells Rocq to open a proof and [reflexivity] is our first proof tactic.
[reflexivity] simplifies both sides of the equality and determines if they are
identical. If they are the goal is discharged and [Qed] ends the proof.  If they
are not, nothing changes and a different path must be chosen.

Periods are important.  They tell the Rocq system to evaluate the tactic or
preceding definition.
*)

(** * SECTION 3: SIMPLE PROPERTIES *)

(**
Now we begin proving properties about eval.
This is what differentiates Rocq from Haskell: we can prove
that our interpreter has certain desirable properties.
 *)

(** PROPERTY 1: Evaluation is deterministic

If we evaluate the same expression twice, we get the same result. This is obvious from the definition, but let's prove it formally.
 *)

Lemma eval_deterministic : forall e,
  eval e = eval e.
Proof.
  intro e.
  reflexivity.
Qed.

(** This is too trivial! Let's prove something more interesting. *)

(** PROPERTY 2: Eval distributes over Plus

This is obvious from the definition, but it's good practice.
 *)

Lemma eval_plus : forall e1 e2,
  eval (Plus e1 e2) = eval e1 + eval e2.
Proof.
  intro e1.
  intro e2.
  (* After simplifying, this is just: eval e1 + eval e2 = eval e1 + eval e2 *)
  reflexivity.
Qed.

(** PROPERTY 3: Plus is commutative on AE

[eval (Plus e1 e2) = eval (Plus e2 e1)]

Why? Because addition of natural numbers is commutative.
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

(** PROPERTY 4: Plus is associative on AE *)

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

(** PROPERTY 5: Minus is not commutative (obviously) *)

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

(** PROPERTY 6: Every AE evaluates to some natural number

This is TRIVIAL because eval always produces a nat, but it's good to state explicitly.
 *)

Lemma eval_produces_nat : forall e,
  exists n, eval e = n.
Proof.
  intro e.
  exists (eval e).
  reflexivity.
Qed.

(** * SECTION 4: INDUCTION OVER AE *)

(**
The real power of formal verification comes when we use induction.
Since AE is inductively defined, we can prove properties * induction over its structure.
 *)

(** PROPERTY 7: Multiplication distributes over addition

For any k: k * (e1 + e2) = k * e1 + k * e2
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

(** PROPERTY 8: Zero is identity for addition

For any e: eval (Plus (Num 0) e) = eval e
 *)

Lemma zero_plus_identity : forall e,
  eval (Plus (Num 0) e) = eval e.
Proof.
  intro e.
  reflexivity.
Qed.

(** PROPERTY 9: Every AE is >= 0 (when interpreted)

 This uses induction on the structure of AE.
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

(** * SECTION 5: AUXILIARY FUNCTIONS AND THEIR PROPERTIES *)

(**
Often we want helper functions to manipulate AE terms.
Let's prove properties about these helpers.
 *)

(** Helper: Count the number of operations in an AE *)

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


(** * SECTION 6: EQUIVALENCE OF EXPRESSIONS *)

(**
Two expressions are semantically equivalent if they evaluate to
the same value.
 *)

Definition ae_equiv (e1 e2 : AE) : Prop := eval e1 = eval e2.

(** Show that equivalence is an equivalence relation *)

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

(** * SECTION 7: PROVING INEQUALITIES *)

(**
Sometimes we need to prove that one expression evaluates to
more or less than another.
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

(** * SECTION 8: OPTIMIZATIONS AND CORRECTNESS PROOFS *)

(**
A common task is to prove that an "optimized" version of
an interpreter is correct.
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

(** * SECTION 9: REFLECTION / DECISION PROCEDURES *)

(**
Sometimes we want to decide properties computationally
and then verify the decision.
 *)

(* Decide if two AE expressions are syntactically identical *)

Fixpoint ae_eq_dec (e1 e2 : AE) : bool :=
  match e1,e2 with
  | Num x, Num y => eqb x y
  | Plus x1 y1, Plus x2 y2 => andb (ae_eq_dec x1 x2) (ae_eq_dec y1 y2)
  | Minus x1 y1, Minus x2 y2 => andb (ae_eq_dec x1 x2) (ae_eq_dec y1 y2)
  | _,_ => false
  end.
                       
(** Prove that the decision procedure is correct *)

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

(** * SECTION 10: CONCRETE SYNTAX - A NOTATION PARSER *)

(**
Every AE term so far has been written in ABSTRACT syntax - the raw
constructors [Num], [Plus], [Minus].  That is precise but verbose:
[Plus (Num 1) (Plus (Num 2) (Num 3))] is a mouthful for "1 + (2 + 3)".
Section 1 even warned that we were "NOT implementing parsing from
text".  We can now lift that restriction.

Following Software Foundations' treatment of Imp, we give AE a layer of
CONCRETE syntax so that

  <{ 1 + (2 + 3) }>

parses directly into the abstract tree [Plus (Num 1) (Plus (Num 2)
(Num 3))].  The parser is built entirely from Rocq NOTATIONS - there is
no separate lexer or parser generator, and the whole thing elaborates
away, so a concrete term is DEFINITIONALLY EQUAL to the abstract tree
it denotes.  Three ingredients do the work.
 *)

(**
INGREDIENT 1 - a COERCION from [nat] to [AE].  Inside concrete syntax a
bare numeral like [3] should stand for [Num 3].  A coercion tells Rocq
to insert [Num] automatically wherever an [AE] is expected but a [nat]
is supplied.
 *)

Coercion Num : nat >-> AE.

(**
INGREDIENT 2 - a private GRAMMAR ENTRY.  [<{ ... }>] switches Rocq's
parser into a custom grammar called [ae] in which we control precedence
and associativity.  Ordinary Rocq syntax (including [nat] [+] and [-])
is left untouched OUTSIDE the brackets.
 *)

Declare Custom Entry ae.
Declare Scope ae_scope.
Delimit Scope ae_scope with ae.

(**
The entry needs three structural notations: the [<{ }>] delimiters that
open it, grouping parentheses, and an "escape hatch" that drops back to
an ordinary Rocq term (this is what lets numerals and [AE] variables
appear inside the brackets).
 *)

Notation "<{ e }>" := e (e custom ae at level 99) : ae_scope.
Notation "( x )" := x (in custom ae, x at level 99) : ae_scope.
Notation "x" := x (in custom ae at level 0, x constr at level 0) : ae_scope.

(**
INGREDIENT 3 - one notation per operator, each carrying its precedence.
[+] and [-] are left-associative at the same level, matching the way we
read the surface language.
 *)

Notation "x + y" := (Plus x y)  (in custom ae at level 50, left associativity) : ae_scope.
Notation "x - y" := (Minus x y) (in custom ae at level 50, left associativity) : ae_scope.

Open Scope ae_scope.

(**
That is the entire "parser".  Because the notation is just sugar, every
example below is proved by [reflexivity]: the concrete form and the
abstract tree are the same term.
 *)

Example parse_plus : <{ 3 + 4 }> = Plus (Num 3) (Num 4).
Proof. reflexivity. Qed.

Example parse_minus : <{ 10 - 2 }> = Minus (Num 10) (Num 2).
Proof. reflexivity. Qed.

(* Left-associativity: [1 + 2 + 3] groups as [(1 + 2) + 3]. *)
Example parse_assoc : <{ 1 + 2 + 3 }> = Plus (Plus (Num 1) (Num 2)) (Num 3).
Proof. reflexivity. Qed.

(* Parentheses override the default grouping. *)
Example parse_paren : <{ 1 + (2 + 3) }> = Plus (Num 1) (Plus (Num 2) (Num 3)).
Proof. reflexivity. Qed.

(* The examples from Section 1, now written concretely. *)
Example ae_example_2_concrete : <{ 3 + 4 }> = ae_example_2.
Proof. reflexivity. Qed.

Example ae_example_4_concrete : <{ 1 + (2 + 3) }> = ae_example_4.
Proof. reflexivity. Qed.

(**
[eval] is oblivious to the notation - it consumes exactly the same tree
whether we wrote it abstractly or concretely.
 *)

Example eval_concrete_1 : eval <{ 3 + 4 }> = 7.
Proof. reflexivity. Qed.

Example eval_concrete_2 : eval <{ (10 - 2) + 5 }> = 13.
Proof. reflexivity. Qed.

(**
Metavariables of type [AE] may appear inside the brackets too, so we
can even state general laws in concrete syntax.  Compare with
[plus_commutative] from Section 3.
 *)

Lemma plus_commutative_concrete : forall e1 e2,
  eval <{ e1 + e2 }> = eval <{ e2 + e1 }>.
Proof.
  intros e1 e2.
  simpl.
  apply Nat.add_comm.
Qed.

(** * SUMMARY *)

(**
In this lecture, we:

#<ol>#
#<li>#Defined a simple language (AE) using an inductive datatype#</li>#
#<li>#Wrote an interpreter ([eval]) that is guaranteed to terminate#</li>#
#<li>#Proved basic properties:
#<ul>#
#<li>#Commutativity of plus#</li>#
#<li>#Associativity of plus#</li>#
#<li>#Non-negativity of evaluation#</li>#
#</ul>#
#</li>#
#<li>#Proved correctness of optimizations#</li>#
#<li>#Proved correctness of decision procedures#</li>#
#<li>#Added CONCRETE SYNTAX with a notation-based parser, so that [<{ 1 + (2 + 3) }>] elaborates to the abstract AE tree#</li>#
#</ol>#

Key insight: By formalizing our language and interpreter in Rocq,
we can prove properties that would be difficult or impossible
to verify in Haskell alone.

Next: We'll add booleans, error handling, and environments.
 *)
