(**
INSTRUCTOR GUIDE: Teaching the ABE Section
Arithmetic + Boolean Expressions

Documentation only - no Rocq code.  Compiles trivially.

ABE is more involved than AE because it introduces:
#<ol>#
#<li>#Multiple value types#</li>#
#<li>#Error handling with option#</li>#
#<li>#Type-consistency reasoning#</li>#
#<li>#Conditional evaluation#</li>#
#</ol>#
 *)

(** * PART 1: KEY DIFFERENCES FROM AE *)

(**
AE was simple: every expression evaluated to a nat.
ABE is more realistic: multiple types plus error handling.

Conceptual shifts:
#<ol>#
#<li>#From "every expression succeeds" to "some expressions fail with a type error": in AE [eval (Num 5) = 5], but in ABE [eval (Num 5) = Some (NumV 5)] and [eval (Plus BTrue (Num 3)) = None] (a type error).#</li>#
#<li>#From a single result type ([nat]) to a value type with several alternatives: [Value ::= NumV nat | BoolV bool].#</li>#
#</ol>#
 *)

(** * PART 2: THREE-HOUR LESSON PLAN *)

(**
HOUR 1 - Motivation and multiple values.
  Objectives: why ABE extends AE; the Value type; option for errors.
  Strategy:
    - Pose the problem: "AE has only numbers.  What about True?
      What about (3 + True)?"
    - Introduce Value (NumV / BoolV).
    - Introduce option Value: None is a type error.
  Assign: exercises 1-8.

HOUR 2 - Boolean operations and conditionals.
  Objectives: boolean operators, comparisons, conditionals.
  Strategy:
    - And / Or / Not require boolean operands:
        eval (And BTrue BFalse) = Some (BoolV false)
        eval (And (Num 3) BTrue) = None        (* type error *)
    - Comparisons take numbers, produce booleans:
        eval (LessThan (Num 3) (Num 5)) = Some (BoolV true)
    - Conditionals need a boolean condition:
        eval (IfThenElse (LessThan (Num 3) (Num 5)) (Num 10) (Num 20))
          = Some (NumV 10)
        eval (IfThenElse (Num 3) e1 e2) = None  (* condition not bool *)
    - Lazy evaluation: only the taken branch is evaluated, so
        eval (IfThenElse BFalse (Plus BTrue (Num 1)) (Num 42))
          = Some (NumV 42)
  Assign: exercises 9-25.

HOUR 3 - Type consistency and proof patterns.
  Objectives: is_numeric / is_boolean; "well-typed expressions do not
  error"; connection to formal type checking.
  Strategy:
    - Define the predicates, then prove numeric_never_fails and
      boolean_never_fails by induction on the derivation.
    - Stress that this is the seed of a type-soundness theorem.
  Assign: exercises 26-40 and the challenges.

HOUR 4 - Concrete syntax (Section 11).
  Objectives: distinguish concrete from abstract syntax; build a parser
  from Rocq notations alone; understand _precedence_ and associativity.
  Strategy:
    - Reuse the AE recipe (coercion + custom entry) but note the larger
      grammar: [true]/[false] keywords, [+ - < = ~ && ||] and
      [if _ then _ else _].
    - Draw the precedence ladder (arithmetic 50 < comparison 70 < ~ 75
      < && 80 < || 85 < if 89); higher level = looser binding.  Work
      [1 + 2 < 4] and [a || b && c] by hand, then confirm by
      [reflexivity].
    - Emphasize [<{ e }>] and its abstract tree are the _same_ term, so
      [eval] is unchanged.
  Common mistake: expecting an operator with no notation to parse
  inside [<{ }>]; only the operators above are in the grammar.
  Assign: exercises 41-44.
 *)

(** * PART 3: COMMON STUDENT MISTAKES *)

(**
MISTAKE 1: Forgetting to case-split on option.
  When reasoning about [eval (Plus e1 e2)], students forget that
  [eval e1] might be None or might be a boolean.  Fix: always
  [destruct (eval e1) as [ [n|b] | ]] to expose every case.

MISTAKE 2: Confusing syntax (ABE) with values (Value).
  [eval] maps an ABE to an [option Value]; it does not return an ABE.
  A claim like [forall v, eval v = v] is ill-typed.

MISTAKE 3: Expecting untyped identities to hold.
  "And BTrue e = e" is _false_ when [e] is numeric.  The correct lemma
  assumes [eval e = Some (BoolV b)].  Use this to motivate typing.

MISTAKE 4: Trying [lia] on goals with unresolved option cases.
  [lia] cannot see through [match eval e with ...].  Case-split
  first, then finish each branch.

MISTAKE 5: Attacking De Morgan without case analysis.
  [reflexivity] alone will not work; the proof needs a case split on
  the operand values (and the error cases) followed by
  [destruct b1; destruct b2; reflexivity].
 *)

(** * PART 4: ASSESSMENT & GRADING *)

(**
Because Rocq checks correctness mechanically, grading is fast:
#<ol>#
#<li>#Run the build (see the project README / _CoqProject).#</li>#
#<li>#Confirm there are no remaining [Admitted] (Rocq warns on each).#</li>#
#<li>#Spot-check a few proofs for clarity and good naming.#</li>#
#</ol>#

A suggested rubric:
  - Compilation, no Admitted (50%)
  - Correctness of statements / no weakening of claims (30%)
  - Clarity and structure (20%)
 *)

(** * PART 5: EXTENSIONS & VARIANTS *)

(**
VARIANT 1: More comparison operators (GreaterThan, LessEqual, ...)
  and prove relationships among them.

VARIANT 2: A third value kind, e.g. StringV, extending Value and eval.

VARIANT 3: Short-circuit semantics for And/Or, and prove the
  short-circuit lemma _without_ the extra "e2 is a boolean" hypothesis
  that the current (eager) semantics requires.  A great way to show
  how semantics choices change which theorems hold.

VARIANT 4: A fuller boolean algebra: associativity, idempotence,
  absorption, in addition to commutativity and De Morgan.
 *)

(** * PART 6: TRANSITION TO IDENTIFIERS *)

(**
After ABE, students are ready for identifiers:
  - Variables have values stored in an environment.
  - Looking up an unbound variable is a new way to fail.
  - Evaluation now depends on a context (the environment).

The proof techniques carry over: case analysis on option, plus
environment lemmas (lookup / extend) from the AE shared library.
 *)

(** * PART 7: TACTICS USED IN THIS SECTION (ROCQ) *)

(**
- reflexivity / simpl / cbn : compute and discharge closed goals.
- destruct (eval e) as [ [n|b] | ] : case-split an [option Value]
    into NumV, BoolV, and None.
- destruct b : case-split a boolean into true / false.
- rewrite H : use an evaluation hypothesis to rewrite the goal.
- induction Hnum / induction e : structural / derivation induction.
- exists / left / right : drive existentials and disjunctions.
- lia : close linear arithmetic goals (size / count lemmas).

Proof structure uses the bullets - + * (not Lean's centered dot),
and unfinished proofs use [Admitted] (not Lean's [sorry]).
 *)

(** * SUMMARY *)

(**
ABE is the chapter where students learn:
#<ol>#
#<li>#Multiple value types - not everything is a number.#</li>#
#<li>#Error handling with option.#</li>#
#<li>#Type consistency: well-formed expressions do not fail.#</li>#
#<li>#How a type discipline changes which equivalences hold.#</li>#
#</ol>#

It is the bridge from simple interpreters to type-safe languages.
 *)
