(**
ABE (Arithmetic + Boolean Expressions) Module
Complete Summary and Organization

This file is documentation only - it contains no Rocq code, just a
guide to the ABE module.  It compiles trivially.
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Complete the AE (Arithmetic Expressions) module first.#</li>#
#<li>#Read plih_abe_lecture.v, sections 1-3, for the core concepts.#</li>#
#<li>#Work through plih_abe_exercises.v, exercises 1-20.#</li>#
#<li>#Check your work against plih_abe_solutions.v.#</li>#
#<li>#Continue with exercises 21-40 and the challenges.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Review plih_abe_instructor_guide.v.#</li>#
#<li>#Prepare three one-hour lectures.#</li>#
#<li>#Assign exercises in increments.#</li>#
#<li>#Grade with plih_abe_solutions.v (Rocq checks correctness for you).#</li>#
#<li>#Move on to the Identifiers section.#</li>#
#</ol>#
 *)

(** * FILE STRUCTURE *)

(**
AE/plih_rocq_ae_shared.v
  Shared AE infrastructure: the option monad (bind, return_, >>=),
  environments, and basic lemmas.  Re-exported by the ABE shared file.

ABE/plih_rocq_abe_shared.v
  - Value type (NumV, BoolV)
  - value_to_nat / value_to_bool, lift_binary_num / _bool / compare
  - ValueType (TNum, TBool) and value_has_type
  - boolean operations (bool_and, bool_or, bool_not)
  - comparison functions (nat_less_than, nat_equal, nat_less_equal)
  - boolean-algebra lemmas (commutativity, De Morgan on bool)

ABE/plih_abe_lecture.v
  - Section 1: Syntax (the ABE inductive type)
  - Section 2: Semantics (eval : ABE -> option Value)
  - Section 3: Classifying expressions (is_numeric, is_boolean)
  - Section 4: Conditionals
  - Section 5: Type consistency (numeric_never_fails, ...)
  - Section 6: Equivalence (abe_equiv) and De Morgan
  - Section 7: Boolean properties
  - Section 8: Comparison properties
  - Section 9: Conditional semantics (lazy evaluation)
  - Section 10: Size metrics
  - Section 11: Concrete syntax - a notation-based parser covering
    booleans, connectives, comparisons, and the conditional, so that
    [<{ if 3 < 5 then 1 + 2 else 10 }>] elaborates to the abstract tree
    (coercion + custom grammar entry, after Software Foundations' Imp)

ABE/plih_abe_exercises.v
  40 exercises + 4 challenges + 4 concrete-syntax exercises, each stated
  with [Admitted] for the student to complete.

ABE/plih_abe_solutions.v
  Complete proofs of every exercise.

ABE/plih_abe_instructor_guide.v
  Teaching notes, lesson plan, common mistakes, assessment.

ABE/plih_abe_summary.v
  This file.
 *)

(** * CONCEPTUAL PROGRESSION *)

(**
AE  (Arithmetic Expressions)
  Syntax: Num, Plus, Minus
  Semantics: eval returns nat; every expression succeeds.

ABE (Arithmetic + Boolean Expressions)   <-- _you are here_
  Syntax: add BTrue, BFalse, And, Or, Not, LessThan, Equal, IfThenElse
  Semantics: eval returns option Value; some expressions fail
  (type errors).  Key insight: well-typed expressions do not fail.

Next (Identifiers): add variables and environments; evaluation can
  also fail because a variable is unbound.

Later (Functions, Typed Functions, State): closures, type checking,
  and mutable state.
 *)

(** * KEY CONCEPTS IN ABE *)

(**
CONCEPT 1: A value type.
  AE evaluated to nat.  ABE evaluates to a Value, which is either a
  number or a boolean:  Value ::= NumV nat | BoolV bool.
 *)

(**
CONCEPT 2: Error handling with option.
  eval : ABE -> option Value.
    None    means a type error (e.g. eval (Plus BTrue (Num 3))).
    Some v  means successful evaluation to value v.
  Proof technique: case-split on the option, e.g.
    destruct (eval e) as [v | ].
 *)

(**
CONCEPT 3: Type classifiers (is_numeric, is_boolean).
  numeric_never_fails : is_numeric e -> exists n, eval e = Some (NumV n)
  boolean_never_fails : is_boolean e -> exists b, eval e = Some (BoolV b)
  Meaning: a well-formed numeric/boolean expression never errors.
  This previews formal type checking in later chapters.
 *)

(**
CONCEPT 4: De Morgan's laws hold for our evaluator, _including_ the
  error cases:
    abe_equiv (Not (And e1 e2)) (Or (Not e1) (Not e2))
    abe_equiv (Not (Or  e1 e2)) (And (Not e1) (Not e2))
  The proof is a careful case analysis on the values (and the error
  cases) of the operands.
 *)

(**
CONCEPT 5: Lazy / short-path conditionals.
    eval (IfThenElse BFalse (Plus BTrue (Num 1)) (Num 42))
      = Some (NumV 42)
  The then-branch is a type error, but it is never evaluated because
  the condition is false.  Only the taken branch is evaluated.
 *)

(**
CONCEPT 6: Type-checking changes which identities hold.
  In an _untyped_ setting one expects "And BTrue e = e".  Here that is
  false in general: if [e] evaluates to a number, [And BTrue e] is a
  type error (None) while [e] is not.  The true statements therefore
  carry a hypothesis such as [eval e = Some (BoolV b)].  The same
  subtlety makes naive double-negation elimination unsound (see
  exercise 38).
 *)

(** * KEY PROOF PATTERNS IN ABE (ROCQ TACTICS) *)

(**
PATTERN 1: Closed computations (exercises 1-17, 26-27).
  The goal is a concrete equation, so it holds by computation:
    Proof. reflexivity. Qed.
 *)

(**
PATTERN 2: Disjunctions for error handling (exercise 9).
  Case-split on the operands and pick the branch:
    simpl.
    destruct (eval e1) as [ [n1|b1] | ];
    destruct (eval e2) as [ [n2|b2] | ];
      try (left; reflexivity).
    right. exists n1, n2. reflexivity.
 *)

(**
PATTERN 3: Case analysis on booleans (exercises 18-22).
    intros e1 e2. simpl.
    destruct (eval e1) as [ [n1|b1] | ];
    destruct (eval e2) as [ [n2|b2] | ];
      try reflexivity.
    destruct b1; destruct b2; reflexivity.
 *)

(**
PATTERN 4: Type-consistency proofs (exercises 28-30).
  Induct on the is_numeric / is_boolean derivation, using the
  induction hypotheses for sub-expressions:
    intros e Hnum. induction Hnum.
    - exists n. reflexivity.
    - destruct IHHnum1 as [n1 H1]. destruct IHHnum2 as [n2 H2].
      exists (n1 + n2). simpl. rewrite H1, H2. reflexivity.
    ...
 *)

(**
PATTERN 5: De Morgan (exercises 34-35).
  Unfold abe_equiv, normalize with cbn, then case-split on the
  operand values; the only interesting case is bool/bool:
    unfold abe_equiv. cbn.
    destruct (eval e1) as [ [n1|b1] | ];
    destruct (eval e2) as [ [n2|b2] | ]; cbn; try reflexivity.
    destruct b1; destruct b2; reflexivity.
 *)

(** * TIPS FOR SUCCESS *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Read the lecture before attempting the exercises.#</li>#
#<li>#Understand _when_ and _why_ evaluation returns None.#</li>#
#<li>#Use case analysis liberally: destruct (eval e), destruct b.#</li>#
#<li>#Study the De Morgan proof; that pattern recurs throughout logic.#</li>#
#<li>#Ask for help early rather than grinding on one proof.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Emphasize the key insight: type checking prevents errors.#</li>#
#<li>#Contrast with AE, where every expression succeeds.#</li>#
#<li>#Do live proofs; let students watch the case analysis unfold.#</li>#
#<li>#Highlight where type-checking breaks untyped intuitions (And BTrue e, double negation): these motivate static typing.#</li>#
#</ol>#
 *)

(** * SUMMARY *)

(**
ABE bridges simple interpreters (AE) and type-safe languages.

Learning outcomes:
  - Multiple value types (NumV, BoolV)
  - Error handling with option
  - Type consistency and safety
  - Boolean algebra and logical operations
  - Conditional evaluation and laziness
  - Proof patterns for option / disjunction case analysis

Next: identifiers and environments, then functions, types, and state.
 *)
