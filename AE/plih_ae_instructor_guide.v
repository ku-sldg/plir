(**
INSTRUCTOR GUIDE: Teaching the AE Section

Documentation only - no Rocq code.  Compiles trivially.

This guide covers: course structure, what to emphasize, common
student mistakes, time estimates, and extensions.
 *)

(** * PART 1: COURSE STRUCTURE *)

(**
WEEK 1 - Rocq basics (prerequisite).  Before AE, students need:

  1. Inductive types.  AE is like a Haskell data type; Num n and
     Plus e1 e2 are CONSTRUCTORS (values, not programs).
  2. Pattern matching via Fixpoint.  Like Haskell, but Rocq
     requires structural recursion - eval MUST terminate.
  3. Basic tactics: intro, reflexivity, simpl (unfold/compute),
     lia (linear arithmetic).

Warm-up examples to demo:
  eval (Num 5) = 5                      (* reflexivity *)
 *   eval (Plus (Num 2) (Num 3)) = 5       (* reflexivity *)
 *   eval (Plus e1 e2) = eval e1 + eval e2 (* simpl; reflexivity *)
 *)

(** * PART 2: LESSON PLAN (one week) *)

(**
HOUR 1 - Defining the language.
  Objectives: abstract syntax; inductive definitions; syntax vs
  semantics.
  Activities: draw ASTs for 3+4, (1+2)+3, 10-2; write the Rocq
  terms; show an ill-formed term (Plus (Num 3) is missing an
  argument).  Compare to Haskell:
    Haskell: data AE = Num Int | Plus AE AE | Minus AE AE
    Rocq:    Inductive AE : Type := Num : nat -> AE | ...

HOUR 2 - Evaluation (semantics).
  Objectives: write an interpreter; understand Fixpoint and
  termination; test the evaluator.
  Activities: trace eval by hand; explain why Rocq requires
  termination; let Rocq compute the examples.

HOUR 3 - Simple proofs.
  Objectives: prove by reflexivity; use simpl and lia.
  Activities: direct proofs (exercises 1-7: unfold then
  reflexivity); commutativity of Plus (exercise 8: simpl reduces
  the goal to eval e1 + eval e2 = eval e2 + eval e1, which lia
  closes via Nat.add_comm).
  Tip: simpl to unfold, then lia.

HOUR 4 - Induction.
  Objectives: structural induction on AE.
  Activities: prove "0 <= eval e" on paper (base case Num n;
  inductive cases Plus / Minus use the IH), then in Rocq with
  [induction e as [n | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2]].
  Common mistake: forgetting to use the IH - lia only sees it if
  it is a hypothesis in context.

HOUR 5 - Optimization and open problems.
  Objectives: prove optimization correctness; work with helpers.
  Activities: study optimize_zero; case-split on the subexpression
  in the Plus case; discuss when an optimization is valid.  Then
  have students attempt constant folding (exercise 30).

Total: ~3 hours instruction + ~2 hours problem solving.
 *)

(** * PART 3: COMMON STUDENT MISTAKES *)

(**
MISTAKE 1: Confusing syntax and semantics.  Students try to prove
  [forall e, Plus e (Num 0) = e] (syntactic equality of ASTs),
  which is false.  The intended claim is semantic:
  [eval (Plus e (Num 0)) = eval e].

MISTAKE 2: Forgetting the induction hypothesis.  After
  [induction e], lia cannot close the Plus/Minus cases unless the
  IH (IHe1 / IHe2) is in context and relevant.

MISTAKE 3: Destructing the wrong term.  For optimization proofs,
  case-split on the subexpression the function matches on, not on
  the whole expression.

MISTAKE 4: Not simplifying.  Many goals need [simpl] before [lia]
  or [reflexivity] can make progress.

MISTAKE 5: Confusing = with <->.  [eval e1 = eval e2] (semantic
  equivalence) is NOT [e1 = e2] (syntactic equality).
 *)

(** * PART 4: PEDAGOGICAL TIPS *)

(**
TIP 1: Use Rocq tactics consistently.  This course is in the Rocq
  Prover, so use Rocq/Coq tactics throughout - simpl, rewrite,
  destruct, induction, reflexivity, lia - and finish unsolved
  goals with [Admitted] (never Lean's [sorry]) and proofs with
  [Qed].  Avoid Lean syntax such as [simp [..]], [rw [..]],
  [cases], or the centered-dot bullet.

TIP 2: Examples before lemmas.  Show concrete computations first:
    Example test_1 : eval (Num 5) = 5.
    Proof. reflexivity. Qed.
  before asking for the general lemma.

TIP 3: Trace by hand.  Evaluate on paper, e.g.
    eval (Plus (Plus (Num 1) (Num 2)) (Num 3))
      = (1 + 2) + 3 = 6
  then show that [simpl] does exactly this.

TIP 4: Emphasize modular proofs - later lemmas reuse earlier ones.

TIP 5: Keep a tactics cheat sheet handy:
    intro x / intros x y z  -- introduce variables
    simpl                   -- simplify / compute
    reflexivity             -- close a computed equality
    lia                     -- linear arithmetic
    induction e             -- structural induction
    destruct e              -- case analysis
    rewrite H               -- rewrite with an equation
    assert (H : P)          -- introduce an intermediate result
 *)

(** * PART 5: ASSESSMENT RUBRIC *)

(**
Suggested grading for the exercise set:
  Exercises 1-10  (basic):        simple tactics only.
  Exercises 11-20 (standard):     require induction.
  Exercises 21-29 (intermediate): multi-step proofs.
  Exercises 30-31 (advanced):     independent problem solving.
  Challenges: optional bonus.

Rubric: compilation with no remaining [Admitted] (most of the
grade), correctness of the stated claim, and clarity / structure.
 *)

(** * PART 6: EXTENSIONS & VARIANTS *)

(**
VARIANT 1: Error handling - add division and make eval return
  [option nat] to handle division by zero.
VARIANT 2: Add booleans early - this is exactly the ABE chapter.
VARIANT 3: Static analysis - define a predicate [safe : AE -> Prop]
  (e.g. "no division by zero") and prove safe expressions never err.
VARIANT 4: More optimizations - (e + 0) ~> e, ((e1+e2)+e3) ~>
  (e1+(e2+e3)) - and prove composing them preserves semantics.
VARIANT 5: Equivalence classes - explore ae_equiv as an
  equivalence relation that partitions AE.
 *)

(** * PART 7: TRANSITION TO ABE *)

(**
After AE, introduce ABE (Arithmetic + Booleans).  Key changes:
  1. Multiple result types: AE evaluates to nat; ABE evaluates to a
     Value (NumV nat | BoolV bool).
  2. Type-mismatch errors: (3 + True) is well-formed syntax but
     semantic nonsense, so eval returns option Value (None = error).
  3. New properties: type consistency ("well-formed expressions do
     not fail") and error analysis.
  4. Optimization gets subtler: a type discipline changes which
     equivalences hold (see the ABE notes).
 *)

(** * PART 8: RESOURCES *)

(**
- The Rocq Prover reference manual: https://rocq-prover.org/doc/
- "Software Foundations" (PL pedagogy + Coq/Rocq proofs)
- Harper, "Practical Foundations for Programming Languages"
- Pierce, "Types and Programming Languages"
- PLIH (the Haskell original): https://ku-sldg.github.io/plih/
  Same progression; the Rocq port adds proofs at each step.
 *)

(** * SUMMARY *)

(**
The AE section teaches:
  1. SYNTAX - defining a language with an inductive type.
  2. SEMANTICS - specifying meaning with a Fixpoint interpreter.
  3. PROOF - verifying properties with Rocq tactics.
  4. PRACTICE - applying these ideas across 31 exercises.

It prepares students for booleans (ABE), identifiers, functions,
types, and state.
 *)
