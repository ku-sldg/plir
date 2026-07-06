(**
PLIH in Rocq: AE (Arithmetic Expressions) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in AE/):
#<ol>#
#<li>#plih_rocq_ae_shared.v      -- shared infrastructure#</li>#
#<li>#plih_ae_lecture.v          -- lecture with worked examples#</li>#
#<li>#plih_ae_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_ae_solutions.v        -- complete solutions#</li>#
#<li>#plih_ae_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_ae_summary.v          -- this file#</li>#
#</ol>#
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Read plih_ae_lecture.v for concepts and worked examples.#</li>#
#<li>#Work through plih_ae_exercises.v, replacing each [Admitted] with a real proof ending in [Qed].#</li>#
#<li>#Check your work against plih_ae_solutions.v.#</li>#
#<li>#Build with [make] at the repo root to confirm everything compiles.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_ae_instructor_guide.v for teaching strategies.#</li>#
#<li>#Assign plih_ae_exercises.v in weekly increments.#</li>#
#<li>#Grade with plih_ae_solutions.v (Rocq checks correctness).#</li>#
#<li>#Adapt the lecture examples to your class style.#</li>#
#</ol>#
 *)

(** * MODULE STRUCTURE *)

(**
LAYER 1: Foundations (plih_rocq_ae_shared.v)
  - option monad (bind, return_, liftM2) and the monad laws
  - environment operations (lookup, extend) and their lemmas
  USE: imported (re-exported) by the other files.

LAYER 2: Lecture (plih_ae_lecture.v)
  Section 1: Syntax (Inductive AE: Num, Plus, Minus)
  Section 2: Semantics (Fixpoint eval, termination)
  Section 3: Simple properties (determinism, distribution,
             commutativity / associativity of Plus)
  Section 4: Induction (distribution of *, zero identity,
             non-negativity)
  Section 5: Auxiliary functions (count_ops) and their properties
  Section 6: Equivalence (ae_equiv: refl / sym / trans)
  Section 7: Inequalities
  Section 8: Optimization (optimize_zero) and its correctness
  Section 9: Decidability (ae_eq_dec) and its correctness
  Section 10: Concrete syntax - a notation-based parser so that
              [<{ 1 + (2 + 3) }>] elaborates to the abstract AE tree
              (coercion + custom grammar entry, after Software
              Foundations' Imp)

LAYER 3: Exercises (plih_ae_exercises.v)
  31 exercises + 2 challenges + 4 concrete-syntax exercises, graduated
  in difficulty, each an [Admitted] stub for the student to complete.
  Helper functions (size, depth, optimize, fold_constants, simplify)
  are provided.

LAYER 4: Solutions (plih_ae_solutions.v)
  Complete proofs for every exercise and challenge.  Solutions are
  not unique: a proof is correct if it has no [Admitted] and
  compiles.

LAYER 5: Instructor guide (plih_ae_instructor_guide.v)
  Course structure, lesson plan, common mistakes, assessment
  rubric, extensions, and the transition to ABE.
 *)

(** * SUGGESTED WEEKLY SCHEDULE *)

(**
WEEK 1 (prerequisite): Rocq basics - inductive types, pattern
  matching, and the tactics intro / reflexivity / simpl / lia.

WEEK 2: AE
  Mon: syntax + semantics; assign exercises 1-5.
  Wed: simple proofs; assign exercises 6-12.
  Fri: induction (live-prove eval_nonneg); assign exercises 13-21.

WEEK 3: AE continued
  Mon: review hard exercises.
  Wed: optimization + correctness; assign exercises 22-31 and the
       challenges.
  Fri: discussion / optional presentations.

Then proceed to ABE (Arithmetic + Boolean Expressions).
 *)

(** * KEY CONCEPTS TESTED BY EXERCISES *)

(**
Exercises 1-5  (warm-up):   what eval does; proof by reflexivity.
Exercises 6-8  (lemmas):    simpl to unfold, lia for arithmetic.
Exercises 9-15 (induction): structural induction on AE, using the
                            induction hypotheses for subterms.
Exercises 16-20 (ineq.):    reasoning with <, >, >= via lia.
Exercises 20-23 (helpers):  size / depth and the size<=2^(depth+1)
                            bound; case-splitting on matches.
Exercises 26-29 (equiv.):   refl / sym / trans; unfold + congruence.
Exercises 30-31 (creative): constant folding; independent proofs.
Challenges:                 recursive predicates, harder induction.
 *)

(** * COMMON PROOF PATTERNS IN AE (ROCQ TACTICS) *)

(**
PATTERN 1: Computation + arithmetic.
  Lemma foo : forall e1 e2,
    eval (Plus e1 e2) = eval e1 + eval e2.
  Proof. intros e1 e2. simpl. reflexivity. Qed.

PATTERN 2: Commutativity via lia.
  Lemma bar : forall e1 e2,
    eval (Plus e1 e2) = eval (Plus e2 e1).
  Proof. intros e1 e2. simpl. lia. Qed.

PATTERN 3: Structural induction.
  Lemma baz : forall e, 0 <= eval e.
  Proof.
    induction e as [n | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2];
      simpl; lia.
  Qed.

PATTERN 4: Optimization correctness.
  Induct on e; in the Plus case, case-split on the relevant
  subexpression, then rewrite with the induction hypotheses.
 *)

(** * ASSESSMENT STRATEGIES *)

(**
STRATEGY 1 - Weekly homework (recommended): assign exercises in
  increments of 5-10; grade by building the file.
STRATEGY 2 - Tiered: everyone does the core exercises; advanced
  students do the challenges.
STRATEGY 3 - Peer review: students check each other's proofs for
  correctness (does it compile?) and clarity.
STRATEGY 4 - Live coding: work a proof on screen in office hours.

Because Rocq checks correctness, grading is fast: build the file,
confirm no remaining [Admitted], spot-check a few proofs for clarity.
 *)

(** * TRANSITION TO NEXT SECTION *)

(**
After AE, students are ready for ABE (Arithmetic + Boolean
Expressions):
  - boolean literals (BTrue, BFalse) and operations (And, Or, Not)
  - comparisons (LessThan, Equal) and conditionals (IfThenElse)
  - a Value type for results: Value ::= NumV nat | BoolV bool
  - error handling: eval returns option Value (type errors -> None)
 *)

(** * FINAL NOTES *)

(**
This module demonstrates formal verification in miniature:
#<ol>#
#<li>#eval is an executable specification - a working interpreter.#</li>#
#<li>#Every lemma is machine-checked; no step is hand-waved.#</li>#
#<li>#If it compiles, it is correct.#</li>#
#<li>#Proofs compose, so an error in one lemma surfaces early.#</li>#
#</ol>#

By completing it, students have written a language implementation,
proven it correct, and prepared for booleans, identifiers,
functions, types, and state.
 *)
