(**
PLIH in Rocq: Env (Adding Environments) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in Env/):
  1. plih_rocq_env_shared.v      -- shared infra (re-exports IDs)
  2. plih_env_lecture.v          -- lecture with the agreement proof
  3. plih_env_exercises.v        -- student problem set (Admitted stubs)
  4. plih_env_solutions.v        -- complete solutions
  5. plih_env_instructor_guide.v -- teaching guide
  6. plih_env_summary.v          -- this file

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//ids/2-Adding-Environments.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
  1. Finish the IDs chapter first - this chapter reuses its BAE
     language, [subst], and [eval].
  2. Read plih_env_lecture.v.
  3. Work plih_env_exercises.v ([Admitted] -> [Qed]).
  4. Check against plih_env_solutions.v.

FOR INSTRUCTORS:
  1. Read plih_env_instructor_guide.v.
  2. Assign the exercises; grade by building the file.
 *)

(** * THE BIG IDEA *)

(**
An ENVIRONMENT is a table of identifier/value bindings.  Instead of
substituting a value the moment a [Bind] is seen, we remember the
binding and look it up when we reach an [Id].  This is a pure
EFFICIENCY optimization: it does not change WHAT eval computes.

The chapter's whole point, made precise in Rocq:

    forall e, evalE nil e = eval e          (evalE_agrees_eval)

where [eval] is the substitution interpreter from the IDs chapter.
The Haskell course checks this with QuickCheck
([\t -> eval [] t == evals t]); we prove it for ALL terms.

A pleasant Rocq-specific bonus: [evalE] is a clean structural
[Fixpoint] (the environment is just a parameter), so - unlike the
substitution interpreter - it needs no fuel.
 *)

(** * MODULE STRUCTURE *)

(**
LAYER 1: Foundations (plih_rocq_env_shared.v)
  - re-exports the IDs lecture (BAE, subst, eval, size, free_in)
    and the shared [Env]/[lookup]/[extend] operations.

LAYER 2: Lecture (plih_env_lecture.v)
  Section 1: Environments as deferred substitution
  Section 2: The structural interpreter [evalE] and [evalEnv]
  Section 3: Testing
  Section 4: Environment lemmas ([evalE_ext], [lookup_shadow_env],
             [lookup_swap_env])
  Section 5: The key lemma
             [evalE (extend i n env) e = evalE env (subst i (Num n) e)]
  Section 6: AGREEMENT ([evalE_evalF], [evalE_agrees_eval])
  Section 7: Properties of [evalE]

LAYER 3: Exercises (plih_env_exercises.v)
  22 exercises + 2 challenges, including a PRELUDE interpreter and an
  error-reporting interpreter [evalErr] (with [Either]-style results).

LAYER 4: Solutions (plih_env_solutions.v)

LAYER 5: Instructor guide (plih_env_instructor_guide.v)
 *)

(** * KEY CONCEPTS TESTED BY EXERCISES *)

(**
Exercises 1-5   (warm-up):    running [evalE]; reflexivity.
Exercises 6-9   (equations):  evalE on Num/Id/Bind; [lookup_extend_eq].
Exercises 10-12 (env lemmas): extensionality, shadowing, swapping.
Exercises 13-16 (agreement):  the two interpreters coincide; progress
                              transfers to [evalE].
Exercises 17-19 (prelude):    an initial environment of globals.
Exercises 20-22 (evalErr):    an [Either]-style error interpreter that
                              refines [evalE].
Challenges:                   error reporting; equivalence transfer.
 *)

(** * TRANSITION TO NEXT SECTION *)

(**
With identifiers, substitution, and environments in hand, the course
next adds FUNCTIONS (first-class [lambda]/application), where the
environment grows into a closure discipline and scoping (static vs
dynamic) becomes a central concern.  The [evalE]/environment
machinery built here is exactly the foundation those chapters extend.
 *)
