(**
 * INSTRUCTOR GUIDE: Teaching the Env (Adding Environments) Section
 *
 * Documentation only - no Rocq code.  Compiles trivially.
 *)

(* ================================================================ *)
(* PART 1: PREREQUISITES                                            *)
(* ================================================================ *)

(**
 * Students must have completed the IDs chapter: BAE, [subst], free/
 * bound instances, closed terms, and the (fuel-driven) substitution
 * interpreter [eval].  This chapter reuses all of it.  New machinery:
 *   - the [Env]/[lookup]/[extend] operations from the shared library;
 *   - reasoning about a function ([evalE]) that carries an extra
 *     parameter through the induction.
 *)

(* ================================================================ *)
(* PART 2: THE ARC OF THE LECTURE                                   *)
(* ================================================================ *)

(**
 * 1. MOTIVATE.  Recall that the substitution interpreter re-walks the
 *    body on every binding, and (in Rocq) even needed fuel because
 *    substitution is not structural.  An environment fixes both: defer
 *    the substitution, record the binding, and look it up on demand.
 *
 * 2. DEFINE [evalE].  Stress that it is a plain [Fixpoint]: every
 *    recursive call is on a subterm; the environment is a parameter.
 *    No fuel, no [size] measure.
 *
 * 3. REASON.  Prove [evalE_ext] (equal lookups => equal results) and
 *    the shadowing/swapping lookup lemmas.  These are the algebra of
 *    environments.
 *
 * 4. THE KEY LEMMA.
 *      evalE (extend i n env) e = evalE env (subst i (Num n) e)
 *    "an environment binding is a deferred substitution."  The [Bind]
 *    case is where shadowing (names equal) and reordering (names
 *    different) show up - hence the two lookup lemmas.
 *
 * 5. AGREEMENT.  [evalE nil e = eval e].  We reason against the fuel
 *    form [evalF]; the [Bind] case uses the key lemma to turn a pushed
 *    binding back into a substitution, and [size_subst_num] keeps the
 *    fuel bound honest.  Emphasize the payoff: environments are proven
 *    to be a pure optimization.
 *)

(* ================================================================ *)
(* PART 3: LESSON PLAN (one week)                                   *)
(* ================================================================ *)

(**
 * HOUR 1 - Environments and [evalE].  Trace [bind x=4 in bind y=5 in
 *   x+y-4] pushing bindings; define [evalE]; run the examples.
 * HOUR 2 - Environment algebra.  Prove [evalE_ext]; discuss shadowing
 *   and swapping via the lookup lemmas.
 * HOUR 3 - The key lemma and agreement.  Walk the [Bind] case slowly;
 *   then assemble [evalE_agrees_eval].
 * HOUR 4 - Prelude and error reporting.  Introduce a prelude
 *   environment; develop [evalErr] and prove it refines [evalE].
 *)

(* ================================================================ *)
(* PART 4: COMMON STUDENT MISTAKES                                  *)
(* ================================================================ *)

(**
 * MISTAKE 1: Looking up in the wrong direction.  [lookup] finds the
 *   FIRST (most recent) binding; [extend x n env = (x,n)::env] pushes
 *   on the front, so inner binds shadow outer ones automatically.
 *
 * MISTAKE 2: Forgetting extensionality is the tool.  To equate two
 *   environments, reduce to "every lookup agrees" via [evalE_ext];
 *   do NOT try to [rewrite] one environment into the other.
 *
 * MISTAKE 3: Reproving agreement per example.  Once
 *   [evalE_agrees_eval] is available, concrete agreement goals are
 *   [apply evalE_agrees_eval] - or just [reflexivity], since both
 *   sides compute.
 *
 * MISTAKE 4: Mishandling [evalErr].  When relating [evalErr] to
 *   [evalE], erase the error message with [forget] and case-split on
 *   the recursive [Result]s; the induction hypotheses do the rest.
 *)

(* ================================================================ *)
(* PART 5: ASSESSMENT                                               *)
(* ================================================================ *)

(**
 * Suggested grading:
 *   Exercises 1-9   (basic):        reflexivity + equation lemmas.
 *   Exercises 10-15 (standard):     environment algebra + agreement.
 *   Exercise 16     (bonus):        progress transfer.
 *   Exercises 17-19 (prelude):      concrete evaluation.
 *   Exercises 20-22 (evalErr):      the refinement proof (hardest).
 *   Challenges:                     short applications of agreement.
 *
 * Rubric as elsewhere: compilation with no remaining [Admitted] carries
 * most of the grade.  Rocq tactics only - never Lean [sorry].
 *)

(* ================================================================ *)
(* PART 6: TRANSITION TO FUNCTIONS                                  *)
(* ================================================================ *)

(**
 * The next unit adds first-class functions.  Environments become the
 * heart of the story: a function value must capture the environment in
 * force at its definition (a CLOSURE) to get STATIC scoping right, and
 * the difference from DYNAMIC scoping is exactly a difference in which
 * environment the body sees.  Everything here - [evalE], [evalE_ext],
 * the key lemma - is the groundwork.
 *)
