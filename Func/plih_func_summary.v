(**
PLIH in Rocq: Func (Adding Functions) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in Func/):
#<ol>#
#<li>#plih_rocq_func_shared.v      -- shared infra (re-exports IDs/AE)#</li>#
#<li>#plih_func_lecture.v          -- lecture: closures, scoping, fuel#</li>#
#<li>#plih_func_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_func_solutions.v        -- complete solutions#</li>#
#<li>#plih_func_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_func_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//funs/1-Adding-Functions.html
  https://ku-sldg.github.io/plih//funs/2-Scoping.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Finish the IDs and Env chapters first - this chapter reuses the environment machinery and the substitution ideas.#</li>#
#<li>#Read plih_func_lecture.v.#</li>#
#<li>#Work plih_func_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_func_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_func_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
FBAE adds _first-class functions_ ([Lambda]/[App]) to BAE.  Two things
change in a fundamental way:
#<ol>#
#<li>#_The language can diverge._ With self-application we can write [omega], which loops forever.  So - unlike AE/BAE - there is _no_ measure that bounds evaluation, and _both_ interpreters (the substitution [evalS] and the environment [evalM]) must be driven by explicit _fuel_.  Running out of fuel yields [None].  The well-definedness result that replaces "size is enough fuel" (proved in IDs/Env) is _fuel monotonicity_, [evalM_mono]: [f1 <= f2 -> evalM f1 env e = Some v -> evalM f2 env e = Some v], i.e. more fuel never changes a definite answer.#</li>#
#<li>#_Scoping becomes a choice._ A function value must remember the environment in force where it was _defined_ - a _closure_ - to get _static_ scoping.  Evaluating a called function's body in the _caller's_ environment instead gives _dynamic_ scoping.  We build both ([evalM] with [ClosureV], [evalDyn] with a bare lambda value) and exhibit a term on which they disagree (4 vs 5).  The substitution interpreter [evalS] agrees with the closure interpreter: both are static.#</li>#
#</ol>#
 *)

(** * MODULE STRUCTURE *)

(**
LAYER 1: Foundations (plih_rocq_func_shared.v)
  - re-exports the IDs shared library ([Env]/[lookup]/[extend], the
    option monad, [String.eqb] lemmas).  FBAE is defined fresh.

LAYER 2: Lecture (plih_func_lecture.v)
  Section 1: Syntax - the FBAE language ([Lambda], [App])
  Section 2: Free identifiers, size, substitution (which can _grow_)
  Section 3: The substitution interpreter [evalS] (fuel)
  Section 4: Values and closures; the environment interpreter [evalM]
  Section 5: Running the interpreters
  Section 6: Fuel monotonicity + determinism (the headline)
  Section 7: Static vs dynamic scoping ([evalDyn]; 4 vs 5)
  Section 8: Currying
  Section 9: Divergence ([omega]); strict vs lazy binding
  (Elaboration and the recursion teaser follow; the lecture closes with)
  Section 12: Concrete syntax - a notation-based parser with
    [lambda ID in body] and _juxtaposition_ [f a] for application, so
    [<{ (lambda "x" in "x" + 1) 4 }>] elaborates to the abstract tree

LAYER 3: Exercises (plih_func_exercises.v)
  22 exercises + 2 challenges + 4 concrete-syntax exercises, including an
  error-reporting interpreter [evalErr] that distinguishes "out of gas"
  from "stuck".

LAYER 4: Solutions (plih_func_solutions.v)

LAYER 5: Instructor guide (plih_func_instructor_guide.v)
 *)

(** * KEY CONCEPTS TESTED BY EXERCISES *)

(**
Exercises 1-5   (warm-up):    running [evalM]; reflexivity.
Exercises 6-9   (equations):  evalM on Num/Lambda/Id; closures.
Exercises 10-13 (fuel):       monotonicity, determinism; re-proving
                              monotonicity for [evalDyn] (induction).
Exercises 14-16 (scoping):    static (4) vs dynamic (5).
Exercises 17-18 (currying):   partial application returns a closure.
Exercises 19-20 (divergence): [omega]; strict binding diverges.
Exercises 21-22 (evalErr):    an error interpreter refining [evalM].
Challenges:                   fuel stability; soundness of [evalErr].
 *)

(** * WHAT'S DIFFERENT FROM THE EARLIER CHAPTERS *)

(**
IDs/Env:  substitution preserves [size], so [size e] is enough fuel
          and (for Env) the interpreter is even a clean structural
          [Fixpoint].  Every closed term terminates.

Func:     substitution can _grow_ a term (we substitute functions), and
          self-application diverges.  No measure works; fuel is
          essential and can genuinely run out.  The metatheory shifts
          from "termination" to "monotone approximation of a partial
          function".
 *)

(** * TRANSITION TO NEXT SECTION *)

(**
The stuck states ("applying a non-function", "unbound identifier")
and the divergence that forced fuel on us are exactly what a _type
system_ sets out to control.  The next chapter, "Typed Functions",
adds function types; well-typed programs no longer get stuck, and the
story regains a total, structural flavour.
 *)
