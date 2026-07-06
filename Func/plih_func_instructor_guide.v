(**
INSTRUCTOR GUIDE: Teaching the Func (Adding Functions) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have completed IDs (substitution, [subst], free/bound
instances, closed terms) and Env ([Env]/[lookup]/[extend], the
environment interpreter).  New machinery:
  - a value type _separate_ from the term type ([FBAEVal]);
  - _closures_: a value that captures an environment;
  - reasoning about a _fuel_-driven partial interpreter when _no_ measure
    bounds it (contrast the [size]-bounded story of IDs/Env).
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
#<ol>#
#<li>#_Motivate._ Functions are values: they can be bound, passed, and returned.  Add [Lambda]/[App]; give the substitution interpreter [evalS] (beta reduction = substitute the argument into the body).#</li>#
#<li>#_The fuel surprise._ In IDs we substituted only numbers, so [size] was preserved and bounded the fuel.  Now we substitute _functions_, so substitution can _grow_ a term ([subst_grows]) - and [omega] diverges outright.  There is _no_ measure; fuel is unavoidable and can run out.  This is the central conceptual step of the chapter.#</li>#
#<li>#_Closures._ A returned function must remember the bindings in force where it was defined, or free variables lose their meaning.  Define [FBAEVal] with [ClosureV i b env] and the environment interpreter [evalM].  Stress the [App] case: run the body in the _closure's_ environment, extended with the argument.#</li>#
#<li>#_Metatheory._ With no measure, the well-definedness result is _fuel monotonicity_ ([evalM_mono]): more fuel never changes an answer.  Prove it by induction on fuel (the proof is a good template - the exercises ask students to redo it for [evalDyn]).#</li>#
#<li>#_Scoping._ Build [evalDyn] (function values carry _no_ environment; the body runs in the caller's environment) and evaluate [scopeTest] under both: 4 (static) vs 5 (dynamic).  Point out that [evalS] (substitution) also gives 4 - substitution is inherently static.#</li>#
#<li>#_Currying_ and _strict/lazy_ round out the picture.#</li>#
#</ol>#
 *)

(** * PART 3: LESSON PLAN (one week) *)

(**
HOUR 1 - Functions as values.  [Lambda]/[App], beta reduction, the
  substitution interpreter [evalS]; run [idFun], [incFun].
HOUR 2 - Divergence and fuel.  [subst_grows], [omega]; why no measure
  works; the fuel discipline and monotonicity.
HOUR 3 - Closures and static scoping.  [FBAEVal], [evalM]; trace a
  returned function; contrast [evalDyn] on [scopeTest] (4 vs 5).
HOUR 4 - Currying, strict/lazy, and the error interpreter [evalErr].
HOUR 5 - Concrete syntax (Section 12).
  Objectives: extend the parser with functions; understand _application
  by juxtaposition_ and its precedence.
  Strategy:
    - Reuse the IDs recipe (two coercions + [bind]); add [lambda ID in
      body] and the juxtaposition rule [f a] = [App f a] at the tightest
      level (1), left-associative.
    - Work [f a b] = [(f a) b] and [f a + b] = [(f a) + b] by hand, then
      confirm by [reflexivity]; reproduce [addFun] concretely and curry
      it: [(lambda "x" in lambda "y" in "x" + "y") 3 4].
  Common mistakes: forgetting that application binds _tighter_ than the
  operators (so [f x + 1] is [(f x) + 1], not [f (x + 1)]); and
  forgetting the quotes on identifiers.
  Assign: exercises 23-26.
 *)

(** * PART 4: COMMON STUDENT MISTAKES *)

(**
MISTAKE 1: "size e is enough fuel."  It was in IDs/Env; it is _not_
  here.  Substituting a function grows the term, and [omega] never
  terminates.  Fuel can legitimately run out; that is not a bug.

MISTAKE 2: Applying the body in the wrong environment.  Static scoping
  uses the _closure's_ captured environment ([cenv]), not the caller's.
  Using the caller's environment is precisely the [evalDyn] bug -
  demonstrated deliberately.

MISTAKE 3: Confusing the term [Lambda] with the value [ClosureV].
  [evalM] never returns a [Lambda]; it returns a [ClosureV] that pairs
  the lambda with an environment.

MISTAKE 4: Trying [reflexivity] with too little fuel.  The example
  wrapper [eval] fixes fuel at 100; a deeper computation needs more.
  Monotonicity ([evalM_mono], challenge 1) is how you raise it safely.

MISTAKE 5: In the monotonicity proof, forgetting to [destruct f2]
  after the [S k] case (a [Some] result forces [f2 = S k2]).
 *)

(** * PART 5: ASSESSMENT *)

(**
Suggested grading:
  Exercises 1-9   (basic):        reflexivity + equation lemmas.
  Exercises 10-12 (standard):     citing monotonicity/determinism.
  Exercise 13     (hard):         re-prove monotonicity for [evalDyn].
  Exercises 14-16 (scoping):      the static/dynamic distinction.
  Exercises 17-20 (standard):     currying and divergence.
  Exercises 21-22 (hard):         the [evalErr] refinement (induction).
  Challenges:                     applications of the above.

Rubric as elsewhere: compilation with no remaining [Admitted] carries
most of the grade.  Rocq tactics only - never Lean [sorry].
 *)

(** * PART 6: TRANSITION TO TYPED FUNCTIONS *)

(**
This chapter leaves two loose ends that a _type system_ ties off:
  - _stuck_ terms (adding a function, applying a number) - ruled out by
    typing, so [evalM] would no longer need its error cases;
  - the _divergence_ that forced fuel on us - a simply-typed calculus is
    strongly normalizing, restoring a total, measure-bounded story.
The next chapter, "Typed Functions", introduces function types and a
type checker, and proves that well-typed programs do not get stuck.
 *)
