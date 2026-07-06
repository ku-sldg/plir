(**
INSTRUCTOR GUIDE: Teaching the IDs (Adding Identifiers) Section

Documentation only - no Rocq code.  Compiles trivially.

This guide covers: prerequisites, what to emphasize, common student
mistakes, a lesson plan, and the transition to Environments.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have finished AE (and ideally ABE): inductive types,
[Fixpoint], and the tactics intro / simpl / reflexivity / lia /
induction / destruct.  New machinery in this chapter:
  - [String] identifiers and [String.eqb] with its reflection
    lemmas ([String.eqb_eq], [String.eqb_neq], [String.eqb_refl]).
  - the option monad for possible failure (a free identifier has no
    value), reused from the AE shared library.
 *)

(** * PART 2: THE TWO BIG IDEAS *)

(**
IDEA 1 - Binding structure.  Spend time on the vocabulary: instance,
binding instance, scope, bound instance, free instance.  Draw the
AST of [bind x = 5+2 in x+x-4] and circle the binding instance and
the bound instances.  Then show a free instance ([x+1] with no
enclosing bind).  Formalize with [free_in] and [closed].

IDEA 2 - Substitution and termination.  Present [subst] and the rule

    a |-> v_a      [i |-> v_a] s |-> v_s
    ------------------------------------  [BindE]
         (bind i = a in s) |-> v_s

Then hit the Rocq-specific wall: the interpreter would recurse on
[subst i (Num n) b], which is _not_ a structural subterm, so a plain
[Fixpoint] is rejected.  This is a genuine teaching moment - Haskell
hides it because it allows non-terminating definitions.  Introduce
the [size]-bounded fuel [evalF] and [eval e := evalF (size e) e], and
explain why [size (subst i (Num n) e) = size e] makes the fuel
sufficient.  The clean equations [eval_Plus]/[eval_Bind]/... let
students reason about [eval] without ever mentioning fuel again.
 *)

(** * PART 3: LESSON PLAN (one week) *)

(**
HOUR 1 - Syntax and binding structure.
  Define BAE; draw ASTs; classify instances; define [free_in] and
  [closed]; compute a few [free_in] examples.

HOUR 2 - Substitution.
  Define [subst]; trace [ [x |-> 7] (x+x-4) ]; show the shadowing
  case [bind x = .. in ..]; prove [subst_not_free].

HOUR 3 - The interpreter and fuel.
  Motivate why a substitution [Fixpoint] is rejected; introduce
  [evalF]/[eval]; prove [size_subst_num] and [evalF_mono] at a high
  level; use the equation lemmas to evaluate examples.

HOUR 4 - Properties and the progress challenge.
  Prove [bind_num_subst], [bind_unused]; discuss [free_in_subst_num]
  and [closed_after_subst]; sketch _progress_ (closed programs never
  get stuck) as the capstone.

HOUR 5 - Concrete syntax (Section 10).
  Objectives: build the [<{ ... }>] parser from notations; understand
  the _two_ leaf coercions (numerals to [Num], strings to [Id]) and the
  [bind ID = e1 in e2] binding form.
  Strategy:
    - Reuse the AE/ABE recipe (custom entry + escape hatch), then add
      the second coercion and the [bind] notation.  Show that the
      identifier slot [v] is an ordinary [string] constr, while the
      bound expression and body are BAE terms.
    - Reproduce [bae_example_1] concretely and confirm by [reflexivity];
      then state [bind_num_subst] in concrete syntax.
  Common mistake: forgetting the quotes on identifiers - inside the
  brackets ["x"] is [Id "x"], but a bare [x] is a Rocq variable.  Also,
  when a bound expression is a metavariable [n : nat] it needs its type
  annotated so the [Num] coercion fires (see the lecture's
  [bind_num_subst_concrete]).
  Assign: exercises 25-28.

Total: ~3.5 hours instruction + ~3 hours problem solving.
 *)

(** * PART 4: COMMON STUDENT MISTAKES *)

(**
MISTAKE 1: Substituting under a shadowing binder.  In [subst], the
  body of [Bind i' v' b'] is substituted only when [i <> i'].  Ask
  students why [subst x v (bind x = e in x)] must leave the inner [x]
  alone.

MISTAKE 2: Expecting a plain [Fixpoint] interpreter.  Emphasize that
  substitution is not structural; the fuel is not a hack but a
  faithful encoding of a size-decreasing recursion.

MISTAKE 3: Fighting the fuel.  Students should reason with the
  equation lemmas ([eval_Plus], [eval_Bind], ...), _not_ by unfolding
  [evalF].  Point them at these lemmas early.

MISTAKE 4: Concrete strings compute.  [String.eqb "x" "x"] reduces to
  [true] under [simpl]/[compute], so goals about literal identifiers
  often close by [reflexivity]/[compute]/[discriminate] without any
  [String.eqb_refl] rewrite (which is needed only for _variable_ names).

MISTAKE 5: Confusing syntactic and semantic equality, as in AE:
  [bae_equiv e1 e2] is [eval e1 = eval e2], not [e1 = e2].
 *)

(** * PART 5: ASSESSMENT *)

(**
Suggested grading for the exercise set:
  Exercises 1-9   (basic):        reflexivity + lemma citations.
  Exercises 10-19 (standard):     free/closed + eval equations.
  Exercises 20-24 (intermediate): equivalence and subst/free facts.
  Challenge 1:                    fuel independence (short).
  Challenge 2:                    progress theorem (bonus, hard).

Rubric: compilation with no remaining [Admitted] (most of the grade),
correctness of the stated claim, and clarity.  Use Rocq tactics only
(never Lean [sorry]; unfinished goals stay [Admitted]).
 *)

(** * PART 6: TRANSITION TO ENVIRONMENTS *)

(**
The next chapter reuses this exact BAE language but replaces eager
substitution with a deferred _environment_.  Preview the payoff:
#<ol>#
#<li>#[evalE] is a clean structural [Fixpoint] - no fuel.#</li>#
#<li>#The equivalence theorem [evalE [] e = eval e] proves the two interpreters compute the same answers, so environments are a pure _efficiency_ optimization.#</li>#
#</ol>#
The substitution lemmas proven here ([subst_not_free],
[free_in_subst_num]) reappear as the workhorses of that proof.
 *)
