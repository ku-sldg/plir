(**
PLIH in Rocq: IDs (Adding Identifiers) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in IDs/):
#<ol>#
#<li>#plih_rocq_ids_shared.v      -- shared infrastructure (re-exports AE)#</li>#
#<li>#plih_ids_lecture.v          -- lecture with worked examples#</li>#
#<li>#plih_ids_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_ids_solutions.v        -- complete solutions#</li>#
#<li>#plih_ids_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_ids_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//ids/1-Adding-IDs.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
  1. Read plih_ids_lecture.v for concepts and worked examples.
  2. Work through plih_ids_exercises.v, replacing each [Admitted]
     with a real proof ending in [Qed].
  3. Check your work against plih_ids_solutions.v.
  4. Build with [make] at the repo root to confirm everything
     compiles.

FOR INSTRUCTORS:
  1. Read plih_ids_instructor_guide.v for teaching strategies.
  2. Assign plih_ids_exercises.v in increments.
  3. Grade with plih_ids_solutions.v (Rocq checks correctness).
 *)

(** * WHAT IS NEW RELATIVE TO AE / ABE *)

(**
BAE = AE + identifiers.  Two new constructors:
  - [Id x]       : a use of an identifier.
  - [Bind x v b] : bind [x] to the value of [v] in the body [b].

The meaning of a binding is given by SUBSTITUTION:
  [bind x = v in b] evaluates [v] to a number, then replaces every
  free [x] in [b] with that number.

Two ideas dominate this chapter:
  1. BINDING STRUCTURE - free vs bound instances, scope, shadowing,
     and closed terms.
  2. A ROCQ-SPECIFIC SURPRISE - a substitution interpreter is not
     structurally recursive (substitution builds a NEW term), so the
     naive [Fixpoint] is rejected.  We drive evaluation with a
     [size]-bounded fuel and recover clean equations via a fuel
     monotonicity lemma.  This friction is precisely what the next
     chapter (Environments) removes.
 *)

(** * MODULE STRUCTURE *)

(**
LAYER 1: Foundations (plih_rocq_ids_shared.v)
  - re-exports the AE shared library (option monad, Env, lookup)
  - [string_eqb_refl], [string_eqb_sym] for name comparison

LAYER 2: Lecture (plih_ids_lecture.v)
  Section 1: Syntax (Inductive BAE) and binding terminology
  Section 2: Free identifiers ([free_in]) and closed terms
  Section 3: Substitution ([subst])
  Section 4: [size] and the invariant [size (subst i (Num n) e) = size e]
  Section 5: The fuel interpreter ([evalF], [eval]), monotonicity,
             and the clean equations [eval_Num]/[eval_Plus]/...
  Section 6: Testing
  Section 7: Substitution properties ([subst_not_free],
             [free_in_subst_num], [closed_after_subst])
  Section 8: Evaluation properties ([bind_num_subst], [bind_unused])
  Section 9: Expression equivalence ([bae_equiv])
  Section 10: Concrete syntax - a notation-based parser where numerals
    coerce to [Num], strings to [Id], and [bind ID = e1 in e2] is
    [Bind], so [<{ bind "x" = 5 + 2 in "x" + "x" - 4 }>] elaborates to
    the abstract tree (after Software Foundations' Imp)

LAYER 3: Exercises (plih_ids_exercises.v)
  24 exercises + 2 challenges (fuel independence; PROGRESS for
  closed programs) + 4 concrete-syntax exercises, graduated in
  difficulty, each an [Admitted] stub.

LAYER 4: Solutions (plih_ids_solutions.v)
  Complete proofs for every exercise and challenge.

LAYER 5: Instructor guide (plih_ids_instructor_guide.v)
 *)

(** * KEY CONCEPTS TESTED BY EXERCISES *)

(**
Exercises 1-5   (warm-up):    running [eval]; proof by reflexivity.
Exercises 6-9   (subst):      computing and reasoning about subst.
Exercises 10-14 (free/closed):[free_in], [closed], shadowing.
Exercises 15-19 (eval eqns):  using the lecture's equation lemmas.
Exercises 20-22 (equiv):      [bae_equiv]; renaming; closed subst.
Exercises 23-24 (subst/free): [free_in_subst_num] consequences.
Challenges:                   fuel independence; progress theorem.
 *)

(** * TRANSITION TO NEXT SECTION *)

(**
The next chapter, "Adding Environments" (Env/), keeps the SAME BAE
language but replaces eager substitution with a deferred
ENVIRONMENT of identifier/value bindings.  Highlights:
  - [evalE : Env nat -> BAE -> option nat] is a clean structural
    [Fixpoint] (no fuel needed).
  - We PROVE the two interpreters always agree:
      [forall e, evalE [] e = eval e].
  This makes precise the chapter's claim that environments do not
  change WHAT eval does - only HOW efficiently it does it.
 *)
