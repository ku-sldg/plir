(**
PLIH in Rocq: Rec (Untyped Recursion) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in Rec/):
#<ol>#
#<li>#plih_rocq_rec_shared.v      -- shared infra (re-exports Func)#</li>#
#<li>#plih_rec_lecture.v          -- lecture: conditionals, Y/Z, recursion#</li>#
#<li>#plih_rec_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_rec_solutions.v        -- complete solutions#</li>#
#<li>#plih_rec_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_rec_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//funs/7-Untyped-Recursion.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Finish the Func chapter first - this chapter reuses closures, the fuel-driven interpreter idea, the [omega] term, and the strict vs lazy story (Func left recursion as a cliffhanger because FBAE had no conditional).#</li>#
#<li>#Read plih_rec_lecture.v.#</li>#
#<li>#Work plih_rec_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_rec_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_rec_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
Recursion needs _no_ new language construct.  With first-class functions
you can already write a _fixpoint combinator_ - a term [fix] with
[fix F ~> F (fix F)] - so a function receives its own recursive call as
an argument.  What the Func chapter's FBAE lacked was a _conditional_:
without a way to _test_ the argument and stop, every recursion diverged.

This chapter adds Booleans + [IsZero] + [If] (giving FBAEC) and then:
  - [omega] still diverges (self-application that loops);
  - the Y combinator = [omega] parameterised by [F]; it diverges under
    _strict_ (call-by-value) evaluation but runs under _lazy_ (call-by-name);
  - the Z combinator eta-guards the self-application ([\v. x x v]), so
    it is the _call-by-value_ fixpoint;
  - summation (0..5 = 15) and factorial (5! = 120) actually _terminate_:
    Z under strict [evalM], Y under lazy [evalL].
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM Func:
  - closures ([ClosureV]) and environment evaluation;
  - _fuel_-driven partial interpreters and _fuel monotonicity_ [evalM_mono];
  - the lazy interpreter [evalL] with thunks;
  - [omega], and the strict/lazy divergence contrast.

NEW HERE:
  - [FBAEC] = FBAE + [Boolean]/[IsZero]/[If] (+ [Mult] for factorial);
  - [BoolV]/[LBoolV] values; the [If] rule that runs only one branch;
  - the Y and Z combinators as FBAEC terms;
  - _productive_ recursion: real answers, not just divergence.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [FBAEC]        -- syntax (Section 1)
  [evalM]/[eval] -- strict closure interpreter + wrapper (Section 2)
  [evalL]/[evalLazy] -- lazy interpreter + wrapper (Section 3)
  [evalM_mono]   -- fuel monotonicity (Section 5)
  [Yc], [Zc]     -- the fixpoint combinators (Section 6)
  [sumGen], [factGen] -- recursive generators (Section 7)
  [sum_Z_strict], [fact_Z_strict]  -- Z runs recursion under strict eval
  [sum_Y_lazy], [fact_Y_lazy]      -- Y runs recursion under lazy eval
  [sum_Y_strict_diverges]          -- strict Y loops
  concrete syntax  -- FBAEC's own <{ }> parser (Section 8): Func's
    grammar plus [*], [true]/[false], [iszero e], [if c then t else f],
    so [sumGen]/[factGen] read as on paper (exercises 11-14)
 *)

(** * WHERE THIS GOES NEXT *)

(**
The untyped language is still Turing powerful ([omega], [Y]), so the
interpreter is inescapably _partial_.  Types will rule out the stuck and
divergent programs - but they also reject the self-application at the
heart of Y/Z, so recursion has to be reintroduced _deliberately_ as a
typed [fix] construct.  That is the Typed Recursion chapter.
 *)
