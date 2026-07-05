(**
PLIH in Rocq: Rec (Untyped Recursion) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in Rec/):
  1. plih_rocq_rec_shared.v      -- shared infra (re-exports Func)
  2. plih_rec_lecture.v          -- lecture: conditionals, Y/Z, recursion
  3. plih_rec_exercises.v        -- student problem set (Admitted stubs)
  4. plih_rec_solutions.v        -- complete solutions
  5. plih_rec_instructor_guide.v -- teaching guide
  6. plih_rec_summary.v          -- this file

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//funs/7-Untyped-Recursion.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
  1. Finish the Func chapter first - this chapter reuses closures, the
     fuel-driven interpreter idea, the [omega] term, and the strict vs
     lazy story (Func left recursion as a cliffhanger because FBAE had
     no conditional).
  2. Read plih_rec_lecture.v.
  3. Work plih_rec_exercises.v ([Admitted] -> [Qed]).
  4. Check against plih_rec_solutions.v.

FOR INSTRUCTORS:
  1. Read plih_rec_instructor_guide.v.
  2. Assign the exercises; grade by building the file.
 *)

(** * THE BIG IDEA *)

(**
Recursion needs NO new language construct.  With first-class functions
you can already write a FIXPOINT COMBINATOR - a term [fix] with
[fix F ~> F (fix F)] - so a function receives its own recursive call as
an argument.  What the Func chapter's FBAE lacked was a CONDITIONAL:
without a way to TEST the argument and stop, every recursion diverged.

This chapter adds Booleans + [IsZero] + [If] (giving FBAEC) and then:
  - [omega] still diverges (self-application that loops);
  - the Y combinator = [omega] parameterised by [F]; it diverges under
    STRICT (call-by-value) evaluation but runs under LAZY (call-by-name);
  - the Z combinator eta-guards the self-application ([\v. x x v]), so
    it is the CALL-BY-VALUE fixpoint;
  - summation (0..5 = 15) and factorial (5! = 120) actually TERMINATE:
    Z under strict [evalM], Y under lazy [evalL].
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM Func:
  - closures ([ClosureV]) and environment evaluation;
  - FUEL-driven partial interpreters and FUEL MONOTONICITY [evalM_mono];
  - the lazy interpreter [evalL] with thunks;
  - [omega], and the strict/lazy divergence contrast.

NEW HERE:
  - [FBAEC] = FBAE + [Boolean]/[IsZero]/[If] (+ [Mult] for factorial);
  - [BoolV]/[LBoolV] values; the [If] rule that runs only one branch;
  - the Y and Z combinators as FBAEC terms;
  - PRODUCTIVE recursion: real answers, not just divergence.
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
interpreter is inescapably PARTIAL.  Types will rule out the stuck and
divergent programs - but they also reject the self-application at the
heart of Y/Z, so recursion has to be reintroduced DELIBERATELY as a
typed [fix] construct.  That is the Typed Recursion chapter.
 *)
