(**
PLIH in Rocq: RMon (Reader Monad) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in RMon/):
#<ol>#
#<li>#plih_rocq_rmon_shared.v      -- shared infra (re-exports TRec)#</li>#
#<li>#plih_rmon_lecture.v          -- lecture: Reader monad type checker#</li>#
#<li>#plih_rmon_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_rmon_solutions.v        -- complete solutions#</li>#
#<li>#plih_rmon_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_rmon_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//types/5-More-Reader-Monad.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
  1. Finish TFun/TRec first - this chapter refactors their type checker.
  2. Read plih_rmon_lecture.v.
  3. Work plih_rmon_exercises.v ([Admitted] -> [Qed]).
  4. Check against plih_rmon_solutions.v.

FOR INSTRUCTORS:
  1. Read plih_rmon_instructor_guide.v.
  2. Assign the exercises; grade by building the file.
 *)

(** * THE BIG IDEA *)

(**
The type checker of TFun/TRec threads a type CONTEXT through every case
by hand.  A READER MONAD - a computation "with access to a fixed
environment", [Reader E A = E -> option A] - makes that threading
implicit:
  - [askR]        reads the context (used by [Id]);
  - [localR g m]  runs [m] under a modified context (used by
                  [Bind]/[Lambda] to add a binding);
  - [bindR]/[;;]  carries the context from one step to the next;
  - [retR]/[failR] succeed/fail without touching it.

The monadic checker [typeofR] has NO [ctx] parameter, yet computes
exactly what the explicit [typeof] does:

    typeofR e ctx = typeof ctx e          ([typeofR_agrees])

The Reader monad is a change of STYLE, proven not to change MEANING.
(This is a technique chapter: the language is TRec's and the evaluator
is unchanged; only the CHECKER is restructured.)
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [typeof]/[typecheck]     -- the direct, explicit-context checker
  [Reader], [retR], [bindR], [askR], [localR], [failR], [runR], [;;]
  [typeofR]/[typecheckR]   -- the monadic checker
  [typeofR_agrees]         -- typeofR e ctx = typeof ctx e  (headline)
  [typecheckR_agrees]      -- typecheckR e = typecheck e
  concrete syntax          -- TRec's type grammar [<[ Nat -> Bool ]>] and
    term grammar [<{ ... }>] (ascribed lambda + prefix [fix]), read via
    [typecheckR] (Section 6, exercises 9-11)
 *)

(** * WHERE THIS GOES NEXT *)

(**
The Reader monad still reports failure as a bare [None] - "ill-typed",
with no reason.  The next chapter (Reader-and-Either) upgrades failure
to an informative error MESSAGE while keeping the Reader threading, so a
rejected program can say WHY it was rejected.
 *)
