(**
PLIH in Rocq: SMon (State Monad) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in SMon/):
  1. plih_rocq_smon_shared.v      -- shared infra (re-exports State)
  2. plih_smon_lecture.v          -- lecture: State monad, evalS,
                                      agreement theorem
  3. plih_smon_exercises.v        -- student problem set (Admitted stubs)
  4. plih_smon_solutions.v        -- complete solutions
  5. plih_smon_instructor_guide.v -- teaching guide
  6. plih_smon_summary.v          -- this file

Source idea (PLIH, Haskell):
  https://ku-sldg.github.io/plih//state/
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
  1. Finish the State chapter first - this chapter refactors that
     chapter's explicit store-threading interpreter [evalM], which it
     keeps as the reference to match.
  2. Read plih_smon_lecture.v.
  3. Work plih_smon_exercises.v ([Admitted] -> [Qed]).
  4. Check against plih_smon_solutions.v.

FOR INSTRUCTORS:
  1. Read plih_smon_instructor_guide.v.
  2. Assign the exercises; grade by building the file.
 *)

(** * THE BIG IDEA *)

(**
The State chapter's interpreter returns a (value, store) pair and
threads the store BY HAND: every case names [s1], [s2], ... and passes
each subexpression the store its predecessor left.  A STATE MONAD names
that pattern once and hides it:

  State S A := S -> option (A * S)

with [retS] (succeed, store untouched), [bindS] (run, then continue in
the store left behind - the threading, in ONE place), [getS] (read the
store), [putS] (replace it), and [failS].  The interpreter [evalS] is
then the SAME interpreter with no store variable in sight: [bindS]
threads it, and [getS]/[putS] appear only at [New]/[Deref]/[Assign].

The headline is AGREEMENT:

  evalS fuel env e s = evalM fuel env s e

The monadic refactor changes the STRUCTURE, not the behavior - exactly
the payoff the Reader monad (RMon) gave the type checker, now for the
evaluator's store.
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM State:
  - the reference-cell language [FBAES], values [RVal] (with [LocV]),
    the [Store], and the explicit interpreter [evalM]/[eval];
  - the store plumbing [update_at] / [nth_error_snoc].

NEW HERE:
  - the STATE monad [State]/[retS]/[bindS]/[getS]/[putS]/[failS] with
    [runState] and [;;] notation;
  - the monadic interpreter [evalS] and its wrapper [evalStore];
  - the AGREEMENT theorem [evalS_agrees] (+ corollary
    [evalStore_agrees]) and the definitional monad laws.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [FBAES]/[RVal]/[Store]/[evalM] -- the reference language and
                                    interpreter (Section 1)
  [State]/[retS]/[bindS]/[getS]/[putS]/[failS]/[runState] -- the monad
                                                             (Section 2)
  [evalS]/[evalStore] -- the monadic interpreter + wrapper (Section 3)
  [evalS_agrees]      -- HEADLINE: monadic = explicit (Section 5)
  [evalStore_agrees]  -- the same, lifted to the top-level wrappers
  [left_id_S], [get_put_S] -- monad laws holding definitionally
  concrete syntax     -- the State chapter's FBAES notation parser
    ([new e]/[! e]/[l := e]/[a ; b]), read via [evalStore] (Section 7,
    exercises 11-13)
 *)

(** * WHERE THIS GOES NEXT *)

(**
This closes the mutable-state arc: State showed WHAT mutation is (an
explicitly threaded store); SMon shows how to STRUCTURE the threading so
the interpreter reads like the pure ones again.  A natural sequel
combines the monads seen so far - a Reader for the (read-only)
environment and a State for the store - into one interpreter, the way
EMon combined Reader with Either for the checker.
 *)
