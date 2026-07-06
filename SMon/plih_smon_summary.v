(**
PLIH in Rocq: SMon (State Monad) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in SMon/):
#<ol>#
#<li>#plih_rocq_smon_shared.v      -- shared infra (re-exports State)#</li>#
#<li>#plih_smon_lecture.v          -- lecture: State monad, evalS, agreement theorem#</li>#
#<li>#plih_smon_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_smon_solutions.v        -- complete solutions#</li>#
#<li>#plih_smon_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_smon_summary.v          -- this file#</li>#
#</ol>#

Source idea (PLIH, Haskell):
  https://ku-sldg.github.io/plih//state/
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Finish the State chapter first - this chapter refactors that chapter's explicit store-threading interpreter [evalM], which it keeps as the reference to match.#</li>#
#<li>#Read plih_smon_lecture.v.#</li>#
#<li>#Work plih_smon_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_smon_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_smon_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
The State chapter's interpreter returns a (value, store) pair and
threads the store _by hand_: every case names [s1], [s2], ... and passes
each subexpression the store its predecessor left.  A _state monad_ names
that pattern once and hides it:

  State S A := S -> option (A * S)

with [retS] (succeed, store untouched), [bindS] (run, then continue in
the store left behind - the threading, in _one_ place), [getS] (read the
store), [putS] (replace it), and [failS].  The interpreter [evalS] is
then the _same_ interpreter with no store variable in sight: [bindS]
threads it, and [getS]/[putS] appear only at [New]/[Deref]/[Assign].

The headline is _agreement_:

  evalS fuel env e s = evalM fuel env s e

The monadic refactor changes the _structure_, not the behavior - exactly
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
  - the _state monad_ [State]/[retS]/[bindS]/[getS]/[putS]/[failS] with
    [runState] and [;;] notation;
  - the monadic interpreter [evalS] and its wrapper [evalStore];
  - the _agreement_ theorem [evalS_agrees] (+ corollary
    [evalStore_agrees]) and the definitional monad laws.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [FBAES]/[RVal]/[Store]/[evalM] -- the reference language and
                                    interpreter (Section 1)
  [State]/[retS]/[bindS]/[getS]/[putS]/[failS]/[runState] -- the monad
                                                             (Section 2)
  [evalS]/[evalStore] -- the monadic interpreter + wrapper (Section 3)
  [evalS_agrees]      -- _headline_: monadic = explicit (Section 5)
  [evalStore_agrees]  -- the same, lifted to the top-level wrappers
  [left_id_S], [get_put_S] -- monad laws holding definitionally
  concrete syntax     -- the State chapter's FBAES notation parser
    ([new e]/[! e]/[l := e]/[a ; b]), read via [evalStore] (Section 7,
    exercises 11-13)
 *)

(** * WHERE THIS GOES NEXT *)

(**
This closes the mutable-state arc: State showed _what_ mutation is (an
explicitly threaded store); SMon shows how to _structure_ the threading so
the interpreter reads like the pure ones again.  A natural sequel
combines the monads seen so far - a Reader for the (read-only)
environment and a State for the store - into one interpreter, the way
EMon combined Reader with Either for the checker.
 *)
