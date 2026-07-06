(**
PLIH in Rocq: RSMon (Reader+State Monad) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in RSMon/):
#<ol>#
#<li>#plih_rocq_rsmon_shared.v      -- shared infra (re-exports SMon)#</li>#
#<li>#plih_rsmon_lecture.v          -- lecture: combined Reader+State monad, evalRS, agreement theorem#</li>#
#<li>#plih_rsmon_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_rsmon_solutions.v        -- complete solutions#</li>#
#<li>#plih_rsmon_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_rsmon_summary.v          -- this file#</li>#
#</ol>#

Source idea (PLIH, Haskell): combining effects / monad transformers
  https://ku-sldg.github.io/plih//state/
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Finish RMon (Reader monad) and SMon (State monad) first - this chapter _combines_ exactly those two effects in one monad.#</li>#
#<li>#Read plih_rsmon_lecture.v.#</li>#
#<li>#Work plih_rsmon_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_rsmon_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_rsmon_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
SMon hid the mutable _store_ behind a State monad but left the _environment_
an explicit argument.  RMon hid a read-only context behind a Reader
monad.  This chapter puts _both_ effects in one monad:

  RS E S A := E -> S -> option (A * S)

- the _Reader_ part (environment [E], read-only): [askRS] reads it,
  [localRS g m] runs [m] under [g e] (used to extend it);
- the _State_ part (store [S], mutable): [getRS] reads it, [putRS] replaces
  it - and only the store is returned, since the environment never
  changes;
- [retRS]/[bindRS]/[failRS] are the monad core, and [bindRS] threads
  _both_ resources at once.

The interpreter [evalRS] then carries _neither_ the environment nor the
store explicitly.  The headline is _agreement_:

  evalRS fuel e env s = evalM fuel env s e

one induction showing both hidden resources line up with [evalM]'s hand
plumbing.
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER:
  - the reference-cell language [FBAES], values [RVal], the [Store], and
    the explicit interpreter [evalM]/[eval] (from State);
  - the store plumbing [update_at] / [nth_error_snoc];
  - the Reader ops idea from RMon and the State ops from SMon.

NEW HERE:
  - the _combined_ monad [RS] with [askRS]/[localRS] and [getRS]/[putRS]
    over one [bindRS];
  - the interpreter [evalRS] hiding _both_ env and store, and its wrapper
    [evalReaderState];
  - the single agreement theorem [evalRS_agrees] (+ corollary
    [evalReaderState_agrees]) and effect-independence lemmas.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [FBAES]/[RVal]/[Store]/[evalM] -- reference language + interpreter (S1)
  [RS]/[retRS]/[bindRS]/[askRS]/[localRS]/[getRS]/[putRS]/[failRS]/[runRS]
                                 -- the combined monad (Section 2)
  [evalRS]/[evalReaderState]     -- the monadic interpreter + wrapper (S3)
  [evalRS_agrees]                -- _headline_: monadic = explicit (S5)
  [evalReaderState_agrees]       -- lifted to the top-level wrappers
  [left_id_RS], [ask_get_comm], [local_scoped] -- laws / independence (S6)
  concrete syntax     -- the State chapter's FBAES notation parser
    ([new e]/[! e]/[l := e]/[a ; b]), read via [evalReaderState]
    (Section 7, exercises 11-13)
 *)

(** * WHERE THIS GOES NEXT *)

(**
This closes the monad arc.  Students have now seen a Reader (RMon), an
Either (EMon), a State (SMon), and finally two effects stacked together
(RSMon) - the essence of _monad transformers_, where each effect
contributes its own operations to a shared [bind].  A natural extension
adds a third layer - Either for descriptive error messages - so the
interpreter reads its environment, mutates its store, and reports typed
failures, all through one monad.
 *)
