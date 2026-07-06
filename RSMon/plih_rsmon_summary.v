(**
PLIH in Rocq: RSMon (Reader+State Monad) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in RSMon/):
#<ol>#
#<li>#plih_rocq_rsmon_shared.v      -- shared infra (re-exports SMon)#</li>#
#<li>#plih_rsmon_lecture.v          -- lecture: combined Reader+State
monad, evalRS, agreement theorem#</li>#
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
  1. Finish RMon (Reader monad) and SMon (State monad) first - this
     chapter COMBINES exactly those two effects in one monad.
  2. Read plih_rsmon_lecture.v.
  3. Work plih_rsmon_exercises.v ([Admitted] -> [Qed]).
  4. Check against plih_rsmon_solutions.v.

FOR INSTRUCTORS:
  1. Read plih_rsmon_instructor_guide.v.
  2. Assign the exercises; grade by building the file.
 *)

(** * THE BIG IDEA *)

(**
SMon hid the mutable STORE behind a State monad but left the ENVIRONMENT
an explicit argument.  RMon hid a read-only context behind a Reader
monad.  This chapter puts BOTH effects in one monad:

  RS E S A := E -> S -> option (A * S)

- the READER part (environment [E], read-only): [askRS] reads it,
  [localRS g m] runs [m] under [g e] (used to extend it);
- the STATE part (store [S], mutable): [getRS] reads it, [putRS] replaces
  it - and only the store is returned, since the environment never
  changes;
- [retRS]/[bindRS]/[failRS] are the monad core, and [bindRS] threads
  BOTH resources at once.

The interpreter [evalRS] then carries NEITHER the environment nor the
store explicitly.  The headline is AGREEMENT:

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
  - the COMBINED monad [RS] with [askRS]/[localRS] AND [getRS]/[putRS]
    over one [bindRS];
  - the interpreter [evalRS] hiding BOTH env and store, and its wrapper
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
  [evalRS_agrees]                -- HEADLINE: monadic = explicit (S5)
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
(RSMon) - the essence of MONAD TRANSFORMERS, where each effect
contributes its own operations to a shared [bind].  A natural extension
adds a third layer - Either for descriptive error messages - so the
interpreter reads its environment, mutates its store, AND reports typed
failures, all through one monad.
 *)
