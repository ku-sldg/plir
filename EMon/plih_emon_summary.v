(**
PLIH in Rocq: EMon (Reader+Either Monad) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in EMon/):
#<ol>#
#<li>#plih_rocq_emon_shared.v      -- shared infra (re-exports RMon)#</li>#
#<li>#plih_emon_lecture.v          -- lecture: Reader+Either type checker#</li>#
#<li>#plih_emon_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_emon_solutions.v        -- complete solutions#</li>#
#<li>#plih_emon_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_emon_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell) - a placeholder page, so we develop the
standard content ourselves:
  https://ku-sldg.github.io/plih//types/6-Reader-And-Either.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Do RMon (the Reader monad) first - this chapter adds error messages on top of it.#</li>#
#<li>#Read plih_emon_lecture.v.#</li>#
#<li>#Work plih_emon_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_emon_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_emon_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
RMon's Reader monad hid the context but failed with a bare [None] - no
reason given.  Stacking the _Either monad_ on top yields a computation
[RE E A = E -> string + A] that _reads_ a context and either _fails with a
message_ ([inl msg]) or _succeeds_ ([inr a]).  The checker [typeofE] uses
[throwE "..."] at each failure, so a rejected program explains itself.

Crucially, the richer checker decides _exactly_ the same programs:

    forget (typeofE e ctx) = typeof ctx e      ([typeofE_refines])

where [forget] erases the message.  The Either layer adds information,
not behavior - a _refinement_ of the plain [option] checker.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [typeof]/[typecheck]     -- the direct [option] checker (reference)
  [RE], [retE], [bindE], [askE], [localE], [throwE], [runE], [;;]
  [typeofE]/[typecheckE]   -- the message-carrying checker
  [forget]                 -- erase a message: [string + A] -> [option A]
  [typeofE_refines]        -- forget (typeofE e ctx) = typeof ctx e
  [typecheckE_refines]     -- forget (typecheckE e) = typecheck e
  concrete syntax          -- TRec's type grammar [<[ Nat -> Bool ]>] and
    term grammar [<{ ... }>] (ascribed lambda + prefix [fix]), read via
    [typecheckE] - [inr] type / [inl] message (Section 6, exercises 9-11)
 *)

(** * THE MONADIC ARC, COMPLETE *)

(**
RMon: the Reader monad removed the _context_ plumbing from the checker.
EMon: the Either monad turned _silent_ failure into _explained_ failure.
Both are proven to preserve exactly what the checker decides - style and
diagnostics improved, meaning unchanged.  Next in the course: _state_.
 *)
