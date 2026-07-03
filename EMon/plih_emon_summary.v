(**
 * PLIH in Rocq: EMon (Reader+Either Monad) Module
 * Complete Summary and Organization
 *
 * Documentation only - no Rocq code, so this file compiles trivially.
 *
 * FILES (in EMon/):
 *   1. plih_rocq_emon_shared.v      -- shared infra (re-exports RMon)
 *   2. plih_emon_lecture.v          -- lecture: Reader+Either type checker
 *   3. plih_emon_exercises.v        -- student problem set (Admitted stubs)
 *   4. plih_emon_solutions.v        -- complete solutions
 *   5. plih_emon_instructor_guide.v -- teaching guide
 *   6. plih_emon_summary.v          -- this file
 *
 * Source chapter (PLIH, Haskell) - a placeholder page, so we develop the
 * standard content ourselves:
 *   https://ku-sldg.github.io/plih//types/6-Reader-And-Either.html
 *)

(* ================================================================ *)
(* QUICK START                                                      *)
(* ================================================================ *)

(**
 * FOR STUDENTS:
 *   1. Do RMon (the Reader monad) first - this chapter adds error
 *      messages on top of it.
 *   2. Read plih_emon_lecture.v.
 *   3. Work plih_emon_exercises.v ([Admitted] -> [Qed]).
 *   4. Check against plih_emon_solutions.v.
 *
 * FOR INSTRUCTORS:
 *   1. Read plih_emon_instructor_guide.v.
 *   2. Assign the exercises; grade by building the file.
 *)

(* ================================================================ *)
(* THE BIG IDEA                                                     *)
(* ================================================================ *)

(**
 * RMon's Reader monad hid the context but failed with a bare [None] - no
 * reason given.  Stacking the EITHER monad on top yields a computation
 * [RE E A = E -> string + A] that READS a context and either FAILS WITH A
 * MESSAGE ([inl msg]) or SUCCEEDS ([inr a]).  The checker [typeofE] uses
 * [throwE "..."] at each failure, so a rejected program explains itself.
 *
 * Crucially, the richer checker decides EXACTLY the same programs:
 *
 *     forget (typeofE e ctx) = typeof ctx e      ([typeofE_refines])
 *
 * where [forget] erases the message.  The Either layer adds information,
 * not behavior - a REFINEMENT of the plain [option] checker.
 *)

(* ================================================================ *)
(* KEY DEFINITIONS AND RESULTS                                     *)
(* ================================================================ *)

(**
 *   [typeof]/[typecheck]     -- the direct [option] checker (reference)
 *   [RE], [retE], [bindE], [askE], [localE], [throwE], [runE], [;;]
 *   [typeofE]/[typecheckE]   -- the message-carrying checker
 *   [forget]                 -- erase a message: [string + A] -> [option A]
 *   [typeofE_refines]        -- forget (typeofE e ctx) = typeof ctx e
 *   [typecheckE_refines]     -- forget (typecheckE e) = typecheck e
 *)

(* ================================================================ *)
(* THE MONADIC ARC, COMPLETE                                       *)
(* ================================================================ *)

(**
 * RMon: the Reader monad removed the CONTEXT plumbing from the checker.
 * EMon: the Either monad turned SILENT failure into EXPLAINED failure.
 * Both are proven to preserve exactly what the checker decides - style and
 * diagnostics improved, meaning unchanged.  Next in the course: STATE.
 *)
