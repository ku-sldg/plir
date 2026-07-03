(**
 * PLIH in Rocq: RSEMon (Reader+State+Either Monad) Module
 * Complete Summary and Organization
 *
 * Documentation only - no Rocq code, so this file compiles trivially.
 *
 * FILES (in RSEMon/):
 *   1. plih_rocq_rsemon_shared.v      -- shared infra (re-exports RSMon)
 *   2. plih_rsemon_lecture.v          -- lecture: three-effect monad,
 *                                        evalRSE, refinement theorem
 *   3. plih_rsemon_exercises.v        -- student problem set (Admitted stubs)
 *   4. plih_rsemon_solutions.v        -- complete solutions
 *   5. plih_rsemon_instructor_guide.v -- teaching guide
 *   6. plih_rsemon_summary.v          -- this file
 *
 * Source idea (PLIH, Haskell): combining effects / monad transformers
 *   https://ku-sldg.github.io/plih//state/
 *)

(* ================================================================ *)
(* QUICK START                                                      *)
(* ================================================================ *)

(**
 * FOR STUDENTS:
 *   1. Finish RMon, EMon, SMon, and RSMon first - this capstone stacks
 *      ALL of their effects (Reader + State + Either) in one monad.
 *   2. Read plih_rsemon_lecture.v.
 *   3. Work plih_rsemon_exercises.v ([Admitted] -> [Qed]).
 *   4. Check against plih_rsemon_solutions.v.
 *
 * FOR INSTRUCTORS:
 *   1. Read plih_rsemon_instructor_guide.v.
 *   2. Assign the exercises; grade by building the file.
 *)

(* ================================================================ *)
(* THE BIG IDEA                                                     *)
(* ================================================================ *)

(**
 * RSMon combined a Reader (environment) and a State (store) but still
 * failed SILENTLY ([None]).  EMon showed an Either layer replaces silent
 * failure with a descriptive MESSAGE, and that the refined version REFINES
 * the plain one.  This capstone stacks all three:
 *
 *   RSE E S A := E -> S -> sum string (A * S)
 *
 * - READER: [askRSE] reads the environment, [localRSE] extends it;
 * - STATE: [getRSE] reads the store, [putRSE] replaces it;
 * - EITHER: [throwRSE] raises a message, and [bindRSE] short-circuits on
 *   the first error while threading the environment and store otherwise.
 *
 * The interpreter [evalRSE] carries no resource by hand and reports a
 * descriptive message at every stuck point (including running out of
 * fuel).  The headline is REFINEMENT:
 *
 *   forget (evalRSE fuel e env s) = evalM fuel env s e
 *
 * erasing the message recovers exactly the explicit option-valued answer -
 * the messages add information without changing behavior.
 *)

(* ================================================================ *)
(* WHAT CARRIES OVER, WHAT IS NEW                                  *)
(* ================================================================ *)

(**
 * CARRIES OVER:
 *   - the reference-cell language [FBAES] and the explicit interpreter
 *     [evalM]/[eval] (from State);
 *   - the store plumbing [update_at] / [nth_error_snoc];
 *   - Reader ops (RMon/RSMon), State ops (SMon/RSMon), and the Either
 *     [forget]/refinement idea (EMon).
 *
 * NEW HERE:
 *   - the THREE-effect monad [RSE] with [askRSE]/[localRSE], [getRSE]/
 *     [putRSE], and [throwRSE] over one [bindRSE];
 *   - the interpreter [evalRSE] with descriptive messages, and [evalRSErr];
 *   - the REFINEMENT theorem [evalRSE_refines] (+ [evalRSErr_refines]) and
 *     the effect-interaction lemmas.
 *)

(* ================================================================ *)
(* KEY DEFINITIONS AND RESULTS                                     *)
(* ================================================================ *)

(**
 *   [FBAES]/[RVal]/[Store]/[evalM] -- reference language + interpreter (S1)
 *   [RSE]/[retRSE]/[bindRSE]/[askRSE]/[localRSE]/[getRSE]/[putRSE]/
 *     [throwRSE]/[runRSE]          -- the three-effect monad (Section 2)
 *   [forget]                       -- erase the message (Section 2)
 *   [evalRSE]/[evalRSErr]          -- the monadic interpreter + wrapper (S3)
 *   [evalRSE_refines]              -- HEADLINE: forget o monadic = explicit
 *   [evalRSErr_refines]            -- lifted to the top-level wrappers
 *   [left_id_RSE], [throw_short_circuits], [channels_independent] -- laws
 *)

(* ================================================================ *)
(* WHERE THIS GOES NEXT                                            *)
(* ================================================================ *)

(**
 * This is the end of the monad arc: Reader (RMon), Either (EMon), State
 * (SMon), Reader+State (RSMon), and finally Reader+State+Either (RSEMon).
 * Each effect contributes its own operations to one shared [bind], and the
 * interpreter reads like a plain recursive definition while an environment,
 * a store, and an error channel are all threaded - provably - underneath.
 * That is the essence of MONAD TRANSFORMERS.  Further layers (a Writer for
 * a trace/log, a nondeterminism list monad) slot in the same way.
 *)
