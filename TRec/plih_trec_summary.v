(**
 * PLIH in Rocq: TRec (Typed Recursion) Module
 * Complete Summary and Organization
 *
 * Documentation only - no Rocq code, so this file compiles trivially.
 *
 * FILES (in TRec/):
 *   1. plih_rocq_trec_shared.v      -- shared infra (re-exports TFun)
 *   2. plih_trec_lecture.v          -- lecture: typed [Fix], recursion
 *   3. plih_trec_exercises.v        -- student problem set (Admitted stubs)
 *   4. plih_trec_solutions.v        -- complete solutions
 *   5. plih_trec_instructor_guide.v -- teaching guide
 *   6. plih_trec_summary.v          -- this file
 *
 * Source chapter (PLIH, Haskell):
 *   https://ku-sldg.github.io/plih//types/3-Typed-Recursion.html
 *)

(* ================================================================ *)
(* QUICK START                                                      *)
(* ================================================================ *)

(**
 * FOR STUDENTS:
 *   1. Finish Typed Functions (TFun) first - this chapter is that typed
 *      language plus one new form, [Fix].
 *   2. Read plih_trec_lecture.v.
 *   3. Work plih_trec_exercises.v ([Admitted] -> [Qed]).
 *   4. Check against plih_trec_solutions.v.
 *
 * FOR INSTRUCTORS:
 *   1. Read plih_trec_instructor_guide.v.
 *   2. Assign the exercises; grade by building the file.
 *)

(* ================================================================ *)
(* THE BIG IDEA                                                     *)
(* ================================================================ *)

(**
 * Typing killed recursion: the Y/Z combinators of the Rec chapter relied
 * on self-application [x x], which does not type-check, so the simply
 * typed language of TFun has NO recursion at all - and in exchange it is
 * STRONGLY NORMALIZING (every well-typed term terminates).
 *
 * This chapter buys recursion back with a PRIMITIVE typed [Fix]:
 *   - TYPING: if [f : T -> T] then [Fix f : T].
 *   - EVALUATION: [Fix f] unfolds by substituting the whole recursion
 *     [Fix (Lambda i t b)] back in for the recursive-call parameter [i] -
 *     "fix installs what the recursive call means", it does not step once.
 *   - RESULT: factorial and summation are now well-typed and RUN.
 *
 * THE BARGAIN, stated honestly and machine-checked:
 *   - type SAFETY is KEPT - self-application is still rejected, [Fix] is
 *     the only loop and it is a deliberate, well-typed one;
 *   - NORMALIZATION is GIVEN UP - [loopT = Fix (\x:Nat. x)] is well-typed
 *     ([TNum]) yet DIVERGES, so [evalM] is genuinely partial again and the
 *     fuel is a necessity, not a convenience.
 *)

(* ================================================================ *)
(* THE ARC OF THE COURSE SO FAR                                    *)
(* ================================================================ *)

(**
 *   Func / Rec (untyped)     : can get STUCK   and can DIVERGE
 *   TFun (simply typed)      : neither - TOTAL and safe, but NO recursion
 *   TRec (typed + [Fix])     : SAFE (no stuck terms) but non-total again
 *
 * [Fix] trades the normalization guarantee for Turing power, while the
 * type system still rules out every stuck (type-error) program.
 *)

(* ================================================================ *)
(* KEY DEFINITIONS AND RESULTS                                     *)
(* ================================================================ *)

(**
 *   [TFBAEC], [subst]   -- typed syntax with [Fix]; term substitution (S2)
 *   [typeof]/[typecheck]-- checker with the [Fix] rule (S3)
 *   [evalM]/[eval]      -- strict interpreter; [Fix] via [subst] (S4)
 *   [evalM_mono]        -- fuel monotonicity, now with a [Fix] case (S5)
 *   [factGen]/[fact], [sumGen]/[sum] -- typed recursive programs (S6)
 *   [run_fact5] : 5! = 120,  [run_sum5] : 0..5 = 15
 *   [ill_selfApp], [ill_fix_mismatch] -- safety kept (S7)
 *   [loopT], [loopT_diverges]         -- normalization lost (S7)
 *   [iszero_yields_bool], [mult_yields_num] -- canonical-forms slices (S8)
 *)

(* ================================================================ *)
(* WHERE THIS GOES NEXT                                            *)
(* ================================================================ *)

(**
 * With a type-safe recursive language in hand, the course turns to
 * structuring the interpreter itself as a MONAD (Reader/Either), and then
 * to STATE.
 *)
