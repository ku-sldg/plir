(**
 * INSTRUCTOR GUIDE: Teaching the Rec (Untyped Recursion) Section
 *
 * Documentation only - no Rocq code.  Compiles trivially.
 *)

(* ================================================================ *)
(* PART 1: PREREQUISITES                                            *)
(* ================================================================ *)

(**
 * Students should have completed Func: closures ([ClosureV]), the
 * fuel-driven closure interpreter [evalM], fuel monotonicity, the lazy
 * interpreter [evalL] with thunks, and the [omega] divergence example.
 * This chapter is the direct payoff to Func's open question - "we can
 * loop, but can we compute recursively?" - so teach it right after Func,
 * before types.
 *)

(* ================================================================ *)
(* PART 2: THE ARC OF THE LECTURE                                  *)
(* ================================================================ *)

(**
 * 1. THE MISSING PIECE.  Recall from Func: [omega] loops, but FBAE has no
 *    conditional, so a recursive function can never test its argument and
 *    stop.  The fix is a CONDITIONAL.  Add [Boolean], [IsZero], [If]
 *    (and [Mult] for factorial), giving FBAEC.  Stress that [If] runs
 *    ONLY the selected branch - that is what lets recursion bottom out
 *    ([ev_if_lazy_branch] shows the untaken branch is never evaluated).
 *
 * 2. TWO INTERPRETERS, ONE STORY.  Reintroduce the strict [evalM] and
 *    lazy [evalL] from Func, now with the conditional cases.  Nothing
 *    conceptually new here - it is deliberately parallel to Func so the
 *    recursion payoff stands out.  Re-prove fuel monotonicity so students
 *    see the extra cases ([Mult]/[Boolean]/[IsZero]/[If]) are routine.
 *
 * 3. OMEGA -> RECURSION.  The key conceptual move: [omega] is useless
 *    self-application; a FIXPOINT COMBINATOR is the SAME trick
 *    parameterised by the function to iterate.  Introduce Y, then observe
 *    it is a parameterised [omega]: under strict evaluation it diverges.
 *
 * 4. THE ETA-GUARD.  Show WHY strict Y loops (call-by-value forces the
 *    argument [x x] before doing any work) and how Z fixes it by hiding
 *    the self-application behind [\v. x x v], which is a value.  Z is the
 *    call-by-value fixpoint.
 *
 * 5. PAYOFF.  Run summation and factorial to real answers - Z under
 *    strict [evalM], Y under lazy [evalL].  This is the moment the course
 *    delivers on "functions are enough for recursion."
 *)

(* ================================================================ *)
(* PART 3: COMMON PITFALLS                                          *)
(* ================================================================ *)

(**
 * - "Why doesn't plain Y work?"  Because [evalM] is call-by-value: it
 *   evaluates arguments before entering a function, and Y's argument is
 *   the diverging self-application.  Trace [Y F] one step to make the
 *   infinite regress visible.
 *
 * - LITERAL FUEL ON AN ABSTRACT TERM.  In proofs, [evalM <literal> env e]
 *   with [e] a variable makes the kernel try to unroll [evalM] to that
 *   depth and can blow up.  Keep fuel a VARIABLE in any lemma quantified
 *   over an abstract term (see [ex9_more_fuel]).  A literal fuel is fine
 *   only on a CONCRETE closed term, where evaluation computes to a value
 *   and stops (that is why all the [reflexivity] examples work).
 *
 * - FUEL TOO SMALL.  The recursive examples need enough fuel: [eval] uses
 *   1000.  If a productive example returns [None], the fuel ran out, not
 *   the recursion.  Divergent examples ([omega], strict Y) return [None]
 *   at ANY fuel - use a modest amount (100) to keep proofs fast.
 *
 * - [If] is not strict in both branches.  Emphasise that evaluating both
 *   branches would defeat recursion; only the condition is forced.
 *)

(* ================================================================ *)
(* PART 4: THE EXERCISES                                            *)
(* ================================================================ *)

(**
 * Part 1 (ex1-ex6) - running the interpreters: strict arithmetic and
 *   conditionals, then Z-strict summation/factorial, lazy-Y factorial,
 *   and strict-Y divergence.  All [reflexivity] on concrete terms.
 * Part 2 (ex7-ex8) - value and branch laws; [ex8] needs a [destruct] on
 *   the fuel because the condition needs a step of its own.
 * Part 3 (ex9-ex10) - fuel monotonicity (cite [evalM_mono], keep fuel a
 *   variable) and determinism.
 *
 * Grade by building plih_rec_exercises.v with the [Admitted]s replaced.
 *)

(* ================================================================ *)
(* PART 5: LOOKING AHEAD                                            *)
(* ================================================================ *)

(**
 * The moral: untyped recursion is definable but the language stays
 * partial (Turing powerful).  Types will restore totality/structural
 * evaluation, but they reject Y/Z's self-application - so the Typed
 * Recursion chapter must add a primitive typed [fix].  Foreshadow this so
 * students see why "just use a combinator" stops working once types
 * arrive.
 *)
