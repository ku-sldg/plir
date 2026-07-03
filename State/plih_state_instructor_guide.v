(**
 * INSTRUCTOR GUIDE: Teaching the State (Mutable State) Section
 *
 * Documentation only - no Rocq code.  Compiles trivially.
 *)

(* ================================================================ *)
(* PART 1: PREREQUISITES                                            *)
(* ================================================================ *)

(**
 * Students should have completed Rec: the FBAEC core (arithmetic,
 * [IsZero], [If]), closures and environment evaluation, the fuel-driven
 * interpreter with fuel monotonicity, and the Z fixpoint combinator.
 * This chapter adds the ONE new idea of mutation on top of that machinery,
 * so teach it right after Rec (and before the SMon monad chapter, which
 * cleans up the threading this chapter does by hand).
 *)

(* ================================================================ *)
(* PART 2: THE ARC OF THE LECTURE                                  *)
(* ================================================================ *)

(**
 * 1. WHY A STORE?  Contrast an IMMUTABLE environment (only ever extended)
 *    with genuine mutation.  The key realisation: a written structure
 *    cannot be threaded implicitly the way the read-only environment is.
 *    Introduce the STORE as a heap of cells and the reference-cell forms
 *    [New]/[Deref]/[Assign]/[Seq].  Add locations [LocV] to the values.
 *
 * 2. THREADING THE STORE.  The interpreter now returns a (value, store)
 *    PAIR.  Walk the [Plus] case slowly: evaluate [l] in store [s] to
 *    [(a, s1)], then evaluate [r] in [s1] (NOT [s]!) to [(b, s2)], and
 *    return the sum in [s2].  Stress that even [Id], which changes
 *    nothing, must PASS THE STORE ALONG.  Then [New] (append, fresh
 *    location = old [length]), [Deref] ([nth_error]), [Assign]
 *    ([update_at]), and [Seq] (run for effect, keep the store).
 *
 * 3. IT ACTUALLY MUTATES.  Run the basics: a cell round-trip and a [Seq]
 *    whose first arm's write is visible to the second arm's read - because
 *    the store threaded between them.  This is the moment "assignment"
 *    becomes real.
 *
 * 4. MONOTONICITY, AGAIN.  Re-prove fuel monotonicity.  The statement now
 *    preserves a (value, store) pair, but the proof is Rec's shape with
 *    the store carried along; the new cases ([Seq]/[New]/[Deref]/[Assign])
 *    are routine.  Point out this says nothing terminates - only that
 *    more fuel never changes an answer.
 *
 * 5. MUTABLE VARIABLES = SUGAR.  We never add a mutable-variable
 *    construct: a mutable variable is a NAME bound to a cell.  Define
 *    [MutBind]/[Get]/[SetVar] as elaboration into the core, then show
 *    ALIASING - binding one name to another's LOCATION makes them share a
 *    cell - and contrast with an immutable [Bind] that copies the value.
 *    This is the conceptual payoff: sharing is a property of mutable
 *    state, not of naming.
 *
 * 6. STATE + RECURSION.  Close by combining the two: a Z-combinator loop
 *    ([incTo]/[counterProg]) that accumulates into a shared cell, showing
 *    the store threads correctly through recursive calls.
 *)

(* ================================================================ *)
(* PART 3: COMMON PITFALLS                                          *)
(* ================================================================ *)

(**
 * - THREADING THE WRONG STORE.  The single most common bug (in the
 *   metatheory AND in hand-written interpreters) is passing [s] where you
 *   meant [s1].  It type-checks - both are stores - but silently loses an
 *   effect.  In the monotonicity proof this shows up as a rewrite that
 *   will not fire; make students trace which store each subcall receives.
 *
 * - LOCATIONS vs VALUES.  [New] returns a [LocV], not the stored value;
 *   you must [Deref] to read.  [Assign] returns the value written (a
 *   common convention), while its EFFECT is the updated store.
 *
 * - ALIASING SURPRISES.  Students expect [Bind "a" (Id "r") ...] to make
 *   an independent copy.  It copies the LOCATION, so [a] and [r] alias.
 *   The immutable-[Bind] contrast ([ev_no_aliasing_immutable]) is worth
 *   dwelling on.
 *
 * - LITERAL FUEL ON AN ABSTRACT TERM.  As in every fuel-driven chapter,
 *   keep fuel a VARIABLE in lemmas over abstract terms (see
 *   [ex9_more_fuel]); a literal fuel is fine only on a concrete closed
 *   term, which is why the [reflexivity] examples work.
 *
 * - CBN AND [evalM].  In the monotonicity proof, reduction between the two
 *   rewrites uses [cbn -[evalM]] so the outer [match] on a returned pair
 *   reduces WITHOUT unfolding the [evalM] fixpoint (whose fuel is an
 *   abstract variable and would get stuck).
 *)

(* ================================================================ *)
(* PART 4: THE EXERCISES                                            *)
(* ================================================================ *)

(**
 * Part 1 (ex1-ex5) - running the interpreter: arithmetic, allocation, a
 *   cell round-trip, aliasing, and distinct-cell independence.  All
 *   [reflexivity] on concrete terms.
 * Part 2 (ex6-ex8) - derived forms and value laws; [ex8] needs a [simpl]
 *   then a [rewrite] of the lookup hypothesis.
 * Part 3 (ex9-ex12) - fuel monotonicity (cite [evalM_mono], keep fuel a
 *   variable), determinism, and the two store lemmas [update_at_length]
 *   and [nth_error_snoc].
 *
 * Grade by building plih_state_exercises.v with the [Admitted]s replaced.
 *)

(* ================================================================ *)
(* PART 5: LOOKING AHEAD                                            *)
(* ================================================================ *)

(**
 * The moral: mutation is definable, but hand-threading the store is
 * verbose and error-prone.  The SMon chapter introduces a STATE MONAD
 * that hides the threading, recovering interpreters that read like the
 * pure ones - and proves, via an agreement theorem, that the monadic
 * interpreter computes exactly what this explicit one does.  Foreshadow
 * this so students feel the pain the monad will relieve.
 *)
