(**
PLIH in Rocq: TRec (Typed Recursion) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in TRec/):
#<ol>#
#<li>#plih_rocq_trec_shared.v      -- shared infra (re-exports TFun)#</li>#
#<li>#plih_trec_lecture.v          -- lecture: typed [Fix], recursion#</li>#
#<li>#plih_trec_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_trec_solutions.v        -- complete solutions#</li>#
#<li>#plih_trec_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_trec_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//types/3-Typed-Recursion.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Finish Typed Functions (TFun) first - this chapter is that typed language plus one new form, [Fix].#</li>#
#<li>#Read plih_trec_lecture.v.#</li>#
#<li>#Work plih_trec_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_trec_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_trec_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
Typing killed recursion: the Y/Z combinators of the Rec chapter relied
on self-application [x x], which does not type-check, so the simply
typed language of TFun has _no_ recursion at all - and in exchange it is
_strongly normalizing_ (every well-typed term terminates).

This chapter buys recursion back with a _primitive_ typed [Fix]:
  - _Typing:_ if [f : T -> T] then [Fix f : T].
  - _Evaluation:_ [Fix f] unfolds by substituting the whole recursion
    [Fix (Lambda i t b)] back in for the recursive-call parameter [i] -
    "fix installs what the recursive call means", it does not step once.
  - _Result:_ factorial and summation are now well-typed and _run_.

_The bargain_, stated honestly and machine-checked:
  - type _safety_ is _kept_ - self-application is still rejected, [Fix] is
    the only loop and it is a deliberate, well-typed one;
  - _normalization_ is _given up_ - [loopT = Fix (\x:Nat. x)] is well-typed
    ([TNum]) yet _diverges_, so [evalM] is genuinely partial again and the
    fuel is a necessity, not a convenience.
 *)

(** * THE ARC OF THE COURSE SO FAR *)

(**
  Func / Rec (untyped)     : can get _stuck_   and can _diverge_
  TFun (simply typed)      : neither - _total_ and safe, but _no_ recursion
  TRec (typed + [Fix])     : _safe_ (no stuck terms) but non-total again

[Fix] trades the normalization guarantee for Turing power, while the
type system still rules out every stuck (type-error) program.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [TFBAEC], [subst]   -- typed syntax with [Fix]; term substitution (S2)
  [typeof]/[typecheck]-- checker with the [Fix] rule (S3)
  [evalM]/[eval]      -- strict interpreter; [Fix] via [subst] (S4)
  [evalM_mono]        -- fuel monotonicity, now with a [Fix] case (S5)
  [factGen]/[fact], [sumGen]/[sum] -- typed recursive programs (S6)
  [run_fact5] : 5! = 120,  [run_sum5] : 0..5 = 15
  [ill_selfApp], [ill_fix_mismatch] -- safety kept (S7)
  [loopT], [loopT_diverges]         -- normalization lost (S7)
  [iszero_yields_bool], [mult_yields_num] -- canonical-forms slices (S8)
  concrete syntax     -- two notations (Section 9): TFun's type grammar
    [<[ Nat -> Bool ]>] and term grammar [<{ ... }>], extended with the
    prefix [fix f] (exercises 11-14)
 *)

(** * WHERE THIS GOES NEXT *)

(**
With a type-safe recursive language in hand, the course turns to
structuring the interpreter itself as a _monad_ (Reader/Either), and then
to _state_.
 *)
