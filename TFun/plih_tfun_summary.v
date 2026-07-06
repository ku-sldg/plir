(**
PLIH in Rocq: TFun (Typed Functions) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in TFun/):
#<ol>#
#<li>#plih_rocq_tfun_shared.v      -- shared infra (re-exports Func)#</li>#
#<li>#plih_tfun_lecture.v          -- lecture: types, typeof, soundness#</li>#
#<li>#plih_tfun_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_tfun_solutions.v        -- complete solutions#</li>#
#<li>#plih_tfun_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_tfun_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//types/1-Function-Types.html
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Finish Func and Rec first - this chapter reuses closures, the fuel-driven strict interpreter [evalM], fuel monotonicity, and the Booleans/[IsZero]/[If] added in Rec.  It drops the lazy interpreter.#</li>#
#<li>#Read plih_tfun_lecture.v.#</li>#
#<li>#Work plih_tfun_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_tfun_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_tfun_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
The untyped language is Turing powerful: it can loop ([omega]) and it
can get _stuck_ - [Plus (Boolean true) (Num 1)] is nonsense the
interpreter only rejects (as [None]) at run time.  A _static type system_
catches such errors _before_ evaluation.

We add a type language [Ty] (numbers, Booleans, _function_ types) and a
_type checker_ [typeof] - "an interpreter that returns types instead of
values", carrying an identifier->type _context_ just as [evalM] carries a
value environment.  Because a parameter's type cannot be inferred from
an un-applied function, [Lambda] now _ascribes_ it: [Lambda x T b].

The checker _accepts_ good programs and _rejects_ every classic stuck term,
including _self-application_ ([\x. x x]): for [x x] to type-check, [x]
would need type [D] and [D -> R] at once, which no finite type
satisfies.  That is exactly the term at the heart of [omega] and the
Y/Z combinators - so typing rules out non-termination-by-combinator.
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM Func/Rec:
  - closures ([ClosureV]) and environment evaluation;
  - the _fuel_-driven strict interpreter [evalM] and _fuel monotonicity_
    [evalM_mono];
  - Booleans, [IsZero], [If] (from Rec).

NEW HERE:
  - the type language [Ty] = [TNum]/[TBool]/[TArr], with decidable
    equality [Ty_eqb] (proved correct);
  - [Lambda] ascribes its parameter type;
  - the _type checker_ [typeof]/[typecheck];
  - _type soundness_: well-typed programs run to a value of the predicted
    type; canonical-forms slices for the base types.

_Dropped_ (design decision): the lazy interpreter [evalL]/[evalLazy].
From here on the language pairs _one_ strict interpreter with a type
checker.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [Ty], [Ty_eqb]      -- type language + decidable equality (Section 1)
  [Ty_eqb_refl], [Ty_eqb_eq] -- correctness of type equality
  [TFBAEC]            -- typed term syntax (Section 2)
  [typeof]/[typecheck] -- the type checker (Section 3)
  [evalM]/[eval]      -- strict closure interpreter + wrapper (Section 4)
  [evalM_mono]        -- fuel monotonicity (Section 5)
  [inc], [selfApp]    -- sample terms; [selfApp] is the rejected one
  [iszero_yields_bool], [plus_yields_num] -- canonical-forms slices (Sec 7)
  concrete syntax     -- two notations (Section 8): types [<[ Nat -> Bool ]>]
    and terms [<{ ... }>] with the ascribed lambda [lambda ID : T in body],
    the one place a type is written (exercises 13-16)
 *)

(** * WHERE THIS GOES NEXT *)

(**
Typing is now strict enough that _recursion_ is gone: Y/Z relied on
self-application, which no longer type-checks.  The next chapter, Typed
Recursion, adds a primitive typed [fix] to put recursion back
deliberately - and its payoff is _normalization_: every well-typed term
terminates (no divergence, no stuck terms).
 *)
