(**
INSTRUCTOR GUIDE: Teaching the State (Mutable State) Section

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should have completed Rec: the FBAEC core (arithmetic,
[IsZero], [If]), closures and environment evaluation, the fuel-driven
interpreter with fuel monotonicity, and the Z fixpoint combinator.
This chapter adds the _one_ new idea of mutation on top of that machinery,
so teach it right after Rec (and before the SMon monad chapter, which
cleans up the threading this chapter does by hand).
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
#<ol>#
#<li>#_Why a store?_ Contrast an _immutable_ environment (only ever extended) with genuine mutation.  The key realisation: a written structure cannot be threaded implicitly the way the read-only environment is.  Introduce the _store_ as a heap of cells and the reference-cell forms [New]/[Deref]/[Assign]/[Seq].  Add locations [LocV] to the values.#</li>#
#<li>#_Threading the store._ The interpreter now returns a (value, store) _pair_.  Walk the [Plus] case slowly: evaluate [l] in store [s] to [(a, s1)], then evaluate [r] in [s1] (_not_ [s]!) to [(b, s2)], and return the sum in [s2].  Stress that even [Id], which changes nothing, must _pass the store along_.  Then [New] (append, fresh location = old [length]), [Deref] ([nth_error]), [Assign] ([update_at]), and [Seq] (run for effect, keep the store).#</li>#
#<li>#_It actually mutates._ Run the basics: a cell round-trip and a [Seq] whose first arm's write is visible to the second arm's read - because the store threaded between them.  This is the moment "assignment" becomes real.#</li>#
#<li>#_Monotonicity, again._ Re-prove fuel monotonicity.  The statement now preserves a (value, store) pair, but the proof is Rec's shape with the store carried along; the new cases ([Seq]/[New]/[Deref]/[Assign]) are routine.  Point out this says nothing terminates - only that more fuel never changes an answer.#</li>#
#<li>#_Mutable variables = sugar._ We never add a mutable-variable construct: a mutable variable is a _name_ bound to a cell.  Define [MutBind]/[Get]/[SetVar] as elaboration into the core, then show _aliasing_ - binding one name to another's _location_ makes them share a cell - and contrast with an immutable [Bind] that copies the value.  This is the conceptual payoff: sharing is a property of mutable state, not of naming.#</li>#
#<li>#_State + recursion._ Close by combining the two: a Z-combinator loop ([incTo]/[counterProg]) that accumulates into a shared cell, showing the store threads correctly through recursive calls.#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _Threading the wrong store._ The single most common bug (in the
    metatheory _and_ in hand-written interpreters) is passing [s] where you
    meant [s1].  It type-checks - both are stores - but silently loses an
    effect.  In the monotonicity proof this shows up as a rewrite that
    will not fire; make students trace which store each subcall receives.

  - _Locations vs values._ [New] returns a [LocV], not the stored value;
    you must [Deref] to read.  [Assign] returns the value written (a
    common convention), while its _effect_ is the updated store.

  - _Aliasing surprises._ Students expect [Bind "a" (Id "r") ...] to make
    an independent copy.  It copies the _location_, so [a] and [r] alias.
    The immutable-[Bind] contrast ([ev_no_aliasing_immutable]) is worth
    dwelling on.

  - _Literal fuel on an abstract term._ As in every fuel-driven chapter,
    keep fuel a _variable_ in lemmas over abstract terms (see
    [ex9_more_fuel]); a literal fuel is fine only on a concrete closed
    term, which is why the [reflexivity] examples work.

  - _cbn and [evalM]._ In the monotonicity proof, reduction between the two
    rewrites uses [cbn -[evalM]] so the outer [match] on a returned pair
    reduces _without_ unfolding the [evalM] fixpoint (whose fuel is an
    abstract variable and would get stuck).
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex5) - running the interpreter: arithmetic, allocation, a
  cell round-trip, aliasing, and distinct-cell independence.  All
  [reflexivity] on concrete terms.
Part 2 (ex6-ex8) - derived forms and value laws; [ex8] needs a [simpl]
  then a [rewrite] of the lookup hypothesis.
Part 3 (ex9-ex12) - fuel monotonicity (cite [evalM_mono], keep fuel a
  variable), determinism, and the two store lemmas [update_at_length]
  and [nth_error_snoc].
Part 4 (ex13-ex16) - concrete syntax (Section 8).  The FBAES notation
  parser: Rec's grammar plus [new e], [! e], [l := e], [a ; b].  All
  [reflexivity].  Emphasize the two precedence facts students trip on:
  [!] binds _tighter_ than [+] (so [! "r" + 1] is [(! "r") + 1]), and [;]
  is the _loosest_, _right_-associative operator (so [a ; b ; c] is
  [a ; (b ; c)]).  Note that [x := e] and [! x] _are_ the mutable-variable
  operations from Section 6 - no separate sugar is needed.

Grade by building plih_state_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: LOOKING AHEAD *)

(**
The moral: mutation is definable, but hand-threading the store is
verbose and error-prone.  The SMon chapter introduces a _state monad_
that hides the threading, recovering interpreters that read like the
pure ones - and proves, via an agreement theorem, that the monadic
interpreter computes exactly what this explicit one does.  Foreshadow
this so students feel the pain the monad will relieve.
 *)
