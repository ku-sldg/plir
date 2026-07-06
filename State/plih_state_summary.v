(**
PLIH in Rocq: State (Mutable State) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in State/):
#<ol>#
#<li>#plih_rocq_state_shared.v      -- shared infra (re-exports Rec) + the store plumbing [update_at]#</li>#
#<li>#plih_state_lecture.v          -- lecture: cells, store threading, mutable vars, state + recursion#</li>#
#<li>#plih_state_exercises.v        -- student problem set (Admitted stubs)#</li>#
#<li>#plih_state_solutions.v        -- complete solutions#</li>#
#<li>#plih_state_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_state_summary.v          -- this file#</li>#
#</ol>#

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//state/
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Finish the Rec chapter first - this chapter reuses FBAEC's arithmetic, conditional, closures, the fuel-driven interpreter, and the Z combinator, and adds mutation on top.#</li>#
#<li>#Read plih_state_lecture.v.#</li>#
#<li>#Work plih_state_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_state_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_state_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEA *)

(**
Every earlier language had _immutable_ bindings: an environment only ever
grows, a stored value never changes.  _Mutable state_ needs a second
structure - a _store_ (a heap of reference cells) - that can be _read and
written_.  Because it is written, the store cannot be threaded implicitly
like the read-only environment: the interpreter must take a store _in_ and
hand a possibly-changed store back _out_, so it returns a (value, store)
_pair_ and passes each subexpression the store its predecessor left.

The primitive is the _reference cell_:
  - [New e]      allocate a fresh cell, return its _location_;
  - [Deref e]    read the cell a location points to;
  - [Assign l e] overwrite that cell;
  - [Seq a b]    run [a] for its store-effect, then [b].

_Mutable variables_ are then just a _derived form_ - a name bound to a cell
([MutBind]/[Get]/[SetVar] = sugar over [New]/[Deref]/[Assign]) - and
_aliasing_ (two names, one cell) falls out for free, something immutable
[Bind] can never express.
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM Rec:
  - the FBAEC core (arithmetic, [IsZero], [If], closures);
  - _fuel_-driven partial interpretation and _fuel monotonicity_;
  - the Z fixpoint combinator for recursion.

NEW HERE:
  - [FBAES] = FBAEC + [Seq]/[New]/[Deref]/[Assign];
  - locations [LocV] in the value domain, and the [Store];
  - the _store-threading_ interpreter returning (value, store);
  - mutable variables as a derived form, and _aliasing_;
  - the store plumbing [update_at] with its length/read lemmas.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  [FBAES]        -- syntax (Section 1)
  [RVal]/[Store] -- values (with [LocV]) and the store (Section 2)
  [evalM]/[eval] -- store-threading interpreter + wrapper (Section 3)
  [evalM_mono]   -- fuel monotonicity, preserving the store (Section 5)
  [MutBind]/[Get]/[SetVar] -- mutable variables as sugar (Section 6)
  [ev_aliasing]  -- two names, one cell (Section 6)
  [Zc]/[incTo]/[counterProg] -- state meets recursion (Section 7)
  [update_at], [update_at_length], [nth_error_snoc] -- store plumbing
  concrete syntax -- FBAES notation parser (Section 8): Rec's grammar
    plus [new e], [! e], [l := e], [a ; b] (exercises 13-16)
 *)

(** * WHERE THIS GOES NEXT *)

(**
The explicit store-threading works but is _painful_: every case names
intermediate stores [s1], [s2], ... and threads them by hand, and a
single wrong store variable is a silent bug the types will not catch.
The follow-on SMon chapter packages the threading into a _state monad_
([State S A := S -> option (A * S)] with [get]/[put]), so the
interpreter reads like the pure ones again - and an agreement theorem
shows the monadic version computes exactly what this one does.
 *)
