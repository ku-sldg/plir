(**
PLIH in Rocq: State (Mutable State) Module
Complete Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in State/):
  1. plih_rocq_state_shared.v      -- shared infra (re-exports Rec) +
                                      the store plumbing [update_at]
  2. plih_state_lecture.v          -- lecture: cells, store threading,
                                      mutable vars, state + recursion
  3. plih_state_exercises.v        -- student problem set (Admitted stubs)
  4. plih_state_solutions.v        -- complete solutions
  5. plih_state_instructor_guide.v -- teaching guide
  6. plih_state_summary.v          -- this file

Source chapter (PLIH, Haskell):
  https://ku-sldg.github.io/plih//state/
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
  1. Finish the Rec chapter first - this chapter reuses FBAEC's
     arithmetic, conditional, closures, the fuel-driven interpreter,
     and the Z combinator, and adds mutation on top.
  2. Read plih_state_lecture.v.
  3. Work plih_state_exercises.v ([Admitted] -> [Qed]).
  4. Check against plih_state_solutions.v.

FOR INSTRUCTORS:
  1. Read plih_state_instructor_guide.v.
  2. Assign the exercises; grade by building the file.
 *)

(** * THE BIG IDEA *)

(**
Every earlier language had IMMUTABLE bindings: an environment only ever
grows, a stored value never changes.  MUTABLE STATE needs a second
structure - a STORE (a heap of reference cells) - that can be READ AND
WRITTEN.  Because it is written, the store cannot be threaded implicitly
like the read-only environment: the interpreter must take a store IN and
hand a possibly-changed store back OUT, so it returns a (value, store)
PAIR and passes each subexpression the store its predecessor left.

The primitive is the REFERENCE CELL:
  - [New e]      allocate a fresh cell, return its LOCATION;
  - [Deref e]    read the cell a location points to;
  - [Assign l e] overwrite that cell;
  - [Seq a b]    run [a] for its store-effect, then [b].

MUTABLE VARIABLES are then just a DERIVED FORM - a name bound to a cell
([MutBind]/[Get]/[SetVar] = sugar over [New]/[Deref]/[Assign]) - and
ALIASING (two names, one cell) falls out for free, something immutable
[Bind] can never express.
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM Rec:
  - the FBAEC core (arithmetic, [IsZero], [If], closures);
  - FUEL-driven partial interpretation and FUEL MONOTONICITY;
  - the Z fixpoint combinator for recursion.

NEW HERE:
  - [FBAES] = FBAEC + [Seq]/[New]/[Deref]/[Assign];
  - locations [LocV] in the value domain, and the [Store];
  - the STORE-THREADING interpreter returning (value, store);
  - mutable variables as a derived form, and ALIASING;
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
 *)

(** * WHERE THIS GOES NEXT *)

(**
The explicit store-threading works but is PAINFUL: every case names
intermediate stores [s1], [s2], ... and threads them by hand, and a
single wrong store variable is a silent bug the types will not catch.
The follow-on SMon chapter packages the threading into a STATE MONAD
([State S A := S -> option (A * S)] with [get]/[put]), so the
interpreter reads like the pure ones again - and an agreement theorem
shows the monadic version computes exactly what this one does.
 *)
