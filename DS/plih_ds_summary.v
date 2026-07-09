(**
PLIH in Rocq: DS (TADS) Module
Typed Algebraic Data Structures - Summary and Organization

Documentation only - no Rocq code, so this file compiles trivially.

FILES (in DS/):
#<ol>#
#<li>#plih_rocq_ds_shared.v      -- shared infra (re-exports plih_rocq_trec_shared)#</li>#
#<li>#plih_ds_lecture.v          -- lecture: TADS language, type checker, evaluator, examples, mono proof, concrete syntax#</li>#
#<li>#plih_ds_exercises.v        -- student problem set (Admitted stubs, 32 exercises)#</li>#
#<li>#plih_ds_solutions.v        -- complete solutions#</li>#
#<li>#plih_ds_instructor_guide.v -- teaching guide#</li>#
#<li>#plih_ds_summary.v          -- this file#</li>#
#</ol>#
 *)

(** * QUICK START *)

(**
FOR STUDENTS:
#<ol>#
#<li>#Read plih_ds_lecture.v.#</li>#
#<li>#Work plih_ds_exercises.v ([Admitted] -> [Qed]).#</li>#
#<li>#Check against plih_ds_solutions.v.#</li>#
#</ol>#

FOR INSTRUCTORS:
#<ol>#
#<li>#Read plih_ds_instructor_guide.v.#</li>#
#<li>#Assign the exercises; grade by building the file.#</li>#
#</ol>#
 *)

(** * THE BIG IDEAS *)

(**
_Algebraic types_ are the foundational vocabulary of typed functional
programming.  Products capture "A _and_ B"; sums capture "A _or_ B".
Lists are the canonical recursive type: a homogeneous sequence built
from a base case ([Nil]) and a step case ([Cons]).

TADS adds all three to TRec's typed-recursion language:
  - [TProd A B]: introduced by [Pair e1 e2], eliminated by [Fst] and [Snd];
  - [TSum A B]:  introduced by [InL T e] or [InR T e], eliminated by [SCase];
  - [TList A]:   introduced by [Nil T] or [Cons e1 e2], eliminated by
                 [Car], [Cdr], and [IsNil].

All three interact cleanly with [Fix]: recursive list operations ([sumList],
[lengthList], [doubleList]) are just [Fix] applied to a generator lambda,
exactly as factorial was in TRec.
 *)

(** * WHAT CARRIES OVER, WHAT IS NEW *)

(**
CARRIES OVER FROM TRec:
  - [TNum], [TBool], [TArr] and all their term forms;
  - [Fix] and the [subst] unfolding mechanism;
  - [typeof]/[typecheck] structure and [tnumBinop];
  - [NumV], [BoolV], [ClosureV] value constructors;
  - [evalM] with fuel, [evalM_mono] proof pattern;
  - Concrete syntax style ([<[ ... ]>] for types, [<{ ... }>] for terms).

NEW HERE:
  - Three new type formers: [TProd], [TSum], [TList];
  - Extended [Ty_eqb] with cases for the new formers;
  - Nine new term constructors: [Pair], [Fst], [Snd], [InL], [InR],
    [SCase], [Nil], [Cons], [Car], [Cdr], [IsNil];
  - Extended [subst] with cases for the new constructors ([SCase] binds
    two names);
  - New typing rules in [typeof] for all nine new constructors;
  - Five new [TVal] constructors: [PairV], [InLV], [InRV], [NilV], [ConsV];
  - Extended [evalM] for all nine new term constructors;
  - [evalM_mono] re-proved with the eight-constructor [TVal] destruct
    pattern;
  - New concrete syntax notations in [tads_scope]: [*], [+], [List T]
    in the type grammar; [pair], [fst], [snd], [inl]/[inr], [case ... of],
    [nil], [cons], [car], [cdr], [isnil] in the term grammar.
 *)

(** * KEY DEFINITIONS AND RESULTS *)

(**
  Types:
    [Ty]       -- [TNum | TBool | TArr | TProd | TSum | TList]
    [Ty_eqb]   -- Boolean equality on [Ty]
    [Ty_eqb_refl], [Ty_eqb_eq], [Ty_eqb_true_iff]  -- correctness lemmas

  Terms:
    [TADS]     -- full term language (TRec + products + sums + lists)
    [subst]    -- capture-naive substitution over [TADS]

  Type checker:
    [Ctx]      -- [Env Ty]
    [typeof]   -- [Ctx -> TADS -> option Ty]
    [typecheck] -- [TADS -> option Ty] (closed terms)

  Values:
    [TVal]     -- [NumV | BoolV | ClosureV | PairV | InLV | InRV | NilV | ConsV]
    [evalM]    -- [nat -> Env TVal -> TADS -> option TVal]
    [eval]     -- [TADS -> option TVal] (1000 fuel, closed)
    [evalM_mono] -- fuel monotonicity

  Examples:
    [swapProg]        -- pair swap using [Bind]/[Fst]/[Snd]
    [safeDiv]         -- safe division returning [TSum TNum TBool]
    [safeDivResult]   -- [SCase] eliminating [safeDiv]'s sum
    [list123]         -- the list [1; 2; 3]
    [boolList]        -- a list of Booleans
    [sumList]         -- [Fix] of [sumListGen]: sum a list of numbers
    [lengthList]      -- [Fix] of [lengthGen]: count list elements
    [factGen]/[fact]  -- factorial from TRec, unchanged
 *)

(** * WHERE THIS GOES NEXT *)

(**
TADS provides the typed vocabulary to discuss _structured_ values.  The
natural sequel is to connect this chapter to the broader PL theory:

  - _Type safety_: well-typed TADS programs never get stuck.  Products
    and sums preserve the progress and preservation properties because
    each typing rule exactly anticipates the evaluator's behavior.

  - _Normalization_: inherited from TRec's non-result - [Fix] can still
    diverge, so TADS is Turing-complete.

  - _Recursive types_: adding a [TRec A] type former (a "mu type") would
    let TADS express its own list type internally, rather than building
    [TList] into the language.  That is the next natural extension.

  - _Monadic interpreters_: the monad arc (RMon, EMon, State, SMon, RSMon,
    RSEMon) applies equally well to TADS - the algebraic types add no new
    monad structure.
 *)
