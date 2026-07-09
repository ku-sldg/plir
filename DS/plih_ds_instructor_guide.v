(**
INSTRUCTOR GUIDE: Teaching the TADS (Typed Algebraic Data Structures) Chapter

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
Students should arrive with:
#<ol>#
#<li>#TRec: [Fix], [typeof], [evalM], [TVal]/[ClosureV], [evalM_mono].  TADS is a direct extension of that language.#</li>#
#<li>#Comfort with [induction], [destruct], [rewrite], [lia], [discriminate].#</li>#
#<li>#The [Env]/[extend]/[lookup] machinery - carried in via [plih_rocq_ds_shared].#</li>#
#</ol>#

The chapter is self-contained given TRec: every definition either copies
TRec verbatim (changing the type from [TFBAEC] to [TADS]) or adds one
new case.  Students who have worked through TRec will recognize the pattern
immediately.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
#<ol>#
#<li>#_Motivate the gap._  TRec values are flat: numbers, Booleans, and
closures.  There is no way to return two values from a function, or to
say "this computation might fail with an error message".  Algebraic types
fill both gaps.#</li>#

#<li>#_Section 1: Extend [Ty]._  Add [TProd], [TSum], [TList] to TRec's
[Ty].  Extend [Ty_eqb] structurally; prove [Ty_eqb_refl] by induction.
Stress: the proof structure mirrors the type's structure exactly.#</li>#

#<li>#_Section 2: Extend [TADS]._  Nine new constructors in three groups.
Show the substitution cases: [SCase] is the only binder-containing new
constructor.#</li>#

#<li>#_Section 3: Type checker._  Walk through the [Pair]/[Fst]/[Snd]
rules (straightforward), then the [InL]/[InR] rules (the annotation
carries the full sum type), then [SCase] (both branches must return the
same type [R]).  The list rules are analogous to the pair rules.#</li>#

#<li>#_Section 4: Evaluator._  The five new [TVal] constructors.  [NilV]
has no arguments - stress this when discussing the [evalM_mono] destruct
pattern.  [Car] and [Cdr] return [None] on [NilV] (safe failure).#</li>#

#<li>#_Sections 5-8: Examples._  Demonstrate [swapProg], [safeDiv] with
[SCase], [list123], and [boolList].  Show the type checker catching errors
(mismatched [Cons], mismatched [SCase] branches, [Car] on non-list).#</li>#

#<li>#_Section 9: Recursive list operations._  [sumList] and [lengthList]
are [Fix] of a generator, word-for-word the same pattern as [fact] in TRec.
Students may find it satisfying that nothing new is needed.#</li>#

#<li>#_Section 10: evalM_mono._  This is the hardest proof.  The pattern
is identical to TRec, but the destruct arms are wider (eight [TVal]
constructors, including [NilV] with no fields).  Consider walking through
the [Plus] case on the board to show the eight-constructor pattern, then
assigning the rest.#</li>#

#<li>#_Section 11: Concrete syntax._  The type grammar gains [*], [+],
and [List T]; the term grammar gains ten new notations.  Show that [fact]
still parses, and demonstrate [pair]/[car]/[inl]/[case ... of] on concrete
programs.#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _[NilV] has no arguments._  In the [evalM_mono] destruct pattern, the
    branch for [NilV] is written as [| |] (two pipes with nothing between
    them) inside the bracket-list notation.  Students often write [| n |]
    by analogy with other constructors.  Check this carefully.

  - _[InL]/[InR] require a [TSum] annotation._  [InL TNum (Num 5)] is
    ill-typed because [TNum] is not a sum type.  Students often forget
    the annotation is the _whole_ sum type, not just the relevant component.

  - _[SCase] names must be fresh._  If the scrutinee is [InL (TSum A B) e]
    and the case binder is [x], then inside [e1] the name [x] refers to
    the injected value.  Make sure students do not accidentally shadow an
    outer binding.

  - _[Cons] homogeneity._  [Cons (Num 1) (Nil TBool)] is rejected because
    the element types disagree.  [Ty_eqb] in the [Cons] branch catches
    this.

  - _[+] notation overload._  The tads_scope's [+] in the [ty] custom
    entry means [TSum], not [Nat.add].  In a term context [<{ ... }>], [+]
    means [Plus].  Since these are separate custom entries there is no
    conflict, but students may be confused when writing types that contain
    [+] inside term brackets.

  - _Destruct patterns in [evalM_mono]._  The order of the eight [TVal]
    constructors must match the [Inductive TVal] declaration exactly:
    [NumV | BoolV | ClosureV | PairV | InLV | InRV | NilV | ConsV].
    An off-by-one or a missing constructor causes a Rocq error.
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex7) - type checker: all [reflexivity].  Covers [TNum],
  [TProd], [Fst], [TList], [Cons], [IsNil], [InL].

Part 2 (ex8-ex15) - evaluator: all [reflexivity].  Covers [PairV],
  projections, [IsNil], [Car], [Cdr], [InLV], [InRV].

Part 3 (ex16-ex21) - typing judgements:
  - ex16-ex17: [reflexivity].
  - ex18-ex19: ill-typed examples return [None]; [reflexivity].
  - ex20: [SCase] with matching types; [reflexivity].
  - ex21: [SCase] with mismatched types; [reflexivity].

Part 4 (ex22-ex24) - products:
  - ex22-ex23: define and run [tripleFirst] (nested [Fst]).
  - ex24: swap function type; [reflexivity].

Part 5 (ex25-ex27) - sums:
  - ex25-ex27: [safeHead] using [If]/[IsNil]/[InL]/[InR].  Students must
    trace through how [typeof] handles [InL] and [InR] with annotations.

Part 6 (ex28-ex30) - lists:
  - ex28-ex29: [doubleList] uses [Car]/[Cdr]/[Mult] inside [Fix].
    The generator pattern is identical to [sumListGen] and [lengthGen].
  - ex30: run [sumList] on [list123]; [reflexivity].

Part 7 (ex31-ex32) - inductions:
  - ex31 ([Ty_eqb_refl]): ★★.  Students write their own version of the
    lecture's proof.  The six-case induction on [Ty] is good practice.
  - ex32 ([mono_pair]): ★★★.  Apply [evalM_mono] with explicit arguments.
    Students must supply the [f1 <= f2] witness; [lia] closes the goal.
    This exercises understanding of how [evalM_mono] works.

Grade by building plih_ds_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: CONNECTIONS TO OTHER CHAPTERS *)

(**
  - _TRec_: TADS is TRec plus three type formers.  Every TRec program
    compiles unchanged in TADS; the shared infrastructure propagates the
    chain [plih_rocq_trec_shared -> plih_rocq_ds_shared].

  - _Data Structures_: the previous DS chapter studied [IntList] and
    [PList A] as _Rocq_ types.  TADS builds analogous structure as
    _object-language_ types.  The [Nil]/[Cons]/[Car]/[Cdr] names are the
    same; now they live inside the interpreted language rather than Rocq
    itself.

  - _Monadic chapters_: the monad arc (RMon through RSEMon) applies
    directly to TADS.  Replacing [TFBAEC] with [TADS] in the monadic
    type-checker would yield a monadic TADS type-checker; the new
    constructors each add one monadic bind.

  - _Type safety_: TADS preserves TRec's type safety.  The new
    constructors each satisfy canonical forms and inversion lemmas by
    straightforward case analysis.  A formal progress-preservation proof
    is natural advanced material after this chapter.
 *)
