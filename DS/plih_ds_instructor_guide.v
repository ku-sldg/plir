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

#<li>#_Section 1: Extend [Ty]._  Add [TUnit], [TProd], [TSum], [TList]
to TRec's [Ty].  Extend [Ty_eqb] structurally; prove [Ty_eqb_refl] by
induction.  Stress: [TUnit] is nullary so its case is [reflexivity] with
no IH needed.  The proof structure mirrors the type's structure exactly.#</li>#

#<li>#_Section 2: Extend [TADS]._  Ten new constructors in four groups.
Show the substitution cases: [SCase] is the only binder-containing new
constructor; [Unit] is atomic.#</li>#

#<li>#_Section 3: Type checker._  Walk through the [Pair]/[Fst]/[Snd]
rules (straightforward), then the [InL]/[InR] rules (the annotation
carries the full sum type), then [SCase] (both branches must return the
same type [R]).  The list rules are analogous to the pair rules.#</li>#

#<li>#_Section 4: Evaluator._  The four new [TVal] constructors.  The
key pedagogical point: there are no [NilV] or [ConsV] constructors.
[Nil] evaluates to [InLV UnitV] and [Cons h t] evaluates to
[InRV (PairV h t)].  List values _are_ sum/product values.  Write this
on the board before showing the code.#</li>#

#<li>#_Sections 5-7: Unit, Products, Sums._  Demonstrate [eval Unit = Some UnitV],
[swapProg], [safeDiv] with [SCase].  Show the type checker catching errors
(mismatched [Cons], mismatched [SCase] branches, [Car] on non-list).#</li>#

#<li>#_Section 8: Lists as Sums of Products._  This is the chapter's
central section.  Write the equation [List A = Unit + (A x List A)] on the
board.  Then show [nil_is_inl] and [cons_is_inr_pair] -- the list values
are literally [InLV UnitV] and [InRV (PairV h t)].  Then show
[scase_on_list]: [SCase] eliminates a list directly (the type checker
rejects this but the evaluator accepts it, proving the representation
is truly shared).  Explain why [TList A] is kept as a distinct type:
unfolding it would require recursive types.#</li>#

#<li>#_Section 9: Polymorphic Lists._  [Nil TBool], [boolList], type
mismatch.  Quick section -- the interesting content is in Section 8.#</li>#

#<li>#_Section 10: Recursive list operations._  [sumList] and [lengthList]
are [Fix] of a generator, word-for-word the same pattern as [fact] in TRec.
Students may find it satisfying that nothing new is needed.#</li>#

#<li>#_Section 11: evalM_mono._  The pattern is identical to TRec, but
the destruct arms are different (seven [TVal] constructors instead of
eight -- no [NilV]/[ConsV]).  The [Car]/[Cdr] cases use a two-step
nested destruct: first on [val] to isolate [InRV iv2], then on [iv2]
to isolate [PairV p1' p2'].  The rewrite via [IH] must happen between
these two destructs, so the goal is simplified before the inner destruct
runs [try discriminate].  Walk through this on the board.#</li>#

#<li>#_Section 12: Concrete syntax._  The type grammar gains [unit],
[*], [+], and [List T]; the term grammar gains [()], and ten new
notations.  Show that [fact] still parses.#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _[TUnit] in [Ty_eqb_refl]._  The new case is [| |] in the induction
    pattern (a nullary constructor with no IH).  The [simpl; try reflexivity]
    closing tactic handles it without any special work.

  - _No [NilV] or [ConsV]._  Students who have seen other PL courses
    expect these constructors.  Emphasize that [TVal] has only seven
    constructors, and that [NilV]/[ConsV] are deliberately absent.
    A common mistake is writing [Some NilV] in an example -- this will
    produce a type error, which is the point.

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

  - _Destruct order in [evalM_mono]._  The seven [TVal] constructors must
    be destructed in declaration order:
    [NumV | BoolV | ClosureV | UnitV | PairV | InLV | InRV].
    The empty slot for [UnitV] (written [| |]) is easily forgotten.
    An off-by-one causes a Rocq error.

  - _Car/Cdr two-step destruct in [evalM_mono]._  After [destruct val],
    only [InRV iv2] survives (discriminate kills the rest).  The [IH]
    rewrite must happen _before_ the inner [destruct iv2], so that the
    goal references [evalM k2] rather than [evalM k] when [try discriminate]
    runs.  The order is: (1) outer destruct, (2) [IH] rewrite, (3) inner
    destruct, (4) [simpl], (5) [exact H].
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex7b) - type checker: all [reflexivity].  Covers [TNum],
  [TProd], [Fst], [TList], [Cons], [IsNil], [InL], [TUnit].

Part 2 (ex8-ex15) - evaluator: all [reflexivity].  Covers [PairV],
  projections, [IsNil] (returns [BoolV false] because the value is [InRV _]),
  [Car], [Cdr] (the tail is [InRV (PairV _ _)]), [InLV], [InRV].
  Stress that ex13 returns [InRV (PairV (NumV 2) (InLV UnitV))], not
  [ConsV (NumV 2) NilV].

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
  - ex28: type-check [doubleList]; [reflexivity].
  - ex29: run [doubleList] on [list123].  The expected value is a
    sum/product tree, not [ConsV _ _].  Students must write out the
    [InRV (PairV _ _)] structure.
  - ex30: run [sumList] on [list123]; [reflexivity].

Part 7 (ex31-ex34) - lists as sums of products:
  - ex31: [eval (Nil TNum) = Some (InLV UnitV)]; [reflexivity].
  - ex32: [eval (Cons (Num 7) (Nil TNum)) = Some (InRV (PairV (NumV 7) (InLV UnitV)))]; [reflexivity].
  - ex33: [SCase] on nil takes the left branch; [reflexivity].
  - ex34: [SCase] on cons takes the right branch, [Fst] extracts the head; [reflexivity].

Part 8 (ex35-ex36) - inductions:
  - ex35 ([Ty_eqb_refl]): ** .  Students write their own version of the
    lecture's proof.  The seven-case induction on [Ty] is good practice;
    [TUnit] closes with [reflexivity] (no IH needed).
  - ex36 ([mono_pair]): ***.  Apply [evalM_mono] with explicit arguments.
    Students must supply the [f1 <= f2] witness; [lia] closes the goal.

Grade by building plih_ds_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: CONNECTIONS TO OTHER CHAPTERS *)

(**
  - _TRec_: TADS is TRec plus four type formers.  Every TRec program
    compiles unchanged in TADS; the shared infrastructure propagates the
    chain [plih_rocq_trec_shared -> plih_rocq_ds_shared].

  - _Data Structures_: the previous DS chapter studied [IntList] and
    [PList A] as _Rocq_ types.  TADS builds analogous structure as
    _object-language_ types.  The [Nil]/[Cons]/[Car]/[Cdr] names are the
    same; now they live inside the interpreted language rather than Rocq
    itself.  The algebraic representation makes explicit what Rocq's [list]
    does implicitly.

  - _Monadic chapters_: the monad arc (RMon through RSEMon) applies
    directly to TADS.  Replacing [TFBAEC] with [TADS] in the monadic
    type-checker would yield a monadic TADS type-checker; the new
    constructors each add one monadic bind.

  - _Type safety_: TADS preserves TRec's type safety.  The list case
    is particularly clean because list values _are_ sum/product values,
    so the canonical-forms lemma for lists reduces to the canonical-forms
    lemmas already proved for sums and products.
 *)
