(**
INSTRUCTOR GUIDE: Teaching the DS (Data Structures) Chapter

Documentation only - no Rocq code.  Compiles trivially.
 *)

(** * PART 1: PREREQUISITES *)

(**
This chapter has no interpreter-chain prerequisites.  It stands alone
as a self-contained introduction to recursive Rocq types, and can be
taught at any point after students are comfortable with:
  - [Fixpoint] definitions and [match] expressions;
  - structural induction (the [induction] tactic);
  - [reflexivity], [simpl], and [rewrite].

Placing it before the typed-language chapters (TFun, TRec) works well:
students arrive at type-checking already fluent with recursive types
and structural induction on data.
 *)

(** * PART 2: THE ARC OF THE LECTURE *)

(**
_Part I — Lists (Sections 1-5):_
#<ol>#
#<li>#_Integer lists from first principles._ Define [IntList] with [Nil]
and [Cons].  Stress that this is exactly LISP's cons cell.  Run
[car]/[cdr]/[isEmpty] on concrete lists with [reflexivity] to build
intuition.#</li>#
#<li>#_Structural operations._ [length] and [append] show the two-case
pattern.  Prove [append_nil_r] by induction (contrast with [append_nil_l]
which is [reflexivity]).  This is often students' first non-trivial
induction proof.#</li>#
#<li>#_Higher-order functions._ Show that [addOne_list] and [double_list]
are the same function except for the per-element operation, then abstract
it as [map].  Repeat for [foldr], [foldl], and [filter].#</li>#
#<li>#_Polymorphic lists._ Ask: why is [map] restricted to [nat -> nat]?
Generalize to [PList A].  Every function carries over with identical
structure.#</li>#
#<li>#_The isomorphism._ Define [intToP]/[pToInt], prove inverses, prove
commutation lemmas.  Central lesson: structure-dependent, not
content-dependent.#</li>#
#</ol>#

_Part II — Algebraic type formers (Sections 6-9):_
#<ol>#
#<li>#_Product types._ [A * B] already appeared in [PList (nat * nat)].
Introduce [fst]/[snd], the [(a, b)] notation, and [prod_eta].  Stress
the counting intuition: [m] values times [n] values = [m * n] pairs.#</li>#
#<li>#_Sum types._ [A + B] is a _choice_.  Introduce [inl]/[inr] and
pattern matching.  The key example is [option A = unit + A]: [None] is
[inl tt] and [Some a] is [inr a].  Prove the isomorphism with case
analysis only (no induction) - good contrast with the list proofs.#</li>#
#<li>#_Records._ Motivate with "products have no documentation."  Show
the [Record] keyword, [{| ... |}] construction, and [.(field)] projection.
Prove [point_eta] (destructs to expose fields) and [Point ≅ nat * nat]
(isomorphism).#</li>#
#<li>#_Sums of products._ The payoff: every [Inductive] is a sum of
products.  Walk through [Shape = nat + (nat * nat)] on the board.
Prove the isomorphism by case analysis.  Connect back to all prior
language types ([FBAE], [FBAEC], etc.): every constructor is a product,
the inductive groups them with [+].#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _[append_nil_l] vs [append_nil_r]._ Students often expect both to be
    [reflexivity].  The asymmetry is because [append] recurses on its
    _first_ argument.  Walk through the [Cons] case by hand.

  - _Implicit vs explicit type arguments._ When [A] is implicit in
    [pmap {A B}], "Cannot infer the implicit argument A" appears when
    Rocq cannot determine the type from context.  Supply explicitly
    ([pmap (A := nat) S xs]) or ensure the context determines the type.

  - _[foldl] vs [foldr] for non-commutative operations._ Subtraction is
    a good example: [foldl Nat.sub 10 (Cons 1 (Cons 2 Nil)) = 7] but
    [foldr Nat.sub 10 (Cons 1 (Cons 2 Nil)) = 9].

  - _[reverse_involutive] without [reverse_append]._ Students get stuck
    because they cannot simplify [reverse (append ...)].  Guide them to
    establish [reverse_append] as a helper first.

  - _[A + B] ambiguity._ The [+] notation is overloaded: [Nat.add] in
    [nat_scope], [sum] in [type_scope].  In a _type position_ Rocq
    automatically uses [type_scope], so [nat + bool] is [sum nat bool].
    In a _term position_, [1 + 2] is [Nat.add 1 2].  If Rocq complains
    about [+] in a type, add [(A + B : Type)] as a hint or open
    [type_scope] locally.

  - _Record field name conflicts._ [Record] field names are global
    definitions (e.g., [px : Point -> nat]).  If two records share a
    field name, the second definition shadows the first.  Use qualified
    names ([Point.px]) or choose distinct field names.

  - _Destructuring [unit] in sum patterns._ In [ex30], the pattern
    [inr (inl _)] works because the wildcard [_] matches [tt].  Students
    can also write [inr (inl tt)] explicitly.  The fully expanded pattern
    [[ [] | [ [] | [] ] ]] in intro style destructs [unit] to its sole
    constructor at each position.
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex8) - running the functions: all [reflexivity] on concrete
  values.  Fast confidence-building; every student should complete these.

Part 2 (ex9-ex12) - structural lemmas:
  - ex9 ([map_length]): standard one-step induction.
  - ex10 ([filter_le_length]): induction + [destruct (p n)] + [lia].
  - ex11 ([reverse_append]): ★★★.  Induction on [xs]; [Cons] case uses
    IH then [append_assoc].  Work this on the board.
  - ex12 ([reverse_involutive]): ★★★.  Cite ex11, then [simpl], then IH.

Part 3 (ex13-ex16) - polymorphic:
  - ex13-ex14: [reflexivity].
  - ex15 ([pmap_length]): parallel of ex9, reinforces structural identity.
  - ex16 ([foldl_commutes]): [revert acc] before induction is the key
    step.  Emphasise: quantifiers over recursively-updated values must
    be generalised before inducting.

Part 4 (ex17-ex20) - products:
  - ex17-ex18: [reflexivity] - [fst]/[snd] on a concrete pair.
  - ex19: [reflexivity] - [swap] on a concrete pair.
  - ex20 ([prod_eta]): [destruct p as [a b]; reflexivity].

Part 5 (ex21-ex26) - sums and records:
  - ex21-ex22: [reflexivity] - [sumToNat] on [inl]/[inr].
  - ex23-ex25: [reflexivity] - [pcar], field projection, [translate].
  - ex26 ([point_eta]): [intros [n m]; reflexivity].  Good parallel
    to [prod_eta]: same proof structure, named vs positional fields.

Part 6 (ex27-ex30) - algebra of types:
  - ex27-ex28: [reflexivity] - [shapeToAlg] on concrete constructors.
  - ex29-ex30 ([Color] isomorphism): ★★★.  Students define [Color] and
    [colorToAlg]/[algToColor] themselves (the definitions are given as
    scaffolding).  ex29: [destruct s] gives three cases, all
    [reflexivity].  ex30: [destruct x as [[] | [[] | []]]] gives three
    [unit + (unit + unit)] cases, all [reflexivity].  The key insight:
    case analysis suffices because [Color] and [unit + (unit + unit)]
    are non-recursive - no induction needed.

Grade by building plih_ds_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: CONNECTIONS TO OTHER CHAPTERS *)

(**
  - [Env A = list (string * A)] used in every interpreter chapter from
    IDs onward is a [PList (string * A)].  The [lookup]/[extend] proofs
    are the two-case structural induction pattern from this chapter.

  - Every language [Inductive] ([FBAE], [FBAEC], [FBAES], ...) is a
    sum of products.  [FBAE] is:
<<
  Num : nat -> FBAE            (* nat *)
  Plus : FBAE -> FBAE -> FBAE  (* FBAE * FBAE *)
  ...
>>
    so [FBAE = nat + (FBAE * FBAE) + ...].  Every proof by [induction e]
    in those chapters is this chapter's sum-of-products case analysis.

  - [RVal] (closure interpreter) is a sum: [NumV nat | ClosureV ...].

  - Typed recursion (TRec) introduces [fix] to give languages recursion
    primitively.  The Rocq analogue is [Fixpoint], used throughout this
    chapter.  Drawing the parallel helps students understand why typed
    [fix] needs a special typing rule.
 *)
