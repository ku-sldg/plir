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
#<ol>#
#<li>#_Integer lists from first principles._ Define [IntList] as an
inductive type with [Nil] and [Cons].  Stress that this is exactly
LISP's cons cell, just spelled differently.  Run [car]/[cdr]/[isEmpty]
on concrete lists with [reflexivity] to build intuition.#</li>#
#<li>#_Structural operations._ [length] and [append] show the two-case
pattern: base case returns a simple value, recursive case combines the
head with the result on the tail.  Prove [append_nil_r] by induction
(contrasting with [append_nil_l] which is just [reflexivity]).  This is
often students' first non-trivial induction proof.#</li>#
#<li>#_Higher-order functions._ Show that [addOne_list] and [double_list]
are the same function except for the per-element operation - then
abstract it out as [map].  Repeat for [foldr] (accumulate right-to-left),
[foldl] (tail-recursive, left-to-right), and [filter].  Have students
verify [sum_list = 6] and [filter_even] by [reflexivity].#</li>#
#<li>#_Polymorphic lists._ Ask: why is [map] still restricted to [nat ->
nat]?  Answer: the list element type is hardcoded.  Generalize to [PList
A] and show that every function carries over with identical structure,
just replacing [nat] with [A].  Demonstrate with a [PList bool] and a
[PList (nat * nat)] example.#</li>#
#<li>#_The isomorphism._ Define [intToP] and [pToInt].  Prove they are
inverses by structural induction (both proofs are one-liners after [simpl]).
Then prove the commutation lemmas.  The conclusion is the chapter's
central lesson: the functions are structure-dependent, not content-
dependent.#</li>#
#</ol>#
 *)

(** * PART 3: COMMON PITFALLS *)

(**
  - _[append_nil_l] vs [append_nil_r]._ Students often expect both to be
    [reflexivity].  The asymmetry - [append Nil ys = ys] by definition,
    but [append xs Nil = xs] requires induction - is confusing until they
    see that [append] recurses on its _first_ argument, not its second.
    Walk through the [Cons] case by hand: [append (Cons n tl) Nil = Cons n
    (append tl Nil) = Cons n tl] only after the IH fires.

  - _Implicit vs explicit type arguments._ When [A] is implicit in
    [pmap {A B}], students sometimes get "Cannot infer the implicit
    argument A" when Rocq cannot determine the element type from context.
    Supply the type explicitly ([pmap (A := nat) S xs]) or ensure the
    surrounding expression determines the type.

  - _[foldl] vs [foldr] for non-commutative operations._ Division and
    subtraction give different results with [foldl] vs [foldr].  Subtraction
    is a good example: [foldl Nat.sub 10 (Cons 1 (Cons 2 Nil)) = 7] but
    [foldr Nat.sub 10 (Cons 1 (Cons 2 Nil)) = 9].

  - _[reverse_involutive] without [reverse_append]._ Students often try
    to prove [reverse (reverse xs) = xs] directly and get stuck in the
    [Cons] case because they cannot simplify [reverse (append ...)].
    Guide them to establish [reverse_append] as a helper first; that is
    the standard proof structure.
 *)

(** * PART 4: THE EXERCISES *)

(**
Part 1 (ex1-ex8) - running the functions: all [reflexivity] on concrete
  values.  Fast confidence-building; every student should complete these.

Part 2 (ex9-ex12) - structural lemmas:
  - ex9 ([map_length]): standard one-step induction, closes with
    [rewrite IH; reflexivity].
  - ex10 ([filter_le_length]): induction + [destruct (p n)] + [lia].
    The [destruct] step is the key insight.
  - ex11 ([reverse_append]): ★★★.  Induction on [xs]; the [Cons] case
    rewrites with IH then uses [append_assoc] (or [<- append_assoc])
    to reassociate.  Work this example on the board.
  - ex12 ([reverse_involutive]): ★★★.  Cite ex11 to unfold the outer
    [reverse], then [simpl] to reduce [reverse (Cons n Nil)], then IH.

Part 3 (ex13-ex16) - polymorphic:
  - ex13-ex14: [reflexivity].
  - ex15 ([pmap_length]): exact parallel of ex9 for [pmap]/[plength].
    Reinforce that the proof structure is identical.
  - ex16 ([foldl_commutes]): the [revert acc] before the induction is
    the key step - without it the induction hypothesis is too weak.
    Emphasise: when the statement is universally quantified over a
    parameter that changes in recursive calls, generalise before
    inducting.

Grade by building plih_ds_exercises.v with the [Admitted]s replaced.
 *)

(** * PART 5: CONNECTIONS TO OTHER CHAPTERS *)

(**
  - The [Env A = list (string * A)] type used in every interpreter
    chapter from IDs onward is a [PList (string * A)].  The
    [lookup]/[extend] proofs are structural inductions with the same
    two-case pattern students learned here.

  - [foldr] applied to lists of expressions ([foldr App f args]) is how
    multi-argument application is encoded in some language chapters.

  - Typed recursion (TRec) introduces [fix] to give languages a way to
    define recursive functions _in the language_.  The analogue in Rocq
    is [Fixpoint], which students have used throughout this chapter.
    Drawing the parallel helps students understand why [fix] must be
    typed carefully.
 *)
