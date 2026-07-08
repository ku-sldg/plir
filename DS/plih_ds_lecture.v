(**
Programming Languages in Rocq - Data Structures Lecture
Recursive types, higher-order functions, and polymorphism

Every chapter so far has been about language _interpreters_: define a
syntax, define a value type, write an evaluation function, prove things
about it.  This chapter steps back and looks at how _data structures_
are built in Rocq itself.

The subject is _lists_.  Lists are the simplest non-trivial recursive
structure: they have a base case ([Nil]) and a recursive case ([Cons]).
Everything interesting about recursive data - induction, structural
recursion, higher-order operations, polymorphism - shows up cleanly
with lists.

We cover seven topics across nine sections.

#<ol>#
#<li>#_Integer lists_ ([IntList]).  A concrete inductive type with the
classic LISP observers ([car], [cdr], [isEmpty]) and structural
operations ([length], [append], [reverse]).#</li>#
#<li>#_Higher-order functions_.  [map], [foldr], [foldl], and [filter]
abstract over the per-element operation.#</li>#
#<li>#_Polymorphic lists_ ([PList A]).  Same functions, same proofs,
element type is a parameter.  Formally: an isomorphism with [IntList].#</li>#
#<li>#_Product types_ ([A * B]).  Pairs, projections, and the eta law.#</li>#
#<li>#_Sum types_ ([A + B]).  Tagged unions; [option A = unit + A].#</li>#
#<li>#_Records_.  Named products; the [Record] keyword; dot projection.#</li>#
#<li>#_Records as sums of products_.  Every [Inductive] type is a sum
of products; the [Shape] example formalises this as an isomorphism.#</li>#
#</ol>#

The central lesson: a function's recursive structure is determined by
the _shape_ of the data, not the _content_ of the elements.  Products
and sums give us the vocabulary to describe that shape precisely.
 *)

Require Import plih_rocq_ds_shared.

(** * Section 1: Integer Lists *)

(**
LISP introduced the idea of building all data from a single recursive
pair type.  The key constructors and observers were:

  - [nil]  -- the empty list
  - [cons] -- prepend an element to a list
  - [car]  -- return the first element (head)
  - [cdr]  -- return the rest of the list (tail)

We build the same idea directly as a Rocq inductive type.  Rocq
convention capitalises constructor names, so we write [Nil] and [Cons]
rather than [nil] and [cons].
 *)

Inductive IntList : Type :=
| Nil  : IntList
| Cons : nat -> IntList -> IntList.

(**
[Nil] is the empty list.  [Cons n xs] prepends the natural number [n]
to the list [xs].  The two constructors are _exhaustive_: every
[IntList] is either empty or a head-and-tail pair.
 *)

(** ** Observers *)

(**
An _observer_ inspects a value without changing it.  The three
canonical list observers correspond directly to LISP's [car], [cdr],
and the [null?] predicate.  All three return [option] or [bool] so they
can handle the empty list gracefully.
 *)

Definition car (xs : IntList) : option nat :=
  match xs with
  | Nil => None
  | Cons n _ => Some n
  end.

Definition cdr (xs : IntList) : option IntList :=
  match xs with
  | Nil => None
  | Cons _ tl => Some tl
  end.

Definition isEmpty (xs : IntList) : bool :=
  match xs with
  | Nil => true
  | Cons _ _ => false
  end.

(** ** Examples *)

(**
Here are three concrete [IntList] values.  We give each a Rocq name so
it can be reused in examples and exercises.
 *)

Definition nil_ex  : IntList := Nil.
Definition list1   : IntList := Cons 1 Nil.
Definition list123 : IntList := Cons 1 (Cons 2 (Cons 3 Nil)).

(**
The observers run on concrete lists by [reflexivity]: Rocq evaluates
the match and compares the normal forms.
 *)

Example car_nil  : car Nil = None.          Proof. reflexivity. Qed.
Example car_list : car list123 = Some 1.    Proof. reflexivity. Qed.
Example cdr_list : cdr list123 = Some (Cons 2 (Cons 3 Nil)). Proof. reflexivity. Qed.
Example isEmpty_nil  : isEmpty Nil = true.  Proof. reflexivity. Qed.
Example isEmpty_cons : isEmpty list123 = false. Proof. reflexivity. Qed.

(** * Section 2: Structural Operations *)

(**
Structural operations recurse on the _shape_ of the list.  At [Nil]
they return a base value; at [Cons] they combine the head with the
recursive result on the tail.  Rocq's [Fixpoint] keyword marks a
recursively-defined function; the [match] must terminate, which it does
here because the tail is structurally smaller than the whole list.
 *)

(** ** Length *)

Fixpoint length (xs : IntList) : nat :=
  match xs with
  | Nil => 0
  | Cons _ tl => 1 + length tl
  end.

Example length_list123 : length list123 = 3. Proof. reflexivity. Qed.
Example length_nil_ex  : length Nil = 0.    Proof. reflexivity. Qed.

(**
Two lemmas follow immediately from the definition by [reflexivity] -
they just unfold the match.
 *)

Lemma length_nil_eq : length Nil = 0.
Proof. reflexivity. Qed.

Lemma length_cons_eq : forall n xs, length (Cons n xs) = 1 + length xs.
Proof. reflexivity. Qed.

(** ** Append *)

(**
[append xs ys] concatenates [xs] and [ys] by recursing on [xs].
 *)

Fixpoint append (xs ys : IntList) : IntList :=
  match xs with
  | Nil => ys
  | Cons n tl => Cons n (append tl ys)
  end.

Example append_ex :
  append (Cons 1 (Cons 2 Nil)) (Cons 3 Nil) = Cons 1 (Cons 2 (Cons 3 Nil)).
Proof. reflexivity. Qed.

(**
[append Nil ys = ys] holds by the [Nil] branch of the match - no
induction needed.
 *)

Lemma append_nil_l : forall ys, append Nil ys = ys.
Proof. reflexivity. Qed.

(**
[append xs Nil = xs] requires induction because [xs] appears on the
left; there is no matching branch that immediately returns [xs].
 *)

Lemma append_nil_r : forall xs, append xs Nil = xs.
Proof.
  intros xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(**
Associativity of [append] is also proved by induction on the first
argument.
 *)

Lemma append_assoc : forall xs ys zs,
  append xs (append ys zs) = append (append xs ys) zs.
Proof.
  intros xs ys zs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(**
The length of a concatenation is the sum of the lengths.
 *)

Lemma length_append : forall xs ys,
  length (append xs ys) = length xs + length ys.
Proof.
  intros xs ys. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ** Reverse *)

(**
[reverse] builds the mirror of a list by appending the head to the
reversed tail.  This is the simple, obviously-correct specification;
a faster accumulator-based version appears in the exercises.
 *)

Fixpoint reverse (xs : IntList) : IntList :=
  match xs with
  | Nil => Nil
  | Cons n tl => append (reverse tl) (Cons n Nil)
  end.

Example reverse_ex :
  reverse (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 3 (Cons 2 (Cons 1 Nil)).
Proof. reflexivity. Qed.

(**
Reversing a list preserves its length.  The proof uses
[length_append] and [lia].
 *)

Lemma reverse_length : forall xs, length (reverse xs) = length xs.
Proof.
  intros xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite length_append. simpl. rewrite IH. lia.
Qed.

(** * Section 3: Higher-Order Functions *)

(**
Every structural operation we defined so far does the same thing:
recurse on the list shape and combine a per-element value with the
recursive result.  _Higher-order functions_ make that combination
argument explicit, so one function can serve many purposes.

The four classical higher-order list operations are:

#<ol>#
#<li>#[map] - apply a function to every element#</li>#
#<li>#[foldr] - combine elements right-to-left with a binary operation#</li>#
#<li>#[foldl] - combine elements left-to-right with a binary operation (tail-recursive)#</li>#
#<li>#[filter] - keep only the elements that satisfy a predicate#</li>#
#</ol>#
 *)

(** ** Map *)

(**
[map f xs] applies [f] to every element of [xs], producing a new list
of the same length.
 *)

Fixpoint map (f : nat -> nat) (xs : IntList) : IntList :=
  match xs with
  | Nil => Nil
  | Cons n tl => Cons (f n) (map f tl)
  end.

Example map_succ :
  map S (Cons 0 (Cons 1 (Cons 2 Nil))) = Cons 1 (Cons 2 (Cons 3 Nil)).
Proof. reflexivity. Qed.

Example map_double :
  map (fun n => n * 2) (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 2 (Cons 4 (Cons 6 Nil)).
Proof. reflexivity. Qed.

(**
[map] preserves list length: the shape of the list is untouched, only
the elements change.
 *)

Lemma map_length : forall f xs, length (map f xs) = length xs.
Proof.
  intros f xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ** Foldr *)

(**
[foldr f acc xs] reduces a list to a single value by applying [f]
between each element and the result of folding the tail.  The
_right fold_ reads the list from right to left: the rightmost element
combines with [acc] first.

The type parameter [{B}] is _implicit_: Rocq infers [B] from the types
of [f] and [acc].  Making [B] implicit lets [foldr] be used without
spelling out the accumulator type at every call site.
 *)

Fixpoint foldr {B : Type} (f : nat -> B -> B) (acc : B) (xs : IntList) : B :=
  match xs with
  | Nil => acc
  | Cons n tl => f n (foldr f acc tl)
  end.

(**
Summing a list: [foldr Nat.add 0] accumulates by addition.
 *)

Example sum_list : foldr Nat.add 0 list123 = 6. Proof. reflexivity. Qed.

(**
Rebuilding the list: [foldr Cons Nil xs = xs] (the identity fold).
 *)

Example foldr_id : foldr Cons Nil list123 = list123. Proof. reflexivity. Qed.

(** ** Foldl *)

(**
[foldl f acc xs] accumulates left-to-right: the _accumulator_ carries
the result so far, and each element updates it.  Unlike [foldr], [foldl]
is _tail-recursive_ - the recursive call is the last action in each
branch.
 *)

Fixpoint foldl {B : Type} (f : B -> nat -> B) (acc : B) (xs : IntList) : B :=
  match xs with
  | Nil => acc
  | Cons n tl => foldl f (f acc n) tl
  end.

(**
For commutative and associative [f], [foldl] and [foldr] agree.
Addition is both, so summing works either way.
 *)

Example sum_foldl : foldl Nat.add 0 list123 = 6. Proof. reflexivity. Qed.

(** ** Filter *)

(**
[filter p xs] keeps only the elements [n] for which [p n = true].
 *)

Fixpoint filter (p : nat -> bool) (xs : IntList) : IntList :=
  match xs with
  | Nil => Nil
  | Cons n tl => if p n then Cons n (filter p tl) else filter p tl
  end.

Example filter_even :
  filter Nat.even (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))) = Cons 2 (Cons 4 Nil).
Proof. reflexivity. Qed.

(**
[filter] never makes a list longer.
 *)

Lemma filter_le_length : forall p xs, length (filter p xs) <= length xs.
Proof.
  intros p xs. induction xs as [| n tl IH].
  - simpl. lia.
  - simpl. destruct (p n); simpl; lia.
Qed.

(** * Section 4: Polymorphic Lists *)

(**
Every function in Sections 1-3 hardcodes [nat] as the element type.
But [length], [append], [reverse], [map], [foldr], [foldl], and
[filter] never look _inside_ the elements - they care only about where
elements sit in the list.

The fix is to parameterise the list type by the element type [A].  A
single _polymorphic_ list handles integers, booleans, strings, or any
other type.
 *)

Inductive PList (A : Type) : Type :=
| PNil  : PList A
| PCons : A -> PList A -> PList A.

(**
The [Arguments] declarations make [A] implicit: Rocq infers it from the
surrounding expression, so we can write [PNil] and [PCons n xs] without
mentioning [A] explicitly.
 *)

Arguments PNil  {A}.
Arguments PCons {A} _ _.

(** ** Polymorphic observers *)

Definition pcar {A : Type} (xs : PList A) : option A :=
  match xs with
  | PNil => None
  | PCons a _ => Some a
  end.

Definition pcdr {A : Type} (xs : PList A) : option (PList A) :=
  match xs with
  | PNil => None
  | PCons _ tl => Some tl
  end.

Definition pisEmpty {A : Type} (xs : PList A) : bool :=
  match xs with
  | PNil => true
  | PCons _ _ => false
  end.

(** ** Polymorphic structural operations *)

Fixpoint plength {A : Type} (xs : PList A) : nat :=
  match xs with
  | PNil => 0
  | PCons _ tl => 1 + plength tl
  end.

Fixpoint pappend {A : Type} (xs ys : PList A) : PList A :=
  match xs with
  | PNil => ys
  | PCons a tl => PCons a (pappend tl ys)
  end.

Fixpoint preverse {A : Type} (xs : PList A) : PList A :=
  match xs with
  | PNil => PNil
  | PCons a tl => pappend (preverse tl) (PCons a PNil)
  end.

(** ** Polymorphic higher-order functions *)

(**
[pmap] now maps [f : A -> B], producing a [PList B] from a [PList A].
The element type of the _output_ can differ from the element type of
the _input_.  This was impossible with [map : (nat -> nat) -> IntList
-> IntList].
 *)

Fixpoint pmap {A B : Type} (f : A -> B) (xs : PList A) : PList B :=
  match xs with
  | PNil => PNil
  | PCons a tl => PCons (f a) (pmap f tl)
  end.

Fixpoint pfoldr {A B : Type} (f : A -> B -> B) (acc : B) (xs : PList A) : B :=
  match xs with
  | PNil => acc
  | PCons a tl => f a (pfoldr f acc tl)
  end.

Fixpoint pfoldl {A B : Type} (f : B -> A -> B) (acc : B) (xs : PList A) : B :=
  match xs with
  | PNil => acc
  | PCons a tl => pfoldl f (f acc a) tl
  end.

Fixpoint pfilter {A : Type} (p : A -> bool) (xs : PList A) : PList A :=
  match xs with
  | PNil => PNil
  | PCons a tl => if p a then PCons a (pfilter p tl) else pfilter p tl
  end.

(** ** Examples with non-integer element types *)

(**
A list of booleans: [PList bool].
 *)

Definition blist : PList bool := PCons true (PCons false (PCons true PNil)).

Example pcar_blist : pcar blist = Some true.  Proof. reflexivity. Qed.
Example plength_blist : plength blist = 3.    Proof. reflexivity. Qed.

(**
A list of pairs - element type is [nat * nat].
 *)

Definition pairlist : PList (nat * nat) :=
  PCons (1, 2) (PCons (3, 4) PNil).

Example pcar_pairlist : pcar pairlist = Some (1, 2). Proof. reflexivity. Qed.

(**
[pmap] can change the element type: extract the first component of
each pair.
 *)

Example pmap_fst :
  pmap fst pairlist = PCons 1 (PCons 3 PNil).
Proof. reflexivity. Qed.

(**
[pmap S] on a [PList nat] works exactly like [map S] on [IntList].
 *)

Example pmap_succ :
  pmap S (PCons 0 (PCons 1 (PCons 2 PNil))) = PCons 1 (PCons 2 (PCons 3 PNil)).
Proof. reflexivity. Qed.

(** * Section 5: Structure Without Content *)

(**
We have now defined the same operations twice: once for [IntList] and
once for [PList A].  The definitions are word-for-word identical except
that [nat] is replaced by [A].  This section makes that identity
_formal_.

The key tool is an _isomorphism_: a pair of functions that convert
between [IntList] and [PList nat] and are each other's inverses.
 *)

(** ** The isomorphism *)

Fixpoint intToP (xs : IntList) : PList nat :=
  match xs with
  | Nil => PNil
  | Cons n tl => PCons n (intToP tl)
  end.

Fixpoint pToInt (xs : PList nat) : IntList :=
  match xs with
  | PNil => Nil
  | PCons n tl => Cons n (pToInt tl)
  end.

(**
The two functions are inverses: applying both in either order returns
the original list.
 *)

Lemma intToP_pToInt : forall xs, pToInt (intToP xs) = xs.
Proof.
  intros xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma pToInt_intToP : forall xs, intToP (pToInt xs) = xs.
Proof.
  intros xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ** The functions commute with the isomorphism *)

(**
If [IntList] and [PList nat] are truly the same thing, then running an
[IntList] function and converting the result should give the same
answer as converting first and then running the corresponding [PList]
function.  We call this _commutativity_ with the isomorphism.

The proof in each case is a straightforward structural induction whose
inductive step rewrites with the induction hypothesis and closes with
[reflexivity].
 *)

Lemma map_commutes : forall (f : nat -> nat) (xs : IntList),
  intToP (map f xs) = pmap f (intToP xs).
Proof.
  intros f xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma foldr_commutes : forall {B : Type} (f : nat -> B -> B) (acc : B) (xs : IntList),
  foldr f acc xs = pfoldr f acc (intToP xs).
Proof.
  intros B f acc xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma foldl_commutes : forall {B : Type} (f : B -> nat -> B) (acc : B) (xs : IntList),
  foldl f acc xs = pfoldl f acc (intToP xs).
Proof.
  intros B f acc xs. revert acc.
  induction xs as [| n tl IH].
  - reflexivity.
  - intros acc. simpl. rewrite IH. reflexivity.
Qed.

Lemma filter_commutes : forall (p : nat -> bool) (xs : IntList),
  intToP (filter p xs) = pfilter p (intToP xs).
Proof.
  intros p xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. destruct (p n); simpl; rewrite IH; reflexivity.
Qed.

(**
What the commutation lemmas say, collectively:

  _Every [IntList] function is its [PList nat] counterpart in disguise._

[IntList] is not a different data structure from [PList nat]; it is the
same structure viewed through a trivial renaming.  And the functions
are the same because _they care only about structure, not content_: the
element type never enters the recursive pattern.

This observation justifies writing polymorphic list functions once and
using them everywhere.  The Rocq standard library does exactly this
with [list A] and [List.map], [List.fold_right], [List.filter], etc.
Our [PList A] is isomorphic to [list A] by the same argument.
 *)

(** * Section 6: Product Types *)

(**
A _product type_ [A * B] packages two values together: one of type [A]
and one of type [B].  The name comes from counting: if [A] has [m]
inhabitants and [B] has [n], then [A * B] has exactly [m * n] distinct
values - every possible pairing.

Rocq provides [prod A B] with notation [A * B] in [type_scope].  The
constructor is [pair : A -> B -> A * B], written [(a, b)] with pair
notation.  Two _projections_ retrieve the components:

  - [fst : A * B -> A] returns the first component
  - [snd : A * B -> B] returns the second component

Product types already appeared in Section 4: [PList (nat * nat)] is a
list whose elements are pairs, and [pmap fst] extracted the first
component of each pair.
 *)

Definition swap {A B : Type} (p : A * B) : B * A := (snd p, fst p).

Example swap_pair : swap (1, true) = (true, 1). Proof. reflexivity. Qed.
Example fst_ex   : fst (42, true) = 42.         Proof. reflexivity. Qed.
Example snd_ex   : snd (42, true) = true.        Proof. reflexivity. Qed.

(**
Nested pairs encode triples and tuples:
[(a, (b, c)) : A * (B * C)] or [((a, b), c) : (A * B) * C].
Both are isomorphic to the "flat" triple; which associativity to choose
is a matter of convention.
 *)

Example nested_pair : fst (fst (1, 2), 3) = 1. Proof. reflexivity. Qed.

(**
The _eta law_ for products: every pair is equal to the pair of its
own projections.  The proof destructs [p] into its components, after
which both sides are syntactically equal.
 *)

Lemma prod_eta : forall {A B : Type} (p : A * B), p = (fst p, snd p).
Proof.
  intros A B p. destruct p as [a b]. reflexivity.
Qed.

(** * Section 7: Sum Types *)

(**
A _sum type_ [A + B] represents a _choice_: a value of type [A + B] is
either a value of type [A] tagged with [inl], or a value of type [B]
tagged with [inr].  The name again comes from counting: if [A] has [m]
inhabitants and [B] has [n], then [A + B] has [m + n].

Rocq provides [sum A B] with notation [A + B] in [type_scope].

  - [inl : A -> A + B] injects from the left
  - [inr : B -> A + B] injects from the right

A function consuming [A + B] must handle both tags.
 *)

Definition sumToNat (x : nat + bool) : nat :=
  match x with
  | inl n => n
  | inr b => if b then 1 else 0
  end.

Example sum_left  : sumToNat (inl 42)    = 42. Proof. reflexivity. Qed.
Example sum_right : sumToNat (inr true)  = 1.  Proof. reflexivity. Qed.
Example sum_right2: sumToNat (inr false) = 0.  Proof. reflexivity. Qed.

(**
_[option A] is a sum_.  Concretely, [option A = unit + A]:
  - [None]   corresponds to [inl tt]  (the sole value of [unit])
  - [Some a] corresponds to [inr a]

The isomorphism makes this precise.
 *)

Definition optionToSum {A : Type} (x : option A) : unit + A :=
  match x with
  | None   => inl tt
  | Some a => inr a
  end.

Definition sumToOption {A : Type} (x : unit + A) : option A :=
  match x with
  | inl _ => None
  | inr a => Some a
  end.

(**
Both directions are proved by case analysis; no induction is needed
because neither type is recursive.
 *)

Lemma optionToSum_sumToOption : forall {A} (x : unit + A),
  optionToSum (sumToOption x) = x.
Proof.
  intros A [[] | a]; reflexivity.
Qed.

Lemma sumToOption_optionToSum : forall {A} (x : option A),
  sumToOption (optionToSum x) = x.
Proof.
  intros A [a |]; reflexivity.
Qed.

(** * Section 8: Records *)

(**
A _record_ is a product type with _named_ fields.  Instead of
retrieving components by position ([fst], [snd]), each field has a
dedicated projection function whose name documents its meaning.

Rocq's [Record] keyword declares the type, its constructor, and all
projection functions in one step.
 *)

Record Point : Type := mkPoint {
  px : nat;
  py : nat
}.

(**
[mkPoint] is the constructor; [px] and [py] are the projections.

Construction uses the [{| field := value |}] notation that fills fields
by name.  Projection uses dot notation [p.(field)].
 *)

Definition origin  : Point := {| px := 0; py := 0 |}.
Definition point35 : Point := {| px := 3; py := 5 |}.

Example px_origin   : origin.(px)  = 0. Proof. reflexivity. Qed.
Example py_origin   : origin.(py)  = 0. Proof. reflexivity. Qed.
Example px_point35  : point35.(px) = 3. Proof. reflexivity. Qed.
Example py_point35  : point35.(py) = 5. Proof. reflexivity. Qed.

(**
Functions on records use projections or pattern matching just as they
would on an anonymous product.
 *)

Definition translate (delta p : Point) : Point :=
  {| px := p.(px) + delta.(px);
     py := p.(py) + delta.(py) |}.

Example translate_ex :
  translate {| px := 1; py := 2 |} point35 = {| px := 4; py := 7 |}.
Proof. reflexivity. Qed.

(**
The _eta law_ for records: every record is equal to the record built
from its own projections.  The proof destructs the record to expose
its fields, after which both sides are syntactically identical.
 *)

Lemma point_eta : forall (p : Point), p = {| px := p.(px); py := p.(py) |}.
Proof.
  intros [n m]. reflexivity.
Qed.

(**
A [Record] with two fields of types [T1] and [T2] is isomorphic to
[T1 * T2].  [Point] is isomorphic to [nat * nat].
 *)

Definition pointToPair (p : Point)       : nat * nat := (p.(px), p.(py)).
Definition pairToPoint (q : nat * nat)   : Point     := {| px := fst q; py := snd q |}.

Lemma pointToPair_pairToPoint : forall q, pointToPair (pairToPoint q) = q.
Proof. intros [n m]. reflexivity. Qed.

Lemma pairToPoint_pointToPair : forall p, pairToPoint (pointToPair p) = p.
Proof. intros [n m]. reflexivity. Qed.

(** * Section 9: Records as Sums of Products *)

(**
Products and sums are the two primitive type-forming operations.
_Every_ inductive type in Rocq - and in most typed functional languages
- can be read as an expression built from [*] and [+] alone.

The reading rule is straightforward:
#<ol>#
#<li>#Each constructor contributes a _product_ of its argument types.
A nullary constructor (no arguments) contributes [unit].#</li>#
#<li>#Multiple constructors are combined by _sum_.#</li>#
#</ol>#

Examples:
<<
  bool         = unit + unit               (true  | false)
  option A     = unit + A                  (None  | Some a)
  IntList      = unit + (nat * IntList)    (Nil   | Cons n tl)
  PList A      = unit + (A   * PList A)    (PNil  | PCons a tl)
>>

The recursive cases ([IntList], [PList A]) need a fixed-point in the
algebra - the type appears on both sides - but the [+]/[*] structure
still describes each constructor exactly.

_Records_ fit the same picture: a record with fields [T1], ..., [Tn]
is a product [T1 * ... * Tn] with named projections instead of
positional [fst]/[snd].  [Point ≅ nat * nat] was proved in Section 8.
 *)

(**
A concrete non-recursive example is [Shape], which has two constructors
with different argument counts.
 *)

Inductive Shape : Type :=
| Circle    : nat -> Shape           (* radius *)
| Rectangle : nat -> nat -> Shape.   (* width, height *)

(**
Reading [Shape] as an algebraic expression:

<<
  Shape = nat + (nat * nat)
>>

[Circle r] injects a single [nat] on the left; [Rectangle w h] injects
a pair [nat * nat] on the right.  The isomorphism formalises this.
 *)

Definition shapeToAlg (s : Shape) : nat + (nat * nat) :=
  match s with
  | Circle r      => inl r
  | Rectangle w h => inr (w, h)
  end.

Definition algToShape (x : nat + (nat * nat)) : Shape :=
  match x with
  | inl r        => Circle r
  | inr (w, h)   => Rectangle w h
  end.

(**
Both directions are one-liners: case analysis on the constructor, then
[reflexivity].
 *)

Lemma shapeToAlg_algToShape : forall x, shapeToAlg (algToShape x) = x.
Proof.
  intros [r | [w h]]; reflexivity.
Qed.

Lemma algToShape_shapeToAlg : forall s, algToShape (shapeToAlg s) = s.
Proof.
  intros [r | w h]; reflexivity.
Qed.

(**
The same technique extends to any inductive type.  A zero-constructor
type ([False]) corresponds to an empty sum (no type at all - a type
with no inhabitants).  A one-constructor type with no arguments
([unit]) corresponds to [unit] itself.  A one-constructor type with
one argument is isomorphic to that argument's type.

The algebraic view - types as expressions in [+] and [*] - is the
foundation of _generic programming_: a single piece of code written
for the algebraic structure can be instantiated for any concrete type.
Rocq's standard library exploits this throughout, and languages like
Haskell expose it via the [Generic] and [Data.Data] mechanisms.
 *)
