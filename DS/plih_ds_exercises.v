(**
Programming Languages in Rocq - Data Structures Exercises
Recursive types, higher-order functions, and polymorphism - Student Problem Set

In these exercises you will:
#<ol>#
#<li>#Run the [IntList] and [PList] functions on concrete values#</li>#
#<li>#Prove structural lemmas about [length], [map], and [filter]#</li>#
#<li>#Prove a classic list identity ([reverse_involutive]) from scratch#</li>#
#<li>#Bridge [IntList] and [PList nat] with commutation lemmas#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: [IntList] ([Nil]/[Cons]), [car]/[cdr]/[isEmpty],
[length]/[append]/[reverse], [map]/[foldr]/[foldl]/[filter]; [PList A]
([PNil]/[PCons]) with [pcar]/[pcdr]/[pisEmpty], [plength]/[pappend]/
[preverse], [pmap]/[pfoldr]/[pfoldl]/[pfilter]; the isomorphism
[intToP]/[pToInt] and commutation lemmas.  Key lemmas available:
[append_nil_r], [append_assoc], [length_append], [map_length],
[filter_le_length], [reverse_length], [intToP_pToInt], [pToInt_intToP].

Difficulty: ★ trivial, ★★ a short induction, ★★★ multi-step proof.
Solutions are in plih_ds_solutions.v.
 *)

Require Import plih_rocq_ds_shared.
Require Import plih_ds_lecture.

(** * PART 1: RUNNING THE FUNCTIONS *)

(* ★ [car] returns the first element of a non-empty list. *)
Example ex1_car : car (Cons 7 (Cons 3 Nil)) = Some 7.
Proof. Admitted.

(* ★ [car] on [Nil] returns [None]. *)
Example ex2_car_nil : car Nil = None.
Proof. Admitted.

(* ★ Length of a three-element list. *)
Example ex3_length : length (Cons 1 (Cons 2 (Cons 3 Nil))) = 3.
Proof. Admitted.

(* ★ Appending two lists. *)
Example ex4_append :
  append (Cons 1 (Cons 2 Nil)) (Cons 3 (Cons 4 Nil)) =
  Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil))).
Proof. Admitted.

(* ★ Reversing a list. *)
Example ex5_reverse :
  reverse (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 3 (Cons 2 (Cons 1 Nil)).
Proof. Admitted.

(* ★ [map S] increments every element. *)
Example ex6_map_succ :
  map S (Cons 0 (Cons 1 (Cons 2 Nil))) = Cons 1 (Cons 2 (Cons 3 Nil)).
Proof. Admitted.

(* ★ [foldr Nat.add 0] sums a list. *)
Example ex7_sum :
  foldr Nat.add 0 (Cons 1 (Cons 2 (Cons 3 Nil))) = 6.
Proof. Admitted.

(* ★ [filter Nat.even] keeps only even elements. *)
Example ex8_filter_even :
  filter Nat.even (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))) = Cons 2 (Cons 4 Nil).
Proof. Admitted.

(** * PART 2: INTLIST LEMMAS *)

(* ★★ [map] does not change list length.
   Proceed by induction on the list. *)
Lemma ex9_map_length : forall f xs, length (map f xs) = length xs.
Proof. Admitted.

(* ★★ [filter] does not make a list longer.
   Proceed by induction; [destruct (p n)] splits the conditional.
   Close each branch with [lia].  Hint: [IH] will be in the context. *)
Lemma ex10_filter_le : forall p xs, length (filter p xs) <= length xs.
Proof. Admitted.

(* ★★★ Reverse distributes over append (contravariant).
   Induct on [xs].  In the [Cons] case, use the induction hypothesis
   and [append_assoc]. *)
Lemma ex11_reverse_append : forall xs ys,
  reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof. Admitted.

(* ★★★ Reversing twice gives back the original list.
   Use [ex11_reverse_append] to unfold [reverse (reverse (Cons n tl))].
   Close with [simpl] and [IH]. *)
Lemma ex12_reverse_involutive : forall xs, reverse (reverse xs) = xs.
Proof. Admitted.

(** * PART 3: POLYMORPHIC LISTS *)

(* ★ [pcar] on a polymorphic list. *)
Example ex13_pcar : pcar (PCons 42 PNil) = Some 42.
Proof. Admitted.

(* ★ [plength] works on any element type. *)
Example ex14_plength_bool :
  plength (PCons true (PCons false PNil)) = 2.
Proof. Admitted.

(* ★★ [pmap] preserves list length, just as [map] does.
   Induct on [xs]. *)
Lemma ex15_pmap_length : forall {A B} (f : A -> B) xs,
  plength (pmap f xs) = plength xs.
Proof. Admitted.

(* ★★ [foldl] and [pfoldl] agree under the isomorphism.
   Induct on [xs].  The [foldl] case updates the accumulator at each
   step, so [revert acc] before the induction to keep the quantifier
   general. *)
Lemma ex16_foldl_commutes : forall {B} (f : B -> nat -> B) acc xs,
  foldl f acc xs = pfoldl f acc (intToP xs).
Proof. Admitted.
