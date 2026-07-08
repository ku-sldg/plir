(**
Programming Languages in Rocq - Data Structures Solutions
Complete solutions to plih_ds_exercises.v

Do not read this file until you have made a genuine attempt at each
exercise.
 *)

Require Import plih_rocq_ds_shared.
Require Import plih_ds_lecture.

(** * PART 1: RUNNING THE FUNCTIONS *)

Example ex1_car : car (Cons 7 (Cons 3 Nil)) = Some 7.
Proof. reflexivity. Qed.

Example ex2_car_nil : car Nil = None.
Proof. reflexivity. Qed.

Example ex3_length : length (Cons 1 (Cons 2 (Cons 3 Nil))) = 3.
Proof. reflexivity. Qed.

Example ex4_append :
  append (Cons 1 (Cons 2 Nil)) (Cons 3 (Cons 4 Nil)) =
  Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil))).
Proof. reflexivity. Qed.

Example ex5_reverse :
  reverse (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 3 (Cons 2 (Cons 1 Nil)).
Proof. reflexivity. Qed.

Example ex6_map_succ :
  map S (Cons 0 (Cons 1 (Cons 2 Nil))) = Cons 1 (Cons 2 (Cons 3 Nil)).
Proof. reflexivity. Qed.

Example ex7_sum :
  foldr Nat.add 0 (Cons 1 (Cons 2 (Cons 3 Nil))) = 6.
Proof. reflexivity. Qed.

Example ex8_filter_even :
  filter Nat.even (Cons 1 (Cons 2 (Cons 3 (Cons 4 Nil)))) = Cons 2 (Cons 4 Nil).
Proof. reflexivity. Qed.

(** * PART 2: INTLIST LEMMAS *)

Lemma ex9_map_length : forall f xs, length (map f xs) = length xs.
Proof.
  intros f xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma ex10_filter_le : forall p xs, length (filter p xs) <= length xs.
Proof.
  intros p xs. induction xs as [| n tl IH].
  - simpl. lia.
  - simpl. destruct (p n); simpl; lia.
Qed.

Lemma ex11_reverse_append : forall xs ys,
  reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof.
  intros xs ys. induction xs as [| n tl IH].
  - simpl. rewrite append_nil_r. reflexivity.
  - simpl. rewrite IH. rewrite <- append_assoc. reflexivity.
Qed.

Lemma ex12_reverse_involutive : forall xs, reverse (reverse xs) = xs.
Proof.
  intros xs. induction xs as [| n tl IH].
  - reflexivity.
  - simpl. rewrite ex11_reverse_append. simpl. rewrite IH. reflexivity.
Qed.

(** * PART 3: POLYMORPHIC LISTS *)

Example ex13_pcar : pcar (PCons 42 PNil) = Some 42.
Proof. reflexivity. Qed.

Example ex14_plength_bool :
  plength (PCons true (PCons false PNil)) = 2.
Proof. reflexivity. Qed.

Lemma ex15_pmap_length : forall {A B} (f : A -> B) xs,
  plength (pmap f xs) = plength xs.
Proof.
  intros A B f xs. induction xs as [| a tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma ex16_foldl_commutes : forall {B} (f : B -> nat -> B) acc xs,
  foldl f acc xs = pfoldl f acc (intToP xs).
Proof.
  intros B f acc xs. revert acc.
  induction xs as [| n tl IH].
  - reflexivity.
  - intros acc. simpl. rewrite IH. reflexivity.
Qed.

(** * PART 4: PRODUCT TYPES *)

Example ex17_fst : fst (42, true) = 42.
Proof. reflexivity. Qed.

Example ex18_snd : snd (42, true) = true.
Proof. reflexivity. Qed.

Example ex19_swap : swap (true, 5) = (5, true).
Proof. reflexivity. Qed.

Lemma ex20_prod_eta : forall {A B} (p : A * B), p = (fst p, snd p).
Proof. intros A B [a b]. reflexivity. Qed.

(** * PART 5: SUM TYPES AND RECORDS *)

Example ex21_inl : sumToNat (inl 7) = 7.
Proof. reflexivity. Qed.

Example ex22_inr : sumToNat (inr false) = 0.
Proof. reflexivity. Qed.

Example ex23_pcar_record : pcar (PCons 99 PNil) = Some 99.
Proof. reflexivity. Qed.

Example ex24_field : point35.(py) = 5.
Proof. reflexivity. Qed.

Example ex25_translate : translate point35 origin = point35.
Proof. reflexivity. Qed.

Lemma ex26_point_eta : forall p : Point,
  p = {| px := p.(px); py := p.(py) |}.
Proof. intros [n m]. reflexivity. Qed.

(** * PART 6: ALGEBRA OF TYPES *)

Example ex27_circle : shapeToAlg (Circle 5) = inl 5.
Proof. reflexivity. Qed.

Example ex28_rect : shapeToAlg (Rectangle 3 4) = inr (3, 4).
Proof. reflexivity. Qed.

Inductive Color : Type := Red | Green | Blue.

Definition colorToAlg (c : Color) : unit + (unit + unit) :=
  match c with
  | Red   => inl tt
  | Green => inr (inl tt)
  | Blue  => inr (inr tt)
  end.

Definition algToColor (x : unit + (unit + unit)) : Color :=
  match x with
  | inl _       => Red
  | inr (inl _) => Green
  | inr (inr _) => Blue
  end.

Lemma ex29_algToColor_colorToAlg : forall s, algToColor (colorToAlg s) = s.
Proof. intros [| |]; reflexivity. Qed.

Lemma ex30_colorToAlg_algToColor : forall x, colorToAlg (algToColor x) = x.
Proof. intros [[] | [[] | []]]; reflexivity. Qed.
