(**
Programming Languages in Rocq - AE Solutions
Complete solutions to plih_ae_exercises.v

The exercises reuse the [AE] syntax, the [eval] interpreter, and the
helpers [count_ops], [ae_equiv], [ae_eq_dec] from the lecture, so we
import it.  The extra helper functions (size, depth, optimize,
fold_constants, simplify) are defined here.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import plih_rocq_ae_shared.
Require Import plih_ae_lecture.

(** * WARM-UP: DIRECT EVALUATION *)

Example ex1_eval_num : eval (Num 42) = 42.
Proof. reflexivity. Qed.

Example ex2_eval_plus : eval (Plus (Num 3) (Num 5)) = 8.
Proof. reflexivity. Qed.

Example ex3_eval_nested :
  eval (Plus (Plus (Num 1) (Num 2)) (Num 3)) = 6.
Proof. reflexivity. Qed.

Example ex4_eval_minus :
  eval (Minus (Num 10) (Num 3)) = 7.
Proof. reflexivity. Qed.

Example ex5_eval_complex :
  eval (Plus (Minus (Num 20) (Num 5)) (Num 10)) = 25.
Proof. reflexivity. Qed.

(** * PART 1: SIMPLE LEMMAS *)

Lemma ex6_eval_plus_distributes : forall e1 e2,
  eval (Plus e1 e2) = eval e1 + eval e2.
Proof. intros e1 e2. reflexivity. Qed.

Lemma ex7_eval_minus_distributes : forall e1 e2,
  eval (Minus e1 e2) = eval e1 - eval e2.
Proof. intros e1 e2. reflexivity. Qed.

Lemma ex8_plus_commutative : forall e1 e2,
  eval (Plus e1 e2) = eval (Plus e2 e1).
Proof. intros e1 e2. simpl. lia. Qed.

(** * PART 2: SIMPLE INDUCTION PROOFS *)

Lemma ex9_zero_left_identity : forall e,
  eval (Plus (Num 0) e) = eval e.
Proof. intro e. reflexivity. Qed.

Lemma ex10_eval_is_nat : forall e,
  exists n, eval e = n.
Proof. intro e. exists (eval e). reflexivity. Qed.

Lemma ex11_eval_nonneg : forall e,
  0 <= eval e.
Proof. intro e. lia. Qed.

Lemma ex12_eval_is_positive : forall e,
  eval e >= 0.
Proof. intro e. lia. Qed.

(** * PART 3: PROPERTIES OF OPERATIONS *)

Lemma ex13_plus_zero_right : forall e,
  eval (Plus e (Num 0)) = eval e.
Proof. intro e. simpl. lia. Qed.

Lemma ex14_minus_self : forall e,
  eval (Minus e e) = 0.
Proof. intro e. simpl. lia. Qed.

Lemma ex15_plus_associative : forall e1 e2 e3,
  eval (Plus (Plus e1 e2) e3) = eval (Plus e1 (Plus e2 e3)).
Proof. intros e1 e2 e3. simpl. lia. Qed.

Lemma ex16_minus_twice : forall e1 e2 e3,
  eval (Minus (Minus e1 e2) e3) =
  if (eval e1) <? (eval e2 + eval e3) then 0 else eval e1 - eval e2 - eval e3.
Proof.
  intros e1 e2 e3. simpl.
  destruct (eval e1 <? eval e2 + eval e3) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - apply Nat.ltb_ge in E. lia.
Qed.

(** * PART 4: INEQUALITIES *)

Lemma ex17_plus_increases : forall e1 e2,
  eval (Plus e1 e2) >= eval e1.
Proof. intros e1 e2. simpl. lia. Qed.

Lemma ex18_minus_decreases : forall e1 e2,
  eval (Minus e1 e2) <= eval e1.
Proof. intros e1 e2. simpl. lia. Qed.

Lemma ex19_plus_both_pos : forall e1 e2,
  eval e1 > 0 -> eval e2 > 0 -> eval (Plus e1 e2) > 1.
Proof. intros e1 e2 H1 H2. simpl. lia. Qed.

(** * PART 5: AUXILIARY FUNCTIONS *)

Fixpoint size (e : AE) : nat :=
  match e with
  | Num _ => 1
  | Plus a b => 1 + size a + size b
  | Minus a b => 1 + size a + size b
  end.

Lemma ex20_size_positive : forall e,
  size e > 0.
Proof. intro e. induction e; simpl; lia. Qed.

Lemma ex21_size_of_plus : forall e1 e2,
  size (Plus e1 e2) = 1 + size e1 + size e2.
Proof. intros e1 e2. reflexivity. Qed.

Fixpoint depth (e : AE) : nat :=
  match e with
  | Num _ => 0
  | Plus a b => 1 + Nat.max (depth a) (depth b)
  | Minus a b => 1 + Nat.max (depth a) (depth b)
  end.

Lemma ex22_depth_num : forall n,
  depth (Num n) = 0.
Proof. intro n. reflexivity. Qed.

(* The classic bound.  We prove the slightly stronger
   [S (size e) <= 2 ^ (depth e + 1)] so the induction goes through,
   then weaken it. *)
Lemma size_lt_pow : forall e,
  S (size e) <= 2 ^ (depth e + 1).
Proof.
  induction e as [n | a IHa b IHb | a IHa b IHb]; cbn [size depth].
  - (* Num n: S 1 <= 2 ^ 1 *)
    simpl. lia.
  - (* Plus a b *)
    assert (Ha : 2 ^ (depth a + 1) <= 2 ^ (Nat.max (depth a) (depth b) + 1)).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hb : 2 ^ (depth b + 1) <= 2 ^ (Nat.max (depth a) (depth b) + 1)).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hpow : 2 ^ (Nat.max (depth a) (depth b) + 1)
                 + 2 ^ (Nat.max (depth a) (depth b) + 1)
                 = 2 ^ (Nat.max (depth a) (depth b) + 2)).
    { rewrite (Nat.pow_add_r 2 (Nat.max (depth a) (depth b)) 1).
      rewrite (Nat.pow_add_r 2 (Nat.max (depth a) (depth b)) 2).
      simpl. lia. }
    replace (1 + Nat.max (depth a) (depth b) + 1)
       with (Nat.max (depth a) (depth b) + 2) by lia.
    lia.
  - (* Minus a b *)
    assert (Ha : 2 ^ (depth a + 1) <= 2 ^ (Nat.max (depth a) (depth b) + 1)).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hb : 2 ^ (depth b + 1) <= 2 ^ (Nat.max (depth a) (depth b) + 1)).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hpow : 2 ^ (Nat.max (depth a) (depth b) + 1)
                 + 2 ^ (Nat.max (depth a) (depth b) + 1)
                 = 2 ^ (Nat.max (depth a) (depth b) + 2)).
    { rewrite (Nat.pow_add_r 2 (Nat.max (depth a) (depth b)) 1).
      rewrite (Nat.pow_add_r 2 (Nat.max (depth a) (depth b)) 2).
      simpl. lia. }
    replace (1 + Nat.max (depth a) (depth b) + 1)
       with (Nat.max (depth a) (depth b) + 2) by lia.
    lia.
Qed.

Lemma ex23_size_depth_relation : forall e,
  size e <= 2 ^ (depth e + 1).
Proof.
  intro e. pose proof (size_lt_pow e). lia.
Qed.

(** * PART 6: OPTIMIZATION CORRECTNESS *)

(* Optimize children first, then drop a [+ 0] on the right.  Recursing
   before folding keeps the correctness proof free of nested-pattern
   reduction surprises. *)
Fixpoint optimize (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus a b =>
      match optimize b with
      | Num 0 => optimize a
      | b' => Plus (optimize a) b'
      end
  | Minus a b => Minus (optimize a) (optimize b)
  end.

Lemma ex24_optimize_correct : forall e,
  eval (optimize e) = eval e.
Proof.
  induction e.
  - reflexivity.
  - (* Plus e1 e2 *)
    simpl. rewrite <- IHe1, <- IHe2.
    destruct (optimize e2) as [n2 | x y | x y].
    + destruct n2; simpl; lia.
    + simpl; lia.
    + simpl; lia.
  - (* Minus *)
    simpl. rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma ex25_optimize_reduces_size : forall e,
  size (optimize e) <= size e.
Proof.
  induction e.
  - simpl. lia.
  - (* Plus e1 e2 *)
    assert (Hb : size (optimize (Plus e1 e2))
                 <= 1 + size (optimize e1) + size (optimize e2)).
    { simpl. destruct (optimize e2) as [n2 | x y | x y];
        try (destruct n2); simpl; lia. }
    cbn [size]. lia.
  - (* Minus *)
    simpl. lia.
Qed.

(** * PART 7: EQUIVALENCE RELATION *)

(* [ae_equiv] is defined in the lecture as [eval e1 = eval e2]. *)

Lemma ex26_equiv_refl : forall e,
  ae_equiv e e.
Proof. exact ae_equiv_refl. Qed.

Lemma ex27_equiv_sym : forall e1 e2,
  ae_equiv e1 e2 -> ae_equiv e2 e1.
Proof. exact ae_equiv_sym. Qed.

Lemma ex28_equiv_trans : forall e1 e2 e3,
  ae_equiv e1 e2 -> ae_equiv e2 e3 -> ae_equiv e1 e3.
Proof. exact ae_equiv_trans. Qed.

Lemma ex29_equiv_example :
  ae_equiv (Plus (Num 1) (Num 2)) (Plus (Num 2) (Num 1)).
Proof. unfold ae_equiv. reflexivity. Qed.

(** * PART 8: CREATIVE PROBLEMS *)

(* Constant folding: evaluate constant subexpressions statically. *)
Fixpoint fold_constants (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus a b =>
      match fold_constants a, fold_constants b with
      | Num x, Num y => Num (x + y)
      | a', b' => Plus a' b'
      end
  | Minus a b =>
      match fold_constants a, fold_constants b with
      | Num x, Num y => Num (x - y)
      | a', b' => Minus a' b'
      end
  end.

Lemma ex30_fold_constants_correct : forall e,
  eval (fold_constants e) = eval e.
Proof.
  induction e.
  - reflexivity.
  - simpl. rewrite <- IHe1, <- IHe2.
    destruct (fold_constants e1); destruct (fold_constants e2);
      simpl; reflexivity.
  - simpl. rewrite <- IHe1, <- IHe2.
    destruct (fold_constants e1); destruct (fold_constants e2);
      simpl; reflexivity.
Qed.

Lemma ex31_double : forall e,
  eval e + eval e = 2 * eval e.
Proof. intro e. lia. Qed.

(** * CHALLENGE PROBLEMS *)

(* Challenge 1: a nonzero operation count means the head is Plus or
   Minus. ([count_ops] is from the lecture.) *)
Lemma challenge1_count_ops_positive : forall e,
  count_ops e > 0 -> exists e1 e2, e = Plus e1 e2 \/ e = Minus e1 e2.
Proof.
  intros e H. destruct e.
  - simpl in H. lia.
  - exists e1, e2. left. reflexivity.
  - exists e1, e2. right. reflexivity.
Qed.

(* Challenge 2: simplify removes (Num 0) summands and (Minus e e).
   We simplify children first, then fold, which keeps the proof clean. *)
Fixpoint simplify (e : AE) : AE :=
  match e with
  | Num n => Num n
  | Plus a b =>
      match simplify a, simplify b with
      | Num 0, b' => b'
      | a', Num 0 => a'
      | a', b' => Plus a' b'
      end
  | Minus a b =>
      if ae_eq_dec a b then Num 0 else Minus (simplify a) (simplify b)
  end.

Lemma challenge2_simplify_correct : forall e,
  eval (simplify e) = eval e.
Proof.
  induction e.
  - reflexivity.
  - (* Plus e1 e2 *)
    simpl. rewrite <- IHe1, <- IHe2.
    destruct (simplify e1) as [n1 | | ]; destruct (simplify e2) as [n2 | | ];
      try (destruct n1); try (destruct n2); simpl; lia.
  - (* Minus e1 e2 *)
    simpl. destruct (ae_eq_dec e1 e2) eqn:Heq.
    + apply ae_eq_dec_correct in Heq. subst. simpl. lia.
    + simpl. rewrite IHe1, IHe2. reflexivity.
Qed.

(** * CONCRETE SYNTAX *)

Open Scope ae_scope.

(* Exercise 32: the concrete form is definitionally the abstract tree. *)
Example ex32_parse : <{ 7 + 2 }> = Plus (Num 7) (Num 2).
Proof. reflexivity. Qed.

(* Exercise 33: [eval] consumes the same tree the notation elaborates to. *)
Example ex33_eval_concrete : eval <{ 6 - 4 }> = 2.
Proof. reflexivity. Qed.

(* Exercise 34: [-] is left-associative, so [9 - 3 - 2] is [(9 - 3) - 2]. *)
Example ex34_left_assoc : <{ 9 - 3 - 2 }> = Minus (Minus (Num 9) (Num 3)) (Num 2).
Proof. reflexivity. Qed.

(* Exercise 35: unfold [eval] and let [lia] close [n - n = 0]. *)
Lemma ex35_minus_self : forall e,
  eval <{ e - e }> = 0.
Proof. intro e. simpl. lia. Qed.
