(**
Programming Languages in Rocq - IDs Solutions
Complete solutions to plih_ids_exercises.v

The BAE syntax, [subst], the fuel interpreter [evalF]/[eval] and its
equation lemmas ([eval_Num], [eval_Plus], [eval_Bind], ...), the
free-variable machinery ([free_in], [closed], [subst_not_free],
[free_in_subst_num], [closed_after_subst]) and [bae_equiv] all come
from the lecture, which we import.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_ids_shared.
Require Import plih_ids_lecture.

Local Open Scope string_scope.

(** * WARM-UP: RUNNING THE INTERPRETER *)

Example ex1_eval_num : eval (Num 42) = Some 42.
Proof. reflexivity. Qed.

Example ex2_eval_bind_id : eval (Bind "x" (Num 5) (Id "x")) = Some 5.
Proof. reflexivity. Qed.

Example ex3_eval_bind_dup :
  eval (Bind "x" (Num 5) (Plus (Id "x") (Id "x"))) = Some 10.
Proof. reflexivity. Qed.

Example ex4_eval_free : eval (Id "z") = None.
Proof. reflexivity. Qed.

Example ex5_eval_nested :
  eval (Bind "x" (Num 4) (Bind "y" (Num 5) (Plus (Id "x") (Id "y"))))
  = Some 9.
Proof. reflexivity. Qed.

(** * PART 1: SUBSTITUTION *)

Example ex6_subst_leaf : subst "x" (Num 3) (Id "x") = Num 3.
Proof. reflexivity. Qed.

Example ex7_subst_other : subst "x" (Num 3) (Id "y") = Id "y".
Proof. reflexivity. Qed.

Lemma ex8_subst_plus : forall i n a b,
  subst i (Num n) (Plus a b)
  = Plus (subst i (Num n) a) (subst i (Num n) b).
Proof. intros. reflexivity. Qed.

Lemma ex9_subst_size : forall e i n,
  size (subst i (Num n) e) = size e.
Proof. intros. apply size_subst_num. Qed.

(** * PART 2: FREE VARIABLES AND CLOSED TERMS *)

Lemma ex10_closed_num : closed (Num 5).
Proof. intro x. reflexivity. Qed.

Lemma ex11_free_in_plus : forall x a b,
  free_in x (Plus a b) = free_in x a || free_in x b.
Proof. intros. reflexivity. Qed.

Lemma ex12_subst_not_free : forall e x v,
  free_in x e = false -> subst x v e = e.
Proof. intros. apply subst_not_free. assumption. Qed.

Lemma ex13_subst_closed : forall e x v,
  closed e -> subst x v e = e.
Proof. intros. apply subst_closed. assumption. Qed.

(* [Id "x"] on its own is not closed. *)
Lemma ex14_id_not_closed : ~ closed (Id "x").
Proof.
  intro H. specialize (H "x"). compute in H. discriminate.
Qed.

(** * PART 3: EVALUATION EQUATIONS *)

Lemma ex15_eval_plus : forall l r,
  eval (Plus l r) =
  match eval l, eval r with
  | Some a, Some b => Some (a + b)
  | _, _ => None
  end.
Proof. intros. apply eval_Plus. Qed.

Lemma ex16_eval_bind_num : forall x n b,
  eval (Bind x (Num n) b) = eval (subst x (Num n) b).
Proof. intros. apply bind_num_subst. Qed.

Lemma ex17_bind_const : forall x n m,
  eval (Bind x (Num n) (Num m)) = Some m.
Proof. intros. reflexivity. Qed.

(* Inner bindings shadow outer ones. *)
Lemma ex18_shadow : forall n m,
  eval (Bind "x" (Num n) (Bind "x" (Num m) (Id "x"))) = Some m.
Proof. intros. reflexivity. Qed.

(* An unused binding can be dropped. *)
Lemma ex19_bind_unused : forall x v b n,
  eval v = Some n ->
  free_in x b = false ->
  eval (Bind x v b) = eval b.
Proof. intros. eapply bind_unused; eassumption. Qed.

(** * PART 4: EQUIVALENCE *)

Lemma ex20_equiv_refl : forall e, bae_equiv e e.
Proof. exact bae_equiv_refl. Qed.

Lemma ex21_equiv_rename :
  bae_equiv (Bind "x" (Num 3) (Plus (Id "x") (Num 1)))
            (Bind "y" (Num 3) (Plus (Id "y") (Num 1))).
Proof. reflexivity. Qed.

(* Substituting into a closed term does not change its value. *)
Lemma ex22_eval_subst_closed : forall e x n,
  closed e -> eval (subst x (Num n) e) = eval e.
Proof.
  intros e x n H. rewrite subst_closed by assumption. reflexivity.
Qed.

(** * PART 5: FREE VARIABLES UNDER SUBSTITUTION *)

(* Substituting for [x] removes [x] from the free set. *)
Lemma ex23_x_not_free_after_subst : forall e n,
  free_in "x" (subst "x" (Num n) e) = false.
Proof.
  intros e n. rewrite free_in_subst_num. rewrite String.eqb_refl. reflexivity.
Qed.

(* Substituting for [x] does not disturb a different free variable. *)
Lemma ex24_other_free_preserved : forall e n z,
  z <> "x" ->
  free_in z (subst "x" (Num n) e) = free_in z e.
Proof.
  intros e n z Hz. rewrite free_in_subst_num.
  apply String.eqb_neq in Hz. rewrite Hz. reflexivity.
Qed.

(** * CHALLENGE PROBLEMS *)

(* Challenge 1: fuel independence - any sufficient fuel gives [eval]. *)
Lemma challenge1_fuel_independent : forall e f,
  size e <= f -> evalF f e = eval e.
Proof. intros e f H. apply evalF_eval. assumption. Qed.

(* Challenge 2: PROGRESS for closed programs.
   A closed BAE never gets "stuck": it always evaluates to a number.
   This is the substitution-semantics analogue of type safety.

   The proof recurses on fuel; the [Bind] case uses
   [closed_after_subst] to see that once the bound value is a number,
   the body becomes closed too. *)

Lemma progress_fuel : forall f e,
  size e <= f -> closed e -> exists m, evalF f e = Some m.
Proof.
  induction f as [| g IH]; intros e Hsz Hc.
  - pose proof (size_pos e). lia.
  - destruct e as [n | l r | l r | x v b | y]; simpl in Hsz.
    + (* Num n *) exists n. reflexivity.
    + (* Plus l r *)
      assert (Hl : closed l) by (intro z; specialize (Hc z);
        simpl in Hc; apply orb_false_iff in Hc; apply Hc).
      assert (Hr : closed r) by (intro z; specialize (Hc z);
        simpl in Hc; apply orb_false_iff in Hc; apply Hc).
      destruct (IH l ltac:(lia) Hl) as [a Ha].
      destruct (IH r ltac:(lia) Hr) as [b Hb].
      exists (a + b). simpl. rewrite Ha, Hb. reflexivity.
    + (* Minus l r *)
      assert (Hl : closed l) by (intro z; specialize (Hc z);
        simpl in Hc; apply orb_false_iff in Hc; apply Hc).
      assert (Hr : closed r) by (intro z; specialize (Hc z);
        simpl in Hc; apply orb_false_iff in Hc; apply Hc).
      destruct (IH l ltac:(lia) Hl) as [a Ha].
      destruct (IH r ltac:(lia) Hr) as [b Hb].
      exists (a - b). simpl. rewrite Ha, Hb. reflexivity.
    + (* Bind x v b *)
      assert (Hv : closed v) by (intro z; specialize (Hc z);
        simpl in Hc; apply orb_false_iff in Hc; apply Hc).
      assert (Hb : forall z, z <> x -> free_in z b = false).
      { intros z Hz. specialize (Hc z). simpl in Hc.
        apply orb_false_iff in Hc. destruct Hc as [_ Hc2].
        apply String.eqb_neq in Hz. rewrite Hz in Hc2. exact Hc2. }
      destruct (IH v ltac:(lia) Hv) as [n Hn].
      assert (Hsb : closed (subst x (Num n) b)) by (apply closed_after_subst; exact Hb).
      destruct (IH (subst x (Num n) b) ltac:(rewrite size_subst_num; lia) Hsb)
        as [m Hm].
      exists m. simpl. rewrite Hn. exact Hm.
    + (* Id y *)
      specialize (Hc y). simpl in Hc.
      rewrite String.eqb_refl in Hc. discriminate.
Qed.

Theorem challenge2_progress : forall e,
  closed e -> exists m, eval e = Some m.
Proof.
  intros e Hc. unfold eval. apply progress_fuel; [lia | exact Hc].
Qed.

(** * PART 6: CONCRETE SYNTAX *)

Open Scope bae_scope.

(* Exercise 25: the concrete form is definitionally the abstract tree. *)
Example ex25_parse_id : <{ "x" + 1 }> = Plus (Id "x") (Num 1).
Proof. reflexivity. Qed.

(* Exercise 26: [bind ID = e1 in e2] is [Bind]. *)
Example ex26_parse_bind :
  <{ bind "x" = 5 in "x" }> = Bind "x" (Num 5) (Id "x").
Proof. reflexivity. Qed.

(* Exercise 27: [eval] consumes the same tree the notation elaborates to. *)
Example ex27_eval_bind :
  eval <{ bind "x" = 3 in "x" + "x" }> = Some 6.
Proof. reflexivity. Qed.

(* Exercise 28: [bind "x" = n in "x" + "x"] reduces to [eval (Num n +
   Num n)] = [Some (n + n)]; it computes for a symbolic [n]. *)
Lemma ex28_bind_value : forall n : nat,
  eval <{ bind "x" = n in "x" + "x" }> = Some (n + n).
Proof. intro n. reflexivity. Qed.
