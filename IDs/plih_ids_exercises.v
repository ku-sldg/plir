(**
Programming Languages in Rocq - IDs Exercises
Adding Identifiers - Student Problem Set

In these exercises you will:
#<ol>#
#<li>#Run the substitution interpreter for BAE#</li>#
#<li>#Reason about substitution, free variables, and closed terms#</li>#
#<li>#Use the [eval] equation lemmas from the lecture#</li>#
#<li>#Prove PROGRESS: closed programs never get stuck (challenge)#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof
ending in [Qed].  The file compiles as given (Rocq accepts
[Admitted]), so you can check progress incrementally.

The BAE syntax, [subst], the fuel interpreter [eval] together with
its equation lemmas ([eval_Num], [eval_Plus], [eval_Minus],
[eval_Bind], [bind_num_subst], [bind_unused]), the free-variable
machinery ([free_in], [closed], [subst_not_free], [subst_closed],
[free_in_subst_num], [closed_after_subst]) and [bae_equiv] all come
from the lecture, which we import.

Difficulty: ★ trivial (reflexivity), ★★ one or two lemma
citations, ★★★ case analysis / small induction, ★★★★ harder.
Complete solutions are in plih_ids_solutions.v.
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

(* Exercise 1 ★: A literal evaluates to itself. *)
Example ex1_eval_num : eval (Num 42) = Some 42.
Proof. Admitted.

(* Exercise 2 ★: A bound identifier looks up its value. *)
Example ex2_eval_bind_id : eval (Bind "x" (Num 5) (Id "x")) = Some 5.
Proof. Admitted.

(* Exercise 3 ★: The bound value is shared by every use. *)
Example ex3_eval_bind_dup :
  eval (Bind "x" (Num 5) (Plus (Id "x") (Id "x"))) = Some 10.
Proof. Admitted.

(* Exercise 4 ★: A free identifier has no value. *)
Example ex4_eval_free : eval (Id "z") = None.
Proof. Admitted.

(* Exercise 5 ★: Nested bindings. *)
Example ex5_eval_nested :
  eval (Bind "x" (Num 4) (Bind "y" (Num 5) (Plus (Id "x") (Id "y"))))
  = Some 9.
Proof. Admitted.

(** * PART 1: SUBSTITUTION *)

(* Exercise 6 ★: Substituting for a matching identifier. *)
Example ex6_subst_leaf : subst "x" (Num 3) (Id "x") = Num 3.
Proof. Admitted.

(* Exercise 7 ★: Substituting leaves other identifiers alone. *)
Example ex7_subst_other : subst "x" (Num 3) (Id "y") = Id "y".
Proof. Admitted.

(* Exercise 8 ★: Substitution pushes through Plus. *)
Lemma ex8_subst_plus : forall i n a b,
  subst i (Num n) (Plus a b)
  = Plus (subst i (Num n) a) (subst i (Num n) b).
Proof. Admitted.

(* Exercise 9 ★★: Substituting a number preserves size.
   Hint: this is [size_subst_num] from the lecture. *)
Lemma ex9_subst_size : forall e i n,
  size (subst i (Num n) e) = size e.
Proof. Admitted.

(** * PART 2: FREE VARIABLES AND CLOSED TERMS *)

(* Exercise 10 ★: A number is closed. *)
Lemma ex10_closed_num : closed (Num 5).
Proof. Admitted.

(* Exercise 11 ★: free_in distributes over Plus. *)
Lemma ex11_free_in_plus : forall x a b,
  free_in x (Plus a b) = free_in x a || free_in x b.
Proof. Admitted.

(* Exercise 12 ★★: Substituting a non-free variable is a no-op.
   Hint: [subst_not_free]. *)
Lemma ex12_subst_not_free : forall e x v,
  free_in x e = false -> subst x v e = e.
Proof. Admitted.

(* Exercise 13 ★★: Substituting into a closed term is a no-op. *)
Lemma ex13_subst_closed : forall e x v,
  closed e -> subst x v e = e.
Proof. Admitted.

(* Exercise 14 ★★: A lone identifier is not closed.
   Hint: apply the hypothesis to "x", then [compute]. *)
Lemma ex14_id_not_closed : ~ closed (Id "x").
Proof. Admitted.

(** * PART 3: EVALUATION EQUATIONS *)

(* Exercise 15 ★: The evaluation equation for Plus. Hint: [eval_Plus]. *)
Lemma ex15_eval_plus : forall l r,
  eval (Plus l r) =
  match eval l, eval r with
  | Some a, Some b => Some (a + b)
  | _, _ => None
  end.
Proof. Admitted.

(* Exercise 16 ★★: Binding a literal is substitution.
   Hint: [bind_num_subst]. *)
Lemma ex16_eval_bind_num : forall x n b,
  eval (Bind x (Num n) b) = eval (subst x (Num n) b).
Proof. Admitted.

(* Exercise 17 ★: Binding a literal in a literal body. *)
Lemma ex17_bind_const : forall x n m,
  eval (Bind x (Num n) (Num m)) = Some m.
Proof. Admitted.

(* Exercise 18 ★: Inner bindings shadow outer ones. *)
Lemma ex18_shadow : forall n m,
  eval (Bind "x" (Num n) (Bind "x" (Num m) (Id "x"))) = Some m.
Proof. Admitted.

(* Exercise 19 ★★★: An unused binding can be dropped.
   Hint: [bind_unused]. *)
Lemma ex19_bind_unused : forall x v b n,
  eval v = Some n ->
  free_in x b = false ->
  eval (Bind x v b) = eval b.
Proof. Admitted.

(** * PART 4: EQUIVALENCE *)

(* Exercise 20 ★: Equivalence is reflexive. *)
Lemma ex20_equiv_refl : forall e, bae_equiv e e.
Proof. Admitted.

(* Exercise 21 ★★: Consistent renaming preserves meaning. *)
Lemma ex21_equiv_rename :
  bae_equiv (Bind "x" (Num 3) (Plus (Id "x") (Num 1)))
            (Bind "y" (Num 3) (Plus (Id "y") (Num 1))).
Proof. Admitted.

(* Exercise 22 ★★: Substituting into a closed term keeps its value. *)
Lemma ex22_eval_subst_closed : forall e x n,
  closed e -> eval (subst x (Num n) e) = eval e.
Proof. Admitted.

(** * PART 5: FREE VARIABLES UNDER SUBSTITUTION *)

(* Exercise 23 ★★: Substituting for [x] removes [x] from the free set.
   Hint: [free_in_subst_num]. *)
Lemma ex23_x_not_free_after_subst : forall e n,
  free_in "x" (subst "x" (Num n) e) = false.
Proof. Admitted.

(* Exercise 24 ★★★: Substituting for [x] leaves other free variables. *)
Lemma ex24_other_free_preserved : forall e n z,
  z <> "x" ->
  free_in z (subst "x" (Num n) e) = free_in z e.
Proof. Admitted.

(** * CHALLENGE PROBLEMS *)

(* Challenge 1 ★★: Any sufficient fuel computes [eval].
   Hint: [evalF_eval]. *)
Lemma challenge1_fuel_independent : forall e f,
  size e <= f -> evalF f e = eval e.
Proof. Admitted.

(* Challenge 2 ★★★★: PROGRESS - a closed program never gets stuck.
   Strategy: first prove a fuel-indexed version by induction on the
   fuel, using [closed_after_subst] in the [Bind] case; then specialise
   the fuel to [size e]. *)
Theorem challenge2_progress : forall e,
  closed e -> exists m, eval e = Some m.
Proof. Admitted.

(** * PART 6: CONCRETE SYNTAX *)

(**
The lecture added a notation-based parser: numerals coerce to [Num],
strings to [Id], [+]/[-] are the arithmetic operators, and
[bind ID = e1 in e2] is [Bind].  We open its scope to use it here.
 *)

Open Scope bae_scope.

(* Exercise 25 ★: an identifier use parses to [Id]. *)
Example ex25_parse_id : <{ "x" + 1 }> = Plus (Id "x") (Num 1).
Proof. Admitted.

(* Exercise 26 ★: a binding parses to [Bind]. *)
Example ex26_parse_bind :
  <{ bind "x" = 5 in "x" }> = Bind "x" (Num 5) (Id "x").
Proof. Admitted.

(* Exercise 27 ★★: evaluation is oblivious to the notation. *)
Example ex27_eval_bind :
  eval <{ bind "x" = 3 in "x" + "x" }> = Some 6.
Proof. Admitted.

(* Exercise 28 ★★: a "let" law stated in concrete syntax. *)
Lemma ex28_bind_value : forall n : nat,
  eval <{ bind "x" = n in "x" + "x" }> = Some (n + n).
Proof. Admitted.

(** * SUBMISSION GUIDELINES *)

(**
Replace every [Admitted] with a complete proof ending in [Qed].
When you are done, the file should compile with no remaining
[Admitted].  Compare your proofs against plih_ids_solutions.v.
 *)
