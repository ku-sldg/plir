(**
Programming Languages in Rocq - Env Exercises
Adding Environments - Student Problem Set

In these exercises you will:
  1. Run the environment interpreter [evalE] for BAE
  2. Reason about environments (extensionality, shadowing, swapping)
  3. Use the AGREEMENT theorem relating [evalE] and the substitution
     interpreter [eval]
  4. Build a prelude interpreter and an error-reporting interpreter

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof
ending in [Qed].  The file compiles as given.

From the Env lecture you have: [evalE], [evalEnv], [evalE_ext],
[lookup_shadow_env], [lookup_swap_env], [evalE_extend_subst],
[evalE_agrees_eval], [evalE_bind_num].  From the IDs chapter you have
[BAE], [subst], [eval], [closed], [bae_example_1], and (for a
challenge) [challenge2_progress].  The lookup lemmas [lookup_extend_eq]
and [lookup_extend_ne] come from the shared library.

The [prelude] interpreter and the error interpreter [evalErr] are
PROVIDED below; the exercises are to prove properties about them.

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof,
★★★★ induction.  Solutions are in plih_env_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_env_shared.
Require Import plih_env_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * WARM-UP: RUNNING THE ENVIRONMENT INTERPRETER *)

(* Exercise 1 ★ *)
Example ex1_evalE_num : evalE nil (Num 7) = Some 7.
Proof. Admitted.

(* Exercise 2 ★ *)
Example ex2_evalE_bind : evalE nil (Bind "x" (Num 5) (Id "x")) = Some 5.
Proof. Admitted.

(* Exercise 3 ★ *)
Example ex3_evalE_nested :
  evalE nil (Bind "x" (Num 4) (Bind "y" (Num 5) (Plus (Id "x") (Id "y"))))
  = Some 9.
Proof. Admitted.

(* Exercise 4 ★ *)
Example ex4_evalE_free : evalE nil (Id "x") = None.
Proof. Admitted.

(* Exercise 5 ★ *)
Example ex5_evalE_shadow :
  evalE nil (Bind "x" (Num 1) (Bind "x" (Num 2) (Id "x"))) = Some 2.
Proof. Admitted.

(** * PART 1: EQUATIONS FOR evalE *)

(* Exercise 6 ★ *)
Lemma ex6_evalE_num : forall env n, evalE env (Num n) = Some n.
Proof. Admitted.

(* Exercise 7 ★ *)
Lemma ex7_evalE_id : forall env x, evalE env (Id x) = lookup x env.
Proof. Admitted.

(* Exercise 8 ★: Hint: [evalE_bind_num]. *)
Lemma ex8_evalE_bind_num : forall env x n b,
  evalE env (Bind x (Num n) b) = evalE (extend x n env) b.
Proof. Admitted.

(* Exercise 9 ★★: Hint: [lookup_extend_eq]. *)
Lemma ex9_evalE_id_bound : forall env x n,
  evalE (extend x n env) (Id x) = Some n.
Proof. Admitted.

(** * PART 2: EXTENSIONALITY, SHADOWING, SWAPPING *)

(* Exercise 10 ★: Hint: [evalE_ext]. *)
Lemma ex10_evalE_ext : forall e env1 env2,
  (forall y, lookup y env1 = lookup y env2) ->
  evalE env1 e = evalE env2 e.
Proof. Admitted.

(* Exercise 11 ★★★: Hint: [evalE_ext] + [lookup_shadow_env]. *)
Lemma ex11_evalE_shadow : forall e env x m n,
  evalE (extend x m (extend x n env)) e = evalE (extend x m env) e.
Proof. Admitted.

(* Exercise 12 ★★★: Hint: [evalE_ext] + [lookup_swap_env]. *)
Lemma ex12_evalE_swap : forall e env x i m n,
  x <> i ->
  evalE (extend x m (extend i n env)) e = evalE (extend i n (extend x m env)) e.
Proof. Admitted.

(** * PART 3: AGREEMENT WITH THE SUBSTITUTION INTERPRETER *)

(* Exercise 13 ★: Hint: [evalE_agrees_eval]. *)
Lemma ex13_agree : forall e, evalE nil e = eval e.
Proof. Admitted.

(* Exercise 14 ★★ *)
Lemma ex14_agree_example :
  evalE nil bae_example_1 = eval bae_example_1.
Proof. Admitted.

(* Exercise 15 ★: Hint: [evalE_extend_subst]. *)
Lemma ex15_extend_is_subst : forall e env i n,
  evalE (extend i n env) e = evalE env (subst i (Num n) e).
Proof. Admitted.

(* Exercise 16 ★★★★: PROGRESS transfers to the environment
   interpreter.  Hint: rewrite with [evalE_agrees_eval], then apply
   [challenge2_progress] from the IDs solutions.  (You will need to add
   [Require Import plih_ids_solutions.] to attempt this one.) *)
Lemma ex16_progress_transfer : forall e,
  closed e -> exists m, evalE nil e = Some m.
Proof. Admitted.

(** * PART 4: A PRELUDE (PROVIDED) *)

Definition prelude : Env nat := extend "answer" 42 (extend "pi" 3 nil).
Definition evalPrelude (e : BAE) : option nat := evalE prelude e.

(* Exercise 17 ★ *)
Lemma ex17_prelude_answer : evalPrelude (Id "answer") = Some 42.
Proof. Admitted.

(* Exercise 18 ★ *)
Lemma ex18_prelude_pi : evalPrelude (Plus (Id "pi") (Id "pi")) = Some 6.
Proof. Admitted.

(* Exercise 19 ★★ *)
Lemma ex19_prelude_shadow :
  evalPrelude (Bind "answer" (Num 1) (Id "answer")) = Some 1.
Proof. Admitted.

(** * PART 5: AN ERROR-REPORTING INTERPRETER (PROVIDED) *)

Definition Result : Type := sum string nat.

Definition forget (r : Result) : option nat :=
  match r with
  | inl _ => None
  | inr n => Some n
  end.

Fixpoint evalErr (env : Env nat) (e : BAE) : Result :=
  match e with
  | Num n => inr n
  | Plus l r =>
      match evalErr env l, evalErr env r with
      | inr a, inr b => inr (a + b)
      | inl s, _ => inl s
      | _, inl s => inl s
      end
  | Minus l r =>
      match evalErr env l, evalErr env r with
      | inr a, inr b => inr (a - b)
      | inl s, _ => inl s
      | _, inl s => inl s
      end
  | Bind i v b =>
      match evalErr env v with
      | inl s => inl s
      | inr n => evalErr (extend i n env) b
      end
  | Id x =>
      match lookup x env with
      | Some n => inr n
      | None => inl "unbound identifier"
      end
  end.

(* Exercise 20 ★ *)
Lemma ex20_evalErr_num : forall env n, evalErr env (Num n) = inr n.
Proof. Admitted.

(* Exercise 21 ★★★★: [evalErr] refines [evalE].  Induction on [e];
   the [Plus]/[Minus] cases rewrite with the IHs then case-split on
   both recursive results. *)
Lemma ex21_forget_evalErr : forall e env,
  forget (evalErr env e) = evalE env e.
Proof. Admitted.

(* Exercise 22 ★★: Hint: [ex21_forget_evalErr] + [evalE_agrees_eval]. *)
Lemma ex22_forget_evalErr_eval : forall e,
  forget (evalErr nil e) = eval e.
Proof. Admitted.

(** * CHALLENGE PROBLEMS *)

(* Challenge 1 ★: a free identifier produces an error message. *)
Lemma challenge1_unbound_reports : exists s,
  evalErr nil (Id "x") = inl s.
Proof. Admitted.

(* Challenge 2 ★★: equivalence is the same under either interpreter. *)
Lemma challenge2_equiv_agree : forall e1 e2,
  eval e1 = eval e2 <-> evalE nil e1 = evalE nil e2.
Proof. Admitted.

(** * PART 6: CONCRETE SYNTAX (INHERITED) *)

(**
The [<{ ... }>] parser is inherited from the IDs chapter (re-exported
through the shared library); we just open its scope.  These programs
now drive the ENVIRONMENT interpreter.
 *)

Open Scope bae_scope.

(* Exercise 23 ★: a concrete program under the environment interpreter. *)
Example ex23_evalE_concrete :
  evalEnv <{ bind "x" = 3 in "x" + "x" }> = Some 6.
Proof. Admitted.

(* Exercise 24 ★★: a concrete program means the same thing under either
   interpreter.  Hint: [evalEnv_agrees_eval]. *)
Example ex24_agree_concrete :
  evalEnv <{ bind "x" = 4 in "x" - 1 }> = eval <{ bind "x" = 4 in "x" - 1 }>.
Proof. Admitted.

(** * SUBMISSION GUIDELINES *)

(**
Replace every [Admitted] with a complete proof ending in [Qed].
Compare your proofs against plih_env_solutions.v.
 *)
