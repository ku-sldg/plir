(**
Programming Languages in Rocq - Env Solutions
Complete solutions to plih_env_exercises.v

The BAE syntax, [subst], [eval], [size], the free-variable machinery
and [challenge2_progress] come from the IDs chapter; [evalE],
[evalE_ext], [evalE_extend_subst], [evalE_agrees_eval] and the
lookup lemmas come from the Env lecture.  The [prelude] interpreter
and the error-reporting interpreter [evalErr] are defined here (and,
identically, in the exercises file).
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_env_shared.
Require Import plih_env_lecture.
Require Import plih_ids_solutions.

Local Open Scope string_scope.
Import ListNotations.

(** * WARM-UP: RUNNING THE ENVIRONMENT INTERPRETER *)

Example ex1_evalE_num : evalE nil (Num 7) = Some 7.
Proof. reflexivity. Qed.

Example ex2_evalE_bind : evalE nil (Bind "x" (Num 5) (Id "x")) = Some 5.
Proof. reflexivity. Qed.

Example ex3_evalE_nested :
  evalE nil (Bind "x" (Num 4) (Bind "y" (Num 5) (Plus (Id "x") (Id "y"))))
  = Some 9.
Proof. reflexivity. Qed.

Example ex4_evalE_free : evalE nil (Id "x") = None.
Proof. reflexivity. Qed.

Example ex5_evalE_shadow :
  evalE nil (Bind "x" (Num 1) (Bind "x" (Num 2) (Id "x"))) = Some 2.
Proof. reflexivity. Qed.

(** * PART 1: EQUATIONS FOR evalE *)

Lemma ex6_evalE_num : forall env n, evalE env (Num n) = Some n.
Proof. reflexivity. Qed.

Lemma ex7_evalE_id : forall env x, evalE env (Id x) = lookup x env.
Proof. reflexivity. Qed.

Lemma ex8_evalE_bind_num : forall env x n b,
  evalE env (Bind x (Num n) b) = evalE (extend x n env) b.
Proof. reflexivity. Qed.

Lemma ex9_evalE_id_bound : forall env x n,
  evalE (extend x n env) (Id x) = Some n.
Proof. intros. cbn [evalE]. apply lookup_extend_eq. Qed.

(** * PART 2: EXTENSIONALITY, SHADOWING, SWAPPING *)

Lemma ex10_evalE_ext : forall e env1 env2,
  (forall y, lookup y env1 = lookup y env2) ->
  evalE env1 e = evalE env2 e.
Proof. exact evalE_ext. Qed.

Lemma ex11_evalE_shadow : forall e env x m n,
  evalE (extend x m (extend x n env)) e = evalE (extend x m env) e.
Proof.
  intros. apply evalE_ext. intro y. apply lookup_shadow_env.
Qed.

Lemma ex12_evalE_swap : forall e env x i m n,
  x <> i ->
  evalE (extend x m (extend i n env)) e = evalE (extend i n (extend x m env)) e.
Proof.
  intros e env x i m n H. apply evalE_ext. intro y. apply lookup_swap_env. exact H.
Qed.

(** * PART 3: AGREEMENT WITH THE SUBSTITUTION INTERPRETER *)

Lemma ex13_agree : forall e, evalE nil e = eval e.
Proof. exact evalE_agrees_eval. Qed.

Lemma ex14_agree_example :
  evalE nil bae_example_1 = eval bae_example_1.
Proof. apply evalE_agrees_eval. Qed.

Lemma ex15_extend_is_subst : forall e env i n,
  evalE (extend i n env) e = evalE env (subst i (Num n) e).
Proof. exact evalE_extend_subst. Qed.

(* PROGRESS transfers to the environment interpreter for free. *)
Lemma ex16_progress_transfer : forall e,
  closed e -> exists m, evalE nil e = Some m.
Proof.
  intros e Hc. rewrite evalE_agrees_eval. apply challenge2_progress. exact Hc.
Qed.

(** * PART 4: A PRELUDE *)

(* A prelude is a starting environment of always-available bindings. *)
Definition prelude : Env nat := extend "answer" 42 (extend "pi" 3 nil).
Definition evalPrelude (e : BAE) : option nat := evalE prelude e.

Lemma ex17_prelude_answer : evalPrelude (Id "answer") = Some 42.
Proof. reflexivity. Qed.

Lemma ex18_prelude_pi : evalPrelude (Plus (Id "pi") (Id "pi")) = Some 6.
Proof. reflexivity. Qed.

(* A local binding can shadow a prelude entry. *)
Lemma ex19_prelude_shadow :
  evalPrelude (Bind "answer" (Num 1) (Id "answer")) = Some 1.
Proof. reflexivity. Qed.

(** * PART 5: AN ERROR-REPORTING INTERPRETER *)

(**
The Haskell course suggests an [evalErr] using [Either] to return a
value OR an error message.  Here [Result = string + nat]: [inl msg]
is an error, [inr n] is a value.  [forget] erases the message, so we
can state that [evalErr] refines [evalE].
 *)

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

Lemma ex20_evalErr_num : forall env n, evalErr env (Num n) = inr n.
Proof. reflexivity. Qed.

(* The error interpreter refines the option interpreter. *)
Lemma ex21_forget_evalErr : forall e env,
  forget (evalErr env e) = evalE env e.
Proof.
  induction e as [m | l IHl r IHr | l IHl r IHr | i v IHv b IHb | x];
    intros env; simpl.
  - reflexivity.
  - rewrite <- (IHl env), <- (IHr env).
    destruct (evalErr env l); destruct (evalErr env r); reflexivity.
  - rewrite <- (IHl env), <- (IHr env).
    destruct (evalErr env l); destruct (evalErr env r); reflexivity.
  - rewrite <- (IHv env).
    destruct (evalErr env v) as [s | n]; simpl.
    + reflexivity.
    + apply IHb.
  - destruct (lookup x env); reflexivity.
Qed.

(* Hence [evalErr] on the empty environment refines the substitution
   interpreter too. *)
Lemma ex22_forget_evalErr_eval : forall e,
  forget (evalErr nil e) = eval e.
Proof.
  intro e. rewrite ex21_forget_evalErr. apply evalE_agrees_eval.
Qed.

(** * CHALLENGE PROBLEMS *)

(* Challenge 1: a free identifier produces an error message. *)
Lemma challenge1_unbound_reports : exists s,
  evalErr nil (Id "x") = inl s.
Proof. exists "unbound identifier". reflexivity. Qed.

(* Challenge 2: semantic equivalence is the same whether measured by
   the substitution interpreter or the environment interpreter. *)
Lemma challenge2_equiv_agree : forall e1 e2,
  eval e1 = eval e2 <-> evalE nil e1 = evalE nil e2.
Proof.
  intros e1 e2. rewrite (evalE_agrees_eval e1), (evalE_agrees_eval e2).
  reflexivity.
Qed.

(** * PART 6: CONCRETE SYNTAX (INHERITED) *)

Open Scope bae_scope.

(* Exercise 23: the concrete program runs under [evalEnv] by computation. *)
Example ex23_evalE_concrete :
  evalEnv <{ bind "x" = 3 in "x" + "x" }> = Some 6.
Proof. reflexivity. Qed.

(* Exercise 24: the two interpreters agree on every term. *)
Example ex24_agree_concrete :
  evalEnv <{ bind "x" = 4 in "x" - 1 }> = eval <{ bind "x" = 4 in "x" - 1 }>.
Proof. apply evalEnv_agrees_eval. Qed.
