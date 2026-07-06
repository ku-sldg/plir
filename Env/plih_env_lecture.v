(**
Programming Languages in Rocq - Env Lecture
Adding Environments

This lecture covers:
  1. Environments: deferring substitution with a table of bindings
  2. A CLEAN structural interpreter [evalE] (no fuel this time!)
  3. Extensionality of [evalE] over environments
  4. The centrepiece: PROVING that the environment interpreter and
     the substitution interpreter always agree,
       forall e, evalE nil e = eval e.

This mirrors the "Adding Environments" section of PLIH:
  https://ku-sldg.github.io/plih//ids/2-Adding-Environments.html

The Haskell course validates the two interpreters with QuickCheck
([\t -> eval [] t == evals t]); here we prove agreement outright.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_env_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: ENVIRONMENTS *)

(**
Instead of substituting a value the moment a binding is seen, we
remember the identifier/value pair in an ENVIRONMENT and look it up
later.  This is exactly the Haskell course's design:

  type Env = [(String, BAE)]

We reuse [Env] from the shared library, specialised to numbers:
  Env nat = list (string * nat)
  extend x n env = (x, n) :: env
  lookup x env   = first binding of x, or None

Consider [bind x = 4 in bind y = 5 in x + y - 4].  Rather than
rewriting the body twice, we push [(x,4)] then [(y,5)] onto the
environment and consult it when we reach [Id x] / [Id y].
 *)

(** * SECTION 2: THE ENVIRONMENT INTERPRETER *)

(**
Compare to Haskell:
  eval :: Env -> BAE -> Maybe BAE
  eval env (Num x)      = Just (Num x)
  eval env (Plus l r)   = ... liftNum (+) ...
  eval env (Minus l r)  = ... liftNum (-) ...
  eval env (Bind i v b) = do { v' <- eval env v ;
                               eval ((i,v'):env) b }
  eval env (Id id)      = lookup id env

Unlike the substitution interpreter, THIS one is structurally
recursive: every recursive call is on a subterm ([v] or [b]); the
environment is just an extra parameter.  So Rocq accepts it as a
plain [Fixpoint] - no fuel required.
 *)

Fixpoint evalE (env : Env nat) (e : BAE) : option nat :=
  match e with
  | Num n => Some n
  | Plus l r =>
      match evalE env l, evalE env r with
      | Some a, Some b => Some (a + b)
      | _, _ => None
      end
  | Minus l r =>
      match evalE env l, evalE env r with
      | Some a, Some b => Some (a - b)
      | _, _ => None
      end
  | Bind i v b =>
      match evalE env v with
      | Some n => evalE (extend i n env) b
      | None => None
      end
  | Id x => lookup x env
  end.

(* The top-level interpreter starts from the empty environment.
   Compare Haskell: [interp = (eval []) . parseBAE]. *)
Definition evalEnv (e : BAE) : option nat := evalE nil e.

(** * SECTION 3: TESTING THE INTERPRETER *)

Example test_evalE_1 :
  evalE nil (Bind "x" (Plus (Num 5) (Num 2))
                      (Minus (Plus (Id "x") (Id "x")) (Num 4)))
  = Some 10.
Proof. reflexivity. Qed.

Example test_evalE_2 :
  evalE nil (Bind "x" (Num 4) (Bind "y" (Num 5)
                      (Minus (Plus (Id "x") (Id "y")) (Num 4))))
  = Some 5.
Proof. reflexivity. Qed.

(* Free identifiers still fail. *)
Example test_evalE_free :
  evalE nil (Plus (Id "x") (Num 1)) = None.
Proof. reflexivity. Qed.

(* Inner bindings shadow outer ones. *)
Example test_evalE_shadow :
  evalE nil (Bind "x" (Num 1) (Bind "x" (Num 2) (Id "x"))) = Some 2.
Proof. reflexivity. Qed.

(** * SECTION 4: ENVIRONMENT LEMMAS *)

(**
Two environments that answer every lookup the same way drive [evalE]
to the same result.  This "extensionality" principle is the tool we
use to reason about shadowing and reordering of bindings.
 *)
Lemma evalE_ext : forall e env1 env2,
  (forall y, lookup y env1 = lookup y env2) ->
  evalE env1 e = evalE env2 e.
Proof.
  induction e as [n | l IHl r IHr | l IHl r IHr | i v IHv b IHb | x];
    intros env1 env2 H; simpl.
  - reflexivity.
  - rewrite (IHl env1 env2 H), (IHr env1 env2 H). reflexivity.
  - rewrite (IHl env1 env2 H), (IHr env1 env2 H). reflexivity.
  - rewrite (IHv env1 env2 H).
    destruct (evalE env2 v) as [m |]; [| reflexivity].
    apply IHb. intro y. simpl. destruct (String.eqb y i).
    + reflexivity.
    + apply H.
  - apply H.
Qed.

(* A shadowed binding is invisible to lookup. *)
Lemma lookup_shadow_env : forall (env : Env nat) x m n y,
  lookup y (extend x m (extend x n env)) = lookup y (extend x m env).
Proof.
  intros env x m n y. simpl. destruct (String.eqb y x); reflexivity.
Qed.

(* Bindings for distinct identifiers may be reordered. *)
Lemma lookup_swap_env : forall (env : Env nat) x i m n y,
  x <> i ->
  lookup y (extend x m (extend i n env))
  = lookup y (extend i n (extend x m env)).
Proof.
  intros env x i m n y Hxi. simpl.
  destruct (String.eqb y x) eqn:Eyx; destruct (String.eqb y i) eqn:Eyi;
    try reflexivity.
  apply String.eqb_eq in Eyx. apply String.eqb_eq in Eyi. subst.
  contradiction.
Qed.

(** * SECTION 5: ENVIRONMENTS DEFER SUBSTITUTION *)

(**
THE KEY LEMMA.  Extending the environment with [(i, n)] is exactly
the same as substituting [Num n] for [i] first and then evaluating.
In other words, an environment binding is nothing more than a
DEFERRED substitution.

The proof is by induction on the expression.  The interesting case
is [Bind]: we must reconcile a newly pushed binding with the deferred
one, using [lookup_shadow_env] (when the names coincide) and
[lookup_swap_env] (when they differ) via [evalE_ext].
 *)
Lemma evalE_extend_subst : forall e env i n,
  evalE (extend i n env) e = evalE env (subst i (Num n) e).
Proof.
  induction e as [m | l IHl r IHr | l IHl r IHr | x v IHv b IHb | y];
    intros env i n.
  - reflexivity.
  - simpl. rewrite (IHl env i n), (IHr env i n). reflexivity.
  - simpl. rewrite (IHl env i n), (IHr env i n). reflexivity.
  - (* Bind x v b *)
    simpl subst. destruct (String.eqb i x) eqn:Eix.
    + (* i = x : the inner binder shadows i in the body *)
      apply String.eqb_eq in Eix. subst x.
      cbn [evalE]. rewrite (IHv env i n).
      destruct (evalE env (subst i (Num n) v)) as [m |]; [| reflexivity].
      apply evalE_ext. intro y. apply lookup_shadow_env.
    + (* i <> x : substitute in the body too *)
      apply String.eqb_neq in Eix.
      cbn [evalE]. rewrite (IHv env i n).
      destruct (evalE env (subst i (Num n) v)) as [m |]; [| reflexivity].
      rewrite <- (IHb (extend x m env) i n).
      apply evalE_ext. intro y. apply lookup_swap_env. apply not_eq_sym. exact Eix.
  - (* Id y *)
    cbn [evalE subst]. destruct (String.eqb i y) eqn:E.
    + apply String.eqb_eq in E. subst y.
      cbn [evalE]. rewrite lookup_extend_eq. reflexivity.
    + cbn [evalE].
      rewrite lookup_extend_ne by (rewrite string_eqb_sym; exact E).
      reflexivity.
Qed.

(** * SECTION 6: AGREEMENT OF THE TWO INTERPRETERS *)

(**
Now we prove the headline result: the environment interpreter
[evalE nil] computes exactly the same answers as the substitution
interpreter [eval] from the previous chapter.

We reason against the fuel form [evalF] (recall [eval e = evalF
(size e) e]).  The [Bind] case ties everything together: the key
lemma turns the pushed environment binding back into a substitution,
and [size_subst_num] keeps the fuel accounting straight.
 *)
Lemma evalE_evalF : forall f e,
  size e <= f -> evalE nil e = evalF f e.
Proof.
  induction f as [| g IH]; intros e Hsz.
  - pose proof (size_pos e). lia.
  - destruct e as [n | l r | l r | x v b | y]; simpl in Hsz.
    + reflexivity.
    + (* Plus l r *)
      cbn [evalF]. simpl.
      rewrite (IH l) by lia. rewrite (IH r) by lia. reflexivity.
    + (* Minus l r *)
      cbn [evalF]. simpl.
      rewrite (IH l) by lia. rewrite (IH r) by lia. reflexivity.
    + (* Bind x v b *)
      cbn [evalF]. simpl.
      rewrite (IH v) by lia.
      destruct (evalF g v) as [m |]; [| reflexivity].
      rewrite evalE_extend_subst.
      rewrite (IH (subst x (Num m) b)) by (rewrite size_subst_num; lia).
      reflexivity.
    + (* Id y *)
      reflexivity.
Qed.

(**
The agreement theorem, stated for the top-level interpreters.  This
is the Rocq counterpart of the chapter's QuickCheck property
[\t -> eval [] t == evals t].
 *)
Theorem evalE_agrees_eval : forall e,
  evalE nil e = eval e.
Proof.
  intro e. unfold eval. apply evalE_evalF. lia.
Qed.

Corollary evalEnv_agrees_eval : forall e,
  evalEnv e = eval e.
Proof. intro e. apply evalE_agrees_eval. Qed.

(**
Because the two interpreters agree, every theorem proved about the
substitution interpreter transfers for free.  For example PROGRESS
(a closed program never gets stuck, proved as [challenge2_progress]
in the IDs solutions) immediately gives the same guarantee for the
environment interpreter - see exercise [ex_progress_transfer].
 *)

(** * SECTION 7: PROPERTIES OF THE ENVIRONMENT INTERPRETER *)

(* A number ignores the environment. *)
Lemma evalE_num : forall env n, evalE env (Num n) = Some n.
Proof. reflexivity. Qed.

(* An identifier is just a lookup. *)
Lemma evalE_id : forall env x, evalE env (Id x) = lookup x env.
Proof. reflexivity. Qed.

(* Binding a literal pushes it onto the environment. *)
Lemma evalE_bind_num : forall env x n b,
  evalE env (Bind x (Num n) b) = evalE (extend x n env) b.
Proof. reflexivity. Qed.

(** * SECTION 8: CONCRETE SYNTAX (INHERITED) *)

(**
Environments changed only HOW we evaluate, not the language itself, so
BAE keeps exactly the surface syntax introduced in the IDs chapter.
Because [plih_rocq_env_shared] re-exports the IDs lecture, the whole
concrete-syntax parser - the [<{ ... }>] notation, the [nat] -> [Num]
and [string] -> [Id] coercions, and the [bind ID = e1 in e2] form - is
already in scope here.  We simply open its notation scope; there is
nothing new to define.
 *)

Open Scope bae_scope.

(**
The very same concrete terms now drive the ENVIRONMENT interpreter.
Here are the Section 3 tests, rewritten concretely.
 *)

Example evalE_concrete_bind :
  evalE nil <{ bind "x" = 5 + 2 in "x" + "x" - 4 }> = Some 10.
Proof. reflexivity. Qed.

Example evalE_concrete_nested :
  evalEnv <{ bind "x" = 4 in bind "y" = 5 in "x" + "y" - 4 }> = Some 5.
Proof. reflexivity. Qed.

Example evalE_concrete_free : evalEnv <{ "x" + 1 }> = None.
Proof. reflexivity. Qed.

Example evalE_concrete_shadow :
  evalEnv <{ bind "x" = 1 in bind "x" = 2 in "x" }> = Some 2.
Proof. reflexivity. Qed.

(**
And because the two interpreters AGREE (Section 6), a concrete program
has the same meaning under either one.
 *)
Example agree_concrete :
  evalEnv <{ bind "x" = 5 + 2 in "x" + "x" - 4 }>
  = eval  <{ bind "x" = 5 + 2 in "x" + "x" - 4 }>.
Proof. apply evalEnv_agrees_eval. Qed.

(** * SUMMARY *)

(**
In this lecture we:
#<ol>#
#<li>#Introduced ENVIRONMENTS as deferred substitutions.#</li>#
#<li>#Defined [evalE], a clean STRUCTURAL interpreter - no fuel,
because it never rebuilds the term.#</li>#
#<li>#Proved extensionality of [evalE] and the key lemma
evalE (extend i n env) e = evalE env (subst i (Num n) e).#</li>#
#<li>#Proved the two interpreters AGREE: [evalE nil e = eval e],
so environments change only HOW we evaluate, not WHAT we get.#</li>#
#<li>#Transferred PROGRESS to the environment interpreter for free.#</li>#
#<li>#Reused the INHERITED concrete syntax, so [<{ ... }>] programs run
under the environment interpreter too - no new notation required.#</li>#
#</ol>#

Exercises: implement an error-reporting variant, and an interpreter
seeded with a PRELUDE (a starting environment of always-available
identifiers).
 *)
