(** * Programming Languages in Rocq - Adding Environments *)

(**
This lecture covers:
#<ol>#
#<li>#Environments: deferring substitution with a table of bindings#</li>#
#<li>#A _clean_ structural interpreter [evalE] (no fuel this time!)#</li>#
#<li>#Extensionality of [evalE] over environments#</li>#
#<li>#The centrepiece: _proving_ that the environment interpreter and the substitution interpreter always agree, [forall e, evalE nil e = eval e].#</li>#
#</ol>#

This mirrors the "Adding Environments" section of PLIH:
  https://ku-sldg.github.io/plih//ids/2-Adding-Environments.html

The PLIH course only spot-checks the two interpreters for agreement on random
terms; here we prove that agreement outright, for _every_ term.
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
Instead of substituting a value the moment a binding is seen, we remember the
identifier/value pair in an _environment_ and look it up later.  We reuse [Env]
from the shared library, specialised to numbers:

  Env nat        = list (string * nat)
  extend x n env = (x, n) :: env
  lookup x env   = the first binding of x, or None

Consider [bind x = 4 in bind y = 5 in x + y - 4].  Rather than rewriting the
body twice, we push [(x,4)] then [(y,5)] onto the environment and consult it
when we reach [Id x] / [Id y].
 *)

(** * SECTION 2: THE ENVIRONMENT INTERPRETER *)

(**
Unlike the substitution interpreter, _this_ one is structurally recursive:
every recursive call is on a subterm ([v] or [b]), and the environment is just
an extra parameter carried along.  [Bind] evaluates the bound expression and
then the body in the _extended_ environment; [Id] is simply a [lookup].  So
Rocq accepts it as a plain [Fixpoint] - no fuel required this time.
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

(* The top-level interpreter starts from the empty environment. *)
Definition evalEnv (e : BAE) : option nat := evalE nil e.

(** * SECTION 3: TESTING THE INTERPRETER *)

(**
The same programs as the IDs chapter, now run under [evalE] from the empty
environment - same answers, and no fuel in sight.
 *)

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

(**
[contradiction] (used just above) closes a goal when the context already holds
an impossibility: here [subst] has collapsed the hypotheses so that they assert
both [x <> i] and [x = i], and [contradiction] spots the clash and finishes.
 *)

(** * SECTION 5: ENVIRONMENTS DEFER SUBSTITUTION *)

(**
_The key lemma._  Extending the environment with [(i, n)] is exactly the same
as substituting [Num n] for [i] first and then evaluating.  In other words, an
environment binding is nothing more than a _deferred_ substitution.

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
The agreement theorem, stated for the top-level interpreters - the Rocq
counterpart of the chapter's QuickCheck spot-check, but proved for _all_ terms.
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
Because the two interpreters agree, every theorem proved about the substitution
interpreter transfers for free.  For example _progress_ (a closed program never
gets stuck, proved as [challenge2_progress] in the IDs solutions) immediately
gives the same guarantee for the environment interpreter - see exercise
[ex_progress_transfer].
 *)

(** * SECTION 7: PROPERTIES OF THE ENVIRONMENT INTERPRETER *)

(**
The [evalE] analogues of the IDs "clean equations": a number ignores the
environment, an identifier is a lookup, and binding a literal just pushes it.
 *)

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
Environments changed only _how_ we evaluate, not the language itself, so
BAE keeps exactly the surface syntax introduced in the IDs chapter.
Because [plih_rocq_env_shared] re-exports the IDs lecture, the whole
concrete-syntax parser - the [<{ ... }>] notation, the [nat] -> [Num]
and [string] -> [Id] coercions, and the [bind ID = e1 in e2] form - is
already in scope here.  We simply open its notation scope; there is
nothing new to define.
 *)

Open Scope bae_scope.

(**
The very same concrete terms now drive the _environment_ interpreter.
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
And because the two interpreters _agree_ (Section 6), a concrete program
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
#<li>#Introduced _environments_ as deferred substitutions.#</li>#
#<li>#Defined [evalE], a clean _structural_ interpreter - no fuel, because it never rebuilds the term.#</li>#
#<li>#Proved extensionality of [evalE] and the key lemma [evalE (extend i n env) e = evalE env (subst i (Num n) e)].#</li>#
#<li>#Proved the two interpreters _agree_: [evalE nil e = eval e], so environments change only _how_ we evaluate, not _what_ we get.#</li>#
#<li>#Transferred _progress_ to the environment interpreter for free.#</li>#
#<li>#Reused the _inherited_ concrete syntax, so [<{ ... }>] programs run under the environment interpreter too - no new notation required.#</li>#
#</ol>#

Exercises: implement an error-reporting variant, and an interpreter
seeded with a _prelude_ (a starting environment of always-available
identifiers).
 *)

(** * NEW PROOF TACTICS IN THIS CHAPTER *)

(**
Almost every tactic here is reused from AE / ABE / IDs.  Two show up in a new
form worth naming:

#<ul>#
#<li>#[contradiction] - close any goal when the context already contains contradictory hypotheses (for instance [x <> i] together with [x = i]).#</li>#
#<li>#[cbn [f g ...]] - the _selective_ form of [cbn]: reduce, but unfold only the named definitions ([cbn [evalE]], [cbn [evalE subst]]), leaving everything else untouched so the goal stays readable.#</li>#
#</ul>#
 *)
