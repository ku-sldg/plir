(** * Programming Languages in Rocq - Env AI-Assisted Exercises *)

(**
This file contains four AI-assisted exercises for the Env chapter.
Each exercise pairs a Rocq proof task with a structured dialogue you will hold
with Claude (or another AI assistant).  The goals are:

#<ol>#
#<li>#Understand [lookup]/[extend] properties from first principles.#</li>#
#<li>#Understand how irrelevant environment bindings can be discarded.#</li>#
#<li>#Understand the inductive structure of the agreement theorem through
     two representative cases.#</li>#
#<li>#Understand (through dialogue) the structural differences between the
     substitution and environment interpreter designs.#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Read the "Ask Claude:" prompts before opening Rocq.  Hold the dialogue first,
then attempt the Rocq tasks.  Each lemma ends in [Admitted]; students who
complete the proof replace [Admitted] with a complete proof.  The file
compiles as given.

Difficulty: ★★ = one or two lemma citations, ★★★ = short proof with a
key lemma.
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

(** * EXERCISE 1 (★★): Lookup properties from first principles *)

(**
The shared library already provides [lookup_extend_eq] and
[lookup_extend_ne].  This exercise asks you to prove those same facts
_without_ citing those library lemmas - only by unfolding [extend] and
[lookup] directly.

Ask Claude:
#<ol>#
#<li>#"Here are the definitions of [extend] and [lookup] from the shared library:
     [extend x v env := (x, v) :: env] and
     [lookup x env] scans the list for the first pair whose key equals [x].
     Please prove [ai1a_lookup_same] and [ai1b_lookup_other] using only
     [unfold], [simpl], [destruct], [rewrite], [apply], [reflexivity],
     [subst], and [contradiction].  Do not use [lookup_extend_eq] or
     [lookup_extend_ne]."#</li>#
#<li>#After Claude gives you the proofs, ask: "The library [plih_rocq_ae_shared]
     already contains [lookup_extend_eq] and [lookup_extend_ne].  Why are those
     lemmas placed in the _shared_ library rather than in the Env chapter itself?"#</li>#
#</ol>#

Reflect: These lemmas feel trivially obvious.  Why does Rocq need them proved
at all?  What does it mean that Rocq treats them as non-trivial proof
obligations even though they follow directly from the definition by a single
[unfold]?
 *)

(* Prove without using [lookup_extend_eq] or [lookup_extend_ne]. *)
Lemma ai1a_lookup_same : forall (env : Env nat) x n,
  lookup x (extend x n env) = Some n.
Proof. Admitted.

Lemma ai1b_lookup_other : forall (env : Env nat) x y n,
  x <> y ->
  lookup y (extend x n env) = lookup y env.
Proof. Admitted.

(** * EXERCISE 2 (★★★): The environment interpreter ignores irrelevant bindings *)

(**
If [x] is not free in [e], then extending the environment with a binding for
[x] makes no difference to [evalE].  This is sometimes called the
_irrelevance lemma_.

Ask Claude:
#<ol>#
#<li>#"Please prove [ai2_evalE_irrelevant_binding].  The key lemmas available
     are [evalE_extend_subst] and [subst_not_free]."#</li>#
#<li>#After Claude gives you a proof, ask it to explain the proof in plain
     English: why does extending the environment with [(x, n)] have the same
     effect as substituting [Num n] for [x], and why does [subst_not_free]
     then finish the job?"#</li>#
#</ol>#

Reflect: This lemma is sometimes called "the irrelevance lemma."  Ask Claude:
what does it say about compiler optimisation?  Could a compiler use this
result to safely discard dead bindings without changing the observable
behaviour of a program?
 *)

Lemma ai2_evalE_irrelevant_binding : forall e env x n,
  free_in x e = false ->
  evalE (extend x n env) e = evalE env e.
Proof. Admitted.

(** * EXERCISE 3 (★★): Agreement for specific expression forms *)

(**
The full agreement theorem ([evalEnv e = eval e] for all [e]) is proved as
[evalEnv_agrees_eval] in the lecture.  This exercise asks you to prove the
[Num] and [Plus] cases as _standalone_ lemmas, with the IHs supplied as
hypotheses, so you can see the inductive structure without the overhead of
setting up the full induction.

Ask Claude:
#<ol>#
#<li>#"Please prove [ai3a_agree_num] and [ai3b_agree_plus].  Available lemmas:
     [evalE_num], [eval_Num], [eval_Plus].  For [ai3b], the induction
     hypotheses are supplied as [H] and [H0]."#</li>#
#<li>#After Claude proves these two cases, ask: "If I proved agreement
     separately for [Num], [Plus], [Minus], [Id], and [Bind], would those five
     proofs together constitute a proof of [forall e, evalEnv e = eval e]?
     What Rocq tactic packages these cases into a single inductive proof?"
     (Expected answer: [induction e].)"#</li>#
#</ol>#

Reflect: Ask Claude why the [Bind] case of the full agreement theorem is much
harder than [Num] and [Plus].  Which lemma in the lecture bridges the gap
between the environment and the substitution?  (Hint: look at
[evalE_extend_subst].)
 *)

Lemma ai3a_agree_num : forall n,
  evalEnv (Num n) = eval (Num n).
Proof. Admitted.

Lemma ai3b_agree_plus : forall l r,
  evalEnv l = eval l ->
  evalEnv r = eval r ->
  evalEnv (Plus l r) = eval (Plus l r).
Proof. Admitted.

(** * EXERCISE 4 (Written): Comparing the two interpreter designs *)

(**
This exercise has no Rocq proof task.  Hold a dialogue with Claude and write a
short reflection (a paragraph or two, in comments below) covering all four
questions.

Ask Claude:
#<ol>#
#<li>#"What is the structural difference between the substitution interpreter
     ([eval], fuel-based) and the environment interpreter ([evalE],
     structurally recursive)?  Why does one need fuel and the other does not?"#</li>#
#<li>#"Which design is easier to reason about in Rocq?  Why?"#</li>#
#<li>#"In a real programming language implementation, which design would you
     choose for an interpreter?  Which for a compiler?"#</li>#
#<li>#"The agreement theorem says both interpreters compute the same answers.
     Does that mean they are equally _correct_ designs?  What is the value of
     having two distinct designs that agree?"#</li>#
#</ol>#

Write your reflection as a comment below, in your own words.
 *)

(*
  STUDENT REFLECTION (replace this comment with your answer after the dialogue):

  [Your reflection here.]
*)
