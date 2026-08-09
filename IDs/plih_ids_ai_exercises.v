(** * Programming Languages in Rocq - IDs AI-Assisted Exercises *)

(**
This file contains four AI-assisted exercises for the IDs chapter.
Each exercise pairs a Rocq proof task with a structured dialogue you will hold
with Claude (or another AI assistant).  The goals are:

#<ol>#
#<li>#Understand how [free_in] and a counting variant relate to each other.#</li>#
#<li>#Understand why substitution of a non-free variable does not change evaluation.#</li>#
#<li>#Understand alpha-renaming as a derived form built on [subst].#</li>#
#<li>#Understand (through dialogue) why the substitution interpreter needs fuel.#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Read the "Ask Claude:" prompts before opening Rocq.  Hold the dialogue first,
then attempt the Rocq tasks.  Each lemma ends in [Admitted]; students who
complete the proof replace [Admitted] with a complete proof.  The file
compiles as given.

Difficulty: ★★ = one or two lemma citations, ★★★ = induction or case analysis.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_ids_shared.
Require Import plih_ids_lecture.

Local Open Scope string_scope.

(** * EXERCISE 1 (★★★): Counting free occurrences *)

(**
The lecture's [free_in x e] is a yes/no test.  This exercise introduces
[count_free x e], which counts _how many_ free occurrences of [x] appear in
[e].  The two functions carry the same information, and this exercise asks you
to prove that they agree.

The definition is provided for you.  Read it carefully and compare it with the
[free_in] definition in the lecture before asking Claude anything.
*)

Fixpoint count_free (x : string) (e : BAE) : nat :=
  match e with
  | Num _      => 0
  | Id y       => if String.eqb x y then 1 else 0
  | Plus  l r  => count_free x l + count_free x r
  | Minus l r  => count_free x l + count_free x r
  | Bind y v b =>
      count_free x v +
      (if String.eqb x y then 0 else count_free x b)
  end.

(**
Ask Claude:
#<ol>#
#<li>#"Please prove [ai1a_count_zero_not_free] and [ai1b_not_free_count_zero]
     by induction on [e].  Use only tactics from the IDs lecture: [induction],
     [simpl], [destruct], [apply], [rewrite], [reflexivity], [assumption],
     [lia].  Do not use [omega] or [tauto]."#</li>#
#<li>#After Claude gives you a proof, check it in Rocq.  If the proof is
     wrong, paste the error message back to Claude and ask it to fix the
     proof.#</li>#
#<li>#"Why is the [Bind] case the hardest?  Walk me through exactly which
     sub-goals arise and how they are closed."#</li>#
#</ol>#

Verify that Claude uses [induction e] (not [induction x]) for both lemmas.
In the [Plus] and [Minus] cases the key library lemmas are
[orb_false_iff] (for [ai1a]) and [Nat.add_eq_0_iff] (for [ai1a]).
In the [Bind] case the [String.eqb x y] branch must be handled separately.

Reflect: [count_free] and [free_in] carry the same information - they agree
on whether a variable occurs free.  What does each representation offer that
the other does not?  When would you prefer [count_free] over [free_in] in a
program analysis or an optimisation pass?
 *)

(* If [x] has no free occurrences, [free_in] reports false. *)
Lemma ai1a_count_zero_not_free : forall e x,
  count_free x e = 0 -> free_in x e = false.
Proof. Admitted.

(* If [free_in] reports false, [x] has no free occurrences. *)
Lemma ai1b_not_free_count_zero : forall e x,
  free_in x e = false -> count_free x e = 0.
Proof. Admitted.

(** * EXERCISE 2 (★★): Substitution of a non-free variable does not change evaluation *)

(**
If [x] is not free in [e], then substituting any term [v] for [x] does
nothing to [e], and therefore evaluation is unaffected.

Ask Claude:
#<ol>#
#<li>#"Please prove [ai2_eval_subst_not_free] without any hints."#</li>#
#<li>#After you have Claude's proof, ask: "Is this result _obvious_ from the
     definition of [eval]?  Why does it require [subst_not_free] as a separate
     lemma rather than following directly from unfolding [eval]?"#</li>#
#</ol>#

Hint for checking the proof: the key step is [rewrite subst_not_free by exact H],
which collapses [subst x v e] to [e] and makes both sides identical.

Reflect: What would change if [x] _does_ appear free in [e]?  Would the
lemma still hold?  Give a concrete counterexample using [BAE] terms, for
instance with [e = Id "x"] and [v = Num 99].
 *)

Lemma ai2_eval_subst_not_free : forall e x v,
  free_in x e = false ->
  eval e = eval (subst x v e).
Proof. Admitted.

(** * EXERCISE 3 (★★★): Renaming a bound variable *)

(**
_Alpha-renaming_ replaces every free occurrence of identifier [x] in an
expression with identifier [y].  Built on [subst], it is a single definition:
*)

(* [rename x y e]: replace every free occurrence of [Id x] with [Id y]. *)
Definition rename (x y : string) (e : BAE) : BAE :=
  subst x (Id y) e.

(**
Ask Claude:
#<ol>#
#<li>#"Please prove [ai3a_rename_same] and [ai3b_rename_size] by induction on
     [e].  In [ai3a], handle the [Id] case with
     [destruct (String.eqb x y) eqn:E] and use [String.eqb_eq] to convert
     the boolean equation to an equality.  In the [Bind] case, consider what
     happens when the binder variable equals [x] (the shadow case)."#</li>#
#<li>#After Claude produces a proof, ask: "In the shadow case of the [Bind]
     case for [ai3a], why is the body left unchanged?  Is that the correct
     behaviour?"#</li>#
#</ol>#

Verify that Claude's proof of [ai3a] correctly handles the [Bind] shadow
case: when the binder variable equals [x], the body must _not_ be renamed
(the binder introduces a new [x] that shadows the outer [x]).

Reflect: [rename x y e] replaces free [x]s with [Id y].  This is called
_alpha-renaming_.  Ask Claude: when is alpha-renaming _safe_?  What property
must [y] satisfy relative to [e] so that

[[
  Bind x v e   and   Bind y v (rename x y e)
]]

are semantically equivalent?  (Hint: think about whether [y] might already
occur free in [e].)
 *)

(* Renaming to the same name is the identity. *)
Lemma ai3a_rename_same : forall x e,
  rename x x e = e.
Proof. Admitted.

(* Renaming preserves the size of an expression. *)
Lemma ai3b_rename_size : forall x y e,
  size (rename x y e) = size e.
Proof. Admitted.

(** * EXERCISE 4 (Written): Why does the substitution interpreter need fuel? *)

(**
This exercise has no Rocq proof task.  Hold a dialogue with Claude and write a
short reflection (a paragraph or two, in comments below) covering all four
questions.

Ask Claude:
#<ol>#
#<li>#"Explain in plain English why a simple
     [Fixpoint eval (e : BAE) : option nat] fails Rocq's termination checker
     for the [Bind] case."#</li>#
#<li>#"Show me what the rejected definition would look like - just the
     definition, not a proof that it is rejected."#</li>#
#<li>#"Explain why [evalF] with a fuel parameter solves the problem."#</li>#
#<li>#"Would the fuel approach still work if [subst] could _increase_ the
     size of a term?  Why or why not?"#</li>#
#</ol>#

Write your reflection as a comment below, in your own words.  You do not need
to reproduce Claude's answers verbatim; synthesise them into a short explanation
that you could give to a classmate.
 *)

(*
  STUDENT REFLECTION (replace this comment with your answer after the dialogue):

  [Your reflection here.]
*)
