(** * Programming Languages in Rocq - Rec AI-Assisted Exercises *)

(**
This file contains four AI-assisted exercises for the Rec chapter.
Each exercise pairs a Rocq proof task with a structured dialogue you will hold
with Claude (or another AI assistant).  The goals are:

#<ol>#
#<li>#Extend the generator pattern to a new recursive function and run it
     under both combinators.#</li>#
#<li>#Understand why [If] evaluating only the selected branch is the key
     ingredient that enables productive recursion.#</li>#
#<li>#Understand the structure of the fuel-monotonicity proof by working
     through the [If] case as a standalone step lemma.#</li>#
#<li>#Reflect on fixpoint combinators, the strict/lazy split, and how real
     languages provide recursion without combinators.#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Read the "Ask Claude:" prompts before opening Rocq.  Hold the dialogue first,
then attempt the Rocq tasks.  Each lemma ends in [Admitted]; students who
complete the proof replace [Admitted] with a complete proof.  The file
compiles as given.

Difficulty: ★★ = a few tactic steps, ★★★ = case analysis.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rec_shared.
Require Import plih_rec_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * EXERCISE 1 (★★★): A New Recursive Generator — Powers of Two *)

(**
The lecture builds [sumGen] (summation) and [factGen] (factorial) using the
_generator pattern_: the function takes its own recursive call as a parameter
[g] and branches on [IsZero] to reach the base case.

A third example: the powers-of-two function [pow2 n = 2^n].

[[
  pow2Gen = lambda g in lambda n in
              if iszero n then 1 else 2 * g (n - 1)
]]

[pow2Gen] fits the same template:
#<ol>#
#<li>#the base case is [n = 0], returning [1] (since 2^0 = 1);#</li>#
#<li>#the recursive case halves the exponent and multiplies by [2].#</li>#
#</ol>#
 *)

Definition pow2Gen : FBAEC :=
  Lambda "g"
    (Lambda "n"
      (If (IsZero (Id "n"))
          (Num 1)
          (Mult (Num 2) (App (Id "g") (Minus (Id "n") (Num 1)))))).

(**
Ask Claude:
#<ol>#
#<li>#"Verify that [pow2Gen] matches the description above.  Trace
     [App (App Zc pow2Gen) (Num 3)] step by step under strict evaluation:
     how many recursive calls does it make, and what does each call
     compute?"#</li>#
#<li>#"Prove [ai1_pow2_strict] and [ai1_pow2_lazy].  Both proofs are a
     single tactic."#</li>#
#<li>#"Why does strict Y diverge on [pow2Gen]?  Trace the first two
     reduction steps of [App (App Yc pow2Gen) (Num 3)] under strict
     evaluation to show where the loop begins."#</li>#
#</ol>#

_Reflect:_
#<ol>#
#<li>#[pow2Gen] never mentions itself by name; instead it receives the
   recursive call as [g].  This is called _open recursion_.  Ask Claude:
   what does a generator look like for a function that is _not_ primitive
   recursive, such as the Ackermann function?#</li>#
#<li>#The lecture shows that Z (strict) and Y (lazy) give the same answer,
   but via different evaluation strategies.  Ask Claude: are there
   computations where strict evaluation and lazy evaluation give
   _different answers_ (not just different performance)?  Give an example
   involving [omega].#</li>#
#<li>#Under strict evaluation, [App (App Yc pow2Gen) (Num 3)] diverges.
   But [App (App Zc pow2Gen) (Num 3)] terminates.  The only difference
   is the eta-guard [lambda v in x x v].  Ask Claude to explain in one
   sentence what job the eta-guard does and why it breaks the loop.#</li>#
#</ol>#
 *)

Lemma ai1_pow2_strict :
  eval (App (App Zc pow2Gen) (Num 3)) = Some (NumV 8).
Proof. Admitted.

Lemma ai1_pow2_lazy :
  evalLazy (App (App Yc pow2Gen) (Num 3)) = Some (LNumV 8).
Proof. Admitted.

(** * EXERCISE 2 (★★): [If] Evaluates Only the Selected Branch *)

(**
The Func chapter ended with [omega]: self-application that loops forever.
The missing ingredient was a _conditional_ that evaluates only one branch.
Without it, a recursive call in the "done" case would never be skipped -
recursion could never bottom out.

FBAEC supplies that ingredient with [If c t f]: it evaluates [c] and
then evaluates _only_ [t] or _only_ [f].  The untaken branch is never
reduced.

Ask Claude:
#<ol>#
#<li>#"Prove [ai2a_if_false] and [ai2b_untaken_ignored] using the hints
     provided."#</li>#
#<li>#"In [ai2b_untaken_ignored], the then-branch is evaluated and returns
     [42], while the else-branch [Plus (Boolean false) (Num 1)] is
     discarded.  What would happen if [evalM] were instead _applicative-
     order_ - evaluating both branches before the [if]?  Would [sumGen]
     still terminate?"#</li>#
#<li>#"Why does the strict interpreter [evalM] nevertheless evaluate the
     _condition_ eagerly?  Is there a variant of [If] that thunks the
     condition too, and would it still be useful for recursion?"#</li>#
#</ol>#

_Reflect:_
#<ol>#
#<li>#FBAE had [Minus] (truncated subtraction) and could test indirectly
   whether a number reached zero - but it could not _branch_ on the result.
   Ask Claude: why is branching essential, and why does truncated subtraction
   alone fail to give you a base case?#</li>#
#<li>#Ask Claude: are there languages where [if] is NOT a special form but
   instead an ordinary function?  Why does ordinary-function [if] fail for
   recursive programs unless the language is lazy?#</li>#
#</ol>#
 *)

(**
When the condition is [false], [If] reduces to its else-branch.
This is the symmetric counterpart of [ex8_if_true] in the exercises.
Hint: [intros k env t f; destruct k; simpl; reflexivity].
 *)
Lemma ai2a_if_false : forall k env t f,
  evalM (S k) env (If (Boolean false) t f) = evalM k env f.
Proof. Admitted.

(**
The then-branch [Num 42] is returned; the else-branch [Plus (Boolean false) (Num 1)]
is never reduced, even though it would return [None] if evaluated.
Hint: [intros k env; simpl; reflexivity].
 *)
Lemma ai2b_untaken_ignored : forall k env,
  evalM (S (S k)) env
    (If (Boolean true) (Num 42) (Plus (Boolean false) (Num 1)))
  = Some (NumV 42).
Proof. Admitted.

(** * EXERCISE 3 (★★★): The [If] Case of Fuel Monotonicity *)

(**
The lecture proves [evalM_mono] by induction on the first fuel amount [f1],
with one case per constructor.  This exercise focuses on the [If] case,
stated as a standalone _step lemma_ with the induction hypotheses for [c],
[t], and [f] given explicitly as hypotheses [IHc], [IHt], and [IHf].

Ask Claude:
#<ol>#
#<li>#"Prove [ai3_if_mono_step] using the following strategy:
     - Start with [simpl in H |- *] to unfold both occurrences of
       [evalM (S _) env (If c t f)].
     - Use [destruct (evalM k1 env c) as [[n | b | i bd ce] |] eqn:Ec;
       try discriminate] to case-split the condition's value and discard
       impossible shapes.
     - For the [BoolV b] case, further [destruct b] to separate the
       [true] and [false] branches.
     - In each branch, [rewrite (IHc (BoolV _) Ec)] to replace
       [evalM k1 env c] with [evalM k2 env c] in the goal, then
       apply [IHt] or [IHf] to close the remaining obligation."#</li>#
#<li>#After Claude gives you a proof, check it in Rocq.  If any case is
     wrong, paste the error and ask Claude to fix it.#</li>#
#<li>#"In the full [evalM_mono] proof, the [IHc]/[IHt]/[IHf] hypotheses
     come from the outer induction on [f1].  Explain in one sentence how
     [ai3_if_mono_step] would fit into that outer induction."#</li>#
#</ol>#

_Reflect:_
#<ol>#
#<li>#The [If] case is structurally richer than [Plus] or [Minus] because
   only _one_ of [t] and [f] is ever evaluated, depending on [c]'s value.
   Ask Claude: how does the [App] case differ from [If] in the
   monotonicity proof?  Which IH does it use and when?#</li>#
#<li>#[evalM_mono] is the well-definedness result that replaces "size is
   enough fuel" from earlier chapters.  Ask Claude: could you prove a
   stronger result - say, that [evalM f env e] is _non-decreasing_ in
   [f] in some ordered sense?  What ordering on [option RVal] would
   you need?#</li>#
#</ol>#
 *)

Lemma ai3_if_mono_step : forall k1 k2 env c t f v,
  k1 <= k2 ->
  (forall u, evalM k1 env c = Some u -> evalM k2 env c = Some u) ->
  (forall u, evalM k1 env t = Some u -> evalM k2 env t = Some u) ->
  (forall u, evalM k1 env f = Some u -> evalM k2 env f = Some u) ->
  evalM (S k1) env (If c t f) = Some v ->
  evalM (S k2) env (If c t f) = Some v.
Proof. Admitted.

(** * EXERCISE 4 (Written): Fixpoint Combinators and Real Languages *)

(**
This exercise has no Rocq proof task.  Hold a dialogue with Claude and write
a short reflection covering all four questions.

Ask Claude:
#<ol>#
#<li>#"Trace why the plain Y combinator diverges under strict evaluation but
     works under lazy evaluation.  Show the first two or three reduction
     steps of [Y sumGen 5] under strict [evalM] and explain where the loop
     forms before [sumGen]'s base case can fire."#</li>#
#<li>#"Name two mainstream languages that provide _named_ recursion (e.g.
     [letrec], [def], or [fun rec]) without requiring the programmer to
     write a fixpoint combinator.  What does the language runtime guarantee
     that makes the combinator unnecessary?"#</li>#
#<li>#"The generator pattern (passing the recursive call as [g]) is
     sometimes called _open recursion_.  Ask Claude: what is the connection
     between open recursion and the design pattern called _dependency
     injection_?  Is [g] a form of dependency injection?"#</li>#
#<li>#"The lecture proves [evalM_mono] for the strict interpreter but not
     for [evalL].  Is [evalL] also monotone in fuel?  If so, sketch how
     the proof would differ from [evalM_mono], pointing to any cases that
     are genuinely different."#</li>#
#</ol>#

Write your reflection as a comment below in your own words.  You do not need
to reproduce Claude's answers verbatim; synthesise them into an explanation
you could give to a classmate.
 *)

(*
  STUDENT REFLECTION (replace this comment with your answer after the dialogue):

  (1) Why Y diverges under strict evaluation:

  (2) Languages with built-in named recursion:

  (3) Open recursion and dependency injection:

  (4) Is evalL monotone in fuel, and how would the proof differ?
*)
