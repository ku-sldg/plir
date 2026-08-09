(** * Programming Languages in Rocq - Func AI-Assisted Exercises *)

(**
This file contains four AI-assisted exercises for the Func chapter.
Each exercise pairs a Rocq proof task with a structured dialogue you will
hold with Claude (or another AI assistant).  The goals are:

#<ol>#
#<li>#Understand static vs dynamic scoping by constructing and analyzing a
     new witness term.#</li>#
#<li>#Understand elaboration (desugaring [Bind] into [App]/[Lambda]) through
     an idempotence property.#</li>#
#<li>#Understand [Lambda] as a variable binder by proving [free_in] properties
     for the new FBAE constructors.#</li>#
#<li>#Reflect on the design choices made in this chapter and their practical
     consequences.#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Read the "Ask Claude:" prompts before opening Rocq.  Hold the dialogue first,
then attempt the Rocq tasks.  Each lemma ends in [Admitted]; students who
complete the proof replace [Admitted] with a complete proof.  The file
compiles as given.

Difficulty: ★★ = a few tactic steps, ★★★ = case analysis or induction.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_func_shared.
Require Import plih_func_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * EXERCISE 1 (★★★): A New Scoping Witness *)

(**
The lecture's [scopeTest] binds [n] twice and shows that the static
interpreter ([evalM]) returns 4 while the dynamic interpreter ([evalDyn])
returns 5.

[[
  bind n = 1 in
  bind f = lambda x in x + n in
  bind n = 2 in
    f 3
]]

Here is a _different_ witness, [scope2], built on [Minus] and a different
numeric structure:

[[
  bind y = 10 in
  bind f  = lambda x in x - y in
  bind y = 3  in
    f 100
]]
 *)

Definition scope2 : FBAE :=
  Bind "y" (Num 10)
    (Bind "f" (Lambda "x" (Minus (Id "x") (Id "y")))
      (Bind "y" (Num 3)
        (App (Id "f") (Num 100)))).

(**
Ask Claude:
#<ol>#
#<li>#"Trace [scope2] step by step under _static_ scoping ([evalM]).
     Which value of [y] does the closure for [f] capture when it is
     defined?  What does [f 100] compute?"#</li>#
#<li>#"Trace [scope2] step by step under _dynamic_ scoping ([evalDyn]).
     Which value of [y] is in scope at the _call site_ [f 100]?  What
     does [f 100] compute?"#</li>#
#<li>#"Prove [ai1_scope2_static] and [ai1_scope2_dynamic].  Both proofs
     are a single tactic."#</li>#
#</ol>#

Verify Claude's predictions before proving them.  If Claude gives the wrong
answer for either interpreter, ask it to trace the evaluation rule for [App]
step by step, paying attention to _which_ environment the closure body runs
in.

_Reflect:_
#<ol>#
#<li>#Under static scoping, the closure for [f] is formed when [f] is
   _defined_ (inside [bind y = 10]).  Under dynamic scoping, [f 100]
   runs inside [bind y = 3].  Explain in your own words which binding
   each interpreter uses and why.#</li>#
#<li>#Python and JavaScript both use static scoping for functions.  Ask
   Claude: is there a mainstream language that uses dynamic scoping by
   default?  In what kinds of programs is dynamic scoping actually useful?#</li>#
#<li>#Nat.sub in Rocq truncates at zero.  Do the answers 90 and 97 avoid
   that corner case for [scope2]?  What would happen if you wrote
   [Minus (Id "y") (Id "x")] instead of [Minus (Id "x") (Id "y")]?#</li>#
#</ol>#
 *)

Lemma ai1_scope2_static : eval scope2 = Some (NumV 90).
Proof. Admitted.

Lemma ai1_scope2_dynamic : evalDyn 100 nil scope2 = Some (DNumV 97).
Proof. Admitted.

(** * EXERCISE 2 (★★★): Elaboration Idempotence *)

(**
The lecture proves two key facts about [elab]:
#<ol>#
#<li>#[elab_bindFree]: elaboration always produces a [Bind]-free term.#</li>#
#<li>#[elab_preserves]: elaboration preserves meaning up to lifting [elab]
   into values.#</li>#
#</ol>#

This exercise asks you to prove a _third_ property: [elab] is _idempotent_
on terms that are already [Bind]-free.  Together with [elab_bindFree] this
will imply [elab (elab e) = elab e] for _all_ [e].

Ask Claude:
#<ol>#
#<li>#"Prove [ai2_elab_idem] by induction on [e] using the following hints:
     - [Num] and [Id] cases: [simpl; reflexivity].
     - [Bind] case: [bindFree (Bind _ _ _) = false], so the hypothesis is
       false.  Close it with [simpl in H; discriminate].
     - [Plus], [Minus], [App] cases: split the conjunction in the hypothesis
       with [apply andb_prop in H; destruct H as [Hl Hr]], apply the
       induction hypotheses, then finish with [simpl; congruence].
     - [Lambda] case: [bindFree (Lambda i b) = bindFree b], so the hypothesis
       reduces directly; apply the IH and finish with [simpl; congruence].
     Do not use [tauto] or [auto].  Name your induction with
     [induction e as [n | l IHl r IHr | l IHl r IHr | i v IHv b IHb |
                       i b IHb | f IHf a IHa | x]]."#</li>#
#<li>#After Claude gives you a proof, check it in Rocq.  If any case is
     wrong, paste the error message back and ask Claude to fix it.#</li>#
#<li>#"Explain why [ai2_elab_idem] and [elab_bindFree] together imply that
     [elab (elab e) = elab e] for ALL [e], not just [Bind]-free ones.
     Walk me through the argument."#</li>#
#</ol>#

_Reflect:_
#<ol>#
#<li>#A function [f] is a _retraction_ when [f (f x) = f x] for all [x].
   [elab] is a retraction on FBAE terms.  Ask Claude: what other compiler
   passes have this property, and why is idempotence useful when composing
   compiler transformations?#</li>#
#<li>#[elab_preserves] finds, for each source fuel [f], an elaborated fuel
   [f'] that works — but it cannot promise [f' = f] because each [Bind]
   becomes an extra [App]/[Lambda] layer.  Ask Claude: could there be a
   variant of [elab] that never increases fuel use?  What would it have
   to do differently?#</li>#
#</ol>#
 *)

Lemma ai2_elab_idem : forall e,
  bindFree e = true ->
  elab e = e.
Proof. Admitted.

(** * EXERCISE 3 (★★): [Lambda] as a Variable Binder *)

(**
FBAE has two binders: [Bind i v b] (from earlier chapters) and [Lambda i b]
(new here).  Both prevent [free_in] from descending into [b] when the outer
variable name matches [i]:

[[
  free_in x (Bind  i _ b) = ... || if x = i then false else free_in x b
  free_in x (Lambda i   b) =        if x = i then false else free_in x b
]]

Three lemmas make this precise.

Ask Claude:
#<ol>#
#<li>#"Prove [ai3a_lambda_binds_itself], [ai3b_lambda_other], and
     [ai3c_free_app] using only [simpl], [rewrite], [reflexivity], and the
     lemma [string_eqb_refl].  For [ai3b], the hypothesis is
     [H : String.eqb x i = false]."#</li>#
#<li>#After Claude gives the proofs, ask: "Why must [Lambda] stop the
     [free_in] scan when the parameter name matches?  What would go wrong
     during substitution or evaluation if [Lambda] did not bind its
     parameter?"#</li>#
#<li>#"Compare the [Bind] and [Lambda] cases in [free_in].  The [Bind] case
     scans the bound expression [v] even when [x = i], but [Lambda] has no
     such component.  What does this tell us about the difference between
     [let x = v in b] and [lambda x in b] as binding constructs?"#</li>#
#</ol>#

_Reflect:_
#<ol>#
#<li>#[Lambda i b] binds [i] in [b] with no counterpart to the [v] in
   [Bind i v b].  Ask Claude: what language term corresponds to the
   "value" of a lambda parameter, and when does that value become known
   relative to the definition of the lambda?#</li>#
#<li>#The elaboration [Bind i v b ~> App (Lambda i b) v] moves [v] from
   inside the binder to the argument position of an [App].  Ask Claude
   how this shift is reflected in [free_in]: does elaboration change
   which variables appear free?#</li>#
#</ol>#
 *)

(**
[Lambda i b] is a binder: [i] is not free in [Lambda i b].
Hint: [simpl; rewrite string_eqb_refl; reflexivity].
 *)
Lemma ai3a_lambda_binds_itself : forall i b,
  free_in i (Lambda i b) = false.
Proof. Admitted.

(**
When [x] is not the lambda parameter, [free_in] passes through to the body.
Hint: [simpl; rewrite H; reflexivity], where [H : String.eqb x i = false].
 *)
Lemma ai3b_lambda_other : forall x i b,
  String.eqb x i = false ->
  free_in x (Lambda i b) = free_in x b.
Proof. Admitted.

(**
[App] is not a binder: both sub-expressions contribute free variables.
Hint: [reflexivity].
 *)
Lemma ai3c_free_app : forall x f a,
  free_in x (App f a) = free_in x f || free_in x a.
Proof. Admitted.

(** * EXERCISE 4 (Written): Language Design Dialogue *)

(**
This exercise has no Rocq proof task.  Hold a dialogue with Claude and write a
short reflection covering all four questions.

Ask Claude:
#<ol>#
#<li>#"FBAE has both a substitution interpreter [evalS] and a closure-based
     environment interpreter [evalM], and the lecture proves they agree on
     first-order programs.  Which design would you choose for a real language
     implementation, and why?  What does each make easier or harder to reason
     about formally?"#</li>#
#<li>#"The [elab] function desugars [Bind] into [App]/[Lambda], and
     [elab_preserves] certifies this is correct.  This means [Bind] is not
     truly primitive.  Can you name a real programming language specification
     that defines [let x = v in b] as syntactic sugar for [(fun x -> b) v],
     or where the semantics says something equivalent?"#</li>#
#<li>#"FBAE's [evalM] is strict: it evaluates the argument before passing it
     to the function.  [evalL] is lazy: arguments become thunks forced on
     demand.  Name one mainstream language that uses lazy evaluation by
     default and describe one practical advantage this gives that strict
     evaluation cannot provide."#</li>#
#<li>#"The [omega] term diverges under both [evalM] and [evalL].  Yet in
     [evalL], binding [omega] to [z] and never using [z] terminates.  Does
     lazy evaluation _avoid_ divergence or merely _defer_ it?  Give an
     example of a term that terminates under lazy evaluation but diverges
     under strict evaluation, and explain why."#</li>#
#</ol>#

Write your reflection as a comment below in your own words.  You do not need
to reproduce Claude's answers verbatim; synthesise them into an explanation
you could give to a classmate.
 *)

(*
  STUDENT REFLECTION (replace this comment with your answer after the dialogue):

  (1) Substitution interpreter vs closure interpreter — design tradeoffs:

  (2) [Bind] as syntactic sugar in a real language:

  (3) Lazy evaluation in a real language — one practical advantage:

  (4) Lazy evaluation and divergence — avoidance vs deferral:
*)
