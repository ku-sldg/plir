(**
Programming Languages in Rocq - ABE AI-Assisted Exercises
Arithmetic + Boolean Expressions - AI Collaboration Problem Set

In these exercises you will:
#<ol>#
#<li>#Ask an AI assistant to extend [ABE] and write proofs#</li>#
#<li>#_Read and verify_ every definition and proof step before accepting it#</li>#
#<li>#Understand when a naively plausible lemma is actually false#</li>#
#<li>#Reason about why [eval] returns [option Value] rather than [Value]#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise has an "Ask Claude:" prompt and a "Reflect:" section.
Scaffold definitions are PROVIDED so the file compiles as given.
Student proof obligations end in [Admitted].

Difficulty: ★ trivial, ★★ easy, ★★★ requires careful case analysis.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Export plih_rocq_abe_shared.
Require Import plih_abe_lecture.

(** * Exercise 1 (★★★): Extending ABE with Exclusive-Or

_Ask Claude:_
"I have [ABE], an arithmetic-and-boolean expression language.  Please
add an [Xor] constructor to produce a new type [ABE_X], write an
[evalX] interpreter for it that uses [xorb] for the new case, and
define an inductive predicate [is_boolean_x] (analogous to
[is_boolean]) that includes a rule for [Xor]."

Inspect every case of [evalX] below and confirm that [Xor] delegates
to [xorb] from [Stdlib.Bool].  Then read the [is_boolean_x] definition
and verify that the rule for [Xor] has the right premises.

_Reflect:_
#<ol>#
#<li>#What rule did you add to [is_boolean_x] for [Xor]?  Why are two
   boolean premises needed?#</li>#
#<li>#[is_boolean] in the lecture has no rule for [IfThenElse].  Ask
   Claude why.  What preconditions would an [IfThenElse] rule need?#</li>#
#<li>#The proof of [ai_xor_never_fails] should follow the same pattern
   as [boolean_never_fails] in the lecture.  Ask Claude to explain the
   key [induction] step for the [Xor] case.#</li>#
#</ol>#
 *)

(** Extended expression type with an exclusive-or constructor. *)
Inductive ABE_X : Type :=
| XNum        : nat  -> ABE_X
| XPlus       : ABE_X -> ABE_X -> ABE_X
| XMinus      : ABE_X -> ABE_X -> ABE_X
| XBTrue      : ABE_X
| XBFalse     : ABE_X
| XAnd        : ABE_X -> ABE_X -> ABE_X
| XOr         : ABE_X -> ABE_X -> ABE_X
| XNot        : ABE_X -> ABE_X
| XLessThan   : ABE_X -> ABE_X -> ABE_X
| XEqual      : ABE_X -> ABE_X -> ABE_X
| XIfThenElse : ABE_X -> ABE_X -> ABE_X -> ABE_X
| Xor         : ABE_X -> ABE_X -> ABE_X.

(** Interpreter for [ABE_X].  The [Xor] case uses [xorb] from [Bool]. *)
Fixpoint evalX (e : ABE_X) : option Value :=
  match e with
  | XNum n      => Some (NumV n)
  | XBTrue      => Some (BoolV true)
  | XBFalse     => Some (BoolV false)
  | XPlus  a b  =>
      match evalX a, evalX b with
      | Some (NumV n1), Some (NumV n2) => Some (NumV (n1 + n2))
      | _, _ => None
      end
  | XMinus a b  =>
      match evalX a, evalX b with
      | Some (NumV n1), Some (NumV n2) => Some (NumV (n1 - n2))
      | _, _ => None
      end
  | XAnd a b    =>
      match evalX a, evalX b with
      | Some (BoolV b1), Some (BoolV b2) => Some (BoolV (b1 && b2))
      | _, _ => None
      end
  | XOr  a b    =>
      match evalX a, evalX b with
      | Some (BoolV b1), Some (BoolV b2) => Some (BoolV (b1 || b2))
      | _, _ => None
      end
  | XNot a      =>
      match evalX a with
      | Some (BoolV b) => Some (BoolV (negb b))
      | _ => None
      end
  | XLessThan a b =>
      match evalX a, evalX b with
      | Some (NumV n1), Some (NumV n2) => Some (BoolV (Nat.ltb n1 n2))
      | _, _ => None
      end
  | XEqual a b  =>
      match evalX a, evalX b with
      | Some (NumV n1), Some (NumV n2) => Some (BoolV (Nat.eqb n1 n2))
      | _, _ => None
      end
  | XIfThenElse c t f =>
      match evalX c with
      | Some (BoolV true)  => evalX t
      | Some (BoolV false) => evalX f
      | _ => None
      end
  | Xor a b     =>
      match evalX a, evalX b with
      | Some (BoolV b1), Some (BoolV b2) => Some (BoolV (xorb b1 b2))
      | _, _ => None
      end
  end.

(** Inductive type-consistency predicate for [ABE_X].
    Mirrors [is_boolean] from the lecture, with an additional rule for
    [Xor].  The definition below is the answer Claude should produce;
    verify that each constructor has the correct premises. *)
Inductive is_boolean_x : ABE_X -> Prop :=
| xbool_true    : is_boolean_x XBTrue
| xbool_false   : is_boolean_x XBFalse
| xbool_and     : forall a b, is_boolean_x a -> is_boolean_x b ->
                               is_boolean_x (XAnd a b)
| xbool_or      : forall a b, is_boolean_x a -> is_boolean_x b ->
                               is_boolean_x (XOr a b)
| xbool_not     : forall a,   is_boolean_x a ->
                               is_boolean_x (XNot a)
| xbool_lt      : forall a b, (forall v, evalX a = Some v -> exists n, v = NumV n) ->
                               (forall v, evalX b = Some v -> exists n, v = NumV n) ->
                               is_boolean_x (XLessThan a b)
| xbool_eq      : forall a b, (forall v, evalX a = Some v -> exists n, v = NumV n) ->
                               (forall v, evalX b = Some v -> exists n, v = NumV n) ->
                               is_boolean_x (XEqual a b)
| xor_bool      : forall a b, is_boolean_x a -> is_boolean_x b ->
                               is_boolean_x (Xor a b).

(** A boolean-typed extended expression always evaluates to a [BoolV].
    The proof follows the same induction-on-derivation pattern as
    [boolean_never_fails] in the lecture.

    Ask Claude to supply the proof, then check every case — especially
    [xor_bool] — step by step. *)
Lemma ai_xor_never_fails : forall e,
  is_boolean_x e -> exists b, evalX e = Some (BoolV b).
Proof. Admitted.

(** * Exercise 2 (★★): Double Negation Needs a Hypothesis

_Ask Claude_ (without giving any hints):
"Prove [forall e, abe_equiv (Not (Not e)) e]."

Claude should either produce a proof attempt that fails, or
immediately point out that the claim is false.  If it produces a
broken proof, ask it to explain why the proof does not go through.

The lemma is FALSE for non-boolean expressions: [Not (Not (Num 5))]
evaluates to [None] (because [Not] expects a boolean, but [Num 5]
gives a [NumV 5]), while [Num 5] evaluates to [Some (NumV 5)].

_Reflect:_
#<ol>#
#<li>#What happened when you asked Claude to prove the unconditional
   version?  Did it flag the error immediately or try a failing proof?#</li>#
#<li>#What hypothesis did you need to add to make the lemma true?  Why
   does knowing [eval e = Some (BoolV b)] fix the problem?#</li>#
#</ol>#
 *)

(** Counterexample: [Not (Not (Num 5))] and [Num 5] are _not_ equivalent
    because the former is [None] and the latter is [Some (NumV 5)]. *)
Example ai2_double_neg_counterexample :
  ~ abe_equiv (Not (Not (Num 5))) (Num 5).
Proof. Admitted.

(** Correct version: double negation is sound _when_ [e] is boolean.
    Hint: unfold [abe_equiv], then [cbn], then rewrite using [H]. *)
Lemma ai2_double_neg : forall e b,
  eval e = Some (BoolV b) ->
  abe_equiv (Not (Not e)) e.
Proof. Admitted.

(** * Exercise 3 (★★★): De Morgan's Law for Disjunction

The lecture proves [de_morgan], which says:
<<
  Not (And e1 e2)  ≡  Or (Not e1) (Not e2)
>>

The _dual_ law for disjunction is:
<<
  Not (Or e1 e2)  ≡  And (Not e1) (Not e2)
>>

_Ask Claude_ for the proof strategy.  It should tell you to:
#<ol>#
#<li>#Unfold [abe_equiv]#</li>#
#<li>#Simplify with [cbn]#</li>#
#<li>#Destruct [eval e1] and [eval e2] into all [Value] shapes#</li>#
#<li>#Finish each boolean sub-case with [destruct b1; destruct b2; reflexivity]#</li>#
#</ol>#

Verify that the strategy Claude gives matches [de_morgan]'s proof in
the lecture before filling in the [Admitted].

_Reflect:_
#<ol>#
#<li>#How similar is the proof to [de_morgan]?  Could both laws be
   captured by a single more general lemma?  What would its statement
   look like?#</li>#
#<li>#De Morgan's laws hold in our [eval] even though [eval] is partial.
   Why?  (Hint: think about what happens when [eval e1 = None].)#</li>#
#</ol>#
 *)

Lemma ai3_de_morgan_or : forall e1 e2,
  abe_equiv (Not (Or e1 e2)) (And (Not e1) (Not e2)).
Proof. Admitted.

(** * Exercise 4 (★★): A More Complex Ill-Typed Expression

[IfThenElse (Num 1) BTrue BFalse] is ill-typed: its condition [Num 1]
is numeric, but [IfThenElse] requires a boolean condition.  The
expression is therefore _neither_ [is_numeric] nor [is_boolean].

_Ask Claude_ to explain:
#<ol>#
#<li>#Why is [IfThenElse] excluded from both [is_numeric] and
   [is_boolean] in the lecture?#</li>#
#<li>#Would it make sense to add a rule for [IfThenElse] to
   [is_boolean]?  What preconditions would that rule need?#</li>#
#</ol>#

Then complete the two lemmas below.  Both proofs should be a single
[unfold ai4_bad_if; intros H; inversion H] call — ask Claude to
explain why [inversion H] closes the goal immediately.

_Reflect:_
What does [inversion H] do when [H : is_numeric (IfThenElse ...)]?
Why does no rule in [is_numeric] match?
 *)

Example ai4_bad_if : ABE := IfThenElse (Num 1) BTrue BFalse.

Lemma ai4_bad_if_not_numeric : ~ is_numeric ai4_bad_if.
Proof. Admitted.

Lemma ai4_bad_if_not_boolean : ~ is_boolean ai4_bad_if.
Proof. Admitted.
