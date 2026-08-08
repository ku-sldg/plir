(** * Programming Languages in Rocq - Adding Identifiers *)

(**
This lecture covers:
#<ol>#
#<li>#Extending AE with identifiers (Id) and local bindings (Bind)#</li>#
#<li>#Substitution as the meaning of a binding#</li>#
#<li>#Free and bound identifiers; closed terms#</li>#
#<li>#Writing a SUBSTITUTION-BASED interpreter in Rocq - and the
surprise that it is NOT structurally recursive, so we drive it
with a fuel argument#</li>#
#<li>#Proving properties about substitution and evaluation#</li>#
#</ol>#

This mirrors the "Adding Identifiers" section of PLIH:
  https://ku-sldg.github.io/plih//ids/1-Adding-IDs.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_ids_shared.

Local Open Scope string_scope.

(** * SECTION 1: SYNTAX - The BAE Language *)

(**
BAE ("Bind and Arithmetic Expressions") is AE plus two new forms:

  - [Id x]       : a use (an _instance_) of an identifier;
  - [Bind x v b] : bind [x] to the value of [v], then evaluate the body [b].

Its concrete syntax implemented by the parser at the end of this file is

  t ::= NUM | ID | t + t | t - t | bind ID = t in t
 
The inductive type representing the BAE abstract syntax is defined in the
canonical fashion by adding constructors for [Bind] and [Id].  Note the argument
to [Id] is the name of the identifier being defined.
 *)

Inductive BAE : Type :=
| Num   : nat -> BAE
| Plus  : BAE -> BAE -> BAE
| Minus : BAE -> BAE -> BAE
| Bind  : string -> BAE -> BAE -> BAE
| Id    : string -> BAE.

(**
Binding terminology (from the chapter):
  - Instance:          any occurrence of an identifier.
  - Binding instance:  where an identifier is declared and given a
                       value - the [x] in [Bind x v b].
  - Scope:             the region where an identifier can be used -
                       the body [b] of [Bind x v b].
  - Bound instance:    a use of [x] inside the scope of its binding.
  - Free instance:     a use of [x] with no enclosing binding.

Example:

[[
<{ bind x = 5 + 2 in
     x + x - 4 }>
]]
introduces [x] with value [7], usable only in the scope of the [bind], [x + x -
4].  Some examples using abstract syntax notations:
*)

Definition bae_example_1 : BAE :=
  Bind "x" (Plus (Num 5) (Num 2)) (Minus (Plus (Id "x") (Id "x")) (Num 4)).

Definition bae_example_2 : BAE :=
  Bind "x" (Num 4) (Bind "y" (Num 5) (Minus (Plus (Id "x") (Id "y")) (Num 4))).

(* [Id "x"] on its own is a _free_ instance - it has no binding. *)
Definition bae_free : BAE := Plus (Id "x") (Num 1).

(** * SECTION 2: FREE IDENTIFIERS AND CLOSED TERMS *)

(**
An identifier occurrence is _free_ when it has no enclosing [Bind] that
provides its value.  Free identifiers are the source of evaluation
failure: [eval (Id x)] always returns [None] because there is no value to
look up (see [eval_Id]).  Identifying which identifiers are free - and
which are _bound_ by an enclosing [Bind] - is therefore the semantic
heart of this chapter.

[free_in x e] decides whether [x] has a free occurrence in [e] by
structural recursion, with one case per constructor:

  - [Num _]: a number literal contains no identifiers, so [x] is never
    free in it.
  - [Id y]: a bare identifier is exactly one potential free occurrence.
    [x] is free here iff [x = y].
  - [Plus l r], [Minus l r]: [x] is free iff it is free in [l] _or_ [r];
    both subexpressions are in the same scope.
  - [Bind y v b]: the crucial case.  The bound expression [v] is evaluated
    _before_ [y] is introduced, so it lives in the outer scope - [x] may
    be free in [v] regardless of what [y] is.  The body [b] is evaluated
    _after_ [y] is bound.  If [x = y] then the new binding _shadows_ any
    outer [x]: no occurrence of [x] inside [b] can escape to the outside.
    Only when [x ≠ y] do we recurse into [b].

The shadowing logic is the one non-obvious line:
<<
  Bind y v b => free_in x v || (if String.eqb x y then false else free_in x b)
>>
The left side of [||] always checks [v]; the right side is forced to
[false] when [x = y] and checks [b] only when [x ≠ y].
 *)

Fixpoint free_in (x : string) (e : BAE) : bool :=
  match e with
  | Num _      => false
  | Id y       => String.eqb x y
  | Plus  l r  => free_in x l || free_in x r
  | Minus l r  => free_in x l || free_in x r
  | Bind y v b => free_in x v || (if String.eqb x y then false else free_in x b)
  end.

(**
A term is _closed_ when _no_ identifier occurs free in it: every [Id]
leaf is covered by an enclosing [Bind].
*)
Definition closed (e : BAE) : Prop := forall x, free_in x e = false.

(**
Closed terms are the natural input domain for a complete interpreter.
[eval] can return [None] for two reasons: a free identifier or an
arithmetic failure.  A closed term eliminates the first cause entirely -
if evaluation fails on a closed term, the failure is purely arithmetic.
The examples from Section 1 are all closed (every [Id] is inside its
[Bind]'s scope), which is why they evaluate successfully.

The examples below show the key cases.  [bae_free] is [Plus (Id "x") (Num 1)]:
[x] is free because there is no [Bind "x" ...] wrapping it.
[bae_example_1] binds [x] at the top level, so [x] is not free anywhere in it.
 *)

Example free_in_example : free_in "x" bae_free = true.
Proof. reflexivity. Qed.

Example bound_not_free : free_in "x" bae_example_1 = false.
Proof. reflexivity. Qed.

(**
Two more cases worth seeing explicitly.

In [Bind "x" (Id "x") (Num 0)], the bound expression [Id "x"] is
evaluated in the _outer_ scope - the one where [x] is not yet defined.
So [x] is still free here, even though [x] is the variable being bound.
 *)

Example free_in_bind_value :
  free_in "x" (Bind "x" (Id "x") (Num 0)) = true.
Proof. reflexivity. Qed.

(**
In [Bind "x" (Num 1) (Bind "x" (Num 2) (Id "x"))], the inner [Bind "x"]
shadows the outer one inside its own body.  The only [Id "x"] is inside
the inner scope, so [x] is not free in the whole expression.
 *)

Example shadowing_not_free :
  free_in "x" (Bind "x" (Num 1) (Bind "x" (Num 2) (Id "x"))) = false.
Proof. reflexivity. Qed.

(** * SECTION 3: SUBSTITUTION *)

(**
Substitution is the _semantic action_ of a binding.  When the interpreter
reaches [Bind i v b], it evaluates [v] to a number [n] and then needs to
"hand [n] to [b]".  Substitution does this syntactically: it walks [b] and
replaces every free occurrence of [i] with [Num n], producing a new term
that no longer mentions [i].  The interpreter then evaluates that term.

[subst i v e] replaces every _free_ instance of identifier [i] in [e] with
the term [v].  The standard notation for this operation is [ [i |-> v] e ]
(read: "[i] maps to [v] in [e]").  Only free occurrences are replaced:
bound ones are owned by an inner [Bind] and must not be disturbed.

The implementation is a structural [Fixpoint] with one case per constructor:

  - [Num x]: a number has no identifiers; return it unchanged.
  - [Plus l r], [Minus l r]: recurse into both operands independently.
    The scope is the same on both sides.
  - [Id i']: the only place a free occurrence can live.  If [i = i'] this
    is the occurrence we are replacing - return [v].  Otherwise return
    [Id i'] untouched.
  - [Bind i' v' b']: the subtle case, and the mirror image of [free_in]'s
    [Bind] case.  The bound expression [v'] lives in the _outer_ scope, so
    [i] may be free there - always recurse into [v'].  The body [b'] is a
    different story: if [i = i'] then [b'] is under a new binding of [i],
    which shadows the [i] we are substituting for.  Every free [i] in [b']
    refers to the _inner_ [i'], not the outer one, so we must _not_ recurse
    into [b'].  If [i ≠ i'] the inner binding does not shadow [i], and we
    recurse into [b'] as usual.

The two branches of the [Bind] case side by side:
[[
  if String.eqb i i'
  then Bind i' (subst i v v') b'          (* shadow: skip body *)
  else Bind i' (subst i v v') (subst i v b')  (* no shadow: recurse *)
]]
 *)

Fixpoint subst (i : string) (v : BAE) (e : BAE) : BAE :=
  match e with
  | Num x      => Num x
  | Plus  l r  => Plus  (subst i v l) (subst i v r)
  | Minus l r  => Minus (subst i v l) (subst i v r)
  | Bind i' v' b' =>
      if String.eqb i i'
      then Bind i' (subst i v v') b'
      else Bind i' (subst i v v') (subst i v b')
  | Id i'      => if String.eqb i i' then v else Id i'
  end.

(**
_Basic replacement._  Substituting [7] for [x] in [x + x - 4] replaces
both free occurrences of [x] and leaves [4] alone.
 *)

Example subst_example :
  subst "x" (Num 7) (Minus (Plus (Id "x") (Id "x")) (Num 4))
  = Minus (Plus (Num 7) (Num 7)) (Num 4).
Proof. reflexivity. Qed.

(**
_Shadowing stops the substitution at the body boundary._  In
[bind x = 1 in x], the [Bind "x"] introduces a new [x] whose scope is
the body [Id "x"].  The outer [subst "x" ...] substitutes into the bound
expression [Num 1] (no [x] there, so nothing changes) but does _not_
enter the body - the inner binding owns that [x].  The term is returned
structurally identical.
 *)

Example subst_shadowed :
  subst "x" (Num 9) (Bind "x" (Num 1) (Id "x"))
  = Bind "x" (Num 1) (Id "x").
Proof. reflexivity. Qed.

(**
_Shadowing applies to the body, not the value._  Even when the binder
variable matches [i], the bound expression [v'] is in the outer scope and
IS substituted into.  Here [x] appears free in the value [x + 1], so it
is replaced by [3].  The body [Id "x"] is skipped because [i = i'].
 *)

Example subst_in_value :
  subst "x" (Num 3) (Bind "x" (Plus (Id "x") (Num 1)) (Id "x"))
  = Bind "x" (Plus (Num 3) (Num 1)) (Id "x").
Proof. reflexivity. Qed.

(**
_A different binder does not stop the substitution._  Here the [Bind] uses
[y], not [x], so it does not shadow [x].  The substitution passes straight
through the binding and replaces the free [x] in the body.
 *)

Example subst_through_other_bind :
  subst "x" (Num 5) (Bind "y" (Num 1) (Id "x"))
  = Bind "y" (Num 1) (Num 5).
Proof. reflexivity. Qed.

(** * SECTION 4: SIZE AND A KEY SUBSTITUTION INVARIANT *)

(**
[size] counts the nodes of an expression.  It is the measure that
makes our interpreter terminate (see Section 5).  Every subterm of a term is
smaller than the term.  Thus, every recursive call to an evaluator or type
checker operates on a smaller structure.  This is the basis for terminating
recursion and structural induction.  Rocq actually checks this fact every time
you create a [Fixpoint] function.
 *)

Fixpoint size (e : BAE) : nat :=
  match e with
  | Num _      => 1
  | Id _       => 1
  | Plus  l r  => 1 + size l + size r
  | Minus l r  => 1 + size l + size r
  | Bind _ v b => 1 + size v + size b
  end.

Lemma size_pos : forall e, 1 <= size e.
Proof. induction e; simpl; lia. Qed.

(**
The interpreter (Section 5) handles [Bind i v b] by evaluating [v] to a
number [n] and then evaluating [subst i (Num n) b].  That second step is
the problem: [subst i (Num n) b] is a freshly constructed term, not a
subterm of the original expression.  Rocq's structural-recursion checker
cannot see that it is "smaller", so a plain [Fixpoint eval] would be
rejected.  The solution is to recurse on a fuel counter instead - but
only if we know the fuel is always sufficient.

[size_subst_num] is what makes that work.  Substituting a number for an
identifier does not change the size of the term: every [Id] leaf (size 1)
is replaced by a [Num] leaf (also size 1), and every other node is
unchanged.  Therefore [size (subst i (Num n) b) = size b], and starting
the interpreter with fuel [= size e] is always enough - the substituted
body never needs more fuel than the original body.
 *)

Lemma size_subst_num : forall e i n,
  size (subst i (Num n) e) = size e.
Proof.
  induction e as [m | l IHl r IHr | l IHl r IHr | i' v IHv b IHb | y];
    intros i n; simpl.
  - reflexivity.
  - rewrite IHl, IHr. reflexivity.
  - rewrite IHl, IHr. reflexivity.
  - destruct (String.eqb i i').
    + simpl. rewrite IHv. reflexivity.
    + simpl. rewrite IHv, IHb. reflexivity.
  - destruct (String.eqb i y); reflexivity.
Qed.

(** * SECTION 5: SEMANTICS - A SUBSTITUTION INTERPRETER (WITH FUEL) *)

(**
BAE extends AE with two new constructors: [Id] and [Bind].  The AE cases
([Num], [Plus], [Minus]) evaluate exactly as before - a number returns
itself, and binary operators evaluate both operands and combine the results.
[Id] has no value on its own and returns [None].  The interesting case is
[Bind].

When the interpreter reaches [Bind i v b] it:
#<ol>#
#<li>#evaluates the bound expression [v] to obtain a number [n];#</li>#
#<li>#substitutes [n] for every free occurrence of [i] in the body [b],
     producing a new term [subst i (Num n) b]; and#</li>#
#<li>#evaluates that new term.#</li>#
#</ol>#

The natural Rocq definition of this case is:
[[
  eval (Bind i v b) =
    match eval v with
    | Some n => eval (subst i (Num n) b)
    | None   => None
    end
]]
but there is a catch that the termination checker forces into the open:
[subst i (Num n) b] is a _brand-new_ term, not a structural subterm of
[Bind i v b].  Rocq cannot see that the recursion shrinks, so a plain
[Fixpoint] on the expression is _rejected_.

The fix is to recurse on a decreasing _fuel_ counter instead.  Because
substituting a number preserves [size] (Section 4), starting with fuel
[= size e] is always enough.

(Foreshadowing: the next chapter, "Adding Environments", removes substitution
entirely, and the resulting interpreter _is_ a clean structural [Fixpoint] with
no fuel - one more reason environments are the better design.)
 *)

Fixpoint evalF (fuel : nat) (e : BAE) : option nat :=
  match fuel with
  | 0 => None
  | S f =>
      match e with
      | Num n => Some n
      | Plus l r =>
          match evalF f l, evalF f r with
          | Some a, Some b => Some (a + b)
          | _, _ => None
          end
      | Minus l r =>
          match evalF f l, evalF f r with
          | Some a, Some b => Some (a - b)
          | _, _ => None
          end
      | Bind i v b =>
          match evalF f v with
          | Some n => evalF f (subst i (Num n) b)
          | None => None
          end
      | Id _ => None
      end
  end.

(**
The interpreter [eval] now becomes running [evalF] with just enough fuel.
[evalF] uses one fuel unit for eacn node.  This "just enough" is the number of
nodes in the abstract syntax term being evaluated.  Our [size] function gives us
exactly that.  [eval] now becomes:
*)
Definition eval (e : BAE) : option nat := evalF (size e) e.

(**
_Fuel monotonicity._  Any two fuel amounts that are both large enough (at least
[size e]) compute the same answer.  This is what makes [eval] well defined
regardless of the exact fuel we picked.
 *)
Lemma evalF_mono : forall f1 f2 e,
  size e <= f1 -> size e <= f2 -> evalF f1 e = evalF f2 e.
Proof.
  induction f1 as [| g IH]; intros f2 e H1 H2.
  - pose proof (size_pos e). lia.
  - destruct f2 as [| h].
    + pose proof (size_pos e). lia.
    + destruct e as [m | l r | l r | i v b | y]; simpl in *.
      * reflexivity.
      * rewrite (IH h l) by lia. rewrite (IH h r) by lia. reflexivity.
      * rewrite (IH h l) by lia. rewrite (IH h r) by lia. reflexivity.
      * rewrite (IH h v) by lia.
        destruct (evalF h v) as [n |] eqn:Ev; [| reflexivity].
        rewrite (IH h (subst i (Num n) b))
          by (rewrite size_subst_num; lia).
        reflexivity.
      * reflexivity.
Qed.

(**
Three proof-engineering patterns appear for the first time in this proof.
Each is triggered by a specific situation:

_[pose proof (size_pos e)]._  Trigger: [lia] cannot close an arithmetic goal
because it is missing a bound it has no way to derive on its own.  In the
[f1 = 0] base case the context contains [H1 : size e <= 0], which looks
contradictory - but [lia] only knows what is explicitly in the context.
It does not know [size e >= 1] unless told.  [pose proof (size_pos e)] adds
that fact as a new hypothesis, after which [lia] can combine [1 <= size e]
with [size e <= 0] and close the goal.  The pattern is: when [lia] fails,
ask what arithmetic fact it is missing, prove it separately with [pose proof],
and let [lia] finish.

_[rewrite (IH h l) by lia]._  Trigger: you want to rewrite with an induction
hypothesis that has arithmetic preconditions, and those preconditions are
not yet in the context as hypotheses.  The IH here says (roughly)
[size e <= g -> size e <= h -> evalF g e = evalF h e].  Applying it at [l]
requires discharging [size l <= g] and [size l <= h].  Instead of opening
two new subgoals and closing them manually, [rewrite (IH h l) by lia] does
both in one step: rewrite with the IH at specific arguments, and
immediately run [lia] on every side condition the rewrite creates.  The
pattern [rewrite ... by tac] generalises to any rewrite whose obligations
are dischargeable by a single tactic.

_[destruct (evalF h v) as [n |] eqn:Ev]._  Trigger: you need to case-split
on a computed value, AND you will need to refer to the result of that
computation in the goal or in a later rewrite.  A plain [destruct (evalF h v)]
would split into [Some n] and [None] cases but discard the equation
[evalF h v = Some n] (or [= None]) from the context.  Adding [eqn:Ev]
records it as [Ev : evalF h v = Some n], which is then available when
[rewrite (IH h (subst i (Num n) b))] needs to refer to the same value [n].
Without [eqn:], the identity of [n] would be lost and the rewrite could not
be stated.  The pattern applies whenever a [destruct] would otherwise
discard information you need downstream.
 *)

(** Running with any sufficient fuel agrees with [eval]. *)
Lemma evalF_eval : forall f e,
  size e <= f -> evalF f e = eval e.
Proof.
  intros f e H. unfold eval. apply evalF_mono; [assumption | lia].
Qed.

(**
_Clean equations._  With monotonicity in hand we can prove the "obvious"
recursive equations for [eval], hiding the fuel entirely.  These are the lemmas
we actually use to reason about [eval].
 *)

Lemma eval_Num : forall n, eval (Num n) = Some n.
Proof. intro n. reflexivity. Qed.

Lemma eval_Id : forall x, eval (Id x) = None.
Proof. intro x. reflexivity. Qed.

Lemma eval_Plus : forall l r,
  eval (Plus l r) =
  match eval l, eval r with
  | Some a, Some b => Some (a + b)
  | _, _ => None
  end.
Proof.
  intros l r. unfold eval at 1. simpl.
  rewrite (evalF_eval (size l + size r) l) by lia.
  rewrite (evalF_eval (size l + size r) r) by lia.
  reflexivity.
Qed.

Lemma eval_Minus : forall l r,
  eval (Minus l r) =
  match eval l, eval r with
  | Some a, Some b => Some (a - b)
  | _, _ => None
  end.
Proof.
  intros l r. unfold eval at 1. simpl.
  rewrite (evalF_eval (size l + size r) l) by lia.
  rewrite (evalF_eval (size l + size r) r) by lia.
  reflexivity.
Qed.

Lemma eval_Bind : forall i v b,
  eval (Bind i v b) =
  match eval v with
  | Some n => eval (subst i (Num n) b)
  | None => None
  end.
Proof.
  intros i v b. unfold eval at 1. simpl.
  rewrite (evalF_eval (size v + size b) v) by lia.
  destruct (eval v) as [n |] eqn:Ev; [| reflexivity].
  rewrite (evalF_eval (size v + size b) (subst i (Num n) b))
    by (rewrite size_subst_num; lia).
  reflexivity.
Qed.

(** * SECTION 6: TESTING THE INTERPRETER *)

(**
A few concrete runs of [eval]: the two examples from Section 1, a free
identifier (which fails), and an inner binding shadowing an outer one.
 *)

Example test_eval_1 :
  eval bae_example_1 = Some 10.
Proof. reflexivity. Qed.

Example test_eval_2 :
  eval bae_example_2 = Some 5.
Proof. reflexivity. Qed.

(* A free identifier has no value. *)
Example test_eval_free :
  eval bae_free = None.
Proof. reflexivity. Qed.

(* Inner bindings can shadow outer ones. *)
Example test_eval_shadow :
  eval (Bind "x" (Num 1) (Bind "x" (Num 2) (Id "x"))) = Some 2.
Proof. reflexivity. Qed.

(** * SECTION 7: PROPERTIES OF SUBSTITUTION *)

(**
Substituting for an identifier that does not occur free leaves the
term unchanged.  This is the syntactic heart of "shadowing".
 *)
Lemma subst_not_free : forall e i v,
  free_in i e = false -> subst i v e = e.
Proof.
  induction e as [m | l IHl r IHr | l IHl r IHr | i' v' IHv' b IHb | y];
    intros i v H; simpl in *.
  - reflexivity.
  - apply orb_false_iff in H. destruct H as [Hl Hr].
    rewrite IHl by assumption. rewrite IHr by assumption. reflexivity.
  - apply orb_false_iff in H. destruct H as [Hl Hr].
    rewrite IHl by assumption. rewrite IHr by assumption. reflexivity.
  - apply orb_false_iff in H. destruct H as [Hv Hb].
    rewrite IHv' by assumption.
    destruct (String.eqb i i') eqn:E.
    + reflexivity.
    + rewrite IHb by assumption. reflexivity.
  - rewrite H. reflexivity.
Qed.

(**
Two more tactics debut here.  [apply orb_false_iff in H] applies a lemma
_forward_, to a hypothesis: from [H : free_in i l || free_in i r = false] it
yields [H : free_in i l = false /\ free_in i r = false] (which [destruct] then
splits).  The plain [apply L] from AE transforms the _goal_; [apply L in H]
transforms a hypothesis instead.  And [rewrite IHl by assumption] uses
[assumption] - "close this side condition with whatever matching hypothesis is
already in context".
 *)

(* Substituting into a closed term does nothing. *)
Lemma subst_closed : forall e i v,
  closed e -> subst i v e = e.
Proof.
  intros e i v Hc. apply subst_not_free. apply Hc.
Qed.

(**
How substitution changes the free variables.  Replacing [x] by a
NUMBER (which has no free variables of its own) removes [x] from the
free set and leaves every other identifier exactly as it was.
 *)
Lemma free_in_subst_num : forall e x n z,
  free_in z (subst x (Num n) e)
  = (if String.eqb z x then false else free_in z e).
Proof.
  induction e as [m | l IHl r IHr | l IHl r IHr | y v IHv b IHb | y];
    intros x n z; simpl.
  - destruct (String.eqb z x); reflexivity.
  - rewrite IHl, IHr. destruct (String.eqb z x); reflexivity.
  - rewrite IHl, IHr. destruct (String.eqb z x); reflexivity.
  - destruct (String.eqb x y) eqn:Exy; simpl.
    + apply String.eqb_eq in Exy. subst y. rewrite IHv.
      destruct (String.eqb z x); reflexivity.
    + rewrite IHv, IHb.
      destruct (String.eqb z x); destruct (String.eqb z y); reflexivity.
  - destruct (String.eqb x y) eqn:Exy; simpl.
    + apply String.eqb_eq in Exy. subst y.
      destruct (String.eqb z x); reflexivity.
    + destruct (String.eqb z x) eqn:Ezx.
      * apply String.eqb_eq in Ezx. subst z.
        rewrite Exy. reflexivity.
      * reflexivity.
Qed.

(**
If [x] is the ONLY identifier that might occur free in [e], then
substituting a number for [x] yields a CLOSED term.  This is the
"last variable gets bound" step behind the progress theorem for
closed programs (an exercise/challenge).
 *)
Lemma closed_after_subst : forall e x n,
  (forall y, y <> x -> free_in y e = false) ->
  closed (subst x (Num n) e).
Proof.
  intros e x n H z. rewrite free_in_subst_num.
  destruct (String.eqb z x) eqn:E.
  - reflexivity.
  - apply String.eqb_neq in E. apply H. exact E.
Qed.

(** * SECTION 8: PROPERTIES OF EVALUATION *)

(**
Evaluation is deterministic - [eval] is a function, so this is
immediate, but it is worth stating.
 *)
Lemma eval_deterministic : forall e r1 r2,
  eval e = r1 -> eval e = r2 -> r1 = r2.
Proof. intros e r1 r2 H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.

(* A number always evaluates to itself. *)
Lemma eval_num_value : forall n, eval (Num n) = Some n.
Proof. exact eval_Num. Qed.

(**
[bind x = a in b] where [a] is a literal is exactly [b] with [x]
replaced by [a].  This is the defining "let" equation.
 *)
Lemma bind_num_subst : forall x n b,
  eval (Bind x (Num n) b) = eval (subst x (Num n) b).
Proof.
  intros x n b. rewrite eval_Bind. rewrite eval_Num. reflexivity.
Qed.

(**
An unused binding can be dropped: if [x] does not occur free in [b]
and the bound expression evaluates, the binding has no effect.
 *)
Lemma bind_unused : forall x v b n,
  eval v = Some n ->
  free_in x b = false ->
  eval (Bind x v b) = eval b.
Proof.
  intros x v b n Hv Hfree.
  rewrite eval_Bind. rewrite Hv.
  rewrite subst_not_free by assumption. reflexivity.
Qed.

(** * SECTION 9: EXPRESSION EQUIVALENCE *)

(**
Two BAE terms are equivalent when they evaluate to the same result
(including both failing).  As with AE this is an equivalence
relation.
 *)

Definition bae_equiv (e1 e2 : BAE) : Prop := eval e1 = eval e2.

Lemma bae_equiv_refl : forall e, bae_equiv e e.
Proof. intro e. unfold bae_equiv. reflexivity. Qed.

Lemma bae_equiv_sym : forall e1 e2,
  bae_equiv e1 e2 -> bae_equiv e2 e1.
Proof. intros e1 e2 H. unfold bae_equiv in *. symmetry. exact H. Qed.

Lemma bae_equiv_trans : forall e1 e2 e3,
  bae_equiv e1 e2 -> bae_equiv e2 e3 -> bae_equiv e1 e3.
Proof.
  intros e1 e2 e3 H12 H23. unfold bae_equiv in *.
  transitivity (eval e2); assumption.
Qed.

(* A worked equivalence: renaming a bound variable that is used
   consistently does not change the meaning. *)
Example alpha_example :
  bae_equiv (Bind "x" (Num 3) (Plus (Id "x") (Num 1)))
            (Bind "y" (Num 3) (Plus (Id "y") (Num 1))).
Proof. reflexivity. Qed.

(** * SECTION 10: CONCRETE SYNTAX - A NOTATION PARSER *)

(**
Section 1 gave the concrete grammar of BAE informally:

  t ::= NUM | ID | t + t | t - t | bind ID = t in t

We can now make that grammar REAL, exactly as in AE and ABE, so that

  <{ bind "x" = 5 + 2 in "x" + "x" - 4 }>

elaborates directly into the abstract tree.  Following Software
Foundations' Imp, the parser is built from Rocq NOTATIONS alone, and a
concrete term is DEFINITIONALLY EQUAL to the abstract tree it denotes.

The new wrinkle here is IDENTIFIERS.  BAE has two leaf coercions
instead of one: a bare numeral is a [Num], and a bare STRING is an
[Id].  So inside the brackets [3] means [Num 3] and ["x"] means
[Id "x"].
 *)

Coercion Num : nat >-> BAE.
Coercion Id  : string >-> BAE.

(**
The grammar entry, its delimiters, grouping, and the escape hatch back
to ordinary Rocq terms (which, via the two coercions above, is what
lets numerals AND string identifiers appear inside the brackets).
 *)

Declare Custom Entry bae.
Declare Scope bae_scope.
Delimit Scope bae_scope with bae.

Notation "<{ e }>" := e (e custom bae at level 99) : bae_scope.
Notation "( x )" := x (in custom bae, x at level 99) : bae_scope.
Notation "x" := x (in custom bae at level 0, x constr at level 0) : bae_scope.

(**
The operators.  [+] and [-] are as before.  The binding form
[bind ID = e1 in e2] is the concrete syntax for [Bind]: its identifier
slot [v] is an ordinary string (a Rocq [constr]), while the bound
expression and the body are themselves BAE terms.
 *)

Notation "x + y" := (Plus x y)  (in custom bae at level 50, left associativity) : bae_scope.
Notation "x - y" := (Minus x y) (in custom bae at level 50, left associativity) : bae_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom bae at level 89, v constr at level 0,
   e1 custom bae at level 99, e2 custom bae at level 99) : bae_scope.

Open Scope bae_scope.

(**
Because the notation is only sugar, every parse below is proved by
[reflexivity].
 *)

Example parse_arith : <{ 3 + 4 }> = Plus (Num 3) (Num 4).
Proof. reflexivity. Qed.

Example parse_id : <{ "x" + 1 }> = Plus (Id "x") (Num 1).
Proof. reflexivity. Qed.

(* The examples from Section 1, written concretely. *)
Example bae_example_1_concrete :
  <{ bind "x" = 5 + 2 in "x" + "x" - 4 }> = bae_example_1.
Proof. reflexivity. Qed.

Example bae_example_2_concrete :
  <{ bind "x" = 4 in bind "y" = 5 in "x" + "y" - 4 }> = bae_example_2.
Proof. reflexivity. Qed.

Example bae_free_concrete : <{ "x" + 1 }> = bae_free.
Proof. reflexivity. Qed.

(**
[eval] is oblivious to the notation - it consumes exactly the same tree.
 *)

Example eval_concrete_bind :
  eval <{ bind "x" = 5 + 2 in "x" + "x" - 4 }> = Some 10.
Proof. reflexivity. Qed.

(* A free identifier still has no value. *)
Example eval_concrete_free : eval <{ "x" + 1 }> = None.
Proof. reflexivity. Qed.

(* Inner bindings shadow outer ones, concretely. *)
Example eval_concrete_shadow :
  eval <{ bind "x" = 1 in bind "x" = 2 in "x" }> = Some 2.
Proof. reflexivity. Qed.

(**
Metavariables may appear inside the brackets too: [v] ranges over
[string] identifiers and [b] over [BAE] bodies.  This lets us restate
the defining "let" equation [bind_num_subst] in concrete syntax.
 *)

Lemma bind_num_subst_concrete : forall (v : string) (n : nat) (b : BAE),
  eval <{ bind v = n in b }> = eval (subst v (Num n) b).
Proof.
  intros v n b. apply bind_num_subst.
Qed.

(** * SUMMARY *)

(**
In this lecture we:
#<ol>#
#<li>#Defined BAE = AE + identifiers (Id) + local bindings (Bind).#</li>#
#<li>#Formalised free/bound instances and closed terms.#</li>#
#<li>#Defined substitution and proved it ignores non-free variables.#</li>#
#<li>#Discovered that a substitution interpreter is NOT structurally
recursive in Rocq, and drove it with a [size]-bounded fuel.#</li>#
#<li>#Recovered clean recursive equations for [eval] and proved
properties of substitution and evaluation.#</li>#
#<li>#Made the concrete grammar real with a notation-based parser, so
that [<{ bind "x" = 5 + 2 in "x" + "x" - 4 }>] elaborates to the
abstract tree (numerals coerce to [Num], strings to [Id]).#</li>#
#</ol>#

Next: "Adding Environments" replaces eager substitution with a
deferred environment, yielding a clean structural interpreter, and
we _prove_ the two interpreters always agree.
 *)

(** * NEW PROOF TACTICS IN THIS CHAPTER *)

(**
Building on AE and ABE, this chapter adds a handful of proof-engineering
tactics, mostly for driving the fuel-based interpreter:

#<ul>#
#<li>#[assumption] - close the goal with whatever hypothesis already in context matches it.#</li>#
#<li>#[apply L in H] - apply a lemma _forward_, transforming a hypothesis [H] rather than the goal (contrast [apply L], which acts on the goal).#</li>#
#<li>#[pose proof t] - add a copy of an already-proved fact [t] to the context, e.g. [pose proof (size_pos e)] so [lia] can use it.#</li>#
#<li>#[rewrite ... by tac] - rewrite and immediately discharge the side conditions it raises with [tac] (typically [by lia] or [by assumption]).#</li>#
#<li>#[destruct t eqn:E] - case-split [t] while recording the chosen case as a hypothesis [E : t = ...] for later rewriting.#</li>#
#<li>#[unfold f at n] - unfold only the [n]-th occurrence of [f] (used as [unfold eval at 1] to expose one side of an equation).#</li>#
#</ul>#
 *)
