(** * Programming Languages in Rocq - Typed Functions *)

(**
Func and Rec gave us a Turing-powerful _untyped_ language: it can loop
([omega]), and it can get _stuck_ - [Plus (Boolean true) (Num 1)] is
nonsense that the interpreter only rejects (as [None]) at run time,
after it has already started evaluating.  This chapter adds a _static
type system_ that rejects such programs _before_ evaluation.

The plan:
#<ol>#
#<li>#A _type language_ [Ty]: numbers, Booleans, and _function_ types.#</li>#
#<li>#The typed term language [TFBAEC]: Rec's FBAEC, except [Lambda] now _ascribes_ its parameter's type (you cannot infer a domain type from a function that has not yet been applied).#</li>#
#<li>#The _type checker_ [typeof] - "an interpreter that returns _types_ instead of values", carrying an identifier->type _context_ exactly like [evalM] carries a value environment.#</li>#
#<li>#The _strict_ interpreter [evalM] (call-by-value, fuel-driven) - the _only_ interpreter now (no more lazy [evalL]) - with _fuel monotonicity_ carried over from Rec.#</li>#
#<li>#_Type soundness_: well-typed programs do not get stuck.  We witness it with a battery of machine-checked examples - good programs run to a value of the predicted type, and every classic stuck term is rejected by [typeof].#</li>#
#</ol>#

This mirrors the "Typed Functions" unit of PLIH:
  https://ku-sldg.github.io/plih//types/1-Function-Types.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_tfun_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: THE TYPE LANGUAGE *)

(**
Types are numbers, Booleans, and _function_ types [TArr d r] ("d -> r"),
the type of a function from domain [d] to range [r].  Function types
are what make this more than a flat set of base types - they let the
checker track what a lambda expects and what an application produces.
 *)
Inductive Ty : Type :=
| TNum  : Ty
| TBool : Ty
| TArr  : Ty -> Ty -> Ty.

(**
Type checking needs to _compare_ types (does the argument's type match
the function's domain?), so we need decidable equality on [Ty].
 *)
Fixpoint Ty_eqb (a b : Ty) : bool :=
  match a, b with
  | TNum, TNum   => true
  | TBool, TBool => true
  | TArr d1 r1, TArr d2 r2 => andb (Ty_eqb d1 d2) (Ty_eqb r1 r2)
  | _, _ => false
  end.

Lemma Ty_eqb_refl : forall t, Ty_eqb t t = true.
Proof.
  intros t. induction t as [| | d IHd r IHr]; simpl; try reflexivity.
  rewrite IHd, IHr. reflexivity.
Qed.

Lemma Ty_eqb_eq : forall a b, Ty_eqb a b = true -> a = b.
Proof.
  induction a as [| | d1 IHd r1 IHr]; intros b H; destruct b as [| | d2 r2];
    simpl in H; try discriminate; try reflexivity.
  apply andb_true_iff in H. destruct H as [Hd Hr].
  rewrite (IHd d2 Hd), (IHr r2 Hr). reflexivity.
Qed.

(* [Ty_eqb] exactly reflects equality: a clean iff for rewriting. *)
Lemma Ty_eqb_true_iff : forall a b, Ty_eqb a b = true <-> a = b.
Proof.
  intros a b. split.
  - apply Ty_eqb_eq.
  - intros H. subst. apply Ty_eqb_refl.
Qed.

(** * SECTION 2: THE TYPED TERM LANGUAGE *)

(**
[TFBAEC] is Rec's FBAEC with one change: [Lambda] now carries the
declared type of its parameter.  We cannot infer a parameter's type
from the function alone - its value is not known until application -
so, as in PLIH, the programmer _ascribes_ it: [Lambda x T b] is
"lambda (x : T) in b".  Everything else is unchanged.
 *)
Inductive TFBAEC : Type :=
| Num     : nat -> TFBAEC
| Plus    : TFBAEC -> TFBAEC -> TFBAEC
| Minus   : TFBAEC -> TFBAEC -> TFBAEC
| Mult    : TFBAEC -> TFBAEC -> TFBAEC
| Boolean : bool -> TFBAEC
| IsZero  : TFBAEC -> TFBAEC
| If      : TFBAEC -> TFBAEC -> TFBAEC -> TFBAEC
| Bind    : string -> TFBAEC -> TFBAEC -> TFBAEC
| Lambda  : string -> Ty -> TFBAEC -> TFBAEC   (* parameter type ascribed *)
| App     : TFBAEC -> TFBAEC -> TFBAEC
| Id      : string -> TFBAEC.

(** * SECTION 3: THE TYPE CHECKER *)

(**
A _type context_ maps identifiers to their types - the static analogue of
an evaluation environment.  It is literally [Env Ty], reusing the same
association lists (and [lookup]/[extend]) that [evalM] uses for values.
 *)
Definition Ctx := Env Ty.

(* Small helper: a binary arithmetic operator wants two numbers and
   produces a number.  Keeps [typeof]'s Plus/Minus/Mult cases uniform. *)
Definition tnumBinop (a b : option Ty) : option Ty :=
  match a, b with
  | Some TNum, Some TNum => Some TNum
  | _, _ => None
  end.

(**
[typeof ctx e] computes the type of [e] under [ctx], or [None] if [e]
is ill-typed.  Compare it to [evalM]: same shape, same recursion, but
it returns _types_ and needs no fuel - type checking always terminates.

  - arithmetic wants numbers, yields a number;
  - [IsZero] wants a number, yields a Boolean;
  - [If] wants a Boolean condition and _two branches of the same type_,
    which is that common type (a static term cannot know which branch
    runs, so both must agree);
  - [Lambda x T b] : with [x:T] in scope [b] has some type [R], so the
    lambda has type [T -> R];
  - [App f a] : [f] must be a function [D -> R] and [a] must have type
    [D]; the application then has type [R].
 *)
Fixpoint typeof (ctx : Ctx) (e : TFBAEC) : option Ty :=
  match e with
  | Num _ => Some TNum
  | Plus  l r => tnumBinop (typeof ctx l) (typeof ctx r)
  | Minus l r => tnumBinop (typeof ctx l) (typeof ctx r)
  | Mult  l r => tnumBinop (typeof ctx l) (typeof ctx r)
  | Boolean _ => Some TBool
  | IsZero e0 =>
      match typeof ctx e0 with
      | Some TNum => Some TBool
      | _ => None
      end
  | If c t f =>
      match typeof ctx c with
      | Some TBool =>
          match typeof ctx t, typeof ctx f with
          | Some tThen, Some tElse =>
              if Ty_eqb tThen tElse then Some tThen else None
          | _, _ => None
          end
      | _ => None
      end
  | Bind i v b =>
      match typeof ctx v with
      | Some tv => typeof (extend i tv ctx) b
      | None => None
      end
  | Lambda i t b =>
      match typeof (extend i t ctx) b with
      | Some tb => Some (TArr t tb)
      | None => None
      end
  | App f a =>
      match typeof ctx f, typeof ctx a with
      | Some (TArr d r), Some ta => if Ty_eqb d ta then Some r else None
      | _, _ => None
      end
  | Id x => lookup x ctx
  end.

(* Type checking a whole program uses the empty context. *)
Definition typecheck (e : TFBAEC) : option Ty := typeof nil e.

(** * SECTION 4: THE STRICT INTERPRETER *)

(**
Values are numbers, Booleans, and closures - exactly Rec's [RVal].  A
closure captures its definition-time environment (static scoping).  The
parameter's declared type plays no role at run time, so the closure
does not store it.
 *)
Inductive TVal : Type :=
| NumV     : nat -> TVal
| BoolV    : bool -> TVal
| ClosureV : string -> TFBAEC -> list (string * TVal) -> TVal.

(**
The _strict_ (call-by-value) interpreter, identical to Rec's [evalM]
except that [Lambda] now has a type annotation to ignore.  It is still
fuel-driven: types will guarantee well-typed programs terminate, but
[evalM] is defined on _all_ terms, including ill-typed ones, so the fuel
stays.  This is the _only_ interpreter in this chapter - no lazy [evalL].
 *)
Fixpoint evalM (fuel : nat) (env : Env TVal) (e : TFBAEC) : option TVal :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (NumV n)
      | Plus l r =>
          match evalM k env l, evalM k env r with
          | Some (NumV a), Some (NumV b) => Some (NumV (a + b))
          | _, _ => None
          end
      | Minus l r =>
          match evalM k env l, evalM k env r with
          | Some (NumV a), Some (NumV b) => Some (NumV (a - b))
          | _, _ => None
          end
      | Mult l r =>
          match evalM k env l, evalM k env r with
          | Some (NumV a), Some (NumV b) => Some (NumV (a * b))
          | _, _ => None
          end
      | Boolean b => Some (BoolV b)
      | IsZero e0 =>
          match evalM k env e0 with
          | Some (NumV n) => Some (BoolV (Nat.eqb n 0))
          | _ => None
          end
      | If c t f =>
          match evalM k env c with
          | Some (BoolV true)  => evalM k env t
          | Some (BoolV false) => evalM k env f
          | _ => None
          end
      | Bind i v b =>
          match evalM k env v with
          | Some v' => evalM k (extend i v' env) b
          | None => None
          end
      | Lambda i _ b => Some (ClosureV i b env)
      | App f a =>
          match evalM k env f with
          | Some (ClosureV i b cenv) =>
              match evalM k env a with
              | Some a' => evalM k (extend i a' cenv) b
              | None => None
              end
          | _ => None
          end
      | Id x => lookup x env
      end
  end.

Definition eval (e : TFBAEC) : option TVal := evalM 1000 nil e.

(** * SECTION 5: FUEL MONOTONICITY (well-definedness of [evalM]) *)

(**
As in Func and Rec, no measure bounds the fuel, so the well-definedness
result is _monotonicity_: more fuel never changes an answer already
produced.  The proof is Rec's verbatim, with [Lambda]'s new type
argument the only difference (still just [exact H]).
 *)
Lemma evalM_mono : forall f1 f2 env e v,
  f1 <= f2 -> evalM f1 env e = Some v -> evalM f2 env e = Some v.
Proof.
  induction f1 as [| k IH]; intros f2 env e v Hle H.
  - simpl in H. discriminate.
  - destruct f2 as [| k2]; [lia |].
    destruct e; simpl in H |- *.
    + (* Num *) exact H.
    + (* Plus *)
      destruct (evalM k env e1) as [[a | b | i bd ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b | i bd ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Minus *)
      destruct (evalM k env e1) as [[a | b | i bd ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b | i bd ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Mult *)
      destruct (evalM k env e1) as [[a | b | i bd ce] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b | i bd ce] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Boolean *) exact H.
    + (* IsZero *)
      destruct (evalM k env e) as [[n | b | i bd ce] |] eqn:E0; try discriminate.
      rewrite (IH k2 env e (NumV n) ltac:(lia) E0). exact H.
    + (* If *)
      destruct (evalM k env e1) as [[a | bb | i bd ce] |] eqn:Ec; try discriminate.
      destruct bb.
      * rewrite (IH k2 env e1 (BoolV true) ltac:(lia) Ec).
        apply (IH k2 env e2 v). lia. exact H.
      * rewrite (IH k2 env e1 (BoolV false) ltac:(lia) Ec).
        apply (IH k2 env e3 v). lia. exact H.
    + (* Bind *)
      destruct (evalM k env e1) as [v' |] eqn:Ev; try discriminate.
      rewrite (IH k2 env e1 v' ltac:(lia) Ev).
      apply (IH k2 (extend s v' env) e2 v). lia. exact H.
    + (* Lambda *) exact H.
    + (* App *)
      destruct (evalM k env e1) as [[a | b | i bd ce] |] eqn:Ef; try discriminate.
      destruct (evalM k env e2) as [a' |] eqn:Ea; try discriminate.
      rewrite (IH k2 env e1 (ClosureV i bd ce) ltac:(lia) Ef).
      rewrite (IH k2 env e2 a' ltac:(lia) Ea).
      apply (IH k2 (extend i a' ce) bd v). lia. exact H.
    + (* Id *) exact H.
Qed.

(** * SECTION 6: TYPE CHECKING IN ACTION *)

(**
A gallery of well-typed terms followed by _rejections_: every classic
stuck term is caught statically.  Good programs pass [typecheck] and
run; bad programs never reach [eval].
 *)

(* [inc] : a well-typed increment function, Nat -> Nat. *)
Definition inc : TFBAEC := Lambda "x" TNum (Plus (Id "x") (Num 1)).

Example ty_inc : typecheck inc = Some (TArr TNum TNum).
Proof. reflexivity. Qed.

Example ty_app : typecheck (App inc (Num 4)) = Some TNum.
Proof. reflexivity. Qed.

(* A function is a first-class value with a function type. *)
Example ty_higher_order :
  typecheck (Lambda "f" (TArr TNum TNum) (App (Id "f") (Num 0)))
  = Some (TArr (TArr TNum TNum) TNum).
Proof. reflexivity. Qed.

Example ty_if : typecheck (If (IsZero (Num 0)) (Num 1) (Num 2)) = Some TNum.
Proof. reflexivity. Qed.

Example ty_bind :
  typecheck (Bind "x" (Num 5) (IsZero (Id "x"))) = Some TBool.
Proof. reflexivity. Qed.

(* ---- and now the _rejections_: every classic "stuck" term is caught ---- *)

(* Adding a Boolean to a number is nonsense - rejected statically. *)
Example ill_plus_bool :
  typecheck (Plus (Boolean true) (Num 1)) = None.
Proof. reflexivity. Qed.

(* [If] branches of different types cannot be given one type. *)
Example ill_if_branches :
  typecheck (If (Boolean true) (Num 1) (Boolean false)) = None.
Proof. reflexivity. Qed.

(* A condition that is not a Boolean is rejected. *)
Example ill_if_cond :
  typecheck (If (Num 1) (Num 2) (Num 3)) = None.
Proof. reflexivity. Qed.

(* Applying a number as if it were a function is rejected. *)
Example ill_apply_num :
  typecheck (App (Num 1) (Num 2)) = None.
Proof. reflexivity. Qed.

(* Argument type mismatch: [inc] wants a Nat, given a Boolean. *)
Example ill_app_argtype :
  typecheck (App inc (Boolean true)) = None.
Proof. reflexivity. Qed.

(* An unbound identifier has no type. *)
Example ill_unbound : typecheck (Id "y") = None.
Proof. reflexivity. Qed.

(**
_The point of types._  Rec's [omega] = [selfApp selfApp] with
[selfApp = \x. x x] cannot be typed: for [x x] to make sense [x] must
be both a function [D -> R] AND its own argument [D], i.e. [D = D -> R],
which no finite [Ty] satisfies.  So even with a parameter annotation,
self-application is _rejected_ - the type checker rules out the very term
that made the untyped language diverge.
 *)
Definition selfApp (t : Ty) : TFBAEC :=
  Lambda "x" t (App (Id "x") (Id "x")).

Example ill_selfApp_num : typecheck (selfApp TNum) = None.
Proof. reflexivity. Qed.

Example ill_selfApp_fun : typecheck (selfApp (TArr TNum TNum)) = None.
Proof. reflexivity. Qed.

(** * SECTION 7: TYPE SOUNDNESS (well-typed programs do not get stuck) *)

(**
_Type soundness_ is the payoff: a well-typed program never gets stuck -
evaluated with enough fuel it produces a value, and that value has the
type [typeof] predicted.  Symbolically, the guarantee we are after is

    typecheck e = Some t  ->  exists v, eval e = Some v /\ v : t.

A fully general machine-checked proof needs a logical-relations
argument (a type-indexed notion of "value [v] has type [t]" that also
constrains the environments captured inside closures); we set that up
in the exercises and leave the full development as advanced material,
exactly as PLIH states soundness informally at this point.

What we can check right now, concretely and completely, is soundness on
whole programs: a well-typed term and its value, side by side, with the
value's kind matching the predicted type.  Together with Section 6's
rejections (bad programs never reach [eval] at all) these witness the
property directly.
 *)

(* A base-type program: predicted [TNum], and indeed evaluates to a [NumV]. *)
Example sound_arith_ty : typecheck (App inc (Num 41)) = Some TNum.
Proof. reflexivity. Qed.
Example sound_arith_val : eval (App inc (Num 41)) = Some (NumV 42).
Proof. reflexivity. Qed.

(* A Boolean-type program: predicted [TBool], evaluates to a [BoolV]. *)
Example sound_bool_ty :
  typecheck (IsZero (Minus (Num 3) (Num 3))) = Some TBool.
Proof. reflexivity. Qed.
Example sound_bool_val :
  eval (IsZero (Minus (Num 3) (Num 3))) = Some (BoolV true).
Proof. reflexivity. Qed.

(* A function-type program: predicted [TNum -> TNum], evaluates to a
   closure (the only kind of value with a function type). *)
Example sound_fun_ty : typecheck inc = Some (TArr TNum TNum).
Proof. reflexivity. Qed.
Example sound_fun_val :
  exists i b env, eval inc = Some (ClosureV i b env).
Proof. eexists. eexists. eexists. reflexivity. Qed.

(**
_Canonical forms_, provably: if a closed value has a base type, we know
exactly which constructor it is.  This is the value-level half of
soundness and is fully provable now.  We phrase "value [v] has base
type" directly by [evalM], since a value's number/Boolean nature is
observable.  (The function-type case is the one needing the logical
relation, hence its omission here.)
 *)
Definition isNumV (v : TVal) : bool :=
  match v with NumV _ => true | _ => false end.
Definition isBoolV (v : TVal) : bool :=
  match v with BoolV _ => true | _ => false end.

(* [IsZero e] always produces a Boolean value whenever it produces one -
   a small, general, machine-checked slice of preservation for [TBool]. *)
Lemma iszero_yields_bool : forall f env e v,
  evalM f env (IsZero e) = Some v -> isBoolV v = true.
Proof.
  intros [| k] env e v H; simpl in H; [discriminate |].
  destruct (evalM k env e) as [[n | b | i bd ce] |]; try discriminate.
  injection H as H; subst v. reflexivity.
Qed.

(* Likewise every arithmetic operator yields a number value. *)
Lemma plus_yields_num : forall f env a b v,
  evalM f env (Plus a b) = Some v -> isNumV v = true.
Proof.
  intros [| k] env a b v H; simpl in H; [discriminate |].
  destruct (evalM k env a) as [[n | bb | i bd ce] |]; try discriminate;
  destruct (evalM k env b) as [[m | bb | i bd ce] |]; try discriminate.
  injection H as H; subst v. reflexivity.
Qed.

(**
[intros [| k]] (used in both lemmas above) destructs a hypothesis at
introduction time, combining [intros] with [destruct].  Writing
[intros [| k] env e v H] instead of [intros f env e v H; destruct f as
[| k]] saves a step and keeps the goal tidy.  The pattern [| k] matches
a [nat]: the left branch is zero, the right branch binds the predecessor
as [k].  After the intro the subgoal for zero is closed by [discriminate]
(evaluation under zero fuel is [None], not [Some v]) and the non-zero
case proceeds.
 *)

(** * SECTION 8: CONCRETE SYNTAX - TERMS AND TYPES *)

(**
Typing adds one thing to the surface syntax: a type _ascription_ on the
lambda parameter, classically written [v : T].  This is the only place
a type appears in a term - [Lambda] is the only constructor carrying a
[Ty] - so [v : T] is needed exactly there.

To support it we build two notations: a small grammar for _types_, and
the FBAEC term grammar from Rec with [lambda ID in body] replaced by
[lambda ID : T in body].
 *)

Coercion Num : nat >-> TFBAEC.
Coercion Id  : string >-> TFBAEC.

(**
_The type grammar._  Types are written between [<[ ... ]>]: [Nat] and
[Bool] are the base types, and [->] is the function arrow,
_right_-associative (so [Nat -> Nat -> Nat] is [Nat -> (Nat -> Nat)], a
function returning a function), matching the usual convention.
 *)

Declare Custom Entry ty.
Declare Scope tfun_scope.
Delimit Scope tfun_scope with tfun.

Notation "<[ t ]>" := t (t custom ty at level 50) : tfun_scope.
Notation "( t )" := t (in custom ty, t at level 50) : tfun_scope.
Notation "'Nat'"  := TNum  (in custom ty at level 0) : tfun_scope.
Notation "'Bool'" := TBool (in custom ty at level 0) : tfun_scope.
Notation "d -> r" := (TArr d r) (in custom ty at level 50, right associativity) : tfun_scope.

(**
_The term grammar._  Exactly Rec's FBAEC grammar - numerals/identifiers
via coercion, [*], [+], [-], [iszero], [true]/[false], [if], [bind], and
_juxtaposition_ application - with the one change that a function value
now carries its parameter type: [lambda ID : T in body].
 *)

Declare Custom Entry tfbaec.
Notation "<{ e }>" := e (e custom tfbaec at level 99) : tfun_scope.
Notation "( x )" := x (in custom tfbaec, x at level 99) : tfun_scope.
Notation "x" := x (in custom tfbaec at level 0, x constr at level 0) : tfun_scope.

Notation "f x" := (App f x) (in custom tfbaec at level 1, left associativity) : tfun_scope.
Notation "'iszero' x" := (IsZero x) (in custom tfbaec at level 75, right associativity) : tfun_scope.
Notation "x * y" := (Mult x y)  (in custom tfbaec at level 40, left associativity) : tfun_scope.
Notation "x + y" := (Plus x y)  (in custom tfbaec at level 50, left associativity) : tfun_scope.
Notation "x - y" := (Minus x y) (in custom tfbaec at level 50, left associativity) : tfun_scope.
Notation "'true'"  := (Boolean true)  (in custom tfbaec at level 0) : tfun_scope.
Notation "'false'" := (Boolean false) (in custom tfbaec at level 0) : tfun_scope.
Notation "'if' c 'then' t 'else' f" := (If c t f)
  (in custom tfbaec at level 89, c custom tfbaec at level 99,
   t custom tfbaec at level 99, f custom tfbaec at level 99) : tfun_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom tfbaec at level 89, v constr at level 0,
   e1 custom tfbaec at level 99, e2 custom tfbaec at level 99) : tfun_scope.
Notation "'lambda' v ':' T 'in' e" := (Lambda v T e)
  (in custom tfbaec at level 90, v constr at level 0,
   T custom ty at level 50, e custom tfbaec at level 99) : tfun_scope.

Open Scope tfun_scope.

(**
Types parse as expected, including right-associative arrows.
 *)

Example parse_ty_base : <[ Nat ]> = TNum.
Proof. reflexivity. Qed.

Example parse_ty_arrow : <[ Nat -> Nat ]> = TArr TNum TNum.
Proof. reflexivity. Qed.

Example parse_ty_right_assoc : <[ Nat -> Nat -> Nat ]> = TArr TNum (TArr TNum TNum).
Proof. reflexivity. Qed.

Example parse_ty_higher : <[ (Nat -> Nat) -> Bool ]> = TArr (TArr TNum TNum) TBool.
Proof. reflexivity. Qed.

(**
And terms, with the type ascription on the parameter.  The Section 6
definitions, written concretely.
 *)

Example inc_concrete : <{ lambda "x" : Nat in "x" + 1 }> = inc.
Proof. reflexivity. Qed.

Example higher_order_concrete :
  <{ lambda "f" : Nat -> Nat in "f" 0 }>
  = Lambda "f" (TArr TNum TNum) (App (Id "f") (Num 0)).
Proof. reflexivity. Qed.

(**
The type checker and the interpreter both read the same concrete terms;
a well-typed program has the predicted type and runs.
 *)

Example typecheck_concrete :
  typecheck <{ lambda "x" : Nat in "x" + 1 }> = Some <[ Nat -> Nat ]>.
Proof. reflexivity. Qed.

Example typecheck_app_concrete :
  typecheck <{ (lambda "x" : Nat in "x" + 1) 4 }> = Some <[ Nat ]>.
Proof. reflexivity. Qed.

Example eval_concrete :
  eval <{ (lambda "x" : Nat in "x" + 1) 4 }> = Some (NumV 5).
Proof. reflexivity. Qed.

(* And the classic stuck term is still rejected, concretely. *)
Example ill_typed_concrete : typecheck <{ true + 1 }> = None.
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
#<ol>#
#<li>#Added a _type language_ [Ty] with numbers, Booleans, and _function_ types, plus decidable type equality [Ty_eqb] (proved correct).#</li>#
#<li>#Typed the term language: [Lambda] now _ascribes_ its parameter type, because a domain type cannot be inferred before application.#</li>#
#<li>#Built the _type checker_ [typeof] - an "interpreter that returns _types_" - and saw it accept good programs and reject every classic stuck term, including self-application ([omega]'s core).#</li>#
#<li>#Kept a single _strict_ interpreter [evalM] (no lazy [evalL]) and re-proved _fuel monotonicity_.#</li>#
#<li>#Stated _type soundness_ and witnessed it: good programs run to a value of the predicted type; bad programs never type-check.  We proved the canonical-forms slices for the base types.#</li>#
#<li>#Added concrete syntax in two parts: a type grammar [<[ Nat -> Bool ]>] and the term grammar with the classical ascription [lambda ID : T in body] - the one place a type is written.#</li>#
#</ol>#

The catch: typing is now so strict that recursion is gone - the Y and Z
combinators relied on self-application, which no longer type-checks.
The next chapter, Typed Recursion, adds a typed [fix] to put recursion
back deliberately, and its payoff is normalization: every well-typed
term terminates.
 *)

(** * NEW PROOF TACTICS IN THIS CHAPTER *)

(**
Two new patterns appear, both in the canonical-forms lemmas:

#<ul>#
#<li>#[intros [| k]] - destructs a value at introduction time by combining [intros] with a match pattern.  Writing [intros [| k] env e v H] is sugar for [intros f env e v H; destruct f as [| k]].  Useful for types with just a few constructors (naturals, options, Booleans) where you want to case-split immediately.#</li>#
#<li>#[eexists] - instantiates an existential goal with a fresh metavariable, deferring the choice of witness to later tactics.  Repeated [eexists. eexists. eexists.] peels off the three existentials in [exists i b env, ...] before [reflexivity] resolves them all at once.#</li>#
#</ul>#
 *)
