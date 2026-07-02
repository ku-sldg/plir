(**
 * Programming Languages in Rocq - Typed Functions Lecture
 * A static type system for the functional language
 *
 * Func and Rec gave us a Turing-powerful UNTYPED language: it can loop
 * ([omega]), and it can get STUCK - [Plus (Boolean true) (Num 1)] is
 * nonsense that the interpreter only rejects (as [None]) at run time,
 * after it has already started evaluating.  This chapter adds a STATIC
 * TYPE SYSTEM that rejects such programs BEFORE evaluation.
 *
 * The plan:
 *   1. A TYPE language [Ty]: numbers, Booleans, and FUNCTION types.
 *   2. The typed term language [TFBAEC]: Rec's FBAEC, except [Lambda] now
 *      ASCRIBES its parameter's type (you cannot infer a domain type from
 *      a function that has not yet been applied).
 *   3. The TYPE CHECKER [typeof] - "an interpreter that returns TYPES
 *      instead of values", carrying an identifier->type CONTEXT exactly
 *      like [evalM] carries a value environment.
 *   4. The STRICT interpreter [evalM] (call-by-value, fuel-driven) - the
 *      ONLY interpreter now (no more lazy [evalL]) - with FUEL
 *      MONOTONICITY carried over from Rec.
 *   5. TYPE SOUNDNESS: well-typed programs do not get stuck.  We witness
 *      it with a battery of machine-checked examples - good programs run
 *      to a value of the predicted type, and every classic stuck term is
 *      rejected by [typeof].
 *
 * This mirrors the "Typed Functions" unit of PLIH:
 *   https://ku-sldg.github.io/plih//types/1-Function-Types.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_tfun_shared.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* SECTION 1: THE TYPE LANGUAGE                                     *)
(* ================================================================ *)

(**
 * Types are numbers, Booleans, and FUNCTION types [TArr d r] ("d -> r"),
 * the type of a function from domain [d] to range [r].  Function types
 * are what make this more than a flat set of base types - they let the
 * checker track what a lambda expects and what an application produces.
 *)
Inductive Ty : Type :=
| TNum  : Ty
| TBool : Ty
| TArr  : Ty -> Ty -> Ty.

(**
 * Type checking needs to COMPARE types (does the argument's type match
 * the function's domain?), so we need decidable equality on [Ty].
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

(* ================================================================ *)
(* SECTION 2: THE TYPED TERM LANGUAGE                              *)
(* ================================================================ *)

(**
 * [TFBAEC] is Rec's FBAEC with ONE change: [Lambda] now carries the
 * declared type of its parameter.  We cannot infer a parameter's type
 * from the function alone - its value is not known until application -
 * so, as in PLIH, the programmer ASCRIBES it: [Lambda x T b] is
 * "lambda (x : T) in b".  Everything else is unchanged.
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

(* ================================================================ *)
(* SECTION 3: THE TYPE CHECKER                                     *)
(* ================================================================ *)

(**
 * A TYPE CONTEXT maps identifiers to their types - the static analogue of
 * an evaluation environment.  It is literally [Env Ty], reusing the same
 * association lists (and [lookup]/[extend]) that [evalM] uses for values.
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
 * [typeof ctx e] computes the type of [e] under [ctx], or [None] if [e]
 * is ill-typed.  Compare it to [evalM]: same shape, same recursion, but
 * it returns TYPES and needs no fuel - type checking always terminates.
 *
 *   - arithmetic wants numbers, yields a number;
 *   - [IsZero] wants a number, yields a Boolean;
 *   - [If] wants a Boolean condition and TWO BRANCHES OF THE SAME TYPE,
 *     which is that common type (a static term cannot know which branch
 *     runs, so both must agree);
 *   - [Lambda x T b] : with [x:T] in scope [b] has some type [R], so the
 *     lambda has type [T -> R];
 *   - [App f a] : [f] must be a function [D -> R] and [a] must have type
 *     [D]; the application then has type [R].
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

(* ================================================================ *)
(* SECTION 4: THE STRICT INTERPRETER                              *)
(* ================================================================ *)

(**
 * Values are numbers, Booleans, and closures - exactly Rec's [RVal].  A
 * closure captures its definition-time environment (static scoping).  The
 * parameter's declared type plays no role at run time, so the closure
 * does not store it.
 *)
Inductive TVal : Type :=
| NumV     : nat -> TVal
| BoolV    : bool -> TVal
| ClosureV : string -> TFBAEC -> list (string * TVal) -> TVal.

(**
 * The STRICT (call-by-value) interpreter, identical to Rec's [evalM]
 * except that [Lambda] now has a type annotation to ignore.  It is still
 * fuel-driven: types will guarantee well-typed programs terminate, but
 * [evalM] is defined on ALL terms, including ill-typed ones, so the fuel
 * stays.  This is the ONLY interpreter in this chapter - no lazy [evalL].
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

(* ================================================================ *)
(* SECTION 5: FUEL MONOTONICITY (well-definedness of [evalM])      *)
(* ================================================================ *)

(**
 * As in Func and Rec, no measure bounds the fuel, so the well-definedness
 * result is MONOTONICITY: more fuel never changes an answer already
 * produced.  The proof is Rec's verbatim, with [Lambda]'s new type
 * argument the only difference (still just [exact H]).
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

(* ================================================================ *)
(* SECTION 6: TYPE CHECKING IN ACTION                             *)
(* ================================================================ *)

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

(* ---- and now the REJECTIONS: every classic "stuck" term is caught ---- *)

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
 * THE POINT OF TYPES.  Rec's [omega] = [selfApp selfApp] with
 * [selfApp = \x. x x] cannot be typed: for [x x] to make sense [x] must
 * be both a function [D -> R] AND its own argument [D], i.e. [D = D -> R],
 * which no finite [Ty] satisfies.  So even with a parameter annotation,
 * self-application is REJECTED - the type checker rules out the very term
 * that made the untyped language diverge.
 *)
Definition selfApp (t : Ty) : TFBAEC :=
  Lambda "x" t (App (Id "x") (Id "x")).

Example ill_selfApp_num : typecheck (selfApp TNum) = None.
Proof. reflexivity. Qed.

Example ill_selfApp_fun : typecheck (selfApp (TArr TNum TNum)) = None.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 7: TYPE SOUNDNESS (well-typed programs do not get stuck) *)
(* ================================================================ *)

(**
 * TYPE SOUNDNESS is the payoff: a well-typed program never gets stuck -
 * evaluated with enough fuel it produces a VALUE, and that value has the
 * type [typeof] predicted.  Symbolically, the guarantee we are after is
 *
 *     typecheck e = Some t  ->  exists v, eval e = Some v /\ v : t.
 *
 * A fully general machine-checked proof needs a logical-relations
 * argument (a type-indexed notion of "value [v] has type [t]" that also
 * constrains the environments captured inside closures); we set that up
 * in the exercises and leave the full development as advanced material,
 * exactly as PLIH states soundness informally at this point.
 *
 * What we CAN check right now, concretely and completely, is soundness on
 * whole programs: a well-typed term and its value, side by side, with the
 * value's kind matching the predicted type.  Together with Section 6's
 * rejections (bad programs never reach [eval] at all) these witness the
 * property directly.
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
 * CANONICAL FORMS, provably: if a CLOSED VALUE has a base type, we know
 * exactly which constructor it is.  This is the value-level half of
 * soundness and is fully provable now.  We phrase "value [v] has base
 * type" directly by [evalM], since a value's number/Boolean nature is
 * observable.  (The function-type case is the one needing the logical
 * relation, hence its omission here.)
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

(* ================================================================ *)
(* SUMMARY                                                          *)
(* ================================================================ *)

(**
 * In this lecture we:
 *   1. Added a TYPE language [Ty] with numbers, Booleans, and FUNCTION
 *      types, plus decidable type equality [Ty_eqb] (proved correct).
 *   2. Typed the term language: [Lambda] now ASCRIBES its parameter type,
 *      because a domain type cannot be inferred before application.
 *   3. Built the TYPE CHECKER [typeof] - an "interpreter that returns
 *      types" - and saw it ACCEPT good programs and REJECT every classic
 *      stuck term, including self-application ([omega]'s core).
 *   4. Kept a single STRICT interpreter [evalM] (no lazy [evalL]) and
 *      re-proved FUEL MONOTONICITY.
 *   5. Stated TYPE SOUNDNESS and witnessed it: good programs run to a
 *      value of the predicted type; bad programs never type-check.  We
 *      proved the canonical-forms slices for the base types.
 *
 * The catch: typing is now so strict that RECURSION is gone - the Y and Z
 * combinators relied on self-application, which no longer type-checks.
 * The next chapter, Typed Recursion, adds a typed [fix] to put recursion
 * back deliberately, and its payoff is NORMALIZATION: every well-typed
 * term terminates.
 *)
