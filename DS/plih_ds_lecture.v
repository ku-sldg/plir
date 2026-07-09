(** * Programming Languages in Rocq - TADS: Typed Algebraic Data Structures *)

(**
The typed-recursion chapter (TRec) gave us a safe, expressive language:
numbers, Booleans, first-class functions, and well-typed [Fix] for
general recursion.  But values are flat: the only compound value is a
closure.

This chapter adds _structure_ to values.  We extend TRec with three
new type formers and the terms that introduce and eliminate them:

#<ol>#
#<li>#_Products_ [(TProd A B)]: pair two values together; eliminate with [Fst] and [Snd].#</li>#
#<li>#_Sums_ [(TSum A B)]: inject a value on the left or right; eliminate with [SCase].#</li>#
#<li>#_Lists_ [(TList A)]: a typed homogeneous list; introduced by [Nil] and [Cons], eliminated by [Car], [Cdr], and [IsNil].#</li>#
#</ol>#

Together these three are the _algebraic_ types: every structured data
type in typed functional programming is built from products, sums, and
recursive occurrences.  We call the resulting language TADS.

The central insight of this chapter is that lists _are_ sums of products.
The evaluator makes this concrete: list values are literally sum and
product values in the representation.  [NilV] and [ConsV] do not
exist as separate constructors; [Nil] evaluates to [InLV UnitV] and
[Cons h t] evaluates to [InRV (PairV h t)].

This mirrors the "Algebraic Data Types" discussion in PLIH:
  https://ku-sldg.github.io/plih//
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_ds_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: EXTENDING THE TYPE LANGUAGE *)

(**
TRec's types are [TNum], [TBool], and [TArr d r].  We keep those three
and add:
  - [TUnit]: the _unit_ type, a type with exactly one value ([UnitV]).
    Unit serves as the element type of [Nil]: an empty list carries no
    data, represented as a left-injected unit.
  - [TProd A B]: the _product_ type "A and B";
  - [TSum  A B]: the _sum_     type "A or B";
  - [TList A]:   the _list_    type "a sequence of A".

These are the typed counterparts of Rocq's [unit], [prod], [sum], and [list].
 *)

Inductive Ty : Type :=
| TNum  : Ty
| TBool : Ty
| TArr  : Ty -> Ty -> Ty
| TUnit : Ty              (* unit type - the type of UnitV and of Nil's payload *)
| TProd : Ty -> Ty -> Ty  (* A * B  - product *)
| TSum  : Ty -> Ty -> Ty  (* A + B  - sum     *)
| TList : Ty -> Ty.       (* List A - list    *)

(**
Decidable equality on [Ty] is essential for the type checker.  We extend
TRec's three-case [Ty_eqb] with four new cases, one for each new former.
 *)

Fixpoint Ty_eqb (a b : Ty) : bool :=
  match a, b with
  | TNum,  TNum  => true
  | TBool, TBool => true
  | TArr  d1 r1, TArr  d2 r2 => andb (Ty_eqb d1 d2) (Ty_eqb r1 r2)
  | TUnit, TUnit => true
  | TProd a1 b1, TProd a2 b2 => andb (Ty_eqb a1 a2) (Ty_eqb b1 b2)
  | TSum  a1 b1, TSum  a2 b2 => andb (Ty_eqb a1 a2) (Ty_eqb b1 b2)
  | TList t1,    TList t2    => Ty_eqb t1 t2
  | _, _ => false
  end.

(**
[Ty_eqb] is _reflexive_: every type equals itself.
 *)

Lemma Ty_eqb_refl : forall t, Ty_eqb t t = true.
Proof.
  intros t.
  induction t as [| | d IHd r IHr | | a1 IH1 b1 IH2 | a1 IH1 b1 IH2 | t IH];
    simpl; try reflexivity.
  - rewrite IHd, IHr. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
Qed.

(**
If [Ty_eqb a b = true] then [a = b].
 *)

Lemma Ty_eqb_eq : forall a b, Ty_eqb a b = true -> a = b.
Proof.
  induction a as [| | d1 IHd r1 IHr | | a1 IH1 b1 IH2 | a1 IH1 b1 IH2 | t IH];
    intros b H; destruct b as [| | d2 r2 | | a2 b2 | a2 b2 | t2];
    simpl in H; try discriminate; try reflexivity.
  - apply andb_true_iff in H. destruct H as [Hd Hr].
    rewrite (IHd d2 Hd), (IHr r2 Hr). reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    rewrite (IH1 a2 H1), (IH2 b2 H2). reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    rewrite (IH1 a2 H1), (IH2 b2 H2). reflexivity.
  - rewrite (IH t2 H). reflexivity.
Qed.

(**
The biconditional: [Ty_eqb a b = true] iff [a = b].
 *)

Lemma Ty_eqb_true_iff : forall a b, Ty_eqb a b = true <-> a = b.
Proof.
  intros a b. split; [apply Ty_eqb_eq | intros H; subst; apply Ty_eqb_refl].
Qed.

(** * SECTION 2: THE TERM LANGUAGE *)

(**
[TADS] is TRec's [TFBAEC] extended with a unit term and with product,
sum, and list terms.

_Unit_:
  - [Unit]: the unique term of type [TUnit].

_Product terms_:
  - [Pair e1 e2]: construct a pair;
  - [Fst e]:      eliminate a pair (first projection);
  - [Snd e]:      eliminate a pair (second projection).

_Sum terms_:
  - [InL T e]:          inject [e] on the left at type [T];
  - [InR T e]:          inject [e] on the right at type [T];
  - [SCase e x e1 y e2]: eliminate a sum: if left, bind [x] and run [e1];
                          if right, bind [y] and run [e2].

_List terms_:
  - [Nil T]:     the empty list of element type [T];
  - [Cons e1 e2]: prepend an element to a list;
  - [Car e]:     head of a list;
  - [Cdr e]:     tail of a list;
  - [IsNil e]:   test whether a list is empty.

The type annotations on [InL], [InR], and [Nil] are mandatory: without
them the type checker cannot determine the full sum or list type from the
term alone.
 *)

Inductive TADS : Type :=
(* from TRec *)
| Num     : nat -> TADS
| Plus    : TADS -> TADS -> TADS
| Minus   : TADS -> TADS -> TADS
| Mult    : TADS -> TADS -> TADS
| Boolean : bool -> TADS
| IsZero  : TADS -> TADS
| If      : TADS -> TADS -> TADS -> TADS
| Bind    : string -> TADS -> TADS -> TADS
| Lambda  : string -> Ty -> TADS -> TADS
| App     : TADS -> TADS -> TADS
| Fix     : TADS -> TADS
| Id      : string -> TADS
(* unit *)
| Unit    : TADS
(* products *)
| Pair    : TADS -> TADS -> TADS
| Fst     : TADS -> TADS
| Snd     : TADS -> TADS
(* sums *)
| InL     : Ty -> TADS -> TADS
| InR     : Ty -> TADS -> TADS
| SCase   : TADS -> string -> TADS -> string -> TADS -> TADS
(* lists *)
| Nil     : Ty -> TADS
| Cons    : TADS -> TADS -> TADS
| Car     : TADS -> TADS
| Cdr     : TADS -> TADS
| IsNil   : TADS -> TADS.

(**
Capture-naive substitution: [subst i v e] replaces free occurrences of
identifier [i] with term [v] in [e].  Binders ([Bind] and [Lambda]) that
rebind [i] shadow the substitution in their body; [SCase] binds [x] in
[e1] and [y] in [e2].  [Unit] is a value; it substitutes to itself.
 *)

Fixpoint subst (i : string) (v : TADS) (e : TADS) : TADS :=
  match e with
  | Num n      => Num n
  | Plus  l r  => Plus  (subst i v l) (subst i v r)
  | Minus l r  => Minus (subst i v l) (subst i v r)
  | Mult  l r  => Mult  (subst i v l) (subst i v r)
  | Boolean b  => Boolean b
  | IsZero e0  => IsZero (subst i v e0)
  | If c t f   => If (subst i v c) (subst i v t) (subst i v f)
  | Bind i' val b =>
      if String.eqb i i'
      then Bind i' (subst i v val) b
      else Bind i' (subst i v val) (subst i v b)
  | Lambda i' t b =>
      if String.eqb i i' then Lambda i' t b else Lambda i' t (subst i v b)
  | App f a    => App (subst i v f) (subst i v a)
  | Fix f      => Fix (subst i v f)
  | Id i'      => if String.eqb i i' then v else Id i'
  | Unit       => Unit
  | Pair e1 e2 => Pair (subst i v e1) (subst i v e2)
  | Fst e0     => Fst (subst i v e0)
  | Snd e0     => Snd (subst i v e0)
  | InL T e0   => InL T (subst i v e0)
  | InR T e0   => InR T (subst i v e0)
  | SCase e0 x e1 y e2 =>
      let e0' := subst i v e0 in
      let e1' := if String.eqb i x then e1 else subst i v e1 in
      let e2' := if String.eqb i y then e2 else subst i v e2 in
      SCase e0' x e1' y e2'
  | Nil T      => Nil T
  | Cons e1 e2 => Cons (subst i v e1) (subst i v e2)
  | Car e0     => Car (subst i v e0)
  | Cdr e0     => Cdr (subst i v e0)
  | IsNil e0   => IsNil (subst i v e0)
  end.

(** * SECTION 3: THE TYPE CHECKER *)

(**
The type context maps identifiers to types.
 *)

Definition Ctx := Env Ty.

(**
Helper for numeric binary operations: both operands must be [TNum],
yielding [TNum].
 *)

Definition tnumBinop (a b : option Ty) : option Ty :=
  match a, b with
  | Some TNum, Some TNum => Some TNum
  | _, _ => None
  end.

(**
[typeof ctx e] infers the type of [e] in context [ctx], returning
[None] if [e] is ill-typed.  The TRec cases are unchanged.

_Unit_: [Unit] always has type [TUnit].

_Products_: [Pair e1 e2] infers [TProd A B] from its components.
[Fst] and [Snd] require a [TProd] scrutinee and return the left or
right component type.

_Sums_: [InL T e] and [InR T e] carry the full sum type [T] as a
mandatory annotation.  The checker verifies [e] matches the
corresponding component of [T], then returns [T].  [SCase] requires
the scrutinee to have a [TSum A B] type, extends the context with the
binder in each branch, and insists both branches return the same type.

_Lists_: [Nil T] always has type [TList T].  [Cons e1 e2] requires
[e1 : A] and [e2 : TList A] (enforced with [Ty_eqb]).  [Car] and
[Cdr] require a [TList A] scrutinee; [IsNil] requires any [TList]
scrutinee and returns [TBool].
 *)

Fixpoint typeof (ctx : Ctx) (e : TADS) : option Ty :=
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
  | Fix f =>
      match typeof ctx f with
      | Some (TArr d r) => if Ty_eqb d r then Some r else None
      | _ => None
      end
  | Id x => lookup x ctx
  | Unit => Some TUnit
  | Pair e1 e2 =>
      match typeof ctx e1, typeof ctx e2 with
      | Some t1, Some t2 => Some (TProd t1 t2)
      | _, _ => None
      end
  | Fst e0 =>
      match typeof ctx e0 with
      | Some (TProd t1 _) => Some t1
      | _ => None
      end
  | Snd e0 =>
      match typeof ctx e0 with
      | Some (TProd _ t2) => Some t2
      | _ => None
      end
  | InL T e0 =>
      match T with
      | TSum t1 _ =>
          match typeof ctx e0 with
          | Some te => if Ty_eqb te t1 then Some T else None
          | _ => None
          end
      | _ => None
      end
  | InR T e0 =>
      match T with
      | TSum _ t2 =>
          match typeof ctx e0 with
          | Some te => if Ty_eqb te t2 then Some T else None
          | _ => None
          end
      | _ => None
      end
  | SCase e0 x e1 y e2 =>
      match typeof ctx e0 with
      | Some (TSum t1 t2) =>
          match typeof (extend x t1 ctx) e1, typeof (extend y t2 ctx) e2 with
          | Some r1, Some r2 => if Ty_eqb r1 r2 then Some r1 else None
          | _, _ => None
          end
      | _ => None
      end
  | Nil T => Some (TList T)
  | Cons e1 e2 =>
      match typeof ctx e1, typeof ctx e2 with
      | Some t, Some (TList t2) => if Ty_eqb t t2 then Some (TList t) else None
      | _, _ => None
      end
  | Car e0 =>
      match typeof ctx e0 with
      | Some (TList t) => Some t
      | _ => None
      end
  | Cdr e0 =>
      match typeof ctx e0 with
      | Some (TList t) => Some (TList t)
      | _ => None
      end
  | IsNil e0 =>
      match typeof ctx e0 with
      | Some (TList _) => Some TBool
      | _ => None
      end
  end.

(**
Top-level type checking: a closed term (no free identifiers).
 *)

Definition typecheck (e : TADS) : option Ty := typeof nil e.

(** * SECTION 4: THE EVALUATOR *)

(**
List values are not a separate constructor.  The empty list is
[InLV UnitV] and a cons cell is [InRV (PairV head tail)].  This makes
the algebraic structure explicit in the representation: a list _is_ a
sum of unit and a product.

Values extend TRec's [TVal] with:
  - [UnitV]:       the unique unit value; also represents the empty list;
  - [PairV v1 v2]: a pair value; also the payload of a cons cell;
  - [InLV v]:      a left-injected value; the empty list is [InLV UnitV];
  - [InRV v]:      a right-injected value; [Cons h t] yields
                   [InRV (PairV h t)].

Closures still carry the parameter's type (needed by [Fix]).
 *)

Inductive TVal : Type :=
| NumV     : nat -> TVal
| BoolV    : bool -> TVal
| ClosureV : string -> Ty -> TADS -> list (string * TVal) -> TVal
| UnitV    : TVal
| PairV    : TVal -> TVal -> TVal
| InLV     : TVal -> TVal
| InRV     : TVal -> TVal.

(**
The strict (call-by-value) interpreter.  TRec's cases are unchanged
except that the type changes from [TFBAEC] to [TADS].  The new cases:

  - [Unit] returns [UnitV].
  - [Nil _] returns [InLV UnitV]: the empty list is left-injected unit.
  - [Cons e1 e2] evaluates both subterms and returns [InRV (PairV v1 v2)]:
    a non-empty list is a right-injected pair of head and tail.
  - [Car e] matches [InRV (PairV v _)] and returns the head.
  - [Cdr e] matches [InRV (PairV _ v)] and returns the tail.
  - [IsNil e] matches [InLV _] (empty) or [InRV _] (non-empty).

_List safety_: [Car] and [Cdr] on a nil list (which is [InLV UnitV],
matching [InLV _]) return [None].  The type checker prevents this in
well-typed programs, but the evaluator is defined for all terms.
 *)

Fixpoint evalM (fuel : nat) (env : Env TVal) (e : TADS) : option TVal :=
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
      | Lambda i t b => Some (ClosureV i t b env)
      | App f a =>
          match evalM k env f with
          | Some (ClosureV i _ b cenv) =>
              match evalM k env a with
              | Some a' => evalM k (extend i a' cenv) b
              | None => None
              end
          | _ => None
          end
      | Fix f =>
          match evalM k env f with
          | Some (ClosureV i t b cenv) =>
              evalM k cenv (subst i (Fix (Lambda i t b)) b)
          | _ => None
          end
      | Id x => lookup x env
      (* unit *)
      | Unit => Some UnitV
      (* products *)
      | Pair e1 e2 =>
          match evalM k env e1, evalM k env e2 with
          | Some v1, Some v2 => Some (PairV v1 v2)
          | _, _ => None
          end
      | Fst e0 =>
          match evalM k env e0 with
          | Some (PairV v1 _) => Some v1
          | _ => None
          end
      | Snd e0 =>
          match evalM k env e0 with
          | Some (PairV _ v2) => Some v2
          | _ => None
          end
      (* sums *)
      | InL _ e0 =>
          match evalM k env e0 with
          | Some v => Some (InLV v)
          | None => None
          end
      | InR _ e0 =>
          match evalM k env e0 with
          | Some v => Some (InRV v)
          | None => None
          end
      | SCase e0 x e1 y e2 =>
          match evalM k env e0 with
          | Some (InLV v) => evalM k (extend x v env) e1
          | Some (InRV v) => evalM k (extend y v env) e2
          | _ => None
          end
      (* lists - implemented as sums of products *)
      | Nil _ => Some (InLV UnitV)
      | Cons e1 e2 =>
          match evalM k env e1, evalM k env e2 with
          | Some v1, Some v2 => Some (InRV (PairV v1 v2))
          | _, _ => None
          end
      | Car e0 =>
          match evalM k env e0 with
          | Some (InRV (PairV v _)) => Some v
          | _ => None
          end
      | Cdr e0 =>
          match evalM k env e0 with
          | Some (InRV (PairV _ v)) => Some v
          | _ => None
          end
      | IsNil e0 =>
          match evalM k env e0 with
          | Some (InLV _) => Some (BoolV true)
          | Some (InRV _) => Some (BoolV false)
          | _ => None
          end
      end
  end.

(**
Top-level evaluation: a closed term with 1000 fuel units.
 *)

Definition eval (e : TADS) : option TVal := evalM 1000 nil e.

(** * SECTION 5: UNIT IN ACTION *)

(**
[Unit] is the unique term of type [TUnit].  Its value is [UnitV].  Unit
appears explicitly when you want "nothing" — it is most important as the
payload of an empty list.
 *)

Example ty_unit : typecheck Unit = Some TUnit.
Proof. reflexivity. Qed.

Example eval_unit : eval Unit = Some UnitV.
Proof. reflexivity. Qed.

(** * SECTION 6: PRODUCTS IN ACTION *)

(**
The canonical example: a pair of numbers.  [typecheck] infers the type
and [eval] computes the value.
 *)

Example ty_pair :
  typecheck (Pair (Num 1) (Num 2)) = Some (TProd TNum TNum).
Proof. reflexivity. Qed.

Example ty_fst :
  typecheck (Fst (Pair (Num 1) (Boolean true))) = Some TNum.
Proof. reflexivity. Qed.

Example run_pair :
  eval (Pair (Num 3) (Num 4)) = Some (PairV (NumV 3) (NumV 4)).
Proof. reflexivity. Qed.

Example run_fst :
  eval (Fst (Pair (Num 3) (Num 4))) = Some (NumV 3).
Proof. reflexivity. Qed.

Example run_snd :
  eval (Snd (Pair (Num 3) (Num 4))) = Some (NumV 4).
Proof. reflexivity. Qed.

(**
[swapProg] binds a pair to [p] and returns its components in reverse
order.
 *)

Definition swapProg : TADS :=
  Bind "p" (Pair (Num 1) (Num 2))
    (Pair (Snd (Id "p")) (Fst (Id "p"))).

Example ty_swap : typecheck swapProg = Some (TProd TNum TNum).
Proof. reflexivity. Qed.

Example run_swap :
  eval swapProg = Some (PairV (NumV 2) (NumV 1)).
Proof. reflexivity. Qed.

(** * SECTION 7: SUMS IN ACTION *)

(**
A safe division: if the divisor is zero, return an error flag
([InR ... (Boolean true)]); otherwise return the quotient.  The result
type is [TSum TNum TBool], encoding "number or error".

Unit could be used as the error payload — [InR (TSum TNum TUnit) Unit]
— but we keep the existing example with [Boolean true] as the error
flag to show that any type can appear in a sum.
 *)

Definition safeDiv : TADS :=
  Bind "n" (Num 10)
    (Bind "d" (Num 0)
      (If (IsZero (Id "d"))
          (InR (TSum TNum TBool) (Boolean true))
          (InL (TSum TNum TBool) (Mult (Id "n") (Id "d"))))).

Example ty_safeDiv : typecheck safeDiv = Some (TSum TNum TBool).
Proof. reflexivity. Qed.

Example run_safeDiv : eval safeDiv = Some (InRV (BoolV true)).
Proof. reflexivity. Qed.

(**
[SCase] eliminates the sum: if the left branch was taken (a number),
return it; if the right branch was taken (an error), return 0 as a
default.
 *)

Definition safeDivResult : TADS :=
  SCase safeDiv "n" (Id "n") "e" (Num 0).

Example ty_safeDivResult : typecheck safeDivResult = Some TNum.
Proof. reflexivity. Qed.

Example run_safeDivResult : eval safeDivResult = Some (NumV 0).
Proof. reflexivity. Qed.

(**
The type checker rejects a [SCase] whose branches have _different_ types:
both branches must return the same type [R].
 *)

Example ill_scase_mismatch :
  typecheck (SCase safeDiv "n" (Id "n") "e" (Boolean false)) = None.
Proof. reflexivity. Qed.

(**
The type checker also rejects [InL] applied to a non-sum type annotation.
 *)

Example ill_inl_not_sum :
  typecheck (InL TNum (Num 5)) = None.
Proof. reflexivity. Qed.

(** * SECTION 8: LISTS AS SUMS OF PRODUCTS *)

(**
The algebraic equation for lists is:

    List A = Unit + (A x List A)

A list is _either_ empty (carrying only unit) _or_ a pair of a head
element and a tail list.  This is a recursive equation; [TList A] names it.

The evaluator makes this equation concrete at the _value_ level.  List
values are literally sum and product values:

  - [Nil T] evaluates to [InLV UnitV]   -- the left branch, carrying unit.
  - [Cons e1 e2] evaluates to [InRV (PairV v1 v2)]  -- the right branch,
    carrying the head and tail as a pair.

There are no separate [NilV] or [ConsV] constructors in [TVal].
 *)

Example nil_is_inl :
  eval (Nil TNum) = Some (InLV UnitV).
Proof. reflexivity. Qed.

Example cons_is_inr_pair :
  eval (Cons (Num 1) (Nil TNum)) =
  Some (InRV (PairV (NumV 1) (InLV UnitV))).
Proof. reflexivity. Qed.

Example list_structure :
  eval (Cons (Num 1) (Cons (Num 2) (Cons (Num 3) (Nil TNum)))) =
  Some (InRV (PairV (NumV 1)
       (InRV (PairV (NumV 2)
       (InRV (PairV (NumV 3) (InLV UnitV))))))).
Proof. reflexivity. Qed.

(**
The list eliminators are just the sum/product patterns under new names:

  - [IsNil] checks whether the sum tag is left ([InLV _]) or right ([InRV _]).
  - [Car] extracts the first component of the right-branch pair.
  - [Cdr] extracts the second component of the right-branch pair.
 *)

(* IsNil checks the sum tag. *)
Example isnil_checks_tag :
  eval (IsNil (Nil TNum)) = Some (BoolV true).
Proof. reflexivity. Qed.

(**
Because list values _are_ sum values, [SCase] can eliminate them
directly.  The type checker rejects this (the scrutinee has type
[TList TNum], not [TSum _ _]), but the evaluator accepts it because the
representation is identical.
 *)

Example scase_on_list :
  eval (SCase (Cons (Num 42) (Nil TNum))
              "u" (Num 0)
              "p" (Fst (Id "p"))) =
  Some (NumV 42).
Proof. reflexivity. Qed.

(* Car is fst of the right-branch pair. *)
Example car_via_fst :
  eval (Car (Cons (Num 5) (Nil TNum))) = Some (NumV 5).
Proof. reflexivity. Qed.

(* IsNil and SCase are equivalent for the nil case. *)
Example isnil_eq_scase_nil :
  eval (IsNil (Nil TNum)) =
  eval (SCase (Nil TNum) "u" (Boolean true) "p" (Boolean false)).
Proof. reflexivity. Qed.

(**
Why does the type checker keep [TList A] as a distinct type rather than
unfolding it to [TSum TUnit (TProd A (TList A))]?  Because that unfolding
is _recursive_: [TList A] appears in its own definition.  Supporting
recursive type equations requires a separate language feature (a "mu
type" or isorecursive type).  [TList A] names the pattern without making
the recursion first-class.  At the _value_ level no such issue arises:
[InRV (PairV h t)] is already a finite tree.
 *)

(** * SECTION 9: POLYMORPHIC LISTS *)

(**
Lists are _polymorphic_: the element type is carried in [Nil T] and
inferred from the elements in [Cons].
 *)

Definition list123 : TADS :=
  Cons (Num 1) (Cons (Num 2) (Cons (Num 3) (Nil TNum))).

Example ty_list123 : typecheck list123 = Some (TList TNum).
Proof. reflexivity. Qed.

Example run_car_list123 : eval (Car list123) = Some (NumV 1).
Proof. reflexivity. Qed.

Example run_cdr_list123 :
  eval (Cdr list123) =
  Some (InRV (PairV (NumV 2) (InRV (PairV (NumV 3) (InLV UnitV))))).
Proof. reflexivity. Qed.

Example run_isnil_list123 : eval (IsNil list123) = Some (BoolV false).
Proof. reflexivity. Qed.

Example run_isnil_nil : eval (IsNil (Nil TNum)) = Some (BoolV true).
Proof. reflexivity. Qed.

(**
The type checker catches [Car] applied to a non-list.
 *)

Example ill_car_num : typecheck (Car (Num 5)) = None.
Proof. reflexivity. Qed.

Definition boolList : TADS :=
  Cons (Boolean true) (Cons (Boolean false) (Nil TBool)).

Example ty_boolList : typecheck boolList = Some (TList TBool).
Proof. reflexivity. Qed.

(**
Every element type yields a well-typed [Nil].
 *)

Example ty_nil_num  : typecheck (Nil TNum)  = Some (TList TNum).
Proof. reflexivity. Qed.

Example ty_nil_bool : typecheck (Nil TBool) = Some (TList TBool).
Proof. reflexivity. Qed.

Example ty_nil_fun :
  typecheck (Nil (TArr TNum TNum)) = Some (TList (TArr TNum TNum)).
Proof. reflexivity. Qed.

(**
The type checker rejects [Cons] with a mismatched element type.
 *)

Example ill_cons_mismatch :
  typecheck (Cons (Num 1) (Nil TBool)) = None.
Proof. reflexivity. Qed.

(** * SECTION 10: RECURSIVE LIST OPERATIONS *)

(**
[sumListGen] is the _generator_ for a recursive list summation.  Its
parameter [g] is "the recursive call"; [Fix] ties the knot.
 *)

Definition sumListGen : TADS :=
  Lambda "g" (TArr (TList TNum) TNum)
    (Lambda "xs" (TList TNum)
      (If (IsNil (Id "xs"))
          (Num 0)
          (Plus (Car (Id "xs")) (App (Id "g") (Cdr (Id "xs")))))).

Definition sumList : TADS := Fix sumListGen.

Example ty_sumList :
  typecheck sumList = Some (TArr (TList TNum) TNum).
Proof. reflexivity. Qed.

Example run_sumList :
  eval (App sumList list123) = Some (NumV 6).
Proof. reflexivity. Qed.

(**
[lengthGen] counts the elements of a list of numbers.
 *)

Definition lengthGen : TADS :=
  Lambda "g" (TArr (TList TNum) TNum)
    (Lambda "xs" (TList TNum)
      (If (IsNil (Id "xs"))
          (Num 0)
          (Plus (Num 1) (App (Id "g") (Cdr (Id "xs")))))).

Definition lengthList : TADS := Fix lengthGen.

Example ty_lengthList :
  typecheck lengthList = Some (TArr (TList TNum) TNum).
Proof. reflexivity. Qed.

Example run_lengthList :
  eval (App lengthList list123) = Some (NumV 3).
Proof. reflexivity. Qed.

(** * SECTION 11: FUEL MONOTONICITY *)

(**
More fuel never changes an answer: if [evalM f1 env e = Some v] and
[f1 <= f2] then [evalM f2 env e = Some v].  The proof follows TRec's
pattern, with additional cases for the new constructors.

The [TVal] inductive now has seven constructors:
    [NumV | BoolV | ClosureV | UnitV | PairV | InLV | InRV]

The full destructor pattern is:
    [[n|b|s t bd ce| |p1 p2|iv|iv2]|]

([UnitV] is nullary -- the empty slot between [ClosureV] and [PairV].)

For [Car]/[Cdr], after destructing [evalM k env e] we need the result
to be [InRV (PairV _ _)]: first [destruct val] leaves only [InRV iv],
then [destruct iv] leaves only [PairV p1' p2'].

For [IsNil], after destructing [evalM k env e], [InLV iv] and [InRV iv2]
are the surviving cases ([try discriminate] kills the rest).
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
      destruct (evalM k env e1) as [[a | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b2 | s2 t2 bd2 ce2 | | p12 p22 | iv3 | iv4] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Minus *)
      destruct (evalM k env e1) as [[a | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b2 | s2 t2 bd2 ce2 | | p12 p22 | iv3 | iv4] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Mult *)
      destruct (evalM k env e1) as [[a | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:El; try discriminate.
      destruct (evalM k env e2) as [[b0 | b2 | s2 t2 bd2 ce2 | | p12 p22 | iv3 | iv4] |] eqn:Er; try discriminate.
      rewrite (IH k2 env e1 (NumV a) ltac:(lia) El).
      rewrite (IH k2 env e2 (NumV b0) ltac:(lia) Er). exact H.
    + (* Boolean *) exact H.
    + (* IsZero *)
      destruct (evalM k env e) as [[n | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:E0; try discriminate.
      rewrite (IH k2 env e (NumV n) ltac:(lia) E0). exact H.
    + (* If *)
      destruct (evalM k env e1) as [[a | bb | s t bd ce | | p1 p2 | iv | iv2] |] eqn:Ec; try discriminate.
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
      destruct (evalM k env e1) as [[a | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:Ef; try discriminate.
      destruct (evalM k env e2) as [a' |] eqn:Ea; try discriminate.
      rewrite (IH k2 env e1 (ClosureV s t bd ce) ltac:(lia) Ef).
      rewrite (IH k2 env e2 a' ltac:(lia) Ea).
      apply (IH k2 (extend s a' ce) bd v). lia. exact H.
    + (* Fix *)
      destruct (evalM k env e) as [[a | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:Ef; try discriminate.
      rewrite (IH k2 env e (ClosureV s t bd ce) ltac:(lia) Ef).
      apply (IH k2 ce (subst s (Fix (Lambda s t bd)) bd) v). lia. exact H.
    + (* Id *) exact H.
    + (* Unit *) exact H.
    + (* Pair *)
      destruct (evalM k env e1) as [v1 |] eqn:E1; try discriminate.
      destruct (evalM k env e2) as [v2 |] eqn:E2; try discriminate.
      rewrite (IH k2 env e1 v1 ltac:(lia) E1).
      rewrite (IH k2 env e2 v2 ltac:(lia) E2). exact H.
    + (* Fst *)
      destruct (evalM k env e) as [[n | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:Ee; try discriminate.
      rewrite (IH k2 env e (PairV p1 p2) ltac:(lia) Ee). simpl. exact H.
    + (* Snd *)
      destruct (evalM k env e) as [[n | b | s t bd ce | | p1 p2 | iv | iv2] |] eqn:Ee; try discriminate.
      rewrite (IH k2 env e (PairV p1 p2) ltac:(lia) Ee). simpl. exact H.
    + (* InL *)
      destruct (evalM k env e) as [v0 |] eqn:Ee; try discriminate.
      rewrite (IH k2 env e v0 ltac:(lia) Ee). simpl. exact H.
    + (* InR *)
      destruct (evalM k env e) as [v0 |] eqn:Ee; try discriminate.
      rewrite (IH k2 env e v0 ltac:(lia) Ee). simpl. exact H.
    + (* SCase *)
      destruct (evalM k env e1) as [[n | b | s' ty' bd' ce' | | p1 p2 | iv | iv2] |] eqn:Ee;
        try discriminate.
      * (* InLV iv *)
        rewrite (IH k2 env e1 (InLV iv) ltac:(lia) Ee). simpl.
        apply (IH k2 (extend s iv env) e2 v). lia. exact H.
      * (* InRV iv2 *)
        rewrite (IH k2 env e1 (InRV iv2) ltac:(lia) Ee). simpl.
        apply (IH k2 (extend s0 iv2 env) e3 v). lia. exact H.
    + (* Nil - returns InLV UnitV directly, no fuel used for subterms *)
      exact H.
    + (* Cons *)
      destruct (evalM k env e1) as [v1 |] eqn:E1; try discriminate.
      destruct (evalM k env e2) as [v2 |] eqn:E2; try discriminate.
      rewrite (IH k2 env e1 v1 ltac:(lia) E1).
      rewrite (IH k2 env e2 v2 ltac:(lia) E2). exact H.
    + (* Car - result is InRV (PairV _ _) *)
      destruct (evalM k env e) as [val |] eqn:Ee; try discriminate.
      (* only InRV iv2 survives after discriminate *)
      destruct val as [n | b | s t bd ce | | p1 p2 | iv | iv2]; try discriminate.
      (* rewrite the goal using IH before destructing iv2 *)
      rewrite (IH k2 env e (InRV iv2) ltac:(lia) Ee).
      (* only PairV survives inside InRV *)
      destruct iv2 as [n' | b' | s' t' bd' ce' | | p1' p2' | iv' | iv2']; try discriminate.
      simpl. exact H.
    + (* Cdr - result is InRV (PairV _ _) *)
      destruct (evalM k env e) as [val |] eqn:Ee; try discriminate.
      (* only InRV iv2 survives after discriminate *)
      destruct val as [n | b | s t bd ce | | p1 p2 | iv | iv2]; try discriminate.
      (* rewrite the goal using IH before destructing iv2 *)
      rewrite (IH k2 env e (InRV iv2) ltac:(lia) Ee).
      (* only PairV survives inside InRV *)
      destruct iv2 as [n' | b' | s' t' bd' ce' | | p1' p2' | iv' | iv2']; try discriminate.
      simpl. exact H.
    + (* IsNil - InLV _ gives true, InRV _ gives false *)
      destruct (evalM k env e) as [val |] eqn:Ee; try discriminate.
      destruct val as [n | b | s t bd ce | | p1 p2 | iv | iv2]; try discriminate.
      * (* InLV iv *)
        rewrite (IH k2 env e (InLV iv) ltac:(lia) Ee). simpl. exact H.
      * (* InRV iv2 *)
        rewrite (IH k2 env e (InRV iv2) ltac:(lia) Ee). simpl. exact H.
Qed.

(** * SECTION 12: CONCRETE SYNTAX *)

(**
We introduce a concrete syntax for TADS.  Types are written between
[<[ ... ]>] and terms between [<{ ... }>].  Both inherit the grammar
from TRec and extend it with the new forms.
 *)

Coercion Num : nat >-> TADS.
Coercion Id  : string >-> TADS.

(**
_The type grammar._  [Nat], [Bool], and [unit] are base types;
[->] is the right-associative function arrow; [*] binds tighter than
[+] which binds tighter than [->].  [List T] introduces list types.
 *)

Declare Custom Entry ty.
Declare Custom Entry tads.
Declare Scope tads_scope.
Delimit Scope tads_scope with tads.

Notation "<[ t ]>" := t (t custom ty at level 50) : tads_scope.
Notation "( t )" := t (in custom ty, t at level 50) : tads_scope.
Notation "'Nat'"    := TNum  (in custom ty at level 0) : tads_scope.
Notation "'Bool'"   := TBool (in custom ty at level 0) : tads_scope.
Notation "'unit'"   := TUnit (in custom ty at level 0) : tads_scope.
Notation "d -> r"   := (TArr d r)  (in custom ty at level 50, right associativity) : tads_scope.
Notation "A * B"    := (TProd A B) (in custom ty at level 40, left associativity) : tads_scope.
Notation "A + B"    := (TSum A B)  (in custom ty at level 45, left associativity) : tads_scope.
Notation "'List' T" := (TList T)   (in custom ty at level 5,  T custom ty at level 0) : tads_scope.

(**
_The term grammar._  Function application is juxtaposition at level 1.
New forms for unit, products, sums, and lists are at level 75, below
[if]/[bind]/[lambda] but above application.
 *)

Notation "<{ e }>" := e (e custom tads at level 99) : tads_scope.
Notation "( x )"   := x (in custom tads, x at level 99) : tads_scope.
Notation "x"       := x (in custom tads at level 0, x constr at level 0) : tads_scope.

Notation "f x"  := (App f x)  (in custom tads at level 1, left associativity) : tads_scope.
Notation "'fix' f" := (Fix f) (in custom tads at level 75, right associativity) : tads_scope.
Notation "'iszero' x" := (IsZero x) (in custom tads at level 75, right associativity) : tads_scope.
Notation "x * y" := (Mult x y)  (in custom tads at level 40, left associativity) : tads_scope.
Notation "x + y" := (Plus x y)  (in custom tads at level 50, left associativity) : tads_scope.
Notation "x - y" := (Minus x y) (in custom tads at level 50, left associativity) : tads_scope.
Notation "'true'"  := (Boolean true)  (in custom tads at level 0) : tads_scope.
Notation "'false'" := (Boolean false) (in custom tads at level 0) : tads_scope.
Notation "'if' c 'then' t 'else' f" := (If c t f)
  (in custom tads at level 89, c custom tads at level 99,
   t custom tads at level 99, f custom tads at level 99) : tads_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom tads at level 89, v constr at level 0,
   e1 custom tads at level 99, e2 custom tads at level 99) : tads_scope.
Notation "'lambda' v ':' T 'in' e" := (Lambda v T e)
  (in custom tads at level 90, v constr at level 0,
   T custom ty at level 50, e custom tads at level 99) : tads_scope.
(* unit form *)
Notation "'()'" := Unit (in custom tads at level 0) : tads_scope.
(* product forms *)
Notation "'fst' e" := (Fst e)
  (in custom tads at level 75, e custom tads at level 74) : tads_scope.
Notation "'snd' e" := (Snd e)
  (in custom tads at level 75, e custom tads at level 74) : tads_scope.
(* sum forms *)
Notation "'inl' e 'as' T" := (InL T e)
  (in custom tads at level 75,
   e custom tads at level 74, T custom ty at level 50) : tads_scope.
Notation "'inr' e 'as' T" := (InR T e)
  (in custom tads at level 75,
   e custom tads at level 74, T custom ty at level 50) : tads_scope.
Notation "'case' e 'of' 'inl' x '=>' e1 'else' 'inr' y '=>' e2" :=
  (SCase e x e1 y e2)
  (in custom tads at level 89,
   e  custom tads at level 99,
   x  constr  at level 0,
   e1 custom tads at level 99,
   y  constr  at level 0,
   e2 custom tads at level 99) : tads_scope.
(* list forms - [nil T] takes a type argument in the ty grammar *)
Notation "'nil' T" := (Nil T)
  (in custom tads at level 75, T custom ty at level 0) : tads_scope.
Notation "'car' e" := (Car e)
  (in custom tads at level 75, e custom tads at level 74) : tads_scope.
Notation "'cdr' e" := (Cdr e)
  (in custom tads at level 75, e custom tads at level 74) : tads_scope.
Notation "'isnil' e" := (IsNil e)
  (in custom tads at level 75, e custom tads at level 74) : tads_scope.

Open Scope tads_scope.

(**
Type examples: the grammar parses unit, product, sum, and function types.
 *)

Example parse_ty_unit : <[ unit ]> = TUnit.
Proof. reflexivity. Qed.

Example parse_ty_prod : <[ Nat * Bool ]> = TProd TNum TBool.
Proof. reflexivity. Qed.

Example parse_ty_sum : <[ Nat + Bool ]> = TSum TNum TBool.
Proof. reflexivity. Qed.

Example parse_ty_list : <[ List Nat ]> = TList TNum.
Proof. reflexivity. Qed.

Example parse_ty_arrow : <[ Nat -> Bool ]> = TArr TNum TBool.
Proof. reflexivity. Qed.

(**
Factorial from TRec still works verbatim in the new scope.
 *)

Definition factGen : TADS :=
  Lambda "g" (TArr TNum TNum)
    (Lambda "n" TNum
      (If (IsZero (Id "n"))
          (Num 1)
          (Mult (Id "n") (App (Id "g") (Minus (Id "n") (Num 1)))))).

Definition fact : TADS := Fix factGen.

Example fact_concrete :
  <{ fix (lambda "g" : Nat -> Nat in
            lambda "n" : Nat in
              if iszero "n" then 1 else "n" * ("g" ("n" - 1))) }> = fact.
Proof. reflexivity. Qed.

Example run_fact5 : eval (App fact (Num 5)) = Some (NumV 120).
Proof. reflexivity. Qed.

(**
The type grammar handles unit, products, sums, and lists.
 *)

Example parse_ty_prod_sum :
  <[ (Nat * Bool) + (List Nat) ]> = TSum (TProd TNum TBool) (TList TNum).
Proof. reflexivity. Qed.

Example parse_ty_arrow_prod :
  <[ Nat * Bool -> Nat ]> = TArr (TProd TNum TBool) TNum.
Proof. reflexivity. Qed.

(**
Term-level concrete syntax: arithmetic, boolean operations, and the new
elimination forms ([isnil], [fst], [snd], [car], [cdr]) all work for
simple arguments.
 *)

Example typecheck_arith_concrete :
  typecheck <{ 3 + 4 }> = Some TNum.
Proof. reflexivity. Qed.

Example eval_arith_concrete :
  eval <{ 3 + 4 }> = Some (NumV 7).
Proof. reflexivity. Qed.

Example typecheck_isnil_concrete :
  typecheck <{ isnil (nil Nat) }> = Some TBool.
Proof. reflexivity. Qed.

Example eval_isnil_concrete :
  eval <{ isnil (nil Nat) }> = Some (BoolV true).
Proof. reflexivity. Qed.

(**
The unit term in concrete syntax: [()] has type [unit] and evaluates to [UnitV].
 *)

Example typecheck_unit_concrete :
  typecheck <{ () }> = Some TUnit.
Proof. reflexivity. Qed.

Example eval_unit_concrete :
  eval <{ () }> = Some UnitV.
Proof. reflexivity. Qed.

(**
Injection forms with type annotation: [inl e as T] and [inr e as T].
 *)

Example typecheck_inl_concrete :
  typecheck <{ inl 5 as Nat + Bool }> = Some (TSum TNum TBool).
Proof. reflexivity. Qed.

Example eval_inl_concrete :
  eval <{ inl 5 as Nat + Bool }> = Some (InLV (NumV 5)).
Proof. reflexivity. Qed.

(**
The [case] elimination form uses keyword separators throughout, so it
parses unambiguously even with complex branch bodies.
 *)

Example typecheck_case_concrete :
  typecheck
    <{ case (inl 5 as Nat + Bool) of inl "n" => "n" else inr "b" => 0 }>
  = Some TNum.
Proof. reflexivity. Qed.

Example eval_case_concrete :
  eval
    <{ case (inl 5 as Nat + Bool) of inl "n" => "n" else inr "b" => 0 }>
  = Some (NumV 5).
Proof. reflexivity. Qed.

(**
Recursive list operations still use [fix] and [lambda] from TRec.
The [isnil] form on a bound variable:
 *)

Example typecheck_sumList_concrete :
  typecheck
    <{ fix (lambda "g" : List Nat -> Nat in
              lambda "xs" : List Nat in
                if isnil "xs" then 0 else
                  (car "xs") + ("g" (cdr "xs"))) }>
  = Some <[ List Nat -> Nat ]>.
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this chapter we extended TRec with three algebraic type formers and
showed how they interact with typing and evaluation.  The central result
is that lists _are_ sums of products at the value level.

#<ol>#
#<li>#Extended the type language [Ty] with [TUnit], [TProd], [TSum], and [TList], along with decidable equality [Ty_eqb] and its correctness lemmas.#</li>#
#<li>#Added [Unit] to the TADS term language alongside product forms ([Pair]/[Fst]/[Snd]), sum forms ([InL]/[InR]/[SCase]), and list forms ([Nil]/[Cons]/[Car]/[Cdr]/[IsNil]).#</li>#
#<li>#Wrote the type checker [typeof]: products infer [TProd A B]; sums require the annotation to determine the full type; lists enforce homogeneity at [Cons]; [Unit] has type [TUnit].#</li>#
#<li>#Defined the strict evaluator [evalM] with value constructors [UnitV], [PairV], [InLV], and [InRV] -- no separate [NilV] or [ConsV].  [Nil] yields [InLV UnitV]; [Cons h t] yields [InRV (PairV h t)].#</li>#
#<li>#Demonstrated the algebraic structure of lists: [nil_is_inl], [cons_is_inr_pair], [list_structure], [scase_on_list].#</li>#
#<li>#Demonstrated products ([swapProg]), sums ([safeDiv] / [safeDivResult]), and polymorphic lists ([list123], [boolList]).#</li>#
#<li>#Wrote recursive list operations ([sumList], [lengthList]) using [Fix] exactly as in TRec.#</li>#
#<li>#Re-proved _fuel monotonicity_ ([evalM_mono]) with cases for all seven [TVal] constructors.#</li>#
#<li>#Added concrete syntax in [tads_scope]: type grammar [<[ ... ]>] with [unit], [*], [+], [List]; term grammar [<{ ... }>] with [()], [fst], [snd], [inl]/[inr], [case ... of], [nil], [car], [cdr], [isnil].#</li>#
#</ol>#

The algebraic types here are the same [*] and [+] studied in Rocq's own
type theory.  Lists reveal this: [TList A] names the recursive equation
[Unit + (A x List A)], and the evaluator makes that equation concrete at
the value level.
 *)

(** * NEW PROOF TACTICS IN THIS CHAPTER *)

(**
This chapter introduces no new proof tactics beyond those in TRec.  All
proofs use the same fuel-induction pattern: [induction f1 as [| k IH]],
[destruct f2 as [| k2]], then per-constructor case analysis with
[destruct ... eqn:...], [rewrite (IH ...)], [apply (IH ...)], and
[exact H].

The [evalM_mono] proof for [Car] and [Cdr] has a two-step destruct: first
[destruct val] to isolate [InRV iv], then [destruct iv] to isolate
[PairV p1' p2'].  This nested destruct reflects the nested structure of
a cons cell value.

The [evalM_mono] proof is shorter than it would be with eight constructors
because removing [NilV] and [ConsV] from [TVal] eliminates those cases
entirely; the list cases now delegate to the same sum/product infrastructure
already proved for [SCase]/[Fst]/[Snd].
 *)
