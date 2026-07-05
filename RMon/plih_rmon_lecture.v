(**
Programming Languages in Rocq - Reader Monad Lecture
Structuring the type checker with a Reader monad

The checkers of TFun and TRec pass a type context [ctx] explicitly
through every call.  This chapter refactors that plumbing into a READER
MONAD - a computation "with access to a fixed context" - so threading
becomes implicit ([ask] to read it, [local] to extend it for a
sub-term, [bind] to carry it along).  We then PROVE the monadic checker
computes exactly what the explicit one does.

The plan:
  1. The typed language [Ty]/[TFBAEC] (with [Fix]) and the DIRECT
     checker [typeof] - the reference, carried over from TRec.
  2. The READER monad: [Reader E A = E -> option A], with [retR], [bindR]
     (with [;;] notation), [askR], [localR], [failR], [runR].
  3. The MONADIC checker [typeofR], written with no explicit context.
  4. AGREEMENT: [typeofR e ctx = typeof ctx e] for all [e], [ctx] - the
     refactor changes the code, not the behavior.

This mirrors the "More Reader Monad" unit of PLIH:
  https://ku-sldg.github.io/plih//types/5-More-Reader-Monad.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rmon_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: THE TYPED LANGUAGE (from TFun/TRec) *)

Inductive Ty : Type :=
| TNum  : Ty
| TBool : Ty
| TArr  : Ty -> Ty -> Ty.

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

Inductive TFBAEC : Type :=
| Num     : nat -> TFBAEC
| Plus    : TFBAEC -> TFBAEC -> TFBAEC
| Minus   : TFBAEC -> TFBAEC -> TFBAEC
| Mult    : TFBAEC -> TFBAEC -> TFBAEC
| Boolean : bool -> TFBAEC
| IsZero  : TFBAEC -> TFBAEC
| If      : TFBAEC -> TFBAEC -> TFBAEC -> TFBAEC
| Bind    : string -> TFBAEC -> TFBAEC -> TFBAEC
| Lambda  : string -> Ty -> TFBAEC -> TFBAEC
| App     : TFBAEC -> TFBAEC -> TFBAEC
| Fix     : TFBAEC -> TFBAEC
| Id      : string -> TFBAEC.

Definition Ctx := Env Ty.

(**
The DIRECT checker, exactly TRec's [typeof]: the type context [ctx] is
an explicit parameter, passed down, extended, and read by hand.  Watch
how often [ctx] is mentioned - that is the plumbing the Reader monad
will hide.
 *)
Fixpoint typeof (ctx : Ctx) (e : TFBAEC) : option Ty :=
  match e with
  | Num _ => Some TNum
  | Boolean _ => Some TBool
  | Plus  l r =>
      match typeof ctx l, typeof ctx r with
      | Some TNum, Some TNum => Some TNum | _, _ => None end
  | Minus l r =>
      match typeof ctx l, typeof ctx r with
      | Some TNum, Some TNum => Some TNum | _, _ => None end
  | Mult  l r =>
      match typeof ctx l, typeof ctx r with
      | Some TNum, Some TNum => Some TNum | _, _ => None end
  | IsZero e0 =>
      match typeof ctx e0 with Some TNum => Some TBool | _ => None end
  | If c t f =>
      match typeof ctx c with
      | Some TBool =>
          match typeof ctx t, typeof ctx f with
          | Some tThen, Some tElse =>
              if Ty_eqb tThen tElse then Some tThen else None
          | _, _ => None end
      | _ => None end
  | Bind i v b =>
      match typeof ctx v with
      | Some tv => typeof (extend i tv ctx) b
      | None => None end
  | Lambda i t b =>
      match typeof (extend i t ctx) b with
      | Some tb => Some (TArr t tb)
      | None => None end
  | App f a =>
      match typeof ctx f, typeof ctx a with
      | Some (TArr d r), Some ta => if Ty_eqb d ta then Some r else None
      | _, _ => None end
  | Fix f =>
      match typeof ctx f with
      | Some (TArr d r) => if Ty_eqb d r then Some r else None
      | _ => None end
  | Id x => lookup x ctx
  end.

Definition typecheck (e : TFBAEC) : option Ty := typeof nil e.

(** * SECTION 2: THE READER MONAD *)

(**
A [Reader E A] is a computation that, given an environment [E], may
produce an [A] (or fail).  It is literally a function [E -> option A].
The monad operations hide the environment argument:
  - [retR a]      : succeed with [a], ignoring the environment;
  - [bindR m f]   : run [m]; if it succeeds with [a], run [f a] - both
                    under the SAME environment, threaded automatically;
  - [askR]        : read the whole environment;
  - [localR g m]  : run [m] under the environment transformed by [g];
  - [failR]       : fail;
  - [runR m e]    : execute [m] with environment [e].
 *)
Definition Reader (E A : Type) : Type := E -> option A.

Definition retR {E A : Type} (a : A) : Reader E A := fun _ => Some a.

Definition bindR {E A B : Type} (m : Reader E A) (f : A -> Reader E B)
  : Reader E B :=
  fun e => match m e with Some a => f a e | None => None end.

Definition askR {E : Type} : Reader E E := fun e => Some e.

Definition localR {E A : Type} (g : E -> E) (m : Reader E A) : Reader E A :=
  fun e => m (g e).

Definition failR {E A : Type} : Reader E A := fun _ => None.

Definition runR {E A : Type} (m : Reader E A) (e : E) : option A := m e.

Notation "x <- m ;; k" := (bindR m (fun x => k))
  (at level 61, m at next level, right associativity).

(** * SECTION 3: THE MONADIC TYPE CHECKER *)

(**
[typeofR] is the SAME checker with the context threading removed.  There
is no [ctx] parameter: [Bind]/[Lambda] use [localR] to extend the
context for a sub-term, and [Id] uses [askR] to read it.  Compare each
case to [typeof] above - the logic is identical, the plumbing is gone.
 *)
Fixpoint typeofR (e : TFBAEC) : Reader Ctx Ty :=
  match e with
  | Num _ => retR TNum
  | Boolean _ => retR TBool
  | Plus  l r =>
      tl <- typeofR l ;; tr <- typeofR r ;;
      match tl, tr with TNum, TNum => retR TNum | _, _ => failR end
  | Minus l r =>
      tl <- typeofR l ;; tr <- typeofR r ;;
      match tl, tr with TNum, TNum => retR TNum | _, _ => failR end
  | Mult  l r =>
      tl <- typeofR l ;; tr <- typeofR r ;;
      match tl, tr with TNum, TNum => retR TNum | _, _ => failR end
  | IsZero e0 =>
      t <- typeofR e0 ;;
      match t with TNum => retR TBool | _ => failR end
  | If c t f =>
      tc <- typeofR c ;;
      match tc with
      | TBool =>
          tt <- typeofR t ;; tf <- typeofR f ;;
          if Ty_eqb tt tf then retR tt else failR
      | _ => failR end
  | Bind i v b =>
      tv <- typeofR v ;;
      localR (extend i tv) (typeofR b)
  | Lambda i t b =>
      tb <- localR (extend i t) (typeofR b) ;;
      retR (TArr t tb)
  | App f a =>
      tf <- typeofR f ;; ta <- typeofR a ;;
      match tf with
      | TArr d r => if Ty_eqb d ta then retR r else failR
      | _ => failR end
  | Fix f =>
      tf <- typeofR f ;;
      match tf with
      | TArr d r => if Ty_eqb d r then retR r else failR
      | _ => failR end
  | Id x =>
      ctx <- askR ;;
      match lookup x ctx with Some t => retR t | None => failR end
  end.

Definition typecheckR (e : TFBAEC) : option Ty := runR (typeofR e) nil.

(** * SECTION 4: AGREEMENT - THE REFACTOR IS BEHAVIOR-PRESERVING *)

(**
The headline: threading the context by monad or by hand gives the SAME
result, at EVERY context.  So [typeofR] is a faithful refactor of
[typeof] - the Reader monad is a change of STYLE, not of MEANING.  The
proof is a direct induction: each case unfolds the monad operations and
closes by the induction hypotheses.
 *)
Theorem typeofR_agrees : forall e ctx, typeofR e ctx = typeof ctx e.
Proof.
  induction e as
    [ n | l IHl r IHr | l IHl r IHr | l IHl r IHr | b | e0 IHe0
    | c IHc t IHt f IHf | i v IHv b IHb | i t b IHb | f IHf a IHa
    | f IHf | x ];
    intros ctx; simpl; cbv beta iota delta [bindR retR askR localR failR].
  - (* Num *) reflexivity.
  - (* Plus *) rewrite IHl, IHr;
      destruct (typeof ctx l) as [[| |]|], (typeof ctx r) as [[| |]|];
      reflexivity.
  - (* Minus *) rewrite IHl, IHr;
      destruct (typeof ctx l) as [[| |]|], (typeof ctx r) as [[| |]|];
      reflexivity.
  - (* Mult *) rewrite IHl, IHr;
      destruct (typeof ctx l) as [[| |]|], (typeof ctx r) as [[| |]|];
      reflexivity.
  - (* Boolean *) reflexivity.
  - (* IsZero *) rewrite IHe0; destruct (typeof ctx e0) as [[| |]|];
      reflexivity.
  - (* If *) rewrite IHc; destruct (typeof ctx c) as [[| |]|]; try reflexivity.
    rewrite IHt, IHf;
      destruct (typeof ctx t) as [tt|], (typeof ctx f) as [tf|]; try reflexivity.
    destruct (Ty_eqb tt tf); reflexivity.
  - (* Bind *) rewrite IHv; destruct (typeof ctx v) as [tv|];
      [rewrite IHb |]; reflexivity.
  - (* Lambda *) rewrite IHb;
      destruct (typeof (extend i t ctx) b) as [tb|]; reflexivity.
  - (* App *) rewrite IHf, IHa;
      destruct (typeof ctx f) as [[| |df rf]|], (typeof ctx a) as [ta|];
      try reflexivity.
    destruct (Ty_eqb df ta); reflexivity.
  - (* Fix *) rewrite IHf; destruct (typeof ctx f) as [[| |df rf]|];
      try reflexivity.
    destruct (Ty_eqb df rf); reflexivity.
  - (* Id *) destruct (lookup x ctx); reflexivity.
Qed.

(* Corollary at the top level: the monadic [typecheckR] equals the direct
   [typecheck]. *)
Corollary typecheckR_agrees : forall e, typecheckR e = typecheck e.
Proof. intros e. unfold typecheckR, typecheck, runR. apply typeofR_agrees. Qed.

(** * SECTION 5: THE CHECKER IN ACTION (via the monad) *)

Definition inc : TFBAEC := Lambda "x" TNum (Plus (Id "x") (Num 1)).

Example rm_inc : typecheckR inc = Some (TArr TNum TNum).
Proof. reflexivity. Qed.

Example rm_app : typecheckR (App inc (Num 4)) = Some TNum.
Proof. reflexivity. Qed.

(* [Bind] extends the context via [localR]; [Id] reads it via [askR]. *)
Example rm_bind :
  typecheckR (Bind "x" (Num 5) (IsZero (Id "x"))) = Some TBool.
Proof. reflexivity. Qed.

(* Rejections still happen - the monad fails ([None]) exactly where the
   direct checker did. *)
Example rm_reject_plus :
  typecheckR (Plus (Boolean true) (Num 1)) = None.
Proof. reflexivity. Qed.

Example rm_reject_unbound : typecheckR (Id "y") = None.
Proof. reflexivity. Qed.

(* A recursive program still type-checks through the monadic checker. *)
Definition factGen : TFBAEC :=
  Lambda "g" (TArr TNum TNum)
    (Lambda "n" TNum
      (If (IsZero (Id "n")) (Num 1)
          (Mult (Id "n") (App (Id "g") (Minus (Id "n") (Num 1)))))).

Example rm_fix : typecheckR (Fix factGen) = Some (TArr TNum TNum).
Proof. reflexivity. Qed.

(** * SECTION 6: CONCRETE SYNTAX *)

(**
The typed language here is the same as TRec's, so it gets the SAME two
notations: a type grammar between [<[ ... ]>] (base [Nat]/[Bool] and the
right-associative arrow [->]) and the term grammar between [<{ ... }>]
with the ascribed lambda [lambda ID : T in body] and the prefix
[fix f].  The MONADIC checker [typecheckR] reads the concrete terms and
predicts the same types the direct checker does.
 *)

Coercion Num : nat >-> TFBAEC.
Coercion Id  : string >-> TFBAEC.

Declare Custom Entry ty.
Declare Scope rmon_scope.
Delimit Scope rmon_scope with rmon.

Notation "<[ t ]>" := t (t custom ty at level 50) : rmon_scope.
Notation "( t )" := t (in custom ty, t at level 50) : rmon_scope.
Notation "'Nat'"  := TNum  (in custom ty at level 0) : rmon_scope.
Notation "'Bool'" := TBool (in custom ty at level 0) : rmon_scope.
Notation "d -> r" := (TArr d r) (in custom ty at level 50, right associativity) : rmon_scope.

Declare Custom Entry tfbaec.
Notation "<{ e }>" := e (e custom tfbaec at level 99) : rmon_scope.
Notation "( x )" := x (in custom tfbaec, x at level 99) : rmon_scope.
Notation "x" := x (in custom tfbaec at level 0, x constr at level 0) : rmon_scope.

Notation "f x" := (App f x) (in custom tfbaec at level 1, left associativity) : rmon_scope.
Notation "'fix' f" := (Fix f) (in custom tfbaec at level 75, right associativity) : rmon_scope.
Notation "'iszero' x" := (IsZero x) (in custom tfbaec at level 75, right associativity) : rmon_scope.
Notation "x * y" := (Mult x y)  (in custom tfbaec at level 40, left associativity) : rmon_scope.
Notation "x + y" := (Plus x y)  (in custom tfbaec at level 50, left associativity) : rmon_scope.
Notation "x - y" := (Minus x y) (in custom tfbaec at level 50, left associativity) : rmon_scope.
Notation "'true'"  := (Boolean true)  (in custom tfbaec at level 0) : rmon_scope.
Notation "'false'" := (Boolean false) (in custom tfbaec at level 0) : rmon_scope.
Notation "'if' c 'then' t 'else' f" := (If c t f)
  (in custom tfbaec at level 89, c custom tfbaec at level 99,
   t custom tfbaec at level 99, f custom tfbaec at level 99) : rmon_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom tfbaec at level 89, v constr at level 0,
   e1 custom tfbaec at level 99, e2 custom tfbaec at level 99) : rmon_scope.
Notation "'lambda' v ':' T 'in' e" := (Lambda v T e)
  (in custom tfbaec at level 90, v constr at level 0,
   T custom ty at level 50, e custom tfbaec at level 99) : rmon_scope.

Open Scope rmon_scope.

(* [inc], concretely, checked through the Reader-monad checker. *)
Example rm_inc_concrete :
  typecheckR <{ lambda "x" : Nat in "x" + 1 }> = Some <[ Nat -> Nat ]>.
Proof. reflexivity. Qed.

(* The factorial generator, concretely; [fix] of it checks at [Nat -> Nat]. *)
Example rm_fix_concrete :
  typecheckR <{ fix (lambda "g" : Nat -> Nat in
                       lambda "n" : Nat in
                         if iszero "n" then 1
                         else "n" * ("g" ("n" - 1))) }>
  = Some <[ Nat -> Nat ]>.
Proof. reflexivity. Qed.

(* A rejection, concretely: the monadic checker still fails on a bad term. *)
Example rm_reject_concrete : typecheckR <{ true + 1 }> = None.
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
  1. Recalled the DIRECT checker [typeof], which threads a type context
     by hand through every case.
  2. Built a READER monad [Reader E A = E -> option A] with
     [retR]/[bindR]/[askR]/[localR]/[failR]/[runR] and a [;;] notation.
  3. Rewrote the checker as [typeofR] with NO explicit context - [localR]
     extends it, [askR] reads it, [bindR] threads it.
  4. Proved AGREEMENT ([typeofR e ctx = typeof ctx e]): the monadic
     refactor is behavior-preserving, a change of style not of meaning.
  5. Added CONCRETE SYNTAX (Section 6): TRec's type grammar
     [<[ Nat -> Bool ]>] and term grammar [<{ ... }>] (ascribed lambda
     and prefix [fix]), read through the monadic checker [typecheckR].

Next: the READER-AND-EITHER chapter upgrades failure from a bare [None]
to an informative error MESSAGE, so a rejected program says WHY.
 *)
