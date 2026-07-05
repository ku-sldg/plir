(**
Programming Languages in Rocq - Reader+Either Monad Lecture
Informative type errors with a combined Reader-and-Either monad

RMon's Reader monad hid the context but still failed with a bare [None].
A type checker should say WHY it rejected a program.  This chapter keeps
the Reader threading and stacks the EITHER monad on top: a computation
is now [RE E A = E -> string + A], which reads a context [E] and either
fails with a message ([inl msg]) or succeeds with a value ([inr a]).

The plan:
  1. The typed language [Ty]/[TFBAEC] and the DIRECT [option] checker
     [typeof] (RMon's reference).
  2. The combined READER+EITHER monad [RE] with [retE]/[bindE]/[askE]/
     [localE]/[throwE]/[runE].
  3. The message-carrying checker [typeofE], throwing a descriptive
     error at each failure.
  4. REFINEMENT: [forget (typeofE e ctx) = typeof ctx e] - erasing the
     message recovers exactly RMon's [option] answer.  So the richer
     checker accepts and rejects exactly the same programs; it just says
     more when it rejects.

This mirrors the "Reader and Either" unit of PLIH (a source placeholder):
  https://ku-sldg.github.io/plih//types/6-Reader-And-Either.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_emon_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: THE TYPED LANGUAGE AND DIRECT CHECKER *)

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

(* The direct, [option]-valued checker, exactly as in TRec/RMon. *)
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

(** * SECTION 2: THE READER+EITHER MONAD *)

(**
[RE E A] combines READER (thread an environment [E]) with EITHER (fail
with a [string] message or succeed with an [A]).  It is a function
[E -> string + A]: given the environment, return [inl msg] on error or
[inr a] on success.
  - [retE a]     : succeed with [a];
  - [bindE m f]  : run [m]; on success feed the value to [f], on error
                   PROPAGATE the message unchanged - both under the same
                   environment;
  - [askE]       : read the environment;
  - [localE g m] : run [m] under a transformed environment;
  - [throwE msg] : fail with [msg];
  - [runE m e]   : execute [m] with environment [e].
 *)
Definition RE (E A : Type) : Type := E -> sum string A.

Definition retE {E A : Type} (a : A) : RE E A := fun _ => inr a.

Definition bindE {E A B : Type} (m : RE E A) (f : A -> RE E B) : RE E B :=
  fun e => match m e with inr a => f a e | inl s => inl s end.

Definition askE {E : Type} : RE E E := fun e => inr e.

Definition localE {E A : Type} (g : E -> E) (m : RE E A) : RE E A :=
  fun e => m (g e).

Definition throwE {E A : Type} (msg : string) : RE E A := fun _ => inl msg.

Definition runE {E A : Type} (m : RE E A) (e : E) : sum string A := m e.

Notation "x <- m ;; k" := (bindE m (fun x => k))
  (at level 61, m at next level, right associativity).

(** * SECTION 3: THE MESSAGE-CARRYING TYPE CHECKER *)

(**
[typeofE] is RMon's monadic checker with every [failR] replaced by a
[throwE] carrying a description of what went wrong.  The Reader
operations ([askE]/[localE]) are unchanged - context is still threaded
implicitly - so only the FAILURE story is richer.
 *)
Fixpoint typeofE (e : TFBAEC) : RE Ctx Ty :=
  match e with
  | Num _ => retE TNum
  | Boolean _ => retE TBool
  | Plus  l r =>
      tl <- typeofE l ;; tr <- typeofE r ;;
      match tl, tr with
      | TNum, TNum => retE TNum
      | _, _ => throwE "plus: operands must be numbers" end
  | Minus l r =>
      tl <- typeofE l ;; tr <- typeofE r ;;
      match tl, tr with
      | TNum, TNum => retE TNum
      | _, _ => throwE "minus: operands must be numbers" end
  | Mult  l r =>
      tl <- typeofE l ;; tr <- typeofE r ;;
      match tl, tr with
      | TNum, TNum => retE TNum
      | _, _ => throwE "mult: operands must be numbers" end
  | IsZero e0 =>
      t <- typeofE e0 ;;
      match t with TNum => retE TBool
                 | _ => throwE "iszero: operand must be a number" end
  | If c t f =>
      tc <- typeofE c ;;
      match tc with
      | TBool =>
          tt <- typeofE t ;; tf <- typeofE f ;;
          if Ty_eqb tt tf then retE tt
          else throwE "if: branches must have the same type"
      | _ => throwE "if: condition must be a Boolean" end
  | Bind i v b =>
      tv <- typeofE v ;;
      localE (extend i tv) (typeofE b)
  | Lambda i t b =>
      tb <- localE (extend i t) (typeofE b) ;;
      retE (TArr t tb)
  | App f a =>
      tf <- typeofE f ;; ta <- typeofE a ;;
      match tf with
      | TArr d r => if Ty_eqb d ta then retE r
                    else throwE "app: argument type does not match domain"
      | _ => throwE "app: applying a non-function" end
  | Fix f =>
      tf <- typeofE f ;;
      match tf with
      | TArr d r => if Ty_eqb d r then retE r
                    else throwE "fix: expected a T -> T function"
      | _ => throwE "fix: applying fix to a non-function" end
  | Id x =>
      ctx <- askE ;;
      match lookup x ctx with
      | Some t => retE t
      | None => throwE "unbound identifier" end
  end.

Definition typecheckE (e : TFBAEC) : sum string Ty := runE (typeofE e) nil.

(** * SECTION 4: REFINEMENT - MESSAGES ASIDE, THE SAME CHECKER *)

(**
[forget] erases an error message, turning the [Either] answer back into
an [option] one.  The headline theorem is that [typeofE] REFINES the
direct [typeof]: forgetting the message recovers exactly RMon's
[option] result.  So the message-carrying checker accepts and rejects
precisely the same programs - it only says MORE when it rejects.
 *)
Definition forget {A : Type} (r : sum string A) : option A :=
  match r with inr a => Some a | inl _ => None end.

Theorem typeofE_refines : forall e ctx, forget (typeofE e ctx) = typeof ctx e.
Proof.
  induction e as
    [ n | l IHl r IHr | l IHl r IHr | l IHl r IHr | b | e0 IHe0
    | c IHc t IHt f IHf | i v IHv b IHb | i t b IHb | f IHf a IHa
    | f IHf | x ];
    intros ctx; simpl; cbv beta iota delta [bindE retE askE localE throwE].
  - (* Num *) reflexivity.
  - (* Plus *) rewrite <- IHl, <- IHr;
      destruct (typeofE l ctx) as [sl|[| |]], (typeofE r ctx) as [sr|[| |]];
      reflexivity.
  - (* Minus *) rewrite <- IHl, <- IHr;
      destruct (typeofE l ctx) as [sl|[| |]], (typeofE r ctx) as [sr|[| |]];
      reflexivity.
  - (* Mult *) rewrite <- IHl, <- IHr;
      destruct (typeofE l ctx) as [sl|[| |]], (typeofE r ctx) as [sr|[| |]];
      reflexivity.
  - (* Boolean *) reflexivity.
  - (* IsZero *) rewrite <- IHe0; destruct (typeofE e0 ctx) as [s|[| |]];
      reflexivity.
  - (* If *) rewrite <- IHc; destruct (typeofE c ctx) as [sc|[| |]];
      cbn; try reflexivity.
    rewrite <- IHt, <- IHf;
      destruct (typeofE t ctx) as [st|tt], (typeofE f ctx) as [sf|tf];
      cbn; try reflexivity.
    destruct (Ty_eqb tt tf); reflexivity.
  - (* Bind *) rewrite <- IHv; destruct (typeofE v ctx) as [sv|tv];
      [reflexivity | apply IHb].
  - (* Lambda *) rewrite <- IHb;
      destruct (typeofE b (extend i t ctx)) as [sb|tb]; reflexivity.
  - (* App *) rewrite <- IHf, <- IHa;
      destruct (typeofE f ctx) as [sf|[| |df rf]], (typeofE a ctx) as [sa|ta];
      cbn; try reflexivity.
    destruct (Ty_eqb df ta); reflexivity.
  - (* Fix *) rewrite <- IHf; destruct (typeofE f ctx) as [sf|[| |df rf]];
      cbn; try reflexivity.
    destruct (Ty_eqb df rf); reflexivity.
  - (* Id *) destruct (lookup x ctx); reflexivity.
Qed.

(* Top-level corollary: forgetting the message recovers [typecheck]. *)
Corollary typecheckE_refines : forall e, forget (typecheckE e) = typecheck e.
Proof. intros e. apply typeofE_refines. Qed.

(** * SECTION 5: ERRORS THAT EXPLAIN THEMSELVES *)

Definition inc : TFBAEC := Lambda "x" TNum (Plus (Id "x") (Num 1)).

(* Good programs succeed with [inr <type>], exactly as before. *)
Example em_ok : typecheckE (App inc (Num 4)) = inr TNum.
Proof. reflexivity. Qed.

(* Bad programs now fail with a MESSAGE instead of a bare [None]. *)
Example em_plus_msg :
  typecheckE (Plus (Boolean true) (Num 1))
  = inl "plus: operands must be numbers".
Proof. reflexivity. Qed.

Example em_if_cond_msg :
  typecheckE (If (Num 1) (Num 2) (Num 3))
  = inl "if: condition must be a Boolean".
Proof. reflexivity. Qed.

Example em_app_msg :
  typecheckE (App (Num 1) (Num 2)) = inl "app: applying a non-function".
Proof. reflexivity. Qed.

Example em_unbound_msg :
  typecheckE (Id "y") = inl "unbound identifier".
Proof. reflexivity. Qed.

(* And by [typecheckE_refines], every one of these agrees with the plain
   [option] checker once the message is erased. *)
Example em_forget_ok : forget (typecheckE (App inc (Num 4))) = Some TNum.
Proof. reflexivity. Qed.

Example em_forget_bad : forget (typecheckE (Id "y")) = None.
Proof. reflexivity. Qed.

(** * SECTION 6: CONCRETE SYNTAX *)

(**
The typed language is the same as TRec's, so it gets the SAME two
notations: a type grammar between [<[ ... ]>] (base [Nat]/[Bool] and the
right-associative arrow [->]) and the term grammar between [<{ ... }>]
with the ascribed lambda [lambda ID : T in body] and the prefix
[fix f].  Through the MESSAGE-CARRYING checker [typecheckE], a good
concrete program yields [inr <type>], and a bad one yields [inl
<message>].
 *)

Coercion Num : nat >-> TFBAEC.
Coercion Id  : string >-> TFBAEC.

Declare Custom Entry ty.
Declare Scope emon_scope.
Delimit Scope emon_scope with emon.

Notation "<[ t ]>" := t (t custom ty at level 50) : emon_scope.
Notation "( t )" := t (in custom ty, t at level 50) : emon_scope.
Notation "'Nat'"  := TNum  (in custom ty at level 0) : emon_scope.
Notation "'Bool'" := TBool (in custom ty at level 0) : emon_scope.
Notation "d -> r" := (TArr d r) (in custom ty at level 50, right associativity) : emon_scope.

Declare Custom Entry tfbaec.
Notation "<{ e }>" := e (e custom tfbaec at level 99) : emon_scope.
Notation "( x )" := x (in custom tfbaec, x at level 99) : emon_scope.
Notation "x" := x (in custom tfbaec at level 0, x constr at level 0) : emon_scope.

Notation "f x" := (App f x) (in custom tfbaec at level 1, left associativity) : emon_scope.
Notation "'fix' f" := (Fix f) (in custom tfbaec at level 75, right associativity) : emon_scope.
Notation "'iszero' x" := (IsZero x) (in custom tfbaec at level 75, right associativity) : emon_scope.
Notation "x * y" := (Mult x y)  (in custom tfbaec at level 40, left associativity) : emon_scope.
Notation "x + y" := (Plus x y)  (in custom tfbaec at level 50, left associativity) : emon_scope.
Notation "x - y" := (Minus x y) (in custom tfbaec at level 50, left associativity) : emon_scope.
Notation "'true'"  := (Boolean true)  (in custom tfbaec at level 0) : emon_scope.
Notation "'false'" := (Boolean false) (in custom tfbaec at level 0) : emon_scope.
Notation "'if' c 'then' t 'else' f" := (If c t f)
  (in custom tfbaec at level 89, c custom tfbaec at level 99,
   t custom tfbaec at level 99, f custom tfbaec at level 99) : emon_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom tfbaec at level 89, v constr at level 0,
   e1 custom tfbaec at level 99, e2 custom tfbaec at level 99) : emon_scope.
Notation "'lambda' v ':' T 'in' e" := (Lambda v T e)
  (in custom tfbaec at level 90, v constr at level 0,
   T custom ty at level 50, e custom tfbaec at level 99) : emon_scope.

Open Scope emon_scope.

(* A concrete success: the checker returns the type on the [inr] side. *)
Example em_ok_concrete :
  typecheckE <{ (lambda "x" : Nat in "x" + 1) 4 }> = inr TNum.
Proof. reflexivity. Qed.

(* A concrete rejection: a descriptive message on the [inl] side. *)
Example em_msg_concrete :
  typecheckE <{ true + 1 }> = inl "plus: operands must be numbers".
Proof. reflexivity. Qed.

(* [fix] still checks through the message-carrying checker. *)
Example em_fix_concrete :
  typecheckE <{ fix (lambda "g" : Nat -> Nat in
                       lambda "n" : Nat in
                         if iszero "n" then 1
                         else "n" * ("g" ("n" - 1))) }>
  = inr <[ Nat -> Nat ]>.
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
  1. Kept the typed language and the direct [option] checker [typeof].
  2. Combined READER with EITHER: [RE E A = E -> string + A], threading
     a context AND carrying an error message, with
     [retE]/[bindE]/[askE]/[localE]/[throwE]/[runE].
  3. Wrote [typeofE], which reports a descriptive message at every
     failure instead of a bare [None].
  4. Proved REFINEMENT ([forget (typeofE e ctx) = typeof ctx e]): the
     message-carrying checker decides exactly the same programs; the
     messages are extra information, not a change of behavior.
  5. Added CONCRETE SYNTAX (Section 6): TRec's type grammar
     [<[ Nat -> Bool ]>] and term grammar [<{ ... }>] (ascribed lambda
     and prefix [fix]), read through [typecheckE] - success on [inr], a
     descriptive message on [inl].

This completes the monadic-interpreter arc: the Reader monad removed the
context plumbing, and the Either monad turned silent failure into
explained failure - all while provably preserving what the checker
decides.  Next in the course: modeling mutable STATE.
 *)
