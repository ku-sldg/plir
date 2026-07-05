(**
Programming Languages in Rocq - State Monad Lecture
Structuring the interpreter with a State monad

The State chapter's interpreter threads the store BY HAND: every case
names intermediate stores [s1], [s2], ... and passes each subexpression
the store its predecessor left.  This chapter refactors that plumbing
into a STATE MONAD - a computation "over a mutable store" - so threading
becomes implicit ([get] to read it, [put] to replace it, [bind] to carry
it along).  We then PROVE the monadic interpreter computes exactly what
the explicit one does.

The plan:
  1. The reference-cell language [FBAES], values [RVal], the [Store], and
     the DIRECT store-threading interpreter [evalM] - the reference,
     carried over from the State chapter.
  2. The STATE monad: [State S A = S -> option (A * S)], with [retS],
     [bindS] (with [;;] notation), [getS], [putS], [failS], [runState].
  3. The MONADIC interpreter [evalS], written with no explicit store.
  4. AGREEMENT: [evalS fuel env e s = evalM fuel env s e] for all inputs
     - the refactor changes the code, not the behavior.

This mirrors the "State Monad" idea of PLIH:
  https://ku-sldg.github.io/plih//state/
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_smon_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: THE LANGUAGE AND THE REFERENCE INTERPRETER *)

(**
[FBAES], its values [RVal] (with locations [LocV]), the [Store], and the
explicit store-threading interpreter [evalM] are carried over verbatim
from the State chapter.  They are the REFERENCE the monadic interpreter
must match - notice how [evalM] names [s1], [s2], ... by hand.
 *)
Inductive FBAES : Type :=
| Num     : nat -> FBAES
| Plus    : FBAES -> FBAES -> FBAES
| Minus   : FBAES -> FBAES -> FBAES
| Mult    : FBAES -> FBAES -> FBAES
| Boolean : bool -> FBAES
| IsZero  : FBAES -> FBAES
| If      : FBAES -> FBAES -> FBAES -> FBAES
| Bind    : string -> FBAES -> FBAES -> FBAES
| Lambda  : string -> FBAES -> FBAES
| App     : FBAES -> FBAES -> FBAES
| Id      : string -> FBAES
| Seq     : FBAES -> FBAES -> FBAES
| New     : FBAES -> FBAES
| Deref   : FBAES -> FBAES
| Assign  : FBAES -> FBAES -> FBAES.

Inductive RVal : Type :=
| NumV     : nat -> RVal
| BoolV    : bool -> RVal
| ClosureV : string -> FBAES -> list (string * RVal) -> RVal
| LocV     : nat -> RVal.

Definition Store := list RVal.

Fixpoint evalM (fuel : nat) (env : Env RVal) (s : Store) (e : FBAES)
  : option (RVal * Store) :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (NumV n, s)
      | Plus l r =>
          match evalM k env s l with
          | Some (NumV a, s1) =>
              match evalM k env s1 r with
              | Some (NumV b, s2) => Some (NumV (a + b), s2)
              | _ => None
              end
          | _ => None
          end
      | Minus l r =>
          match evalM k env s l with
          | Some (NumV a, s1) =>
              match evalM k env s1 r with
              | Some (NumV b, s2) => Some (NumV (a - b), s2)
              | _ => None
              end
          | _ => None
          end
      | Mult l r =>
          match evalM k env s l with
          | Some (NumV a, s1) =>
              match evalM k env s1 r with
              | Some (NumV b, s2) => Some (NumV (a * b), s2)
              | _ => None
              end
          | _ => None
          end
      | Boolean b => Some (BoolV b, s)
      | IsZero e0 =>
          match evalM k env s e0 with
          | Some (NumV n, s1) => Some (BoolV (Nat.eqb n 0), s1)
          | _ => None
          end
      | If c t f =>
          match evalM k env s c with
          | Some (BoolV b, s1) =>
              if b then evalM k env s1 t else evalM k env s1 f
          | _ => None
          end
      | Bind i v b =>
          match evalM k env s v with
          | Some (v', s1) => evalM k (extend i v' env) s1 b
          | None => None
          end
      | Lambda i b => Some (ClosureV i b env, s)
      | App f a =>
          match evalM k env s f with
          | Some (ClosureV i b cenv, s1) =>
              match evalM k env s1 a with
              | Some (a', s2) => evalM k (extend i a' cenv) s2 b
              | None => None
              end
          | _ => None
          end
      | Id x =>
          match lookup x env with
          | Some v => Some (v, s)
          | None => None
          end
      | Seq a b =>
          match evalM k env s a with
          | Some (_, s1) => evalM k env s1 b
          | None => None
          end
      | New e0 =>
          match evalM k env s e0 with
          | Some (v, s1) => Some (LocV (length s1), (s1 ++ [v])%list)
          | None => None
          end
      | Deref e0 =>
          match evalM k env s e0 with
          | Some (LocV n, s1) =>
              match nth_error s1 n with
              | Some v => Some (v, s1)
              | None => None
              end
          | _ => None
          end
      | Assign l r =>
          match evalM k env s l with
          | Some (LocV n, s1) =>
              match evalM k env s1 r with
              | Some (v, s2) =>
                  match update_at n v s2 with
                  | Some s3 => Some (v, s3)
                  | None => None
                  end
              | None => None
              end
          | _ => None
          end
      end
  end.

Definition eval (e : FBAES) : option (RVal * Store) := evalM 1000 nil nil e.

(** * SECTION 2: THE STATE MONAD *)

(**
A STATE computation over store type [S] producing an [A] is a function
[S -> option (A * S)]: given the current store it may FAIL ([None]) or
produce a value together with the UPDATED store.  This is exactly the
shape [evalM] returns - the monad just names the pattern.

  - [retS a]   : succeed with [a], leaving the store untouched;
  - [bindS m f]: run [m], then run [f] on its result IN THE STORE [m]
                 left - this is where the threading happens, once;
  - [getS]     : read the current store as the value;
  - [putS s']  : replace the store with [s'];
  - [failS]    : fail;
  - [runState] : run a computation from an initial store.
 *)
Definition State (S A : Type) : Type := S -> option (A * S).

Definition retS {S A : Type} (a : A) : State S A :=
  fun s => Some (a, s).

Definition bindS {S A B : Type} (m : State S A) (f : A -> State S B) : State S B :=
  fun s => match m s with
           | Some (a, s') => f a s'
           | None => None
           end.

Definition getS {S : Type} : State S S :=
  fun s => Some (s, s).

Definition putS {S : Type} (s' : S) : State S unit :=
  fun _ => Some (tt, s').

Definition failS {S A : Type} : State S A :=
  fun _ => None.

Definition runState {S A : Type} (m : State S A) (s : S) : option (A * S) := m s.

Notation "x <- m ;; k" := (bindS m (fun x => k))
  (at level 61, m at next level, right associativity).

(** * SECTION 3: THE MONADIC INTERPRETER *)

(**
The same interpreter, restructured over the State monad.  There is NO
store variable in sight: [bindS] threads it, [getS]/[putS] touch it only
where a cell is actually read or written.  Compare case-by-case with
[evalM] above - [New]/[Deref]/[Assign] are where [getS]/[putS] appear;
everything else is pure [retS]/[bindS].  The environment is still an
explicit argument (it is READ-ONLY, so it needs no monad here).
 *)
Fixpoint evalS (fuel : nat) (env : Env RVal) (e : FBAES) : State Store RVal :=
  match fuel with
  | 0 => failS
  | S k =>
      match e with
      | Num n => retS (NumV n)
      | Plus l r =>
          a <- evalS k env l ;;
          match a with
          | NumV x => b <- evalS k env r ;;
                      match b with NumV y => retS (NumV (x + y)) | _ => failS end
          | _ => failS
          end
      | Minus l r =>
          a <- evalS k env l ;;
          match a with
          | NumV x => b <- evalS k env r ;;
                      match b with NumV y => retS (NumV (x - y)) | _ => failS end
          | _ => failS
          end
      | Mult l r =>
          a <- evalS k env l ;;
          match a with
          | NumV x => b <- evalS k env r ;;
                      match b with NumV y => retS (NumV (x * y)) | _ => failS end
          | _ => failS
          end
      | Boolean b => retS (BoolV b)
      | IsZero e0 =>
          a <- evalS k env e0 ;;
          match a with NumV n => retS (BoolV (Nat.eqb n 0)) | _ => failS end
      | If c t f =>
          a <- evalS k env c ;;
          match a with
          | BoolV b => if b then evalS k env t else evalS k env f
          | _ => failS
          end
      | Bind i v b =>
          a <- evalS k env v ;;
          evalS k (extend i a env) b
      | Lambda i b => retS (ClosureV i b env)
      | App f a =>
          g <- evalS k env f ;;
          match g with
          | ClosureV i b cenv =>
              w <- evalS k env a ;;
              evalS k (extend i w cenv) b
          | _ => failS
          end
      | Id x =>
          match lookup x env with Some v => retS v | None => failS end
      | Seq a b =>
          _ <- evalS k env a ;;
          evalS k env b
      | New e0 =>
          v <- evalS k env e0 ;;
          s0 <- getS ;;
          _ <- putS (s0 ++ [v])%list ;;
          retS (LocV (length s0))
      | Deref e0 =>
          a <- evalS k env e0 ;;
          match a with
          | LocV n =>
              s0 <- getS ;;
              match nth_error s0 n with Some w => retS w | None => failS end
          | _ => failS
          end
      | Assign l r =>
          a <- evalS k env l ;;
          match a with
          | LocV n =>
              w <- evalS k env r ;;
              s0 <- getS ;;
              match update_at n w s0 with
              | Some s' => _ <- putS s' ;; retS w
              | None => failS
              end
          | _ => failS
          end
      end
  end.

Definition evalStore (e : FBAES) : option (RVal * Store) :=
  runState (evalS 1000 nil e) nil.

(** * SECTION 4: RUNNING THE MONADIC INTERPRETER *)

(* The same programs as in the State chapter - now the store is threaded by
   the monad, but the answers are identical. *)

Example evS_arith :
  evalStore (Mult (Num 6) (Plus (Num 3) (Num 4))) = Some (NumV 42, nil).
Proof. reflexivity. Qed.

Example evS_new :
  evalStore (New (Num 7)) = Some (LocV 0, [NumV 7]).
Proof. reflexivity. Qed.

Example evS_roundtrip :
  evalStore (Bind "r" (New (Num 0))
               (Seq (Assign (Id "r") (Num 7))
                    (Deref (Id "r"))))
  = Some (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

(* Aliasing works exactly as before - two names, one cell. *)
Example evS_aliasing :
  evalStore (Bind "r" (New (Num 0))
               (Bind "a" (Id "r")
                  (Seq (Assign (Id "r") (Num 99))
                       (Deref (Id "a")))))
  = Some (NumV 99, [NumV 99]).
Proof. reflexivity. Qed.

(** * SECTION 5: AGREEMENT - THE HEADLINE *)

(**
The refactor is faithful: run from any store, the monadic interpreter
returns exactly what the explicit one does.  The proof is by induction
on fuel; each case unfolds the monad operations and rewrites the
inductive hypothesis at every subexpression, so the implicit threading
of [bindS]/[getS]/[putS] lines up with [evalM]'s hand-written stores.
 *)
Theorem evalS_agrees : forall fuel env e s,
  evalS fuel env e s = evalM fuel env s e.
Proof.
  induction fuel as [| k IH]; intros env e s.
  - reflexivity.
  - destruct e as
      [ n | l r | l r | l r | b | e0 | c t f | i ve be | i be
      | fe ae | x | ae be | e0 | e0 | le re ];
      cbn [evalS evalM]; cbv beta iota delta [bindS retS getS putS failS].
    + (* Num *) reflexivity.
    + (* Plus *)
      rewrite (IH env l s).
      destruct (evalM k env s l) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH env r s1).
      destruct (evalM k env s1 r) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|]; reflexivity.
    + (* Minus *)
      rewrite (IH env l s).
      destruct (evalM k env s l) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH env r s1).
      destruct (evalM k env s1 r) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|]; reflexivity.
    + (* Mult *)
      rewrite (IH env l s).
      destruct (evalM k env s l) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH env r s1).
      destruct (evalM k env s1 r) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|]; reflexivity.
    + (* Boolean *) reflexivity.
    + (* IsZero *)
      rewrite (IH env e0 s).
      destruct (evalM k env s e0) as [[[a|b|i bd ce|loc] s1]|]; reflexivity.
    + (* If *)
      rewrite (IH env c s).
      destruct (evalM k env s c) as [[[a|bb|i bd ce|loc] s1]|]; try reflexivity.
      destruct bb; cbn -[evalS evalM].
      * rewrite (IH env t s1). reflexivity.
      * rewrite (IH env f s1). reflexivity.
    + (* Bind *)
      rewrite (IH env ve s).
      destruct (evalM k env s ve) as [[v1 s1]|]; try reflexivity.
      rewrite (IH (extend i v1 env) be s1). reflexivity.
    + (* Lambda *) reflexivity.
    + (* App *)
      rewrite (IH env fe s).
      destruct (evalM k env s fe) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH env ae s1).
      destruct (evalM k env s1 ae) as [[w s2]|]; try reflexivity.
      rewrite (IH (extend i w ce) bd s2). reflexivity.
    + (* Id *)
      destruct (lookup x env) as [v|]; reflexivity.
    + (* Seq *)
      rewrite (IH env ae s).
      destruct (evalM k env s ae) as [[v1 s1]|]; try reflexivity.
      rewrite (IH env be s1). reflexivity.
    + (* New *)
      rewrite (IH env e0 s).
      destruct (evalM k env s e0) as [[v1 s1]|]; reflexivity.
    + (* Deref *)
      rewrite (IH env e0 s).
      destruct (evalM k env s e0) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      destruct (nth_error s1 loc); reflexivity.
    + (* Assign *)
      rewrite (IH env le s).
      destruct (evalM k env s le) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH env re s1).
      destruct (evalM k env s1 re) as [[w s2]|]; try reflexivity.
      destruct (update_at loc w s2); reflexivity.
Qed.

(**
The wrapper agrees too: running the monadic interpreter from the empty
store and environment is exactly the explicit [eval].
 *)
Corollary evalStore_agrees : forall e, evalStore e = eval e.
Proof. intro e. unfold evalStore, runState, eval. apply evalS_agrees. Qed.

(** * SECTION 6: MONAD LAWS *)

(**
The State operations obey the monad laws.  LEFT IDENTITY holds by
computation (and eta): binding a pure value just applies the
continuation.
 *)
Lemma left_id_S : forall (A B : Type) (a : A) (f : A -> State Store B),
  bindS (retS a) f = f a.
Proof. reflexivity. Qed.

(**
GET-AFTER-PUT: after replacing the store with [s'], reading it back
yields [s'] - so [put] then [get] is the same as [put] then return [s'].
 *)
Lemma get_put_S : forall (s' : Store),
  bindS (putS s') (fun _ => getS) = bindS (putS s') (fun _ => retS s').
Proof. reflexivity. Qed.

(**
(RIGHT IDENTITY [bindS m retS = m] also holds, but only up to functional
extensionality - it needs to reduce a [match m s] whose scrutinee is
abstract - so we omit it, as in the Reader/Either chapters.)
 *)

(** * SECTION 7: CONCRETE SYNTAX *)

(**
[FBAES] is the same reference-cell language as the State chapter, so it
gets the SAME notation parser: Rec's FBAEC grammar plus the four state
forms [new e], [! e], [l := e], and [a ; b].  (The term-level [;]
between [<{ ... }>] is unrelated to the monadic [;;] on [State] values.)
Reading the concrete programs through the MONADIC interpreter
[evalStore] gives the same answers as the explicit one - the surface
never changed, only the interpreter's internals did.
 *)

Coercion Num : nat >-> FBAES.
Coercion Id  : string >-> FBAES.

Declare Custom Entry fbaes.
Declare Scope smon_scope.
Delimit Scope smon_scope with smon.

Notation "<{ e }>" := e (e custom fbaes at level 99) : smon_scope.
Notation "( x )" := x (in custom fbaes, x at level 99) : smon_scope.
Notation "x" := x (in custom fbaes at level 0, x constr at level 0) : smon_scope.

Notation "f x" := (App f x) (in custom fbaes at level 1, left associativity) : smon_scope.
Notation "'!' e" := (Deref e) (in custom fbaes at level 1, e custom fbaes at level 0) : smon_scope.
Notation "'new' e" := (New e) (in custom fbaes at level 75, right associativity) : smon_scope.
Notation "'iszero' x" := (IsZero x) (in custom fbaes at level 75, right associativity) : smon_scope.
Notation "x * y" := (Mult x y)  (in custom fbaes at level 40, left associativity) : smon_scope.
Notation "x + y" := (Plus x y)  (in custom fbaes at level 50, left associativity) : smon_scope.
Notation "x - y" := (Minus x y) (in custom fbaes at level 50, left associativity) : smon_scope.
Notation "'true'"  := (Boolean true)  (in custom fbaes at level 0) : smon_scope.
Notation "'false'" := (Boolean false) (in custom fbaes at level 0) : smon_scope.
Notation "'if' c 'then' t 'else' f" := (If c t f)
  (in custom fbaes at level 89, c custom fbaes at level 99,
   t custom fbaes at level 99, f custom fbaes at level 99) : smon_scope.
Notation "'lambda' v 'in' e" := (Lambda v e)
  (in custom fbaes at level 90, v constr at level 0, e custom fbaes at level 99) : smon_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom fbaes at level 89, v constr at level 0,
   e1 custom fbaes at level 99, e2 custom fbaes at level 99) : smon_scope.
Notation "l ':=' e" := (Assign l e)
  (in custom fbaes at level 85, e custom fbaes at level 84, no associativity) : smon_scope.
Notation "a ';' b" := (Seq a b)
  (in custom fbaes at level 90, right associativity) : smon_scope.

Open Scope smon_scope.

(* The Section 4 programs, concretely, through the monadic interpreter. *)
Example evS_roundtrip_concrete :
  evalStore <{ bind "r" = new 0 in "r" := 7 ; !"r" }> = Some (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

Example evS_aliasing_concrete :
  evalStore <{ bind "r" = new 0 in
                 bind "a" = "r" in "r" := 99 ; !"a" }>
  = Some (NumV 99, [NumV 99]).
Proof. reflexivity. Qed.

(* And agreement means the concrete program runs identically under the
   explicit reference interpreter. *)
Example evS_matches_reference :
  evalStore <{ bind "c" = new 0 in "c" := !"c" + 1 ; "c" := !"c" + 1 ; !"c" }>
  = eval    <{ bind "c" = new 0 in "c" := !"c" + 1 ; "c" := !"c" + 1 ; !"c" }>.
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
  1. Carried over the reference-cell language [FBAES] and its EXPLICIT
     store-threading interpreter [evalM] from the State chapter.
  2. Defined the STATE monad [State S A = S -> option (A * S)] with
     [retS]/[bindS]/[getS]/[putS]/[failS] and [;;] notation.
  3. Rebuilt the interpreter as [evalS] with NO explicit store - [bindS]
     threads it, [getS]/[putS] appear only at [New]/[Deref]/[Assign].
  4. Proved AGREEMENT: [evalS fuel env e s = evalM fuel env s e], so the
     monadic refactor changes the structure, not the behavior (corollary
     [evalStore_agrees] lifts this to the top-level wrappers).
  5. Checked the monad laws that hold definitionally (left identity,
     get-after-put).
  6. Added CONCRETE SYNTAX (Section 7): the same FBAES notation parser as
     the State chapter ([new e]/[! e]/[l := e]/[a ; b]), read through the
     monadic interpreter [evalStore].

This closes the mutable-state arc: the State chapter showed WHAT
mutation means (an explicitly threaded store); this chapter shows how to
STRUCTURE that threading so the interpreter reads like the pure ones
again - the same payoff the Reader monad gave the type checker.
 *)
