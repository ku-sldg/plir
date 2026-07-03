(**
 * Programming Languages in Rocq - Reader+State Monad Lecture
 * Structuring the interpreter with a combined Reader + State monad
 *
 * SMon hid the mutable STORE behind a State monad, but the read-only
 * ENVIRONMENT stayed an explicit argument.  RMon hid a read-only context
 * behind a Reader monad.  This chapter COMBINES both effects in one monad,
 * so the interpreter carries neither the environment nor the store by hand:
 *   - the environment is read with [askRS] and extended for a sub-term
 *     with [localRS] (the Reader part);
 *   - the store is read with [getRS] and replaced with [putRS] (the State
 *     part);
 *   - [bindRS] threads BOTH automatically.
 *
 * The plan:
 *   1. The reference-cell language [FBAES], values [RVal], the [Store], and
 *      the explicit interpreter [evalM] threading BOTH env and store by
 *      hand - the reference, carried over from the State chapter.
 *   2. The combined monad [RS E S A = E -> S -> option (A * S)], with
 *      [retRS]/[bindRS]/[askRS]/[localRS]/[getRS]/[putRS]/[failRS]/[runRS].
 *   3. The MONADIC interpreter [evalRS], with NO explicit env or store.
 *   4. AGREEMENT: [evalRS fuel e env s = evalM fuel env s e] - one proof
 *      that both hidden resources line up with [evalM]'s hand plumbing.
 *
 * This mirrors the effect-combining ("monad transformer") idea of PLIH:
 *   https://ku-sldg.github.io/plih//state/
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rsmon_shared.

Local Open Scope string_scope.
Import ListNotations.

(* ================================================================ *)
(* SECTION 1: THE LANGUAGE AND THE REFERENCE INTERPRETER           *)
(* ================================================================ *)

(**
 * [FBAES], its values [RVal] (with locations [LocV]), the [Store], and the
 * explicit interpreter [evalM] are carried over from the State chapter.
 * [evalM] threads BOTH resources by hand: the environment [env] as an
 * argument (extended for [Bind]/[Lambda]/[App]), and the store [s] returned
 * in a pair.  The combined monad below hides both.
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

(* ================================================================ *)
(* SECTION 2: THE COMBINED READER + STATE MONAD                    *)
(* ================================================================ *)

(**
 * A combined computation over an environment [E] and a store [S] producing
 * an [A] is a function [E -> S -> option (A * S)]: given the CURRENT
 * environment and store, it may fail, or produce a value with the UPDATED
 * store (the environment is read-only, so it is never returned).  This is
 * exactly what [evalM] is, curried - the monad names the pattern.
 *
 * READER operations (environment):
 *   - [askRS]      : read the current environment as the value;
 *   - [localRS g m]: run [m] under environment [g e] (used to extend it).
 * STATE operations (store):
 *   - [getRS]      : read the current store as the value;
 *   - [putRS s']   : replace the store with [s'].
 * And the monad core [retRS] / [bindRS] (threading BOTH) / [failRS].
 *)
Definition RS (E S A : Type) : Type := E -> S -> option (A * S).

Definition retRS {E S A : Type} (a : A) : RS E S A :=
  fun _ s => Some (a, s).

Definition bindRS {E S A B : Type} (m : RS E S A) (f : A -> RS E S B) : RS E S B :=
  fun e s => match m e s with
             | Some (a, s') => f a e s'
             | None => None
             end.

Definition askRS {E S : Type} : RS E S E :=
  fun e s => Some (e, s).

Definition localRS {E S A : Type} (g : E -> E) (m : RS E S A) : RS E S A :=
  fun e s => m (g e) s.

Definition getRS {E S : Type} : RS E S S :=
  fun _ s => Some (s, s).

Definition putRS {E S : Type} (s' : S) : RS E S unit :=
  fun _ _ => Some (tt, s').

Definition failRS {E S A : Type} : RS E S A :=
  fun _ _ => None.

Definition runRS {E S A : Type} (m : RS E S A) (e : E) (s : S) : option (A * S) :=
  m e s.

Notation "x <- m ;; k" := (bindRS m (fun x => k))
  (at level 61, m at next level, right associativity).

(* ================================================================ *)
(* SECTION 3: THE MONADIC INTERPRETER                             *)
(* ================================================================ *)

(**
 * The interpreter, restructured over the combined monad.  There is NO
 * environment and NO store variable anywhere:
 *   - [Id] reads the environment with [askRS];
 *   - [Lambda] captures it with [askRS];
 *   - [Bind] extends it for the body with [localRS (extend i a)];
 *   - [App] switches to the closure's environment with
 *     [localRS (fun _ => extend i w cenv)] (static scoping);
 *   - [New]/[Deref]/[Assign] touch the store with [getRS]/[putRS];
 *   - [bindRS] threads both, everywhere, once.
 *)
Fixpoint evalRS (fuel : nat) (e : FBAES) : RS (Env RVal) Store RVal :=
  match fuel with
  | 0 => failRS
  | S k =>
      match e with
      | Num n => retRS (NumV n)
      | Plus l r =>
          a <- evalRS k l ;;
          match a with
          | NumV x => b <- evalRS k r ;;
                      match b with NumV y => retRS (NumV (x + y)) | _ => failRS end
          | _ => failRS
          end
      | Minus l r =>
          a <- evalRS k l ;;
          match a with
          | NumV x => b <- evalRS k r ;;
                      match b with NumV y => retRS (NumV (x - y)) | _ => failRS end
          | _ => failRS
          end
      | Mult l r =>
          a <- evalRS k l ;;
          match a with
          | NumV x => b <- evalRS k r ;;
                      match b with NumV y => retRS (NumV (x * y)) | _ => failRS end
          | _ => failRS
          end
      | Boolean b => retRS (BoolV b)
      | IsZero e0 =>
          a <- evalRS k e0 ;;
          match a with NumV n => retRS (BoolV (Nat.eqb n 0)) | _ => failRS end
      | If c t f =>
          a <- evalRS k c ;;
          match a with
          | BoolV b => if b then evalRS k t else evalRS k f
          | _ => failRS
          end
      | Bind i v b =>
          a <- evalRS k v ;;
          localRS (extend i a) (evalRS k b)
      | Lambda i b =>
          env <- askRS ;;
          retRS (ClosureV i b env)
      | App f a =>
          g <- evalRS k f ;;
          match g with
          | ClosureV i b cenv =>
              w <- evalRS k a ;;
              localRS (fun _ => extend i w cenv) (evalRS k b)
          | _ => failRS
          end
      | Id x =>
          env <- askRS ;;
          match lookup x env with Some v => retRS v | None => failRS end
      | Seq a b =>
          _ <- evalRS k a ;;
          evalRS k b
      | New e0 =>
          v <- evalRS k e0 ;;
          s0 <- getRS ;;
          _ <- putRS (s0 ++ [v])%list ;;
          retRS (LocV (length s0))
      | Deref e0 =>
          a <- evalRS k e0 ;;
          match a with
          | LocV n =>
              s0 <- getRS ;;
              match nth_error s0 n with Some w => retRS w | None => failRS end
          | _ => failRS
          end
      | Assign l r =>
          a <- evalRS k l ;;
          match a with
          | LocV n =>
              w <- evalRS k r ;;
              s0 <- getRS ;;
              match update_at n w s0 with
              | Some s' => _ <- putRS s' ;; retRS w
              | None => failRS
              end
          | _ => failRS
          end
      end
  end.

Definition evalReaderState (e : FBAES) : option (RVal * Store) :=
  runRS (evalRS 1000 e) nil nil.

(* ================================================================ *)
(* SECTION 4: RUNNING THE MONADIC INTERPRETER                     *)
(* ================================================================ *)

(* The same programs as before - now BOTH the environment and the store are
   threaded by the monad, and the answers are unchanged. *)

Example evRS_arith :
  evalReaderState (Mult (Num 6) (Plus (Num 3) (Num 4))) = Some (NumV 42, nil).
Proof. reflexivity. Qed.

Example evRS_closure :
  evalReaderState (App (Lambda "x" (Plus (Id "x") (Num 1))) (Num 41))
  = Some (NumV 42, nil).
Proof. reflexivity. Qed.

Example evRS_roundtrip :
  evalReaderState (Bind "r" (New (Num 0))
                     (Seq (Assign (Id "r") (Num 7))
                          (Deref (Id "r"))))
  = Some (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

(* Static scoping AND mutable state in one program: the closure captures
   its definition-time environment (with cell [r]), and the write persists. *)
Example evRS_scope_and_state :
  evalReaderState
    (Bind "r" (New (Num 1))
       (Bind "f" (Lambda "n" (Assign (Id "r") (Plus (Deref (Id "r")) (Id "n"))))
          (Seq (App (Id "f") (Num 10))
               (Deref (Id "r")))))
  = Some (NumV 11, [NumV 11]).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SECTION 5: AGREEMENT - THE HEADLINE                            *)
(* ================================================================ *)

(**
 * The combined refactor is faithful: supply any environment and store, and
 * the monadic interpreter returns exactly what the explicit one does.  One
 * induction handles BOTH hidden resources - the [askRS]/[localRS] threading
 * of the environment lines up with [evalM]'s [env] argument, and the
 * [getRS]/[putRS] threading of the store lines up with its returned store.
 *)
Theorem evalRS_agrees : forall fuel e env s,
  evalRS fuel e env s = evalM fuel env s e.
Proof.
  induction fuel as [| k IH]; intros e env s.
  - reflexivity.
  - destruct e as
      [ n | l r | l r | l r | b | e0 | c t f | i ve be | i be
      | fe ae | x | ae be | e0 | e0 | le re ];
      cbn [evalRS evalM];
      cbv beta iota delta [retRS bindRS askRS localRS getRS putRS failRS].
    + (* Num *) reflexivity.
    + (* Plus *)
      rewrite (IH l env s).
      destruct (evalM k env s l) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH r env s1).
      destruct (evalM k env s1 r) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|]; reflexivity.
    + (* Minus *)
      rewrite (IH l env s).
      destruct (evalM k env s l) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH r env s1).
      destruct (evalM k env s1 r) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|]; reflexivity.
    + (* Mult *)
      rewrite (IH l env s).
      destruct (evalM k env s l) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH r env s1).
      destruct (evalM k env s1 r) as [[[a2|b2|i2 bd2 ce2|loc2] s2]|]; reflexivity.
    + (* Boolean *) reflexivity.
    + (* IsZero *)
      rewrite (IH e0 env s).
      destruct (evalM k env s e0) as [[[a|b|i bd ce|loc] s1]|]; reflexivity.
    + (* If *)
      rewrite (IH c env s).
      destruct (evalM k env s c) as [[[a|bb|i bd ce|loc] s1]|]; try reflexivity.
      destruct bb; cbn -[evalRS evalM].
      * rewrite (IH t env s1). reflexivity.
      * rewrite (IH f env s1). reflexivity.
    + (* Bind *)
      rewrite (IH ve env s).
      destruct (evalM k env s ve) as [[v1 s1]|]; try reflexivity.
      rewrite (IH be (extend i v1 env) s1). reflexivity.
    + (* Lambda *) reflexivity.
    + (* App *)
      rewrite (IH fe env s).
      destruct (evalM k env s fe) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH ae env s1).
      destruct (evalM k env s1 ae) as [[w s2]|]; try reflexivity.
      rewrite (IH bd (extend i w ce) s2). reflexivity.
    + (* Id *)
      destruct (lookup x env) as [v|]; reflexivity.
    + (* Seq *)
      rewrite (IH ae env s).
      destruct (evalM k env s ae) as [[v1 s1]|]; try reflexivity.
      rewrite (IH be env s1). reflexivity.
    + (* New *)
      rewrite (IH e0 env s).
      destruct (evalM k env s e0) as [[v1 s1]|]; reflexivity.
    + (* Deref *)
      rewrite (IH e0 env s).
      destruct (evalM k env s e0) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      destruct (nth_error s1 loc); reflexivity.
    + (* Assign *)
      rewrite (IH le env s).
      destruct (evalM k env s le) as [[[a|b|i bd ce|loc] s1]|]; try reflexivity.
      rewrite (IH re env s1).
      destruct (evalM k env s1 re) as [[w s2]|]; try reflexivity.
      destruct (update_at loc w s2); reflexivity.
Qed.

(**
 * The wrapper agrees too: running from the empty environment and store is
 * exactly the explicit [eval].
 *)
Corollary evalReaderState_agrees : forall e, evalReaderState e = eval e.
Proof. intro e. unfold evalReaderState, runRS, eval. apply evalRS_agrees. Qed.

(* ================================================================ *)
(* SECTION 6: MONAD LAWS AND EFFECT INTERACTION                   *)
(* ================================================================ *)

(**
 * LEFT IDENTITY holds by computation (and eta), as in the single-effect
 * monads.
 *)
Lemma left_id_RS : forall (A B : Type) (a : A) (f : A -> RS (Env RVal) Store B),
  bindRS (retRS a) f = f a.
Proof. reflexivity. Qed.

(**
 * The two effects are INDEPENDENT: reading the environment does not touch
 * the store, and vice versa.  [askRS] leaves the store alone, and a store
 * write is invisible to [askRS] - so [ask]-then-[get] and [get]-then-[ask]
 * observe the same environment and store.
 *)
Lemma ask_get_comm : forall (env : Env RVal) (s : Store),
  runRS (x <- askRS ;; y <- getRS ;; retRS (x, y)) env s = Some ((env, s), s).
Proof. reflexivity. Qed.

(**
 * LOCAL is scoped: extending the environment for a sub-computation does not
 * leak out, and it never affects the store.
 *)
Lemma local_scoped : forall (env : Env RVal) (s : Store) i (v : RVal),
  runRS (localRS (extend i v) askRS) env s = Some (extend i v env, s).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* SUMMARY                                                          *)
(* ================================================================ *)

(**
 * In this lecture we:
 *   1. Carried over the reference-cell language [FBAES] and its explicit
 *      interpreter [evalM], which threads BOTH the environment and the
 *      store by hand.
 *   2. Combined a READER (for the read-only environment) and a STATE (for
 *      the mutable store) into one monad [RS E S A = E -> S -> option (A*S)]
 *      with [askRS]/[localRS] and [getRS]/[putRS] over a shared [bindRS].
 *   3. Rebuilt the interpreter as [evalRS] carrying NEITHER resource
 *      explicitly - [askRS]/[localRS] handle the environment,
 *      [getRS]/[putRS] the store, [bindRS] threads both.
 *   4. Proved AGREEMENT [evalRS fuel e env s = evalM fuel env s e] in a
 *      single induction (corollary [evalReaderState_agrees] for the
 *      wrappers), and checked the monad laws / effect-independence.
 *
 * This is the culmination of the monad arc: RMon hid a context, SMon hid a
 * store, and here BOTH are hidden at once by stacking their operations in
 * one monad - the interpreter finally reads like a plain recursive
 * definition while every resource is threaded, provably, underneath.
 *)
