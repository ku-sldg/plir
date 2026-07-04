(**
Programming Languages in Rocq - Reader+State+Either Monad Lecture
Stacking three effects: environment, store, and error messages

RSMon hid the environment (Reader) and the store (State) in one monad,
but failure was still silent - a wrong program just returned [None].
EMon showed how an EITHER layer turns that [None] into a descriptive
error MESSAGE, and that the message is "added information": forgetting it
recovers the plain answer.  This chapter is the capstone that stacks all
three effects in one monad:
  - the environment is read with [askRSE] / extended with [localRSE];
  - the store is read with [getRSE] / replaced with [putRSE];
  - failure raises a descriptive message with [throwRSE];
  - [bindRSE] threads the environment and store AND short-circuits on the
    first error.

The plan:
  1. The language [FBAES] and the explicit interpreter [evalM] (option
     valued, threading env and store by hand) - the reference.
  2. The combined monad [RSE E S A = E -> S -> sum string (A * S)] with
     [retRSE]/[bindRSE]/[askRSE]/[localRSE]/[getRSE]/[putRSE]/[throwRSE].
  3. The MONADIC interpreter [evalRSE], raising descriptive messages.
  4. REFINEMENT: [forget (evalRSE fuel e env s) = evalM fuel env s e] -
     the messages are extra information, not changed behavior.

This mirrors the effect-combining ("monad transformer") idea of PLIH:
  https://ku-sldg.github.io/plih//state/
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rsemon_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: THE LANGUAGE AND THE REFERENCE INTERPRETER *)

(**
[FBAES], values [RVal] (with locations [LocV]), the [Store], and the
explicit interpreter [evalM] are carried over from the State chapter -
option valued, threading BOTH env and store by hand.  [evalM] is the
reference the refined interpreter must match after erasing messages.
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

(** * SECTION 2: THE READER + STATE + EITHER MONAD *)

(**
Three effects in one type: given an environment [E] and a store [S], a
computation either raises an error MESSAGE ([inl : string]) or succeeds
with a value and the updated store ([inr : A * S]).

  RSE E S A := E -> S -> sum string (A * S)

READER: [askRSE] reads the environment, [localRSE g m] runs [m] under a
modified one.  STATE: [getRSE] reads the store, [putRSE] replaces it.
EITHER: [throwRSE msg] raises a message, and [bindRSE] SHORT-CIRCUITS on
the first [inl] while threading env and store through the [inr] path.
 *)
Definition RSE (E S A : Type) : Type := E -> S -> sum string (A * S).

Definition retRSE {E S A : Type} (a : A) : RSE E S A :=
  fun _ s => inr (a, s).

Definition bindRSE {E S A B : Type} (m : RSE E S A) (f : A -> RSE E S B) : RSE E S B :=
  fun e s => match m e s with
             | inr (a, s') => f a e s'
             | inl msg => inl msg
             end.

Definition askRSE {E S : Type} : RSE E S E :=
  fun e s => inr (e, s).

Definition localRSE {E S A : Type} (g : E -> E) (m : RSE E S A) : RSE E S A :=
  fun e s => m (g e) s.

Definition getRSE {E S : Type} : RSE E S S :=
  fun _ s => inr (s, s).

Definition putRSE {E S : Type} (s' : S) : RSE E S unit :=
  fun _ _ => inr (tt, s').

Definition throwRSE {E S A : Type} (msg : string) : RSE E S A :=
  fun _ _ => inl msg.

Definition runRSE {E S A : Type} (m : RSE E S A) (e : E) (s : S)
  : sum string (A * S) := m e s.

Notation "x <- m ;; k" := (bindRSE m (fun x => k))
  (at level 61, m at next level, right associativity).

(**
[forget] erases the error message, turning the [Either] answer back into
the option-valued answer of [evalM]: an [inl] message becomes [None] and
an [inr] result becomes [Some].
 *)
Definition forget {X : Type} (r : sum string X) : option X :=
  match r with
  | inr a => Some a
  | inl _ => None
  end.

(** * SECTION 3: THE MONADIC INTERPRETER *)

(**
The interpreter over the three-effect monad.  It carries neither the
environment nor the store, and instead of failing silently it raises a
DESCRIPTIVE message at every stuck point.  Running out of fuel is itself
reported as an error.
 *)
Fixpoint evalRSE (fuel : nat) (e : FBAES) : RSE (Env RVal) Store RVal :=
  match fuel with
  | 0 => throwRSE "out of fuel"
  | S k =>
      match e with
      | Num n => retRSE (NumV n)
      | Plus l r =>
          a <- evalRSE k l ;;
          match a with
          | NumV x => b <- evalRSE k r ;;
                      match b with
                      | NumV y => retRSE (NumV (x + y))
                      | _ => throwRSE "plus: operands must be numbers"
                      end
          | _ => throwRSE "plus: operands must be numbers"
          end
      | Minus l r =>
          a <- evalRSE k l ;;
          match a with
          | NumV x => b <- evalRSE k r ;;
                      match b with
                      | NumV y => retRSE (NumV (x - y))
                      | _ => throwRSE "minus: operands must be numbers"
                      end
          | _ => throwRSE "minus: operands must be numbers"
          end
      | Mult l r =>
          a <- evalRSE k l ;;
          match a with
          | NumV x => b <- evalRSE k r ;;
                      match b with
                      | NumV y => retRSE (NumV (x * y))
                      | _ => throwRSE "mult: operands must be numbers"
                      end
          | _ => throwRSE "mult: operands must be numbers"
          end
      | Boolean b => retRSE (BoolV b)
      | IsZero e0 =>
          a <- evalRSE k e0 ;;
          match a with
          | NumV n => retRSE (BoolV (Nat.eqb n 0))
          | _ => throwRSE "isZero: operand must be a number"
          end
      | If c t f =>
          a <- evalRSE k c ;;
          match a with
          | BoolV b => if b then evalRSE k t else evalRSE k f
          | _ => throwRSE "if: condition must be a Boolean"
          end
      | Bind i v b =>
          a <- evalRSE k v ;;
          localRSE (extend i a) (evalRSE k b)
      | Lambda i b =>
          env <- askRSE ;;
          retRSE (ClosureV i b env)
      | App f a =>
          g <- evalRSE k f ;;
          match g with
          | ClosureV i b cenv =>
              w <- evalRSE k a ;;
              localRSE (fun _ => extend i w cenv) (evalRSE k b)
          | _ => throwRSE "app: applying a non-function"
          end
      | Id x =>
          env <- askRSE ;;
          match lookup x env with
          | Some v => retRSE v
          | None => throwRSE "unbound identifier"
          end
      | Seq a b =>
          _ <- evalRSE k a ;;
          evalRSE k b
      | New e0 =>
          v <- evalRSE k e0 ;;
          s0 <- getRSE ;;
          _ <- putRSE (s0 ++ [v])%list ;;
          retRSE (LocV (length s0))
      | Deref e0 =>
          a <- evalRSE k e0 ;;
          match a with
          | LocV n =>
              s0 <- getRSE ;;
              match nth_error s0 n with
              | Some w => retRSE w
              | None => throwRSE "deref: location out of range"
              end
          | _ => throwRSE "deref: not a location"
          end
      | Assign l r =>
          a <- evalRSE k l ;;
          match a with
          | LocV n =>
              w <- evalRSE k r ;;
              s0 <- getRSE ;;
              match update_at n w s0 with
              | Some s' => _ <- putRSE s' ;; retRSE w
              | None => throwRSE "assign: location out of range"
              end
          | _ => throwRSE "assign: not a location"
          end
      end
  end.

Definition evalRSErr (e : FBAES) : sum string (RVal * Store) :=
  runRSE (evalRSE 1000 e) nil nil.

(** * SECTION 4: RUNNING THE MONADIC INTERPRETER *)

(* Successes carry the value and store on the [inr] side. *)
Example evRSE_arith :
  evalRSErr (Mult (Num 6) (Plus (Num 3) (Num 4))) = inr (NumV 42, nil).
Proof. reflexivity. Qed.

Example evRSE_roundtrip :
  evalRSErr (Bind "r" (New (Num 0))
               (Seq (Assign (Id "r") (Num 7))
                    (Deref (Id "r"))))
  = inr (NumV 7, [NumV 7]).
Proof. reflexivity. Qed.

(* Failures now carry a DESCRIPTIVE message on the [inl] side. *)
Example evRSE_unbound :
  evalRSErr (Id "x") = inl "unbound identifier".
Proof. reflexivity. Qed.

Example evRSE_type_error :
  evalRSErr (Plus (Boolean true) (Num 1)) = inl "plus: operands must be numbers".
Proof. reflexivity. Qed.

Example evRSE_not_a_location :
  evalRSErr (Deref (Num 0)) = inl "deref: not a location".
Proof. reflexivity. Qed.

Example evRSE_apply_nonfunction :
  evalRSErr (App (Num 1) (Num 2)) = inl "app: applying a non-function".
Proof. reflexivity. Qed.

(* And [forget] recovers exactly the explicit [eval] on each. *)
Example evRSE_forget_ok :
  forget (evalRSErr (Mult (Num 6) (Plus (Num 3) (Num 4))))
  = eval (Mult (Num 6) (Plus (Num 3) (Num 4))).
Proof. reflexivity. Qed.

Example evRSE_forget_bad :
  forget (evalRSErr (Id "x")) = eval (Id "x").
Proof. reflexivity. Qed.

(** * SECTION 5: REFINEMENT - THE HEADLINE *)

(**
The three-effect interpreter REFINES the explicit one: forgetting the
error message recovers exactly [evalM]'s option-valued answer.  The
messages are added information, not changed behavior.  The proof is by
induction on fuel; each case rewrites the [evalM] side BACKWARDS with the
inductive hypothesis to expose [forget (evalRSE ...)], then splits the
[sum] result - [inl] (error/out-of-fuel) forgets to [None], [inr]
carries the value and store that line up with [evalM].
 *)
Theorem evalRSE_refines : forall fuel e env s,
  forget (evalRSE fuel e env s) = evalM fuel env s e.
Proof.
  induction fuel as [| k IH]; intros e env s.
  - reflexivity.
  - destruct e as
      [ n | l r | l r | l r | b | e0 | c t f | i ve be | i be
      | fe ae | x | ae be | e0 | e0 | le re ];
      cbn [evalRSE evalM];
      cbv beta iota delta [retRSE bindRSE askRSE localRSE getRSE putRSE throwRSE].
    + (* Num *) reflexivity.
    + (* Plus *)
      rewrite <- (IH l env s).
      destruct (evalRSE k l env s) as [msg | [[a|b|i bd ce|loc] s1]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH r env s1).
      destruct (evalRSE k r env s1) as [m2 | [[a2|b2|i2 bd2 ce2|loc2] s2]];
        cbn [forget]; reflexivity.
    + (* Minus *)
      rewrite <- (IH l env s).
      destruct (evalRSE k l env s) as [msg | [[a|b|i bd ce|loc] s1]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH r env s1).
      destruct (evalRSE k r env s1) as [m2 | [[a2|b2|i2 bd2 ce2|loc2] s2]];
        cbn [forget]; reflexivity.
    + (* Mult *)
      rewrite <- (IH l env s).
      destruct (evalRSE k l env s) as [msg | [[a|b|i bd ce|loc] s1]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH r env s1).
      destruct (evalRSE k r env s1) as [m2 | [[a2|b2|i2 bd2 ce2|loc2] s2]];
        cbn [forget]; reflexivity.
    + (* Boolean *) reflexivity.
    + (* IsZero *)
      rewrite <- (IH e0 env s).
      destruct (evalRSE k e0 env s) as [msg | [[a|b|i bd ce|loc] s1]];
        cbn [forget]; reflexivity.
    + (* If *)
      rewrite <- (IH c env s).
      destruct (evalRSE k c env s) as [msg | [[a|bb|i bd ce|loc] s1]];
        cbn [forget]; try reflexivity.
      destruct bb.
      * rewrite <- (IH t env s1). reflexivity.
      * rewrite <- (IH f env s1). reflexivity.
    + (* Bind *)
      rewrite <- (IH ve env s).
      destruct (evalRSE k ve env s) as [msg | [v1 s1]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH be (extend i v1 env) s1). reflexivity.
    + (* Lambda *) reflexivity.
    + (* App *)
      rewrite <- (IH fe env s).
      destruct (evalRSE k fe env s) as [msg | [[a|b|i bd ce|loc] s1]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH ae env s1).
      destruct (evalRSE k ae env s1) as [m2 | [w s2]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH bd (extend i w ce) s2). reflexivity.
    + (* Id *)
      destruct (lookup x env) as [v|]; cbn [forget]; reflexivity.
    + (* Seq *)
      rewrite <- (IH ae env s).
      destruct (evalRSE k ae env s) as [msg | [v1 s1]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH be env s1). reflexivity.
    + (* New *)
      rewrite <- (IH e0 env s).
      destruct (evalRSE k e0 env s) as [msg | [v1 s1]];
        cbn [forget]; reflexivity.
    + (* Deref *)
      rewrite <- (IH e0 env s).
      destruct (evalRSE k e0 env s) as [msg | [[a|b|i bd ce|loc] s1]];
        cbn [forget]; try reflexivity.
      destruct (nth_error s1 loc); reflexivity.
    + (* Assign *)
      rewrite <- (IH le env s).
      destruct (evalRSE k le env s) as [msg | [[a|b|i bd ce|loc] s1]];
        cbn [forget]; try reflexivity.
      rewrite <- (IH re env s1).
      destruct (evalRSE k re env s1) as [m2 | [w s2]];
        cbn [forget]; try reflexivity.
      destruct (update_at loc w s2); reflexivity.
Qed.

(**
The wrapper refines too: forgetting the message recovers the explicit
[eval].
 *)
Corollary evalRSErr_refines : forall e, forget (evalRSErr e) = eval e.
Proof. intro e. unfold evalRSErr, runRSE, eval. apply evalRSE_refines. Qed.

(** * SECTION 6: MONAD LAWS AND THE THREE CHANNELS *)

(**
LEFT IDENTITY holds by computation, as in every monad here.
 *)
Lemma left_id_RSE : forall (A B : Type) (a : A) (f : A -> RSE (Env RVal) Store B),
  bindRSE (retRSE a) f = f a.
Proof. reflexivity. Qed.

(**
The EITHER channel short-circuits: once a message is raised, the rest of
the computation is skipped.
 *)
Lemma throw_short_circuits :
  forall (B : Type) (msg : string) (f : RVal -> RSE (Env RVal) Store B),
    bindRSE (throwRSE msg) f = throwRSE msg.
Proof. reflexivity. Qed.

(**
The three channels are independent: a single computation can observe the
environment ([askRSE]), read the store ([getRSE]), and still succeed -
each effect leaves the others untouched.
 *)
Lemma channels_independent : forall (env : Env RVal) (s : Store),
  runRSE (x <- askRSE ;; y <- getRSE ;; retRSE (x, y)) env s
  = inr ((env, s), s).
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
  1. Carried over [FBAES] and the explicit option-valued interpreter
     [evalM] as the reference.
  2. Stacked THREE effects in one monad
     [RSE E S A = E -> S -> sum string (A * S)]: Reader
     ([askRSE]/[localRSE]) for the environment, State
     ([getRSE]/[putRSE]) for the store, and Either ([throwRSE], with
     [bindRSE] short-circuiting) for descriptive error messages.
  3. Rebuilt the interpreter as [evalRSE], carrying no resource by hand
     and raising a descriptive message at every stuck point (including
     running out of fuel).
  4. Proved REFINEMENT [forget (evalRSE fuel e env s) = evalM fuel env s e]
     (corollary [evalRSErr_refines] for the wrappers): the messages add
     information without changing behavior.

This is the capstone of the monad arc.  Reader (RMon) hid a context,
Either (EMon) added messages, State (SMon) hid a store, RSMon combined
two effects, and here THREE effects share one [bindRSE] - each effect
contributing its own operations while the interpreter reads like a plain
recursive definition.  That is exactly what monad transformers buy you.
 *)
