(**
Programming Languages in Rocq - Untyped Recursion Lecture
Recursion via fixpoint combinators

The Func chapter left a cliffhanger: [omega] shows the language can
LOOP, but FBAE has no conditional, so recursion could never TEST its
argument and stop - nothing productive could be written.  This chapter
fixes that and delivers real recursion:
  1. FBAEC = FBAE + Booleans + [If]: the missing CONDITIONAL.
  2. A STRICT (call-by-value) closure interpreter [evalM], and a LAZY
     (call-by-name) interpreter [evalL] - both fuel-driven, as in Func.
  3. FUEL MONOTONICITY for the strict interpreter (the well-definedness
     metatheorem, carried over from Func with the new cases).
  4. RECURSION with NO new construct: the Y and Z fixpoint combinators
     as ordinary FBAEC terms.  Y is a parameterised [omega] that needs
     LAZY evaluation; Z eta-guards the self-application so it also works
     under STRICT evaluation.
  5. PRODUCTIVE examples that actually terminate: summation and
     factorial, computed by [Z] under [evalM] and by [Y] under [evalL].

This mirrors the "Untyped Recursion" unit of PLIH:
  https://ku-sldg.github.io/plih//funs/7-Untyped-Recursion.html
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_rec_shared.

Local Open Scope string_scope.
Import ListNotations.

(** * SECTION 1: SYNTAX - The FBAEC Language *)

(**
FBAEC ("FBAE + Conditionals") is the Func language extended with what
it was missing to make recursion useful:
  - [Boolean b] : a Boolean literal;
  - [IsZero e]  : the test that produces a Boolean from a number;
  - [If c t f]  : a CONDITIONAL - and crucially, it evaluates ONLY the
                  branch selected, so a recursive call in the untaken
                  branch is never made.  That is what lets recursion
                  bottom out.
We also add [Mult] so factorial has something to multiply with.
 *)
Inductive FBAEC : Type :=
| Num     : nat -> FBAEC
| Plus    : FBAEC -> FBAEC -> FBAEC
| Minus   : FBAEC -> FBAEC -> FBAEC
| Mult    : FBAEC -> FBAEC -> FBAEC
| Boolean : bool -> FBAEC
| IsZero  : FBAEC -> FBAEC
| If      : FBAEC -> FBAEC -> FBAEC -> FBAEC
| Bind    : string -> FBAEC -> FBAEC -> FBAEC
| Lambda  : string -> FBAEC -> FBAEC
| App     : FBAEC -> FBAEC -> FBAEC
| Id      : string -> FBAEC.

(** * SECTION 2: THE STRICT (CALL-BY-VALUE) INTERPRETER *)

(**
Values are numbers, Booleans, and closures - exactly Func's [FBAEVal]
plus [BoolV].  As in Func, a closure captures its definition-time
environment.
 *)
Inductive RVal : Type :=
| NumV     : nat -> RVal
| BoolV    : bool -> RVal
| ClosureV : string -> FBAEC -> list (string * RVal) -> RVal.

(**
The strict interpreter.  [Bind] and [App] evaluate the bound/argument
expression BEFORE the body (call-by-value); [If] evaluates its
condition and then only the chosen branch.  Fuel-driven, since the
language still diverges.
 *)
Fixpoint evalM (fuel : nat) (env : Env RVal) (e : FBAEC) : option RVal :=
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
      | Lambda i b => Some (ClosureV i b env)
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

(* A convenience wrapper with fuel generous enough for the recursive
   examples below.  As always there is no universally "right" default. *)
Definition eval (e : FBAEC) : option RVal := evalM 1000 nil e.

(** * SECTION 3: THE LAZY (CALL-BY-NAME) INTERPRETER *)

(**
The lazy interpreter, carried over from Func's [evalL] and extended
with the new arithmetic/conditional cases.  A bound name or argument
is stored UNEVALUATED as a thunk (expression + its environment) and
forced only when looked up.  Arithmetic, [IsZero], and [If]'s
condition still force their operands - you cannot branch on a thunk.
 *)
Inductive LThunk : Type :=
| Thk : FBAEC -> list (string * LThunk) -> LThunk.

Inductive LVal : Type :=
| LNumV  : nat -> LVal
| LBoolV : bool -> LVal
| LCloV  : string -> FBAEC -> list (string * LThunk) -> LVal.

Fixpoint evalL (fuel : nat) (env : Env LThunk) (e : FBAEC) : option LVal :=
  match fuel with
  | 0 => None
  | S k =>
      match e with
      | Num n => Some (LNumV n)
      | Plus l r =>
          match evalL k env l, evalL k env r with
          | Some (LNumV a), Some (LNumV b) => Some (LNumV (a + b))
          | _, _ => None
          end
      | Minus l r =>
          match evalL k env l, evalL k env r with
          | Some (LNumV a), Some (LNumV b) => Some (LNumV (a - b))
          | _, _ => None
          end
      | Mult l r =>
          match evalL k env l, evalL k env r with
          | Some (LNumV a), Some (LNumV b) => Some (LNumV (a * b))
          | _, _ => None
          end
      | Boolean b => Some (LBoolV b)
      | IsZero e0 =>
          match evalL k env e0 with
          | Some (LNumV n) => Some (LBoolV (Nat.eqb n 0))
          | _ => None
          end
      | If c t f =>
          match evalL k env c with
          | Some (LBoolV true)  => evalL k env t
          | Some (LBoolV false) => evalL k env f
          | _ => None
          end
      | Bind i v b =>
          (* the bound expression is NOT evaluated - just thunked *)
          evalL k (extend i (Thk v env) env) b
      | Lambda i b => Some (LCloV i b env)
      | App f a =>
          match evalL k env f with
          | Some (LCloV i b cenv) =>
              (* the ARGUMENT is thunked in the caller's env, unevaluated *)
              evalL k (extend i (Thk a env) cenv) b
          | _ => None
          end
      | Id x =>
          match lookup x env with
          | Some (Thk e' env') => evalL k env' e'   (* force on demand *)
          | None => None
          end
      end
  end.

Definition evalLazy (e : FBAEC) : option LVal := evalL 1000 nil e.

(** * SECTION 4: RUNNING THE BASICS *)

Example ev_arith : eval (Mult (Num 6) (Plus (Num 3) (Num 4))) = Some (NumV 42).
Proof. reflexivity. Qed.

Example ev_iszero_t : eval (IsZero (Num 0)) = Some (BoolV true).
Proof. reflexivity. Qed.

Example ev_iszero_f : eval (IsZero (Num 5)) = Some (BoolV false).
Proof. reflexivity. Qed.

(* [If] takes only the selected branch: the untaken branch is never run,
   even when it would be nonsense (here, adding a Boolean to a number). *)
Example ev_if_lazy_branch :
  eval (If (IsZero (Num 0)) (Num 1) (Plus (Boolean true) (Num 2)))
  = Some (NumV 1).
Proof. reflexivity. Qed.

Example evL_arith :
  evalLazy (Mult (Num 6) (Plus (Num 3) (Num 4))) = Some (LNumV 42).
Proof. reflexivity. Qed.

(** * SECTION 5: FUEL MONOTONICITY (STRICT INTERPRETER) *)

(**
As in Func, no measure bounds the fuel, so the well-definedness result
is MONOTONICITY: more fuel never changes an answer already produced.
The proof is Func's, with cases for [Mult], [Boolean], [IsZero], [If].
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

(** * SECTION 6: OMEGA AND THE FIXPOINT COMBINATORS *)

(**
[omega] is still here - self-application that loops - and still
diverges under strict evaluation.
 *)
Definition selfApp : FBAEC := Lambda "x" (App (Id "x") (Id "x")).
Definition omega : FBAEC := App selfApp selfApp.

Example omega_diverges : evalM 100 nil omega = None.
Proof. reflexivity. Qed.

(**
RECURSION is [omega] made useful: self-application PARAMETERISED by the
function to iterate.  A fixpoint combinator [fix] satisfies
[fix F ~> F (fix F)], so [F]'s recursive-call parameter is bound to
another copy of the recursion - definable as an ordinary term.

The Y combinator, Y = \f. (\x. f (x x)) (\x. f (x x)):
 *)
Definition Yc : FBAEC :=
  Lambda "f"
    (App (Lambda "x" (App (Id "f") (App (Id "x") (Id "x"))))
         (Lambda "x" (App (Id "f") (App (Id "x") (Id "x"))))).

(**
The Z combinator, Y with the self-application ETA-GUARDED behind a
lambda, Z = \f. (\x. f (\v. x x v)) (\x. f (\v. x x v)).  The delayed
[\v. x x v] is a VALUE, so strict evaluation can build the fixpoint
without looping.
 *)
Definition Zc : FBAEC :=
  Lambda "f"
    (App (Lambda "x" (App (Id "f")
            (Lambda "v" (App (App (Id "x") (Id "x")) (Id "v")))))
         (Lambda "x" (App (Id "f")
            (Lambda "v" (App (App (Id "x") (Id "x")) (Id "v")))))).

(** * SECTION 7: PRODUCTIVE RECURSION *)

(**
A recursive generator takes its own recursive call as parameter [g].
Summation, sum z = z + (z-1) + ... + 0, matching the PLIH chapter:

  sumGen = \g. \z. if z = 0 then z else z + (g (z-1))
 *)
Definition sumGen : FBAEC :=
  Lambda "g"
    (Lambda "z"
      (If (IsZero (Id "z"))
          (Id "z")
          (Plus (Id "z") (App (Id "g") (Minus (Id "z") (Num 1)))))).

(**
Under STRICT evaluation the Z combinator ties the knot and the
recursion RUNS to completion: sum 0..5 = 15.  This is the payoff the
Func chapter could not reach - real, terminating recursion.
 *)
Example sum_Z_strict :
  eval (App (App Zc sumGen) (Num 5)) = Some (NumV 15).
Proof. reflexivity. Qed.

(**
The plain Y combinator DIVERGES under strict evaluation - it is a
parameterised [omega], looping before any work (cf. Func's [recY]).
 *)
Example sum_Y_strict_diverges :
  evalM 100 nil (App (App Yc sumGen) (Num 5)) = None.
Proof. reflexivity. Qed.

(**
But under LAZY (call-by-name) evaluation the eta-guard is unnecessary:
the plain Y combinator computes the same answer, 15.  Strict needs Z;
lazy runs Y directly - the classic strict/lazy split for recursion.
 *)
Example sum_Y_lazy :
  evalLazy (App (App Yc sumGen) (Num 5)) = Some (LNumV 15).
Proof. reflexivity. Qed.

(**
The canonical example: factorial, fact z = z * (z-1) * ... * 1.

  factGen = \g. \z. if z = 0 then 1 else z * (g (z-1))
 *)
Definition factGen : FBAEC :=
  Lambda "g"
    (Lambda "z"
      (If (IsZero (Id "z"))
          (Num 1)
          (Mult (Id "z") (App (Id "g") (Minus (Id "z") (Num 1)))))).

Example fact_Z_strict :
  eval (App (App Zc factGen) (Num 5)) = Some (NumV 120).
Proof. reflexivity. Qed.

Example fact_Y_lazy :
  evalLazy (App (App Yc factGen) (Num 5)) = Some (LNumV 120).
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
  1. Extended FBAE to FBAEC with Booleans, [IsZero], and a CONDITIONAL
     [If] that evaluates only the selected branch - the ingredient the
     Func chapter lacked, which lets recursion bottom out.
  2. Gave a STRICT closure interpreter [evalM] and a LAZY interpreter
     [evalL], both fuel-driven, and proved FUEL MONOTONICITY for [evalM].
  3. Encoded recursion with NO new construct: the Y and Z fixpoint
     combinators as ordinary FBAEC terms.
  4. Ran PRODUCTIVE recursion to real answers: summation (0..5 = 15)
     and factorial (5! = 120), with Z under strict [evalM] and Y under
     lazy [evalL], while strict Y diverges.

The catch: [omega] and [Y] show the untyped language is still Turing
powerful, so [evalM] is inescapably PARTIAL (the fuel can run out).
Next: TYPES rule out the stuck/divergent programs - but, as the Typed
Recursion chapter shows, recursion must then be put BACK deliberately
with a typed [fix], because the combinators stop type-checking.
 *)
