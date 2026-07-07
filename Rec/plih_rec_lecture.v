(** * Programming Languages in Rocq - Untyped Recursion *)

(**
The Func chapter left a cliffhanger: [omega] shows the language can
_loop_, but FBAE has no conditional, so recursion could never _test_ its
argument and stop - nothing productive could be written.  This chapter
fixes that and delivers real recursion:
#<ol>#
#<li>#FBAEC = FBAE + Booleans + [If]: the missing _conditional_.#</li>#
#<li>#A _strict_ (call-by-value) closure interpreter [evalM], and a _lazy_ (call-by-name) interpreter [evalL] - both fuel-driven, as in Func.#</li>#
#<li>#_Fuel monotonicity_ for the strict interpreter (the well-definedness metatheorem, carried over from Func with the new cases).#</li>#
#<li>#Recursion with _no new construct_: the Y and Z fixpoint combinators as ordinary FBAEC terms.  Y needs _lazy_ evaluation; Z eta-guards the self-application so it also works under _strict_ evaluation.#</li>#
#<li>#_Productive_ examples that actually terminate: summation and factorial, computed by Z under [evalM] and by Y under [evalL].#</li>#
#</ol>#

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
  - [If c t f]  : a _conditional_ - crucially, it evaluates _only_ the
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
expression _before_ the body (call-by-value); [If] evaluates its
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
is stored _unevaluated_ as a thunk (expression + its environment) and
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
              (* the argument is thunked in the caller's env, unevaluated *)
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

(**
A few sanity-check examples to confirm the new forms work before we
build the recursive combinators on top of them.
 *)

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
is _monotonicity_: more fuel never changes an answer already produced.
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
_Recursion_ is [omega] made useful: self-application _parameterised_ by the
function to iterate.  A fixpoint combinator [fix] satisfies
[fix F ~> F (fix F)], so [F]'s recursive-call parameter is bound to
another copy of the recursion - definable as an ordinary term.

The Y combinator:
<<
  Y = lambda f in (lambda x in f (x x)) (lambda x in f (x x))
>>
 *)
Definition Yc : FBAEC :=
  Lambda "f"
    (App (Lambda "x" (App (Id "f") (App (Id "x") (Id "x"))))
         (Lambda "x" (App (Id "f") (App (Id "x") (Id "x"))))).

(**
The Z combinator, Y with the self-application _eta-guarded_ behind a lambda:
<<
  Z = lambda f in (lambda x in f (lambda v in x x v))
                  (lambda x in f (lambda v in x x v))
>>
The delayed [lambda v in x x v] is a _value_, so strict evaluation can build
the fixpoint without looping.
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

  sumGen = lambda g in lambda z in
             if iszero z then z else z + g (z - 1)
 *)
Definition sumGen : FBAEC :=
  Lambda "g"
    (Lambda "z"
      (If (IsZero (Id "z"))
          (Id "z")
          (Plus (Id "z") (App (Id "g") (Minus (Id "z") (Num 1)))))).

(**
Under _strict_ evaluation the Z combinator ties the knot and the
recursion _runs_ to completion: sum 0..5 = 15.  This is the payoff the
Func chapter could not reach - real, terminating recursion.
 *)
Example sum_Z_strict :
  eval (App (App Zc sumGen) (Num 5)) = Some (NumV 15).
Proof. reflexivity. Qed.

(**
The plain Y combinator _diverges_ under strict evaluation - it is a
parameterised [omega], looping before any work.
 *)
Example sum_Y_strict_diverges :
  evalM 100 nil (App (App Yc sumGen) (Num 5)) = None.
Proof. reflexivity. Qed.

(**
But under _lazy_ (call-by-name) evaluation the eta-guard is unnecessary:
the plain Y combinator computes the same answer, 15.  Strict needs Z;
lazy runs Y directly - the classic strict/lazy split for recursion.
 *)
Example sum_Y_lazy :
  evalLazy (App (App Yc sumGen) (Num 5)) = Some (LNumV 15).
Proof. reflexivity. Qed.

(**
The canonical example: factorial, fact z = z * (z-1) * ... * 1.

  factGen = lambda g in lambda z in
              if iszero z then 1 else z * g (z - 1)
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

(** * SECTION 8: CONCRETE SYNTAX - A NOTATION PARSER *)

(**
FBAEC keeps the whole FBAE surface syntax and adds four forms, so it
needs its _own_ parser (the notation is tied to the FBAEC type, not
FBAE's).  It is Func's grammar - numerals/identifiers via coercion,
[+]/[-], [bind ID = e1 in e2], [lambda ID in body], and application by
_juxtaposition_ [f a] - extended with multiplication [*], the Boolean
literals [true]/[false], the numeric test [iszero e], and the
conditional [if c then t else f].
 *)

Coercion Num : nat >-> FBAEC.
Coercion Id  : string >-> FBAEC.

Declare Custom Entry fbaec.
Declare Scope fbaec_scope.
Delimit Scope fbaec_scope with fbaec.

Notation "<{ e }>" := e (e custom fbaec at level 99) : fbaec_scope.
Notation "( x )" := x (in custom fbaec, x at level 99) : fbaec_scope.
Notation "x" := x (in custom fbaec at level 0, x constr at level 0) : fbaec_scope.

(**
Precedence, tightest to loosest: application (1), [*] (40), [+]/[-]
(50), [iszero] (75), then the [if]/[bind]/[lambda] binders.  So
[iszero z] in [z * g (z-1)] and [z + g (z-1)] all group the way the
recursive generators below expect.
 *)

Notation "f x" := (App f x) (in custom fbaec at level 1, left associativity) : fbaec_scope.
Notation "'iszero' x" := (IsZero x) (in custom fbaec at level 75, right associativity) : fbaec_scope.
Notation "x * y" := (Mult x y)  (in custom fbaec at level 40, left associativity) : fbaec_scope.
Notation "x + y" := (Plus x y)  (in custom fbaec at level 50, left associativity) : fbaec_scope.
Notation "x - y" := (Minus x y) (in custom fbaec at level 50, left associativity) : fbaec_scope.
Notation "'true'"  := (Boolean true)  (in custom fbaec at level 0) : fbaec_scope.
Notation "'false'" := (Boolean false) (in custom fbaec at level 0) : fbaec_scope.
Notation "'if' c 'then' t 'else' f" := (If c t f)
  (in custom fbaec at level 89, c custom fbaec at level 99,
   t custom fbaec at level 99, f custom fbaec at level 99) : fbaec_scope.
Notation "'lambda' v 'in' e" := (Lambda v e)
  (in custom fbaec at level 90, v constr at level 0, e custom fbaec at level 99) : fbaec_scope.
Notation "'bind' v '=' e1 'in' e2" := (Bind v e1 e2)
  (in custom fbaec at level 89, v constr at level 0,
   e1 custom fbaec at level 99, e2 custom fbaec at level 99) : fbaec_scope.

Open Scope fbaec_scope.

(**
As always the notation is only sugar, so every parse is [reflexivity].
 *)

Example parse_arith : <{ 6 * (3 + 4) }> = Mult (Num 6) (Plus (Num 3) (Num 4)).
Proof. reflexivity. Qed.

Example parse_iszero : <{ iszero 0 }> = IsZero (Num 0).
Proof. reflexivity. Qed.

Example parse_if :
  <{ if iszero 0 then 1 else true + 2 }>
  = If (IsZero (Num 0)) (Num 1) (Plus (Boolean true) (Num 2)).
Proof. reflexivity. Qed.

(**
The real payoff is _readability_ of the recursive generators.  Here are
[sumGen] and [factGen] from Section 7, written the way the chapter
states them on paper.
 *)

Example sumGen_concrete :
  <{ lambda "g" in lambda "z" in
       if iszero "z" then "z" else "z" + "g" ("z" - 1) }> = sumGen.
Proof. reflexivity. Qed.

Example factGen_concrete :
  <{ lambda "g" in lambda "z" in
       if iszero "z" then 1 else "z" * "g" ("z" - 1) }> = factGen.
Proof. reflexivity. Qed.

(**
Because the fixpoint combinators [Yc]/[Zc] and the generators are
ordinary FBAEC terms, they are just names inside the brackets, applied
by juxtaposition.  The productive-recursion runs from Section 7 read as
plainly as [Z sumGen 5].
 *)

Example sum_Z_concrete : eval <{ Zc sumGen 5 }> = Some (NumV 15).
Proof. reflexivity. Qed.

Example fact_Z_concrete : eval <{ Zc factGen 5 }> = Some (NumV 120).
Proof. reflexivity. Qed.

Example fact_Y_lazy_concrete : evalLazy <{ Yc factGen 5 }> = Some (LNumV 120).
Proof. reflexivity. Qed.

(** * SUMMARY *)

(**
In this lecture we:
#<ol>#
#<li>#Extended FBAE to FBAEC with Booleans, [IsZero], and a _conditional_ [If] that evaluates only the selected branch - the ingredient the Func chapter lacked, which lets recursion bottom out.#</li>#
#<li>#Gave a _strict_ closure interpreter [evalM] and a _lazy_ interpreter [evalL], both fuel-driven, and proved _fuel monotonicity_ for [evalM].#</li>#
#<li>#Encoded recursion with _no new construct_: the Y and Z fixpoint combinators as ordinary FBAEC terms.#</li>#
#<li>#Ran _productive_ recursion to real answers: summation (0..5 = 15) and factorial (5! = 120), with Z under strict [evalM] and Y under lazy [evalL], while strict Y diverges.#</li>#
#<li>#Added _concrete syntax_ (its own parser, since FBAEC is a new type): Func's grammar plus [*], [true]/[false], [iszero e], and [if c then t else f], so [sumGen]/[factGen] read as on paper.#</li>#
#</ol>#

The catch: [omega] and [Y] show the untyped language is still Turing
powerful, so [evalM] is inescapably _partial_ (the fuel can run out).
Next: types rule out the stuck/divergent programs - but, as the Typed
Recursion chapter shows, recursion must then be put _back_ deliberately
with a typed [fix], because the combinators stop type-checking.
 *)

(** * NEW PROOF TACTICS IN THIS CHAPTER *)

(**
This chapter introduces no new proof tactics.  The [evalM_mono] proof
uses the same patterns established in Func: [discriminate], [ltac:(lia)],
[try discriminate], [destruct ... eqn:E], and [exact].  The extra
constructor cases ([Mult], [Boolean], [IsZero], [If]) follow the same
template as [Plus]/[Minus]/[App].

See Func's "New Proof Tactics" section for a full glossary of all tactics
used here.
 *)
