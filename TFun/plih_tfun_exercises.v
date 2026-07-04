(**
Programming Languages in Rocq - Typed Functions Exercises
A static type system for the functional language - Student Problem Set

In these exercises you will:
  1. Run the TYPE CHECKER [typeof]/[typecheck]: accept good programs,
     reject the classic stuck terms (including self-application)
  2. Run the STRICT interpreter [evalM]/[eval]
  3. Connect the two - TYPE SOUNDNESS in miniature - and use the
     metatheory ([Ty_eqb] correctness, fuel monotonicity, canonical
     forms)

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: the types [Ty] ([TNum]/[TBool]/[TArr]) with
[Ty_eqb] (and [Ty_eqb_refl]/[Ty_eqb_eq]); the term language [TFBAEC];
the checker [typeof]/[typecheck]; the values [TVal]
([NumV]/[BoolV]/[ClosureV]); the strict interpreter [evalM]/[eval];
[evalM_mono]; the predicates [isNumV]/[isBoolV]; and the sample terms
[inc]/[selfApp].  [lookup]/[extend] come from the shared library.

NOTE ON FUEL.  Keep fuel a VARIABLE whenever the term is abstract - a
literal fuel forces the kernel to unroll [evalM] and can blow up.  A
literal fuel is fine only on a CONCRETE closed term.

Difficulty: [*] trivial, [**] a lemma citation, [***] short proof.
Solutions are in plih_tfun_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_tfun_shared.
Require Import plih_tfun_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: THE TYPE CHECKER - ACCEPTING AND REJECTING *)

(* [*] A well-typed arithmetic term has type [TNum]. *)
Example ex1_ty_arith :
  typecheck (Mult (Num 6) (Plus (Num 3) (Num 4))) = Some TNum.
Proof. Admitted.

(* [*] A lambda whose parameter is a Boolean has a function type. *)
Example ex2_ty_lambda :
  typecheck (Lambda "x" TBool (If (Id "x") (Num 1) (Num 2)))
  = Some (TArr TBool TNum).
Proof. Admitted.

(* [*] A non-Boolean condition is rejected. *)
Example ex3_reject_if_cond :
  typecheck (If (Num 0) (Num 1) (Num 2)) = None.
Proof. Admitted.

(* [*] Argument type mismatch: [inc] wants a Nat, given a Boolean. *)
Example ex4_reject_argtype :
  typecheck (App inc (Boolean true)) = None.
Proof. Admitted.

(* [*] Self-application does not type-check at ANY parameter type - this
   is why [omega] (and the Y/Z combinators) are gone. *)
Example ex5_reject_selfApp :
  typecheck (selfApp (TArr TNum TNum)) = None.
Proof. Admitted.

(** * PART 2: THE STRICT INTERPRETER *)

(* [*] Applying [inc] to 41 evaluates to 42. *)
Example ex6_eval_app : eval (App inc (Num 41)) = Some (NumV 42).
Proof. Admitted.

(* [*] [If] with a true condition takes the then-branch. *)
Example ex7_eval_if :
  eval (If (IsZero (Num 0)) (Boolean true) (Boolean false))
  = Some (BoolV true).
Proof. Admitted.

(* [*] A lambda evaluates to a closure capturing the current environment
   (the parameter type is dropped at run time). *)
Example ex8_eval_lambda : forall k env i t b,
  evalM (S k) env (Lambda i t b) = Some (ClosureV i b env).
Proof. Admitted.

(** * PART 3: METATHEORY *)

(* [**] Type equality is sound: cite [Ty_eqb_eq]. *)
Example ex9_ty_eqb_sound : forall a b,
  Ty_eqb a b = true -> a = b.
Proof. Admitted.

(* [**] Adding fuel cannot change an answer.  Cite [evalM_mono].  Keep the
   fuel a VARIABLE - do not instantiate it to a literal. *)
Example ex10_more_fuel : forall f env e v,
  evalM f env e = Some v -> evalM (S f) env e = Some v.
Proof. Admitted.

(* [***] CANONICAL FORMS (multiplication): whenever [Mult a b] produces a
   value, that value is a number.  Model your proof on the lecture's
   [plus_yields_num]. *)
Example ex11_mult_yields_num : forall f env a b v,
  evalM f env (Mult a b) = Some v -> isNumV v = true.
Proof. Admitted.

(* [***] The strict interpreter is deterministic for fixed fuel. *)
Example ex12_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. Admitted.

(** * CHALLENGE PROBLEMS *)

(* PROVIDED: [twice f x] applies a Nat->Nat function twice. *)
Definition twice : TFBAEC :=
  Lambda "f" (TArr TNum TNum)
    (Lambda "x" TNum (App (Id "f") (App (Id "f") (Id "x")))).

(* [**] [twice] takes a Nat->Nat function and returns a Nat->Nat function. *)
Example challenge1_twice_ty :
  typecheck twice = Some (TArr (TArr TNum TNum) (TArr TNum TNum)).
Proof. Admitted.

(* [**] Soundness in miniature: [twice inc 5] type-checks at [TNum] AND
   evaluates to the [NumV] the type predicts (inc applied twice to 5). *)
Example challenge2_twice_ty :
  typecheck (App (App twice inc) (Num 5)) = Some TNum.
Proof. Admitted.

Example challenge2_twice_eval :
  eval (App (App twice inc) (Num 5)) = Some (NumV 7).
Proof. Admitted.
