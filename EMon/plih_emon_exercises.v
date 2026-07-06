(**
Programming Languages in Rocq - Reader+Either Monad Exercises
Informative type errors - Student Problem Set

In these exercises you will:
#<ol>#
#<li>#Run the message-carrying checker [typeofE]/[typecheckE]#</li>#
#<li>#Use the REFINEMENT theorem relating it to the direct [typeof]#</li>#
#<li>#Verify small laws of the combined Reader+Either monad#</li>#
#</ol>#

HOW TO USE THIS FILE
--------------------
Each exercise ends in [Admitted].  Replace it with a real proof ending
in [Qed].  The file compiles as given.

From the lecture you have: [Ty]/[Ty_eqb], the terms [TFBAEC], the direct
checker [typeof]/[typecheck], the monad [RE]
([retE]/[bindE]/[askE]/[localE]/[throwE]/[runE] with [;;]), the checker
[typeofE]/[typecheckE], [forget], the theorems [typeofE_refines] and
[typecheckE_refines], and the sample term [inc].

Difficulty: ★ trivial, ★★ a lemma citation, ★★★ short proof.
Solutions are in plih_emon_solutions.v.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_emon_shared.
Require Import plih_emon_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: RUNNING THE MESSAGE-CARRYING CHECKER *)

(* ★ A good program succeeds with [inr <type>]. *)
Example ex1_ok : typecheckE (Bind "x" (Num 5) (IsZero (Id "x"))) = inr TBool.
Proof. Admitted.

(* ★ A mismatched [If] reports its message. *)
Example ex2_if_msg :
  typecheckE (If (Boolean true) (Num 1) (Boolean false))
  = inl "if: branches must have the same type".
Proof. Admitted.

(* ★ Applying a non-function reports its message. *)
Example ex3_app_msg :
  typecheckE (App (Num 1) (Num 2)) = inl "app: applying a non-function".
Proof. Admitted.

(** * PART 2: REFINEMENT OF THE DIRECT CHECKER *)

(* ★★ On a concrete term, forgetting the message recovers the direct
   checker's answer at every context.  Cite [typeofE_refines]. *)
Example ex4_refine_app : forall ctx,
  forget (typeofE (App inc (Num 4)) ctx) = typeof ctx (App inc (Num 4)).
Proof. Admitted.

(* ★★ At the top level, erasing the message recovers [typecheck]. *)
Example ex5_refine_top : forall e, forget (typecheckE e) = typecheck e.
Proof. Admitted.

(** * PART 3: MONAD LAWS *)

(* ★★ Left identity: binding a pure value just applies the function. *)
Example ex6_left_id : forall (E A B : Type) (a : A) (f : A -> RE E B),
  bindE (retE a) f = f a.
Proof. Admitted.

(* ★★ A thrown error SHORT-CIRCUITS: the continuation is skipped and the
   message propagates. *)
Example ex7_throw_short : forall (E A B : Type) (msg : string) (f : A -> RE E B),
  bindE (throwE msg) f = throwE msg.
Proof. Admitted.

(* ★ [askE] hands back the environment it is run in. *)
Example ex8_ask : forall (E : Type) (e : E), runE askE e = inr e.
Proof. Admitted.

(** * PART 4: CONCRETE SYNTAX *)

(**
The typed language gets TRec's two notations: types between [<[ ... ]>]
([Nat], [Bool], the right-associative [->]) and terms between
[<{ ... }>] with the ascribed lambda [lambda ID : T in body] and the
prefix [fix f].  Read the concrete terms through the MESSAGE-CARRYING
checker [typecheckE]: success on [inr], a descriptive message on [inl].
 *)

Open Scope emon_scope.

(* ★ the function arrow is right-associative. *)
Example ex9_parse_ty :
  <[ Nat -> Nat -> Nat ]> = TArr TNum (TArr TNum TNum).
Proof. Admitted.

(* ★★ a well-typed concrete program succeeds on the [inr] side. *)
Example ex10_typecheck_ok :
  typecheckE <{ (lambda "x" : Nat in "x" + 1) 4 }> = inr TNum.
Proof. Admitted.

(* ★★ a stuck concrete program lands on [inl] with a descriptive message. *)
Example ex11_typecheck_msg :
  typecheckE <{ if 1 then 2 else 3 }> = inl "if: condition must be a Boolean".
Proof. Admitted.
