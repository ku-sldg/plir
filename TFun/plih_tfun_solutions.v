(**
 * Programming Languages in Rocq - Typed Functions Solutions
 * Complete solutions to plih_tfun_exercises.v
 *
 * The types [Ty]/[Ty_eqb], the term language [TFBAEC], the checker
 * [typeof]/[typecheck], the strict interpreter [evalM]/[eval], the
 * metatheorem [evalM_mono], the predicates [isNumV]/[isBoolV], and the
 * sample terms [inc]/[selfApp] all come from the Typed Functions lecture.
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

(* ================================================================ *)
(* PART 1: THE TYPE CHECKER - ACCEPTING AND REJECTING              *)
(* ================================================================ *)

Example ex1_ty_arith :
  typecheck (Mult (Num 6) (Plus (Num 3) (Num 4))) = Some TNum.
Proof. reflexivity. Qed.

Example ex2_ty_lambda :
  typecheck (Lambda "x" TBool (If (Id "x") (Num 1) (Num 2)))
  = Some (TArr TBool TNum).
Proof. reflexivity. Qed.

Example ex3_reject_if_cond :
  typecheck (If (Num 0) (Num 1) (Num 2)) = None.
Proof. reflexivity. Qed.

Example ex4_reject_argtype :
  typecheck (App inc (Boolean true)) = None.
Proof. reflexivity. Qed.

Example ex5_reject_selfApp :
  typecheck (selfApp (TArr TNum TNum)) = None.
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 2: THE STRICT INTERPRETER                                  *)
(* ================================================================ *)

Example ex6_eval_app : eval (App inc (Num 41)) = Some (NumV 42).
Proof. reflexivity. Qed.

Example ex7_eval_if :
  eval (If (IsZero (Num 0)) (Boolean true) (Boolean false))
  = Some (BoolV true).
Proof. reflexivity. Qed.

(* [Lambda] under positive fuel [S k] steps directly to the closure. *)
Example ex8_eval_lambda : forall k env i t b,
  evalM (S k) env (Lambda i t b) = Some (ClosureV i b env).
Proof. reflexivity. Qed.

(* ================================================================ *)
(* PART 3: METATHEORY                                              *)
(* ================================================================ *)

Example ex9_ty_eqb_sound : forall a b,
  Ty_eqb a b = true -> a = b.
Proof. exact Ty_eqb_eq. Qed.

Example ex10_more_fuel : forall f env e v,
  evalM f env e = Some v -> evalM (S f) env e = Some v.
Proof.
  intros f env e v H.
  apply (evalM_mono f (S f) env e v); [lia | exact H].
Qed.

(* Same shape as the lecture's [plus_yields_num]: split on fuel, then on
   the two operand values; the only surviving case builds a [NumV]. *)
Example ex11_mult_yields_num : forall f env a b v,
  evalM f env (Mult a b) = Some v -> isNumV v = true.
Proof.
  intros [| k] env a b v H; simpl in H; [discriminate |].
  destruct (evalM k env a) as [[n | bb | i bd ce] |]; try discriminate;
  destruct (evalM k env b) as [[m | bb | i bd ce] |]; try discriminate.
  injection H as H; subst v. reflexivity.
Qed.

Example ex12_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. intros f env e r1 r2 H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.

(* ================================================================ *)
(* CHALLENGE PROBLEMS                                              *)
(* ================================================================ *)

Definition twice : TFBAEC :=
  Lambda "f" (TArr TNum TNum)
    (Lambda "x" TNum (App (Id "f") (App (Id "f") (Id "x")))).

Example challenge1_twice_ty :
  typecheck twice = Some (TArr (TArr TNum TNum) (TArr TNum TNum)).
Proof. reflexivity. Qed.

Example challenge2_twice_ty :
  typecheck (App (App twice inc) (Num 5)) = Some TNum.
Proof. reflexivity. Qed.

Example challenge2_twice_eval :
  eval (App (App twice inc) (Num 5)) = Some (NumV 7).
Proof. reflexivity. Qed.
