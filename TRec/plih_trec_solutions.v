(**
Programming Languages in Rocq - Typed Recursion Solutions
Complete solutions to plih_trec_exercises.v

The types [Ty], the term language [TFBAEC]/[subst], the checker
[typeof]/[typecheck], the values [TVal], the strict interpreter
[evalM]/[eval], [evalM_mono], [isNumV]/[isBoolV] with their
canonical-forms lemmas, and the sample terms [fact]/[sum]/[selfApp]/
[loopT] all come from the Typed Recursion lecture.
 *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Require Import plih_rocq_trec_shared.
Require Import plih_trec_lecture.

Local Open Scope string_scope.
Import ListNotations.

(** * PART 1: TYPING RECURSION *)

Example ex1_ty_fact_app : typecheck (App fact (Num 3)) = Some TNum.
Proof. reflexivity. Qed.

Example ex2_reject_fix_mismatch :
  typecheck (Fix (Lambda "x" TNum (IsZero (Id "x")))) = None.
Proof. reflexivity. Qed.

Example ex3_reject_selfApp : typecheck (selfApp TNum) = None.
Proof. reflexivity. Qed.

Example ex4_ty_ctx :
  typeof (extend "g" (TArr TNum TNum) nil) (App (Id "g") (Num 1)) = Some TNum.
Proof. reflexivity. Qed.

(** * PART 2: RUNNING RECURSION *)

Example ex5_fact3 : eval (App fact (Num 3)) = Some (NumV 6).
Proof. reflexivity. Qed.

Example ex6_sum4 : eval (App sum (Num 4)) = Some (NumV 10).
Proof. reflexivity. Qed.

Example ex7_loop_diverges : evalM 200 nil loopT = None.
Proof. reflexivity. Qed.

(** * PART 3: METATHEORY *)

Example ex8_more_fuel : forall f env e v,
  evalM f env e = Some v -> evalM (f + 7) env e = Some v.
Proof.
  intros f env e v H.
  apply (evalM_mono f (f + 7) env e v); [lia | exact H].
Qed.

Example ex9_mult_num : forall f env a b v,
  evalM f env (Mult a b) = Some v -> isNumV v = true.
Proof. intros f env a b v H. exact (mult_yields_num f env a b v H). Qed.

Example ex10_deterministic : forall f env e r1 r2,
  evalM f env e = r1 -> evalM f env e = r2 -> r1 = r2.
Proof. intros f env e r1 r2 H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.

(** * PART 4: CONCRETE SYNTAX *)

Open Scope trec_scope.

(* ex11: the arrow is right-associative. *)
Example ex11_parse_ty :
  <[ (Nat -> Nat) -> Nat -> Nat ]> = TArr (TArr TNum TNum) (TArr TNum TNum).
Proof. reflexivity. Qed.

(* ex12: [fix (lambda ...)] is [Fix (Lambda ...)], i.e. [loopT]. *)
Example ex12_parse_fix :
  <{ fix (lambda "x" : Nat in "x") }> = loopT.
Proof. reflexivity. Qed.

(* ex13: the checker consumes the concrete factorial. *)
Example ex13_typecheck_fact :
  typecheck <{ fix (lambda "g" : Nat -> Nat in
                      lambda "n" : Nat in
                        if iszero "n" then 1 else "n" * ("g" ("n" - 1))) }>
  = Some <[ Nat -> Nat ]>.
Proof. reflexivity. Qed.

(* ex14: [eval] consumes the same tree the notation elaborates to. *)
Example ex14_eval_fact :
  eval <{ (fix (lambda "g" : Nat -> Nat in
                  lambda "n" : Nat in
                    if iszero "n" then 1 else "n" * ("g" ("n" - 1)))) 4 }>
  = Some (NumV 24).
Proof. reflexivity. Qed.
